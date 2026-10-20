#!/usr/bin/env python3
"""Manage this repository's GitHub issues and Project using the authenticated gh CLI."""

import argparse
import json
from pathlib import Path
import subprocess
import sys

CONFIG = json.loads(
    (Path(__file__).resolve().parents[1] / ".github/project.json").read_text()
)
STATUSES = {"todo": "Todo", "in-progress": "In Progress", "done": "Done"}


def gh(*args, structured=False):
    result = subprocess.run(
        ["gh", *map(str, args)], check=True, text=True, capture_output=True
    )
    return json.loads(result.stdout) if structured else result.stdout.strip()


# [impl->req~github-tracking~1]
def track(number, status):
    issue = gh(
        "issue",
        "view",
        number,
        "--repo",
        CONFIG["repository"],
        "--json",
        "url",
        structured=True,
    )
    item = gh(
        "project",
        "item-add",
        CONFIG["number"],
        "--owner",
        CONFIG["owner"],
        "--url",
        issue["url"],
        "--format",
        "json",
        structured=True,
    )
    fields = gh(
        "project",
        "field-list",
        CONFIG["number"],
        "--owner",
        CONFIG["owner"],
        "--format",
        "json",
        structured=True,
    )["fields"]
    field = next(f for f in fields if f["name"] == "Status")
    option = next(o for o in field["options"] if o["name"] == STATUSES[status])
    gh(
        "project",
        "item-edit",
        "--id",
        item["id"],
        "--project-id",
        CONFIG["id"],
        "--field-id",
        field["id"],
        "--single-select-option-id",
        option["id"],
    )
    print(f"{issue['url']} — {STATUSES[status]}", flush=True)


def parser():
    root = argparse.ArgumentParser(description=__doc__)
    commands = root.add_subparsers(dest="command", required=True)
    commands.add_parser("list", help="List open repository issues")
    create = commands.add_parser("create", help="Create an issue and track it as Todo")
    create.add_argument("--title", required=True)
    create.add_argument("--body-file", type=Path, required=True)
    create.add_argument("--label", action="append", default=[])
    create.add_argument("--no-project", action="store_true",
                        help="Create only the repository issue; leave Project tracking to a maintainer")
    tracking = commands.add_parser(
        "track", help="Add/reconcile Project membership and status"
    )
    tracking.add_argument("number", type=int)
    tracking.add_argument("--status", choices=STATUSES, default="todo")
    edit = commands.add_parser("edit", help="Edit an existing issue")
    edit.add_argument("number", type=int)
    edit.add_argument("--title")
    edit.add_argument("--body-file", type=Path)
    edit.add_argument("--add-label", action="append", default=[])
    edit.add_argument("--remove-label", action="append", default=[])
    comment = commands.add_parser("comment", help="Post a progress or decision comment")
    comment.add_argument("number", type=int)
    comment.add_argument("--body-file", type=Path, required=True)
    close = commands.add_parser(
        "close", help="Close an issue and mark its Project item Done"
    )
    close.add_argument("number", type=int)
    close.add_argument(
        "--reason", choices=["completed", "not planned"], default="completed"
    )
    close.add_argument("--no-project", action="store_true",
                       help="Close only the repository issue; leave Project tracking to a maintainer")
    return root


# [impl->req~github-tracking~1]
def main(argv=None):
    cli = parser()
    args = cli.parse_args(argv)
    if getattr(args, "body_file", None) is not None and not args.body_file.is_file():
        cli.error("--body-file must name an existing file")
    repository = ("--repo", CONFIG["repository"])
    if args.command == "list":
        print(
            gh(
                "issue",
                "list",
                *repository,
                "--limit",
                100,
                "--json",
                "number,title,url,labels,assignees",
            )
        )
    elif args.command == "create":
        labels = [part for label in args.label for part in ("--label", label)]
        url = gh(
            "issue",
            "create",
            *repository,
            "--title",
            args.title,
            "--body-file",
            args.body_file,
            *labels,
        )
        if args.no_project:
            print(f"Created {url}; Project tracking is left to a maintainer", flush=True)
        else:
            # Preserve the issue identity even if subsequent Project operations fail.
            print(
                f"Created {url}; retry tracking with: tickets.py track {url.rsplit('/', 1)[-1]}",
                flush=True,
            )
            track(int(url.rsplit("/", 1)[-1]), "todo")
    elif args.command == "track":
        track(args.number, args.status)
    elif args.command == "edit":
        options = []
        for flag, value in (("--title", args.title), ("--body-file", args.body_file)):
            if value is not None:
                options.extend((flag, value))
        for flag, values in (
            ("--add-label", args.add_label),
            ("--remove-label", args.remove_label),
        ):
            for value in values:
                options.extend((flag, value))
        if not options:
            cli.error("edit requires a title, body, or label change")
        print(gh("issue", "edit", args.number, *repository, *options))
    elif args.command == "comment":
        print(
            gh(
                "issue",
                "comment",
                args.number,
                *repository,
                "--body-file",
                args.body_file,
            )
        )
    elif args.command == "close":
        print(gh("issue", "close", args.number, *repository, "--reason", args.reason))
        if not args.no_project:
            track(args.number, "done")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        print(error.stderr or str(error), file=sys.stderr)
        raise SystemExit(error.returncode)
    except (OSError, ValueError, KeyError, StopIteration) as error:
        print(f"Ticket operation failed: {error}", file=sys.stderr)
        raise SystemExit(1)
