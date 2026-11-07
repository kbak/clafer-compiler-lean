"""Ticket status wiring; adapted from clafer-semantics at 6d04d6c856a8.

Upstream MIT, copyright Kacper Bak. No live credentials or Project writes in tests.
"""
import contextlib
import importlib.util
import io
from pathlib import Path
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location(
    "tickets", Path(__file__).resolve().parents[1] / "scripts/tickets.py"
)
tickets = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(tickets)


# [utest->req~github-tracking~1]
class TicketTests(unittest.TestCase):
    def test_track_resolves_each_status_using_live_project_ids(self):
        for status, display in (("todo", "Todo"), ("ready", "Ready"),
                                ("in-progress", "In Progress"), ("done", "Done")):
            with (
                self.subTest(status=status),
                patch.object(tickets, "gh", side_effect=[
                    {"url": "https://github.com/kbak/clafer-compiler-lean/issues/70"},
                    {"id": "LIVE_ITEM"},
                    {"fields": [{
                        "id": "LIVE_FIELD", "name": "Status",
                        "options": [{"id": "WRONG", "name": "Unrelated"},
                                    {"id": "LIVE_OPTION", "name": display}],
                    }]},
                    "",
                ]) as gh,
                contextlib.redirect_stdout(io.StringIO()) as output,
            ):
                tickets.main(["track", "70", "--status", status])
            self.assertEqual(gh.call_args.args, (
                "project", "item-edit", "--id", "LIVE_ITEM", "--project-id",
                tickets.CONFIG["id"], "--field-id", "LIVE_FIELD",
                "--single-select-option-id", "LIVE_OPTION"))
            self.assertIn(display, output.getvalue())

    def test_missing_ready_option_does_not_write_another_status(self):
        with (
            patch.object(tickets, "gh", side_effect=[
                {"url": "https://github.com/kbak/clafer-compiler-lean/issues/70"},
                {"id": "LIVE_ITEM"},
                {"fields": [{"id": "LIVE_FIELD", "name": "Status",
                             "options": [{"id": "TODO", "name": "Todo"}]}]},
            ]) as gh,
            self.assertRaises(StopIteration),
        ):
            tickets.main(["track", "70", "--status", "ready"])
        self.assertFalse(any(call.args[:2] == ("project", "item-edit")
                             for call in gh.call_args_list))

    def test_unknown_status_fails_before_any_github_call(self):
        with patch.object(tickets, "gh") as gh, contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as error:
                tickets.main(["track", "70", "--status", "blocked"])
        self.assertEqual(error.exception.code, 2)
        gh.assert_not_called()
