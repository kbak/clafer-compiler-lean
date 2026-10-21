// Original MIT test adapter. Normalization and solving are external evidence,
// never part of the kernel proof or a replacement for independent expectations.
import com.google.gson.*;
import edu.mit.csail.sdg.alloy4.*;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.parser.*;
import edu.mit.csail.sdg.translator.*;
import kodkod.engine.satlab.SATFactory;
import java.nio.file.*;
import java.util.*;

public final class AlloyTextBridge {
    static Object expr(Expr e, List<ExprVar> bound) {
        if (e instanceof ExprUnary u) {
            if (u.op == ExprUnary.Op.NOOP) return expr(u.sub, bound);
            return List.of(u.op.name(), expr(u.sub, bound));
        }
        if (e instanceof ExprBinary b)
            return List.of(b.op.name(), expr(b.left, bound), expr(b.right, bound));
        if (e instanceof ExprCall c) {
            if (!Set.of("integer/plus", "integer/minus").contains(c.fun.label))
                throw new IllegalArgumentException("unhandled function " + c.fun.label);
            List<Object> args = new ArrayList<>();
            for (Expr a : c.args) args.add(expr(a, bound));
            return List.of("call", c.fun.label, args);
        }
        if (e instanceof ExprList l) {
            List<Object> values = new ArrayList<>(); values.add(l.op.name());
            for (Expr a : l.args) values.add(expr(a, bound));
            return values;
        }
        if (e instanceof ExprQt q) {
            List<ExprVar> env = new ArrayList<>(bound);
            List<Object> declarations = new ArrayList<>();
            for (Decl d : q.decls) {
                Object domain = expr(d.expr, env);
                declarations.add(List.of(d.disjoint != null, d.disjoint2 != null, d.names.size(), domain));
                for (ExprHasName n : d.names) env.add((ExprVar)n);
            }
            return List.of(q.op.name(), declarations, expr(q.sub, env));
        }
        if (e instanceof ExprVar v) {
            int i = bound.lastIndexOf(v);
            if (i < 0) throw new IllegalArgumentException("unresolved variable " + v);
            return List.of("var", bound.size() - i - 1);
        }
        if (e instanceof Sig.Field f) return List.of("field", f.sig.label, f.label);
        if (e instanceof Sig s) return List.of("sig", s.label);
        if (e instanceof ExprConstant c) return List.of(c.op.name(), c.num, c.string == null ? "" : c.string);
        throw new IllegalArgumentException("unhandled AST: " + e.getClass() + " " + e);
    }
    static CompModule parse(Path file) throws Exception {
        return CompUtil.parseEverything_fromFile(new A4Reporter(), null, file.toString());
    }
    static Map<String,Object> normalized(CompModule model) {
        if (model.getAllCommands().size() != 1) throw new IllegalArgumentException("command count");
        Command c = model.getAllCommands().get(0);
        if (CompUtil.isTemporalModel(model.getAllReachableSigs(), c))
            throw new IllegalArgumentException("temporal input");
        Map<String,Object> result = new TreeMap<>();
        List<Object> sigs = new ArrayList<>();
        for (Sig s : model.getAllReachableSigs()) if (!s.builtin) {
            if (!(s instanceof Sig.PrimSig p)) throw new IllegalArgumentException("subset signature");
            List<Object> fields = new ArrayList<>();
            for (Sig.Field f : s.getFields()) fields.add(List.of(f.label, expr(f.decl().expr, List.of())));
            sigs.add(List.of(s.label, p.parent.label, s.isAbstract != null, s.isOne != null,
                            s.isLone != null, s.isSome != null, fields));
        }
        List<Object> scopes = new ArrayList<>();
        for (CommandScope s : c.scope)
            scopes.add(List.of(s.sig.label, s.isExact, s.startingScope, s.endingScope, s.increment));
        result.put("signatures", sigs); result.put("scopes", scopes);
        result.put("bitwidth", c.bitwidth); result.put("check", c.check);
        result.put("formula", expr(c.formula, List.of()));
        return result;
    }
    static Map<String,Object> solve(CompModule model, String name) throws Exception {
        A4Options o = new A4Options();
        o.solver = SATFactory.get("sat4j"); o.symmetry = 0; o.skolemDepth = 0;
        o.inferPartialInstance = false; o.noOverflow = true;
        o.unrolls = -1; o.coreMinimization = 2; o.coreGranularity = 0;
        o.recordKodkod = false; o.decompose_mode = 0; o.decompose_threads = 1;
        o.originalFilename = name + ".als"; o.tempDirectory = "."; o.solverDirectory = "";
        Map<String,Object> options = new TreeMap<>();
        for (java.lang.reflect.Field f : A4Options.class.getFields())
            if (!java.lang.reflect.Modifier.isStatic(f.getModifiers()))
                options.put(f.getName(), f.getName().equals("solver") ? o.solver.id() : f.get(o));
        // Retain the effective options even if translation fails before solving.
        Files.writeString(Path.of(name + "-options.json"), new GsonBuilder().setPrettyPrinting().create().toJson(options));
        A4Solution sol = TranslateAlloyToKodkod.execute_command(new A4Reporter(),
            model.getAllReachableSigs(), model.getAllCommands().get(0), o);
        if (sol.satisfiable()) sol.writeXML(name + ".xml", Collections.emptyList());
        return Map.of("satisfiable", sol.satisfiable(), "options", options);
    }
    public static void main(String[] args) throws Exception {
        if (Runtime.version().feature() != 17) throw new IllegalStateException("Java 17 required");
        Gson json = new GsonBuilder().setPrettyPrinting().create();
        Path root = Path.of(args[0]);
        JsonArray cases = JsonParser.parseString(Files.readString(root.resolve("manifest.json"))).getAsJsonArray();
        List<Object> results = new ArrayList<>();
        for (JsonElement row : cases) {
            JsonObject item = row.getAsJsonObject();
            String id = item.get("id").getAsString();
            if (!id.matches("case_[0-9]+")) throw new IllegalArgumentException("case ID");
            CompModule model = parse(root.resolve(id + ".als"));
            Map<String,Object> ast = normalized(model);
            Map<String,Object> result = new TreeMap<>(); result.put("id", id); result.put("ast", ast);
            if (item.has("reference")) {
                Map<String,Object> ref = normalized(parse(root.resolve(id + "-reference.als")));
                Files.writeString(root.resolve(id + "-reference-ast.json"), json.toJson(ref));
                if (!ast.equals(ref)) throw new IllegalStateException("AST mismatch: " + id + "\n" + json.toJson(ast));
                result.put("referenceMatched", true);
            }
            if (item.has("expected")) {
                Map<String,Object> observation = solve(parse(root.resolve(id + "-pinned.als")), id + "-pinned");
                if (!observation.get("satisfiable").equals(item.get("expected").getAsBoolean()))
                    throw new IllegalStateException("meaning mismatch " + id);
                result.put("observation", observation);
            }
            results.add(result);
            Files.writeString(root.resolve("results.json"), json.toJson(results));
        }
        // Both deliberate mutations remain valid Alloy. The independent AST
        // comparison must detect grouping loss and reference aliasing.
        for (int i : new int[]{24, 25}) {
            Object original = normalized(parse(root.resolve("case_" + i + ".als")));
            Object mutation = normalized(parse(root.resolve("case_" + i + "-mutated.als")));
            if (original.equals(mutation)) throw new IllegalStateException("mutation survived " + i);
        }
    }
}
