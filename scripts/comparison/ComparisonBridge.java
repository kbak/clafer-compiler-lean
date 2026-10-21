// Original MIT adapter. Reuses the pinned upstream AST audit, tuple reader and
// command recorder. Java/JSON parsing, Analyzer and SAT solving remain external.
import com.google.gson.*;
import edu.mit.csail.sdg.alloy4.*;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.parser.*;
import edu.mit.csail.sdg.translator.*;
import kodkod.engine.satlab.SATFactory;
import java.nio.file.*;
import java.util.*;

public final class ComparisonBridge {
    public static void main(String[] args) throws Exception {
        Map<String,Object> out = new TreeMap<>();
        Gson json = new GsonBuilder().serializeNulls().create();
        out.put("outcome", null); out.put("status", "error");
        try {
            AlloyBridge.require(Runtime.version().feature() == 17, "Java 17 required");
            JsonObject r = JsonParser.parseString(Files.readString(Path.of("request.json"))).getAsJsonObject();
            CompModule m = CompUtil.parseEverything_fromFile(new A4Reporter(), null, "comparison.als");
            AlloyBridge.require(m.getAllCommands().size() == 1, "command count");
            Command c = m.getAllCommands().get(0);
            AlloyBridge.require(!CompUtil.isTemporalModel(m.getAllReachableSigs(), c) && !c.check &&
                c.bitwidth == r.get("bitwidth").getAsInt(), "static command/bitwidth");
            JsonObject bounds = r.getAsJsonObject("scope_bounds");
            JsonObject sigSpec = r.getAsJsonObject("signatures");
            AlloyBridge.require(c.scope.size() == bounds.size(), "complete scopes");
            Set<String> scoped = new HashSet<>();
            for (CommandScope s : c.scope) {
                String name = AlloyBridge.uid(s.sig.label);
                AlloyBridge.require(bounds.has(name) && scoped.add(name) && !s.isExact &&
                    s.startingScope == bounds.get(name).getAsInt() && s.endingScope == s.startingScope &&
                    s.increment == 1, "scope mismatch");
            }
            Map<String,Sig> sigs = new TreeMap<>();
            Map<String,Sig.Field> fields = new TreeMap<>();
            for (Sig s : m.getAllReachableSigs()) if (!s.builtin) {
                String name = AlloyBridge.uid(s.label);
                AlloyBridge.require(sigSpec.has(name) && sigs.put(name,s) == null && s.isVariable == null, "signature");
                JsonObject expected = sigSpec.getAsJsonObject(name);
                if (!r.get("subset_mutation").getAsBoolean()) {
                    AlloyBridge.require(s instanceof Sig.PrimSig, "primitive signature");
                    String parent = ((Sig.PrimSig)s).parent == Sig.UNIV ? "" : AlloyBridge.uid(((Sig.PrimSig)s).parent.label);
                    AlloyBridge.require(parent.equals(expected.get("parent").isJsonNull() ? "" : expected.get("parent").getAsString()) &&
                        (s.isAbstract != null) == expected.get("abstract").getAsBoolean(), "hierarchy");
                }
                for (Sig.Field f : s.getFields())
                    AlloyBridge.require(f.type().arity() == 2 && !f.defined && f.isVariable == null &&
                        fields.put(f.label, f) == null, "field");
            }
            AlloyBridge.require(sigs.keySet().equals(sigSpec.keySet()) &&
                fields.keySet().equals(r.getAsJsonObject("fields").keySet()), "inventory");
            Set<String> labels = new HashSet<>();
            for (Sig s : sigs.values()) labels.add(s.label);
            AlloyBridge.audit(c.formula, Collections.newSetFromMap(new IdentityHashMap<>()),
                labels, r.get("maximum").getAsLong());
            A4Options o = new A4Options();
            o.solver=SATFactory.get("sat4j"); o.symmetry=0; o.skolemDepth=0;
            o.inferPartialInstance=false; o.noOverflow=true; o.unrolls=-1;
            o.coreMinimization=2; o.coreGranularity=0; o.recordKodkod=false;
            o.decompose_mode=0; o.decompose_threads=1;
            o.originalFilename="comparison.als"; o.tempDirectory="."; o.solverDirectory="";
            Map<String,Object> options = new TreeMap<>();
            for (java.lang.reflect.Field f : A4Options.class.getFields())
                if (!java.lang.reflect.Modifier.isStatic(f.getModifiers()))
                    options.put(f.getName(), f.getName().equals("solver") ? o.solver.id() : f.get(o));
            out.put("command", AlloyBridge.command(c)); out.put("options", options);
            out.put("stage", "solver");
            Files.writeString(Path.of("execution.json"), json.toJson(out));
            A4Solution sol = TranslateAlloyToKodkod.execute_command(new A4Reporter(),m.getAllReachableSigs(),c,o);
            out.put("outcome", sol.satisfiable() ? "sat" : "unsat");
            AlloyBridge.require(sol.getMinTrace() == -1 && sol.getMaxTrace() == -1, "static trace");
            if (sol.satisfiable()) {
                Map<String,Object> extents = new TreeMap<>(), tuples = new TreeMap<>();
                for (var e : sigs.entrySet()) extents.put(e.getKey(),
                    AlloyBridge.tuples(sol.eval(e.getValue())).stream().map(x -> x.get(0)).toList());
                for (var e : fields.entrySet()) tuples.put(e.getKey(), AlloyBridge.tuples(sol.eval(e.getValue())));
                out.put("witness", Map.of("signatures", extents, "fields", tuples));
                sol.writeXML("witness.xml", Collections.emptyList());
            }
            out.put("status", "ok"); out.put("stage", "complete");
        } catch (OutOfMemoryError e) { out.put("status", "resource_limit"); }
          catch (Throwable e) { out.put("detail", e.toString()); }
        Files.writeString(Path.of("solver.json"), json.toJson(out));
    }
}
