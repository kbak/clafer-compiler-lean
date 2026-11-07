// Original MIT adapter using Alloy 6.2 public APIs; an external tested boundary.
import com.google.gson.*;
import edu.mit.csail.sdg.alloy4.*;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.parser.*;
import edu.mit.csail.sdg.translator.*;
import kodkod.engine.satlab.SATFactory;
import java.nio.file.*;
import java.util.*;

public final class AlloyTemporalBridge {
    static final Gson JSON = new GsonBuilder().serializeNulls().create();
    static final Map<String,Object> out = new TreeMap<>();
    static void require(boolean b, String message) {
        if (!b) throw new IllegalArgumentException(message);
    }
    static void stage(String name) throws Exception {
        out.put("stage", name);
        Files.writeString(Path.of("execution.json"), JSON.toJson(out));
    }
    static List<List<String>> tuples(A4TupleSet set) {
        List<List<String>> rows = new ArrayList<>();
        for (A4Tuple tuple : set) {
            List<String> row = new ArrayList<>();
            for (int i=0; i<tuple.arity(); i++) row.add(tuple.atom(i));
            rows.add(row);
        }
        rows.sort(Comparator.comparing(Object::toString));
        return rows;
    }
    static Map<String,Object> command(Command c) {
        List<Object> scopes = new ArrayList<>();
        for (CommandScope s : c.scope) scopes.add(Map.of("signature", s.sig.label,
            "exact", s.isExact, "start", s.startingScope, "end", s.endingScope,
            "increment", s.increment));
        return Map.of("label", c.label, "check", c.check, "overall", c.overall,
            "bitwidth", c.bitwidth, "maxseq", c.maxseq, "min_steps", c.minprefix,
            "max_steps", c.maxprefix, "scopes", scopes, "formula", c.formula.toString());
    }
    // [impl->req~compiler-temporal-oracles~1]
    static void execute(JsonObject r) throws Exception {
        require(Runtime.version().feature()==17, "Java 17 required");
        stage("parse");
        CompModule model = CompUtil.parseEverything_fromFile(new A4Reporter(), null, "model.als");
        int index = r.get("command_index").getAsInt();
        require(index>=0 && index<model.getAllCommands().size(), "command index");
        Command original = model.getAllCommands().get(index);
        out.put("original_command", command(original));
        int min = r.get("min_steps").getAsInt(), max = r.get("max_steps").getAsInt();
        Command c = new Command(original.pos, original.nameExpr, original.label, original.check,
            r.get("overall").getAsInt(), r.get("bitwidth").getAsInt(), 0, min, max,
            original.expects, List.of(), List.of(), original.commandKeyword, original.formula, null);
        JsonObject bounds = r.getAsJsonObject("identities");
        Map<String,Sig> sigs = new TreeMap<>();
        Map<String,Sig.Field> fields = new TreeMap<>();
        Map<String,Object> declarations = new TreeMap<>();
        Map<String,Object> fieldDeclarations = new TreeMap<>();
        for (Sig s : model.getAllReachableSigs()) {
            if (s.builtin) continue;
            require(s.label.startsWith("this/"), "external module signature");
            require(s instanceof Sig.PrimSig, "subset scope needs a separate policy");
            require(bounds.has(s.label), "missing identity scope: " + s.label);
            JsonObject bound = bounds.getAsJsonObject(s.label);
            int count = bound.get("count").getAsInt();
            // Static singleton scopes and temporal populations are different:
            // one/lone var sigs may replace their atom across the whole trace.
            require(s.isOne==null || (s.isVariable==null ? count==1 : count>=1),
                "one signature scope: " + s.label);
            require(s.isLone==null || s.isVariable!=null || count<=1,
                "lone signature scope: " + s.label);
            require(s.isSome==null || count>=1, "some signature scope: " + s.label);
            c = c.change(s, bound.get("exact").getAsBoolean(), count);
            sigs.put(s.label,s);
            declarations.put(s.label,Map.of("mutable",s.isVariable!=null,
                "parent",((Sig.PrimSig)s).parent.label,"abstract",s.isAbstract!=null));
            for (Sig.Field f:s.getFields()) {
                String key=s.label+"/"+f.label;
                fields.put(key,f);
                fieldDeclarations.put(key,Map.of("mutable",f.isVariable!=null,"arity",f.type().arity()));
            }
        }
        require(sigs.keySet().equals(bounds.keySet()), "unknown identity scopes");
        require(c.minprefix==min && c.maxprefix==max && min>0 && max>=min, "step bounds");
        require(CompUtil.isTemporalModel(model.getAllReachableSigs(),c), "temporal model required");
        A4Options options = new A4Options();
        options.solver=SATFactory.get("sat4j");
        require(options.solver.isPresent() && !options.solver.unbounded(), "SAT4J unavailable");
        options.symmetry=0; options.skolemDepth=0; options.inferPartialInstance=false;
        options.noOverflow=true; options.unrolls=-1; options.coreMinimization=2;
        options.coreGranularity=0; options.recordKodkod=false;
        options.decompose_mode=0; options.decompose_threads=1;
        options.originalFilename="model.als"; options.tempDirectory="."; options.solverDirectory="";
        Map<String,Object> effective = new TreeMap<>();
        for (java.lang.reflect.Field f:A4Options.class.getFields())
            if (!java.lang.reflect.Modifier.isStatic(f.getModifiers()))
                effective.put(f.getName(),f.getName().equals("solver") ? options.solver.id() : f.get(options));
        out.put("options",effective); out.put("command",command(c));
        stage("solver");
        A4Solution solution=TranslateAlloyToKodkod.execute_command(new A4Reporter(),model.getAllReachableSigs(),c,options);
        out.put("outcome",solution.satisfiable()?"sat":"bounded_unsat");
        stage("trace");
        if (solution.satisfiable()) {
            int length=solution.getTraceLength(), loop=solution.getLoopState();
            require(length>0 && loop>=0 && loop<length && length<=max, "lasso shape");
            List<Object> frames=new ArrayList<>();
            Set<String> inventory=new TreeSet<>();
            for (int i=0;i<length;i++) {
                Map<String,Object> extents=new TreeMap<>(), relations=new TreeMap<>();
                for (var e:sigs.entrySet()) {
                    List<List<String>> rows=tuples(solution.eval(e.getValue(),i));
                    extents.put(e.getKey(),rows);
                    for (var row:rows) inventory.addAll(row);
                }
                for (var e:fields.entrySet()) relations.put(e.getKey(),tuples(solution.eval(e.getValue(),i)));
                frames.add(Map.of("signatures",extents,"fields",relations));
            }
            out.put("trace",Map.of("length",length,"loop",loop,"inventory",inventory,"frames",frames,
                "signatures",declarations,"fields",fieldDeclarations));
            solution.writeXML("witness.xml",List.of());
        }
        out.put("status","ok"); stage("complete");
    }
    public static void main(String[] args) throws Exception {
        out.put("schema","clafer-temporal-solver/1"); out.put("outcome",null);
        try {execute(JsonParser.parseString(Files.readString(Path.of("request.json"))).getAsJsonObject());}
        catch (OutOfMemoryError e) {out.put("status","resource_limit"); out.put("detail",e.toString());}
        catch (IllegalArgumentException e) {out.put("status","malformed"); out.put("detail",e.toString());}
        catch (Throwable e) {out.put("status","error"); out.put("detail",e.toString()); e.printStackTrace(System.err);}
        Files.writeString(Path.of("solver.json"),JSON.toJson(out));
    }
}
