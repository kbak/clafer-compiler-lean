// Independent test adapter; the pinned Analyzer remains outside the Lean kernel.
import com.google.gson.*;
import edu.mit.csail.sdg.alloy4.*;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.parser.*;
import edu.mit.csail.sdg.translator.*;
import kodkod.engine.satlab.SATFactory;
import java.nio.file.*;
import java.util.*;

public final class AlloyCoreBridge {
    public static void main(String[] args) throws Exception {
        if (Runtime.version().feature() != 17) throw new IllegalStateException("Java 17 required");
        Gson json = new GsonBuilder().setPrettyPrinting().create();
        JsonArray cases = JsonParser.parseString(Files.readString(Path.of(args[0]))).getAsJsonArray();
        List<Object> results = new ArrayList<>();
        for (JsonElement element : cases) {
            JsonObject item = element.getAsJsonObject();
            String id = item.get("id").getAsString();
            if (!id.matches("[a-z_]+")) throw new IllegalArgumentException("fixture ID");
            Path source = Path.of(id + ".als");
            Files.writeString(source, item.get("source").getAsString());
            A4Reporter reporter = new A4Reporter();
            CompModule model = CompUtil.parseEverything_fromFile(reporter, null, source.toString());
            if (model.getAllCommands().size() != 1) throw new IllegalArgumentException("command count");
            Command command = model.getAllCommands().get(0);
            if (CompUtil.isTemporalModel(model.getAllReachableSigs(), command))
                throw new IllegalArgumentException("temporal model");
            A4Options options = new A4Options();
            options.solver = SATFactory.get("sat4j");
            options.symmetry = 0; options.skolemDepth = 0;
            options.inferPartialInstance = false; options.noOverflow = true;
            options.unrolls = -1; options.coreMinimization = 2; options.coreGranularity = 0;
            options.recordKodkod = false; options.decompose_mode = 0; options.decompose_threads = 1;
            options.originalFilename = source.toString(); options.tempDirectory = "."; options.solverDirectory = "";
            Map<String,Object> effective = new TreeMap<>();
            for (java.lang.reflect.Field f : A4Options.class.getFields())
                if (!java.lang.reflect.Modifier.isStatic(f.getModifiers()))
                    effective.put(f.getName(), f.getName().equals("solver") ? options.solver.id() : f.get(options));
            Map<String,Object> result = new TreeMap<>();
            result.put("id", id); result.put("options", effective);
            result.put("command", command.toString()); result.put("formula", command.formula.toString());
            result.put("bitwidth", command.bitwidth); result.put("check", command.check);
            result.put("java", Map.of("runtime", System.getProperty("java.runtime.version"),
                "vendor", System.getProperty("java.vendor"), "vm", System.getProperty("java.vm.name")));
            Files.writeString(Path.of(id + "-request.json"), json.toJson(result));
            A4Solution solution = TranslateAlloyToKodkod.execute_command(reporter,
                model.getAllReachableSigs(), command, options);
            if (solution.getMinTrace() != -1 || solution.getMaxTrace() != -1)
                throw new IllegalStateException("temporal search bounds");
            result.put("satisfiable", solution.satisfiable());
            if (solution.satisfiable()) solution.writeXML(id + "-witness.xml", Collections.emptyList());
            results.add(result);
            Files.writeString(Path.of("results.json"), json.toJson(results));
        }
    }
}
