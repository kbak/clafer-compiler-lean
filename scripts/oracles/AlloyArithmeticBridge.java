// Original MIT test adapter; reuse the pinned parser, AST normalizer and solver.
import com.google.gson.*;
import java.nio.file.*;
import java.util.*;

public final class AlloyArithmeticBridge {
    public static void main(String[] args) throws Exception {
        if (Runtime.version().feature() != 17) throw new IllegalStateException("Java 17 required");
        Path root = Path.of(args[0]);
        Gson json = new GsonBuilder().setPrettyPrinting().create();
        JsonArray manifest = JsonParser.parseString(Files.readString(root.resolve("manifest.json"))).getAsJsonArray();
        List<Object> results = new ArrayList<>();
        for (JsonElement row : manifest) {
            JsonObject item = row.getAsJsonObject();
            String id = item.get("id").getAsString();
            if (!id.matches("case_[0-9]+")) throw new IllegalArgumentException("case ID");
            var model = AlloyTextBridge.parse(root.resolve(id + ".als"));
            var ast = AlloyTextBridge.normalized(model);
            var reference = AlloyTextBridge.normalized(AlloyTextBridge.parse(root.resolve(id + "-reference.als")));
            if (!ast.equals(reference)) throw new IllegalStateException("AST mismatch " + id + " " + json.toJson(ast));
            Map<String,Object> observation;
            try {
                observation = AlloyTextBridge.solve(model, id);
            } catch (edu.mit.csail.sdg.alloy4.Err failure) {
                // Preserve the known width-16 translation limit as a tool error,
                // never as bounded UNSAT or agreement with the native result.
                if (!item.has("expectedToolError") ||
                    !failure.getMessage().contains("Translation capacity exceeded") ||
                    !failure.getMessage().contains("65536 atoms")) throw failure;
                results.add(Map.of("id", id, "ast", ast, "toolError", failure.getMessage()));
                continue;
            }
            if (item.has("expectedToolError"))
                throw new IllegalStateException("expected capacity limit changed: " + id);
            if (!observation.get("satisfiable").equals(item.get("expected").getAsBoolean()))
                throw new IllegalStateException("meaning mismatch " + id);
            Map<String,Object> result = new TreeMap<>();
            result.put("id", id); result.put("ast", ast); result.put("observation", observation);
            if (item.has("mutation")) {
                var mutation = AlloyTextBridge.parse(root.resolve(id + "-mutated.als"));
                if (ast.equals(AlloyTextBridge.normalized(mutation)))
                    throw new IllegalStateException("mutation AST survived " + id);
                var changed = AlloyTextBridge.solve(mutation, id + "-mutated");
                if (changed.get("satisfiable").equals(observation.get("satisfiable")))
                    throw new IllegalStateException("mutation meaning survived " + id);
                result.put("mutation", changed);
            }
            results.add(result);
        }
        Files.writeString(root.resolve("results.json"), json.toJson(results));
    }
}
