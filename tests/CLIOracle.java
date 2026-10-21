// Original MIT integration wrapper. Reuse the existing pinned Analyzer adapter.
import com.google.gson.*;
import java.nio.file.*;
import java.util.*;

public final class CLIOracle {
    public static void main(String[] args) throws Exception {
        List<Object> rows = new ArrayList<>();
        for (String name : args) {
            var model = AlloyTextBridge.parse(Path.of(name + ".als"));
            rows.add(Map.of("name", name, "ast", AlloyTextBridge.normalized(model),
                            "observation", AlloyTextBridge.solve(model, name)));
        }
        Files.writeString(Path.of("results.json"),
            new GsonBuilder().setPrettyPrinting().create().toJson(rows));
    }
}
