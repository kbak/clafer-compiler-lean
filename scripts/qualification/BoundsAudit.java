// Original MIT adapter. Inspect actual Analyzer commands without invoking solving.
import com.google.gson.*;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.parser.CompUtil;
import java.nio.file.*;
import java.util.*;

public final class BoundsAudit {
    public static void main(String[] args) throws Exception {
        var model = CompUtil.parseEverything_fromFile(new A4Reporter(), null, args[0]);
        var expected = JsonParser.parseString(Files.readString(Path.of(args[1]))).getAsJsonObject();
        if (model.getAllCommands().size() != 1) throw new IllegalStateException("command count");
        var command = model.getAllCommands().get(0);
        if (command.check || CompUtil.isTemporalModel(model.getAllReachableSigs(), command))
            throw new IllegalStateException("non-static run");
        if (command.bitwidth != expected.get("bitwidth").getAsInt())
            throw new IllegalStateException("bitwidth mismatch");
        var actual = new JsonObject();
        for (var scope : command.scope) {
            if (scope.startingScope != scope.endingScope || scope.increment != 1)
                throw new IllegalStateException("scope range");
            var row = new JsonObject();
            row.addProperty("size", scope.startingScope);
            row.addProperty("exact", scope.isExact);
            actual.add(scope.sig.label.replaceFirst("^this/", ""), row);
        }
        if (!actual.equals(expected.getAsJsonObject("declarations")))
            throw new IllegalStateException("scope mismatch: " + actual + " expected " + expected);
        for (var sig : model.getAllReachableSigs())
            if (!sig.builtin && !actual.has(sig.label.replaceFirst("^this/", "")))
                throw new IllegalStateException("implicit signature scope: " + sig.label);
        var result = new JsonObject();
        result.addProperty("bitwidth", command.bitwidth);
        result.addProperty("solver_invoked", false);
        result.add("declarations", actual);
        Files.writeString(Path.of(args[2]), new GsonBuilder().setPrettyPrinting().create().toJson(result));
    }
}
