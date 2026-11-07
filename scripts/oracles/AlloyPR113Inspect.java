// Original MIT adapter. The existing bridge supplies query execution unchanged.
import com.google.gson.*;
import edu.mit.csail.sdg.alloy4.*;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.parser.*;
import java.nio.file.*;
import java.util.*;

public final class AlloyPR113Inspect {
    static List<String> targets(Expr expression) {
        if (expression instanceof Sig) return List.of(((Sig) expression).label);
        if (expression instanceof ExprUnary) {
            ExprUnary u = (ExprUnary) expression;
            if (u.op == ExprUnary.Op.NOOP || u.op == ExprUnary.Op.SETOF ||
                u.op == ExprUnary.Op.ONEOF || u.op == ExprUnary.Op.LONEOF || u.op == ExprUnary.Op.SOMEOF)
                return targets(u.sub);
        }
        if (expression instanceof ExprBinary && ((ExprBinary) expression).op == ExprBinary.Op.PLUS) {
            ExprBinary b = (ExprBinary) expression;
            List<String> result = new ArrayList<>(targets(b.left));
            result.addAll(targets(b.right));
            return result;
        }
        throw new IllegalArgumentException("unsupported field declaration: " + expression);
    }
    // [impl->req~compiler-temporal-oracles~1]
    static Map<String,Object> inventory(CompModule model) {
        Map<String,Object> sigs = new TreeMap<>(), fields = new TreeMap<>();
        for (Sig s : model.getAllReachableSigs()) {
            if (s.builtin) continue;
            if (!(s instanceof Sig.PrimSig)) throw new IllegalArgumentException("subset signature");
            sigs.put(s.label, Map.of("parent", ((Sig.PrimSig)s).parent.label,
                "abstract", s.isAbstract != null, "one", s.isOne != null));
            for (Sig.Field f : s.getFields()) {
                List<List<String>> cols = new ArrayList<>();
                for (List<Sig.PrimSig> product : f.type().fold()) {
                    List<String> names = new ArrayList<>();
                    for (Sig.PrimSig col : product) names.add(col.label);
                    cols.add(names);
                }
                fields.put(s.label + "/" + f.label, Map.of("owner",s.label,
                    "arity",f.type().arity(), "columns",cols, "targets",targets(f.decl().expr),
                    "mutable",f.isVariable != null));
            }
        }
        List<Object> commands = new ArrayList<>();
        for (Command c : model.getAllCommands()) commands.add(AlloyTemporalBridge.command(c));
        return Map.of("schema","clafer-pr113-inspection/1", "signatures",sigs,"fields",fields,"commands",commands);
    }
    static final class Warnings extends A4Reporter {
        final List<Object> messages = new ArrayList<>();
        @Override public void warning(ErrorWarning warning) {
            messages.add(Map.of("message", warning.msg, "line", warning.pos.y,
                "column", warning.pos.x, "end_line", warning.pos.y2, "end_column", warning.pos.x2));
            save();
        }
        void save() {
            try { Files.writeString(Path.of("warnings.json"), AlloyTemporalBridge.JSON.toJson(
                Map.of("schema", "clafer-alloy-warnings/1", "warnings", messages))); }
            catch (java.io.IOException e) { throw new java.io.UncheckedIOException(e); }
        }
    }
    public static void main(String[] args) throws Exception {
        if (Arrays.equals(args, new String[]{"--solve-c7"}) ||
            Arrays.equals(args, new String[]{"--solve-static-c7"})) {
            Warnings reporter = new Warnings();
            reporter.save();
            AlloyTemporalBridge.run(AlloyPR113Inspect::inventory, reporter, args[0].equals("--solve-c7"));
        } else if (Arrays.equals(args, new String[]{"--inspect-c7"})) {
            Warnings reporter = new Warnings();
            reporter.save();
            CompModule model = CompUtil.parseEverything_fromFile(reporter, null, "model.als");
            Files.writeString(Path.of("inspection.json"), AlloyTemporalBridge.JSON.toJson(inventory(model)));
        } else if (Arrays.equals(args, new String[]{"--solve"})) {
            // The bridge retains one fresh model and the ordinary query/error path.
            AlloyTemporalBridge.run(AlloyPR113Inspect::inventory);
        } else {
            if (args.length != 0) throw new IllegalArgumentException("expected --solve or no arguments");
            CompModule model = CompUtil.parseEverything_fromFile(new A4Reporter(), null, "model.als");
            Files.writeString(Path.of("inspection.json"), AlloyTemporalBridge.JSON.toJson(inventory(model)));
        }
    }
}
