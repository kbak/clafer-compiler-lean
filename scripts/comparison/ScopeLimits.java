// Read logical limits from the Analyzer's parsed command and named facts.
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.parser.CompModule;
import java.util.*;

final class ScopeLimits {
    static Map<Sig, Integer> read(CompModule model, Command command) {
        Map<Sig, CommandScope> allocations = new HashMap<>();
        for (CommandScope scope : command.scope) {
            if (allocations.put(scope.sig, scope) != null)
                throw new IllegalArgumentException("duplicate scope");
        }
        Map<Sig, Integer> limits = new HashMap<>();
        for (var fact : model.getAllFacts()) {
            if (!fact.a.startsWith("limit_cc")) continue;
            if (!(fact.b.deNOP() instanceof ExprBinary cmp) || cmp.op != ExprBinary.Op.LTE ||
                !(cmp.left.deNOP() instanceof ExprUnary count) || count.op != ExprUnary.Op.CARDINALITY ||
                !(count.sub.deNOP() instanceof Sig sig) ||
                !(cmp.right.deNOP() instanceof ExprConstant n) || n.op != ExprConstant.Op.NUMBER ||
                !sig.label.equals("this/" + fact.a.substring("limit_".length())))
                throw new IllegalArgumentException("malformed declaration limit");
            CommandScope scope = allocations.get(sig);
            if (scope == null || scope.isExact || n.num < 0 || n.num > scope.startingScope ||
                command.bitwidth < 1 || command.bitwidth > 16 ||
                scope.startingScope >= (1 << (command.bitwidth - 1)) ||
                limits.put(sig, n.num) != null)
                throw new IllegalArgumentException("invalid declaration limit");
        }
        return limits;
    }
}
