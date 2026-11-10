import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashSet;
import java.util.Set;
import javax.xml.stream.XMLOutputFactory;
import javax.xml.stream.XMLStreamWriter;
import org.clafer.ast.*;
import org.clafer.ast.analysis.InsufficientScopeException;
import org.clafer.compiler.*;
import org.clafer.frontend.ExplicitParser;
import org.clafer.instance.*;
import org.clafer.scope.*;

/** External extraction only: semantic verdicts belong to the existing Lean checker. */
// [impl->req~compiler-choco-instances~1]
public final class ChocoInstances {
    private static XMLStreamWriter out;
    private static AstModel model;

    private static void attr(String name, Object value) throws Exception {
        out.writeAttribute(name, String.valueOf(value));
    }

    private static void card(String prefix, Card card) throws Exception {
        attr(prefix + "Low", card.getLow());
        attr(prefix + "High", card.hasHigh() ? card.getHigh() : -1);
    }

    private static String parent(AstClafer c) {
        if (c instanceof AstAbstractClafer) return "";
        return c.getParent() == model.getAbstractRoot() || c.getParent() == model.getRoot()
                ? "root" : c.getParent().getName();
    }

    private static void declarations(Scope scope) throws Exception {
        out.writeStartElement("declarations");
        Set<String> names = new HashSet<>();
        for (AstClafer c : AstUtil.getClafers(model)) {
            if (c == model.getRoot() || c == model.getAbstractRoot() || c == model.getTypeRoot()) continue;
            if (!names.add(c.getName()) || c.isPrimitive() || c.hasConstraints())
                throw new IllegalArgumentException("Unsupported declaration: " + c.getName());
            out.writeEmptyElement("declaration");
            attr("uid", c.getName());
            attr("parent", parent(c));
            attr("super", c.hasSuperClafer() && c.getSuperClafer() != model.getTypeRoot()
                    ? c.getSuperClafer().getName() : "");
            attr("abstract", c instanceof AstAbstractClafer);
            card("card", c instanceof AstConcreteClafer concrete ? concrete.getCard() : new Card(0));
            card("group", c.hasGroupCard() ? c.getGroupCard() : new Card(0));
            attr("mode", c.hasRef() ? (c.getRef().isUnique() ? "set" : "bag") : "basic");
            attr("target", c.hasRef() ? c.getRef().getTargetType().getName() : "");
            attr("scope", scope.getScope(c));
        }
        out.writeEndElement();
    }

    private static void object(InstanceClafer value, InstanceClafer parent) throws Exception {
        out.writeStartElement("object");
        attr("type", value.getType().getName());
        attr("id", value.getId());
        attr("parentType", parent == null ? "root" : parent.getType().getName());
        attr("parentId", parent == null ? 0 : parent.getId());
        if (value.hasRef()) {
            if (!(value.getRef() instanceof InstanceClafer target))
                throw new IllegalArgumentException("Missing or primitive reference target");
            out.writeEmptyElement("reference");
            attr("type", target.getType().getName());
            attr("id", target.getId());
        }
        out.writeEndElement();
        for (InstanceClafer child : value.getChildren()) object(child, value);
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 4) throw new IllegalArgumentException("explicit.cfr scopes output.xml limit");
        int limit = Integer.parseInt(args[3]);
        if (limit < 1 || limit > 1000) throw new IllegalArgumentException("Instance limit 1..1000 required");
        var parsed = ExplicitParser.parse(Files.readString(Path.of(args[0])));
        if (!parsed.diagnostics().isEmpty()) throw new IllegalArgumentException(parsed.diagnostics().toString());
        model = parsed.model();
        if (parsed.objectives().length != 0 || parsed.assertions().length != 0 || model.hasConstraints())
            throw new IllegalArgumentException("Guarded structural models only");
        Scope scope = ScopeFile.parse(Files.readString(Path.of(args[1])), args[1])
                .applyTo(Scope.builder().toScope(), model);
        try (var stream = Files.newOutputStream(Path.of(args[2]))) {
            out = XMLOutputFactory.newFactory().createXMLStreamWriter(stream, "UTF-8");
            out.writeStartDocument("UTF-8", "1.0");
            out.writeStartElement("choco-instances");
            attr("schema", "clafer-choco-instances/1");
            declarations(scope);
            out.flush();
            ClaferSolver solver;
            try {
                solver = ClaferCompiler.compile(model, scope);
            } catch (InsufficientScopeException error) {
                out.writeEmptyElement("search");
                attr("generated", 0);
                attr("termination", "insufficient_scope");
                attr("detail", error.getMessage());
                out.writeEndElement();
                out.writeEndDocument();
                out.close();
                return;
            }
            int count = 0;
            boolean exhausted = false;
            while (count < limit) {
                if (!solver.find()) { exhausted = true; break; }
                out.writeStartElement("instance");
                attr("index", count++);
                for (InstanceClafer value : solver.instance().getTopClafers()) object(value, null);
                out.writeEndElement();
                out.flush();
            }
            out.writeEmptyElement("search");
            attr("generated", count);
            attr("termination", exhausted ? "exhausted" : "limit");
            attr("detail", "");
            out.writeEndElement();
            out.writeEndDocument();
            out.close();
        }
    }
}
