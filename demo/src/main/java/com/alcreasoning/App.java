package com.alcreasoning;
import java.io.File;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectVisitor;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Hello world!
 */
public final class App {
    private App() {
    }

    /**
     * Says hello to the world.
     * @param args The arguments of the program.
     */
    public static void main(String[] args) {
        OWLOntologyManager man = OWLManager.createOWLOntologyManager();
        File file = new File("H:\\Università\\Progetto IW\\example.owl");
        System.out.println("\n\n\nLogical Axioms:\n");
        String pattern = "[^#]*#([a-zA-Z0-9]+)>$";
        Pattern r = Pattern.compile(pattern);
        OWLObjectVisitor v = new OWLObjectVisitor() {
            public void visit(OWLEquivalentClassesAxiom ax) {
                // this is an example of recursive visit
                //System.out.print(ax.getOperandsAsList().get(0).asOWLClass().getIRI().getShortForm());
                //System.out.print(" equiv ");
                List<OWLClassExpression> expr_list = ax.getClassExpressionsAsList();
                expr_list.get(0).accept(this);
                System.out.print(" equiv ");
                expr_list.get(1).accept(this);             
            }
        
            public void visit(OWLObjectSomeValuesFrom ce) {
                OWLObjectPropertyExpression p = ce.getProperty();
                System.out.print("exists ");
                Matcher m = r.matcher(p.toString());
                if(m.find()){
                    System.out.print(m.group(1));
                }
                ce.getFiller().accept(this);
            }

            public void visit(OWLObjectComplementOf ce) {
                System.out.print("not (");
                ce.getOperand().accept(this);
                System.out.print(")");
            }

            public void visit(OWLClass class_expr) {
                System.out.print(class_expr.getIRI().getShortForm());
            }

            public void visit(OWLObjectIntersectionOf intersection) {
                int list_len = intersection.getOperandsAsList().size(), i = 0;
                for(OWLClassExpression c : intersection.getOperands()){
                    c.accept(this);
                    if(++i < list_len){
                        System.out.print(" and ");
                    }
                }
            }
        };
        try {
            OWLOntology o = man.loadOntologyFromOntologyDocument(file);
            //System.out.println(o.getLogicalAxioms());
            for(OWLAxiom ax : o.getLogicalAxioms()){
                    //System.out.println(ax);
                    ax.accept(v);
                    //((OWLEquivalentClassesAxiom)ax).namedClasses().forEach(System.out::println);
                    System.out.println("\n\n");
            }
            //o.logicalAxioms().forEach(System.out::println);
        } catch (OWLOntologyCreationException e) {
            e.printStackTrace();
        }
    }
}
