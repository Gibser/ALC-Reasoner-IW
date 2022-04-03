package com.alcreasoning;
import java.io.File;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLObject;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLObjectVisitor;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
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
        
        Set<OWLObject> rule_list = new HashSet<OWLObject>();

        FunnyVisitor v = new FunnyVisitor();
        
        OWLObjectVisitor and_visitor = new OWLObjectVisitor() {
            
            public void visit(OWLEquivalentClassesAxiom ax) {
                ax.getOperandsAsList().get(1).accept(this);             
            }

            public void visit(OWLObjectIntersectionOf intersection) {
                for(OWLClassExpression c : intersection.getOperands()){
                    rule_list.add(c);
                }
            }
        };
        
        OWLObjectVisitor or_visitor = new OWLObjectVisitor() {
            
            public void visit(OWLEquivalentClassesAxiom ax) {
                ax.getOperandsAsList().get(1).accept(this);             
            }

            public void visit(OWLObjectUnionOf intersection) {
                for(OWLClassExpression c : intersection.getOperands()){
                    rule_list.add(c);
                }
            }
        };

        try {
            OWLOntology o = man.loadOntologyFromOntologyDocument(file);
            //System.out.println(o.getLogicalAxioms());
            for(OWLAxiom ax : o.getLogicalAxioms()){
                    System.out.println(ax.getNNF());
                    ax.getNNF().accept(or_visitor);

                    for(OWLObject obj : rule_list){
                        obj.accept(v);
                        System.out.println();
                    }

                    //((OWLEquivalentClassesAxiom)ax).namedClasses().forEach(System.out::println);
                    System.out.println("\n\n");
            }
            //o.logicalAxioms().forEach(System.out::println);
        } catch (OWLOntologyCreationException e) {
            e.printStackTrace();
        }
    }

    public List<OWLObject> and_rule(OWLAxiom ax){

        return null;
    }
}
