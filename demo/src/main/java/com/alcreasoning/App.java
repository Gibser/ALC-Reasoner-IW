package com.alcreasoning;
import java.io.File;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLObject;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLObjectVisitor;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

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
        File file = new File("H:\\Università\\Progetto IW\\concept.owl");
        System.out.println("\n\n\nLogical Axioms:\n");
        HashSet<OWLObject> L_x = new HashSet<OWLObject>();
        HashSet<OWLObject> exs = new HashSet<OWLObject>();
        FunnyVisitor v = new FunnyVisitor();

        OWLObjectVisitor eq = new OWLObjectVisitor() {
            public void visit(OWLEquivalentClassesAxiom ax) {
                L_x.add(ax.getOperandsAsList().get(1));             
            }
        };
        try {
            OWLOntology o = man.loadOntologyFromOntologyDocument(file);
            Reasoner r = new Reasoner();
            AndVisitor and = new AndVisitor();
            //System.out.println(o.getLogicalAxioms());
            for(OWLAxiom ax : o.getLogicalAxioms()){ 
                ax.getNNF().accept(v);
                System.out.println();
                ax.getNNF().accept(eq);
                System.out.print(r.tableau_algorithm(0, L_x));
                //exs = and.get_rule_set_and_reset().stream().filter(e -> (e instanceof OWLObjectSomeValuesFrom)).collect(Collectors.toCollection(HashSet::new));
                //exs.stream().forEach(e -> e.accept(v));
                System.out.println("\n\n");
            }
            //o.logicalAxioms().forEach(System.out::println);
        } catch (OWLOntologyCreationException e) {
            e.printStackTrace();
        }
    }

}
