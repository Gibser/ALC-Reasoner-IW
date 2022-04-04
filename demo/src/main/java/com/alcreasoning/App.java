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
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLObjectVisitor;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

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
        HashSet<OWLObject> rule_set = new HashSet<OWLObject>();
        FunnyVisitor v = new FunnyVisitor();
        AndVisitor and_visitor = new AndVisitor();
        OrVisitor or_visitor = new OrVisitor();

        try {
            OWLOntology o = man.loadOntologyFromOntologyDocument(file);
            //System.out.println(o.getLogicalAxioms());
            for(OWLAxiom ax : o.getLogicalAxioms()){
                    //System.out.println(ax.getNNF());
                    //ax.getNNF().accept(v);
                    ax.getNNF().accept(and_visitor);
                    rule_set.addAll(and_visitor.get_rule_set_and_reset());
                    /*
                    for(OWLObject obj : rule_set){
                        obj.accept(or_visitor);
                    }
                    */
                    //rule_set.addAll(or_visitor.get_rule_set_and_reset());
                    for(OWLObject obj : rule_set){
                        obj.accept(v);
                        System.out.println();
                    }

                    HashSet<OWLObject> atomic_concept = new HashSet<OWLObject>();
                    HashSet<OWLObject> not_atomic_concept = new HashSet<OWLObject>();

                    System.out.println();
                    for(OWLObject obj : rule_set){
                        if(obj instanceof OWLClass){
                           atomic_concept.add((OWLClass)obj);
                        }
                        else if(obj instanceof OWLObjectComplementOf){
                            not_atomic_concept.add((OWLObjectComplementOf) obj);
                        }
                    }

                    for(OWLObject obj : atomic_concept){
                        if(not_atomic_concept.contains(((OWLClass)obj).getObjectComplementOf())){
                            System.out.println("CLASH!");
                        }
                    }
                    //((OWLEquivalentClassesAxiom)ax).namedClasses().forEach(System.out::println);
                    System.out.println("\n\n");
            }
            //o.logicalAxioms().forEach(System.out::println);
        } catch (OWLOntologyCreationException e) {
            e.printStackTrace();
        }
    }

}
