package com.alcreasoning;
import java.io.File;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLLogicalAxiom;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObject;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLObjectVisitor;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;

import javafx.util.Pair;

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
        // Implementare input C da prompt o campo testo
        // quindi va costruita con il data factory
        OntologyPreprocessor preproc = new OntologyPreprocessor("H:\\Università\\Progetto IW\\concept_person.owl", "H:\\Università\\Progetto IW\\prova_atomic_concepts.owl");
        System.out.println("\n\n\nLogical Axioms:\n");
        ///////nord
        FunnyVisitor v = new FunnyVisitor();
        OrAndPreprocessorVisitor p = new OrAndPreprocessorVisitor();
        AtomicConceptVisitor n = new AtomicConceptVisitor();

        for(OWLAxiom ax : preproc.getTBox().getLogicalAxioms()){
            System.out.print("Assioma: ");
            ax.getNNF().accept(v);
            System.out.println();
            /*
            System.out.print("\nPreprocessing: ");
            ax.getNNF().accept(p);
            p.getLogicalAxiom().accept(v);
            System.out.println("\n\n");
            System.out.print("\nLeft side = {");
            p.getLogicalAxiom().accept(n);
            n.get_left_side_concepts_and_clear().stream().forEach(e -> {e.accept(v); System.out.print(", ");});
            System.out.println("}");
            System.out.print("Right side = {");
            n.get_right_side_concepts_and_clear().stream().forEach(e -> {e.accept(v); System.out.print(", ");});
            System.out.println("}");
            */
        }

        Pair<HashSet<OWLLogicalAxiom>, HashSet<OWLLogicalAxiom>> partition = preproc.partition_TBox();
        System.out.print("\nT_g = {");
        partition.getKey().stream().forEach(e -> {e.accept(v); System.out.print(", ");});
        System.out.println("}");
        System.out.print("T_u = {");
        partition.getValue().stream().forEach(e -> {e.accept(v); System.out.print(", ");});
        System.out.println("}");
        //Pair<OWLClassExpression, Pair<HashSet<OWLObject>, HashSet<OWLObject>>> KB_and_Ĉ = preproc.preprocess_tbox_and_concept();

        //Reasoner r = new Reasoner(KB_and_Ĉ.getKey(), KB_and_Ĉ.getValue().getKey(), KB_and_Ĉ.getValue().getValue(), preproc.get_tbox_ontology_IRI());
        //System.out.println(r.check_consistency());

        /*
        try {
            OWLOntology o = man.loadOntologyFromOntologyDocument(file);
            
            IRI ontologyIRI = o.getOntologyID().getOntologyIRI().get();
            OWLDataFactory factory = man.getOWLDataFactory();
            OWLNamedIndividual x = factory.getOWLNamedIndividual(IRI.create(ontologyIRI + "#x_0"));
            AndVisitor and = new AndVisitor();
            //System.out.println(o.getLogicalAxioms());
            for(OWLAxiom ax : o.getLogicalAxioms()){ 
                ax.getNNF().accept(v);
                System.out.print("\nPreprocessing: ");
                if(ax instanceof OWLSubClassOfAxiom){
                    OWLObjectComplementOf not_A = factory.getOWLObjectComplementOf(((OWLSubClassOfAxiom)ax).getSubClass());
                    OWLObjectUnionOf preprocess_subclass = factory.getOWLObjectUnionOf(not_A, ((OWLSubClassOfAxiom)ax).getSuperClass());
                    preprocess_subclass.accept(v);
                }
                //System.out.println(ax);
                //ax.getNNF().accept(eq);
                //Reasoner r = new Reasoner(x, c.iterator().next(), factory, ontologyIRI);
                System.out.println();
                //System.out.print(r.tableau_algorithm(x, L_x, 0));
                //exs = and.get_rule_set_and_reset().stream().filter(e -> (e instanceof OWLObjectSomeValuesFrom)).collect(Collectors.toCollection(HashSet::new));
                //exs.stream().forEach(e -> e.accept(v));
                System.out.println("\n\n");
            }
            //o.logicalAxioms().forEach(System.out::println);
        } catch (OWLOntologyCreationException e) {
            e.printStackTrace();
        }
        */
    }

}