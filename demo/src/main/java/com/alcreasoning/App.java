package com.alcreasoning;

import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLLogicalAxiom;
import org.semanticweb.owlapi.model.OWLObject;

import javafx.util.Pair;

import java.util.HashSet;

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
        OntologyPreprocessor preproc = new OntologyPreprocessor("H:\\Università\\Progetto IW\\concept.owl", "H:\\Università\\Progetto IW\\prova_atomic_concepts.owl");
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
        Pair<OWLClassExpression, Pair<HashSet<OWLObject>, HashSet<OWLObject>>> KB_and_Ĉ = preproc.preprocess_tbox_and_concept(partition.getKey());
        Reasoner r = new Reasoner(KB_and_Ĉ.getKey(), partition.getValue(), KB_and_Ĉ.getValue().getKey(), KB_and_Ĉ.getValue().getValue(), preproc.get_tbox_ontology_IRI());
        System.out.println(r.check_consistency_lazy_unfolding());
    }

}