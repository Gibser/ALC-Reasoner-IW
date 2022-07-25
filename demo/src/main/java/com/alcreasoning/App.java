package com.alcreasoning;

import com.alcreasoning.visitors.AllVisitors;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.expression.ShortFormEntityChecker;
import org.semanticweb.owlapi.manchestersyntax.renderer.ParserException;
import org.semanticweb.owlapi.model.OWLAnnotationProperty;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDeclarationAxiom;
import org.semanticweb.owlapi.model.OWLLogicalAxiom;
import org.semanticweb.owlapi.util.BidirectionalShortFormProvider;
import org.semanticweb.owlapi.util.BidirectionalShortFormProviderAdapter;
import org.semanticweb.owlapi.util.ShortFormProvider;
import org.semanticweb.owlapi.util.mansyntax.ManchesterOWLSyntaxParser;
import org.semanticweb.owlapi.util.AnnotationValueShortFormProvider;

import javafx.util.Pair;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;

public final class App {
    private App() {
    }

    public static void main(String[] args) {

        OntologyPreprocessor preproc = new OntologyPreprocessor("blocking_example.owl");
        Pair<OWLClass, OWLClassExpression> concept = null;

        
        try {
            concept = get_concept_from_input(preproc);
        } catch (ParserException e) {
            System.out.println(
                    "Errore parsing; Definire i concetti atomici, le relazioni, owl:Thing e owl:Nothing nella KB passata in input.");
            return;
        } catch (IOException e) {
            System.out.println("Errore in lettura; La lettura degli elementi in input è fallita.");
            return;
        }

        preproc.set_concept(concept);
        System.out.println("\n\n\nLogical Axioms:\n");
        
        
        for (OWLAxiom ax : preproc.getTBox().getLogicalAxioms()) {
            System.out.print("Assioma: ");
            ax.getNNF().accept(AllVisitors.printer_visitor);
            System.out.println();
        }
        System.out.println();
        
        System.out.println(run_tableau(true, true, "./graphs/", preproc));

    }

    static String run_tableau(boolean lazy_unfolding, boolean draw_graph, String save_path, OntologyPreprocessor preproc){

        Reasoner r = build_reasoner_for_tableau(lazy_unfolding, preproc, draw_graph);
        
        return "\nSoddisfacibile: " + r.check_consistency(save_path, lazy_unfolding) + "\n";
    }

    static Pair<OWLClass, OWLClassExpression> get_concept_from_input(OntologyPreprocessor preproc) throws IOException {

        BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));

        System.out.println("Enter concept name: ");
        String concept_name = null;
        concept_name = new String(reader.readLine());

        System.out.println("Enter concept: ");
        String concept = null;
        concept = new String(reader.readLine());

        ShortFormProvider sfp = new AnnotationValueShortFormProvider(Arrays.asList(preproc.getFactory().getRDFSLabel()),
                Collections.<OWLAnnotationProperty, List<String>>emptyMap(), OntologyPreprocessor.tbox_man);

        BidirectionalShortFormProvider shortFormProvider = new BidirectionalShortFormProviderAdapter(
                OntologyPreprocessor.tbox_man.getOntologies(), sfp);

        ShortFormEntityChecker owlEntityChecker = new ShortFormEntityChecker(shortFormProvider);

        ManchesterOWLSyntaxParser parser;
        parser = OWLManager.createManchesterParser();
        parser.setOWLEntityChecker(owlEntityChecker);
        parser.setDefaultOntology(preproc.getTBox());

        OWLClass c_name = preproc.getFactory()
                .getOWLClass(preproc.getTBox().getOntologyID().getOntologyIRI().get() + "#" + concept_name);

        OWLClassExpression class_exp = parser.parseClassExpression(concept).getNNF();

        OWLDeclarationAxiom concept_declaration = preproc.getFactory().getOWLDeclarationAxiom(c_name);
        preproc.getTBox().add(concept_declaration);

        return new Pair<OWLClass, OWLClassExpression>(c_name, class_exp);
    }

    static Pair<OWLClass, OWLClassExpression> get_concept_from_string(OntologyPreprocessor preproc, String input){

        ShortFormProvider sfp = new AnnotationValueShortFormProvider(Arrays.asList(preproc.getFactory().getRDFSLabel()),
                Collections.<OWLAnnotationProperty, List<String>>emptyMap(), OntologyPreprocessor.tbox_man);

        BidirectionalShortFormProvider shortFormProvider = new BidirectionalShortFormProviderAdapter(
                OntologyPreprocessor.tbox_man.getOntologies(), sfp);

        ShortFormEntityChecker owlEntityChecker = new ShortFormEntityChecker(shortFormProvider);

        ManchesterOWLSyntaxParser parser;
        parser = OWLManager.createManchesterParser();
        parser.setOWLEntityChecker(owlEntityChecker);
        parser.setDefaultOntology(preproc.getTBox());

        OWLClass c_name = preproc.getFactory()
                .getOWLClass(preproc.getTBox().getOntologyID().getOntologyIRI().get() + "#Z");

        OWLClassExpression class_exp = parser.parseClassExpression(input).getNNF();

        OWLDeclarationAxiom concept_declaration = preproc.getFactory().getOWLDeclarationAxiom(c_name);
        preproc.getTBox().add(concept_declaration);

        return new Pair<OWLClass, OWLClassExpression>(c_name, class_exp);
    }
    
    static void print_T_g_T_u(Pair<HashSet<OWLLogicalAxiom>, HashSet<OWLLogicalAxiom>> T_g_and_T_u){
        int i = 0;
        System.out.print("\nT_g = {");
        for(OWLLogicalAxiom ax : T_g_and_T_u.getKey()){
            ax.accept(AllVisitors.printer_visitor);
            if(i++ < T_g_and_T_u.getKey().size()-1) System.out.print(", ");
        }
        System.out.println("}");
        i = 0;
        System.out.print("T_u = {");
        for(OWLLogicalAxiom ax : T_g_and_T_u.getValue()){
            ax.accept(AllVisitors.printer_visitor);
            if(i++ < T_g_and_T_u.getValue().size()-1) System.out.print(", ");
        }
        System.out.println("}");
    }

    static Reasoner build_reasoner_for_tableau(boolean lazy_unfolding, OntologyPreprocessor preprocessor, boolean draw_graph){

        Reasoner r;

        if(lazy_unfolding){
            Pair<HashSet<OWLLogicalAxiom>, HashSet<OWLLogicalAxiom>> T_g_and_T_u = preprocessor.partition_TBox();
 
            //////Fase di stampa di T_g e T_u
            System.out.println("-------------------\nLazy unfolding\n-------------------");
            print_T_g_T_u(T_g_and_T_u);
            //////
            
            Pair<OWLClassExpression, Pair<HashSet<OWLClassExpression>, HashSet<OWLClassExpression>>> KB_and_Ĉ = preprocessor.preprocess_tbox_and_concept(T_g_and_T_u.getKey());
            r = new Reasoner(KB_and_Ĉ.getKey(), T_g_and_T_u.getValue(), KB_and_Ĉ.getValue().getKey(), KB_and_Ĉ.getValue().getValue(), preprocessor.get_tbox_ontology_IRI(), draw_graph);
        }
        else{
            preprocessor.preprocess_and_or_tbox();
            Pair<OWLClassExpression, Pair<HashSet<OWLClassExpression>, HashSet<OWLClassExpression>>> KB_and_Ĉ = preprocessor.preprocess_tbox_and_concept();
            r = new Reasoner(KB_and_Ĉ.getKey(), KB_and_Ĉ.getValue().getKey(), KB_and_Ĉ.getValue().getValue(), preprocessor.get_tbox_ontology_IRI(), draw_graph);
        }
        return r;
    }

    static void try_queries(OntologyPreprocessor preproc){
        String[] queries = {"Elf and useInCombat some Elf", "Human and useInCombat some Sword", "Human and useInCombat some Magic",
        "Orc and Human", "Human and Elf", "Elf and useInCombat some Magic", "Elf and useInCombat some Sword",
        "(Human and Orc) or ((useInCombat some (Sword or Magic)) and owl:Nothing) or (useInCombat some (Sword or Magic) and (useInCombat some Sword))"
       };
        for(String query : queries){
            preproc.set_concept(get_concept_from_string(preproc, query));
            System.out.println("Query: " + query);
            System.out.println(run_tableau(false, false, "./graphs/", preproc));
            System.out.println(run_tableau(false, true, "./graphs/", preproc));
            System.out.println(run_tableau(true, false, "./graphs/", preproc));
            System.out.println(run_tableau(true, true, "./graphs/", preproc));
            System.out.println("-----------------------------------------------");
        }
    }
}