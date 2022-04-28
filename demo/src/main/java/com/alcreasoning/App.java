package com.alcreasoning;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.expression.ShortFormEntityChecker;
import org.semanticweb.owlapi.manchestersyntax.renderer.ParserException;
import org.semanticweb.owlapi.model.OWLAnnotationProperty;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDeclarationAxiom;
import org.semanticweb.owlapi.model.OWLLogicalAxiom;
import org.semanticweb.owlapi.model.OWLObject;
import org.semanticweb.owlapi.util.BidirectionalShortFormProvider;
import org.semanticweb.owlapi.util.BidirectionalShortFormProviderAdapter;
import org.semanticweb.owlapi.util.ShortFormProvider;
import org.semanticweb.owlapi.util.mansyntax.ManchesterOWLSyntaxParser;
import org.semanticweb.owlapi.util.AnnotationValueShortFormProvider;
import guru.nidi.graphviz.attribute.Color;
import guru.nidi.graphviz.attribute.Font;
import guru.nidi.graphviz.attribute.Label;
import guru.nidi.graphviz.attribute.Rank;
import guru.nidi.graphviz.attribute.Style;
import guru.nidi.graphviz.engine.Format;
import guru.nidi.graphviz.engine.Graphviz;
import guru.nidi.graphviz.model.Graph;
import guru.nidi.graphviz.model.MutableGraph;
import guru.nidi.graphviz.model.MutableNode;

import static guru.nidi.graphviz.model.Factory.*;

import javafx.util.Pair;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.time.Duration;
import java.time.Instant;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;


import org.apache.jena.*;
import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.ModelFactory;
import org.apache.jena.rdf.model.Resource;
import org.apache.jena.vocabulary.VCARD;
import org.checkerframework.checker.regex.qual.PartialRegex;

public final class App {
    private App() {
    }

    static Pair<OWLClass, OWLClassExpression> get_concept_from_input(OntologyPreprocessor preproc){
        BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));
        System.out.println("Enter concept name: ");
    	String concept_name = null;
    	try {
    		concept_name = new String(reader.readLine());
		} catch (IOException e) {
			e.printStackTrace();
		}

    	System.out.println("Enter concept: ");
    	String concept = null;
    	try {
    		concept = new String(reader.readLine());
		} catch (IOException e) {
			e.printStackTrace();
		}

        ShortFormProvider sfp =
        new AnnotationValueShortFormProvider(Arrays.asList(preproc.getFactory().getRDFSLabel()),
            Collections.<OWLAnnotationProperty, List<String>>emptyMap(), OntologyPreprocessor.tbox_man);

        BidirectionalShortFormProvider shortFormProvider =
        new BidirectionalShortFormProviderAdapter(OntologyPreprocessor.tbox_man.getOntologies(), sfp);
        ShortFormEntityChecker owlEntityChecker = new ShortFormEntityChecker(shortFormProvider);
        
        ManchesterOWLSyntaxParser parser = OWLManager.createManchesterParser();
        parser.setOWLEntityChecker(owlEntityChecker);
        parser.setDefaultOntology(preproc.getTBox());


        OWLClass c_name = preproc.getFactory().getOWLClass(preproc.getTBox().getOntologyID().getOntologyIRI().get() + "#" + concept_name);

        OWLClassExpression class_exp = parser.parseClassExpression(concept).getNNF();

        OWLDeclarationAxiom concept_declaration = preproc.getFactory().getOWLDeclarationAxiom(c_name);
        preproc.getTBox().add(concept_declaration);

        return new Pair<OWLClass, OWLClassExpression>(c_name, class_exp);
    }

    public static void main(String[] args) {
        /*
        // some definitions
        String personURI    = "http://somewhere/JohnSmith";
        String fullName     = "John Smith";

        // create an empty Model
        Model model = ModelFactory.createDefaultModel();

        // create the resource
        Resource johnSmith = model.createResource(personURI);

        // add the property
        johnSmith.addProperty(VCARD.FN, fullName);
        
        model.write(System.out);

        */

        ///////nord
        FunnyVisitor v = new FunnyVisitor();
        OrAndPreprocessorVisitor p = new OrAndPreprocessorVisitor();
        AtomicConceptVisitor n = new AtomicConceptVisitor();

        OntologyPreprocessor preproc = new OntologyPreprocessor("KB_12.owl");
        Pair<OWLClass, OWLClassExpression> concept = null;
        try{
             concept = get_concept_from_input(preproc);
        }
        catch(ParserException e){
            System.out.println("Errore parsing; Definire i concetti atomici, le relazioni, owl:Thing e owl:Nothing nella KB passata in input.");
            return;
        }
        //concept.getValue().accept(v);
        preproc.set_concept(concept);
        
        System.out.println("\n\n\nLogical Axioms:\n");
        

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
        System.out.println(System.getProperty("user.dir"));
        Pair<HashSet<OWLLogicalAxiom>, HashSet<OWLLogicalAxiom>> partition = preproc.partition_TBox();
        System.out.print("\nT_g = {");
        partition.getKey().stream().forEach(e -> {e.accept(v); System.out.print(", ");});
        System.out.println("}");
        System.out.print("T_u = {");
        partition.getValue().stream().forEach(e -> {e.accept(v); System.out.print(", ");});
        System.out.println("}");
        //Pair<OWLClassExpression, Pair<HashSet<OWLObject>, HashSet<OWLObject>>> KB_and_Ĉ = preproc.preprocess_tbox_and_concept(partition.getKey());
        Pair<OWLClassExpression, Pair<HashSet<OWLObject>, HashSet<OWLObject>>> KB_and_Ĉ = preproc.preprocess_tbox_and_concept();
        Reasoner r = new Reasoner(KB_and_Ĉ.getKey(), KB_and_Ĉ.getValue().getKey(), KB_and_Ĉ.getValue().getValue(), preproc.get_tbox_ontology_IRI(), false);
        
        System.out.println(r.check_consistency("./graphs/", false));
        
    }

}