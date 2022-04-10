package com.alcreasoning;

import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLLogicalAxiom;
import org.semanticweb.owlapi.model.OWLObject;

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

import java.io.File;
import java.io.IOException;
import java.time.Duration;
import java.time.Instant;
import java.util.HashSet;

import org.apache.jena.*;
import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.ModelFactory;
import org.apache.jena.rdf.model.Resource;
import org.apache.jena.vocabulary.VCARD;


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

        /*
        // Graphviz
        MutableNode node = mutNode("x0").add((Label.of("L_x").external()));
        MutableGraph g = mutGraph("example1").setDirected(true);//.add(mutNode("a").add(Color.RED).add((Label.of("Alleikum").external())).addLink(mutNode("b")));
        //g.add(node.addLink());// .add((Label.of("L_x").external())));
        g.add(node.addLink(to(mutNode("x1")).with(Label.of("R"))));
        g.add(node.addLink(to(mutNode("x1")).with(Label.of("R"))));
        try{
            Graphviz.fromGraph(g).width(200).render(Format.PNG).toFile(new File("example/ex1i.png"));
        }
        catch(IOException ex){
            System.out.println("ALKASJHASDF");
        }
        */
        // Implementare input C da prompt o campo testo
        // quindi va costruita con il data factory
        OntologyPreprocessor preproc = new OntologyPreprocessor("H:\\Università\\Progetto IW\\prova.owl.xml", "H:\\Università\\Progetto IW\\prova_atomic_concepts.owl");
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
        //Pair<OWLClassExpression, Pair<HashSet<OWLObject>, HashSet<OWLObject>>> KB_and_Ĉ = preproc.preprocess_tbox_and_concept(partition.getKey());
        Pair<OWLClassExpression, Pair<HashSet<OWLObject>, HashSet<OWLObject>>> KB_and_Ĉ = preproc.preprocess_tbox_and_concept();
        Reasoner r = new Reasoner(KB_and_Ĉ.getKey(), KB_and_Ĉ.getValue().getKey(), KB_and_Ĉ.getValue().getValue(), preproc.get_tbox_ontology_IRI());
        Instant start = Instant.now();
        System.out.println(r.check_consistency());
        Instant end = Instant.now();
        System.out.println("\nElapsed Time: "+ Duration.between(start, end).toMillis()+"ms");
    }

}