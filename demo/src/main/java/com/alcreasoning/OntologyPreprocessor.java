package com.alcreasoning;

import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLLogicalAxiom;
import org.semanticweb.owlapi.model.OWLObject;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLObjectVisitor;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;

import javafx.util.Pair;

public class OntologyPreprocessor {
    
    public static OWLOntologyManager concept_man = OWLManager.createOWLOntologyManager();
    public static OWLOntologyManager tbox_man = OWLManager.createOWLOntologyManager();

    private OWLOntology concept;
    private OWLOntology tbox;
    private OWLDataFactory factory;
    private FunnyVisitor v;

    public OntologyPreprocessor(String concept_path, String tbox_path){
        File concept_file = new File(concept_path);
        File tbox_file = new File(tbox_path);
        this.factory = concept_man.getOWLDataFactory();
        this.v = new FunnyVisitor();

        try{
            this.tbox = tbox_man.loadOntologyFromOntologyDocument(tbox_file);
            this.concept = concept_man.loadOntologyFromOntologyDocument(concept_file);
        }catch(OWLOntologyCreationException e){
            e.printStackTrace();
        }
    }

    public OntologyPreprocessor(String concept_path){
        File concept_file = new File(concept_path);
        this.factory = tbox_man.getOWLDataFactory();
        this.v = new FunnyVisitor();

        try{
            this.concept = tbox_man.loadOntologyFromOntologyDocument(concept_file);
        }catch(OWLOntologyCreationException e){
            e.printStackTrace();
        }
    }

    public OWLOntology getTBox(){
        return this.tbox;
    }

    public IRI get_concept_ontology_IRI(){
        return this.concept.getOntologyID().getOntologyIRI().get();
    }

    public IRI get_tbox_ontology_IRI(){
        return this.tbox.getOntologyID().getOntologyIRI().get();
    }

    private OWLObjectUnionOf preprocess_subclassof(OWLSubClassOfAxiom subclassof){
        OWLClassExpression not_a = this.factory.getOWLObjectComplementOf(subclassof.getSubClass()).getNNF();
        OWLClassExpression b = subclassof.getSuperClass();
        ArrayList<OWLClassExpression> operands = new ArrayList<>();
        
        if(not_a instanceof OWLObjectUnionOf)
            operands.addAll(((OWLObjectUnionOf)not_a).getOperandsAsList());
        else
            operands.add(not_a);

    
        if(b instanceof OWLObjectUnionOf)
            operands.addAll(((OWLObjectUnionOf)b).getOperandsAsList());
        else
            operands.add(b);
        
        OWLObjectUnionOf preprocess_subclass = this.factory.getOWLObjectUnionOf(operands);

        return preprocess_subclass; 
    }

    private ArrayList<OWLObjectUnionOf> preprocess_equivalence(OWLEquivalentClassesAxiom equivalence){
        ArrayList<OWLObjectUnionOf> preprocessed_equivalence = new ArrayList<>();

        OWLClassExpression a = equivalence.getOperandsAsList().get(0);
        OWLClassExpression b = equivalence.getOperandsAsList().get(1);

        OWLSubClassOfAxiom a_in_b = factory.getOWLSubClassOfAxiom(a, b);
        OWLSubClassOfAxiom b_in_a = factory.getOWLSubClassOfAxiom(b, a);

        preprocessed_equivalence.add(this.preprocess_subclassof(a_in_b));
        preprocessed_equivalence.add(this.preprocess_subclassof(b_in_a));

        return preprocessed_equivalence; 
    }

    public Pair<HashSet<OWLObject>, HashSet<OWLObject>> preprocess_concept(){
        HashSet<OWLObject> L_x = new HashSet<>();
        HashSet<OWLObject> abox = new HashSet<>();

        OWLObjectVisitor eq = new OWLObjectVisitor() {
            public void visit(OWLEquivalentClassesAxiom ax) {
                abox.add(ax.getOperandsAsList().get(0));  
                L_x.add(ax.getOperandsAsList().get(1));   
            }
        };

        for(OWLLogicalAxiom ax : this.concept.getLogicalAxioms()){
            ///
            System.out.print("Concetto: ");
            ax.getNNF().accept(v);
            System.out.println();
            ///
            ax.getNNF().accept(eq);
        }
        
        return new Pair<HashSet<OWLObject>, HashSet<OWLObject>>(abox, L_x);
    }

    private OWLClassExpression preprocess_tbox(){
        HashSet<OWLClassExpression> preprocessed_tbox = new HashSet<>();
        OWLClassExpression conjunction = null;

        for(OWLLogicalAxiom ax : this.tbox.getLogicalAxioms()){
            ///
            System.out.print("TBox: ");
            ax.getNNF().accept(v);
            System.out.println();
            ///
            if(ax instanceof OWLSubClassOfAxiom)
                preprocessed_tbox.add(preprocess_subclassof((OWLSubClassOfAxiom)ax));
            else if(ax instanceof OWLEquivalentClassesAxiom)
                preprocessed_tbox.addAll(this.preprocess_equivalence((OWLEquivalentClassesAxiom)ax));
        }
        if(preprocessed_tbox.size() > 1)
            conjunction = this.factory.getOWLObjectIntersectionOf(preprocessed_tbox);
        else if(preprocessed_tbox.size() == 1)
            conjunction = preprocessed_tbox.iterator().next();
        return conjunction;
    }

    public Pair<OWLClassExpression, Pair<HashSet<OWLObject>, HashSet<OWLObject>>> preprocess_tbox_and_concept(){
        Pair<HashSet<OWLObject>, HashSet<OWLObject>> KB = this.preprocess_concept();
        OWLClassExpression Ĉ = this.preprocess_tbox();

        KB.getValue().add(Ĉ);
        KB.getKey().add(Ĉ);

        Pair<OWLClassExpression, Pair<HashSet<OWLObject>, HashSet<OWLObject>>> ret = new Pair<>(Ĉ, KB);

        return ret;
    }
    
}
