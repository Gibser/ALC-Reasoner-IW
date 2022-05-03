package com.alcreasoning;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;

import org.eclipse.rdf4j.model.vocabulary.OWL;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLLogicalAxiom;
import org.semanticweb.owlapi.model.OWLObject;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
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
    
    private Pair<OWLClass, OWLClassExpression> concept;
    private OWLOntology tbox;
    private HashSet<OWLLogicalAxiom> tbox_set;
    private OWLDataFactory factory;
    private PrinterVisitor v;
    private AtomicConceptVisitor atomic_visitor;
    private OrAndPreprocessorVisitor or_and_preproc_visitor;

    /*
    public OntologyPreprocessor(String concept_path, String tbox_path){
        File concept_file = new File(concept_path);
        File tbox_file = new File(tbox_path);
        this.factory = concept_man.getOWLDataFactory();
        this.v = new FunnyVisitor();
        this.atomic_visitor = new AtomicConceptVisitor();
        this.or_and_preproc_visitor = new OrAndPreprocessorVisitor();
        this.tbox_set = new HashSet<>();

        try{
            this.tbox = tbox_man.loadOntologyFromOntologyDocument(tbox_file);
            this.concept = concept_man.loadOntologyFromOntologyDocument(concept_file);
        }catch(OWLOntologyCreationException e){
            e.printStackTrace();
        }
    }
    */

    // TBox non vuota
    public OntologyPreprocessor(String tbox_path){
        File tbox_file = new File(tbox_path);
        this.factory = tbox_man.getOWLDataFactory();
        this.v = new PrinterVisitor();
        this.atomic_visitor = new AtomicConceptVisitor();
        this.or_and_preproc_visitor = new OrAndPreprocessorVisitor();
        this.tbox_set = new HashSet<>();

        try{
            this.tbox = tbox_man.loadOntologyFromOntologyDocument(tbox_file);
        }catch(OWLOntologyCreationException e){
            e.printStackTrace();
        }
    }


    public void set_concept(Pair<OWLClass, OWLClassExpression> concept){
        this.concept = concept;
    }

    public OWLOntology getTBox(){
        return this.tbox;
    }

    public OWLDataFactory getFactory(){
        return this.factory;
    }

    public IRI get_tbox_ontology_IRI(){
        return this.tbox.getOntologyID().getOntologyIRI().get();
    }

    private OWLClassExpression preprocess_subclassof(OWLSubClassOfAxiom subclassof){
        OWLClassExpression not_a = this.factory.getOWLObjectComplementOf(subclassof.getSubClass()).getNNF();
        OWLClassExpression b = subclassof.getSuperClass();
        HashSet<OWLClassExpression> operands = new HashSet<>();
        
        if(not_a instanceof OWLObjectUnionOf)
            operands.addAll(((OWLObjectUnionOf)not_a).getOperandsAsList());
        else
            operands.add(not_a);

    
        if(b instanceof OWLObjectUnionOf)
            operands.addAll(((OWLObjectUnionOf)b).getOperandsAsList());
        else
            operands.add(b);
        
        OWLClassExpression preprocess_subclass;
        if(operands.size() > 1)
            preprocess_subclass = this.factory.getOWLObjectUnionOf(operands);
        else
            preprocess_subclass = operands.iterator().next();
            
        return preprocess_subclass; 
    }

    private ArrayList<OWLClassExpression> preprocess_equivalence(OWLEquivalentClassesAxiom equivalence){
        ArrayList<OWLClassExpression> preprocessed_equivalence = new ArrayList<>();

        OWLClassExpression a = equivalence.getOperandsAsList().get(0);
        OWLClassExpression b = equivalence.getOperandsAsList().get(1);

        OWLSubClassOfAxiom a_in_b = factory.getOWLSubClassOfAxiom(a, b);
        OWLSubClassOfAxiom b_in_a = factory.getOWLSubClassOfAxiom(b, a);

        preprocessed_equivalence.add(this.preprocess_subclassof(a_in_b));
        preprocessed_equivalence.add(this.preprocess_subclassof(b_in_a));

        return preprocessed_equivalence; 
    }

    public Pair<HashSet<OWLClassExpression>, HashSet<OWLClassExpression>> preprocess_concept(){
        HashSet<OWLClassExpression> L_x = new HashSet<>();
        HashSet<OWLClassExpression> abox = new HashSet<>();

        //
        System.out.print("Concetto: ");
        this.concept.getKey().accept(this.v);
        System.out.print(" equivalent to ");
        this.concept.getValue().accept(this.v);
        System.out.println();
        //

        abox.add(this.concept.getKey());
        L_x.add(this.concept.getValue());
        return new Pair<HashSet<OWLClassExpression>, HashSet<OWLClassExpression>>(abox, L_x);
    }

    private OWLClassExpression preprocess_tbox(){
        HashSet<OWLClassExpression> preprocessed_tbox = new HashSet<>();
        OWLClassExpression conjunction = null;

        for(OWLLogicalAxiom ax : this.tbox_set){
            ///
            System.out.print("TBox: ");
            ax.getNNF().accept(v);
            System.out.println();
            ///
            if(ax instanceof OWLSubClassOfAxiom)
                preprocessed_tbox.add(preprocess_subclassof((OWLSubClassOfAxiom)ax.getNNF()));
            else if(ax instanceof OWLEquivalentClassesAxiom)
                preprocessed_tbox.addAll(this.preprocess_equivalence((OWLEquivalentClassesAxiom)ax.getNNF()));
        }
        if(preprocessed_tbox.size() > 1)
            conjunction = this.factory.getOWLObjectIntersectionOf(preprocessed_tbox);
        else if(preprocessed_tbox.size() == 1)
            conjunction = preprocessed_tbox.iterator().next();
        return conjunction;
    }

    private HashSet<OWLLogicalAxiom> convert_disjointness(OWLDisjointClassesAxiom disj){
        HashSet<OWLLogicalAxiom> preprocessed_disj = new HashSet<>();
        for(OWLDisjointClassesAxiom ex : ((OWLDisjointClassesAxiom)disj).asPairwiseAxioms()){
            preprocessed_disj.add(this.factory.getOWLSubClassOfAxiom(ex.getOperandsAsList().get(0), ex.getOperandsAsList().get(1).getComplementNNF()));
        }
        return preprocessed_disj;
    }

    /*
    private OWLClassExpression preprocess_disjointness(OWLDisjointClassesAxiom disjointness){
        return this.preprocess_subclassof(this.convert_disjointness(disjointness));
    }
    */

    private OWLClassExpression preprocess_tbox(HashSet<OWLLogicalAxiom> T_g){
        HashSet<OWLClassExpression> preprocessed_tbox = new HashSet<>();
        OWLClassExpression conjunction = null;

        for(OWLLogicalAxiom ax : T_g){
            ///
            System.out.print("TBox: ");
            ax.getNNF().accept(v);
            System.out.println();
            ///
            if(ax instanceof OWLSubClassOfAxiom)
                preprocessed_tbox.add(preprocess_subclassof((OWLSubClassOfAxiom)ax.getNNF()));
            else if(ax instanceof OWLEquivalentClassesAxiom)
                preprocessed_tbox.addAll(this.preprocess_equivalence((OWLEquivalentClassesAxiom)ax.getNNF()));
            /*
            else if(ax instanceof OWLDisjointClassesAxiom)
                // Con inclusioni pairwise
                for(OWLDisjointClassesAxiom ex : ((OWLDisjointClassesAxiom)ax).asPairwiseAxioms()){
                    this.factory.getOWLSubClassOfAxiom(ex.getOperandsAsList().get(0), this.factory.getOWLObjectComplementOf(ex.getOperandsAsList().get(1))).accept(this.v);
                    System.out.println();
                    preprocessed_tbox.add(this.preprocess_subclassof(this.factory.getOWLSubClassOfAxiom(ex.getOperandsAsList().get(0), this.factory.getOWLObjectComplementOf(ex.getOperandsAsList().get(1)))));
                }
            */
        }
        if(preprocessed_tbox.size() > 1)
            conjunction = this.factory.getOWLObjectIntersectionOf(preprocessed_tbox);
        else if(preprocessed_tbox.size() == 1)
            conjunction = preprocessed_tbox.iterator().next();
        
        if(conjunction != null){
            System.out.println("\n");
            conjunction.accept(this.v);
            System.out.println("\n");
        }
        return conjunction;
    }

    public Pair<OWLClassExpression, Pair<HashSet<OWLClassExpression>, HashSet<OWLClassExpression>>> preprocess_tbox_and_concept(){
        Pair<HashSet<OWLClassExpression>, HashSet<OWLClassExpression>> KB = this.preprocess_concept();
        OWLClassExpression Ĉ = this.preprocess_tbox();
        
        if(Ĉ != null){
            KB.getValue().add(Ĉ);
            KB.getKey().add(Ĉ);
        }
        Pair<OWLClassExpression, Pair<HashSet<OWLClassExpression>, HashSet<OWLClassExpression>>> ret = new Pair<>(Ĉ, KB);

        return ret;
    }

    public Pair<OWLClassExpression, Pair<HashSet<OWLClassExpression>, HashSet<OWLClassExpression>>> preprocess_tbox_and_concept(HashSet<OWLLogicalAxiom> T_g){
        Pair<HashSet<OWLClassExpression>, HashSet<OWLClassExpression>> KB = this.preprocess_concept();
        OWLClassExpression Ĉ = this.preprocess_tbox(T_g);
        
        if(Ĉ != null){
            KB.getValue().add(Ĉ);
            KB.getKey().add(Ĉ);
        }

        Pair<OWLClassExpression, Pair<HashSet<OWLClassExpression>, HashSet<OWLClassExpression>>> ret = new Pair<>(Ĉ, KB);

        return ret;
    }

    public void preprocess_and_or_tbox(){
        for(OWLLogicalAxiom axm : this.tbox.getLogicalAxioms()){
            if(axm instanceof OWLDisjointClassesAxiom)
                this.convert_disjointness((OWLDisjointClassesAxiom)axm).stream()
                                    .forEach(disj_axm -> {disj_axm.accept(this.or_and_preproc_visitor);
                                                          this.tbox_set.add(this.or_and_preproc_visitor.getLogicalAxiom());
                                                         });
            else if(axm instanceof OWLObjectPropertyDomainAxiom){
                OWLObjectSomeValuesFrom expr = this.factory.getOWLObjectSomeValuesFrom(((OWLObjectPropertyDomainAxiom)axm).getProperty(), this.factory.getOWLNothing());
                OWLSubClassOfAxiom processed_domain_axiom = this.factory.getOWLSubClassOfAxiom(expr, ((OWLObjectPropertyDomainAxiom)axm).getDomain());
                this.tbox_set.add(processed_domain_axiom);
            }
            else if(axm instanceof OWLObjectPropertyRangeAxiom){
                OWLObjectAllValuesFrom expr = this.factory.getOWLObjectAllValuesFrom(((OWLObjectPropertyRangeAxiom)axm).getProperty(), ((OWLObjectPropertyRangeAxiom)axm).getRange());
                OWLSubClassOfAxiom processed_range_axiom = this.factory.getOWLSubClassOfAxiom(this.factory.getOWLThing(), expr);
                this.tbox_set.add(processed_range_axiom);
            }
            else{
                axm.getNNF().accept(this.or_and_preproc_visitor);
                this.tbox_set.add(this.or_and_preproc_visitor.getLogicalAxiom());
            }
            
        }
    }

    private OWLClass get_atomic_left_side(OWLLogicalAxiom axm){
        if(!this.is_left_side_atomic(axm))
            return null;

        if(axm instanceof OWLEquivalentClassesAxiom)
            return (OWLClass)((OWLEquivalentClassesAxiom)axm).getOperandsAsList().get(0);
        else if(axm instanceof OWLSubClassOfAxiom)
            return (OWLClass)((OWLSubClassOfAxiom)axm).getSubClass();
        else
            return null;
    }

    private HashSet<OWLClass> get_right_side(OWLLogicalAxiom axm){
        axm.accept(this.atomic_visitor);
        this.atomic_visitor.get_left_side_concepts_and_clear();
        return this.atomic_visitor.get_right_side_concepts_and_clear();
    }

    private boolean is_left_side_atomic(OWLLogicalAxiom axm){
        if(axm instanceof OWLEquivalentClassesAxiom)
            return ((OWLEquivalentClassesAxiom)axm).getOperandsAsList().get(0) instanceof OWLClass;
        else if(axm instanceof OWLSubClassOfAxiom)
            return ((OWLSubClassOfAxiom)axm).getSubClass() instanceof OWLClass;
        else
            return false;
    }

    private boolean is_axiom_acyclic(OWLLogicalAxiom axm){
        axm.accept(this.atomic_visitor);
        HashSet<OWLClass> left_side = this.atomic_visitor.get_left_side_concepts_and_clear();
        HashSet<OWLClass> right_side = this.atomic_visitor.get_right_side_concepts_and_clear();

        return !right_side.containsAll(left_side);
    }

    private boolean is_class_not_in_left_side(OWLClass concept, HashSet<OWLClass> left_side_T_u){
        return !left_side_T_u.contains(concept);
    }

    private boolean is_T_u_graph_acyclic(OWLLogicalAxiom axm, HashSet<OWLClass> left_side_T_u, HashSet<OWLClass> right_side_T_u){
        axm.accept(this.atomic_visitor);
        HashSet<OWLClass> left_side = this.atomic_visitor.get_left_side_concepts_and_clear();
        HashSet<OWLClass> right_side = this.atomic_visitor.get_right_side_concepts_and_clear();

        HashSet<OWLClass> left_right_intersection = new HashSet<>(left_side_T_u);
        HashSet<OWLClass> right_left_intersection = new HashSet<>(right_side_T_u);
        
        left_right_intersection.retainAll(right_side);
        right_left_intersection.retainAll(left_side);

        boolean left_right_not_present = left_right_intersection.size() == 0;
        boolean right_left_not_present = right_left_intersection.size() == 0;

        return right_left_not_present || left_right_not_present;

    }

    public Pair<HashSet<OWLLogicalAxiom>, HashSet<OWLLogicalAxiom>> partition_TBox(){
        this.preprocess_and_or_tbox();
        
        HashSet<OWLLogicalAxiom> T_g = new HashSet<>();
        HashSet<OWLLogicalAxiom> T_u = new HashSet<>();

        HashSet<OWLClass> left_side_T_u = new HashSet<>();
        HashSet<OWLClass> right_side_T_u = new HashSet<>();

        for(OWLLogicalAxiom axm : this.tbox_set){
            //axm.accept(this.v);
            if(!is_left_side_atomic(axm))
                T_g.add(axm);
            else{
                if(
                      this.is_axiom_acyclic(axm)                                                       &&
                      this.is_class_not_in_left_side(this.get_atomic_left_side(axm), left_side_T_u)    &&
                      this.is_T_u_graph_acyclic(axm, left_side_T_u, right_side_T_u)                        
                  ){
                    T_u.add(axm);
                    left_side_T_u.add(this.get_atomic_left_side(axm));
                    right_side_T_u.addAll(this.get_right_side(axm));
                   }
                else
                    T_g.add(axm);
            } 
        }
        return new Pair<HashSet<OWLLogicalAxiom>, HashSet<OWLLogicalAxiom>>(T_g, T_u);
    }
    
}
