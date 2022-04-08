package com.alcreasoning;

import java.util.HashSet;

import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLObject;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLObjectVisitor;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;


/**
    OWLObjectVisitor che estrae i concetti atomici dalla parte sinistra e destra di un assioma
*/
public class AtomicConceptVisitor implements OWLObjectVisitor{

    private HashSet<OWLClass> concepts;
    private HashSet<OWLClass> right_side_concepts;
    private HashSet<OWLClass> left_side_concepts;
    
    public AtomicConceptVisitor(){
        this.right_side_concepts = new HashSet<>();
        this.left_side_concepts = new HashSet<>();
        this.concepts = new HashSet<>();
    }

    private void add_and_clear_left_side(){
        this.left_side_concepts.addAll(this.concepts);
        this.concepts.clear();
    }

    private void add_and_clear_right_side(){
        this.right_side_concepts.addAll(this.concepts);
        this.concepts.clear();
    }

    public void visit(OWLEquivalentClassesAxiom axm){
        axm.getOperandsAsList().get(0).accept(this);
        add_and_clear_left_side();
        axm.getOperandsAsList().get(1).accept(this);
        add_and_clear_right_side();
    }

    public void visit(OWLSubClassOfAxiom axm){
        axm.getSubClass().accept(this);
        add_and_clear_left_side();
        axm.getSuperClass().accept(this);
        add_and_clear_right_side();
    }
    
    public void visit(OWLObjectSomeValuesFrom expr){
        expr.getFiller().accept(this);
    }

    public void visit(OWLObjectAllValuesFrom expr){
        expr.getFiller().accept(this);
    }

    public void visit(OWLObjectComplementOf ce) {
        ce.getOperand().accept(this);
    }

    public void visit(OWLClass atomic_concept){
        this.concepts.add(atomic_concept);
    }

    public void visit(OWLObjectIntersectionOf intersection) {
        for(OWLClassExpression c : intersection.getOperands()){
            c.accept(this);
        }
    }

    public void visit(OWLObjectUnionOf intersection) {
        for(OWLClassExpression c : intersection.getOperands()){
            c.accept(this);
        }
    }

    public HashSet<OWLClass> get_left_side_concepts_and_clear(){
        HashSet<OWLClass> temp;
        temp = (HashSet<OWLClass>)this.left_side_concepts.clone();
        this.left_side_concepts.clear();
        return temp;
    }

    public HashSet<OWLClass> get_right_side_concepts_and_clear(){
        HashSet<OWLClass> temp;
        temp = (HashSet<OWLClass>)this.right_side_concepts.clone();
        this.right_side_concepts.clear();
        return temp;
    }

}
