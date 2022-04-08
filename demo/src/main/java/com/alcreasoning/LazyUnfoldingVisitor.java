package com.alcreasoning;

import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLObjectVisitor;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;

public class LazyUnfoldingVisitor implements OWLObjectVisitor{

    private OWLClass left_side;
    private OWLClassExpression right_side;

    public void visit(OWLEquivalentClassesAxiom eq){
        this.left_side = (OWLClass) eq.getOperandsAsList().get(0);
        this.right_side = eq.getOperandsAsList().get(1);

    }

    public void visit(OWLSubClassOfAxiom eq){
        this.left_side = (OWLClass) eq.getSubClass();
        this.right_side = eq.getSuperClass();
    }

    public OWLClass get_left_side(){
        return this.left_side;
    }

    public OWLClassExpression get_right_side(){
        return this.right_side;
    }
}
