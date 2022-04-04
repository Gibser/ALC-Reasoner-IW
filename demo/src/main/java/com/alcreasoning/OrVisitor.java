package com.alcreasoning;

import java.util.HashSet;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLObjectVisitor;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLObject;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;

public class OrVisitor implements OWLObjectVisitor{

    HashSet<OWLObject> rule_set = new HashSet<OWLObject>();
    
    public void visit(OWLEquivalentClassesAxiom ax) {
        ax.getOperandsAsList().get(1).accept(this);             
    }

    public void visit(OWLObjectUnionOf intersection) {
        for(OWLClassExpression c : intersection.getOperands()){
            rule_set.add(c);
        }
    }

    public HashSet<OWLObject> get_rule_set_and_reset(){
        HashSet<OWLObject> temp = new HashSet<OWLObject>();
        temp = (HashSet<OWLObject>)rule_set.clone();
        rule_set.clear();
        return temp;
    }
}