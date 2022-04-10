package com.alcreasoning;

import java.util.HashSet;

import org.semanticweb.owlapi.model.OWLObjectVisitor;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLObject;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;

/**
    OWLObjectVisitor utilizzato per applicare la regola dell'OR nell'algoritmo del tableau
 */
public class OrVisitor implements OWLObjectVisitor{

    HashSet<OWLClassExpression> rule_set = new HashSet<OWLClassExpression>();
    
    public void visit(OWLEquivalentClassesAxiom ax) {
        ax.getOperandsAsList().get(1).accept(this);             
    }

    public void visit(OWLObjectUnionOf intersection) {
        for(OWLClassExpression c : intersection.getOperands()){
            rule_set.add(c);
        }
    }

    public HashSet<OWLClassExpression> get_rule_set_and_reset(){
        HashSet<OWLClassExpression> temp = new HashSet<>(rule_set);
        rule_set.clear();
        return temp;
    }
}