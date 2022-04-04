package com.alcreasoning;
import java.util.HashSet;
import java.util.Set;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLObject;
import org.semanticweb.owlapi.model.OWLObjectCardinalityRestriction;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLObjectVisitor;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.providers.OWLVocabularyProvider;


public class Reasoner {

    private AndVisitor or_visitor;
    private OrVisitor and_visitor;

    public Reasoner(){
        or_visitor = new AndVisitor();
        and_visitor = new OrVisitor();
    }


    public boolean tableau_algorithm(int x, HashSet<OWLObject> L_x){
        HashSet<OWLObject> disjointed;
        boolean clash_free = false;

        for(OWLObject obj : L_x){
            obj.accept(or_visitor);
        }

        L_x.addAll(or_visitor.get_rule_set_and_reset());

        for(OWLObject obj : L_x){
            obj.accept(and_visitor);
            disjointed = and_visitor.get_rule_set_and_reset();
            boolean is_present = false;
            for(OWLObject disj : disjointed){
                if(L_x.contains(disj)){
                    is_present = true;
                    break;
                }
            }
            
            if(!is_present){
                for(OWLObject disj : disjointed){
                    L_x.add(disj);
                    clash_free = tableau_algorithm(x, L_x);
                    if(clash_free){
                        break;
                    }
                    else{
                        L_x.remove(disj);
                    }
                }
            }
        

        }
        return false;
    }
}
