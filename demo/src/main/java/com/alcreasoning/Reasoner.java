package com.alcreasoning;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLObject;
import org.semanticweb.owlapi.model.OWLObjectCardinalityRestriction;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLObjectVisitor;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.providers.OWLVocabularyProvider;


public class Reasoner {

    private AndVisitor or_visitor;
    private OrVisitor and_visitor;
    private FunnyVisitor v;

    public Reasoner(){
        or_visitor = new AndVisitor();
        and_visitor = new OrVisitor();
        v = new FunnyVisitor();
    }


    private boolean check_not_clash(HashSet<OWLObject> L_x){
        HashSet<OWLObject> atomic_concept = new HashSet<OWLObject>();
        HashSet<OWLObject> not_atomic_concept = new HashSet<OWLObject>();

        for(OWLObject obj : L_x){
            if(obj instanceof OWLClass){
               atomic_concept.add((OWLClass)obj);
            }
            else if(obj instanceof OWLObjectComplementOf){
                not_atomic_concept.add((OWLObjectComplementOf) obj);
            }
        }

        for(OWLObject obj : atomic_concept){
            if(not_atomic_concept.contains(((OWLClass)obj).getObjectComplementOf())){
                System.out.print("Clash: ");
                obj.accept(this.v);
                System.out.println();
                return false;
            }
        }   

        return true;
    }

    private void print_L_x(HashSet<OWLObject> L_x){
        System.out.print("{");
        for(OWLObject obj : L_x){
            obj.accept(this.v);
            System.out.print(", ");
        }
        System.out.print("}\n");
    }

    public boolean tableau_algorithm(int x, HashSet<OWLObject> L_x){
        HashSet<OWLObject> disjointed;
        HashSet<OWLObject> owl_some_values_set;
        boolean clash_free = false;

        for(OWLObject obj : L_x){
            obj.accept(or_visitor);
        }
        
        L_x.addAll(or_visitor.get_rule_set_and_reset());
        ////
        System.out.println();
        System.out.println("Inizio chiamata. L_x = ");
        this.print_L_x(L_x);
        ////
        for(OWLObject obj : L_x){
            ////
            System.out.print("Processo ");
            obj.accept(v);
            System.out.println();
            ////
            obj.accept(and_visitor);
            disjointed = and_visitor.get_rule_set_and_reset();
            boolean is_present = false;
            for(OWLObject disj : disjointed){
                if(L_x.contains(disj)){
                    is_present = true;
                    break;
                }
            }
            
            if(!is_present && !disjointed.isEmpty()){
                for(OWLObject disj : disjointed){
                    HashSet<OWLObject> L_x_with_disj = (HashSet<OWLObject>)L_x.clone();
                    L_x_with_disj.add(disj);
                    ////
                    System.out.print("Aggiungo ");
                    disj.accept(this.v);
                    System.out.println();
                    ////
                    clash_free = tableau_algorithm(x, L_x_with_disj);
                    if(clash_free){
                        break;
                    }
                    else{
                        L_x.remove(disj);
                    }
                }
                // Se finiscono i disgiunti e clash_free è ancora false, vuol dire che nessuna combinazione di disgiunti evita un clash, 
                // quindi posso ritornare false
                if(!clash_free){
                    return false;
                }
                System.out.println("Disgiunti terminati\n");
            }
            // Se ho trovato un ramo clash free, posso interrompere l'iterazione e ritornare true
            // altrimenti si procede con l'iterazione
            if(clash_free){
                return true;
            }
        }
        // Controllo se localmente ci sono clash
        if(!this.check_not_clash(L_x)){
            return false;
        }

        owl_some_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectSomeValuesFrom)).collect(Collectors.toCollection(HashSet::new));
        owl_some_values_set.stream().forEach(e -> e.accept(this.v));

        return true;
    }
}
