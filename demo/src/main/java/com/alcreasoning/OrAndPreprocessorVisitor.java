package com.alcreasoning;

import java.util.HashSet;
import java.util.List;

import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLLogicalAxiom;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLObjectVisitor;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;

/**
    OWLObjectVisitor che visita un assioma e, appena trova un or, verifica se tra i disgiunti c'è un TOP (come A or not(A))
    oppure, appena trova un and, verifica se tra i congiunti c'è un BOTTOM (come A and not(A)).
    Ricostruisce ricorsivamente il nuovo assioma inserendo i vecchi assiomi se non cambiati
    oppure, nel caso di AND o OR, restituisce il nuovo assioma senza i BOTTOM (per gli or) e i TOP (per gli and)
    o direttamente TOP (se c'è un TOP in un or) o BOTTOM (se c'è un BOTTOM in un and)
*/
public class OrAndPreprocessorVisitor implements OWLObjectVisitor{

    OWLClassExpression ret_expr = null;
    OWLLogicalAxiom new_axiom = null;
    private OWLDataFactory factory;
    private FunnyVisitor v;

    public OrAndPreprocessorVisitor(){
        this.factory = OntologyPreprocessor.tbox_man.getOWLDataFactory();
        this.v = new FunnyVisitor();
    }


    public void visit(OWLObjectUnionOf union) {
        /*
        System.out.print("\nProcesso ");
        union.accept(this.v);
        System.out.println();
        */
        HashSet<OWLClassExpression> operands = new HashSet<>();

        for(OWLClassExpression c : union.getOperands()){
            c.accept(this);
            /*
            System.out.print("ret_expr or: ");
            ret_expr.accept(this.v);
            System.out.println();
            */
            if(!ret_expr.equals(this.factory.getOWLThing())){
                OWLObjectComplementOf not_a = this.factory.getOWLObjectComplementOf(ret_expr);

                if(ret_expr.equals(this.factory.getOWLNothing())) continue;

                if(!union.getOperands().contains(not_a.getNNF())) //&& !ret_expr.equals(this.factory.getOWLNothing()))
                    operands.add(ret_expr);
                else{
                    ret_expr = this.factory.getOWLThing();
                    return;
                }
                
            }
            else
                return;
        }

        if(operands.size() > 1){
            ret_expr = this.factory.getOWLObjectUnionOf(operands);
            /*
            System.out.print("\nAggiungo: ");
            ret_expr.accept(this.v);
            System.out.println();
            */
        }
        else if(operands.size() == 1){
            this.ret_expr = operands.iterator().next();
            /*
            System.out.print("\nAggiungo: ");
            ret_expr.accept(this.v);
            System.out.println();
            */
        }
    }

    public void visit(OWLObjectIntersectionOf intersection) {
        /*
        System.out.print("\nProcesso ");
        intersection.accept(this.v);
        System.out.println();
        */
        HashSet<OWLClassExpression> operands = new HashSet<>();

        for(OWLClassExpression c : intersection.getOperands()){
            c.accept(this);
            /*
            System.out.print("ret_expr and: ");
            ret_expr.accept(this.v);
            System.out.println();
            */
            if(!ret_expr.equals(this.factory.getOWLNothing())){
                OWLObjectComplementOf not_a = this.factory.getOWLObjectComplementOf(ret_expr);
                
                if(ret_expr.equals(this.factory.getOWLThing())) continue;

                if(!intersection.getOperands().contains(not_a.getNNF())) //&& !ret_expr.equals(this.factory.getOWLThing()))
                    operands.add(ret_expr);
                else{
                    ret_expr = this.factory.getOWLNothing();
                    return;
                }
                
            }
            else
                return;
        }

        if(operands.size() > 1){
            ret_expr = this.factory.getOWLObjectIntersectionOf(operands);
            /*
            System.out.print("\nAggiungo: ");
            ret_expr.accept(this.v);
            System.out.println();
            */
        }
        else if(operands.size() == 1){
            this.ret_expr = operands.iterator().next();
            /*
            System.out.print("\nAggiungo: ");
            ret_expr.accept(this.v);
            System.out.println();
            */
        }
    }

    public void visit(OWLClass class_expr) {
        this.ret_expr = class_expr;
    }

    
    public void visit(OWLEquivalentClassesAxiom ax) {
        List<OWLClassExpression> expr_list = ax.getOperandsAsList();
        expr_list.get(0).accept(this);
        OWLClassExpression ret1 = ret_expr;
        expr_list.get(1).accept(this);
        new_axiom = this.factory.getOWLEquivalentClassesAxiom(ret1, ret_expr);
    }
    
    public void visit(OWLSubClassOfAxiom ax) {
        ax.getSubClass().accept(this);
        OWLClassExpression ret1 = ret_expr;
        ax.getSuperClass().accept(this);
        new_axiom = this.factory.getOWLSubClassOfAxiom(ret1, ret_expr);
    }
    
    public void visit(OWLObjectSomeValuesFrom ce) {
        OWLClassExpression filler = ce.getFiller();
        filler.accept(this);
        ret_expr = this.factory.getOWLObjectSomeValuesFrom(ce.getProperty(), ret_expr);
    }

    public void visit(OWLObjectComplementOf ce) {
        ce.getOperand().accept(this);
        ret_expr = this.factory.getOWLObjectComplementOf(ret_expr);
    }


    public void visit(OWLObjectAllValuesFrom ce) {
        OWLClassExpression filler = ce.getFiller();
        filler.accept(this);
        ret_expr = this.factory.getOWLObjectSomeValuesFrom(ce.getProperty(), ret_expr);
    }

    public OWLLogicalAxiom getLogicalAxiom(){
        return this.new_axiom;
    }

}
