package com.alcreasoning;

import org.semanticweb.owlapi.model.OWLObjectVisitor;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObject;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;


public class FunnyVisitor implements OWLObjectVisitor{
    
    private String regexp_for_names;
    private Pattern r;

    public FunnyVisitor(){
        regexp_for_names = "[^#]*#([a-zA-Z0-9_-]+)>$";
        r = Pattern.compile(regexp_for_names);
    }
    
    public void visit(OWLEquivalentClassesAxiom ax) {
        // this is an example of recursive visit
        //System.out.print(ax.getOperandsAsList().get(0).asOWLClass().getIRI().getShortForm());
        //System.out.print(" equiv ");
        List<OWLClassExpression> expr_list = ax.getOperandsAsList();
        expr_list.get(0).accept(this);
        System.out.print(" equiv ");
        expr_list.get(1).accept(this);             
    }

    public void visit(OWLObjectSomeValuesFrom ce) {
        OWLObjectPropertyExpression p = ce.getProperty();
        System.out.print("exists ");
        Matcher m = r.matcher(p.toString());
        if(m.find()){
            System.out.print(m.group(1));
            System.out.print(".");
        }
        ce.getFiller().accept(this);
    }

    public void visit(OWLObjectComplementOf ce) {
        System.out.print("not(");
        ce.getOperand().accept(this);
        System.out.print(")");
    }

    public void visit(OWLClass class_expr) {
        System.out.print(class_expr.getIRI().getShortForm());
    }

    public void visit(OWLNamedIndividual ind) {
        Matcher m = r.matcher(ind.toString());
        if(m.find()){
            System.out.print(m.group(1));
        }
    }

    public void visit(OWLObjectIntersectionOf intersection) {
        int list_len = intersection.getOperandsAsList().size(), i = 0;
        System.out.print("(");
        for(OWLClassExpression c : intersection.getOperands()){
            c.accept(this);
            if(++i < list_len){
                System.out.print(" and ");
            }
        }
        System.out.print(")");
    }

    public void visit(OWLObjectUnionOf union) {
        int list_len = union.getOperandsAsList().size(), i = 0;
        System.out.print("(");
        for(OWLClassExpression c : union.getOperands()){
            c.accept(this);
            if(++i < list_len){
                System.out.print(" or ");
            }
        }
        System.out.print(")");
    }

    public void visit(OWLObjectAllValuesFrom ce) {
        OWLObjectPropertyExpression p = ce.getProperty();
        System.out.print("for all ");
        Matcher m = r.matcher(p.toString());
        if (m.find()) {
            System.out.print(m.group(1));
            System.out.print(".");
        }
        ce.getFiller().accept(this);
    }

    public void visit(OWLClassAssertionAxiom class_axiom) {
        class_axiom.getClassExpression().accept(this);
        System.out.print("(");
        class_axiom.getIndividual().accept(this);
        System.out.print(")");
    }

    public void visit(OWLObjectPropertyAssertionAxiom relation) {
        relation.getProperty().accept(this);
        System.out.print("(");
        relation.getSubject().accept(this);
        System.out.print(", ");
        relation.getObject().accept(this);
        System.out.print(")");
    }

    public void visit(OWLObjectProperty relation_property) {
        Matcher m = r.matcher(relation_property.toString());
        if (m.find()) {
            System.out.print(m.group(1));
        }
    }

    public void visit(OWLObjectPropertyExpression relation_property) {
        Matcher m = r.matcher(relation_property.toString());
        if (m.find()) {
            System.out.print(m.group(1));
        }
    }
}