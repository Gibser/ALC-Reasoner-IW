package com.alcreasoning.visitors;

import org.semanticweb.owlapi.model.OWLObjectVisitor;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;

import java.io.PrintStream;
import java.io.UnsupportedEncodingException;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;

/**
    OWLObjectVisitor utilizzato per stampare assiomi nel terminale come formula in logica descrittiva
*/
public class PrinterVisitor implements OWLObjectVisitor{
    
    private String regexp_for_names;
    private Pattern r;
    private boolean save_string = false;
    private String return_string;
    private PrintStream out;
    static final char intersect = '\u2293';
	static final char union = '\u2294';
	static final char foreach = '\u2200';
	static final char exists = '\u2203';
	static final char not = '\u00AC';
	static final char inclusion = '\u2291';
    static final char equiv = '\u2261';
    static final char bottom = '\u22a5';
    static final char top = '\u22a4';


    public PrinterVisitor(){
        regexp_for_names = "[^#]*#([a-zA-Z0-9_-]+)>$";
        r = Pattern.compile(regexp_for_names);
        try{
            this.out = new PrintStream(System.out, true, "UTF-8");
        }
        catch(UnsupportedEncodingException e){
            System.out.println("Error");
        }
    }

    public PrinterVisitor(boolean save_string){
        this();
        this.save_string = save_string;
        this.return_string = "";
    }
    
    private void process_output(boolean print, String text){
        if(this.save_string)
            this.return_string += text;
        else
            this.out.print(text);
    }

    private void process_output(boolean print, char text){
        if(this.save_string)
            this.return_string += text;
        else
            this.out.print(text);
    }

    public String get_return_string(){
        return this.return_string;
    }

    public String get_and_destroy_return_string(){
        String tmp = new String(this.return_string);
        this.return_string = "";
        return tmp;
    }

    public void visit(OWLObjectPropertyDomainAxiom ax){
        ax.getProperty().accept(this);
        this.process_output(this.save_string, " domain: ");
        ax.getDomain().accept(this);
    }

    public void visit(OWLObjectPropertyRangeAxiom ax){
        ax.getProperty().accept(this);
        this.process_output(this.save_string, " range: ");
        ax.getRange().accept(this);
    }

    public void visit(OWLEquivalentClassesAxiom ax) {
        List<OWLClassExpression> expr_list = ax.getOperandsAsList();
        int i = 0;
        for(OWLClassExpression operand : expr_list){
            operand.accept(this);
            if(i++ < expr_list.size()-1){
                this.process_output(this.save_string, " ");
                this.process_output(this.save_string, equiv);
                this.process_output(this.save_string, " ");
            }
        }           
    }

    public void visit(OWLObjectSomeValuesFrom ce) {
        OWLObjectPropertyExpression p = ce.getProperty();
        this.process_output(this.save_string, exists);
        Matcher m = r.matcher(p.toString());
        if(m.find())
            this.process_output(this.save_string, m.group(1) + ".");

        ce.getFiller().accept(this);
    }

    public void visit(OWLObjectComplementOf ce) {
        this.process_output(this.save_string, not);
        //this.process_output(this.save_string, "(");
        ce.getOperand().accept(this);
        //this.process_output(this.save_string, ")");
    }

    public void visit(OWLDisjointClassesAxiom disj){
        List<OWLClassExpression> expr_list = disj.getOperandsAsList();
        int i = 0;
        for(OWLClassExpression operand : expr_list){
            operand.accept(this);
            if(i++ < expr_list.size()-1)
                this.process_output(this.save_string, " disjoint ");
        }           
    }


    public void visit(OWLClass class_expr) {
        if(class_expr.getIRI().getShortForm().equals("Nothing"))
            this.process_output(this.save_string, bottom);
        else if(class_expr.getIRI().getShortForm().equals("Thing"))
            this.process_output(this.save_string, top);
        else
            this.process_output(this.save_string, class_expr.getIRI().getShortForm());
    }

    public void visit(OWLNamedIndividual ind) {
        Matcher m = r.matcher(ind.toString());
        if(m.find())
            this.process_output(this.save_string, m.group(1));
    }

    public void visit(OWLObjectIntersectionOf intersection) {
        int list_len = intersection.getOperandsAsList().size(), i = 0;
        this.process_output(this.save_string, "(");
        for(OWLClassExpression c : intersection.getOperands()){
            c.accept(this);
            if(++i < list_len){
                this.process_output(this.save_string, " ");
                this.process_output(this.save_string, intersect);
                this.process_output(this.save_string, " ");
            }
        }
        this.process_output(this.save_string, ")");
    }

    public void visit(OWLObjectUnionOf union) {
        int list_len = union.getOperandsAsList().size(), i = 0;
        this.process_output(this.save_string, "(");
        for(OWLClassExpression c : union.getOperands()){
            c.accept(this);
            if(++i < list_len){
                this.process_output(this.save_string, " ");
                this.process_output(this.save_string, PrinterVisitor.union);
                this.process_output(this.save_string, " ");
            }
        }
        this.process_output(this.save_string, ")");
    }

    public void visit(OWLObjectAllValuesFrom ce) {
        OWLObjectPropertyExpression p = ce.getProperty();
        this.process_output(this.save_string, foreach);
        Matcher m = r.matcher(p.toString());
        if (m.find())
            this.process_output(this.save_string, m.group(1) + ".");

        ce.getFiller().accept(this);
    }

    public void visit(OWLClassAssertionAxiom class_axiom) {
        class_axiom.getClassExpression().accept(this);
        this.process_output(this.save_string, "(");
        class_axiom.getIndividual().accept(this);
        this.process_output(this.save_string, ")");
    }

    public void visit(OWLObjectPropertyAssertionAxiom relation) {
        relation.getProperty().accept(this);
        this.process_output(this.save_string, "(");
        relation.getSubject().accept(this);
        this.process_output(this.save_string, ", ");
        relation.getObject().accept(this);
        this.process_output(this.save_string, ")");
    }

    public void visit(OWLObjectProperty relation_property) {
        Matcher m = r.matcher(relation_property.toString());
        if (m.find())
            this.process_output(this.save_string, m.group(1));
    }

    public void visit(OWLObjectPropertyExpression relation_property) {
        Matcher m = r.matcher(relation_property.toString());
        if (m.find())
            this.process_output(this.save_string, m.group(1));
    }

    public void visit(OWLSubClassOfAxiom subclass){
        subclass.getSubClass().accept(this);
        this.process_output(this.save_string, inclusion);
        subclass.getSuperClass().accept(this);
    }
}