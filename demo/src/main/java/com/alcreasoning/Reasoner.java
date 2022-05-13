package com.alcreasoning;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.stream.Collectors;

import com.alcreasoning.visitors.AllVisitors;
import com.alcreasoning.visitors.AndVisitor;
import com.alcreasoning.visitors.LazyUnfoldingVisitor;
import com.alcreasoning.visitors.OrVisitor;
import com.alcreasoning.visitors.PrinterVisitor;

import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.ModelFactory;
import org.apache.jena.rdf.model.RDFWriter;
import org.apache.jena.rdf.model.Resource;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLLogicalAxiom;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObject;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;

import guru.nidi.graphviz.model.Node;

public class Reasoner {
    private static final char union = '\u2294';

    private AndVisitor and_visitor;
    private OrVisitor or_visitor;
    private PrinterVisitor printer_visitor;
    private PrinterVisitor return_visitor;
    private LazyUnfoldingVisitor lazy_unfolding_v;

    private OWLDataFactory factory;
    private IRI ontology_iri;
    private OWLClassExpression Ĉ = null;
    private HashSet<OWLObject> abox = new HashSet<OWLObject>();
    private HashSet<OWLObject> L_x = new HashSet<OWLObject>();
    private HashSet<OWLLogicalAxiom> T_u = new HashSet<OWLLogicalAxiom>();    

    private OWLNamedIndividual root;
    private int node_index = -1;

    private boolean draw_graph;

    private GraphDrawer graph_drawer;
    private Node last_child;
    
    private Model rdf_model;  
    private Resource last_child_rdf;

    private Reasoner(){
        this.and_visitor = AllVisitors.and_visitor;
        this.or_visitor = AllVisitors.or_visitor;
        this.printer_visitor = AllVisitors.printer_visitor;
        this.return_visitor = AllVisitors.printer_v_save_string;
    }


    private Reasoner(IRI ontology_iri, boolean draw_graph) {
        this();
        this.factory = OntologyPreprocessor.concept_man.getOWLDataFactory();
        this.ontology_iri = ontology_iri;
        this.graph_drawer = new GraphDrawer("ALC Tableau");
        this.draw_graph = draw_graph;
        if (this.draw_graph)
            rdf_model = ModelFactory.createDefaultModel();
    }
    
    public Reasoner(OWLClassExpression Ĉ, HashSet<OWLClassExpression> KB_with_concept_name,
        HashSet<OWLClassExpression> KB_with_concept, IRI ontology_iri, boolean draw_graph) {
        this(ontology_iri, draw_graph);
        this.L_x.addAll(KB_with_concept);
        this.root = this.create_individual();
        this.addall_axiom_to_abox(KB_with_concept_name, root);
        this.Ĉ = Ĉ;
    }

    public Reasoner(OWLClassExpression T_g, HashSet<OWLLogicalAxiom> T_u, HashSet<OWLClassExpression> KB_with_concept_name, HashSet<OWLClassExpression> KB_with_concept, IRI ontology_iri, boolean draw_graph){
        this(ontology_iri, draw_graph);
        this.L_x.addAll(KB_with_concept);
        this.root = this.create_individual();
        this.addall_axiom_to_abox(KB_with_concept_name, root);
        this.Ĉ = T_g;
        this.T_u = T_u;
        this.lazy_unfolding_v = AllVisitors.lazy_unfolding_v;
    }


    private boolean check_not_clash(HashSet<OWLObject> L_x){
        if(L_x.contains(this.factory.getOWLNothing()))
            return false;


        
        for(OWLObject obj : L_x){
            if (obj instanceof OWLClass)
                if (L_x.contains(((OWLClass) obj).getComplementNNF()))
                    return false;
        }   

        return true;
    } 

    private void print_L_x(HashSet<OWLObject> L_x, String name){
        int i = 0;
        System.out.print(name + " = {");
        for(OWLObject obj : L_x){
            obj.accept(this.printer_visitor);
            if(i++ < L_x.size()-1) System.out.print(", "); else System.out.print("}\n");
        }
    }

    private String return_set_as_string(HashSet<OWLObject> L_x, String set_name){
        String ret_string = set_name + " = {";
        int i = 0;
        for(OWLObject obj : L_x){
            obj.accept(this.return_visitor);
            ret_string += this.return_visitor.get_and_destroy_return_string();
            if(i++ < L_x.size()-1) ret_string += ", "; else ret_string += "}";
        }

        return ret_string;
    }

    private void print_abox(){
        int i = 0;
        System.out.print("ABox = {");
        for(OWLObject obj : this.abox){
            obj.accept(this.printer_visitor);
            if(i++ < this.abox.size()-1) System.out.print(", "); else System.out.print("}\n");
        }
    }

    private boolean add_axiom_to_abox(OWLObject axm, OWLNamedIndividual x){
        return this.abox.add(this.factory.getOWLClassAssertionAxiom((OWLClassExpression) axm, x));
    }

    private boolean add_axiom_to_abox(OWLObject axm) {
        return this.abox.add(axm);
    }
    
    private HashSet<OWLClassExpression> addall_axiom_to_abox(HashSet<OWLClassExpression> axms, OWLNamedIndividual x){
        HashSet<OWLClassExpression> added_items = new HashSet<>();
        for(OWLClassExpression obj : axms){
            OWLClassAssertionAxiom inst_axm = this.factory.getOWLClassAssertionAxiom((OWLClassExpression) obj, x);
            if(this.abox.add(inst_axm))
                added_items.add(obj);
        }
        return added_items;
    }

    private OWLNamedIndividual create_individual(){
        return this.factory.getOWLNamedIndividual(IRI.create(this.ontology_iri+ "#x_" + ++this.node_index));
    }

    private HashSet<OWLClassAssertionAxiom> instantiateall_axiom(HashSet<OWLClassExpression> axms, OWLNamedIndividual x){
        HashSet<OWLClassAssertionAxiom> instantiated_axms = new HashSet<>();
        for(OWLClassExpression axm : axms){
            instantiated_axms.add(this.instantiate_axiom(axm, x));
        }
        return instantiated_axms;
    }

    private OWLClassAssertionAxiom instantiate_axiom(OWLClassExpression axm, OWLNamedIndividual x){
        return this.factory.getOWLClassAssertionAxiom(axm, x);
    }

    private OWLObjectPropertyAssertionAxiom instantiate_property_axiom(OWLObjectPropertyExpression relation,
            OWLNamedIndividual x1, OWLNamedIndividual x2) {
        return this.factory.getOWLObjectPropertyAssertionAxiom(relation, x1, x2);
    }

    
    private void removeall_axiom_from_abox(HashSet<? extends OWLObject> axms) {
        this.abox.removeAll(axms);
    }

    private Node update_graph(boolean or_branch, Node node, String parent_name, String individual_name, OWLObject operand){
        Node child_node = null;
        if(this.draw_graph){
            operand.accept(this.return_visitor);
            if(or_branch)
                child_node = this.graph_drawer.add_new_child(node, "" + union + ": " + this.return_visitor.get_and_destroy_return_string(), individual_name);
            else{
                child_node = this.graph_drawer.add_new_child(node, this.return_visitor.get_and_destroy_return_string() + ":" + parent_name, individual_name);
            }
        }
        return child_node;
    }

    private void clash_rollback_all(HashSet<OWLObject> L_x, HashSet<OWLClassExpression> added, OWLNamedIndividual x, Node node, Resource node_rdf){
        // rimuovo congiunti da L_x
        L_x.removeAll(added);
        // rimuovo congiunti dall'ABox
        this.removeall_axiom_from_abox(this.instantiateall_axiom(added, x));
        // Grafo
        this.graph_drawer.add_clash_node(node);
        // RDF
        node_rdf.addProperty(this.rdf_model.createProperty(this.ontology_iri + "/#clash"), "CLASH");
    }

    private void clash_rollback_all(HashSet<OWLObject> L_x, HashSet<OWLClassExpression> added, OWLNamedIndividual x) {
        // rimuovo congiunti da L_x
        L_x.removeAll(added);
        // rimuovo congiunti dall'ABox
        this.removeall_axiom_from_abox(this.instantiateall_axiom(added, x));
    }

    private void clash_rollback(HashSet<OWLObject> L_x, OWLClassExpression added, OWLNamedIndividual x) {
        // rimuovo congiunto da L_x
        L_x.remove(added);
        // rimuovo congiunto dall'ABox
        this.abox.remove(this.instantiate_axiom(added, x));
    }

    private HashSet<OWLClassExpression> and_rule(HashSet<OWLObject> L_x) {
        HashSet<OWLClassExpression> added_items = new HashSet<>();

        for (OWLObject obj : L_x) {
            obj.accept(and_visitor);
        }

        for (OWLClassExpression obj : and_visitor.get_rule_set_and_reset()) {
            if (L_x.add(obj))
                added_items.add(obj);
        }
        return added_items;
    }

    private HashSet<OWLObject> exists_rule(HashSet<OWLObject> L_x, OWLNamedIndividual x, HashSet<OWLObject> L_child, OWLNamedIndividual child, OWLObjectSomeValuesFrom obj) {
        HashSet<OWLObject> added_axioms = new HashSet<>();
        OWLClassExpression filler = obj.getFiller();
        OWLObjectPropertyExpression property = obj.getProperty();
        OWLClassAssertionAxiom instantiated_axiom = this.instantiate_axiom(filler, child);
        OWLObjectPropertyAssertionAxiom instantiated_property_axiom = this.instantiate_property_axiom(property, x, child);
                
        if(this.add_axiom_to_abox(instantiated_axiom))
            added_axioms.add(instantiated_axiom);                       // Si aggiunge C(child) all'ABox
        
        if(this.add_axiom_to_abox(instantiated_property_axiom))         // Si aggiunge R(x, child) all'ABox 
            added_axioms.add(instantiated_property_axiom);
        
        L_child.add(filler);                                            // L(x') U {C};
            
        if (this.Ĉ != null) {                                           // TBox non vuota: L(x') U {Ĉ}
            L_child.add(this.Ĉ);
            instantiated_axiom = this.instantiate_axiom(this.Ĉ, child);
            if (this.add_axiom_to_abox(instantiated_axiom)) // Si aggiunge Ĉ(child) all'ABox
                added_axioms.add(instantiated_axiom);
        }

        return added_axioms;
    }
    
    private HashSet<OWLObject> all_values_rule(HashSet<OWLObjectAllValuesFrom> owl_all_values_set, HashSet<OWLObject> L_child, OWLNamedIndividual child, OWLObjectPropertyExpression property) {
        HashSet<OWLObject> added_axioms = new HashSet<>();
        owl_all_values_set.stream()                                                                         // forall R.D
        .filter(e -> e.getProperty().equals(property))                                                      // Filtra i per ogni con la stessa relazione R
        .forEach(e -> {
                        L_child.add(e.getFiller());
                        if(this.add_axiom_to_abox(e.getFiller(), child))                                    // cambiato x a child, va istanziato per il figlio, non per x
                            added_axioms.add(this.instantiate_axiom(e.getFiller(), child));                 // cambiato x a child
                            });
                      
        return added_axioms;
    }
    
    private HashSet<OWLObjectUnionOf> disjunctions(HashSet<OWLObject> L_x) {
        return L_x.stream().filter(e -> e instanceof OWLObjectUnionOf).map(e -> (OWLObjectUnionOf) e)
                .collect(Collectors.toCollection(HashSet::new));
    }
    
    private boolean or_rule_condition(HashSet<OWLClassExpression> elements, OWLNamedIndividual x) {
        for (OWLClassExpression disj : elements) {
            if (this.abox.contains(this.instantiate_axiom(disj, x))) {
                return false;
            }
        }
        return true;
    }

    private boolean exists_rule_conditions(OWLObjectPropertyExpression property, OWLClassExpression filler, OWLNamedIndividual x){
        boolean exists_rule_condition[] = {true};

        this.abox.stream()                                                                                                                                  // exists R.C
            .filter(e -> e instanceof OWLObjectPropertyAssertionAxiom)                                                                                      // Raccolgo tutte le relazioni
            .map(e -> (OWLObjectPropertyAssertionAxiom)e)                                                                                                   // Cast    
            .filter(e -> e.getProperty().equals(property))                                                                                                  // Filtro tutte le relazioni di tipo R    
            .filter(e -> e.getSubject().equals(x))                                                                                                          // Filtro tutte le relazioni R da x a qualche z
                .forEach(e -> {
                    if (this.abox.contains(this.factory.getOWLClassAssertionAxiom(filler, e.getObject()))) {                                                // Filtro le relazioni tali che C(z)
                        exists_rule_condition[0] = false;
                    }
                }); 

        return exists_rule_condition[0];
    }

    
    //Con grafo
    public boolean tableau_algorithm_non_empty_tbox(OWLNamedIndividual x, List<HashSet<OWLObject>> blocking_list, HashSet<OWLObject> L_x, Node node, Resource node_rdf){
        HashSet<OWLClassExpression> disjointed;
        HashSet<OWLObjectSomeValuesFrom> owl_some_values_set;
        HashSet<OWLObjectAllValuesFrom> owl_all_values_set;
        HashSet<OWLClassExpression> added_joint;
        boolean clash_free = false;

        added_joint = this.and_rule(L_x);

        // Blocking
        if (this.Ĉ != null && this.blocking(blocking_list, L_x)) {
            System.out.println("Blocking");
            return true;
        }

        this.addall_axiom_to_abox(added_joint, x);
        
        // Grafo: Aggiungo L_x al nodo dopo regola AND
        node = this.graph_drawer.add_L_x_to_node(node, L_x, x.getIRI().getShortForm());
        // RDF
        node_rdf.addProperty(this.rdf_model.createProperty(this.ontology_iri + "/#L_x"), this.graph_drawer.return_set_as_string(L_x, "L_" + x.getIRI().getShortForm()));
        
        /*
        if(!(clash_free = this.check_not_clash(L_x))){
            this.clash_rollback_all(L_x, added_joint, x, node, node_rdf);
            return false;
        }
        */
        for(OWLObjectUnionOf obj : this.disjunctions(L_x)){
            
            obj.accept(or_visitor);
            disjointed = or_visitor.get_rule_set_and_reset();
            
            if(this.or_rule_condition(disjointed, x)){
                for(OWLClassExpression disj : disjointed){
                    L_x.add(disj);
                    this.add_axiom_to_abox(disj, x);
                    
                    // Grafo
                    this.last_child = this.update_graph(true, node, null, x.getIRI().getShortForm(), disj);
                    // RDF
                    Resource rdf_union_node = this.rdf_model.createResource();
                    node_rdf.addProperty(this.rdf_model.createProperty(this.ontology_iri + "/#union"), rdf_union_node);

                    clash_free = this.tableau_algorithm_non_empty_tbox(x, blocking_list, L_x, this.last_child, rdf_union_node);
                    
                    if(clash_free)
                        break;
                    else 
                        this.clash_rollback(L_x, disj, x);
                }
                // Se finiscono i disgiunti e clash_free è ancora false, vuol dire che nessuna combinazione di disgiunti evita un clash, 
                // quindi posso ritornare false
                if(!clash_free){
                    this.clash_rollback_all(L_x, added_joint, x);
                    return false;
                }
            }

            // Se ho trovato un ramo clash free, posso interrompere l'iterazione e ritornare true
            // altrimenti si procede con l'iterazione
            if(clash_free)
                return true;            
        }
        // Controllo se localmente ci sono clash
        if(!(clash_free = this.check_not_clash(L_x))){
            this.clash_rollback_all(L_x, added_joint, x, node, node_rdf);
            return false;
        }

        owl_some_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectSomeValuesFrom)).map(e -> (OWLObjectSomeValuesFrom)e).collect(Collectors.toCollection(HashSet::new));
        owl_all_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectAllValuesFrom)).map(e -> (OWLObjectAllValuesFrom)e).collect(Collectors.toCollection(HashSet::new));
        
        
        for(OWLObjectSomeValuesFrom obj : owl_some_values_set){
            OWLClassExpression filler = obj.getFiller();
            OWLObjectPropertyExpression property = obj.getProperty();
            
            if(filler.equals(this.factory.getOWLNothing())){                                // Non creo un figlio se il filler è bottom
                this.clash_rollback_all(L_x, added_joint, x, node, node_rdf);
                return false;                                          
            }

            if(this.exists_rule_conditions(property, filler, x)){
                HashSet<OWLObject> added_axioms;
                HashSet<OWLObject> L_child = new HashSet<>();                               // L_child rappresenta L(x')
                OWLNamedIndividual child = create_individual();                             // Creo nuovo figlio child

                added_axioms = this.exists_rule(L_x, x, L_child, child, obj);
                                                                                                                        
                added_axioms.addAll(this.all_values_rule(owl_all_values_set, L_child, child, property));
                
                // Grafo
                this.last_child = this.update_graph(false, node, x.getIRI().getShortForm(), child.getIRI().getShortForm(), property);
                // RDF
                this.last_child_rdf = this.rdf_model.createResource(child.getIRI().toString());
                property.accept(this.return_visitor);
                node_rdf.addProperty(this.rdf_model.createProperty(this.ontology_iri + "/#" + this.return_visitor.get_and_destroy_return_string()), this.last_child_rdf);

                blocking_list.add(L_x);
                clash_free = this.tableau_algorithm_non_empty_tbox(child, blocking_list, L_child, this.last_child, this.last_child_rdf);

                if(!clash_free){
                    this.clash_rollback_all(L_x, added_joint, x);
                    this.removeall_axiom_from_abox(added_axioms);
                    return false;
                }
                else{
                    node = this.last_child;
                    node_rdf = this.last_child_rdf;
                }
            }
        }

        this.graph_drawer.add_new_child(node);

        return clash_free;
    }

    // Senza grafo
    public boolean tableau_algorithm_non_empty_tbox(OWLNamedIndividual x, List<HashSet<OWLObject>> blocking_list, HashSet<OWLObject> L_x){
        HashSet<OWLClassExpression> disjointed;
        HashSet<OWLObjectSomeValuesFrom> owl_some_values_set;
        HashSet<OWLObjectAllValuesFrom> owl_all_values_set;
        HashSet<OWLClassExpression> added_joint;
        boolean clash_free = false;
        
        added_joint = this.and_rule(L_x);

        // Blocking
        if(this.Ĉ != null && this.blocking(blocking_list, L_x)){
            System.out.println("Blocking");
            return true;
        }

        this.addall_axiom_to_abox(added_joint, x);

        /*
        if(!this.check_not_clash(L_x)){
            this.clash_rollback_all(L_x, added_joint, x);
            return false;
        }
        */
        
        for(OWLObjectUnionOf obj : this.disjunctions(L_x)){
            
            obj.accept(or_visitor);
            disjointed = or_visitor.get_rule_set_and_reset();
            
            if(this.or_rule_condition(disjointed, x)){
                for(OWLClassExpression disj : disjointed){
                    L_x.add(disj);
                    this.add_axiom_to_abox(disj, x);
                    
                    clash_free = this.tableau_algorithm_non_empty_tbox(x, blocking_list, L_x);
                    
                    if(clash_free)
                        break; 
                    else
                        this.clash_rollback(L_x, disj, x);
                }
                // Se finiscono i disgiunti e clash_free è ancora false, vuol dire che nessuna combinazione di disgiunti evita un clash, 
                // quindi posso ritornare false
                if(!clash_free){
                    this.clash_rollback_all(L_x, added_joint, x);
                    return false;
                }
            }
            // Se ho trovato un ramo clash free, posso interrompere l'iterazione e ritornare true
            // altrimenti si procede con l'iterazione
            if(clash_free)
                return true;
        }
        // Controllo se localmente ci sono clash
        if(!(clash_free = this.check_not_clash(L_x))){
            this.clash_rollback_all(L_x, added_joint, x);
            return false;
        }

        owl_some_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectSomeValuesFrom)).map(e -> (OWLObjectSomeValuesFrom)e).collect(Collectors.toCollection(HashSet::new));
        owl_all_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectAllValuesFrom)).map(e -> (OWLObjectAllValuesFrom)e).collect(Collectors.toCollection(HashSet::new));

        for(OWLObjectSomeValuesFrom obj : owl_some_values_set){

            OWLClassExpression filler = obj.getFiller();
            OWLObjectPropertyExpression property = obj.getProperty();

            if (filler.equals(this.factory.getOWLNothing())) {
                this.clash_rollback_all(L_x, added_joint, x);
                return false;
            }
            
            if(this.exists_rule_conditions(property, filler, x)){
                HashSet<OWLObject> added_axioms = new HashSet<>();
                HashSet<OWLObject> L_child = new HashSet<>();                                                           // L_child rappresenta L(x')
                OWLNamedIndividual child = create_individual();                                                         // Creo nuovo figlio child
        
                added_axioms = this.exists_rule(L_x, x, L_child, child, obj);
                                                                                                                        
                added_axioms.addAll(this.all_values_rule(owl_all_values_set, L_child, child, property));
                
                blocking_list.add(L_x);
                clash_free = this.tableau_algorithm_non_empty_tbox(child, blocking_list, L_child);

                if(!clash_free){
                    this.clash_rollback_all(L_x, added_joint, x);
                    this.removeall_axiom_from_abox(added_axioms);
                    return false;
                }
            }
        }
        return clash_free;
    }

    private HashSet<OWLClassExpression> lazy_unfolding_rules(HashSet<OWLObject> L_x){
        HashSet<OWLClassExpression> added_axioms = new HashSet<>();
        for(OWLLogicalAxiom ax : this.T_u){
            ax.accept(this.lazy_unfolding_v);
            OWLClass left_side = this.lazy_unfolding_v.get_left_side();
            OWLClassExpression right_side = this.lazy_unfolding_v.get_right_side();

            // (A in L_x) e (C not in L_x)
            if(L_x.contains(left_side) && !L_x.contains(right_side)){
                added_axioms.add(right_side);
                L_x.add(right_side);
            }
            // Per l'equivalenza, controllo anche se (not(A) in L_x) e (not(C) not in L_x)
            else if(   (ax instanceof OWLEquivalentClassesAxiom)                                   && 
                       L_x.contains(this.factory.getOWLObjectComplementOf(left_side).getNNF())     &&
                       !L_x.contains(this.factory.getOWLObjectComplementOf(right_side).getNNF())
                   ){
                    added_axioms.add(this.factory.getOWLObjectComplementOf(this.lazy_unfolding_v.get_right_side()).getNNF());
                    L_x.add(this.factory.getOWLObjectComplementOf(this.lazy_unfolding_v.get_right_side()).getNNF());
                   }
        }
        return added_axioms;
    }

    /*
    private boolean blocking(HashSet<OWLObject> L_parent, HashSet<OWLObject> L_x){
        if(L_parent != null)
            this.print_L_x(L_parent, "L_parent");
        this.print_L_x(L_x, "L_x");
        return L_parent == null ? false : L_parent.containsAll(L_x);
    }
    */

    private boolean blocking(List<HashSet<OWLObject>> blocking_list, HashSet<OWLObject> L_x){
        if(!blocking_list.isEmpty())
            for(HashSet<OWLObject> L_parent : blocking_list){
                if(L_parent.containsAll(L_x))
                    return true;
            }
        return false;
    }


    private boolean contains_and(HashSet<OWLClassExpression> added_lazy){
        if(added_lazy.isEmpty())
            return false;

        for(OWLObject obj : added_lazy){
            if(obj instanceof OWLObjectIntersectionOf)
                return true;
        }
        return false;
    }

    //Con grafo
    public boolean tableau_algorithm_non_empty_tbox_lazy_unfolding(OWLNamedIndividual x, List<HashSet<OWLObject>> blocking_list, HashSet<OWLObject> L_x, Node node, Resource node_rdf){
        HashSet<OWLClassExpression> disjointed;
        HashSet<OWLObjectSomeValuesFrom> owl_some_values_set;
        HashSet<OWLObjectAllValuesFrom> owl_all_values_set;
        HashSet<OWLClassExpression> added_conj_lazy = new HashSet<>();
        HashSet<OWLClassExpression> added_lazy = new HashSet<>();
        boolean clash_free = false;
        boolean apply_lazy_unfolding = true;
    
        while(apply_lazy_unfolding){

            added_conj_lazy.addAll(this.and_rule(L_x));
            
            // Regole lazy unfolding
            added_lazy = this.lazy_unfolding_rules(L_x);
            added_conj_lazy.addAll(added_lazy);
            
            if(!this.contains_and(added_lazy))
                apply_lazy_unfolding = false;
        }

        // Blocking
        if(this.blocking(blocking_list, L_x)){
            System.out.println("Blocking");
            return true;
        }

        // Grafo: Aggiungo L_x al nodo dopo regola AND
        node = this.graph_drawer.add_L_x_to_node(node, L_x, x.getIRI().getShortForm());
        // RDF
        node_rdf.addProperty(this.rdf_model.createProperty(this.ontology_iri + "/#L_x"), this.graph_drawer.return_set_as_string(L_x, "L_" + x.getIRI().getShortForm()));

        this.addall_axiom_to_abox(added_conj_lazy, x);

        /*
        if(!this.check_not_clash(L_x)){
            this.clash_rollback_all(L_x, added_conj_lazy, x, node, node_rdf);
            return false;
        }
        */
        for(OWLClassExpression obj : this.disjunctions(L_x)){
            obj.accept(or_visitor);
            disjointed = or_visitor.get_rule_set_and_reset();
            
            if(this.or_rule_condition(disjointed, x)){
                for(OWLClassExpression disj : disjointed){
                    L_x.add(disj);
                    this.add_axiom_to_abox(disj, x);

                    // Grafo
                    this.last_child = this.update_graph(true, node, null, x.getIRI().getShortForm(), disj);
                    // RDF
                    this.last_child_rdf = this.rdf_model.createResource();
                    node_rdf.addProperty(this.rdf_model.createProperty(this.ontology_iri + "/#union"), this.last_child_rdf);

                    clash_free = this.tableau_algorithm_non_empty_tbox_lazy_unfolding(x, blocking_list, L_x, this.last_child, this.last_child_rdf);

                    if(clash_free)
                        break;
                    else
                        this.clash_rollback(L_x, disj, x);
                }
                // Se finiscono i disgiunti e clash_free è ancora false, vuol dire che nessuna combinazione di disgiunti evita un clash, 
                // quindi posso ritornare false
                if(!clash_free){
                    this.clash_rollback_all(L_x, added_conj_lazy, x);
                    return false;
                }
            }
            // Se ho trovato un ramo clash free, posso interrompere l'iterazione e ritornare true
            // altrimenti si procede con l'iterazione
            
            if(clash_free)
                return true;
        }
        // Controllo se localmente ci sono clash
        if(!(clash_free = this.check_not_clash(L_x))){
            this.clash_rollback_all(L_x, added_conj_lazy, x, node, node_rdf);
            return false;
        }

        owl_some_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectSomeValuesFrom)).map(e -> (OWLObjectSomeValuesFrom)e).collect(Collectors.toCollection(HashSet::new));
        owl_all_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectAllValuesFrom)).map(e -> (OWLObjectAllValuesFrom)e).collect(Collectors.toCollection(HashSet::new));
        

        for(OWLObjectSomeValuesFrom obj : owl_some_values_set){
            OWLClassExpression filler = obj.getFiller();
            OWLObjectPropertyExpression property = obj.getProperty();

            if(filler.equals(this.factory.getOWLNothing())){                            // Non creo un figlio se il filler è bottom
                this.clash_rollback_all(L_x, added_conj_lazy, x, node, node_rdf);
                return false;
            }
            
            if(this.exists_rule_conditions(property, filler, x)){
                
                HashSet<OWLObject> added_axioms = new HashSet<>();
                HashSet<OWLObject> L_child = new HashSet<>();                                                           // L_child rappresenta L(x')
                OWLNamedIndividual child = create_individual();                                                         // Creo nuovo figlio child

                added_axioms = this.exists_rule(L_x, x, L_child, child, obj);
                                                                                                                        
                added_axioms.addAll(this.all_values_rule(owl_all_values_set, L_child, child, property));
                
                // Grafo
                this.last_child = this.update_graph(false, node, x.getIRI().getShortForm(), child.getIRI().getShortForm(), property);
                // RDF
                this.last_child_rdf = this.rdf_model.createResource(child.getIRI().toString());
                property.accept(this.return_visitor);
                node_rdf.addProperty(this.rdf_model.createProperty(this.ontology_iri + "/#" + this.return_visitor.get_and_destroy_return_string()), this.last_child_rdf);
                
                blocking_list.add(L_x);
                clash_free = this.tableau_algorithm_non_empty_tbox_lazy_unfolding(child, blocking_list, L_child, this.last_child, this.last_child_rdf);

                if(!clash_free){
                    this.clash_rollback_all(L_x, added_conj_lazy, x);
                    this.removeall_axiom_from_abox(added_axioms);
                    return false;
                }
                else{
                    node = this.last_child;
                    node_rdf = this.last_child_rdf;
                }
            }
        }
        
        this.graph_drawer.add_new_child(node);

        return clash_free;
    }

    //Senza grafo
    public boolean tableau_algorithm_non_empty_tbox_lazy_unfolding(OWLNamedIndividual x, List<HashSet<OWLObject>> blocking_list, HashSet<OWLObject> L_x){
        HashSet<OWLClassExpression> disjointed;
        HashSet<OWLObjectSomeValuesFrom> owl_some_values_set;
        HashSet<OWLObjectAllValuesFrom> owl_all_values_set;
        HashSet<OWLClassExpression> added_conj_lazy = new HashSet<>();
        HashSet<OWLClassExpression> added_lazy = new HashSet<>();
        boolean clash_free = false;
        boolean apply_lazy_unfolding = true;

        while(apply_lazy_unfolding){
            
            added_conj_lazy.addAll(this.and_rule(L_x));

            // Regole lazy unfolding
            added_lazy = this.lazy_unfolding_rules(L_x);
            added_conj_lazy.addAll(added_lazy);
            
            if(!this.contains_and(added_lazy))
                apply_lazy_unfolding = false;
        }

        // Blocking
        if(this.blocking(blocking_list, L_x)){
            System.out.println("Blocking");
            return true;
        }

        this.addall_axiom_to_abox(added_conj_lazy, x);

        /*
        if(!this.check_not_clash(L_x)){
            this.clash_rollback_all(L_x, added_conj_lazy, x);
            return false;
        }
        */

        for(OWLClassExpression obj : this.disjunctions(L_x)){
            obj.accept(or_visitor);
            disjointed = or_visitor.get_rule_set_and_reset();
            
            if(this.or_rule_condition(disjointed, x)){
                for(OWLClassExpression disj : disjointed){
                    L_x.add(disj);
                    this.add_axiom_to_abox(disj, x);

                    clash_free = this.tableau_algorithm_non_empty_tbox_lazy_unfolding(x, blocking_list, L_x);

                    if(clash_free)
                        break;
                    else
                        this.clash_rollback(L_x, disj, x);                        
                }
                // Se finiscono i disgiunti e clash_free è ancora false, vuol dire che nessuna combinazione di disgiunti evita un clash, 
                // quindi posso ritornare false
                if(!clash_free){
                    this.clash_rollback_all(L_x, added_conj_lazy, x);
                    return false;
                }
            }
            // Se ho trovato un ramo clash free, posso interrompere l'iterazione e ritornare true
            // altrimenti si procede con l'iterazione
            
            if(clash_free)
                return true;
        }
        // Controllo se localmente ci sono clash
        if(!(clash_free = this.check_not_clash(L_x))){
            this.clash_rollback_all(L_x, added_conj_lazy, x);
            return false;
        }

        owl_some_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectSomeValuesFrom)).map(e -> (OWLObjectSomeValuesFrom)e).collect(Collectors.toCollection(HashSet::new));
        owl_all_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectAllValuesFrom)).map(e -> (OWLObjectAllValuesFrom)e).collect(Collectors.toCollection(HashSet::new));
        
        for(OWLObjectSomeValuesFrom obj : owl_some_values_set){
            OWLClassExpression filler = obj.getFiller();
            OWLObjectPropertyExpression property = obj.getProperty();

            if (filler.equals(this.factory.getOWLNothing())) {              // Non creo un figlio se il filler è bottom
                this.clash_rollback_all(L_x, added_conj_lazy, x);
                return false;
            }
            
            if(this.exists_rule_conditions(property, filler, x)){
                HashSet<OWLObject> added_axioms = new HashSet<>();
                HashSet<OWLObject> L_child = new HashSet<>();                                                           // L_child rappresenta L(x')
                OWLNamedIndividual child = create_individual();                                                         // Creo nuovo figlio child

                added_axioms = this.exists_rule(L_x, x, L_child, child, obj);
                                                                                                                        
                added_axioms.addAll(this.all_values_rule(owl_all_values_set, L_child, child, property));

                blocking_list.add(L_x);
                clash_free = this.tableau_algorithm_non_empty_tbox_lazy_unfolding(child, blocking_list, L_child);

                if(!clash_free){
                    this.clash_rollback_all(L_x, added_conj_lazy, x);
                    this.removeall_axiom_from_abox(added_axioms);
                    return false;
                }
            }
        }
        return clash_free;
    }
    
    private void print_class_expression_set(HashSet<? extends OWLClassExpression> expr_set, String name) {
        System.out.print(name + " = {");
        for (OWLClassExpression expr : expr_set) {
            expr.accept(this.printer_visitor);
            System.out.print(", ");
        }
        System.out.println("}");
    }

    public boolean tableau_algorithm(boolean lazy_unfolding){
        boolean clash_free = false;
        List<HashSet<OWLObject>> blocking_list = new ArrayList<>();
        if(lazy_unfolding)
            clash_free = this.tableau_algorithm_non_empty_tbox_lazy_unfolding(this.root, blocking_list, this.L_x);
        else
            clash_free = this.tableau_algorithm_non_empty_tbox(this.root, blocking_list, this.L_x);
        return clash_free;
    }

    public boolean tableau_algorithm_draw_graph(boolean lazy_unfolding, Node root_node, Resource root_rdf){
        boolean clash_free = false;
        List<HashSet<OWLObject>> blocking_list = new ArrayList<>();
        if(lazy_unfolding)
            clash_free = this.tableau_algorithm_non_empty_tbox_lazy_unfolding(this.root, blocking_list, this.L_x, root_node, root_rdf);
        else
            clash_free = this.tableau_algorithm_non_empty_tbox(this.root, blocking_list, this.L_x, root_node, root_rdf);
        return clash_free;
    }

    private void save_rdf_graph(String save_path){
        int duplicate_index = 1;
        String filename = "graph.rdf";
        Path path = Paths.get(save_path + "\\" + filename);
        try{
            while(Files.exists(path)){
                filename = "graph" + "_" + duplicate_index++ + ".rdf";
                path = Paths.get(save_path + "\\" + filename);
            }

            RDFWriter writer = this.rdf_model.getWriter("RDF/XML");
            writer.setProperty("showXmlDeclaration", "true");
            writer.setProperty("showDoctypeDeclaration", "true");
            writer.setProperty("tab", "8");
            Writer out = new BufferedWriter(new OutputStreamWriter(
                         new FileOutputStream(save_path.concat("\\").concat(filename)), "UTF8"));

            writer.write(this.rdf_model, out, null);
            
        }
        catch(IOException ex){
            System.out.println("Errore");
        }
    }

    public boolean check_consistency(String save_path, boolean lazy_unfolding){
        File labels_dir = new File("./labels");
        File graphs_dir = new File(save_path);
        boolean clash_free = false;
        Instant start, end;
        if(!labels_dir.exists()) labels_dir.mkdir();
        if(!graphs_dir.exists()) labels_dir.mkdir();
        
        if(this.draw_graph){
            // Grafo
            Node root_node = this.graph_drawer.create_new_node("x_0");
            this.last_child = root_node;
            // RDF
            Resource root_rdf = this.rdf_model.createResource(this.root.getIRI().toString());

            start = Instant.now();
            clash_free = this.tableau_algorithm_draw_graph(lazy_unfolding, root_node, root_rdf);
            end = Instant.now();

            if(clash_free)
                this.graph_drawer.add_clash_free_node(this.last_child);

            this.graph_drawer.save_graph(save_path);
            this.save_rdf_graph(save_path);
            System.out.println("Grafi salvati in " + save_path + "\n");
        }
        else{
            start = Instant.now();
            clash_free = this.tableau_algorithm(lazy_unfolding);
            end = Instant.now();
        }
        System.out.println("Elapsed Time: "+ Duration.between(start, end).toMillis()+"ms");
        return clash_free;
    }
}