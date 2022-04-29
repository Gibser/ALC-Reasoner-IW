package com.alcreasoning;
import java.io.File;
import java.io.IOException;
import java.time.Duration;
import java.time.Instant;
import java.util.HashMap;
import java.util.HashSet;
import java.util.stream.Collectors;

import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.ModelFactory;
import org.apache.jena.rdf.model.Property;
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
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLPropertyAssertionAxiom;

import guru.nidi.graphviz.attribute.Label;
import guru.nidi.graphviz.attribute.Label.Justification;
import guru.nidi.graphviz.engine.Format;
import guru.nidi.graphviz.engine.Graphviz;
import guru.nidi.graphviz.model.MutableGraph;
import guru.nidi.graphviz.model.MutableNode;
import guru.nidi.graphviz.model.Node;

import static guru.nidi.graphviz.model.Factory.*;

public class Reasoner {

    
    private AndVisitor or_visitor;
    private OrVisitor and_visitor;
    private FunnyVisitor v;
    private FunnyVisitor return_visitor;
    private OWLDataFactory factory;
    HashSet<OWLObject> abox = new HashSet<OWLObject>();
    HashSet<OWLObject> L_x = new HashSet<OWLObject>();
    HashSet<OWLLogicalAxiom> T_u = new HashSet<OWLLogicalAxiom>();
    private IRI ontology_iri;
    private int node_index = -1;
    private OWLClassExpression Ĉ = null;
    private OWLNamedIndividual root;
    private LazyUnfoldingVisitor lazy_unfolding_v;
    private GraphDrawer graph_drawer;
    private Node last_parent;
    private Node last_child;
    private boolean draw_graph;
    private boolean can_draw_clash_free = false;
    private Model rdf_model;


    private Reasoner(IRI ontology_iri, boolean draw_graph){
        this.factory = OntologyPreprocessor.concept_man.getOWLDataFactory();
        this.ontology_iri = ontology_iri;
        this.or_visitor = new AndVisitor();
        this.and_visitor = new OrVisitor();
        this.v = new FunnyVisitor();
        this.return_visitor = new FunnyVisitor(true);
        this.graph_drawer = new GraphDrawer("ALC Tableaux");
        this.draw_graph = draw_graph;
        if(this.draw_graph)
            rdf_model = ModelFactory.createDefaultModel();
        //this.graph = ModelFactory.createDefaultModel();
    }

    public Reasoner(OWLClassExpression concept_name, OWLClassExpression concept, IRI ontology_iri, boolean draw_graph){
        this(ontology_iri, draw_graph);
        this.L_x.add(concept);
        this.root = this.create_individual();
        this.add_axiom_to_abox(concept_name, root);
    }

    public Reasoner(OWLClassExpression Ĉ, HashSet<OWLClassExpression> KB_with_concept_name, HashSet<OWLClassExpression> KB_with_concept, IRI ontology_iri, boolean draw_graph){
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
        this.lazy_unfolding_v = new LazyUnfoldingVisitor();
    }


    private boolean check_not_clash(HashSet<OWLObject> L_x){
        HashSet<OWLObject> atomic_concept = new HashSet<OWLObject>();
        HashSet<OWLObject> not_atomic_concept = new HashSet<OWLObject>();

        if(L_x.contains(this.factory.getOWLNothing()))
            return false;

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
        int i = 0;
        System.out.print("L_x = {");
        for(OWLObject obj : L_x){
            obj.accept(this.v);
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

    private void print_L_x_temp(HashSet<OWLObject> L_x_temp){
        int i = 0;
        System.out.print("L_x_temp = {");
        for(OWLObject obj : L_x_temp){
            obj.accept(this.v);
            if(i++ < L_x.size()-1) System.out.print(", "); else System.out.print("}\n");
        }
    }

    private void print_abox(){
        int i = 0;
        System.out.print("ABox = {");
        for(OWLObject obj : this.abox){
            obj.accept(this.v);
            if(i++ < this.abox.size()-1) System.out.print(", "); else System.out.print("}\n");
        }
    }

    private boolean add_axiom_to_abox(OWLObject axm, OWLNamedIndividual x){
        return this.abox.add(this.factory.getOWLClassAssertionAxiom((OWLClassExpression) axm, x));
    }

    private boolean add_axiom_to_abox(OWLObject axm){
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

    private void removeall_axiom_from_abox(HashSet<? extends OWLObject> axms){
        this.abox.removeAll(axms);
    }

    private OWLNamedIndividual create_individual(){
        return this.factory.getOWLNamedIndividual(IRI.create(this.ontology_iri+ "#x_" + ++this.node_index));
    }

    private boolean add_axiom_to_abox(OWLObjectPropertyExpression relation, OWLNamedIndividual x1, OWLNamedIndividual x2){
        return this.abox.add(this.instantiate_property_axiom(relation, x1, x2));
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

    private OWLObjectPropertyAssertionAxiom instantiate_property_axiom(OWLObjectPropertyExpression relation, OWLNamedIndividual x1, OWLNamedIndividual x2){
        return this.factory.getOWLObjectPropertyAssertionAxiom(relation, x1, x2);
    }

    
    /*
    public boolean tableau_algorithm(OWLNamedIndividual x, HashSet<OWLObject> L_x, int node_index){
        HashSet<OWLClassExpression> disjointed;
        HashSet<OWLObjectSomeValuesFrom> owl_some_values_set;
        HashSet<OWLObjectAllValuesFrom> owl_all_values_set;
        HashSet<OWLObject> added_joint;  // ;)
        boolean clash_free = false;

        for(OWLObject obj : L_x){
            obj.accept(or_visitor);
        }

        
        L_x.addAll(or_visitor.get_rule_set());
        added_joint = this.addall_axiom_to_abox(or_visitor.get_rule_set_and_reset(), x);
        
        ////
        System.out.println();
        System.out.println("############# Chiamata ricorsiva #############");
        System.out.print("Inizio chiamata. ");
        this.print_L_x(L_x);
        this.print_abox();
        System.out.println("-----------------------------------");
        System.out.println("Applicazione regola unione");
        System.out.println("-----------------------------------");
        ////

        HashSet<OWLObjectUnionOf> disjunctions;

        disjunctions = L_x.stream().filter(e -> e instanceof OWLObjectUnionOf)
                                  .map(e -> (OWLObjectUnionOf)e)
                                  .collect(Collectors.toCollection(HashSet::new));

        for(OWLClassExpression obj : disjunctions){
            ////
            System.out.print("Processo ");
            obj.accept(v);
            System.out.println();
            ////
            obj.accept(and_visitor);
            disjointed = and_visitor.get_rule_set_and_reset();
            boolean is_present = false;
            for(OWLObject disj : disjointed){
                if(this.abox.contains(this.factory.getOWLClassAssertionAxiom((OWLClassExpression) disj, x))){
                    is_present = true;
                    break;
                }
            }
            
            if(!is_present && !disjointed.isEmpty()){
                for(OWLObject disj : disjointed){
                    HashSet<OWLObject> L_x_with_disj = (HashSet<OWLObject>)L_x.clone();
                    L_x_with_disj.add(disj);
                    this.add_axiom_to_abox(disj, x);
                    ////
                    System.out.print("Aggiungo ");
                    disj.accept(this.v);
                    System.out.println();
                    ////
                    clash_free = tableau_algorithm(x, L_x_with_disj, node_index);
                    if(clash_free){
                        break;
                    }
                    else{
                        L_x.remove(disj);
                        this.abox.remove(this.factory.getOWLClassAssertionAxiom((OWLClassExpression) disj, x));
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
        if(!(clash_free = this.check_not_clash(L_x))){
            // rimuovo congiunti dall'ABox
            this.removeall_axiom_from_abox(added_joint);
            return false;
        }

        owl_some_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectSomeValuesFrom)).map(e -> (OWLObjectSomeValuesFrom)e).collect(Collectors.toCollection(HashSet::new));
        owl_all_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectAllValuesFrom)).map(e -> (OWLObjectAllValuesFrom)e).collect(Collectors.toCollection(HashSet::new));
        

        System.out.println("-----------------------------------");
        System.out.println("Applicazione regola esiste");
        System.out.println("-----------------------------------");
        for(OWLObjectSomeValuesFrom obj : owl_some_values_set){
            OWLClassExpression filler = obj.getFiller();
            OWLObjectPropertyExpression property = obj.getProperty();
            boolean exists_rule_condition =
                this.abox.stream()                                                                                      // exists R.C
                    .filter(e -> e instanceof OWLObjectPropertyAssertionAxiom)                                          // Raccolgo tutte le relazioni
                    .map(e -> (OWLObjectPropertyAssertionAxiom)e)                                                       // Cast    
                    .filter(e -> e.getProperty().equals(property))                                                      // Filtro tutte le relazioni di tipo R    
                    .filter(e -> e.getSubject().equals(x))                                                              // Filtro tutte le relazioni R da x a qualche z
                    .filter(e -> !this.abox.contains(this.factory.getOWLClassAssertionAxiom(filler, e.getObject())))    // Filtro le relazioni tali che C(z)
                    .count() == 0;

            if(exists_rule_condition){
                HashSet<OWLObject> added_axioms = new HashSet<>();
                HashSet<OWLObject> L_child = new HashSet<>();                                                           // L_child rappresenta L(x')
                OWLNamedIndividual child = create_individual();                                                         // Creo nuovo figlio child
                ///
                //System.out.println("\n\nNuovo figlio: x_" + this.node_index + "\n\n");
                ///
                OWLClassAssertionAxiom instantiated_axiom = this.instantiate_axiom(filler, child);
                OWLObjectPropertyAssertionAxiom instantiated_property_axiom = this.instantiate_property_axiom(property, x, child);
                
                if(this.add_axiom_to_abox(instantiated_axiom))
                    added_axioms.add(instantiated_axiom);                                                                                   // Si aggiunge C(child) all'ABox
                
                if(this.add_axiom_to_abox(instantiated_property_axiom))                                                            // Si aggiunge R(x, child) all'ABox 
                    added_axioms.add(instantiated_property_axiom);

                L_child.add(filler);                                                                                    // L(x') = {C}
                
                owl_all_values_set.stream()                                                                                      // forall R.D
                    .filter(e -> e.getProperty().equals(property))                                                      // Filtra i per ogni con la stessa relazione R
                    .forEach(e -> {
                                    L_child.add(e.getFiller());
                                    if(this.add_axiom_to_abox(e.getFiller(), child)) 
                                        added_axioms.add(this.instantiate_axiom(e.getFiller(), child));
                                  });          
                clash_free = tableau_algorithm(child, L_child, this.node_index);

                if(!clash_free){
                    this.removeall_axiom_from_abox(added_axioms);
                    break;
                }
            }
        }
        System.out.println("Fine chiamata nodo x_" + node_index);
        System.out.println("Clash free: " + clash_free);
        return clash_free;
    }
    */
    private Node update_graph(boolean or_branch, Node node, String individual_name, OWLObjectPropertyExpression property){
        Node child_node = null;
        if(this.draw_graph){
            if(or_branch)
                child_node = this.graph_drawer.add_new_child(node, "" + FunnyVisitor.union, individual_name);
            else{
                property.accept(this.return_visitor);
                child_node = this.graph_drawer.add_new_child(node, this.return_visitor.get_and_destroy_return_string(), individual_name);
            }
        }

        return child_node;
    }

    private boolean check_bottom(OWLObjectPropertyExpression property, OWLClassExpression expr1, OWLClassExpression filler, HashMap<OWLObjectPropertyExpression, OWLClassExpression> properties_fillers){
        return properties_fillers.containsKey(property) && properties_fillers.get(property).equals(expr1) && !filler.equals(expr1);
    }

    public boolean tableau_algorithm_non_empty_tbox(OWLNamedIndividual x, HashSet<OWLObject> L_parent, HashSet<OWLObject> L_x, Node node, Resource node_rdf){
        HashSet<OWLClassExpression> disjointed;
        HashSet<OWLObjectSomeValuesFrom> owl_some_values_set;
        HashSet<OWLObjectAllValuesFrom> owl_all_values_set;
        HashSet<OWLClassExpression> added_joint;  // ;)
        HashSet<OWLClassAssertionAxiom> instantiated_added_joint;
        HashMap<OWLObjectPropertyExpression, OWLClassExpression> properties_fillers = null;     // HashMap per conservare gli elementi <relazione, concetto>
        boolean clash_free = false;
        
        for(OWLObject obj : L_x){
            obj.accept(or_visitor);
        }
        
        L_x.addAll(or_visitor.get_rule_set());

        // Blocking
        if(this.Ĉ != null && this.blocking(L_parent, L_x)){
            System.out.println("Blocking");
            return true;
        }

        // Grafo: Aggiungo L_x al nodo dopo regola AND
        node = this.graph_drawer.add_L_x_to_node(node, L_x, x.getIRI().getShortForm());
        // RDF
        node_rdf.addProperty(this.rdf_model.createProperty(this.ontology_iri + "/#L_x"), this.graph_drawer.return_set_as_string(L_x, "L_" + x.getIRI().getShortForm()));


        added_joint = this.addall_axiom_to_abox(or_visitor.get_rule_set_and_reset(), x);
        instantiated_added_joint = this.instantiateall_axiom(added_joint, x);
        //added_joint = this.addall_axiom_to_abox(or_visitor.get_rule_set_and_reset(), x);
        
        // TODO: Controllare effettivo tempo risparmiato senza stampe
        if(!this.check_not_clash(L_x)){
            // rimuovo congiunti da L_x
            L_x.removeAll(added_joint);
            // rimuovo congiunti dall'ABox
            this.removeall_axiom_from_abox(instantiated_added_joint);
            this.graph_drawer.add_clash_node(node);
            //RDF
            node_rdf.addProperty(this.rdf_model.createProperty(this.ontology_iri + "/#clash"), "CLASH");
            return false;
        }
        
        ////
        System.out.println();
        System.out.println("############# Chiamata ricorsiva #############");
        System.out.print("Inizio chiamata. ");
        
        this.print_L_x(L_x);
        System.out.println();
        this.print_abox();
        System.out.println();
        System.out.println("-----------------------------------");
        System.out.println("Applicazione regola unione");
        System.out.println("-----------------------------------");
        ////
        
        HashSet<OWLObjectUnionOf> disjunctions;

        disjunctions = L_x.stream().filter(e -> e instanceof OWLObjectUnionOf)
                                  .map(e -> (OWLObjectUnionOf)e)
                                  .collect(Collectors.toCollection(HashSet::new));

        for(OWLObjectUnionOf obj : disjunctions){
            
            ////
            System.out.print("Processo ");
            obj.accept(v);
            System.out.println();
            ////
            
            obj.accept(and_visitor);
            disjointed = and_visitor.get_rule_set_and_reset();
            boolean is_present = false;
            for(OWLClassExpression disj : disjointed){
                if(this.abox.contains(this.factory.getOWLClassAssertionAxiom((OWLClassExpression) disj, x))){
                    System.out.println("Trovato");
                    is_present = true;
                    break;
                }
            }
            
            if(!is_present){
                for(OWLObject disj : disjointed){
                    //HashSet<OWLObject> L_x_with_disj = new HashSet<>(L_x);
                    L_x.add(disj);
                    this.add_axiom_to_abox(disj, x);
                    
                    ////
                    System.out.print("Aggiungo ");
                    disj.accept(this.v);
                    System.out.println();
                    ////
                    
                    // Grafo
                    this.last_child = this.update_graph(true, node, x.getIRI().getShortForm(), null);
                    // RDF
                    Resource rdf_union_node = this.rdf_model.createResource();
                    node_rdf.addProperty(this.rdf_model.createProperty(this.ontology_iri + "/#union"), rdf_union_node);

                    clash_free = tableau_algorithm_non_empty_tbox(x, null, L_x, this.last_child, rdf_union_node);
                    if(clash_free){
                        // Grafo
                        this.last_parent = this.last_child;
                        //
                        break;
                    }
                    else{
                        L_x.remove(disj);
                        this.abox.remove(this.factory.getOWLClassAssertionAxiom((OWLClassExpression) disj, x));
                    }
                }
                // Se finiscono i disgiunti e clash_free è ancora false, vuol dire che nessuna combinazione di disgiunti evita un clash, 
                // quindi posso ritornare false
                if(!clash_free){
                    System.out.println("Disgiunti terminati: " + clash_free + "\n");
                    return false;
                }
                
            }

            // Se ho trovato un ramo clash free, posso interrompere l'iterazione e ritornare true
            // altrimenti si procede con l'iterazione
            if(clash_free){
                return true;
            }
            
        }
        // Controllo se localmente ci sono clash
        if(!(clash_free = this.check_not_clash(L_x))){
            // rimuovo congiunti da L_x
            L_x.removeAll(added_joint);
            // rimuovo congiunti dall'ABox
            this.removeall_axiom_from_abox(instantiated_added_joint);
            // Grafo
            this.graph_drawer.add_clash_node(node);
            //RDF
            node_rdf.addProperty(this.rdf_model.createProperty(this.ontology_iri + "/#clash"), "CLASH");
            return false;
        }

        owl_some_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectSomeValuesFrom)).map(e -> (OWLObjectSomeValuesFrom)e).collect(Collectors.toCollection(HashSet::new));
        owl_all_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectAllValuesFrom)).map(e -> (OWLObjectAllValuesFrom)e).collect(Collectors.toCollection(HashSet::new));
        

        System.out.println("-----------------------------------");
        System.out.println("Applicazione regola esiste");
        System.out.println("-----------------------------------");

        // Per grafo
        int exists_processed = 0;
        
        
        if(!owl_some_values_set.isEmpty()){
            properties_fillers = new HashMap<>();
        }


        for(OWLObjectSomeValuesFrom obj : owl_some_values_set){
            // Per grafo: Se sono arrivato all'ultimo esiste da valutare, allora posso iniziare a settare true can_draw_clash_free.
            // Se l'ultimo esiste è clash free allora verrà rappresentato nel grafo, altrimenti ci sarà il return false
            if(++exists_processed == owl_some_values_set.size())
                this.can_draw_clash_free = true;

            OWLClassExpression filler = obj.getFiller();
            OWLObjectPropertyExpression property = obj.getProperty();
            boolean exists_rule_condition[] = {false};
            
            // Se nel nodo attuale ho processato un Property some bottom, non puó esserci un altro figlio di relazione Property, 
            // oppure se ho processato un Property some C non posso trovare un Property some bottom, quindi insoddisfacibile
            if(this.check_bottom(property, this.factory.getOWLNothing(), filler, properties_fillers) || 
               this.check_bottom(property, filler, this.factory.getOWLNothing(), properties_fillers)  
              ){
                // rimuovo congiunti da L_x
                L_x.removeAll(added_joint);
                // rimuovo congiunti dall'ABox
                this.removeall_axiom_from_abox(instantiated_added_joint);
                // Grafo
                this.graph_drawer.add_clash_node(node);
                //RDF
                node_rdf.addProperty(this.rdf_model.createProperty(this.ontology_iri + "/#clash"), "CLASH");
                return false;
            }

            properties_fillers.put(property, filler);

            if(filler.equals(this.factory.getOWLNothing()))
                continue;                                          // Non creo un figlio se il filler è bottom

            this.abox.stream()                                                                                                                                      // exists R.C
                    .filter(e -> e instanceof OWLObjectPropertyAssertionAxiom)                                                                                      // Raccolgo tutte le relazioni
                    .map(e -> (OWLObjectPropertyAssertionAxiom)e)                                                                                                   // Cast    
                    .filter(e -> e.getProperty().equals(property))                                                                                                  // Filtro tutte le relazioni di tipo R    
                    .filter(e -> e.getSubject().equals(x))                                                                                                          // Filtro tutte le relazioni R da x a qualche z
                    .forEach(e -> {if(this.abox.contains(this.factory.getOWLClassAssertionAxiom(filler, e.getObject()))){ exists_rule_condition[0] = true;} });     // Filtro le relazioni tali che C(z)
                    //.filter(e -> !this.abox.contains(this.factory.getOWLClassAssertionAxiom(filler, e.getObject())))    // Filtro le relazioni tali che C(z)
                    //.count() == 0;
            
            if(!exists_rule_condition[0]){
                HashSet<OWLObject> added_axioms = new HashSet<>();
                HashSet<OWLObject> L_child = new HashSet<>();                                                           // L_child rappresenta L(x')
                OWLNamedIndividual child = create_individual();                                                         // Creo nuovo figlio child
                ///
                //System.out.println("\n\nNuovo figlio: x_" + this.node_index + "\n\n");
                ///
                OWLClassAssertionAxiom instantiated_axiom = this.instantiate_axiom(filler, child);
                OWLObjectPropertyAssertionAxiom instantiated_property_axiom = this.instantiate_property_axiom(property, x, child);
                
                if(this.add_axiom_to_abox(instantiated_axiom))
                    added_axioms.add(instantiated_axiom);                                                                                   // Si aggiunge C(child) all'ABox
                
                if(this.add_axiom_to_abox(instantiated_property_axiom))                                                            // Si aggiunge R(x, child) all'ABox 
                    added_axioms.add(instantiated_property_axiom);
                
                if(this.Ĉ != null){                                                                                                // TBox non vuota: L(x') U {Ĉ}
                    L_child.add(this.Ĉ);        
                    instantiated_axiom = this.instantiate_axiom(this.Ĉ, child);
                    if(this.add_axiom_to_abox(instantiated_axiom))                                                                 // Si aggiunge Ĉ(child) all'ABox
                        added_axioms.add(instantiated_axiom);
                }

                
                L_child.add(filler);                                                                                    // L(x') U {C};
                                                                                                                        
                

                owl_all_values_set.stream()                                                                             // forall R.D
                    .filter(e -> e.getProperty().equals(property))                                                      // Filtra i per ogni con la stessa relazione R
                    .forEach(e -> {
                                    L_child.add(e.getFiller());
                                    if(this.add_axiom_to_abox(e.getFiller(), child))                                    // cambiato x a child, va istanziato per il figlio, non per x
                                        added_axioms.add(this.instantiate_axiom(e.getFiller(), child));                 // cambiato x a child
                                  });
                
                // Grafo
                //Node child_node = this.update_graph(false, node, child.getIRI().getShortForm(), property);
                this.last_child = this.update_graph(false, node, child.getIRI().getShortForm(), property);
                // RDF
                Resource rdf_child_node = this.rdf_model.createResource(child.getIRI().toString());
                property.accept(this.return_visitor);
                node_rdf.addProperty(this.rdf_model.createProperty(this.ontology_iri + "/#" + this.return_visitor.get_and_destroy_return_string()), rdf_child_node);

                clash_free = tableau_algorithm_non_empty_tbox(child, L_x, L_child, this.last_child, rdf_child_node);

                if(!clash_free){
                    // Aggiunto per risolvere bug di disgiunti non rimossi dopo clash
                    // rimuovo congiunti da L_x
                    L_x.removeAll(added_joint);
                    // rimuovo congiunti dall'ABox
                    this.removeall_axiom_from_abox(instantiated_added_joint);

                    this.removeall_axiom_from_abox(added_axioms);
                    // Grafo
                    this.can_draw_clash_free = false;
                    return false;                                   // posso fare direttamente return false invece di break(?)
                    //break;
                }
                
                else{
                    node = this.last_child;
                    node_rdf = rdf_child_node;
                }
            }
        }
        System.out.println("Fine chiamata nodo " + x.getIRI().getShortForm());
        System.out.println("Clash free: " + clash_free);
        /*
        // Grafo
        if(clash_free && this.can_draw_clash_free){//&& owl_some_values_set.isEmpty() ){
            this.graph_drawer.add_clash_free_node(node);
            this.can_draw_clash_free = false;
        }
        // Se il nodo è clash free inserisco solo il nodo generato (serve principalmente per far stampare il label)
        else if(clash_free && owl_some_values_set.isEmpty() && !this.can_draw_clash_free)
            this.graph_drawer.add_new_child(node);
            //this.graph_drawer.add_child_clash_free_node(node);
        */
        this.graph_drawer.add_new_child(node);
        ///////////
        System.out.println("Fine");
        return clash_free;
    }

    // Senza grafo
    public boolean tableau_algorithm_non_empty_tbox(OWLNamedIndividual x, HashSet<OWLObject> L_parent, HashSet<OWLObject> L_x){
        HashSet<OWLClassExpression> disjointed;
        HashSet<OWLObjectSomeValuesFrom> owl_some_values_set;
        HashSet<OWLObjectAllValuesFrom> owl_all_values_set;
        HashSet<OWLClassExpression> added_joint;  // ;)
        HashSet<OWLClassAssertionAxiom> instantiated_added_joint;
        HashMap<OWLObjectPropertyExpression, OWLClassExpression> properties_fillers = null;     // HashMap per conservare gli elementi <relazione, concetto>
        boolean clash_free = false;
        
        for(OWLObject obj : L_x){
            obj.accept(or_visitor);
        }
        
        L_x.addAll(or_visitor.get_rule_set());

        // Blocking
        if(this.Ĉ != null && this.blocking(L_parent, L_x)){
            System.out.println("Blocking");
            return true;
        }


        added_joint = this.addall_axiom_to_abox(or_visitor.get_rule_set_and_reset(), x);
        instantiated_added_joint = this.instantiateall_axiom(added_joint, x);
        

        if(!this.check_not_clash(L_x)){
            // rimuovo congiunti da L_x
            L_x.removeAll(added_joint);
            // rimuovo congiunti dall'ABox
            this.removeall_axiom_from_abox(instantiated_added_joint);
            return false;
        }
        
        HashSet<OWLObjectUnionOf> disjunctions;

        disjunctions = L_x.stream().filter(e -> e instanceof OWLObjectUnionOf)
                                  .map(e -> (OWLObjectUnionOf)e)
                                  .collect(Collectors.toCollection(HashSet::new));

        for(OWLObjectUnionOf obj : disjunctions){
            
            obj.accept(and_visitor);
            disjointed = and_visitor.get_rule_set_and_reset();
            boolean is_present = false;
            for(OWLClassExpression disj : disjointed){
                if(this.abox.contains(this.factory.getOWLClassAssertionAxiom((OWLClassExpression) disj, x))){
                    is_present = true;
                    break;
                }
            }
            
            if(!is_present){
                for(OWLObject disj : disjointed){
                    L_x.add(disj);
                    this.add_axiom_to_abox(disj, x);
                    
                    clash_free = tableau_algorithm_non_empty_tbox(x, null, L_x);
                    
                    if(clash_free)
                        break; 
                    else{
                        L_x.remove(disj);
                        this.abox.remove(this.factory.getOWLClassAssertionAxiom((OWLClassExpression) disj, x));
                    }
                }
                // Se finiscono i disgiunti e clash_free è ancora false, vuol dire che nessuna combinazione di disgiunti evita un clash, 
                // quindi posso ritornare false
                if(!clash_free){
                    return false;
                }
                
            }

            // Se ho trovato un ramo clash free, posso interrompere l'iterazione e ritornare true
            // altrimenti si procede con l'iterazione
            if(clash_free){
                return true;
            }
            
        }
        // Controllo se localmente ci sono clash
        if(!(clash_free = this.check_not_clash(L_x))){
            // rimuovo congiunti da L_x
            L_x.removeAll(added_joint);
            // rimuovo congiunti dall'ABox
            this.removeall_axiom_from_abox(instantiated_added_joint);
            return false;
        }

        owl_some_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectSomeValuesFrom)).map(e -> (OWLObjectSomeValuesFrom)e).collect(Collectors.toCollection(HashSet::new));
        owl_all_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectAllValuesFrom)).map(e -> (OWLObjectAllValuesFrom)e).collect(Collectors.toCollection(HashSet::new));
        
        
        
        if(!owl_some_values_set.isEmpty()){
            properties_fillers = new HashMap<>();
        }


        for(OWLObjectSomeValuesFrom obj : owl_some_values_set){

            OWLClassExpression filler = obj.getFiller();
            OWLObjectPropertyExpression property = obj.getProperty();
            boolean exists_rule_condition[] = {false};
            
            // Se nel nodo attuale ho processato un Property some bottom, non puó esserci un altro figlio di relazione Property, 
            // oppure se ho processato un Property some C non posso trovare un Property some bottom, quindi insoddisfacibile
            if(this.check_bottom(property, this.factory.getOWLNothing(), filler, properties_fillers) || 
               this.check_bottom(property, filler, this.factory.getOWLNothing(), properties_fillers)  
              ){
                // rimuovo congiunti da L_x
                L_x.removeAll(added_joint);
                // rimuovo congiunti dall'ABox
                this.removeall_axiom_from_abox(instantiated_added_joint);
                return false;
            }

            properties_fillers.put(property, filler);

            if(filler.equals(this.factory.getOWLNothing()))
                continue;                                          // Non creo un figlio se il filler è bottom

            this.abox.stream()                                                                                                                                      // exists R.C
                    .filter(e -> e instanceof OWLObjectPropertyAssertionAxiom)                                                                                      // Raccolgo tutte le relazioni
                    .map(e -> (OWLObjectPropertyAssertionAxiom)e)                                                                                                   // Cast    
                    .filter(e -> e.getProperty().equals(property))                                                                                                  // Filtro tutte le relazioni di tipo R    
                    .filter(e -> e.getSubject().equals(x))                                                                                                          // Filtro tutte le relazioni R da x a qualche z
                    .forEach(e -> {if(this.abox.contains(this.factory.getOWLClassAssertionAxiom(filler, e.getObject()))){ exists_rule_condition[0] = true;} });     // Filtro le relazioni tali che C(z)
                    //.filter(e -> !this.abox.contains(this.factory.getOWLClassAssertionAxiom(filler, e.getObject())))    // Filtro le relazioni tali che C(z)
                    //.count() == 0;
            
            if(!exists_rule_condition[0]){
                HashSet<OWLObject> added_axioms = new HashSet<>();
                HashSet<OWLObject> L_child = new HashSet<>();                                                           // L_child rappresenta L(x')
                OWLNamedIndividual child = create_individual();                                                         // Creo nuovo figlio child
        
                OWLClassAssertionAxiom instantiated_axiom = this.instantiate_axiom(filler, child);
                OWLObjectPropertyAssertionAxiom instantiated_property_axiom = this.instantiate_property_axiom(property, x, child);
                
                if(this.add_axiom_to_abox(instantiated_axiom))
                    added_axioms.add(instantiated_axiom);                                                                                   // Si aggiunge C(child) all'ABox
                
                if(this.add_axiom_to_abox(instantiated_property_axiom))                                                            // Si aggiunge R(x, child) all'ABox 
                    added_axioms.add(instantiated_property_axiom);
                
                if(this.Ĉ != null){                                                                                                // TBox non vuota: L(x') U {Ĉ}
                    L_child.add(this.Ĉ);        
                    instantiated_axiom = this.instantiate_axiom(this.Ĉ, child);
                    if(this.add_axiom_to_abox(instantiated_axiom))                                                                 // Si aggiunge Ĉ(child) all'ABox
                        added_axioms.add(instantiated_axiom);
                }

                
                L_child.add(filler);                                                                                    // L(x') U {C};
                                                                                                                        
                

                owl_all_values_set.stream()                                                                             // forall R.D
                    .filter(e -> e.getProperty().equals(property))                                                      // Filtra i per ogni con la stessa relazione R
                    .forEach(e -> {
                                    L_child.add(e.getFiller());
                                    if(this.add_axiom_to_abox(e.getFiller(), child))                                    // cambiato x a child, va istanziato per il figlio, non per x
                                        added_axioms.add(this.instantiate_axiom(e.getFiller(), child));                 // cambiato x a child
                                  });
                
                clash_free = tableau_algorithm_non_empty_tbox(child, L_x, L_child);

                if(!clash_free){
                    this.removeall_axiom_from_abox(added_axioms);
                    return false;                                   // posso fare direttamente return false invece di break(?)
                    //break;
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
            if(L_x.contains(left_side) && !L_x.contains(right_side))
                added_axioms.add(right_side);
            
            // Per l'equivalenza, controllo anche se (not(A) in L_x) e (not(C) not in L_x)
            else if((ax instanceof OWLEquivalentClassesAxiom)                                   && 
                    L_x.contains(this.factory.getOWLObjectComplementOf(left_side).getNNF())     &&
                    !L_x.contains(this.factory.getOWLObjectComplementOf(right_side).getNNF())
                   )
                    added_axioms.add(this.factory.getOWLObjectComplementOf(this.lazy_unfolding_v.get_right_side()).getNNF());
        }
        return added_axioms;
    }

    private boolean blocking(HashSet<OWLObject> L_parent, HashSet<OWLObject> L_x){
        return L_parent == null ? false : L_parent.containsAll(L_x);
    }

    private boolean contains_and(HashSet<OWLClassExpression> added_lazy){
        for(OWLObject obj : added_lazy){
            if(obj instanceof OWLObjectIntersectionOf)
                return true;
        }
        return false;
    }


    public boolean tableau_algorithm_non_empty_tbox_lazy_unfolding(OWLNamedIndividual x, HashSet<OWLObject> L_parent, HashSet<OWLObject> L_x, Node node, Resource node_rdf){
        HashSet<OWLClassExpression> disjointed;
        HashSet<OWLObjectSomeValuesFrom> owl_some_values_set;
        HashSet<OWLObjectAllValuesFrom> owl_all_values_set;
        HashSet<OWLClassExpression> added_conj_lazy = new HashSet<>();
        HashSet<OWLClassAssertionAxiom> instantiated_added_conj_lazy = new HashSet<>();
        HashSet<OWLClassExpression> added_lazy = new HashSet<>();
        boolean clash_free = false;
        boolean apply_lazy_unfolding = true;
        HashMap<OWLObjectPropertyExpression, OWLClassExpression> properties_fillers = null;     // HashMap per conservare gli elementi <relazione, concetto>

        while(apply_lazy_unfolding){
            
            // Regola and
            for(OWLObject obj : L_x){
                obj.accept(or_visitor);
            }
            
            L_x.addAll(or_visitor.get_rule_set());

            // Regole lazy unfolding
            added_lazy = this.lazy_unfolding_rules(L_x);
            added_conj_lazy.addAll(added_lazy);
            L_x.addAll(added_conj_lazy); 

            if(this.contains_and(added_lazy))
                apply_lazy_unfolding = false;
        }

        // Blocking
        if(this.blocking(L_parent, L_x)){
            System.out.println("Blocking");
            return true;
        }

        // Grafo: Aggiungo L_x al nodo dopo regola AND
        node = this.graph_drawer.add_L_x_to_node(node, L_x, x.getIRI().getShortForm());
        // RDF
        node_rdf.addProperty(this.rdf_model.createProperty(this.ontology_iri + "/#L_x"), this.graph_drawer.return_set_as_string(L_x, "L_" + x.getIRI().getShortForm()));

        added_conj_lazy.addAll(this.addall_axiom_to_abox(or_visitor.get_rule_set_and_reset(), x));
        instantiated_added_conj_lazy = this.instantiateall_axiom(added_conj_lazy, x);
        //instantiated_added_conj_lazy.addAll(this.addall_axiom_to_abox(or_visitor.get_rule_set_and_reset(), x));
        System.out.println("Dopo istanza");


        // TODO: Controllare effettivo tempo risparmiato senza stampe
        if(!this.check_not_clash(L_x)){
            // rimuovo congiunti da L_x
            L_x.removeAll(added_conj_lazy);
            // rimuovo congiunti dall'ABox
            this.removeall_axiom_from_abox(instantiated_added_conj_lazy);
            this.graph_drawer.add_clash_node(node);
            //RDF
            node_rdf.addProperty(this.rdf_model.createProperty(this.ontology_iri + "/#clash"), "CLASH");
            return false;
        }

        ////
        System.out.println();
        System.out.println("############# Chiamata ricorsiva #############");
        System.out.print("Inizio chiamata. ");
        this.print_L_x(L_x);
        this.print_abox();
        System.out.println("-----------------------------------");
        System.out.println("Applicazione regola unione");
        System.out.println("-----------------------------------");
        ////

        HashSet<OWLObjectUnionOf> disjunctions;

        disjunctions = L_x.stream().filter(e -> e instanceof OWLObjectUnionOf)
                                  .map(e -> (OWLObjectUnionOf)e)
                                  .collect(Collectors.toCollection(HashSet::new));


        for(OWLClassExpression obj : disjunctions){
            ////
            System.out.print("Processo ");
            obj.accept(v);
            System.out.println();
            ////
            obj.accept(and_visitor);
            disjointed = and_visitor.get_rule_set_and_reset();
            boolean is_present = false;
            for(OWLObject disj : disjointed){
                if(this.abox.contains(this.factory.getOWLClassAssertionAxiom((OWLClassExpression) disj, x))){
                    is_present = true;
                    break;
                }
            }
            
            if(!is_present){
                for(OWLObject disj : disjointed){
                    //HashSet<OWLObject> L_x_with_disj = new HashSet<>(L_x);
                    L_x.add(disj);
                    this.add_axiom_to_abox(disj, x);
                    ////
                    System.out.print("Aggiungo ");
                    disj.accept(this.v);
                    System.out.println();
                    ////

                    // Grafo
                    Node child_node = this.update_graph(true, node, x.getIRI().getShortForm(), null);
                    // RDF
                    Resource rdf_union_node = this.rdf_model.createResource();
                    node_rdf.addProperty(this.rdf_model.createProperty(this.ontology_iri + "/#union"), rdf_union_node);


                    clash_free = this.tableau_algorithm_non_empty_tbox_lazy_unfolding(x, null, L_x, child_node, rdf_union_node);

                    if(clash_free){
                        // Grafo
                        this.last_parent = child_node;
                        //
                        break;
                    }
                    else{
                        L_x.remove(disj);
                        this.abox.remove(this.factory.getOWLClassAssertionAxiom((OWLClassExpression) disj, x));
                    }
                }
                // Se finiscono i disgiunti e clash_free è ancora false, vuol dire che nessuna combinazione di disgiunti evita un clash, 
                // quindi posso ritornare false
                if(!clash_free){
                    System.out.println("Disgiunti terminati: " + clash_free + "\n");
                    return false;
                }
            }
            // Se ho trovato un ramo clash free, posso interrompere l'iterazione e ritornare true
            // altrimenti si procede con l'iterazione
            
            if(clash_free){
                return true;
            }
            
        }
        // Controllo se localmente ci sono clash
        if(!(clash_free = this.check_not_clash(L_x))){
            // rimuovo congiunti da L_x
            L_x.removeAll(added_conj_lazy);
            // rimuovo congiunti e lazy dall'ABox
            this.removeall_axiom_from_abox(added_conj_lazy);
            // Grafo
            this.graph_drawer.add_clash_node(node);
            //RDF
            node_rdf.addProperty(this.rdf_model.createProperty(this.ontology_iri + "/#clash"), "CLASH");
            return false;
        }

        owl_some_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectSomeValuesFrom)).map(e -> (OWLObjectSomeValuesFrom)e).collect(Collectors.toCollection(HashSet::new));
        owl_all_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectAllValuesFrom)).map(e -> (OWLObjectAllValuesFrom)e).collect(Collectors.toCollection(HashSet::new));
        

        System.out.println("-----------------------------------");
        System.out.println("Applicazione regola esiste");
        System.out.println("-----------------------------------");

        // Per grafo
        int exists_processed = 0;

        if(!owl_some_values_set.isEmpty()){
            properties_fillers = new HashMap<>();
        }

        for(OWLObjectSomeValuesFrom obj : owl_some_values_set){
            // Per grafo: Se sono arrivato all'ultimo esiste da valutare, allora posso iniziare a settare true can_draw_clash_free.
            // Se l'ultimo esiste è clash free allora verrà rappresentato nel grafo, altrimenti ci sarà il return false
            if(++exists_processed == owl_some_values_set.size())
                this.can_draw_clash_free = true;
            
            OWLClassExpression filler = obj.getFiller();
            OWLObjectPropertyExpression property = obj.getProperty();
            boolean exists_rule_condition[] = {false};

            // Se nel nodo attuale ho processato un Property some bottom, non puó esserci un altro figlio di relazione Property, 
            // oppure se ho processato un Property some C non posso trovare un Property some bottom, quindi insoddisfacibile
            if(this.check_bottom(property, this.factory.getOWLNothing(), filler, properties_fillers) || 
               this.check_bottom(property, filler, this.factory.getOWLNothing(), properties_fillers)  
              ){
                // rimuovo congiunti dall'ABox
                this.removeall_axiom_from_abox(added_conj_lazy);
                // Grafo
                this.graph_drawer.add_clash_node(node);
                //RDF
            node_rdf.addProperty(this.rdf_model.createProperty(this.ontology_iri + "/#clash"), "CLASH");
                return false;
            }

            properties_fillers.put(property, filler);

            if(filler.equals(this.factory.getOWLNothing()))
                continue;

            this.abox.stream()                                                                                                                                      // exists R.C
                .filter(e -> e instanceof OWLObjectPropertyAssertionAxiom)                                                                                      // Raccolgo tutte le relazioni
                .map(e -> (OWLObjectPropertyAssertionAxiom)e)                                                                                                   // Cast    
                .filter(e -> e.getProperty().equals(property))                                                                                                  // Filtro tutte le relazioni di tipo R    
                .filter(e -> e.getSubject().equals(x))                                                                                                          // Filtro tutte le relazioni R da x a qualche z
                .forEach(e -> {if(this.abox.contains(this.factory.getOWLClassAssertionAxiom(filler, e.getObject()))){ exists_rule_condition[0] = true;} });     // Filtro le relazioni tali che C(z)
                //.filter(e -> !this.abox.contains(this.factory.getOWLClassAssertionAxiom(filler, e.getObject())))    // Filtro le relazioni tali che C(z)
                //.count() == 0;

            if(exists_rule_condition[0]){
                HashSet<OWLObject> added_axioms = new HashSet<>();
                HashSet<OWLObject> L_child = new HashSet<>();                                                           // L_child rappresenta L(x')
                OWLNamedIndividual child = create_individual();                                                         // Creo nuovo figlio child
                ///
                //System.out.println("\n\nNuovo figlio: x_" + this.node_index + "\n\n");
                ///
                OWLClassAssertionAxiom instantiated_axiom = this.instantiate_axiom(filler, child);
                OWLObjectPropertyAssertionAxiom instantiated_property_axiom = this.instantiate_property_axiom(property, x, child);
                
                if(this.add_axiom_to_abox(instantiated_axiom))
                    added_axioms.add(instantiated_axiom);                                                                          // Si aggiunge C(child) all'ABox
                
                if(this.add_axiom_to_abox(instantiated_property_axiom))                                                            // Si aggiunge R(x, child) all'ABox 
                    added_axioms.add(instantiated_property_axiom);
                
                if(this.Ĉ != null){                                                                                                // TBox non vuota: L(x') U {Ĉ}
                    L_child.add(this.Ĉ);        
                    instantiated_axiom = this.instantiate_axiom(this.Ĉ, child);
                    if(this.add_axiom_to_abox(instantiated_axiom))                                                                 // Si aggiunge Ĉ(child) all'ABox
                        added_axioms.add(instantiated_axiom);
                }

                L_child.add(filler);                                                                                               // L(x') U {C};
              
                /*
                // Vanno aggiunti anche gli assiomi dell'esiste perché vanno rimossi se il figlio non è clash free
                added_axioms.add(this.instantiate_axiom(filler, child));
                added_axioms.add(this.factory.getOWLObjectPropertyAssertionAxiom(property, x, child));
                added_axioms.add(this.instantiate_axiom(this.Ĉ, child));
                */

                owl_all_values_set.stream()                                                                                      // forall R.D
                    .filter(e -> e.getProperty().equals(property))                                                      // Filtra i per ogni con la stessa relazione R
                    .forEach(e -> {
                                    L_child.add(e.getFiller());
                                    if(this.add_axiom_to_abox(e.getFiller(), child)) 
                                        added_axioms.add(this.instantiate_axiom(e.getFiller(), child));
                                  });

                // Grafo
                Node child_node = this.update_graph(false, node, child.getIRI().getShortForm(), property);
                // RDF
                Resource rdf_child_node = this.rdf_model.createResource(child.getIRI().toString());
                property.accept(this.return_visitor);
                node_rdf.addProperty(this.rdf_model.createProperty(this.ontology_iri + "/#" + this.return_visitor.get_and_destroy_return_string()), rdf_child_node);


                clash_free = tableau_algorithm_non_empty_tbox_lazy_unfolding(child, L_x, L_child, child_node, rdf_child_node);

                if(!clash_free){
                    this.removeall_axiom_from_abox(added_axioms);
                    // Grafo
                    this.can_draw_clash_free = false;
                    //break;
                }
                else{
                    node = child_node;
                    node_rdf = rdf_child_node;
                }
            }
        }
        System.out.println("Fine chiamata nodo x_" + node_index);
        System.out.println("Clash free: " + clash_free);
        // Grafo
        if(clash_free && this.can_draw_clash_free){//&& owl_some_values_set.isEmpty() ){
            this.graph_drawer.add_clash_free_node(node);
            this.can_draw_clash_free = false;
        }
        // Se il nodo è clash free inserisco un nodo pallino verde
        else if(clash_free && owl_some_values_set.isEmpty() && !this.can_draw_clash_free)
            this.graph_drawer.add_child_clash_free_node(node);
        ///////////
        return clash_free;
    }

    public boolean tableau_algorithm_non_empty_tbox_lazy_unfolding(OWLNamedIndividual x, HashSet<OWLObject> L_parent, HashSet<OWLObject> L_x){
        HashSet<OWLClassExpression> disjointed;
        HashSet<OWLObjectSomeValuesFrom> owl_some_values_set;
        HashSet<OWLObjectAllValuesFrom> owl_all_values_set;
        HashSet<OWLClassExpression> added_conj_lazy = new HashSet<>();
        HashSet<OWLClassAssertionAxiom> instantiated_added_conj_lazy = new HashSet<>();
        HashSet<OWLClassExpression> added_lazy = new HashSet<>();
        boolean clash_free = false;
        boolean apply_lazy_unfolding = true;
        HashMap<OWLObjectPropertyExpression, OWLClassExpression> properties_fillers = null;     // HashMap per conservare gli elementi <relazione, concetto>

        while(apply_lazy_unfolding){
            
            // Regola and
            for(OWLObject obj : L_x){
                obj.accept(or_visitor);
            }
            
            L_x.addAll(or_visitor.get_rule_set());

            // Regole lazy unfolding
            added_lazy = this.lazy_unfolding_rules(L_x);
            added_conj_lazy.addAll(added_lazy);
            L_x.addAll(added_conj_lazy); 

            if(this.contains_and(added_lazy))
                apply_lazy_unfolding = false;
        }

        // Blocking
        if(this.blocking(L_parent, L_x)){
            System.out.println("Blocking");
            return true;
        }

        added_conj_lazy.addAll(this.addall_axiom_to_abox(or_visitor.get_rule_set_and_reset(), x));
        instantiated_added_conj_lazy = this.instantiateall_axiom(added_conj_lazy, x);
        System.out.println("Dopo istanza");

        if(!this.check_not_clash(L_x)){
            // rimuovo congiunti da L_x
            L_x.removeAll(added_conj_lazy);
            // rimuovo congiunti dall'ABox
            this.removeall_axiom_from_abox(instantiated_added_conj_lazy);
            return false;
        }

        HashSet<OWLObjectUnionOf> disjunctions;

        disjunctions = L_x.stream().filter(e -> e instanceof OWLObjectUnionOf)
                                  .map(e -> (OWLObjectUnionOf)e)
                                  .collect(Collectors.toCollection(HashSet::new));


        for(OWLClassExpression obj : disjunctions){
            obj.accept(and_visitor);
            disjointed = and_visitor.get_rule_set_and_reset();
            boolean is_present = false;
            for(OWLObject disj : disjointed){
                if(this.abox.contains(this.factory.getOWLClassAssertionAxiom((OWLClassExpression) disj, x))){
                    is_present = true;
                    break;
                }
            }
            
            if(!is_present){
                for(OWLObject disj : disjointed){
                    L_x.add(disj);
                    this.add_axiom_to_abox(disj, x);

                    clash_free = this.tableau_algorithm_non_empty_tbox_lazy_unfolding(x, null, L_x);

                    if(clash_free){
                        break;
                    }
                    else{
                        L_x.remove(disj);
                        this.abox.remove(this.factory.getOWLClassAssertionAxiom((OWLClassExpression) disj, x));
                    }
                }
                // Se finiscono i disgiunti e clash_free è ancora false, vuol dire che nessuna combinazione di disgiunti evita un clash, 
                // quindi posso ritornare false
                if(!clash_free){
                    System.out.println("Disgiunti terminati: " + clash_free + "\n");
                    return false;
                }
            }
            // Se ho trovato un ramo clash free, posso interrompere l'iterazione e ritornare true
            // altrimenti si procede con l'iterazione
            
            if(clash_free){
                return true;
            }
            
        }
        // Controllo se localmente ci sono clash
        if(!(clash_free = this.check_not_clash(L_x))){
            // rimuovo congiunti da L_x
            L_x.removeAll(added_conj_lazy);
            // rimuovo congiunti dall'ABox
            this.removeall_axiom_from_abox(instantiated_added_conj_lazy);
            return false;
        }

        owl_some_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectSomeValuesFrom)).map(e -> (OWLObjectSomeValuesFrom)e).collect(Collectors.toCollection(HashSet::new));
        owl_all_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectAllValuesFrom)).map(e -> (OWLObjectAllValuesFrom)e).collect(Collectors.toCollection(HashSet::new));
        
        if(!owl_some_values_set.isEmpty()){
            properties_fillers = new HashMap<>();
        }

        for(OWLObjectSomeValuesFrom obj : owl_some_values_set){
            OWLClassExpression filler = obj.getFiller();
            OWLObjectPropertyExpression property = obj.getProperty();
            boolean exists_rule_condition[] = {false};

            // Se nel nodo attuale ho processato un Property some bottom, non puó esserci un altro figlio di relazione Property, 
            // oppure se ho processato un Property some C non posso trovare un Property some bottom, quindi insoddisfacibile
            if(this.check_bottom(property, this.factory.getOWLNothing(), filler, properties_fillers) || 
               this.check_bottom(property, filler, this.factory.getOWLNothing(), properties_fillers)  
              ){
                // rimuovo congiunti da L_x
                L_x.removeAll(added_conj_lazy);
                // rimuovo congiunti dall'ABox
                this.removeall_axiom_from_abox(instantiated_added_conj_lazy);
                return false;
            }

            properties_fillers.put(property, filler);

            if(filler.equals(this.factory.getOWLNothing()))
                continue;

            this.abox.stream()                                                                                                                                      // exists R.C
                .filter(e -> e instanceof OWLObjectPropertyAssertionAxiom)                                                                                      // Raccolgo tutte le relazioni
                .map(e -> (OWLObjectPropertyAssertionAxiom)e)                                                                                                   // Cast    
                .filter(e -> e.getProperty().equals(property))                                                                                                  // Filtro tutte le relazioni di tipo R    
                .filter(e -> e.getSubject().equals(x))                                                                                                          // Filtro tutte le relazioni R da x a qualche z
                .forEach(e -> {if(this.abox.contains(this.factory.getOWLClassAssertionAxiom(filler, e.getObject()))){ exists_rule_condition[0] = true;} });     // Filtro le relazioni tali che C(z)
                //.filter(e -> !this.abox.contains(this.factory.getOWLClassAssertionAxiom(filler, e.getObject())))    // Filtro le relazioni tali che C(z)
                //.count() == 0;

            if(exists_rule_condition[0]){
                HashSet<OWLObject> added_axioms = new HashSet<>();
                HashSet<OWLObject> L_child = new HashSet<>();                                                           // L_child rappresenta L(x')
                OWLNamedIndividual child = create_individual();                                                         // Creo nuovo figlio child
                ///
                //System.out.println("\n\nNuovo figlio: x_" + this.node_index + "\n\n");
                ///
                OWLClassAssertionAxiom instantiated_axiom = this.instantiate_axiom(filler, child);
                OWLObjectPropertyAssertionAxiom instantiated_property_axiom = this.instantiate_property_axiom(property, x, child);
                
                if(this.add_axiom_to_abox(instantiated_axiom))
                    added_axioms.add(instantiated_axiom);                                                                          // Si aggiunge C(child) all'ABox
                
                if(this.add_axiom_to_abox(instantiated_property_axiom))                                                            // Si aggiunge R(x, child) all'ABox 
                    added_axioms.add(instantiated_property_axiom);
                
                if(this.Ĉ != null){                                                                                                // TBox non vuota: L(x') U {Ĉ}
                    L_child.add(this.Ĉ);        
                    instantiated_axiom = this.instantiate_axiom(this.Ĉ, child);
                    if(this.add_axiom_to_abox(instantiated_axiom))                                                                 // Si aggiunge Ĉ(child) all'ABox
                        added_axioms.add(instantiated_axiom);
                }

                L_child.add(filler);                                                                                               // L(x') U {C};
              
                /*
                // Vanno aggiunti anche gli assiomi dell'esiste perché vanno rimossi se il figlio non è clash free
                added_axioms.add(this.instantiate_axiom(filler, child));
                added_axioms.add(this.factory.getOWLObjectPropertyAssertionAxiom(property, x, child));
                added_axioms.add(this.instantiate_axiom(this.Ĉ, child));
                */

                owl_all_values_set.stream()                                                                                      // forall R.D
                    .filter(e -> e.getProperty().equals(property))                                                      // Filtra i per ogni con la stessa relazione R
                    .forEach(e -> {
                                    L_child.add(e.getFiller());
                                    if(this.add_axiom_to_abox(e.getFiller(), child)) 
                                        added_axioms.add(this.instantiate_axiom(e.getFiller(), child));
                                  });


                clash_free = tableau_algorithm_non_empty_tbox_lazy_unfolding(child, L_x, L_child);

                if(!clash_free){
                    this.removeall_axiom_from_abox(added_axioms);
                    //break;
                }
            }
        }
        return clash_free;
    }

    public boolean tableau_algorithm(boolean lazy_unfolding){
        boolean clash_free = false;
        if(lazy_unfolding && this.Ĉ != null)
            clash_free = this.tableau_algorithm_non_empty_tbox_lazy_unfolding(this.root, null, this.L_x);
        else
            clash_free = this.tableau_algorithm_non_empty_tbox(this.root, null, this.L_x);
        return clash_free;
    }

    public boolean tableau_algorithm_draw_graph(boolean lazy_unfolding, Node root_node, Resource root_rdf){
        boolean clash_free = false;
        if(lazy_unfolding && this.Ĉ != null)
            clash_free = this.tableau_algorithm_non_empty_tbox_lazy_unfolding(this.root, null, this.L_x, root_node, root_rdf);
        else
            clash_free = this.tableau_algorithm_non_empty_tbox(this.root, null, this.L_x, root_node, root_rdf);
        return clash_free;
    }


    public boolean check_consistency(String save_path, boolean lazy_unfolding){
        File dir = new File("./ProgettoIW/labels");
        boolean clash_free = false;
        Instant start, end;
        if(!dir.exists())
            dir.mkdir();
        
        if(this.draw_graph){
            // Grafo
            Node root_node = this.graph_drawer.create_new_node("x_0");
            this.last_child = root_node;
            // RDF
            Resource root_rdf = this.rdf_model.createResource(this.root.getIRI().toString());

            start = Instant.now();
            clash_free = this.tableau_algorithm_draw_graph(lazy_unfolding, root_node, root_rdf);
            end = Instant.now();
            this.rdf_model.write(System.out);
            this.graph_drawer.add_clash_free_node(this.last_child);
            this.graph_drawer.save_graph(save_path);
        }
        else{
            start = Instant.now();
            clash_free = this.tableau_algorithm(lazy_unfolding);
            end = Instant.now();
        }
        System.out.println("\nElapsed Time: "+ Duration.between(start, end).toMillis()+"ms");
        return clash_free;
    }

}