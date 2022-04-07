package com.alcreasoning;
import java.util.HashSet;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.semanticweb.owlapi.metrics.GCICount;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObject;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;


public class Reasoner {

    private AndVisitor or_visitor;
    private OrVisitor and_visitor;
    private FunnyVisitor v;
    private OWLDataFactory factory;
    HashSet<OWLObject> abox = new HashSet<OWLObject>();
    HashSet<OWLObject> L_x = new HashSet<OWLObject>();
    private IRI ontology_iri;
    private int node_index = -1;
    private OWLClassExpression Ĉ = null;
    private OWLNamedIndividual root;

    private Reasoner(IRI ontology_iri){
        this.factory = OntologyPreprocessor.concept_man.getOWLDataFactory();
        this.ontology_iri = ontology_iri;
        this.or_visitor = new AndVisitor();
        this.and_visitor = new OrVisitor();
        this.v = new FunnyVisitor();
    }

    public Reasoner(OWLClassExpression concept_name, OWLClassExpression concept, IRI ontology_iri){
        this(ontology_iri);
        this.L_x.add(concept);
        this.root = this.create_individual();
        this.add_axiom_to_abox(concept_name, root);
    }

    public Reasoner(OWLClassExpression Ĉ, HashSet<OWLObject> KB_with_concept_name, HashSet<OWLObject> KB_with_concept, IRI ontology_iri){
        this(ontology_iri);
        this.L_x.addAll(KB_with_concept);
        this.root = this.create_individual();
        this.addall_axiom_to_abox(KB_with_concept_name, root);
        this.Ĉ = Ĉ;
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
        int i = 0;
        System.out.print("L_x = {");
        for(OWLObject obj : L_x){
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

    private HashSet<OWLObject> addall_axiom_to_abox(HashSet<OWLObject> axms, OWLNamedIndividual x){
        HashSet<OWLObject> added_items = new HashSet<>();
        for(OWLObject obj : axms){
            OWLClassAssertionAxiom inst_axm = this.factory.getOWLClassAssertionAxiom((OWLClassExpression) obj, x);
            if(this.abox.add(inst_axm))
                added_items.add(inst_axm);
        }
        return added_items;
    }

    private void removeall_axiom_from_abox(HashSet<OWLObject> axms){
        this.abox.removeAll(axms);
    }


    private OWLNamedIndividual create_individual(){
        return this.factory.getOWLNamedIndividual(IRI.create(this.ontology_iri+ "#x_" + ++this.node_index));
    }

    private boolean add_axiom_to_abox(OWLObjectPropertyExpression relation, OWLNamedIndividual x1, OWLNamedIndividual x2){
        return this.abox.add(factory.getOWLObjectPropertyAssertionAxiom(relation, x1, x2));
    }

    private OWLClassAssertionAxiom instantiate_axiom(OWLClassExpression axm, OWLNamedIndividual x){
        return this.factory.getOWLClassAssertionAxiom(axm, x);
    }

    public boolean tableau_algorithm(OWLNamedIndividual x, HashSet<OWLObject> L_x, int node_index){
        HashSet<OWLObject> disjointed;
        HashSet<OWLObject> owl_some_values_set;
        Stream<OWLObjectAllValuesFrom> owl_all_values_set;
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

        owl_some_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectSomeValuesFrom)).collect(Collectors.toCollection(HashSet::new));
        owl_all_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectAllValuesFrom)).map(e -> (OWLObjectAllValuesFrom)e);//.collect(Collectors.toCollection(HashSet::new));
        

        System.out.println("-----------------------------------");
        System.out.println("Applicazione regola esiste");
        System.out.println("-----------------------------------");
        for(OWLObject obj : owl_some_values_set){
            HashSet<OWLObject> added_axioms = new HashSet<>();
            OWLClassExpression filler = ((OWLObjectSomeValuesFrom)obj).getFiller();
            OWLObjectPropertyExpression property = ((OWLObjectSomeValuesFrom)obj).getProperty();
            boolean exists_rule_condition =
                this.abox.stream()                                                                                      // exists R.C
                    .filter(e -> e instanceof OWLObjectPropertyAssertionAxiom)                                          // Raccolgo tutte le relazioni
                    .map(e -> (OWLObjectPropertyAssertionAxiom)e)                                                       // Cast    
                    .filter(e -> e.getProperty().equals(property))                                                      // Filtro tutte le relazioni di tipo R    
                    .filter(e -> e.getSubject().equals(x))                                                              // Filtro tutte le relazioni R da x a qualche z
                    .filter(e -> !this.abox.contains(this.factory.getOWLClassAssertionAxiom(filler, e.getObject())))    // Filtro le relazioni tali che C(z)
                    .count() == 0;

            if(exists_rule_condition){
                HashSet<OWLObject> L_child = new HashSet<>();                                                           // L_child rappresenta L(x')
                OWLNamedIndividual child = create_individual();                                                         // Creo nuovo figlio child
                ///
                System.out.println("\n\nNuovo figlio: x_" + this.node_index + "\n\n");
                ///
                this.add_axiom_to_abox(filler, child);                                                                  // Si aggiunge C(child) all'ABox
                this.add_axiom_to_abox(property, x, child);                                                             // Si aggiunge R(x, child) all'ABox    
                L_child.add(filler);                                                                                    // L(x') = {C}
                
                owl_all_values_set                                                                                      // forall R.D
                    .filter(e -> e.getProperty().equals(property))                                                      // Filtra i per ogni con la stessa relazione R
                    .forEach(e -> {
                                    L_child.add(e.getFiller());
                                    if(this.add_axiom_to_abox(e.getFiller(), x)) 
                                        added_axioms.add(this.instantiate_axiom(e.getFiller(), x));
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

    public boolean tableau_algorithm_non_empty_tbox(OWLNamedIndividual x, HashSet<OWLObject> L_x, int node_index){
        HashSet<OWLObject> disjointed;
        HashSet<OWLObject> owl_some_values_set;
        Stream<OWLObjectAllValuesFrom> owl_all_values_set;
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

        owl_some_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectSomeValuesFrom)).collect(Collectors.toCollection(HashSet::new));
        owl_all_values_set = L_x.stream().filter(e -> (e instanceof OWLObjectAllValuesFrom)).map(e -> (OWLObjectAllValuesFrom)e);//.collect(Collectors.toCollection(HashSet::new));
        

        System.out.println("-----------------------------------");
        System.out.println("Applicazione regola esiste");
        System.out.println("-----------------------------------");
        for(OWLObject obj : owl_some_values_set){
            HashSet<OWLObject> added_axioms = new HashSet<>();
            OWLClassExpression filler = ((OWLObjectSomeValuesFrom)obj).getFiller();
            OWLObjectPropertyExpression property = ((OWLObjectSomeValuesFrom)obj).getProperty();
            boolean exists_rule_condition =
                this.abox.stream()                                                                                      // exists R.C
                    .filter(e -> e instanceof OWLObjectPropertyAssertionAxiom)                                          // Raccolgo tutte le relazioni
                    .map(e -> (OWLObjectPropertyAssertionAxiom)e)                                                       // Cast    
                    .filter(e -> e.getProperty().equals(property))                                                      // Filtro tutte le relazioni di tipo R    
                    .filter(e -> e.getSubject().equals(x))                                                              // Filtro tutte le relazioni R da x a qualche z
                    .filter(e -> !this.abox.contains(this.factory.getOWLClassAssertionAxiom(filler, e.getObject())))    // Filtro le relazioni tali che C(z)
                    .count() == 0;

            if(exists_rule_condition){
                HashSet<OWLObject> L_child = new HashSet<>();                                                           // L_child rappresenta L(x')
                OWLNamedIndividual child = create_individual();                                                         // Creo nuovo figlio child
                ///
                System.out.println("\n\nNuovo figlio: x_" + this.node_index + "\n\n");
                ///
                this.add_axiom_to_abox(filler, child);                                                                  // Si aggiunge C(child) all'ABox
                this.add_axiom_to_abox(property, x, child);                                                             // Si aggiunge R(x, child) all'ABox 
                this.add_axiom_to_abox(this.Ĉ, child);                                                                  // Si aggiunge Ĉ(child) all'ABox
                L_child.add(filler);                                                                                    
                L_child.add(this.Ĉ);                                                                                    // L(x') = {C, Ĉ}

                owl_all_values_set                                                                                      // forall R.D
                    .filter(e -> e.getProperty().equals(property))                                                      // Filtra i per ogni con la stessa relazione R
                    .forEach(e -> {
                                    L_child.add(e.getFiller());
                                    if(this.add_axiom_to_abox(e.getFiller(), x)) 
                                        added_axioms.add(this.instantiate_axiom(e.getFiller(), x));
                                  });
                if(L_x.containsAll(L_child))
                    clash_free = true;
                else
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

    public boolean check_consistency(){
        boolean clash_free;
        if(this.Ĉ == null)
            clash_free = this.tableau_algorithm(this.root, this.L_x, this.node_index);
        else
            clash_free = this.tableau_algorithm_non_empty_tbox(this.root, this.L_x, this.node_index);
        
        return clash_free;
    }
}