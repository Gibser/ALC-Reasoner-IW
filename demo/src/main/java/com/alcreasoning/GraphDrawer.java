package com.alcreasoning;

import static guru.nidi.graphviz.model.Factory.*;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import org.semanticweb.owlapi.model.OWLObject;

import guru.nidi.graphviz.attribute.Color;
import guru.nidi.graphviz.attribute.Label;
import guru.nidi.graphviz.attribute.Shape;
import guru.nidi.graphviz.attribute.Style;
import guru.nidi.graphviz.attribute.Label.Justification;
import guru.nidi.graphviz.engine.Format;
import guru.nidi.graphviz.engine.Graphviz;
import guru.nidi.graphviz.model.Graph;
import guru.nidi.graphviz.model.MutableGraph;
import guru.nidi.graphviz.model.MutableNode;
import guru.nidi.graphviz.model.Node;


public class GraphDrawer {
    private int graphviz_node_id = 0;       // Questo id serve solo per dare un id diverso ai nodi graphviz
    private FunnyVisitor return_visitor;
    Graph graph;
    List<Node> node_list;

    public GraphDrawer(String graph_name){
        //this.graph = graph(graph_name).directed();
        this.return_visitor = new FunnyVisitor(true);
        this.node_list = new ArrayList<>();
    }

    private String write_L_x_to_file(HashSet<OWLObject> L_x, String individual_name){
        String L_x_string = this.return_set_as_string(L_x, "L_" + individual_name);
        //TODO: Creare cartella se non esiste
        String folder = "labels\\";
        String filename = "" + this.graphviz_node_id;
        int duplicate_index = 1;
        Path path = Paths.get(folder + filename);
        
        while(Files.exists(path)){
            filename = "" + this.graphviz_node_id + "_" + duplicate_index++;
            path = Paths.get(folder + filename);
        }
        System.out.println(filename);
        File L_x_file = new File(folder, filename);

        try{
            //System.out.println("Sono qui");
            //L_x_file.createNewFile();
            try (BufferedWriter wr = Files.newBufferedWriter(path, StandardCharsets.UTF_8)) {
                wr.write(L_x_string);
            }
            //FileWriter writer = new FileWriter(L_x_file);
            //writer.write(L_x_string);
            //writer.close();
        }
        catch(IOException e){
            System.out.println("Errore");
            e.printStackTrace();
        } 

        return folder+filename;
    }

    public Node create_new_node(HashSet<OWLObject> L_x, String individual_name){
        //String L_x_string = this.return_set_as_string(L_x, "L_"+individual_name);
        System.out.println("Nodo: " + this.graphviz_node_id);
        String file_path = this.write_L_x_to_file(L_x, individual_name);
        //String html = "<table border='0'><tr><td><a href=\"file:///" + System.getProperty("user.dir") + "\\" + file_path + "\">L_" + individual_name + "</a></td></tr></table>";
        //String html = "<a href=\"file:///" + System.getProperty("user.dir") + "\\" + file_path + "\">L_" + individual_name + "</a>";
        String html = "<table cellspacing='0' cellpadding='2' border='1'><tr><td href=\"file:///" + System.getProperty("user.dir") + "\\" + file_path + "\">L<sub>" + individual_name + "</sub></td></tr></table>";
        System.out.println(html);
        Node child_node = node("" + this.graphviz_node_id++).with(Label.of(individual_name)).with(Label.html(html).external());
        return child_node;
    }
    
    public Node add_L_x_to_node(Node node, HashSet<OWLObject> L_x, String individual_name){
        String file_path = this.write_L_x_to_file(L_x, individual_name);
        String[] name_split = individual_name.split("_");
        String html = "<table cellspacing='0' cellpadding='4' border='1'><tr><td href=\"file:///" + System.getProperty("user.dir") + "\\" + file_path + "\">L<sub>" + name_split[0] + "<sub>" + name_split[1] + "</sub></sub></td></tr></table>";
        return node.with(Label.html(html).external());
    }

    public Node create_new_node(String individual_name){
        String[] name_split = individual_name.split("_");
        Node child_node = node("" + this.graphviz_node_id++).with(Label.html(name_split[0] + "<sub>" + name_split[1] + "</sub>"));
        return child_node;
    }

    private Node create_child_clash_free_node(){
        return node("" + this.graphviz_node_id++).with(Label.of("\u2B24"), Shape.NONE, Color.rgb("00cc00").font());
    }    

    public void add_child_clash_free_node(Node child){
        Node clash_free_node = this.create_child_clash_free_node();
        this.node_list.add(this.add_link_to_node(child, clash_free_node));
    }

    private Node create_clash_free_node(){
        return node("" + this.graphviz_node_id++).with(Label.of("\u2713"), Shape.NONE, Color.rgb("00cc00").font());
    }

    public void add_clash_free_node(Node parent){
        Node clash_free_node = this.create_clash_free_node();
        this.node_list.add(this.add_link_to_node(parent, clash_free_node));
    }
    
    private Node create_clash_node(){
        return node("" + this.graphviz_node_id++).with(Label.of("\u2716"), Shape.NONE, Color.rgb("cc3300").font());
    }

    public void add_clash_node(Node parent){
        Node clash_node = this.create_clash_node();
        this.node_list.add(this.add_link_to_node(parent, clash_node));
    }
    
    private Node add_link_to_node(Node parent, Node child, String relation){
        return parent.link(to(child).with(Label.of(relation)));
    }

    private Node add_link_to_node(Node parent, Node child){
        return parent.link(to(child));
    }

    public Node add_new_child(Node node, String relation, String individual_name){
        Node child_node = this.create_new_node(individual_name);
        //this.graph.add(this.add_link_to_node(node, child_node, relation));
        this.node_list.add(this.add_link_to_node(node, child_node, relation));
        return child_node;
    }

    public Node add_new_child(Node parent_node, Node child_node, String relation){
        //this.graph.add(this.add_link_to_node(node, child_node, relation));
        this.node_list.add(this.add_link_to_node(parent_node, child_node, relation));
        return child_node;
    }

    public void add_new_child(Node child){
        this.node_list.add(child);
    }

    public String return_set_as_string(HashSet<OWLObject> L_x, String set_name){
        String ret_string = set_name + " = {";
        int i = 0;
        for(OWLObject obj : L_x){
            obj.accept(this.return_visitor);
            ret_string += this.return_visitor.get_and_destroy_return_string();
            if(i++ < L_x.size()-1) ret_string += ", "; else ret_string += "}";
        }

        return ret_string;
    }

    public void save_graph(String save_path){
        this.graph = graph("Tableau").directed().with(this.node_list);
        int duplicate_index = 1;
        String filename = "graph.svg";
        Path path = Paths.get(save_path + "\\" + filename);
        try{
            while(Files.exists(path)){
                filename = "graph" + "_" + duplicate_index++ + ".svg";
                path = Paths.get(filename);
            }
            Graphviz.fromGraph(this.graph).width(500).render(Format.SVG).toFile(new File(save_path + "\\" + filename));
        }
        catch(IOException ex){
            System.out.println("Errore");
        }
    }
}
