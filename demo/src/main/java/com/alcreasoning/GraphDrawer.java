package com.alcreasoning;

import static guru.nidi.graphviz.model.Factory.*;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashSet;

import org.semanticweb.owlapi.model.OWLObject;

import guru.nidi.graphviz.attribute.Label;
import guru.nidi.graphviz.attribute.Label.Justification;
import guru.nidi.graphviz.engine.Format;
import guru.nidi.graphviz.engine.Graphviz;
import guru.nidi.graphviz.model.MutableGraph;
import guru.nidi.graphviz.model.MutableNode;


public class GraphDrawer {
    private int graphviz_node_id = 0;       // Questo id serve solo per dare un id diverso ai nodi graphviz
    private FunnyVisitor return_visitor;
    MutableGraph graph;

    public GraphDrawer(String graph_name){
        this.graph = mutGraph(graph_name).setDirected(true);
        this.return_visitor = new FunnyVisitor(true);
    }

    private String write_L_x_to_file(HashSet<OWLObject> L_x, String individual_name){
        String L_x_string = this.return_set_as_string(L_x, "L_" + individual_name);
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
            System.out.println("Sono qui");
            L_x_file.createNewFile();
            FileWriter writer = new FileWriter(L_x_file);
            writer.write(L_x_string);
            writer.close();
        }
        catch(IOException e){
            System.out.println("Errore");
            e.printStackTrace();
        } 

        return folder+filename;
    }

    private MutableNode create_new_node(HashSet<OWLObject> L_x, String individual_name){
        //String L_x_string = this.return_set_as_string(L_x, "L_"+individual_name);
        String file_path = this.write_L_x_to_file(L_x, individual_name);
        //String html = "<a href=\"file:///" + System.getProperty("user.dir") + "\\" + file_path + "\">L_" + individual_name + "</a>";
        String html = "href=\"file:///" + System.getProperty("user.dir") + "\\" + file_path + "\"";
        System.out.println(html);
        MutableNode child_node = mutNode("" + this.graphviz_node_id++).add(Label.of(individual_name)).add(Label.html(html).external());
        return child_node;
    }

    private MutableNode add_link_to_node(MutableNode parent, MutableNode child, String relation){
        return parent.addLink(to(child).with(Label.of(relation)));
    }

    public MutableNode add_new_child(MutableNode node, String relation, HashSet<OWLObject> L_x, String individual_name){
        MutableNode child_node = this.create_new_node(L_x, individual_name);
        this.graph.add(this.add_link_to_node(node, child_node, relation));
        return child_node;
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

    public void save_graph(String save_path){
        try{
            Graphviz.fromGraph(this.graph).render(Format.SVG).toFile(new File(save_path));
        }
        catch(IOException ex){
            System.out.println("Errore");
        }
    }
}
