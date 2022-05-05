package com.alcreasoning.visitors;

/**
    OWLObjectVisitor utilizzato per applicare la regola dell'AND nell'algoritmo del tableau
*/
public class AllVisitors {

    public static AndVisitor and_visitor = new AndVisitor();
    public static OrVisitor or_visitor = new OrVisitor();
    public static PrinterVisitor printer_visitor = new PrinterVisitor();
    public static PrinterVisitor printer_v_save_string = new PrinterVisitor(true);
    public static AtomicConceptVisitor atomic_visitor = new AtomicConceptVisitor();
    public static LazyUnfoldingVisitor lazy_unfolding_v = new LazyUnfoldingVisitor();
    public static OrAndPreprocessorVisitor or_and_preproc_v = new OrAndPreprocessorVisitor();
}