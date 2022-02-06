// Copyright 2006 by Mordechai (Moti) Ben-Ari. See VN.java. */

package vn;

import java.io.*;
import java.util.ArrayList;

class WriteGraph {
	static String color(Object o, String which) {
        String bw = "";
        if (which.equals("path")) 
            return Config.HIGHLIGHT_TYPE[Config.getIntProperty("HIGHLIGHT")];
        else if (which.equals("fa-path")) {
        	if ((o == null) ||
        	    ((o instanceof State) && 
        	     (VN.pathStates.indexOf((State) o) != -1)) ||
    		    ((o instanceof Transition) && 
    		     (VN.pathTransitions.indexOf((Transition) o) != -1)) )
    				return Config.HIGHLIGHT_TYPE[Config.getIntProperty("HIGHLIGHT")];
        }
        return bw;
	}
	
    // Write the graph - nodes and edges
    static void writeGraph(String which,
    		ArrayList<State> states,
    		ArrayList<Transition> transitions) {

        String ext = Config.dotExt;
    	PrintWriter graphWriter = null;
    	if (Config.VERBOSE)
    		VN.progress(Config.GRAPH_WRITE + VN.fileName + '-' + which + ext);

        try {
            graphWriter = new PrintWriter(
                new FileWriter(VN.fileRoot + '-' + which + ext));
        } catch (IOException e) { VN.fileError(ext); }
        graphWriter.println(
		    "digraph " + "\"" + VN.fileName + '-' + which + "\"" + " {\n" +
		    "\tgraph [ranksep=.2];\n" +
		    "\tnode [shape=circle,fontname=Helvetica,fontsize=" + 
		    Config.GRAPH_FONT[Config.getIntProperty("GRAPH_SIZE")] + 
		    "];\n" +
		    "\tnode [width=" + 
		    Config.GRAPH_WIDTH[Config.getIntProperty("GRAPH_SIZE")] + 
		    ",fixedsize=true];\n" +
        	"\tedge [fontname=Helvetica,fontsize=" + 
		    Config.GRAPH_FONT[Config.getIntProperty("GRAPH_SIZE")] + 
        	"];\n");
        if (which.equals("path")) graphWriter.println("{\nrank=same;");
        graphWriter.println("-1 [width=0.2,shape=point" + color(null, which) + "];");

        boolean even = true;  // Ranks for "path"
        for (State st : states) {
        	if (st.initial) 
                graphWriter.println("-1 -> " + st.name + " [" + color(null, which) + "];");
            int sti = State.toInt(st);
            if (sti >= Config.DELTA) sti = sti % Config.DELTA;
            graphWriter.println(
                 st.name + " [" +
                 "label=q" + sti + 
                 (st.finalState ? " peripheries=2" : "") + 
                 color(st, which) + "];");
            if (which.equals("path")) {
	            if (even) graphWriter.println("}\n{\nrank=same;");
	            even = !even;
            }
        }
        if (which.equals("path")) graphWriter.println("}");
        else graphWriter.println();
        for (Transition t : transitions) {
            graphWriter.println(
                t.from + 
                " -> " + 
                t.to + " [" +
                "label=\" " + t.letter + "\" " +
                color(t, which) + "];");
        }
        graphWriter.println("}");
        graphWriter.close();
        runDot(which);
    }

    static void runDot(String which) {
        if (Config.VERBOSE) 
        	VN.progress(Config.RUN_DOT + " to create " + VN.fileName + '-' + which + Config.graphExt);
        Process p;
        try {
            // Use ProcessBuilder to run dot
            String[] sa = {Config.getStringProperty("DOT_COMMAND"), 
            		"-T" + Config.graphExt.substring(1),
            		"-o" + VN.fileRoot + '-' + which + Config.graphExt,
            		VN.fileRoot + '-' + which + Config.dotExt
            		};
            ProcessBuilder pb = new ProcessBuilder(sa);
            File pf = new File(VN.fileRoot + which + Config.dotExt).getParentFile();
            if (pf != null) pb.directory(pf.getCanonicalFile());
            pb.redirectErrorStream(true);
            p = pb.start();
            InputStream istream = p.getInputStream();
            BufferedReader input =
                new BufferedReader(new InputStreamReader(istream));
            String s;
            while (true) {
                s = input.readLine();
                if (s == null) break;
            }
            p.waitFor();
        }
        catch (InterruptedException e) {  }
        catch (IOException e) { }
    }
}
