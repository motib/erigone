// Copyright 2008 by Mordechai (Moti) Ben-Ari. See VN.java. */
package vn;
import java.io.*;
/*
 * GenerateSpinInteractive
 *     Generates an interactive Promela program for the NDFA
 */
class GenerateSpinInteractive {
	static private PrintWriter programWriter;

	static void emit(String s) { programWriter.println(s); }
	
	static void writePromela(boolean choose) {
		if (Config.VERBOSE)
			VN.progress(Config.SPIN_WRITE + VN.fileName + 
                  Config.interactiveModifier + Config.PromelaExt);
        try {
            programWriter = new PrintWriter(
            		new FileWriter(
                  VN.fileRoot + Config.interactiveModifier + Config.PromelaExt));
        } catch (IOException e) { VN.fileError(Config.PromelaExt); }
        
        Object[] stateObject = VN.states.toArray();
        java.util.Arrays.sort(stateObject);
        Object[] transitionObject = VN.transitions.toArray();
        java.util.Arrays.sort(transitionObject);
        
        int initial = 0;
        for (int i = 0; i < stateObject.length; i++) {
			if ( ((State) stateObject[i]).initial ) 
				{ initial = i; break; }
		}
        
        emit("byte i;");
        emit("byte q = 0;");
        emit("chan STDIN;");
        emit("bool accepted = false;");

        emit("inline Get(q, accepting) {");
        emit("\tprintf(\"At state q%d, next " + 
          (choose ? "transition" : "symbol") + ": \", q);");
        emit("\tSTDIN ? i;");
        emit("\tSTDIN ? _;   /* end of line */");
        emit("\tif");
        emit("\t:: i == '-' && accepting ->");
        emit("\t\taccepted = true; break");
        emit("\t:: i == '-' && !accepting ->");
        emit("\t\tbreak");
        emit("\t:: else");
        emit("\tfi");
        emit("}");

        emit("active proctype FA() {");
        emit("\tdo");

        int t = 0;   // Index of transitions
        int tNum;      // Transition number for chooseing NDFA
        for (Object sObject : stateObject) {
        	State st = (State) sObject;
        	emit("\t:: q == " + st.name + "->");
        	emit("\t\tGet(" + st.name + (st.finalState ? ", true" : ", false") + ");"); 
          emit("\t\tif");
          tNum = 1;

        	while (true) {
        		if (t == transitionObject.length) break;
        		Transition tr = (Transition) transitionObject[t];
        		if (tr.from.equals(st.name)) {
              if (choose)
                emit("\t\t:: i == '" + (tNum++) + "' -> q = " + tr.to);
              else if(tr.letter == 'L') 
                emit("\t\t:: true -> q = " + tr.to);
              else
           		  emit("\t\t:: i == '" + tr.letter + "' -> q = " + tr.to);
              t++;
        		}
        		else break;
        	}
      		emit("\t\t:: else -> break");
        	emit("\tfi;");
        }
        emit("\tod;");
        
        emit("\tif");
        emit("\t:: accepted -> printf(\"Accepted!\\n\");");
        emit("\t:: !accepted -> printf(\"Rejected!\\n\");");
        emit("\tfi");
        emit("}");
        programWriter.close();
	}
}
