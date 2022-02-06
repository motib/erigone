// Copyright 2006 by Mordechai (Moti) Ben-Ari. See VN.java. */
package vn;
import java.io.*;
/*
 * GenerateSpin
 *     Generates a Promela program for the NDFA
 */
class GenerateSpin {
	static private PrintWriter programWriter;

	static void emit(String s) { programWriter.println(s); }
	
	static void writePromela(String input, int inputLength) {
		if (Config.VERBOSE)
			VN.progress(Config.SPIN_WRITE + VN.fileName + Config.PromelaExt);
        try {
            programWriter = new PrintWriter(
            		new FileWriter(VN.fileRoot + Config.PromelaExt));
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
        
        emit("byte i[" + (inputLength+1) + "];");
        emit("byte h;");
        emit("int x;  /* Dummy variable for Find Next */");
        
        emit("inline Accept() {");
        emit("\t_ = x;");
        emit("\tprintf(\"**" + Config.RESULT_ACCEPT + "\\n\");");
        emit("\tassert(false);");
        emit("\tgoto halt");
        emit("}");

        emit("proctype FA() {");
        emit("    goto q" + initial + ";");

        int t = 0;   // Index of transitions
        int x = 0;   // Value of dummy variable
        for (Object sObject : stateObject) {
        	State st = (State) sObject;
        	emit("q" + st.name + ":");
        	emit("\tprintf(\"**q" + st.name + "\\n\");"); 
            emit("\tif"); 
        	while (true) {
        		if (t == transitionObject.length) break;
        		Transition tr = (Transition) transitionObject[t];
        		if (tr.from.equals(st.name)) {
                	if(tr.letter == 'L') 
                		emit("\t:: true -> " + "x=x+" + (x++) +
                			 "; printf(\"**L\\n\"); goto q" + 
                             tr.to);
                	else 
                		emit("\t:: i[h] == '" + 
                             tr.letter + 
                    		 "' -> " + "x=x+" + (x++) + 
                    		 "; printf(\"**%c\\n\", i[h]); h++; goto q" + 
                             tr.to);
                	t++;
        		}
        		else break;
        	}
        	if (st.finalState) 
        		emit("\t:: i[h] == '.' -> " + "x=x+" + (x++) + "; Accept()");
        	emit("\tfi;");
        }
        emit("halt: skip");
        emit("}");
        emit("active proctype watchdog() {");
        emit("\ttimeout -> printf(\"**" + Config.RESULT_REJECT + "\\n\")");
        emit("}");
        		
       	emit("init {");
        emit("\tatomic {");
        if (VN.multiple)
        	for (int i = 0; i < inputLength; i++) {
        		String ifString = "\tif ";
        		for (char c : VN.symbols)
        			ifString = ifString + " :: i["+i+"] = '" + c + "'";
        		ifString = ifString + " fi;";
        		emit(ifString);
        }
        else
        	for (int i = 0; i < inputLength; i++)
        		emit("\ti["+i+"] = '" + input.charAt(i) + "';");
        emit("\ti[" + inputLength + "] = '.';"); // Dummy
		emit("\trun FA();");
        emit("\t}");
        emit("}");
        programWriter.close();
	}
}
