// Copyright 2008 by Mordechai (Moti) Ben-Ari. See VN.java. */
package vn;
import java.io.*;
/*
 * GenerateJavaInteractive
 *     Generates an interactive Java program for the NDFA
 */
class GenerateJavaInteractive {
	static private PrintWriter programWriter;

	static void emit(String s) { programWriter.println(s); }
	
  static final String blanks = "          ";

	static void writeJava(boolean choose, boolean jeliot) {
		if (Config.VERBOSE)
			VN.progress(Config.SPIN_WRITE + VN.fileName + 
                  Config.interactiveModifier + Config.JavaExt);
        try {
            programWriter = new PrintWriter(
            		new FileWriter(
                  VN.fileRoot + Config.interactiveModifier + Config.JavaExt));
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
        
    emit("class " + VN.fileName + "Interactive {");
    if (!jeliot) 
      emit("  static java.util.Scanner scanner = new java.util.Scanner(System.in);");
    emit("  public static void main(" + (jeliot ? "" : "String[] args") + ") {");
    emit("    char i;");
    emit("    byte q = 0;");    
    emit("    boolean accepted = false;");
    emit("    loop:");
    emit("    while (true) {");
    if (jeliot) {
      emit("      Output.print(\"At state q\" + q + \", next " + 
           (choose ? "transition" : "symbol") + ":  \");");
      emit("      i = Input.readChar();");
    }
    else {
      emit("      System.out.print(\"At state q\" + q + \", next " +
           (choose ? "transition" : "symbol") + ":  \");");
      emit("      i = scanner.next().charAt(0);");
    }
    emit("      switch (q) { ");

    int t = 0;   // Index of transitions
    int tNum;      // Transition number for chooseing NDFA
    for (Object sObject : stateObject) {
      State st = (State) sObject;
      emit("        case " + st.name + ":");
      emit(blanks + "if (i == '-') { " + 
           (st.finalState ? "accepted = true; " : "") + "break loop; } ");
      tNum = 1;
      
      while (true) {
        if (t == transitionObject.length) break;
        Transition tr = (Transition) transitionObject[t];
        if (tr.from.equals(st.name)) {
          if (choose)
            emit(blanks + "else if (i == '" + (tNum++) + "') q = " + tr.to + ";");
          else if (tr.letter == 'L')
            emit(blanks + "else if (true) q = " + tr.to + ";");
          else
            emit(blanks + "else if (i == '" + tr.letter + "') q = " + tr.to + ";");
          t++;
        }
        else break;
      }
      emit(blanks + "else break loop;");
      emit(blanks + "break;");
    }
    emit("      }");
    emit("    }");
    
    emit("    if (accepted) System.out.println(\"Accepted!\\n\");");
    emit("    else System.out.println(\"Rejected!\\n\");");
    emit("  }");
    emit("}");
    programWriter.close();
	}
}
