// Copyright 2006 by Mordechai (Moti) Ben-Ari. See VN.java. */
package vn;
import java.io.*;

class ReadPath {
	
	static void readPath(boolean duplicates) {
	    State st;   
	    Transition tr;
        int delta = Config.DELTA;
        String previousState = null;
        String currentState = null;
        String nextState = null; 
        String currentLetter = null;
        String previousLetter = null;
        BufferedReader stateReader = null;
        boolean finalState = false;
        boolean stop = false;

        VN.pathStates.clear();
        VN.pathTransitions.clear();

        try {  // Everything in try block for IOException
        	if (Config.VERBOSE) 
        		VN.progress(Config.READ_PATH);
            stateReader = new BufferedReader(
                new FileReader(VN.fileRoot + Config.pathExt));
          	currentState = stateReader.readLine();
          	if (currentState != null) currentState = currentState.trim();

        while (true) {
        	if ((currentState == null) || stop ||
                (!currentState.startsWith("q"))) break;
            currentState = currentState.substring(1);
            boolean initial = previousState == null;
          	currentLetter = stateReader.readLine();
          	if (currentLetter != null) currentLetter = currentLetter.trim();
            if ((currentLetter == null) || 
            	(currentLetter.startsWith(Config.RESULT_REJECT)))
                stop = true;
            else if (currentLetter.startsWith(Config.RESULT_ACCEPT)) {
          		finalState = true;
                stop = true;
            }
          	else { 
          		nextState = stateReader.readLine();
          		if (nextState == null)
          			stop = true;
          		else nextState = nextState.trim();
          	}
            st = new State(currentState, initial, finalState);
            // Disambiguate repeated visits to states
            if (duplicates && 
            	(VN.pathStates.indexOf(st) != -1)) {
            	int i = 0;
            	try { i = Integer.parseInt(currentState); } 
            	catch (NumberFormatException e) {}
            	currentState = "" + (i + delta);
            	delta = delta + Config.DELTA;
            	st = new State(currentState, initial, finalState);
            }
            VN.pathStates.add(st);

            if (!initial) {
                tr = new Transition(previousState, currentState, 
                    previousLetter.charAt(0));
                if (duplicates || 
                	(VN.pathTransitions.indexOf(tr) == -1))
                    VN.pathTransitions.add(tr);
            }
            previousState = currentState;
            currentState = nextState;
            previousLetter = currentLetter;
        }
        
        stateReader.close(); 
        } catch (IOException e) { VN.fileError(Config.pathExt); }
	}
}
