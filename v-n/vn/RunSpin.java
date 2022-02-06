// Copyright 2006 by Mordechai (Moti) Ben-Ari. See VN.java. */

package vn;
import java.io.*;
import javax.swing.JOptionPane;

/*
 * RunSpin
 *     Forks a process to run Spin
 */

class RunSpin {
    static private String[] spinProgram = new String[Config.STATEMENTS];
    static private OutputStreamWriter output;

    static void readPromelaProgram() {
        BufferedReader sourceReader;
        String s = "";
        if (Config.VERBOSE) 
        	VN.progress(Config.SPIN_READ);
        try {  
            sourceReader = new BufferedReader(
                new FileReader(VN.fileRoot + Config.PromelaExt));
            int l = 0;
            while (true) {
                s = sourceReader.readLine();
                if (s == null) break;
                spinProgram[l++] = s;
            }
        } catch (IOException e) { VN.fileError(Config.PromelaExt); }
    }
    
    static void out(String s) {
        try {
            output.write(s);
            output.flush();
        }
        catch (IOException e) { 
        	e.printStackTrace();
        	System.exit(1);
        }
    }

    static void runC() {
        if (Config.VERBOSE) 
        	VN.progress(Config.RUN_C);
        Process p;
        try {
        	File pf = new File(VN.fileRoot + Config.PromelaExt).getParentFile();
            ProcessBuilder pb = new ProcessBuilder(
            		Config.getStringProperty("C_COMMAND"),
            		"-DSAFETY", "-o", "pan", "pan.c");
            if (pf != null) pb.directory(pf.getCanonicalFile());
            p = pb.start();
            p.waitFor();
        }
        catch (InterruptedException e) {  }
        catch (IOException e) { VN.fileError(Config.PromelaExt); }
    }

    static boolean runPan(boolean allTrails) {
        Process p;
        boolean accepted = false;
        if (Config.VERBOSE) 
        	VN.progress(Config.RUN_PAN);
        try {
        	File pf = new File(VN.fileRoot + Config.PromelaExt).getParentFile();
        	String panCommand = Config.getStringProperty("PAN");
            if (pf != null) 
            	panCommand = pf.getCanonicalFile() + File.separator + panCommand;
            ProcessBuilder pb = 
            	(allTrails ? 
            	new ProcessBuilder(panCommand, "-E",  "-c0", "-e") :
            	new ProcessBuilder(panCommand, "-E",  "-c" + VN.pathNumber));
            if (pf != null) pb.directory(pf.getCanonicalFile());
            pb.redirectErrorStream(true);
            p = pb.start();
            InputStream istream = p.getInputStream();
            BufferedReader input =
                new BufferedReader(new InputStreamReader(istream));
            String s = "";
            do { 
            	s = input.readLine();
            	if (s == null) break;
            	else if (s.indexOf("assertion violated") != -1)
            		accepted = true;
            	else if (!allTrails && s.indexOf("errors:") != -1) 
            		if (Integer.parseInt(
            			s.substring(s.indexOf("errors:")+7).trim()) < VN.pathNumber)
            			accepted = false;  // No more accepting computations
            } while (true);
            p.waitFor();
            if (!allTrails && !accepted) 
            	VN.pathArea.append(Config.NO_ACCEPT + (VN.pathNumber-1));
        }
        catch (InterruptedException e) {  }
        catch (IOException e) { VN.fileError(Config.PromelaExt); }
        return accepted;
    }
    
    static void runSpin(VN.SpinMode spinMode) {
    	boolean allTrails = spinMode == VN.SpinMode.ALL_TRAILS;
    	if (allTrails) spinMode = VN.SpinMode.TRAIL;
        String inputString = "";
        readPromelaProgram();
        VN.pathArea.setText("");
        PrintWriter pathWriter = null;
        if (spinMode != VN.SpinMode.VERIFY)
	        try {
	            pathWriter = new PrintWriter(
	                new FileWriter(VN.fileRoot + Config.pathExt)); 
	        } catch (IOException e) { VN.fileError(Config.pathExt); }
        
        if (Config.VERBOSE) 
        	VN.progress(Config.RUN_SPIN + ": " + spinMode);
        Process p;
        ProcessBuilder pb = null;
        try {
            // Use ProcessBuilder to run Spin, redirecting ErrorStream
            if (spinMode == VN.SpinMode.RANDOM)
            	pb = new ProcessBuilder(
            		Config.getStringProperty("SPIN_COMMAND"), 
            		"-B", "-T", 
                    VN.fileName + Config.PromelaExt);
            else if (spinMode == VN.SpinMode.INTERACTIVE)
            	pb = new ProcessBuilder(
            		Config.getStringProperty("SPIN_COMMAND"), 
            		"-B", "-T", "-i", "-X", 
                    VN.fileName + Config.PromelaExt);
            else if (spinMode == VN.SpinMode.VERIFY)
            	pb = new ProcessBuilder(Config.getStringProperty("SPIN_COMMAND"),
            		"-a", 
                    VN.fileName + Config.PromelaExt);
            else if (spinMode == VN.SpinMode.TRAIL)
            	pb = new ProcessBuilder(Config.getStringProperty("SPIN_COMMAND"),
            		"-B", "-T", "-t" + (allTrails ? VN.pathNumber: ""),
                    VN.fileName + Config.PromelaExt);
            File pf = new File(VN.fileRoot + Config.PromelaExt).getParentFile();
            if (pf != null) pb.directory(pf.getCanonicalFile());
            pb.redirectErrorStream(true);
            p = pb.start();
            // Connect to I/O streams
            InputStream istream = p.getInputStream();
            BufferedReader input =
                new BufferedReader(new InputStreamReader(istream));
            OutputStream ostream = p.getOutputStream();
            output = new OutputStreamWriter(ostream);
            // Process Spin output line by line
            boolean isState = true;
            String lastState = "";
            String[] choices = new String[Config.CHOICES];
            int numChoices = 0;
            String s = "";
            inputString = "";
            while (true) {
                s = input.readLine();
//                System.out.println(s);
                if (s == null) 
                    break;
                else if (s.startsWith("**")) {
                    s = s.substring(2);
                    pathWriter.println(s);
                    if (s.startsWith(Config.RESULT_ACCEPT) || 
                        s.startsWith(Config.RESULT_REJECT)) {
                        VN.pathArea.append(" : " + s);
                    }
                    else if (isState) {
                        VN.pathArea.append(s);
                        lastState = new String(s);
                    }
                    else {
                        VN.pathArea.append(" -" + s + "-> ");
                        if ((spinMode == VN.SpinMode.TRAIL) && !s.equals("L")) 
                        	inputString = inputString + s;
                    }
                    isState = !isState;
                }
                else if ((spinMode != VN.SpinMode.INTERACTIVE)) {
                }
                else if (s.indexOf("(FA)") != -1) {
                    choices[numChoices++] = s;
                }
                else if (s.startsWith("Make Selection")) {
                	// Weirdness of Spin: double set of choices
                	int unexecutable = 0;
                	for (int j = 0; j < numChoices; j++)
                		if (choices[j].indexOf("unexecutable") != -1)
                			unexecutable++;
                	if ((numChoices > 0) && (unexecutable == numChoices)) {
						VN.pathArea.append(" : " + Config.RESULT_REJECT);
                        out("q\n");
                        break;
                	}
                    if (numChoices <= 1) out("1\n");
                    else {
                        pathWriter.flush();
                        VN.showGraph();
                        int choice = 
                        	selectChoice(choices, numChoices, lastState);
                        if (choice == numChoices+1) {
							VN.pathArea.append(" : " + Config.QUIT);
                            out("q\n");
                            break;
                        }
                        else out(choice + "\n");
                    }
                    s = input.readLine();
                    numChoices = 0;
                }
            }
            // Wait for Spin process to end
            p.waitFor();
        }
        catch (InterruptedException e) {  }
        catch (IOException e) { VN.fileError(Config.PromelaExt); }
        if (spinMode != VN.SpinMode.VERIFY)
        	pathWriter.close();
        if (spinMode == VN.SpinMode.TRAIL) 
        	if (!VN.inputs.contains(inputString)) 
        		VN.inputs.add(inputString);
    }
    
    static void printTokens(String[] tokens) {
    	for (int j = 0; j < tokens.length; j++) 
    		System.out.print("#"+tokens[j]);
    	System.out.println("#");
    }
    
    static int selectChoice(String[] choices, int numChoices, String lastState) {
        String[] selections = new String[numChoices+1];
        for (int i = 0; i < numChoices; i++) {
            String[] tokens = choices[i].split("\\s");
            // Weirdness of Spin: extra token for single digit numbers
            int lineIndex = 9;
            if (tokens[lineIndex].equals("")) lineIndex++;
            String source = spinProgram[java.lang.Integer.parseInt(tokens[lineIndex])+i];
            tokens = source.split("\\s");
            char letter = ' ';
            if (tokens[2].equals("true")) letter = 'L';
            else if (tokens[2].equals("i[h]")) letter = tokens[4].charAt(1);
            int last = tokens.length-1;
            String target = tokens[last].substring(0,tokens[last].length());
            if (letter == '.') selections[i] = Config.ACCEPT;
            else selections[i] = "-" + letter + "->" + target;
            if (choices[i].indexOf("unexecutable") != -1)
                selections[i] = '[' + selections[i] + ']';
        }
        choices[numChoices] = Config.QUIT;
        selections[numChoices] = Config.QUIT;
        int n;
        String message = Config.SELECT + lastState;
        do {
            n = JOptionPane.showOptionDialog(
                VN.messageArea, message, null, 
                JOptionPane.DEFAULT_OPTION, JOptionPane.PLAIN_MESSAGE, null,
                selections, selections[0]);
            if (n == JOptionPane.CLOSED_OPTION) return numChoices + 1;
            message = Config.NOT_ENABLED + Config.SELECT + lastState;
        } while (choices[n].indexOf("unexecutable") != -1);
        return n+1;
    }
}
