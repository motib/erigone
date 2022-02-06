// Copyright 2006 by Mordechai (Moti) Ben-Ari. See VN.java. */
package vn;
import java.awt.event.KeyEvent;
import java.io.*;
import java.util.Properties;

/*
 * Config - configuration:
 *   Directorie and file names and extensions
 *   Fonts, colors and sizes
 *   Button names and mnemonics
 *   Texts for messages and errors
 */

class Config {
    static final String 	VERSION = " V2.3.1";
    static final String 	TITLE = 
        "VN - Visualization of Nondeterminism" + VERSION;

	static private Properties properties = new Properties();
	static private final String FILE_NAME = "config.cfg";

	// Verbose output in progress pane
	static final boolean    VERBOSE = false;
	
	private static void setDefaultProperties() {
		properties.put("SOURCE_DIRECTORY",	"examples");
    properties.put("HELP_FILE_NAME",	"txt\\help.txt");
	  properties.put("ABOUT_FILE_NAME",	"txt\\copyright.txt");
	  properties.put("SPIN_COMMAND", 		"bin\\spin.exe");
	  properties.put("DOT_COMMAND",		"bin\\dot.exe");
	  properties.put("C_COMMAND",         "c:\\mingw\\bin\\gcc.exe"); 
		properties.put("DUMMY_JFF_FILE",	"examples\\dummy.jff");
		properties.put("PAN", 				"pan.exe");
		properties.put("HIGHLIGHT", 		Integer.toString(0));  // Color
		properties.put("GRAPH_SIZE", 		Integer.toString(2));  // Large
    properties.put("INTERACTIVE",   Integer.toString(0)); // None
    properties.put("CHOOSE",        Boolean.toString(false)); // None
	}

    static final String 	jflapExt = ".jff";
    static final String 	dotExt   = ".dot";
    static final String 	graphExt = ".png";
    static final String 	pathExt  = ".pth";
    static final String 	PromelaExt = ".pml";
    static final String 	JavaExt  = ".java";
    static final String   interactiveModifier = "Interactive";

    static final int 		STATES = 100;
    static final int 		TRANSITIONS = 200;
    static final int    STATEMENTS = 250;
    static final int    CHOICES = 10;
	  static final int 		DELTA = 100;  // Dummy node name offset

    static final int 		WIDTH = 1000;
    static final int 		HEIGHT = 720;
    static final int    LEFT_WIDTH = 500;
    static final int    TB_DIVIDER = 530;
    static final int    BUTTON_WIDTH = 70;
    static final int    BUTTON_HEIGHT = 40;
    static final int    TEXT_WIDTH = 150;
    static final int    COLUMNS = 100;
    static final int		PATH_HEIGHT = 42;

    static final String FONT_FAMILY = "Lucida Sans Typewriter";
    static final int 		FONT_STYLE = java.awt.Font.PLAIN;
    static final int 		FONT_SIZE = 14;
    
    static final String INPUT    = "String or length: ";
    static final String OPEN     = "Open";
    static final int 		OPENMN   = KeyEvent.VK_O;
    static final String EDIT     = "Edit";
    static final int 		EDITMN   = KeyEvent.VK_E;
    static final String RANDOM   = "Random";
    static final int 		RANDOMMN = KeyEvent.VK_R;
    static final String CREATE   = "Create";
    static final int    CREATEMN = KeyEvent.VK_C;
    static final String FIND     = "Find";
    static final int    FINDMN   = KeyEvent.VK_F;
    static final String NEXT     = "Next";
    static final int    NEXTMN   = KeyEvent.VK_N;
    static final String GENERATE = "Generate";
    static final int 		GENMN    = KeyEvent.VK_G;
    static final String DFA      = "DFA";
    static final int 		DFAMN    = KeyEvent.VK_D;
    static final String HELP     = "Help";
    static final int 		HELPMN   = KeyEvent.VK_H;
    static final String ABOUT    = "About";
    static final int 		ABOUTMN  = KeyEvent.VK_A;
    static final String EXIT     = "Exit";
    static final int 		EXITMN   = KeyEvent.VK_X;

    static final int[]    GRAPH_FONT  = { 9, 12, 14 };
    static final float[]  GRAPH_WIDTH = { 0.2f, 0.3f, 0.4f };
    static final String[] HIGHLIGHT_TYPE = { " color=red", " style=bold" };

    static final String OPTIONS  = "Options";
    static final int 		OPTIONSMN= KeyEvent.VK_P;
    static final String OK       = "OK";
    static final int 		OKMN     = KeyEvent.VK_O;
    static final String CANCEL   = "Cancel";
    static final int 		CANCELMN = KeyEvent.VK_A;
	  static final String	SIZE	 = "Size";
	  static final String SMALL 	 = "Small";
    static final int 		SMALLMN  = KeyEvent.VK_S;
    static final String MEDIUM	 = "Medium";
    static final int 		MEDIUMMN = KeyEvent.VK_M;
    static final String LARGE	 = "Large";
    static final int 		LARGEMN  = KeyEvent.VK_L;
    static final String	HIGHLIGHT = "Highlight";
    static final String COLOR	 = "Color";
    static final int 		COLORMN  = KeyEvent.VK_C;
    static final String	BOLD	 = "Bold";
    static final int 		BOLDMN   = KeyEvent.VK_B;
    static final String INTERACTIVE = "Interactive";
    static final String NONE = "None";
    static final int 		NONEMN   = KeyEvent.VK_N;
    static final String PROMELA = "Promela";
    static final int 		PROMELAMN   = KeyEvent.VK_R;
    static final String JAVA    = "Java";
    static final int 		JAVAMN   = KeyEvent.VK_J;
    static final String JELIOT  = "Jeliot";
    static final int 		JELIOTMN   = KeyEvent.VK_T;
    static final String CHOOSE  = "Choose NDFA";
    static final int 		CHOOSEMN   = KeyEvent.VK_H;
    
    static final String		ENTER_NUMBER = "Enter a positive integer and select Generate";
    static final String   FILE_ERROR   = "File error ";
    static final String		NO_INPUT     = "Enter a nonempty string or positive integer and select Generate";
    static final String		NO_JFF_FILE  = "Open a \"jff\" file with the automaton";
    static final String		NO_MULTIPLE  = "Enter a nonempty string and select Generate";
    
    static final String		DEBUG_WRITE  = "Writing debug file";
    static final String		GRAPH_WRITE  = "Writing graph ";
    static final String	  READ_PATH    = "Reading path file";
    static final String   READING      = "Reading ";
    static final String		RUN_C        = "Running C compiler";
    static final String		RUN_DOT      = "Running dot";
    static final String		RUN_PAN      = "Running pan";
    static final String		RUN_SPIN     = "Running Spin";
    static final String		SPIN_WRITE   = "Generating program ";
    static final String   SPIN_READ    = "Reading Promela program ";
    
    static final String   ACCEPT       = "Accept";
    static final String		ACCEPTS_ON	 = ", inputs: ";
    static final String		FINAL_STATE  = "Inputs accepted by final state q";
    static final String		GENERATED    = "Program generated";
    static final String   NO_ACCEPT    = "Number of accepting computations: ";
    static final String   NOT_ENABLED  = "Transition not enabled\n";
    static final String   QUIT         = "Quit";
    static final String   RESULT_ACCEPT= "Accepted!";
    static final String   RESULT_REJECT= "Rejected ...";
    static final String 	SELECT  	   = "Select a transition leaving ";
    static final int      SELECT_BUTTON= 120; 
    static final int      SELECT_HEIGHT= 70;

	// Initialize configuration file
    static void init() {
        setDefaultProperties();
        FileInputStream in = null;
        try {
            in = new FileInputStream(FILE_NAME);
        } catch (FileNotFoundException e1) {
            System.out.println(
				"Cannot open VN file, creating new file");
            try {
                saveFile();
                in = new FileInputStream(FILE_NAME);
            } catch (IOException e2) {
                System.err.println("Cannot write VN file");
            }
        }
        try {
            properties.load(in);
            in.close();
        } catch (IOException e3) {
            System.err.println("Cannot read VN file");
        }
    }

	// Save configuration file
    static void saveFile() {
        try {
            FileOutputStream out = new FileOutputStream(FILE_NAME);
            properties.store(out, "VN configuration file");
            out.close();
            System.out.println("Saved VN file " + FILE_NAME);
        } catch (IOException e2) {
            System.err.println("Cannot write VN file");
        }
    }

	// Interface to get/set propertyies of various types
    static String getStringProperty(String s) {
        return properties.getProperty(s);
    }

    static void setStringProperty(String s, String newValue) {
        properties.setProperty(s, newValue);
    }

    static boolean getBooleanProperty(String s) {
        return Boolean.valueOf(properties.getProperty(s)).booleanValue();
    }

    static void setBooleanProperty(String s, boolean newValue) {
        properties.setProperty(s, Boolean.toString(newValue));
    }

    static int getIntProperty(String s) {
        return Integer.valueOf(properties.getProperty(s)).intValue();
    }

    static void setIntProperty(String s, int newValue) {
        properties.setProperty(s, Integer.toString(newValue));
    }
}
