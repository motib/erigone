// Copyright 2006 by Mordechai (Moti) Ben-Ari. See VN.java. */
package vn;
import java.io.*;
import org.xml.sax.*;
import org.xml.sax.helpers.DefaultHandler;
import javax.xml.parsers.SAXParserFactory;
//import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;

/*
 * ReadXML:
 *   Read the XML of the .jff file.
 *   Adapted from an example in the Java tutorial
 *   which is based upon callbacks.
 */

public class ReadXML extends DefaultHandler {
	
	// Variables for storing data between callbacks
	State state = null;
    Transition transition = null;
    boolean initial = false;
    boolean finalState = false;
	String stateName = "";
    String from = "";
    String to = "";
	char letter = ' ';
	String current = null;
	
    public void startDocument() throws SAXException {}
    public void endDocument() throws SAXException {}

    public void startElement(
    	String nURI, String l, String qName, Attributes attrs) 
    		throws SAXException {
    	if (qName.equals("state")) {
    		if (state != null) {		// If state already read
    			VN.states.add(state);	//   add it to data structure
    			state = null;
    		}
	        stateName = attrs.getValue(0);
    	}
    	else if (qName.equals("initial"))
    		initial = true;
    	else if (qName.equals("final"))
    		finalState = true;
    	else if (qName.equals("transition")) {
    		if (state != null) { 		// Add the last state
    			VN.states.add(state);
    			state = null; 
    		}
    	}
    	else if (qName.equals("from") || 
                 qName.equals("to") || 
    			 qName.equals("read")) {
    		current = qName;			// Remember component of transition
    	}
    }

    // For transitions, get data between start and end element
    // Replace epsilon transitions by 'L'
    public void characters(char buf[], int offset, int len)
    		throws SAXException {
    	if (current == null) return;
    	if (current.equals("from"))
    		from = new String(buf, offset, len);
    	else if (current.equals("to")) 
    		to = new String(buf, offset, len);
    	else if (current.equals("read"))
    		letter = (offset == 0 ? 'L' : buf[offset]);
    	current = null;
    }

    public void endElement(
    	String nURI, String s, String qName) 
    		throws SAXException {
    	if (qName.equals("state")) {
    		state = new State(stateName, initial, finalState);
    		initial = false; finalState = false;
    	}
    	else if (qName.equals("transition")) {
    		transition = new Transition(from, to, letter);
    		VN.transitions.add(transition);
    	}
    }

	public void readXML(File file) {
		// Clear state and transition data structures before reading file
		VN.states.clear();
		VN.transitions.clear();
        DefaultHandler handler = this;
        SAXParserFactory factory = SAXParserFactory.newInstance();
        try {
            SAXParser saxParser = factory.newSAXParser();
            saxParser.parse(file, handler);
        } catch (Throwable t) { t.printStackTrace(); }
        // for (State s : VN.states) System.out.println(s);
        // for (Transition t : VN.transitions) System.out.println(t);
    }
}
