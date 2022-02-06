// Copyright 2006 by Mordechai (Moti) Ben-Ari. See VN.java. */
package vn;

/*
 * Transition:
 *   A transitions consists of the names of the states it connects
 *   and the letter that takes the transition.
 *   The letter 'L' is used for lambda on epsilon transitions. 
 */

class Transition implements Comparable<Transition> {
    String from;
    String to;
    char   letter;

    public Transition(String f, String t, char l) {
    	from = f; to = t; letter = l;
    	if ((letter != 'L') && !VN.symbols.contains(letter)) 
    		VN.symbols.add(letter);
    }

    public String toString() {
        return from + " -- " + letter + " --> " + to;
    }

    // Transitions are equal if all components are equal
    public boolean equals(Object o) {
        Transition tr = (Transition) o;
        return
            (from.equals(tr.from)) && 
            (to.equals(tr.to)) &&
            (letter == tr.letter);
    }

    // For sorting, compare the source state and letter of the transitions 
    public int compareTo(Transition t) {
    	int i1, i2;
    	try { 
            i1 = Integer.parseInt(from); 
            i2 = Integer.parseInt(t.from);
        } 
    	catch (NumberFormatException e) { i1 = 0; i2 = 0;}
      int result = (i1 < i2 ? -1 : (i2 < i1 ? 1 : 0));
      if (result != 0) return result;
      result = (letter < t.letter ? -1 : (t.letter < letter ? 1 : 0));
      if (result != 0) return result;
    	try { 
            i1 = Integer.parseInt(to); 
            i2 = Integer.parseInt(t.to);
        } 
    	catch (NumberFormatException e) { i1 = 0; i2 = 0;}
    	return (i1 < i2 ? -1 : (i2 < i1 ? 1 : 0));
    }
}
