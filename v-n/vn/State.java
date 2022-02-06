// Copyright 2006 by Mordechai (Moti) Ben-Ari. See VN.java. */
package vn;

/*
 * State:
 *   A state consists of its name (which must be a numeral)
 *   and indications if it is initial or final
 */

class State implements Comparable<State>{
    String name;
    boolean initial;
    boolean finalState;

    public State(String n, boolean i, boolean f) {
        name = n; initial = i; finalState = f;
    }
    
    public String toString() {
        return name +
        	(initial ? " initial " : "") +
        	(finalState ? " final ": "");
    }
    
    // States are equal if their names are equal
    public boolean equals(Object o) {
    	return name.equals(((State) o).name);
    }

    // Convert name string to number
    public static int toInt(State s) {
        try { return Integer.parseInt(s.name); }
        catch (NumberFormatException e) { return 0; }
    }
    
    // For sorting, compare states by comparing their numerical values
    public int compareTo(State s) {
    	int i1, i2;
    	try { 
            i1 = Integer.parseInt(name); 
            i2 = Integer.parseInt(s.name);
        } 
    	catch (NumberFormatException e) { i1 = 0; i2 = 0;}
    	return (i1 < i2 ? -1 : (i2 < i1 ? 1 : 0));
    }
}
