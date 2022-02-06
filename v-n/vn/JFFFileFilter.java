/* Copyright 2005 by Mordechai (Moti) Ben-Ari. See copyright.txt. */
package vn;
import java.io.File;
import javax.swing.filechooser.*;

/*
 * JFFFileFilter:
 *   A file filter for .jff files
*/
class JFFFileFilter extends FileFilter {

    public boolean accept(File f) {
        if (f.isDirectory())
            return true;
        else {
            String e = f.getName().toUpperCase();
            return e.endsWith(".JFF"); 
        }
    }

    public String getDescription() {
        return "JFLAP files";
    }
}
