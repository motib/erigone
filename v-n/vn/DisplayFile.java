/* Copyright 2005 by Mordechai (Moti) Ben-Ari. See copyright.txt. */
// Class DisplayFile for Help, About, Display raw
package vn;
import javax.swing.*;
import java.awt.event.*;
import java.io.*;

/*
 * DisplayFile:
 *   For "About" and "Help", reads a text file and displays
 *   the contents in the JFrame with scrollbars.
 *   Dispose of the frame if the window is closed or Escape is pressed.  
 */

class DisplayFile extends JFrame implements ActionListener {
	
    DisplayFile(java.awt.Font font, JTextArea message, 
            String file, String title) {
        String s = readFile(new java.io.File(file));
        JTextArea area = new JTextArea();
        area.setFont(font);
        area.setText(s);
        area.setCaretPosition(0);
        area.setEditable(false);
        getContentPane().add(new JScrollPane(area));
        setDefaultCloseOperation(
            javax.swing.WindowConstants.DISPOSE_ON_CLOSE);
        getRootPane().registerKeyboardAction(this,
                KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0),
                JComponent.WHEN_IN_FOCUSED_WINDOW);
        setTitle(Config.TITLE + " - " + title);
        setSize(2*Config.WIDTH/3, 2*Config.HEIGHT/3);
        setLocationRelativeTo(null); 
        setVisible(true);
    }
    
	public void actionPerformed(ActionEvent e) {
		dispose();
	}

    String readFile(File fc) {
        BufferedReader textReader = null;
        try {
        	textReader = new BufferedReader(new FileReader(fc));
        	StringWriter textWriter = new StringWriter();
        	int c = 0;
            while (true) {
                c = textReader.read();
                if (c == -1) break;
                else textWriter.write(c);
            }
            textReader.close();
            return textWriter.toString();
        }
        catch (IOException e) { return Config.FILE_ERROR + fc; }
    }
}
