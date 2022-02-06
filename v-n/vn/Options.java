// Copyright 2006 by Mordechai (Moti) Ben-Ari. See VN.java. */
package vn;
import javax.swing.*;
import java.awt.event.*;

class Options extends JFrame  implements ActionListener, ItemListener {
    private JRadioButton small;
    private JRadioButton medium;
    private JRadioButton large;
    private ButtonGroup  sizeGroup;

    private JRadioButton color;
    private JRadioButton bold;
    private ButtonGroup  highlightGroup = new ButtonGroup();

    private JRadioButton none;
    private JRadioButton promela;
    private JRadioButton javaprogram;
    private JRadioButton jeliot;
    private ButtonGroup  interactiveGroup = new ButtonGroup();

    private JCheckBox    chooseBox;

    private JButton ok          = new JButton(Config.OK);
    private JButton cancel      = new JButton(Config.CANCEL);
    
    private int size;  // 0 = small, 1 = medium, 2 = large
    private int high;  // 0 = color, 1 = bold
    private int interactive; // 0 = none, 1 = promela, 2 = java, 3 = jeliot
    private boolean choose;

    public void actionPerformed(ActionEvent e) {
    	if (e.getSource() == ok) {
    		Config.setIntProperty("GRAPH_SIZE",  size);
    		Config.setIntProperty("HIGHLIGHT",   high);
    		Config.setIntProperty("INTERACTIVE", interactive);
    		Config.setBooleanProperty("CHOOSE",  choose);
        if (VN.file != null)
    		  Config.setStringProperty("SOURCE_DIRECTORY", 
    			  VN.file.getParentFile().toString());
    		Config.saveFile();
    	    dispose();
    	} else if (e.getSource() == cancel)
    		dispose();
		else if (e.getSource() == small)  size = 0;
		else if (e.getSource() == medium) size = 1;
		else if (e.getSource() == large)  size = 2;
		else if (e.getSource() == color)  high = 0;
		else if (e.getSource() == bold)   high = 1;
		else if (e.getSource() == none)        interactive = 0;
		else if (e.getSource() == promela)     interactive = 1;
		else if (e.getSource() == javaprogram) interactive = 2;
		else if (e.getSource() == jeliot)      interactive = 3;
    }
    
    public void itemStateChanged(ItemEvent e) {
      if (e.getItemSelectable() == chooseBox)
        choose = e.getStateChange() == ItemEvent.SELECTED;
    }

    void setItem(AbstractButton item, ButtonGroup b, JPanel p, int mn) {
    	item.setMnemonic(mn);
        item.addActionListener(this);
        if (b != null) b.add(item);
        p.add(item);
    }
    
    Options() {
    	size = Config.getIntProperty("GRAPH_SIZE");
    	high = Config.getIntProperty("HIGHLIGHT");
      interactive = Config.getIntProperty("INTERACTIVE");
      choose = Config.getBooleanProperty("CHOOSE");
    	
      small  = new JRadioButton(Config.SMALL,  size == 0);
      medium = new JRadioButton(Config.MEDIUM, size == 1);
      large  = new JRadioButton(Config.LARGE,  size == 2);
      sizeGroup = new ButtonGroup();
        
      color  = new JRadioButton(Config.COLOR,  high == 0);
      bold   = new JRadioButton(Config.BOLD,   high == 1);
      highlightGroup = new ButtonGroup();
        
      none        = new JRadioButton(Config.NONE,    interactive == 0); 
      promela     = new JRadioButton(Config.PROMELA, interactive == 1);
      javaprogram = new JRadioButton(Config.JAVA,    interactive == 2);
      jeliot      = new JRadioButton(Config.JELIOT,  interactive == 3);
      interactiveGroup = new ButtonGroup();

      chooseBox   = new JCheckBox(Config.CHOOSE, choose);

      JPanel sizePanel = new JPanel();
      sizePanel.setLayout(new java.awt.GridLayout(1,4));
      sizePanel.setBorder(BorderFactory.createLineBorder(java.awt.Color.blue));
      sizePanel.add(new JLabel("  " + Config.SIZE));
      setItem(small, sizeGroup, sizePanel, Config.SMALLMN);
      setItem(medium, sizeGroup, sizePanel, Config.MEDIUMMN);
      setItem(large, sizeGroup, sizePanel, Config.LARGEMN);

      JPanel highlightPanel = new JPanel();
      highlightPanel.setLayout(new java.awt.GridLayout(1,4));
      highlightPanel.setBorder(BorderFactory.createLineBorder(java.awt.Color.blue));
      highlightPanel.add(new JLabel("  " + Config.HIGHLIGHT));
      setItem(color, highlightGroup, highlightPanel, Config.COLORMN);
      setItem(bold, highlightGroup, highlightPanel, Config.BOLDMN);
      highlightPanel.add(new JLabel());

      JPanel interactivePanel = new JPanel();
      interactivePanel.setLayout(new java.awt.GridLayout(1,5));
      interactivePanel.setBorder(BorderFactory.createLineBorder(java.awt.Color.blue));
      interactivePanel.add(new JLabel("  " + Config.INTERACTIVE));
      setItem(none, interactiveGroup, interactivePanel, Config.NONEMN);
      setItem(promela, interactiveGroup, interactivePanel, Config.PROMELAMN);
      setItem(javaprogram, interactiveGroup, interactivePanel, Config.JAVAMN);
      setItem(jeliot, interactiveGroup, interactivePanel, Config.JELIOTMN);

      JPanel choosePanel = new JPanel();
//      choosePanel.setLayout(new java.awt.GridLayout(1,1));
      choosePanel.setBorder(BorderFactory.createLineBorder(java.awt.Color.blue));
      chooseBox.setMnemonic(Config.CHOOSEMN);
      chooseBox.addItemListener(this);
      choosePanel.add(chooseBox, "CENTER");
      
      JPanel buttonPanel = new JPanel();
      buttonPanel.setLayout(new java.awt.GridLayout(1,2));
      buttonPanel.setBorder(BorderFactory.createLineBorder(java.awt.Color.blue));
      setItem(ok, null, buttonPanel, Config.OKMN);
      setItem(cancel, null, buttonPanel, Config.CANCELMN);
        
      getContentPane().setLayout(new java.awt.GridLayout(5,1));
      getContentPane().add(sizePanel);
      getContentPane().add(highlightPanel);
      getContentPane().add(interactivePanel);
      getContentPane().add(choosePanel);
      getContentPane().add(buttonPanel);

      setDefaultCloseOperation(javax.swing.WindowConstants.DISPOSE_ON_CLOSE);
      setFont(new java.awt.Font(Config.FONT_FAMILY, Config.FONT_STYLE, Config.FONT_SIZE));
      setTitle(Config.OPTIONS);
      setSize(400, 250);
      setLocationRelativeTo(null); 
      setVisible(true);
    }
}
