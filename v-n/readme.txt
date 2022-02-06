
            VN - Visualization of Nondeterminism
          
          Copyright 2007 by Mordechai (Moti) Ben-Ari
	           under the GNU Public License
              See copyright.txt and gpl.txt
           
            http://stwww.weizmann.ac.il/g-cs/benari/

For a given input string, a nondeterministic finite automata (NDFA)
can have more than one execution sequence. Sources of nondeterminism
include multiple transitions for the same letter from a state,
as well as lambda-transitions. VN nondeterministically executes a
finite automaton and displays the path in the graph for the automaton. 

A description of the automaton is created using the JFLAP package 
(http://jflap.org/).

VN uses Spin (http://spinroot.com/) to run a nondeterministic program
and dot (http://www.graphviz.org/) to create graphics files.

0. Make sure that a JRE for Java 5 is installed.

1. Make sure that an ANSI C compiler is installed.
For windows, you use the gcc compiler from mingw or cygwin.
A self-extracting archive mingw.exe is supplied;
extract it into the directory c:\mingw.

2a. Run the Windows installer vn.exe.

or

2b. Unzip the archive into a clean directory such as c:\vn.

3. Run the jar file: javaw -jar vn.jar. The batch file run.bat contains
this command. The name of a JFLAP file (without the jff extension) can 
be given as a command line parameter. See the Help screen for
instructions on using VN.

4. To build, compile all Java programs and create the jar file.
The batch file build.bat is provided. Labels, messages, sizes,
commands, font and so on are in Config.java for easy modification.

5. The installation file and the archive vn-bin.zip 
includes the files needed to run Spin, JFLAP and dot in the
directory bin, but you can install these packages, 
configuration file and rebuild.
