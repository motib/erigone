-- Copyright 2008-11 by  Mordechai (Moti) Ben-Ari. See version.ads
with Ada.Command_Line, Ada.Strings.Fixed, Ada.Text_IO;
with Files, Utilities, Version;
with Options; use Options;
package body Arguments is
  -- Internal exception raised by Error, handled by Get_Arguments
  Command_Line_Error: exception;

  -- Display usage
  procedure Usage is
    use Ada.Text_IO;

    -- Sizes are in thousands, display without 000
    function To_String(N: Positive) return String is
    begin
      return " (" & Utilities.Trim(Integer'Image(N/1000)) & ")";
    end To_String;

  begin -- Usage
    Put_Line(Version.Copyright);
    New_Line;
    Put_Line(
      "Usage: erigone [arguments] filename (default extension .pml)");
    New_Line;
    Put_Line("  -X  execution mode, X is one of:");
    Put_Line("   a     acceptance verification");
    Put_Line("   c     compilation only");
    Put_Line("   f     fairness verification");
    Put_Line("   g     guided simulation");
    Put_Line("   gN    guided simulation with trail N");
    Put_Line("   i     interactive simulation");
    Put_Line("   r     random simulation (default)");
    Put_Line("   s     safety verification");
    New_Line;
    Put_Line("  -d  display everything");
    Put_Line("  -dX display X, where X is a string of:");
    Put_Line("    a    all transitions");
    Put_Line("    b    buchi automata");
    Put_Line("    c    chosen transitions");
    Put_Line("    e    executable transitions");
    Put_Line("    g    pro[g]ress notification");
    Put_Line("    h    hash table");
    Put_Line("    l    location stack");
    Put_Line("    m    si[m]ulation states");
    Put_Line("    n    nodes of LTL tableau");
    Put_Line("    o    channel c[o]ntents");
    Put_Line("    p    program symbols and transitions");
    Put_Line("    r    runtime statistics");
    Put_Line("    s    state stack");
    Put_Line("    t    trail");
    Put_Line("    v    version and copyright message");
    Put_Line("    y    b[y]te code");
    New_Line;
    Put_Line("  -lXN   limits in thousands except hash, (defaults):");
    Put_Line("    h    hash slots     "  & To_String(Hash_Slots*1000) &
                                           " 2**N slots, 16<=N<=32");
    Put_Line("    l    location stack "  & To_String(Location_Stack_Max));
    Put_Line("    p    progress steps "  & To_String(Progress_Steps));
    Put_Line("    s    state stack    "  & To_String(State_Stack_Max));
    Put_Line("    t    total steps    "  & To_String(Total_Steps));
    New_Line;
    Put_Line("  -e     do not stop on end state");
    Put_Line("  -h     help screen");
    Put_Line("  -mN    stop after N'th error; 0=report all errors");
    Put_Line("  -nN    random seed");
    Put_Line("  -t     temporal logic formula (use default)");
    Put_Line("  -t-[n] named internal temporal logic formula");
    Put_Line("  -t[n]  named temporal logic formula in file");
    Put_Line("  -u     debug all");
    Put_Line("  -uX    debug options, where X is a string of:");
    Put_Line("           [i]nterpreter, [p]arser, p[r]eprocessor");
  end Usage;

  -- If argument error, display usage
  --   S is the unrecognized argument
  procedure Error(S: in String) is
  begin
    Ada.Text_IO.Put_Line("*** Invalid argument: " & S & " ***");
    Ada.Text_IO.New_Line;
    raise Command_Line_Error;
  end Error;

  -- Set flags for -d display argument
  procedure Set_Display(C: in Character) is
    D: Display_Type;
  begin
    case C is
      when 'a' => D := All_T;
      when 'b' => D := LTL;
      when 'c' => D := Chosen;
      when 'e' => D := Executable;
      when 'g' => D := Progress;
      when 'h' => D := Hash;
      when 'l' => D := Location_Stack;
      when 'm' => D := Simulation_States;
      when 'n' => D := Nodes;
      when 'o' => D := Channels;
      when 'p' => D := Program;
      when 'r' => D := Run;
      when 's' => D := State_Stack;
      when 't' => D := Trail;
      when 'v' => D := Options.Version;
      when 'y' => D := Byte_Codes;
      when others => Error("-d" & C);
    end case;
    Display(D) := True;
  end Set_Display;

  -- Set option from argument -S
  procedure Set_Option(S: in String) is
    I:   Positive := S'First+1;  -- Argument is after hyphen
    Len: Positive := S'Length;

    -- Sizes must be multiplied by 1_000
    function Get_Thousands return Positive is
    begin
      return Positive'Value(S(I+2..S'Last)) * 1_000;
    end Get_Thousands;

  begin
    case S(I) is
      when 'a' => Execution_Mode  := Acceptance;
      -- when 'b' =>
      when 'c' => Execution_Mode  := Compile_Only;
      when 'd' =>
        if Len = 2 then   -- Set all flags true if "-d"
          Display := (others => True);
        else -- For each character set the relevant flag
          for J in S'First+2..S'Last loop
            Set_Display(S(J));
          end loop;
        end if;
      when 'e' => No_Stop_On_End_State := True;
      when 'f' => Execution_Mode  := Fairness;
      when 'g' => Simulation_Mode := Guided;
                  if Len > 2 then
                    Trail_Number := Natural'Value(S(I+1..S'Last));
                  end if;
      when 'h' => Usage;
                  raise Command_Line_Error;
      when 'i' => Simulation_Mode := Interactive;
      -- when 'j' =>
      -- when 'k' =>
      when 'l' => -- Set limits -lXN
        case S(I+1) is
          when 'h' => Hash_Slots := Positive'Value(S(I+2..S'Last));
          when 'l' => Location_Stack_Max := Get_Thousands;
          when 'p' => Progress_Steps     := Get_Thousands;
          when 's' => State_Stack_Max    := Get_Thousands;
          when 't' => Total_Steps        := Get_Thousands;
          when others => Error(S);
        end case;
      when 'm' => Error_Number    := Natural'Value(S(I+1..S'Last));
      when 'n' => Seed            := Natural'Value(S(I+1..S'Last));
      -- when 'o' =>
      -- when 'p' =>
      -- when 'q' =>
      when 'r' => Simulation_Mode := Random;
      when 's' => Execution_Mode  := Safety;
      when 't' => if Len = 2 then
                    LTL_Mode := Default_LTL;
                  elsif S(S'First+2) = '-' then
                    LTL_Mode := Internal;
                    Files.LTL_File_Name :=
                        new String'(S(S'First+3..S'Last));
                  else
                    LTL_Mode := File;
                    Files.LTL_File_Name :=
                        new String'(S(S'First+2..S'Last));
                  end if;
      when 'u' =>
        if Len = 2 then   -- Set all flags true if "-u"
          Debug := (others => True);
        else -- For each character set the relevant flag
          for J in S'First+2..S'Last loop
            if    S(J) = 'p' then Debug(Debug_Parser)      := True;
            elsif S(J) = 'i' then Debug(Debug_Interpreter) := True;
            elsif S(J) = 'r' then Debug(Debug_Preprocessor) := True;
            end if;
          end loop;
        end if;
      -- when 'v' =>
      -- when 'w' =>
      -- when 'x' =>
      -- when 'y' =>
      -- when 'z' =>
      when others => Error(S);
    end case;
    exception
      -- Size parameter may not be numeric
      when Constraint_Error => Error(S);
  end Set_Option;

  -- Set the file names from the source file name
  procedure Set_File_Names is
    use Ada.Command_Line;
    Index: Natural;
  begin
    -- Check whether the file name has an extension
    Index := Ada.Strings.Fixed.Index(
               Argument(Argument_Count), ".", Ada.Strings.Backward);
    if  Index = 0 then
      -- If not, use the default
      Files.Root_File_Name   :=
        new String'(Argument(Argument_Count));
      Files.Source_File_Name :=
        new String'(Files.Root_File_Name.all & Files.Source_Extension);
    else
      -- If so, compute the root for other files
      Files.Root_File_Name   := 
        new String'(Argument(Argument_Count)(1..Index-1));
      Files.Source_File_Name :=
        new String'(Argument(Argument_Count));
    end if;

    -- Add extensions to get other file names
    Files.LTL_File_Name      :=
          new String'(Files.Root_File_Name.all & Files.LTL_Extension);
    Files.Trail_File_Name    :=
          new String'(Files.Root_File_Name.all & Files.Trail_Extension);
    Files.Automata_File_Name :=
          new String'(Files.Root_File_Name.all & Files.Automata_Extension);
    Files.DOT_File_Name :=
          new String'(Files.Root_File_Name.all & Files.DOT_Extension);
  end Set_File_Names;

  -- Put message concerning an argument
  procedure Message(S: in String) is
    use Ada.Command_Line, Ada.Text_IO;
  begin
    New_Line; Put_Line("*** " & S & " ***"); New_Line;
  end Message;

  -- Get and set arguments
  function Get_Arguments return Boolean is
    use Ada.Command_Line, Ada.Text_IO;
  begin
    if Argument_Count < 1 then         -- No arguments
      Usage;
      raise Command_Line_Error;
    elsif Argument_Count = 1 then      -- One argument must be:
      if Argument(1) = "-dv" then      --   -dv
        Put_Line(Version.Copyright);
        return False;
      elsif Argument(1) = "-h" then    --   or -h
        Usage;
        raise Command_Line_Error;
      elsif Argument(1)(1) = '-' then  --   or file name
        Message("Missing file name");
        return False;
      end if;
    end if;

    Set_File_Names;

    -- Process each argument
    for Count in 1 .. Argument_Count-1 loop
      if Argument(Count)(1) /= '-' then
        Error(Argument(Count));
      else
        Set_Option(Argument(Count));
      end if;
    end loop;

    if LTL_Mode = None and then
        (Execution_Mode = Acceptance or Execution_Mode = Fairness) then
      Error("-t required for this mode");
    end if;

    -- Optionally display the version and the options
    if Display(Options.Version) then 
      Put_Line(Version.Copyright);
    end if;

    if Display(Run) then
      Put_Options;
    end if;
    return True;
  exception
    when Command_Line_Error => return False;
  end Get_Arguments;
end Arguments;
