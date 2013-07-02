-- Copyright 2008 by Mordechai (Moti) Ben-Ari. GNU GPL.
package States.Arguments is
  File_Name:       access String;
  Argument_Error:  exception;

  procedure Get_Arguments;
end States.Arguments;
