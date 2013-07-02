-- Copyright 2008-9 by  Mordechai (Moti) Ben-Ari. See version.ads
--
--  Instantiation of Ada.Text_IO.Modular_IO for Byte
--
with Ada.Text_IO;
with Global;
package Byte_IO is new Ada.Text_IO.Modular_IO(Global.Byte);
