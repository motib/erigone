--
--               The Erigone Model Checker
--       Copyright 2008-12 by Mordechai (Moti) Ben-Ari.
--
-- This program is free software; you can redistribute it and/or
-- modify it under the terms of the GNU General Public License
-- as published by the Free Software Foundation; either version 2
-- of the License, or (at your option) any later version.
-- This program is distributed in the hope that it will be useful
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
-- See the GNU General Public License for more details.
-- You should have received a copy of the GNU General Public License
-- along with this program; if not, write to the Free Software
-- Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
-- 02111-1307, USA.
--
-- Version number and copyright notice
--
package Version is
  Number:    constant String := "3.2.5";
  Year:      constant String := "2008-12";
  Copyright: constant String :=
    "Erigone v"        & Number &
    ", Copyright "     & Year   &
    " by Moti Ben-Ari, GNU GPL.";
end Version;
