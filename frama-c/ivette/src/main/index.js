/* ************************************************************************ */
/*                                                                          */
/*   This file is part of Frama-C.                                          */
/*                                                                          */
/*   Copyright (C) 2007-2022                                                */
/*     CEA (Commissariat à l'énergie atomique et aux énergies               */
/*          alternatives)                                                   */
/*                                                                          */
/*   you can redistribute it and/or modify it under the terms of the GNU    */
/*   Lesser General Public License as published by the Free Software        */
/*   Foundation, version 2.1.                                               */
/*                                                                          */
/*   It is distributed in the hope that it will be useful,                  */
/*   but WITHOUT ANY WARRANTY; without even the implied warranty of         */
/*   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the          */
/*   GNU Lesser General Public License for more details.                    */
/*                                                                          */
/*   See the GNU Lesser General Public License version 2.1                  */
/*   for more details (enclosed in the file licenses/LGPLv2.1).             */
/*                                                                          */
/* ************************************************************************ */

// --------------------------------------------------------------------------
// --- Electron main-process entry-point for Dome.
// --------------------------------------------------------------------------

/*
   Template of ./src/main/index.js
   Imported from $(DOME)/template/main.js

   The call to Dome.start() will initialize the Dome application
   and create the main window that will run the renderer process
   from `src/renderer/index.js`.

   You may add your own code to be run in the Electron main-process
   before or after the call to `Dome.start()`.
*/

import * as Dome from 'dome' ;
Dome.setName('Ivette');
Dome.start();
