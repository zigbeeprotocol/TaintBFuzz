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

/* Currently Cytoscape.use emits an error when a library is already loaded.
This prevents Hot Module Reloading for modules where Cytescope.use is used.
Grouping all Cytoscape plugins registrations here solves the problem. */

import Cytoscape from 'cytoscape';

import CxtMenu from 'cytoscape-cxtmenu';
import Popper from 'cytoscape-popper';
import Panzoom from 'cytoscape-panzoom';

// Layouts
import Dagre from 'cytoscape-dagre';
import Cola from 'cytoscape-cola';
import CoseBilkent from 'cytoscape-cose-bilkent';
import Klay from 'cytoscape-klay';

Cytoscape.use(Popper);
Cytoscape.use(CxtMenu);
Panzoom(Cytoscape); // register extension

Cytoscape.use(Dagre);
Cytoscape.use(Cola);
Cytoscape.use(CoseBilkent);
Cytoscape.use(Klay);
