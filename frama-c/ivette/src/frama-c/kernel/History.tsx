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

/* --------------------------------------------------------------------------*/
/* --- Frama-C Selection History                                          ---*/
/* --------------------------------------------------------------------------*/

import React from 'react';
import * as Toolbar from 'dome/frame/toolbars';
import * as States from 'frama-c/states';

export default function History(): JSX.Element {
  const [selection, updateSelection] = States.useSelection();

  const doPrevSelect = () => void updateSelection('HISTORY_PREV');
  const doNextSelect = () => void updateSelection('HISTORY_NEXT');

  return (
    <Toolbar.ButtonGroup>
      <Toolbar.Button
        icon="ANGLE.LEFT"
        onClick={doPrevSelect}
        disabled={!selection || selection.history.prevSelections.length === 0}
        title="Previous location"
      />
      <Toolbar.Button
        icon="ANGLE.RIGHT"
        onClick={doNextSelect}
        disabled={!selection || selection.history.nextSelections.length === 0}
        title="Next location"
      />
    </Toolbar.ButtonGroup>
  );
}

/* --------------------------------------------------------------------------*/
