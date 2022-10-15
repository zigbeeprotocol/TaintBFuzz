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
// --- Frama-C Globals
// --------------------------------------------------------------------------

import React from 'react';
import * as Dome from 'dome';
import { classes } from 'dome/misc/utils';
import { alpha } from 'dome/data/compare';
import { Section, Item } from 'dome/frame/sidebars';
import { Button } from 'dome/controls/buttons';
import * as Toolbars from 'dome/frame/toolbars';

import * as States from 'frama-c/states';
import { functions, functionsData } from 'frama-c/kernel/api/ast';
import { computationState } from 'frama-c/plugins/eva/api/general';

// --------------------------------------------------------------------------
// --- Global Search Hints
// --------------------------------------------------------------------------

function makeFunctionHint(fct: functionsData): Toolbars.Hint {
  return {
    id: fct.key,
    label: fct.name,
    title: fct.signature,
    value: () => States.setSelection({ fct: fct.name }),
  };
}

async function lookupGlobals(pattern: string): Promise<Toolbars.Hint[]> {
  const lookup = pattern.toLowerCase();
  const fcts = States.getSyncArray(functions).getArray();
  return fcts.filter((fn) => (
    0 <= fn.name.toLowerCase().indexOf(lookup)
  )).map(makeFunctionHint);
}

Toolbars.registerSearchHints('frama-c.globals', lookupGlobals);

// --------------------------------------------------------------------------
// --- Function Item
// --------------------------------------------------------------------------

interface FctItemProps {
  fct: functionsData;
  current: string | undefined;
  onSelection: (name: string) => void;
}

function FctItem(props: FctItemProps): JSX.Element {
  const { name, signature, main, stdlib, builtin, defined } = props.fct;
  const className = classes(
    main && 'globals-main',
    (stdlib || builtin) && 'globals-stdlib',
  );
  const attributes = classes(
    main && '(main)',
    !stdlib && !builtin && !defined && '(ext)',
  );
  return (
    <Item
      className={className}
      label={name}
      title={signature}
      selected={name === props.current}
      onSelection={() => props.onSelection(name)}
    >
      {attributes && <span className="globals-attr">{attributes}</span>}
    </Item>
  );
}

// --------------------------------------------------------------------------
// --- Globals Section(s)
// --------------------------------------------------------------------------

export default function Globals(): JSX.Element {

  // Hooks
  const [selection, updateSelection] = States.useSelection();
  const fcts = States.useSyncArray(functions).getArray().sort(
    (f, g) => alpha(f.name, g.name),
  );
  const { useFlipSettings } = Dome;
  const [stdlib, flipStdlib] =
    useFlipSettings('ivette.globals.stdlib', false);
  const [builtin, flipBuiltin] =
    useFlipSettings('ivette.globals.builtin', false);
  const [undef, flipUndef] =
    useFlipSettings('ivette.globals.undef', true);
  const [selected, flipSelected] =
    useFlipSettings('ivette.globals.selected', false);
  const [evaOnly, flipEvaOnly] =
    useFlipSettings('ivette.globals.evaonly', false);
  const multipleSelection = selection?.multiple;
  const multipleSelectionActive = multipleSelection?.allSelections.length > 0;
  const evaComputed = States.useSyncValue(computationState) === 'computed';

  function isSelected(fct: functionsData): boolean {
    return multipleSelection?.allSelections.some(
      (l) => fct.name === l?.fct,
    );
  }

  // Currently selected function.
  const current: undefined | string = selection?.current?.fct;

  function showFunction(fct: functionsData): boolean {
    const visible =
      (stdlib || !fct.stdlib)
      && (builtin || !fct.builtin)
      && (undef || fct.defined)
      && (!evaOnly || !evaComputed || (fct.eva_analyzed === true))
      && (!selected || !multipleSelectionActive || isSelected(fct));
    return visible || (!!current && fct.name === current);
  }

  function onSelection(name: string): void {
    updateSelection({ location: { fct: name } });
  }

  async function onContextMenu(): Promise<void> {
    const items: Dome.PopupMenuItem[] = [
      {
        label: 'Show Frama-C builtins',
        checked: builtin,
        onClick: flipBuiltin,
      },
      {
        label: 'Show stdlib functions',
        checked: stdlib,
        onClick: flipStdlib,
      },
      {
        label: 'Show undefined functions',
        checked: undef,
        onClick: flipUndef,
      },
      'separator',
      {
        label: 'Selected only',
        enabled: multipleSelectionActive,
        checked: selected,
        onClick: flipSelected,
      },
      {
        label: 'Analyzed by Eva only',
        enabled: evaComputed,
        checked: evaOnly,
        onClick: flipEvaOnly,
      },
    ];
    Dome.popupMenu(items);
  }

  // Filtered

  const filtered = fcts.filter(showFunction);
  const nTotal = fcts.length;
  const nFilter = filtered.length;
  const title = `Functions ${nFilter} / ${nTotal}`;

  const filterButtonProps = {
    icon: 'TUNINGS',
    title: `Functions filtering options (${nFilter} / ${nTotal})`,
    onClick: onContextMenu,
  };

  const filteredFunctions =
    filtered.map((fct) => (
      <FctItem
        key={fct.name}
        fct={fct}
        current={current}
        onSelection={onSelection}
      />
    ));

  const noFunction =
    <div className='dome-xSideBarSection-content'>
      <label className='dome-xSideBarSection-info'>
        {'There is no function to display.'}
      </label>
    </div>;

  const allFiltered =
    <div className='dome-xSideBarSection-content'>
      <label className='dome-xSideBarSection-info'>
        {'All functions are filtered. Try adjusting function filters.'}
      </label>
      <Button {...filterButtonProps} label='Functions filters' />
    </div>;

  return (
    <Section
      label="Functions"
      title={title}
      defaultUnfold
      settings="frama-c.sidebar.globals"
      rightButtonProps={filterButtonProps}
      summary={[nFilter]}
      className='globals-function-section'
    >
      {nFilter > 0 ? filteredFunctions : nTotal > 0 ? allFiltered : noFunction}
    </Section>
  );

}

// --------------------------------------------------------------------------
