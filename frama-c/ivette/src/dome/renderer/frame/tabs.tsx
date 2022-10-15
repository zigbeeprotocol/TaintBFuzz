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
// --- Tabs
// --------------------------------------------------------------------------

/**
   @packageDocumentation
   @module dome/frame/tabs
*/

import React from 'react';
import { Icon } from 'dome/controls/icons';
import { classes } from 'dome/misc/utils';

import './style.css';

// --------------------------------------------------------------------------
// --- Tabs Bar
// --------------------------------------------------------------------------

export interface TabsBarProps {
  children?: React.ReactNode;
}

/** Container for Tabs. */
export function TabsBar(props: TabsBarProps): JSX.Element {
  return (
    <div className="dome-xTabsBar dome-color-frame">
      {props.children}
    </div>
  );
}

// --------------------------------------------------------------------------
// --- Single Tab
// --------------------------------------------------------------------------

export interface TabIcon {
  icon: string;
  title?: string;
  display?: boolean;
  enabled?: boolean;
  onClick?: () => void;
}

export interface TabProps {
  /** Tab's label icon. */
  icon?: string;
  /** Tab's label. */
  label?: string;
  /** Tab's tooltip text. */
  title?: string;
  /** Currently selected tab. */
  selected: boolean;
  headIcons?: TabIcon[];
  tailIcons?: TabIcon[];
  /** Selection callback. */
  onSelection: () => void;
}

/** Tab Selector. */
export function Tab(props: TabProps): JSX.Element {
  const { icon, selected, onSelection } = props;
  // --- Tab Rendering
  const { headIcons = [], tailIcons = [] } = props;
  const makeIcon = (icn: TabIcon): JSX.Element | null => {
    const { icon, title, display = true, enabled = true } = icn;
    if (!display) return null;
    const className = classes(
      'dome-xTab-icon',
      !enabled && 'dome-control-disabled'
    );
    return (
      <Icon key={icon}
        className={className}
        title={title}
        id={icon} size={10} offset={1}
        onClick={enabled ? icn.onClick : undefined}
      />
    );
  };
  const labelIcon = icon ? (
    <Icon key='icon'
      className='dome-xTab-icon'
      id={icon} size={10} offset={1} />
  ) : null;
  const header = selected ? headIcons.map(makeIcon) : null;
  const trailer = selected ? tailIcons.map(makeIcon) : null;
  const classNames = classes(
    'dome-xTab',
    selected ? 'dome-active' : 'dome-inactive'
  );
  return (
    <div
      className={classNames}
      title={props.title}
      onClick={onSelection}
    >
      {header}
      <div className='dome-xTab-filler' />
      {labelIcon}
      <label key='name' className='dome-xTab-label'>
        {props.label}
      </label>
      <div className='dome-xTab-filler' />
      {trailer}
    </div>
  );
}

// --------------------------------------------------------------------------
