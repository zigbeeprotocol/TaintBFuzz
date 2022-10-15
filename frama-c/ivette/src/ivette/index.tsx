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
/* --- Lab View Component                                                 ---*/
/* --------------------------------------------------------------------------*/

/**
   @packageDocumentation
   @module ivette
 */

import React from 'react';
import { DEVEL } from 'dome';
import { Label } from 'dome/controls/labels';
import { DefineElement } from 'dome/layout/dispatch';
import { GridItem, GridHbox, GridVbox } from 'dome/layout/grids';
import * as Lab from 'ivette@lab';
import * as Ext from 'ivette@ext';

/* --------------------------------------------------------------------------*/
/* --- Items                                                              ---*/
/* --------------------------------------------------------------------------*/

export interface ItemProps {
  /** Identifier. */
  id: string;
  /** Displayed name. */
  label: string;
  /** Tooltip description. */
  title?: string;
  /** Ordering index. */
  rank?: number;
}

export interface ContentProps extends ItemProps {
  /** Contents. */
  children?: React.ReactNode;
}

/* --------------------------------------------------------------------------*/
/* --- Groups                                                             ---*/
/* --------------------------------------------------------------------------*/

let GROUP: string | undefined;

/**
   Defines a group of components.
   To arrach components to the group, use their `group` property.
   Empty groups are not displayed.

   If provided, the group is used by default for all components registered
   during the continuation.
 */
export function registerGroup(group: ItemProps, job?: () => void): void {
  Lab.addLibraryItem('groups', group);
  if (job) {
    const STACK = GROUP;
    try {
      GROUP = group.id;
      job();
    } finally {
      GROUP = STACK;
    }
  }
}

/* --------------------------------------------------------------------------*/
/* --- View Layout                                                        ---*/
/* --------------------------------------------------------------------------*/

/**
   Alternating V-split and H-split layouts.
 */
export type Layout = string | Layout[];

function makeLayout(ly: Layout, hsplit = false): JSX.Element | null {
  if (typeof (ly) === 'string') return <GridItem id={ly} />;
  if (!ly) return null;
  if (hsplit) {
    return (
      <GridHbox>
        {React.Children.toArray(ly.map((l) => makeLayout(l, false)))}
      </GridHbox>
    );
  }
  return (
    <GridVbox>
      {React.Children.toArray(ly.map((l) => makeLayout(l, true)))}
    </GridVbox>
  );

}

export interface ViewLayoutProps extends ItemProps {
  /** Use this view by default. */
  defaultView?: boolean;
  /** View layout. */
  layout: Layout;
}

/** Register a new View. */
export function registerView(view: ViewLayoutProps): void {
  const { layout, ...viewprops } = view;
  Lab.addLibraryItem('views', {
    ...viewprops,
    children: makeLayout(layout),
  });
}

/* --------------------------------------------------------------------------*/
/* --- Components                                                         ---*/
/* --------------------------------------------------------------------------*/

export interface ComponentProps extends ContentProps {
  /** Group attachment. */
  group?: string;
}

/**
   Register the given Ivette Component.
   Components are sorted by rank and identifier among each group.
 */
export function registerComponent(props: ComponentProps): void {
  Lab.addLibraryItem('components', { group: GROUP, ...props });
}

export interface TitleBarProps {
  /** Displayed icon. */
  icon?: string;
  /** Displayed name (when mounted). */
  label?: string;
  /** Tooltip description (when mounted). */
  title?: string;
  /** TitleBar additional components (stacked to right). */
  children?: React.ReactNode;
}

/**
   LabView Component's title bar.
   Defines an alternative component title bar in current context.
   Default values are taken from the associated component.
 */
export function TitleBar(props: TitleBarProps): JSX.Element | null {
  const { icon, label, title, children } = props;
  const context = Lab.useTitleContext();
  if (!context.id) return null;
  return (
    <DefineElement id={`labview.title.${context.id}`}>
      <Label
        className="labview-handle"
        icon={icon}
        label={label || context.label}
        title={title || context.title}
      />
      {children}
    </DefineElement>
  );
}

/* --------------------------------------------------------------------------*/
/* --- Sidebar Panels                                                     ---*/
/* --------------------------------------------------------------------------*/

export interface ToolProps {
  id: string;
  rank?: number;
  children?: React.ReactNode;
}

export function registerSidebar(panel: ToolProps): void {
  Ext.SIDEBAR.register(panel);
}

export function registerToolbar(tools: ToolProps): void {
  Ext.TOOLBAR.register(tools);
}

export function registerStatusbar(status: ToolProps): void {
  Ext.STATUSBAR.register(status);
}

/* --------------------------------------------------------------------------*/
/* --- Sandbox                                                            ---*/
/* --------------------------------------------------------------------------*/

if (DEVEL) {
  registerGroup({
    id: 'sandbox',
    label: 'Sandbox',
    title: 'Ivette Sandbox Components (only in DEVEL mode)',
  });
  registerView({
    id: 'sandbox',
    rank: -2,
    label: 'Sandbox',
    title: 'Sandbox Playground (only in DEVEL mode)',
    layout: [],
  });
}

export function registerSandbox(props: ComponentProps): void {
  if (DEVEL) registerComponent({ ...props, group: 'sandbox' });
}

// --------------------------------------------------------------------------
