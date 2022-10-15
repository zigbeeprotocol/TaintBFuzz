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
/* --- Ivette Extensions                                                  ---*/
/* --------------------------------------------------------------------------*/

import React from 'react';
import * as Dome from 'dome';

/* --------------------------------------------------------------------------*/
/* --- Extension Elements                                                 ---*/
/* --------------------------------------------------------------------------*/

const UPDATED = new Dome.Event('ivette.updated');

export interface ElementProps {
  id: string;
  rank?: number;
  children?: React.ReactNode;
}

function byPanel(p: ElementProps, q: ElementProps): number {
  const rp = p.rank ?? 0;
  const rq = q.rank ?? 0;
  if (rp < rq) return -1;
  if (rp > rq) return +1;
  const ip = p.id;
  const iq = q.id;
  if (ip < iq) return -1;
  if (ip > iq) return +1;
  return 0;
}

export class ElementRack {

  private rank = 1;
  private readonly items = new Map<string, ElementProps>();

  register(elt: ElementProps): void {
    if (elt.rank === undefined) elt.rank = this.rank;
    this.rank++;
    this.items.set(elt.id, elt);
    UPDATED.emit();
  }

  render(): JSX.Element {
    const panels: ElementProps[] = [];
    this.items.forEach((p) => { if (p.children) { panels.push(p); } });
    const contents = panels.sort(byPanel).map((p) => p.children);
    return <>{React.Children.toArray(contents)}</>;
  }

}

export function useRack(E: ElementRack): JSX.Element {
  Dome.useUpdate(UPDATED);
  return E.render();
}

export const SIDEBAR = new ElementRack();
export const TOOLBAR = new ElementRack();
export const STATUSBAR = new ElementRack();

export function Sidebar(): JSX.Element { return useRack(SIDEBAR); }
export function Toolbar(): JSX.Element { return useRack(TOOLBAR); }
export function Statusbar(): JSX.Element { return useRack(STATUSBAR); }

/* --------------------------------------------------------------------------*/
