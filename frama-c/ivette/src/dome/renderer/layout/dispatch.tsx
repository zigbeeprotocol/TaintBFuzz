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
// --- Dispatch Layout
// --------------------------------------------------------------------------

/**

   This module allows to declare components anywhere in a component hierarchy
   and to render them a totally different place.

   You shall wrap dispatched components inside a `<Dispatch.Item>` container,
   and render them wherever you want with `<Dispatch.Render>`. Each target
   place can display only one uniquely identified item.

   This can be also used to display some item among many in one unique place.

   @packageDocumentation
   @module dome/layout/dispatch
 */

import React from 'react';
import { Event } from 'dome';

// --------------------------------------------------------------------------
// --- Global Dispatcher
// --------------------------------------------------------------------------

class ITEM {
  event: Event;
  rendered = false;
  content: React.ReactNode = undefined;
  constructor(id: string) {
    this.event = new Event(`dome-dispatch-${id}`);
  }

  update(content: React.ReactNode): void {
    this.content = content;
    if (this.rendered) {
      this.rendered = false;
      setImmediate(this.event.emit);
    }
  }
}

const ITEMS = new Map<string, ITEM>();

const getItem = (id: string): ITEM => {
  let item = ITEMS.get(id);
  if (!item) {
    item = new ITEM(id);
    ITEMS.set(id, item);
  }
  return item;
};

// --------------------------------------------------------------------------
// --- Element Definition
// --------------------------------------------------------------------------

export interface ElementProps {
  /** Element identifier. */
  id: string;
  /** Element contents. */
  children?: React.ReactNode;
}

/**
   Define an identified element.

   The `<DefineElement />` renders `null` and register its contents under
   the specified identifier, which would be rendered by `<RenderElement />`
   everywhere else.

   Multiple definitions of the same element might produce
   unpredictable results.
 */
export function DefineElement(props: ElementProps): JSX.Element | null {
  React.useEffect(() => {
    const item = getItem(props.id);
    item.update(props.children);
    return () => item.update(undefined);
  });
  return null;
}

// --------------------------------------------------------------------------
// --- Render Elements
// --------------------------------------------------------------------------

export interface RenderProps {
  id?: string;
  children?: React.ReactNode | ((content: React.ReactNode) => React.ReactNode);
}

/**
   Render an identified element.

   If the render element has a function as children, it is passed the content
   of the item, or `undefined` if there is no identifier or no
   corresponding `<DefineElement />` currently mounted.
 */
export function RenderElement(props: RenderProps): JSX.Element {
  const [age, setAge] = React.useState(0);
  const { id, children } = props;
  const item = id ? getItem(id) : undefined;
  React.useEffect(() => {
    if (item) {
      const { event } = item;
      const trigger = (): void => setAge(age + 1);
      event.on(trigger);
      return () => event.off(trigger);
    }
    return undefined;
  }, [age, item]);
  if (item) item.rendered = true;
  if (typeof (children) === 'function')
    return <>{children(item?.content)}</>;
  const content = item?.content || children || null;
  return <>{content}</>;
}

// --------------------------------------------------------------------------
