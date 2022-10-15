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
// --- Utilities
// --------------------------------------------------------------------------

/**
   @packageDocumentation
   @module dome/misc/utils
 */

import type { CSSProperties } from 'react';

type Falsy = undefined | boolean | null | '';

export type ClassSpec = string | Falsy | { [cname: string]: true | Falsy };

/**
   Utility function to merge various HTML class properties
   into a `className` property.
   Class specifications can be made of:
    - a string, interpreted as a CSS class specification
    - an object, with keys corresponding to CSS class associated
      to true of falsy value.
    - any falsy value, which is discarded

    Example of usage:

    * ```ts
    *    const className = classes(
    *       'my-base-class',
    *        condition && 'my-class-when-condition',
    *        {
    *           'my-class-1': cond-1,
    *           'my-class-2': cond-2,
    *           'my-class-3': cond-3,
    *        }
    *    );
    * ```

 */
export function classes(
  ...args: ClassSpec[]
): string {
  const buffer: string[] = [];
  args.forEach((cla) => {
    if (cla) {
      if (typeof (cla) === 'string' && cla !== '') buffer.push(cla);
      else if (typeof (cla) === 'object') {
        const cs = Object.keys(cla);
        cs.forEach((c) => { if (cla[c]) buffer.push(c); });
      }
    }
  });
  return buffer.join(' ');
}

export type StyleSpec = Falsy | CSSProperties;

/**
   Utility function to merge various CSS style properties
   into a single CSS style object.

   Each style specification can be made of a CSS object or (discarded)
   falsy values.
   Example of usage:

   * ```ts
   *    const sty = styles(
   *        { ... },
   *        cond-1 && { ... },
   *        cond-2 && { ... },
   *    );
   * ```

*/

export function styles(
  ...args: StyleSpec[]
): CSSProperties | undefined {
  let empty = true;
  let buffer = {};
  args.forEach((sty) => {
    if (sty && typeof (sty) === 'object') {
      empty = false;
      buffer = { ...buffer, ...sty };
    }
  });
  return (empty ? undefined : buffer);
}

// --------------------------------------------------------------------------
