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
// --- Text Pages
// --------------------------------------------------------------------------

/**
   A collection of text area and elements do render textual content.

   Inside such areas, all elements are styled like a classical web page.
   All elements are encapsulated inside a `<div>` with `'dome-pages'`
   class name, which can be used in your CSS selectors.

   All the textual parts are selectable inside the page, contrarily to
   most other widget components.

   The behaviour of `<a href=...>` elements differs for local links and
   external URLs. Local links trigger a `'dome.href'` event, that
   you can listen to from the originating renderer process, _eg. by
   using `Dome.useUpdate()` custom hook.

   External links launch the user's default browser.

   @packageDocumentation
   @module dome/text/pages
 */

import React from 'react';
import { classes } from 'dome/misc/utils';
import './style.css';

export interface TextProps {
  /** Additional classe(s). */
  className?: string;
  /** Additional style properties. */
  style?: React.CSSProperties;
  /** Inner Components. */
  children?: React.ReactNode;
}

// --------------------------------------------------------------------------
// --- Page
// --------------------------------------------------------------------------

/**
   Blank HTML page.

   The page has insets and shadows and fills the entire available area.
   Large content is crolled inside in both directions.
 */
export const Page = (props: TextProps): JSX.Element => (
  <div className="dome-xPages-page">
    <div
      className={classes('dome-xPages-sheet dome-pages', props.className)}
      style={props.style}
    >
      {props.children}
    </div>
  </div>
);

// --------------------------------------------------------------------------
// --- Note
// --------------------------------------------------------------------------

/**
   Blank HTML textarea.

   The area has small padding and no margin, and does not scroll its content.
 */
export const Note = (props: TextProps): JSX.Element => (
  <div
    className={classes('dome-xPages-note', 'dome-pages', props.className)}
    style={props.style}
  >
    {props.children}
  </div>
);

// --------------------------------------------------------------------------
