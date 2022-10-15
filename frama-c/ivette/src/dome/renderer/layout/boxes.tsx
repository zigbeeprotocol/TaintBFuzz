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
// --- Box Layout
// --------------------------------------------------------------------------

/**
   This modules offers several `<div>` containers with various
   predefined layout.

   Boxes are the very elementary way to layout components horizontally
   or vertically. The different kinds of proposed boxes differ in how they
   extends in both directions: normal boxes extends
   along their layout direction, _pack_ boxes don't extends and _fill_ boxes
   extends along both directions.

   Grids layout their component from left-to-right inside predefined _columns_,
   then vertically by wrapping cells in rows.

   The various containers layout and extensibility is listed below:
   - [[Hbox]] horizontal, fixed height
   - [[Vbox]] vertical, fixed width
   - [[Hpack]] horizontal, fixed dimensions
   - [[Vpack]] vertical, fixed dimensions
   - [[Hfill]] horizontal, extends in both directions
   - [[Vfill]] vertical, extends in both directions
   - [[Grid]] uses CSS grid columns, extends in both directions
   - [[Scroll]] scrolls its content

   Inside a box, you may add `<Space/>` and `<Filler/>` to separate items.
   Inside a grid, you may also use `<Space/>` or an empty `<div/>` for empty
   cells.

   <strong>Warning:</strong> large elements will be clipped if they overflow.
   If you want to add scrolling capabilities to some item that does not manage
   overflow natively, place it inside a `<Scroll/>` sub-container.

   @packageDocumentation
   @module dome/layout/boxes
 */

import React from 'react';
import * as Dome from 'dome';
import { Title } from 'dome/controls/labels';
import { classes, styles } from 'dome/misc/utils';
import './style.css';

// --------------------------------------------------------------------------
// --- Generic Box
// --------------------------------------------------------------------------

/** Div properties that you can also use in boxes. */
export type DivProps = React.HTMLAttributes<HTMLDivElement>;

const makeBox = (
  boxClasses: string,
  props: DivProps,
  morestyle?: React.CSSProperties,
): JSX.Element => {
  const { children, className, style, ...others } = props;
  const allClasses = classes(className, boxClasses);
  const allStyles = styles(style, morestyle);
  return (
    <div className={allClasses} style={allStyles} {...others}>
      {children}
    </div>
  );
};

// --------------------------------------------------------------------------
// --- Predefined Defaults
// --------------------------------------------------------------------------

/**
   Horizontal box (extends horizontally, no overflow).
*/
export const Hbox =
  (props: DivProps): JSX.Element =>
    makeBox('dome-xBoxes-hbox dome-xBoxes-box', props);

/**
   Vertical box (extends vertically, no overflow).
 */
export const Vbox =
  (props: DivProps): JSX.Element =>
    makeBox('dome-xBoxes-vbox dome-xBoxes-box', props);

/**
   Compact Horizontal box (fixed dimensions, no overflow).
 */
export const Hpack =
  (props: DivProps): JSX.Element =>
    makeBox('dome-xBoxes-hbox dome-xBoxes-pack', props);

/**
   Compact Vertical box (fixed dimensions, no overflow).
 */
export const Vpack =
  (props: DivProps): JSX.Element =>
    makeBox('dome-xBoxes-vbox dome-xBoxes-pack', props);

/**
   Horizontally filled box (fixed height, maximal width, no overflow).
 */
export const Hfill =
  (props: DivProps): JSX.Element =>
    makeBox('dome-xBoxes-hbox dome-xBoxes-fill', props);

/**
   Vertically filled box (fixed width, maximal height, no overflow).
 */
export const Vfill =
  (props: DivProps): JSX.Element =>
    makeBox('dome-xBoxes-vbox dome-xBoxes-fill', props);

// --------------------------------------------------------------------------
// --- Scrolling & Spacing
// --------------------------------------------------------------------------

/**
   Scrolling container.
 */
export const Scroll =
  (props: DivProps): JSX.Element =>
    makeBox('dome-xBoxes-scroll dome-container', props);

/**
   Rigid space between items in a box.
 */
export const Space =
  (props: DivProps): JSX.Element => makeBox('dome-xBoxes-space', props);

/**
   Extensible space between items in a box.
 */
export const Filler =
  (props: DivProps): JSX.Element => makeBox('dome-xBoxes-filler', props);

// --------------------------------------------------------------------------
// --- Grids
// --------------------------------------------------------------------------

export interface GridProps extends DivProps { columns?: string }

/**
   Grid box container.

   Layout its children in a multi-column grid. Each column is specified by its
   width, following the CSS Grid Layout `grid-template-columns` property.

   The rows are populated with children from left-to-right, using one column at
   a time.  Items layout can be modified by using CSS Grid Layout item
   properties.

   Example: `<Grid columns="25% auto auto"> ... </Grid>`
 */
export const Grid = (props: GridProps): JSX.Element => {
  const { columns, ...others } = props;
  return makeBox('dome-xBoxes-grid', others, { gridTemplateColumns: columns });
};

// --------------------------------------------------------------------------
// --- Folders
// --------------------------------------------------------------------------

export interface FolderProps {
  /** Title bar label. */
  label: string;
  /** Title bar tooltip. */
  title?: string;
  /** Window settings key. */
  settings?: string;
  /** Default state (`false`). */
  defaultUnfold?: boolean;
  /** Contents left margin (in pixels, defaults to 18). */
  indent?: number;
  /** Children JSX elements. */
  children?: React.ReactNode;
}

/**
   Foldable (vertical, packed) box.
   The head label is clickable to fold/unfold its contents.
*/
export const Folder = (props: FolderProps): JSX.Element => {
  const {
    settings,
    defaultUnfold = false,
    indent = 18,
    label, title, children,
  } = props;
  const [unfold, flip] = Dome.useFlipSettings(settings, defaultUnfold);
  const icon = unfold ? 'TRIANGLE.DOWN' : 'TRIANGLE.RIGHT';
  const display = unfold ? 'block' : 'none';
  return (
    <Vpack>
      <Hpack onClick={flip}>
        <Title icon={icon} label={label} title={title} />
      </Hpack>
      <Vpack style={{ display, marginLeft: indent }}>
        {children}
      </Vpack>
    </Vpack>
  );
};

// --------------------------------------------------------------------------
