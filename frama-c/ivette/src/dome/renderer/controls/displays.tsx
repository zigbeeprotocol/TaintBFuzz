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
// --- LEDs, LCD, meters, etc.
// --------------------------------------------------------------------------

/**
   @packageDocumentation
   @module dome/controls/displays
 */

import React from 'react';
import { classes } from 'dome/misc/utils';
import { Icon } from './icons';
import { LabelProps } from './labels';
import './style.css';

// --------------------------------------------------------------------------
// --- LCD
// --------------------------------------------------------------------------

/** Button-like label. */
export function LCD(props: LabelProps): JSX.Element {
  const className = classes(
    'dome-xButton dome-xBoxButton dome-text-code dome-xButton-lcd ',
    props.className,
  );
  return (
    <label
      className={className}
      title={props.title}
      style={props.style}
    >
      {props.icon && <Icon id={props.icon} />}
      {props.label}
      {props.children}
    </label>
  );
}

// --------------------------------------------------------------------------
// --- Led
// --------------------------------------------------------------------------

export type LEDstatus =
  undefined | 'inactive' | 'active' | 'positive' | 'negative' | 'warning';

export interface LEDprops {
  /**
     Led status:
     - `'inactive'`: off (default)
     - `'active'`: blue color
     - `'positive'`: green color
     - `'negative'`: red color
     - `'warning'`: orange color
   */
  status?: LEDstatus;
  /** Blinking Led (default: `false`). */
  blink?: boolean;
  /** Tooltip text. */
  title?: string;
  /** Additional CSS class. */
  className?: string;
  /** Additional CSS style. */
  style?: React.CSSProperties;
}

export const LED = (props: LEDprops): JSX.Element => {
  const className = classes(
    'dome-xButton-led',
    `dome-xButton-led-${props.status || 'inactive'}`,
    props.blink && 'dome-xButton-blink',
    props.className,
  );
  return (
    <div className={className} title={props.title} style={props.style} />
  );
};

// --------------------------------------------------------------------------
// --- Metter
// --------------------------------------------------------------------------

export interface MeterProps {
  /** Additional CSS class. */
  className?: string;
  /** Additional CSS style. */
  style?: React.CSSProperties;
  /** Disabled control. */
  /** Meter value. Undefined means disabled. */
  value: number; /** default is undefined */
  min?: number;  /** default is 0.0 */
  low?: number;  /** default is 0.0 */
  high?: number; /** default is 1.0 */
  max?: number;  /** default is 1.0 */
  optimum?: number | 'LOW' | 'MEDIUM' | 'HIGH'; /** default is undefined */
}

export const Meter = (props: MeterProps): JSX.Element => {
  const { className, style, value, optimum, ...ms } = props;
  const min = props.min ?? 0.0;
  const max = props.max ?? 1.0;
  const low = props.low ?? min;
  const hight = props.high ?? max;
  const theClass = classes('dome-xMeter', className);
  let opt: number | undefined;
  if (value !== undefined)
    switch (optimum) {
      case 'LOW': opt = (min + low) / 2; break;
      case 'MEDIUM': opt = (low + hight) / 2; break;
      case 'HIGH': opt = (hight + max) / 2; break;
      default: opt = optimum;
    }
  const mv = value === undefined ? min : Math.min(max, Math.max(min, value));
  return (
    <meter
      className={theClass}
      style={style}
      value={mv}
      optimum={opt}
      {...ms} />
  );
};

// --------------------------------------------------------------------------
