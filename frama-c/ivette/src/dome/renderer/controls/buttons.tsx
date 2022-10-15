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
// --- Buttons, Check Boxes and Radio Groups
// --------------------------------------------------------------------------

/**
   @packageDocumentation
   @module dome/controls/buttons
*/

import React from 'react';
import { classes } from 'dome/misc/utils';
import { Icon } from './icons';
import './style.css';

interface EVENT {
  stopPropagation: () => void;
}

const DISABLED = ({ disabled = false, enabled = true }): boolean => (
  !!disabled || !enabled
);

const TRIGGER = (onClick?: () => void) => (evt?: EVENT) => {
  evt?.stopPropagation();
  if (onClick) onClick();
};

// --------------------------------------------------------------------------
// --- Button
// --------------------------------------------------------------------------

const VISIBLE: React.CSSProperties = { visibility: 'visible' };
const HIDDEN: React.CSSProperties = { visibility: 'hidden' };

interface LABELprops {
  disabled: boolean;
  label: string;
}

const LABEL = ({ disabled, label }: LABELprops): JSX.Element => (
  <div className="dome-xButton-label">
    <div
      className="dome-xButton-label dome-control-enabled"
      style={disabled ? HIDDEN : VISIBLE}
    >{label}
    </div>
    <div
      className="dome-xButton-label dome-control-disabled"
      style={disabled ? VISIBLE : HIDDEN}
    >{label}
    </div>
  </div>
);

export type ButtonKind =
  'default' | 'primary' | 'warning' | 'positive' | 'negative';

export interface ButtonProps {
  /** Text of the label. Prepend to other children elements. */
  label?: string;
  /** Icon identifier. Displayed on the left side of the label. */
  icon?: string;
  /** Tool-tip description. */
  title?: string;
  /** Additional class. */
  className?: string;
  /** Additional style. */
  style?: React.CSSProperties;
  /** Defaults to `false`. */
  selected?: boolean;
  /** Defaults to `true`. */
  enabled?: boolean;
  /** Defaults to `false`. */
  disabled?: boolean;
  /** Defaults to `true`. */
  visible?: boolean;
  /** Defaults to `true`. */
  display?: boolean;
  /**
     May gain focus.
     Focused button can be clicked with the `ENTER` key.
     Defaults to `false`.
   */
  focusable?: boolean;
  /** Styled bytton:
     - `'default'`: normal button;
     - `'primary'`: primary button, in blue;
     - `'warning'`: warning button, in orange;
     - `'positive'`: positive button, in green;
     - `'negative'`: negative button, in red.
   */
  kind?: ButtonKind;
  /** Blinking button. Defaults to `false`. */
  blink?: boolean;
  /**
     Button callback.
     An undefined callback automatically disables the button.
   */
  onClick?: () => void;
}

/** Standard button. */
export function Button(props: ButtonProps): JSX.Element {
  const disabled = props.onClick ? DISABLED(props) : true;
  const {
    focusable = false, kind = 'default',
    visible = true, display = true, blink = false,
    selected, icon, label, className = '',
  } = props;
  const theClass = classes(
    'dome-xButton dome-xBoxButton',
    `dome-xButton-${selected ? 'selected' : kind}`,
    blink && 'dome-xButton-blink',
    !visible && 'dome-control-hidden',
    !display && 'dome-control-erased',
    className,
  );
  const nofocus = focusable ? undefined : true;
  return (
    <button
      type="button"
      className={theClass}
      disabled={disabled}
      onClick={TRIGGER(props.onClick)}
      title={props.title}
      style={props.style}
      tabIndex={nofocus && -1}
      onMouseDown={nofocus && ((evt) => evt.preventDefault())}
    >
      {icon && <Icon id={icon} />}
      {label && <LABEL disabled={disabled} label={label} />}
    </button>
  );
}

// --------------------------------------------------------------------------
// --- Icon Button
// --------------------------------------------------------------------------

/** Circled Icon Button. The label property is ignored. */
export const CircButton = (props: ButtonProps): JSX.Element => {
  const disabled = props.onClick ? DISABLED(props) : true;
  const {
    focusable = false, kind = 'default',
    visible = true, display = true,
    selected, icon, blink, className = '',
  } = props;
  const theClass = classes(
    'dome-xButton dome-xCircButton',
    `dome-xButton-${selected ? 'selected' : kind}`,
    blink && 'dome-xButton-blink',
    !visible && 'dome-control-hidden',
    !display && 'dome-control-erased',
    className,
  );
  const nofocus = focusable ? undefined : true;
  return (
    <button
      type="button"
      className={theClass}
      disabled={disabled}
      onClick={TRIGGER(props.onClick)}
      title={props.title}
      style={props.style}
      tabIndex={nofocus && -1}
      onMouseDown={nofocus && ((evt) => evt.preventDefault())}
    >
      {icon && <Icon offset={-1} id={icon} />}
    </button>
  );
};

// --------------------------------------------------------------------------
// --- Icon Button
// --------------------------------------------------------------------------

export type IconButtonKind =
  undefined | 'selected' | 'default' | 'negative' | 'positive' | 'warning';

export interface IconButtonProps {
  /** Icon identifier. Displayed on the left side of the label. */
  icon: string;
  /** Tool-tip description. */
  title?: string;
  /** Icon size, in pixels (default: `12`). */
  size?: number;
  /** Vertical offset, in pixels. */
  offset?: number;
  /** Additional class. */
  className?: string;
  /** Additional style. */
  style?: React.CSSProperties;
  /** Defaults to `false`. */
  selected?: boolean;
  /** Defaults to `true`. */
  enabled?: boolean;
  /** Defaults to `false`. */
  disabled?: boolean;
  /** Defaults to `true`. */
  visible?: boolean;
  /** Defaults to `true`. */
  display?: boolean;
  /** Styled bytton:
     - `'default'`: normal button;
     - `'selected'`: selection button, in blue;
     - `'warning'`: warning button, in orange;
     - `'positive'`: positive button, in green;
     - `'negative'`: negative button, in red.
   */
  kind?: IconButtonKind;
  /**
     Button callback.
     An undefined callback automatically disables the button.
   */
  onClick?: () => void;
}

/** Borderless Icon Button. Label property is ignored. */
export function IconButton(props: IconButtonProps): JSX.Element | null {
  const disabled = props.onClick ? DISABLED(props) : true;
  const {
    icon, title, className,
    visible = true, display = true, selected,
    kind = 'default',
  } = props;
  if (!icon) return null;
  const theClass = classes(
    'dome-xIconButton',
    `dome-xIconButton-${selected ? 'selected' : kind}`,
    (disabled ? 'dome-control-disabled' : 'dome-control-enabled'),
    !visible && 'dome-control-hidden',
    !display && 'dome-control-erased',
    className,
  );
  return (
    <Icon
      id={icon}
      title={title}
      size={props.size}
      offset={props.offset}
      style={props.style}
      className={theClass}
      onClick={TRIGGER(disabled ? undefined : props.onClick)}
    />
  );
}

// --------------------------------------------------------------------------
// --- CheckBox
// --------------------------------------------------------------------------

const CHECKBOX_ENABLED = 'dome-control-enabled dome-xCheckbox ';
const CHECKBOX_DISABLED = 'dome-control-disabled dome-xCheckbox ';

export interface CheckProps {
  /** Button label. */
  label: string;
  /** Button tooltip. */
  title?: string;
  /** Additional class. */
  className?: string;
  /** Additional style. */
  style?: React.CSSProperties;
  /** Defaults to `true`. */
  enabled?: boolean;
  /** Defaults to `false`. */
  disabled?: boolean;
  /** Defaults to `false`. */
  value?: boolean;
  /** Callback to changes. */
  onChange?: (newValue: boolean) => void;
}

/** Checkbox button. */
export const Checkbox = (props: CheckProps): JSX.Element => {
  const { value, onChange } = props;
  const disabled = onChange ? DISABLED(props) : true;
  const callback = onChange && (() => onChange(!value));
  const baseClass = disabled ? CHECKBOX_DISABLED : CHECKBOX_ENABLED;
  const labelClass = props.className || '';
  return (
    <label
      title={props.title}
      style={props.style}
      className={baseClass + labelClass}
    >
      <input
        type="checkbox"
        disabled={disabled}
        checked={value}
        onChange={callback}
      />
      {props.label}
    </label>
  );
};

/** Switch button. */
export const Switch = (props: CheckProps): JSX.Element => {
  const { onChange, value } = props;
  const disabled = onChange ? DISABLED(props) : true;
  const iconId = props.value ? 'SWITCH.ON' : 'SWITCH.OFF';
  const onClick = onChange && (() => onChange(!value));
  const className = classes(
    'dome-xSwitch',
    (disabled ? 'dome-control-disabled' : 'dome-control-enabled'),
    props.className,
  );
  return (
    <label
      title={props.title}
      style={props.style}
      className={className}
      onClick={TRIGGER(onClick)}
    >
      <Icon size={16} id={iconId} />
      {props.label}
    </label>
  );
};

// --------------------------------------------------------------------------
// --- Radio Button
// --------------------------------------------------------------------------

export interface RadioProps<A> {
  /** Button label. */
  label: string;
  /** Button tooltip. */
  title?: string;
  /** Additional class. */
  className?: string;
  /** Additional style. */
  style?: React.CSSProperties;
  /** Defaults to `true`. */
  enabled?: boolean;
  /** Defaults to `false`. */
  disabled?: boolean;
  /** Value associated to the Radio. */
  value: A;
  /** Currently selected value. */
  selection?: A;
  /** Callback to changes. */
  onSelection?: (newValue: A) => void;
}

/** Radio Button. See also [[RadioGroup]]. */
export function Radio<A>(props: RadioProps<A>): JSX.Element {
  const { onSelection, value, selection } = props;
  const disabled = onSelection ? DISABLED(props) : true;
  const checked = value === selection;
  const onChange = onSelection && (() => onSelection(value));
  const baseClass = disabled ? CHECKBOX_DISABLED : CHECKBOX_ENABLED;
  const labelClass = props.className || '';
  return (
    <label
      title={props.title}
      style={props.style}
      className={baseClass + labelClass}
    >
      <input
        type="radio"
        disabled={disabled}
        checked={checked}
        onChange={onChange}
      />
      {props.label}
    </label>
  );
}

// --------------------------------------------------------------------------
// --- Radio Group
// --------------------------------------------------------------------------

export interface RadioGroupProps<A> {
  /** Defaults to `true`. */
  enabled?: boolean;
  /** Defaults to `false`. */
  disabled?: boolean;
  /** Currently selected value. */
  value?: A;
  /** Callback to selected values. */
  onChange?: (newValue: A) => void;
  /** Default selected value. */
  className?: string;
  /** Additional style for the `< dov /> ` container of Raiods */
  style?: React.CSSProperties;
  /** [[Radio]] Buttons. */
  children?: React.ReactNode;
}

/**
   Selector of Radio Buttons.  Childrens of the `RadioGroup` shall be [[Radio]]
   buttons.

   The selected value of the group is broadcasted to the radio buttons. Their
   callbacks are activated _before_ the radio group one, if any.

   If the radio group is disabled, all the radio buttons are disabled also and
   their `disabled` properties are ignored. On the contrary, when the radio
   group is enabled, the `disabled` property of each radio button is taken into
   account.

   The radio buttons inside a group are laidout in a vertical box with the
   additional styling properties.
*/
export function RadioGroup<A>(props: RadioGroupProps<A>): JSX.Element {
  const {
    className = '',
    style,
    value: selection,
    onChange: onGroupSelect,
  } = props;
  const disabledGroup = onGroupSelect ? DISABLED(props) : true;
  const makeRadio = (elt: unknown): JSX.Element => {
    const typedElt = elt as React.ReactElement<RadioProps<A>>;
    const radioProps = typedElt.props;
    const disabled = disabledGroup || DISABLED(radioProps);
    const { onSelection: onRadioSelect } = radioProps;
    const onSelection = (v: A): void => {
      if (onRadioSelect) onRadioSelect(v);
      if (onGroupSelect) onGroupSelect(v);
    };
    return React.cloneElement(typedElt, {
      disabled,
      enabled: !disabled,
      selection,
      onSelection,
    });
  };
  return (
    <div className={`dome - xRadio - group ${className} `} style={style}>
      {React.Children.map(props.children, makeRadio)}
    </div>
  );
}

// --------------------------------------------------------------------------
// --- Selector
// --------------------------------------------------------------------------

export interface SelectProps {
  /** Field identifier (to make forms or labels) */
  id?: string;
  /** Button tooltip */
  title?: string;
  /** Button placeholder */
  placeholder?: string;
  /** Defaults to `true`. */
  enabled?: boolean;
  /** Defaults to `false`. */
  disabled?: boolean;
  /** Currently selected value. */
  value?: string;
  /** Callback to selected values. */
  onChange?: (newValue?: string) => void;
  /** Default selected value. */
  className?: string;
  /** Additional style for the `< dov /> ` container of Raiods */
  style?: React.CSSProperties;
  /** Shall be standard `<option/>` and `<optgroup/>` elements. */
  children?: React.ReactNode;
}

/**
   Menu Button.

   The different options shall be specified with HTML
   `< option/>` and `<optgroup/>` elements.
   Options and group shall be specified as follows:

   *   <optgroup label='…'>…</optgroup>
   *   <option value='…' disabled=… >…</option>

 */
export function Select(props: SelectProps): JSX.Element {
  const { onChange, placeholder } = props;
  const className = classes(
    'dome-xSelect dome-xBoxButton dome-xButton-default dome-xButton-label',
    props.className,
  );
  const disabled = onChange ? DISABLED(props) : true;
  const callback = (evt: React.ChangeEvent<HTMLSelectElement>): void => {
    if (onChange) onChange(evt.target.value);
  };
  return (
    <select
      id={props.id}
      disabled={disabled}
      className={className}
      style={props.style}
      title={props.title}
      value={props.value}
      onChange={callback}
    >
      {placeholder && <option value="">— {placeholder} —</option>}
      {props.children}
    </select >
  );
}

// --------------------------------------------------------------------------
// --- Text Input
// --------------------------------------------------------------------------

export interface FieldProps {
  /** Field identifier (to make forms or labels) */
  id?: string;
  /** Button tooltip */
  title?: string;
  /** Button placeholder */
  placeholder?: string;
  /** Defaults to `true`. */
  enabled?: boolean;
  /** Defaults to `false`. */
  disabled?: boolean;
  /** Default fo `false`. */
  autoFocus?: boolean;
  /** Currently selected value (updated on `ENTER` key) */
  value?: string;
  /** Callback on `ENTER` key. */
  onChange?: (newValue: string) => void;
  /** Callback on every modification. */
  onEdited?: (tmpValue: string) => void;
  /** Default selected value. */
  className?: string;
  /** Additional style for the `< dov /> ` container of Raiods */
  style?: React.CSSProperties;
}

/**
   Text Field.
*/
export const Field = (props: FieldProps): JSX.Element => {
  const [current, setCurrent] = React.useState<string>();
  const { className = '', onChange, onEdited, value = '' } = props;
  const disabled = onChange ? DISABLED(props) : true;
  const theValue = current ?? value;
  const ONCHANGE = (evt: React.ChangeEvent<HTMLInputElement>): void => {
    const text = evt.target.value || '';
    setCurrent(text);
    if (onEdited) onEdited(text);
  };
  const ONKEYPRESS = (evt: React.KeyboardEvent): void => {
    switch (evt.key) {
      case 'Enter':
        setCurrent(undefined);
        if (onChange && current) onChange(current);
        break;
      case 'Escape':
        setCurrent(undefined);
        break;
      default:
        break;
    }
  };
  return (
    <input
      id={props.id}
      type="text"
      autoFocus={!disabled && props.autoFocus}
      value={theValue}
      className={`dome - xField ${className} `}
      style={props.style}
      disabled={disabled}
      placeholder={props.placeholder}
      onKeyPress={ONKEYPRESS}
      onChange={ONCHANGE}
    />
  );
};

// --------------------------------------------------------------------------
