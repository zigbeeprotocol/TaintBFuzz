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
// --- ToolBars
// --------------------------------------------------------------------------

/**
   @packageDocumentation
   @module dome/frame/toolbars
 */

import React from 'react';
import { Event, find, usePromise } from 'dome';
import { SVG } from 'dome/controls/icons';
import { Label } from 'dome/controls/labels';
import { classes } from 'dome/misc/utils';
import './style.css';

// --------------------------------------------------------------------------
// --- ToolBar Container
// --------------------------------------------------------------------------

export interface ToolBarProps {
  className?: string;
  style?: React.CSSProperties;
  children?: React.ReactNode;
}

/**
   @class
   @summary Container for toolbar items.
 */
export function ToolBar(props: ToolBarProps): JSX.Element | null {
  const { children } = props;
  const n = React.Children.count(children);
  if (n === 0) return null;
  const className = classes(
    'dome-xToolBar',
    'dome-color-frame',
    props.className,
  );
  return (
    <div className={className} style={props.style}>
      <div className="dome-xToolBar-inset" />
      {children}
      <div className="dome-xToolBar-inset" />
    </div>
  );
}

// --------------------------------------------------------------------------
// --- ToolBar Spaces
// --------------------------------------------------------------------------

/** Fixed (tiny) space. */
export const Inset = (): JSX.Element => (
  <div className="dome-xToolBar-inset" />
);

/** Fixed space. */
export const Space = (): JSX.Element => (
  <div className="dome-xToolBar-space" />
);

/** Auto-extensible space. */
export const Filler = (): JSX.Element => (
  <div className="dome-xToolBar-filler" />
);

/** Fixed space with vertical rule. */
export const Separator = (): JSX.Element => (
  <div className="dome-xToolBar-separator">
    <div className="dome-xToolBar-vrule" />
  </div>
);

const SELECT = 'dome-xToolBar-control dome-selected';
const BUTTON = 'dome-xToolBar-control dome-color-frame';
const KIND = (kind: undefined | string): string => (
  kind ? ` dome-xToolBar-${kind}` : ''
);

export type ButtonKind =
  | 'default' | 'cancel' | 'warning' | 'positive' | 'negative';

export interface ButtonProps<A> {
  /** Button icon, Cf. [gallery](gallery-icons.html). */
  icon?: string;
  /** Button label. */
  label?: string;
  /** Button tooltip text. */
  title?: string;
  /** Button kind. */
  kind?: ButtonKind;
  /** Button is displayed (default `true`). */
  visible?: boolean;
  /** Button is hidden (default `false`). */
  hidden?: boolean;
  /** Enabled State (default `true`). */
  enabled?: boolean;
  /** Disabled State (default `false`). */
  disabled?: boolean;
  /** Selection State (defaults to `false` or `selection` equal to `value`). */
  selected?: boolean;
  /** Button's value. */
  value?: A;
  /** Currently selected value. */
  selection?: A;
  /** Selection callback. Receives the button's value. */
  onClick?: (value: A | undefined) => void;
  /** Button contents */
  children?: React.ReactNode;
}

/** Toolbar Button. */
export function Button<A = undefined>(
  props: ButtonProps<A>
): JSX.Element | null {
  const { visible = true, hidden = false } = props;
  if (!visible || hidden) return null;
  const { enabled = true, disabled = false } = props;
  const { selected, value, selection, onClick } = props;
  const isSelected = selected !== undefined
    ? selected
    : (value !== undefined && value === selection);
  return (
    <button
      type="button"
      disabled={disabled || !enabled}
      className={isSelected ? SELECT : (BUTTON + KIND(props.kind))}
      onClick={onClick && (() => onClick(value))}
      title={props.title}
    >
      {props.icon && <SVG id={props.icon} />}
      {props.label && <label>{props.label}</label>}
      {props.children}
    </button>
  );
}

export interface SwitchProps {
  /** Switch tooltip. */
  title?: string;
  /** Additional class. */
  className?: string;
  /** Additional style. */
  style?: React.CSSProperties;
  /** Defaults to `true`. */
  enabled?: boolean;
  /** Defaults to `false`. */
  disabled?: boolean;
  /** Switch position. Defaults to 'left'. */
  position?: 'left' | 'right';
  /** Click callback. */
  onChange?: (newPosition: 'left' | 'right') => void;
}

/** Toolbar Left/Right Switch. */
export function Switch(props: SwitchProps): JSX.Element | null {
  const { position, onChange } = props;
  const checked = position === 'right';
  const { title, className, style } = props;
  const { enabled = true, disabled = false } = props;
  const callback = onChange && (() => onChange(checked ? 'left' : 'right'));
  if (disabled || !enabled) return null;
  return (
    <label className={classes('dome-xSwitch', className)} style={style}>
      <input type={'checkbox'} checked={checked} onChange={callback} />
      <span className={'dome-xSwitch-slider'} title={title} />
    </label >
  );
}

// --------------------------------------------------------------------------
// --- Selection Props
// --------------------------------------------------------------------------

export interface SelectionProps<A> {
  /** Enabled Group (default `true`). */
  enabled?: boolean;
  /** Disabled Group (default `false`). */
  disabled?: boolean;
  /** Currently selected button. */
  value?: A;
  /** Callback on clicked buttons. */
  onChange?: (value: undefined | A) => void;
  /** Buttons array. */
  children: React.ReactElement[];
}

// --------------------------------------------------------------------------
// --- ToolBar Button Group
// --------------------------------------------------------------------------

export interface ButtonGroupProps<A> extends SelectionProps<A> {
  className?: string;
  style?: React.CSSProperties;
}

/**
   Toolbar Button Group.

   Properties of the button group are passed down the buttons of the group
   as appropriate defaults.
 */
export function ButtonGroup<A>(props: ButtonGroupProps<A>): JSX.Element {
  const { children, value, onChange, enabled, disabled } = props;
  const baseProps: ButtonProps<A> = {
    enabled,
    disabled,
    selection: value,
    onClick: onChange,
  };
  const className = classes('dome-xToolBar-group', props.className);
  return (
    <div className={className} style={props.style}>
      {React.Children.map(children, (elt) => React.cloneElement(
        elt,
        { ...baseProps, ...elt.props },
      ))}
    </div>
  );
}

// --------------------------------------------------------------------------
// --- ToolBar Menu
// --------------------------------------------------------------------------

/** Toolbar Selector Menu.

   Behaves likes a standard `<select>` element, except that callback directly
   receives the select value, not the entire event.
   The list of options shall be given with standard
   `<option value={...} label={...}>` elements.
 */
export function Select(props: SelectionProps<string>): JSX.Element {
  const { enabled = true, disabled = false, onChange } = props;
  const callback =
    (evt: React.ChangeEvent<HTMLSelectElement>): void => {
      if (onChange) onChange(evt.target.value);
    };
  return (
    <select
      className="dome-xToolBar-control dome-color-frame"
      value={props.value}
      disabled={disabled || !enabled}
      onChange={callback}
    >
      {props.children}
    </select>
  );
}

// --------------------------------------------------------------------------
// --- ModalActionField necessary types
// --------------------------------------------------------------------------

/** Description of a hint used to populate the suggestions. */
export interface Hint {
  id: string | number;
  icon?: string;
  label: string;
  title?: string;
  value(): void;
  rank?: number;
}

/** Total order on hints. */
export function byHint(a: Hint, b: Hint): number {
  return (a.rank ?? 0) - (b.rank ?? 0);
}

/** Type alias for functions that build hints list from a pattern. */
export type HintsEvaluator = (pattern: string) => Promise<Hint[]>;

/** Description of an action mode. */
export interface ActionMode {
  /** Mode tooltip title. */
  title?: string;
  /** Mode tooltip label. */
  label: string;
  /** Mode placeholder text. */
  placeholder?: string;
  /** Icon displayed when the mode is selected. */
  icon: string;
  /** CSS class for the mode section. */
  className: string;
  /** Hints provider. */
  hints: HintsEvaluator;
  /** Hint selection callback. Defaults to evaluate the <value> field. */
  onHint?: (hint: Hint) => void;
  /** Action to perform when Enter is hit. Useful for modes without hints. */
  onEnter?: (pattern: string) => void;
  /** Event that triggers a focus request. */
  event?: Event<void>;
}

// --------------------------------------------------------------------------
// --- ModalActionField default mode: Search
// --------------------------------------------------------------------------

const searchEvaluators = new Map<string, HintsEvaluator>();

// Updates to the new evaluator if the id is already registered
export function registerSearchHints(
  id: string,
  search: HintsEvaluator
): void {
  searchEvaluators.set(id, search);
}

export function unregisterSearchHints(id: string): void {
  searchEvaluators.delete(id);
}

async function searchHints(pattern: string): Promise<Hint[]> {
  if (pattern === '') return [];
  const promises = Array.from(searchEvaluators).map(([_id, E]) => E(pattern));
  const hints = await Promise.all(promises);
  return hints.flat().sort(byHint);
}

const searchMode: ActionMode = {
  label: "Search",
  title: 'Search through the global definitions',
  placeholder: "Search…",
  icon: "SEARCH",
  className: 'dome-xToolBar-searchMode',
  hints: searchHints,
  event: find,
};

// --------------------------------------------------------------------------
// --- ModalActionField mode button component
// --------------------------------------------------------------------------

interface ModeButtonComponentProps {
  current: ActionMode;
  onClick: () => void;
}

function ModeButton(props: ModeButtonComponentProps): JSX.Element {
  const { current, onClick } = props;
  return (
    <div
      className={classes("dome-xToolBar-modeSelection", current.className)}
      onClick={onClick}
    >
      <SVG
        className="dome-xToolBar-modeIcon"
        id={current.icon}
        offset={-1}
      />
    </div>
  );
}

// --------------------------------------------------------------------------
// --- ModalActionField suggestions component
// --------------------------------------------------------------------------

interface SuggestionsProps {
  hints: Hint[];
  onHint: (hint: Hint) => void;
  index: number;
}

function scrollToRef(r: null | HTMLLabelElement): void {
  if (r) r.scrollIntoView({ block: 'nearest' });
}

function Suggestions(props: SuggestionsProps): JSX.Element {
  const { hints, onHint, index } = props;

  // Computing the relevant suggestions. */
  const suggestions = hints.map((h, k) => {
    const selected = k === index || hints.length === 1;
    const classSelected = selected && 'dome-xToolBar-searchindex';
    const className = classes('dome-xToolBar-searchitem', classSelected);
    return (
      <Label
        ref={selected ? scrollToRef : undefined}
        key={h.id}
        icon={h.icon}
        title={h.title}
        className={className}
        onClick={() => onHint(h)}
      >
        {h.label}
      </Label>
    );
  });

  // Rendering the component.
  return (
    <div
      style={{ visibility: suggestions.length > 0 ? 'visible' : 'hidden' }}
      className='dome-xToolBar-suggestions'
      onMouseDown={(event) => event.preventDefault()}
    >
      {suggestions}
    </div>
  );
}

// --------------------------------------------------------------------------
// --- ModalActionField input field component
// --------------------------------------------------------------------------

interface ActionInputProps {
  title?: string;
  placeholder?: string;
  hints: Hint[];
  onHint: (hint: Hint) => void;
  onEnter?: (pattern: string) => void;
  index: number;
  setIndex: (n: number) => void;
  pattern: string;
  setPattern: (p: string) => void;
  inputRef: React.MutableRefObject<HTMLInputElement | null>;
}

function ActionInput(props: ActionInputProps): JSX.Element {
  const { title, placeholder, hints, onHint, onEnter } = props;
  const { index, setIndex, pattern, setPattern, inputRef } = props;

  // Blur Event
  const onBlur = (): void => { setPattern(''); setIndex(-1); };

  // Key Up Events
  const onKeyUp = (evt: React.KeyboardEvent): void => {
    const blur = (): void => inputRef.current?.blur();
    switch (evt.key) {
      case 'Escape':
        blur();
        break;
      case 'Enter':
        blur();
        if (index >= 0 && index < hints.length) onHint(hints[index]);
        else if (hints.length === 1) onHint(hints[0]);
        else if (onEnter) onEnter(pattern);
        break;
      case 'ArrowUp':
        if (index < 0) setIndex(hints.length - 1);
        if (index > 0) setIndex(index - 1);
        break;
      case 'ArrowDown':
        if (index < 0 && 0 < hints.length) setIndex(0);
        if (0 <= index && index < hints.length - 1) setIndex(index + 1);
        break;
    }
  };

  // Key Down Events. Disables the default behavior on ArrowUp and ArrowDown.
  const onKeyDown = (evt: React.KeyboardEvent): void => {
    if (evt.key === 'ArrowUp' || evt.key === 'ArrowDown') evt.preventDefault();
  };

  // // Input Events
  const onChange = (evt: React.ChangeEvent<HTMLInputElement>): void => {
    setIndex(-1);
    setPattern(evt.target.value);
  };

  return (
    <input
      type="search"
      placeholder={placeholder}
      ref={inputRef}
      title={title}
      value={pattern}
      onKeyUp={onKeyUp}
      onKeyDown={onKeyDown}
      onChange={onChange}
      onBlur={onBlur}
    />
  );
}

// --------------------------------------------------------------------------
// --- ModalActionField component
// --------------------------------------------------------------------------

export const RegisterMode: Event<ActionMode> =
  new Event('dome.actionmode.register');

export const UnregisterMode: Event<ActionMode> =
  new Event('dome.actionmode.unregister');

export function ModalActionField(): JSX.Element {

  // Internal state of the component along with useful functions acting on it.
  const inputRef = React.useRef<HTMLInputElement | null>(null);
  const [index, setIndex] = React.useState(-1);
  const [pattern, setPattern] = React.useState('');
  const [current, onModeChange] = React.useState<ActionMode>(searchMode);
  const focus = (): void => inputRef.current?.focus();
  const changeMode = (m: ActionMode) =>
    (): void => { onModeChange(m); focus(); };
  const toDefault = (): void => onModeChange(searchMode);
  const reset = (m: ActionMode): void => { if (current === m) toDefault(); };

  // Set of all modes currently active. We populate it by reacting to
  // RegisterMode and UnregisterMode events. We also activate the mode event if
  // available. Everything is cleaned when the component is unmounted.
  const [allModes] = React.useState<Set<ActionMode>>(new Set());
  React.useEffect(() => {
    const on = (m: ActionMode): void => m.event?.on(changeMode(m));
    const register = (m: ActionMode): void => { allModes.add(m); on(m); };
    const off = (m: ActionMode): void => m.event?.off(changeMode(m));
    const remove =
      (m: ActionMode): void => { allModes.delete(m); off(m); reset(m); };
    RegisterMode.on(register); UnregisterMode.on(remove);
    return () => { RegisterMode.off(register); UnregisterMode.off(remove); };
  });

  // Register the search mode.
  React.useEffect(() => RegisterMode.emit(searchMode));

  // Compute the hints for the current mode.
  const { hints, onHint = (h) => h.value(), onEnter } = current;
  const hintsPromise = React.useMemo(() => hints(pattern), [pattern, hints]);
  const { result = [] } = usePromise(hintsPromise);

  // Auxiliary function that build a Hint from an ActionMode.
  const modeToHint = (mode: ActionMode): Hint => {
    const { label, title = '', icon } = mode;
    const id = 'ActionMode-' + title + '-' + icon;
    const value = (): void => { onModeChange(mode); };
    return { id, icon, label, title, value, rank: -1000 };
  };

  // Hints provider for the mode of all modes.
  const modesHints = React.useCallback((input: string) => {
    const p = input.toLowerCase();
    const fit = (m: ActionMode): boolean => m.label.toLowerCase().includes(p);
    return Promise.resolve(Array.from(allModes).filter(fit).map(modeToHint));
  }, [allModes]);

  // Build the mode of all modes. This special mode is activated when clicking
  // on the current mode icon and allows to change the current mode, displaying
  // a list of all available modes as hints.
  const modesMode = React.useMemo(() => {
    const label = "Mode selection";
    const placeholder = "Search mode";
    const icon = "TUNINGS";
    const className = 'dome-xToolBar-modeOfModes';
    return { label, placeholder, icon, className, hints: modesHints };
  }, [modesHints]);

  // Build a new search engine for the search mode, adding available modes to
  // the possible search hints.
  const searchModeHints = React.useCallback(async (input: string) => {
    const hs = await modesMode.hints(input);
    const notCurrent = (h: Hint): boolean => !(h.label.includes(current.label));
    return hs.filter(notCurrent);
  }, [current.label, modesMode]);

  // Register the new search engine.
  React.useEffect(() => {
    registerSearchHints('ModesMode', searchModeHints);
    return () => unregisterSearchHints('ModesMode');
  }, [searchModeHints]);

  // Build the component.
  const { title, placeholder } = current;
  const handleModeClick = changeMode(modesMode);
  const onBlur = (): void => reset(modesMode);
  return (
    <div className="dome-xToolBar-actionComponent" onBlur={onBlur}>
      <div className="dome-xToolBar-actionField">
        <ModeButton current={current} onClick={handleModeClick} />
        <ActionInput
          title={title}
          placeholder={placeholder}
          hints={result}
          onHint={onHint}
          onEnter={onEnter}
          index={index}
          setIndex={setIndex}
          pattern={pattern}
          setPattern={setPattern}
          inputRef={inputRef}
        />
      </div>
      <Suggestions hints={result} onHint={onHint} index={index} />
    </div>
  );
}

// --------------------------------------------------------------------------
