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

/* eslint-disable @typescript-eslint/no-explicit-any */

/**
   Dome Application (Renderer Process)

   This modules manages your main application window
   and its interaction with the main process.

   Example:

   * ```ts
   *   // File 'src/renderer/index.js':
   *   import Application from './Application.js' ;
   *   Dome.setContent( Application );
   * ```

   @packageDocumentation
   @module dome
 */

import _ from 'lodash';
import Emitter from 'events';
import React from 'react';
import ReactDOM from 'react-dom';
import { AppContainer } from 'react-hot-loader';
import { ipcRenderer } from 'electron';
import SYS, * as System from 'dome/system';
import * as Json from 'dome/data/json';
import * as Settings from 'dome/data/settings';
import './dark.css';
import './light.css';
import './style.css';
import { State } from './data/states';

// --------------------------------------------------------------------------
// --- Context
// --------------------------------------------------------------------------

// main window focus
let windowFocus = true;

function setContextAppNode(): HTMLElement | null {
  const node = document.getElementById('app');
  if (node) {
    node.className =
      `dome-container dome-platform-${System.platform
      }${windowFocus ? ' dome-window-active' : ' dome-window-inactive'}`;
  }
  return node;
}

// --------------------------------------------------------------------------
// --- Helpers
// --------------------------------------------------------------------------

/** Configured to be `'true'` when in development mode. */
export const { DEVEL } = System;

export type PlatformKind = 'linux' | 'macos' | 'windows';

/** System platform. */
export const platform: PlatformKind = (System.platform as PlatformKind);

// --------------------------------------------------------------------------
// --- User's Directories
// --------------------------------------------------------------------------

let loadedPaths = false;
const remoteAppPaths: { [index: string]: string } = {};

function getPath(k: string): string {
  if (!loadedPaths) {
    loadedPaths = true;
    Object.assign(remoteAppPaths, ipcRenderer.sendSync('dome.app.paths'));
  }
  return remoteAppPaths[k];
}

/** Returns user's home directory. */
export function getHome(): string { return getPath('home'); }

/** Returns user's desktop directory. */
export function getDesktop(): string { return getPath('desktop'); }

/** Returns user's documents directory. */
export function getDocuments(): string { return getPath('documents'); }

/** Returns user's downloads directory. */
export function getDownloads(): string { return getPath('downloads'); }

/** Returns temporary directory. */
export function getTempDir(): string { return getPath('temp'); }

/** Working directory (Application Window). */
export function getWorkingDir(): string { return System.getWorkingDir(); }

/** Current process ID.. */
export function getPID(): number { return System.getPID(); }

// --------------------------------------------------------------------------
// --- Application Emitter
// --------------------------------------------------------------------------

/** Typed Dome Event.

   To register an event with no argument, simply use `new Event('myEvent')`.
 */
export class Event<A = void> {

  private name: string;

  constructor(name: string) {
    this.name = name;
    this.emit = this.emit.bind(this);
  }

  on(callback: (arg: A) => void): void {
    System.emitter.on(this.name, callback);
  }

  off(callback: (arg: A) => void): void {
    System.emitter.off(this.name, callback);
  }

  /**
     Notify all listeners with the provided argument.
     This methods is bound to the event, so you may use `myEvent.emit`
     as a callback function, instead of eg. `(arg) => myEvent.emit(arg)`.
  */
  emit(arg: A): void {
    System.emitter.emit(this.name, arg);
  }

  /**
     Number of currenty registered listeners.
   */
  listenerCount(): number {
    return System.emitter.listenerCount(this.name);
  }

}

/** Custom React Hook on event. */
export function useEvent<A>(
  evt: undefined | null | Event<A>,
  callback: (arg: A) => void,
): void {
  React.useEffect(() => {
    if (evt) {
      evt.on(callback);
      return () => evt.off(callback);
    }
    return undefined;
  }, [evt, callback]);
}

/** Custom React Hook on Node Emitters. */
export function useEmitter(
  emitter: undefined | null | Emitter,
  event: undefined | null | string,
  callback: () => void,
): void {
  return React.useEffect((): (undefined | (() => void)) => {
    if (emitter && event) {
      emitter.on(event, callback);
      return () => emitter.off(event, callback);
    }
    return undefined;
  }, [emitter, event, callback]);
}

// --------------------------------------------------------------------------
// --- Application Events
// --------------------------------------------------------------------------

/**
   Dome update event.
   It is emitted when a general re-rendering is required, typically when
   the window frame is resized.
   You can use it for your own components as an easy-to-use global
   re-render event.
 */
export const update = new Event('dome.update');

/**
   Dome reload event.
   It is emitted when the entire window is reloaded.
 */
export const reload = new Event('dome.reload');
ipcRenderer.on('dome.ipc.reload', () => reload.emit());

/**
   Dome « Find » event. Trigered by [Cmd+F] and [Edit > Find] menu.
 */
export const find = new Event('dome.find');
ipcRenderer.on('dome.ipc.find', () => find.emit());

/** Command-line arguments event handler. */
export function onCommand(
  job: (argv: string[], workingDir: string) => void,
): void {
  System.emitter.on('dome.command', job);
}

ipcRenderer.on('dome.ipc.command', (_event, argv, wdir) => {
  SYS.setCommandLine(argv, wdir);
  System.emitter.emit('dome.command', argv, wdir);
});

/** Window Settings event.
    Emitted when window settings are reset or restored. */
export const windowSettings = new Event(Settings.window);

/** Global Settings event.
    Emiited when global settings are updated. */
export const globalSettings = new Event(Settings.global);

// --------------------------------------------------------------------------
// --- Closing
// --------------------------------------------------------------------------

ipcRenderer.on('dome.ipc.closing', System.doExit);

/** Register a callback to be executed when the window is closing. */
export function atExit(callback: () => void): void {
  System.atExit(callback);
}

// --------------------------------------------------------------------------
// --- Focus Management
// --------------------------------------------------------------------------

/** Window focus event. */
export const focus = new Event<boolean>('dome.focus');

/** Current focus state of the main window. See also [[useWindowFocus]]. */
export function isFocused(): boolean { return windowFocus; }

ipcRenderer.on('dome.ipc.focus', (_sender, value) => {
  windowFocus = value;
  setContextAppNode();
  focus.emit(value);
});

/** Return the current window focus. See [[isFocused]]. */
export function useWindowFocus(): boolean {
  useUpdate(focus);
  return windowFocus;
}

// --------------------------------------------------------------------------
// --- Web Navigation
// --------------------------------------------------------------------------

/**
   DOM href events for internal URLs.

   This event is emitted whenever some `<a href/>` DOM element
   is clicked with an internal link. External links will be automatically
   opened with the user's default Web navigator.
 */
export const navigate = new Event<string>('dome.href');

ipcRenderer.on(
  'dome.ipc.href',
  (_sender, href) => navigate.emit(href),
);

// --------------------------------------------------------------------------
// --- Window Management
// --------------------------------------------------------------------------

export function isApplicationWindow(): boolean {
  return process.argv.includes(SYS.WINDOW_APPLICATION_ARGV);
}

export function isPreferencesWindow(): boolean {
  return process.argv.includes(SYS.WINDOW_PREFERENCES_ARGV);
}

// --------------------------------------------------------------------------
// --- Window Title
// --------------------------------------------------------------------------

/** Sets the modified status of the window-frame flag.
    User feedback is platform dependent. */
export function setModified(modified = false): void {
  ipcRenderer.send('dome.ipc.window.modified', modified);
}

/** Sets the window-frame title. */
export function setTitle(title: string): void {
  ipcRenderer.send('dome.ipc.window.title', title);
}

// --------------------------------------------------------------------------
// --- Window Container
// --------------------------------------------------------------------------

function setContainer(
  Component: React.FunctionComponent | React.ComponentClass,
): void {
  Settings.synchronize();
  const appNode = setContextAppNode();
  const contents = <AppContainer><Component /></AppContainer>;
  ReactDOM.render(contents, appNode);
}

// --------------------------------------------------------------------------
// --- Main Content
// --------------------------------------------------------------------------

/**
   Defines the user's main window content.

   Binds the component to the main window.  A `<Component/>` instance is
   generated and rendered in the `#app` window element. Its class name is set to
   `dome-platform-<platform>` with the `<platform>` set to the `Dome.platform`
   value. This class name can be used as a CSS selector for platform-dependent
   styling.

   @param Component - to be rendered in the main window
*/
export function setApplicationWindow(
  Component: React.FunctionComponent | React.ComponentClass,
): void {
  if (isApplicationWindow()) setContainer(Component);
}

// --------------------------------------------------------------------------
// --- Settings Window
// --------------------------------------------------------------------------

/**
   Defines the user's preferences window content.

   A `<Component/>` instance is generated and rendered in the `#app` window
   element. Its class name is set to `dome-platform-<platform>` with the
   `<platform>` set to the `Dome.platform` value. This class name can be used as
   a CSS selector for platform-dependent styling.

   @param Component - to be rendered in the preferences window
*/
export function setPreferencesWindow(
  Component: React.FunctionComponent | React.ComponentClass,
): void {
  if (isPreferencesWindow()) setContainer(Component);
}

// --------------------------------------------------------------------------
// --- MenuBar Management
// --------------------------------------------------------------------------

type callback = () => void;
const customItemCallbacks = new Map<string, callback>();

/**
   Create a new custom menu in the menu bar.


   This function shall be called statically, although calls from _secondary_
   windows would be ignored. It is also possible to call this function from the
   main process.

   It is also possible to call this function from the main process.

   @param label - the menu title (shall be unique)
 */
export function addMenu(label: string): void {
  ipcRenderer.send('dome.ipc.menu.addmenu', label);
}

export type MenuName = 'File' | 'Edit' | 'View' | string;
export type MenuItemType = 'normal' | 'separator' | 'checkbox' | 'radio';

export interface MenuItemProps {
  /** The label of the menu to insert the item in. */
  menu: MenuName;
  /** The menu item identifier. Shall be unique in the _entire_ menu bar. */
  id: string;
  /** Default is `'normal'`. */
  type: MenuItemType;
  /** Item label. Only optional for separators. */
  label?: string;
  /** Item is visible or not (default is `true`). */
  visible?: boolean;
  /** Enabled item (default is `true`). */
  enabled?: boolean;
  /** Item status for radio and checkbox. Default is `false`. */
  checked?: boolean;
  /** Keyboard shortcut. */
  key?: string;
  /** Callback. */
  onClick?: () => void;
}

/** Inserts a new custom item in a menu.

   The menu can be modified later with [[setMenuItem]].

   When clicked, the menu-item will also trigger a `'dome.menu.clicked'(id)`
   event on all application windows.  The item callback, if any, is invoked only
   in the process that specify it.

   Key short cuts shall be specified with the following codes: - `"Cmd+<Key>"`
   for command (MacOS) or control (Linux) key - `"Alt+<Key>"` for command+option
   (MacOS) or alt (Linux) key - `"Meta+<Key>"` for command+shift (MacOS) or
   control+alt (Linux) key

   This function shall be called statically, although calls from _secondary_
   windows would be ignored. It is also possible to call this function from the
   main process.
 */
export function addMenuItem(props: MenuItemProps): void {
  if (!props.id && props.type !== 'separator') {
    // eslint-disable-next-line no-console
    console.error('[Dome] Missing menu-item identifier', props);
    return;
  }
  const { onClick, ...options } = props;
  if (onClick) customItemCallbacks.set(props.id, onClick);
  ipcRenderer.send('dome.ipc.menu.addmenuitem', options);
}

export interface MenuItemOptions {
  id: string;
  label?: string;
  visible?: boolean;
  enabled?: boolean;
  checked?: boolean;
  onClick?: null | (() => void);
}

/**
   Update properties of an existing menu-item.

   If an `onClick` callback is specified, it will _replace_ the previous one.
   You shall specify `null` to remove the previously registered callback
   (`undefined` callback is ignored).

   It is also possible to call this function from the main process.
 */
export function setMenuItem(options: MenuItemOptions): void {
  const { onClick, ...updates } = options;
  if (onClick === null) {
    customItemCallbacks.delete(options.id);
  } else if (onClick !== undefined) {
    customItemCallbacks.set(options.id, onClick);
  }
  ipcRenderer.send('dome.ipc.menu.setmenuitem', updates);
}

ipcRenderer.on('dome.ipc.menu.clicked', (_sender, id: string) => {
  const callback = customItemCallbacks.get(id);
  if (callback) callback();
});

// --------------------------------------------------------------------------
// --- Context Menus
// --------------------------------------------------------------------------

export interface PopupMenuItemProps {
  /** Item label. */
  label: string;
  /** Optional menu identifier. */
  id?: string;
  /** Displayed item, default is `true`. */
  display?: boolean;
  /** Enabled item, default is `true`. */
  enabled?: boolean;
  /** Checked item, default is `false`. */
  checked?: boolean;
  /** Item selection callback. */
  onClick?: (() => void);
}

export type PopupMenuItem = PopupMenuItemProps | 'separator';

/**
   Popup a contextual menu.

   Items can be separated by inserting a `'separator'` constant string in the
   array. Item identifier and label default to each others. Alternatively, an
   item can be specified by a single string that will be used for both its label
   and identifier. Undefined or null items are allowed (and skipped).

   The menu is displayed at the current mouse location.  The callback is called
   with the selected item identifier or label.  If the menu popup is canceled by
   the user, the callback is called with `undefined`.

   Example:

   * ```ts
   *    let myPopup = (_evt) => Dome.popupMenu([ …items… ],(id) => … );
   *    <div onRightClick={myPopup}>...</div>
   * ```

*/
export function popupMenu(
  items: PopupMenuItem[],
  callback?: (item: string | undefined) => void,
): void {
  const ipcItems = items.map((item) => {
    if (!item) return undefined;
    if (item === 'separator') return item;
    return {
      label: item.label,
      id: item.id,
      display: !!(item.display ?? true),
      enabled: !!(item.enabled ?? true),
      checked: !!(item.checked ?? false),
    };
  });
  ipcRenderer.invoke('dome.popup', ipcItems).then((index: number) => {
    const item = items[index];
    if (item && item !== 'separator') {
      const { id, label, onClick } = item;
      if (onClick) onClick();
      if (callback) callback(id || label);
    } else {
      if (callback) callback(undefined);
    }
  });
}

// --------------------------------------------------------------------------
// --- React Hooks
// --------------------------------------------------------------------------

/**
   Hook to re-render on demand (Custom React Hook).
   Returns a callback to trigger a render on demand.
*/
export function useForceUpdate(): () => void {
  const [tac, onTic] = React.useState(false);
  return () => onTic(!tac);
}

/**
   Hook to re-render on Dome events (Custom React Hook).
   @param events - event names, defaults to a single `'dome.update'`.
*/
export function useUpdate(...events: Event<any>[]): void {
  const fn = useForceUpdate();
  React.useEffect(() => {
    const theEvents = events ? events.slice() : [update];
    theEvents.forEach((evt) => evt.on(fn));
    return () => theEvents.forEach((evt) => evt.off(fn));
  });
}

interface PromiseHook<A> {
  result: A | undefined;
  error: Error | undefined;
  loading: boolean;
}

/**
   Hook to re-render when a Promise returns.
   The promise will be typically created by using `React.useMemo()`.
   The hook returns three informations:
   - result: the promise result if it succeeds, undefined otherwise;
   - error: the promise error if it fails, undefined otherwise;
   - loading: the promise status, true if the promise is still running.
*/
export function usePromise<A>(job: Promise<A>): PromiseHook<A> {
  const [result, setResult] = React.useState<A | undefined>();
  const [error, setError] = React.useState<Error | undefined>();
  const [loading, setLoading] = React.useState(true);
  React.useEffect(() => {
    let cancel = false;
    const doCancel = (): boolean => {
      if (!cancel) setLoading(false);
      return cancel;
    };
    const onResult = (x: A): void => { if (!doCancel()) setResult(x); };
    const onError = (e: Error): void => { if (!doCancel()) setError(e); };
    job.then(onResult, onError);
    return () => { cancel = true; };
  }, [job]);
  return { result, error, loading };
}

/* Internal type alias */
type Serialize<A> = (a: A) => string;

/**
   Hook to add a cache system to a function, allowing to reuse previous results.
   As the equality used in JS maps does not allow to effectively implement a
   cache for complex type, a serialization function can be procured.
   The hook returns the cached version of the function.
*/
export function useCache<K, V>(r: (k: K) => V, s?: Serialize<K>): (k: K) => V {
  const { current: cache } = React.useRef(new Map<string, V>());
  const serialize = React.useMemo(() => s ? s : (k: K) => `${k}`, [s]);
  const get = React.useCallback((k: K): V => {
    const id = serialize(k);
    if (cache.has(id))
      return cache.get(id) as V;
    const v = r(k);
    cache.set(id, v);
    return v;
  }, [cache, r, serialize]);
  return get;
}

// --------------------------------------------------------------------------
// --- Timer Hooks
// --------------------------------------------------------------------------

interface Clock {
  timer?: NodeJS.Timeout;
  pending: number; // Number of listeners
  time: number; // Ellapsed time since firts pending
  event: string; // Tic events
  period: number; // Period
}

// Collection of clocks indexed by period
const CLOCKS = new Map<number, Clock>();

const CLOCKEVENT = (period: number): string => `dome.clock.${period}`;

const TIC_CLOCK = (clk: Clock) => (): void => {
  if (0 < clk.pending) {
    clk.time += clk.period;
    System.emitter.emit(clk.event, clk.time);
  } else {
    if (clk.timer) clearInterval(clk.timer);
    CLOCKS.delete(clk.period);
  }
};

const INC_CLOCK = (period: number): string => {
  let clk = CLOCKS.get(period);
  if (!clk) {
    const event = CLOCKEVENT(period);
    const time = (new Date()).getTime();
    clk = { pending: 0, time, period, event };
    clk.timer = setInterval(TIC_CLOCK(clk), period);
    CLOCKS.set(period, clk);
  }
  clk.pending++;
  return clk.event;
};

const DEC_CLOCK = (period: number): void => {
  const clk = CLOCKS.get(period);
  if (clk) clk.pending--;
};

export interface Timer {
  /** Starts the timer, if not yet. */
  start(): void;
  /** Stops the timer. Can be restarted after. */
  stop(): void;
  /** Elapsed time (in milliseconds). */
  time: number;
  /** Running timer. */
  running: boolean;
}

/**
   Synchronized start & stop timer (Custom React Hook).

   Create a local timer, synchronized on a global clock, that can be started
   and stopped on demand during the life cycle of the component.

   Each timer has its individual start & stop state. However,
   all timers with the same period _are_ synchronized with each others.

   @param period - timer interval, in milliseconds (ms)
   @param initStart - whether to initially start the timer (default is `false`)

 */
export function useClock(period: number, initStart: boolean): Timer {
  const started = React.useRef(0);
  const [time, setTime] = React.useState(0);
  const [running, setRunning] = React.useState(initStart);
  const start = React.useCallback(() => setRunning(false), []);
  const stop = React.useCallback(() => {
    setRunning(false);
    setTime(0);
    started.current = 0;
  }, []);
  React.useEffect(() => {
    if (running) {
      const event = INC_CLOCK(period);
      const callback = (t: number): void => {
        if (!started.current) started.current = t;
        else setTime(t - started.current);
      };
      System.emitter.on(event, callback);
      return () => {
        System.emitter.off(event, callback);
        DEC_CLOCK(period);
      };
    } return undefined;
  }, [period, running]);
  return { time, running, start, stop };
}

// --------------------------------------------------------------------------
// --- Settings Hookds
// --------------------------------------------------------------------------

/**
   Bool window settings helper. Default is `false` unless specified.
*/
export function useBoolSettings(
  key: string | undefined,
  defaultValue = false,
): State<boolean> {
  return Settings.useWindowSettings(
    key, Json.jBoolean, defaultValue,
  );
}

/**
   Bool window settings helper with a flip callback.
 */
export function useFlipSettings(
  key: string | undefined,
  defaultValue = false,
): [boolean, () => void] {
  const [state, setState] = Settings.useWindowSettings(
    key, Json.jBoolean, defaultValue,
  );
  return [state, () => setState(!state)];
}

/** Number window settings helper. Default is `0` unless specified. */
export function useNumberSettings(
  key: string | undefined,
  defaultValue = 0,
): State<number> {
  return Settings.useWindowSettings(
    key, Json.jNumber, defaultValue,
  );
}

/** String window settings. Default is `''` unless specified). */
export function useStringSettings(
  key: string | undefined,
  defaultValue = ''
): State<string> {
  return Settings.useWindowSettings(
    key, Json.jString, defaultValue,
  );
}

/** Optional string window settings. Default is `undefined`. */
export function useStringOptSettings(
  key: string | undefined
): State<string | undefined> {
  return Settings.useWindowSettings(
    key, Json.jString, undefined,
  );
}

/** Direct shortcut to [[dome/data/settings.useWindowSettings]]. */
export const { useWindowSettings } = Settings;

/**
   Utility shortcut to [[dome/data/settings.useGlobalSettings]]
   with global settings class created on-the-fly.
 */
export function useGlobalSettings<A extends Json.json>(
  globalKey: string,
  decoder: Json.Loose<A>,
  defaultValue: A,
): State<A> {
  // Object creation is cheaper than useMemo...
  const G = new Settings.GlobalSettings(
    globalKey, decoder, Json.identity, defaultValue,
  );
  return Settings.useGlobalSettings(G);
}

// --------------------------------------------------------------------------
// --- Pretty Printing (Browser Console)
// --------------------------------------------------------------------------

export class Debug {
  moduleName: string;
  constructor(moduleName: string) {
    this.moduleName = moduleName;
  }

  /* eslint-disable no-console */

  log(...args: any): void {
    if (DEVEL) console.log(`[${this.moduleName}]`, ...args);
  }

  warn(...args: any): void {
    if (DEVEL) console.warn(`[${this.moduleName}]`, ...args);
  }

  error(...args: any): void {
    if (DEVEL) console.error(`[${this.moduleName}]`, ...args);
  }

  /* eslint-enable no-console */
}

// --------------------------------------------------------------------------
