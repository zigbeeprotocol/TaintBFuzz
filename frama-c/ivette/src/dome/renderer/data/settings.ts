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
// --- States
// --------------------------------------------------------------------------

/**
   Typed States & Settings
   @packageDocumentation
   @module dome/data/settings
*/

import React from 'react';
import { ipcRenderer } from 'electron';
import { debounce } from 'lodash';
import isEqual from 'react-fast-compare';
import { emitter as SysEmitter } from 'dome/misc/system';
import * as JSON from './json';
import type { State } from './states';

// --------------------------------------------------------------------------
// --- Settings
// --------------------------------------------------------------------------

/** @internal */
interface Settings<A> {
  decoder: JSON.Loose<A>;
  encoder: JSON.Encoder<A>;
  defaultValue: A;
}

/**
   Global settings.
   This utility class allows you to share accross several
   components and windows the parameters associated to global settings.

   However, it is important to note that global settings are uniquely identified
   by their `name`. If you have multiple definitions of global settings class
   with the same name, they will actually share the same value. Hence, if they
   have different default values or decoders, this might leads to strange
   results.
 */
export class GlobalSettings<A> {
  name: string;
  decoder: JSON.Loose<A>;
  encoder: JSON.Encoder<A>;
  defaultValue: A;
  constructor(
    name: string,
    decoder: JSON.Loose<A>,
    encoder: JSON.Encoder<A>,
    defaultValue: A,
  ) {
    this.name = name;
    this.decoder = decoder;
    this.encoder = encoder;
    this.defaultValue = defaultValue;
  }
}

// --------------------------------------------------------------------------
// --- Smart Constructors
// --------------------------------------------------------------------------

/** Boolean settings with `true` default. */
export class GTrue extends GlobalSettings<boolean> {
  constructor(name: string) {
    super(name, JSON.jBoolean, JSON.identity, true);
  }
}

/** Boolean settings with `false` default. */
export class GFalse extends GlobalSettings<boolean> {
  constructor(name: string) {
    super(name, JSON.jBoolean, JSON.identity, false);
  }
}

/** Numeric settings (default is zero unless specified). */
export class GNumber extends GlobalSettings<number> {
  constructor(name: string, defaultValue = 0) {
    super(name, JSON.jNumber, JSON.identity, defaultValue);
  }
}

/** String settings (default is `""` unless specified). */
export class GString extends GlobalSettings<string> {
  constructor(name: string, defaultValue = '') {
    super(name, JSON.jString, JSON.identity, defaultValue);
  }
}

/** Smart constructor for optional (JSON serializable) data. */
export class GOption<A extends JSON.json>
  extends GlobalSettings<A | undefined>
{
  constructor(name: string, encoder: JSON.Loose<A>, defaultValue?: A) {
    super(name, encoder, JSON.identity, defaultValue);
  }
}

/** Smart constructor for (JSON serializable) data with default. */
export class GDefault<A extends JSON.json> extends GlobalSettings<A> {
  constructor(name: string, encoder: JSON.Loose<A>, defaultValue: A) {
    super(name, encoder, JSON.identity, defaultValue);
  }
}

/** Smart constructor for object (JSON serializable) data. */
export class GObject<A extends JSON.json> extends GlobalSettings<A> {
  constructor(name: string, fields: JSON.Props<A>, defaultValue: A) {
    super(name, JSON.jObject(fields), JSON.identity, defaultValue);
  }
}

// --------------------------------------------------------------------------
// --- Generic Settings (private)
// --------------------------------------------------------------------------

type store = { [key: string]: JSON.json };
type patch = { key: string; value: JSON.json };
type driver = {
  evt: string;
  ipc: string;
  globals: boolean; // Global Settings (all windows share the same)
  defaults: boolean; // Restore defaults on demand
};

class Driver {

  readonly evt: string; // Global Update Event
  readonly store: Map<string, JSON.json> = new Map();
  readonly diffs: Map<string, JSON.json> = new Map();
  readonly commit: (() => void) & { flush: () => void; cancel: () => void };

  constructor({ evt, ipc, defaults, globals }: driver) {
    this.evt = evt;
    // --- Update Events
    this.commit = debounce(() => {
      const m = this.diffs;
      if (m.size > 0) {
        const patches: patch[] = [];
        m.forEach((value, key) => {
          patches.push({ key, value });
        });
        m.clear();
        ipcRenderer.send(ipc, patches);
      }
    }, 100);
    // --- Restore Defaults Events
    if (defaults) {
      ipcRenderer.on('dome.ipc.settings.defaults', () => {
        this.commit.cancel();
        this.store.clear();
        this.diffs.clear();
        SysEmitter.emit(this.evt);
      });
    }
    // --- Broadcast Events
    if (globals) {
      ipcRenderer.on(
        'dome.ipc.settings.broadcast',
        (_sender, updates: patch[]) => {
          const m = this.store;
          const d = this.diffs;
          updates.forEach(({ key, value }) => {
            // Don't cancel local updates
            if (!d.has(key)) {
              if (value === null)
                m.delete(key);
              else
                m.set(key, value);
            }
          });
          SysEmitter.emit(this.evt);
        },
      );
    }
    // --- Closing Events
    ipcRenderer.on('dome.ipc.closing', () => {
      this.commit();
      this.commit.flush();
    });
  }

  // --- Initial Data

  sync(data: store): void {
    this.commit.cancel();
    this.store.clear();
    this.diffs.clear();
    const m = this.store;
    Object.keys(data).forEach((k) => { m.set(k, data[k]); });
    SysEmitter.emit(this.evt);
  }

  // --- Load Data

  load(key: string | undefined): JSON.json {
    return key === undefined ? undefined : this.store.get(key);
  }

  // --- Save Data

  save(key: string | undefined, data: JSON.json): void {
    if (key === undefined) return;
    if (data === undefined) {
      this.store.delete(key);
      this.diffs.set(key, null);
    } else {
      this.store.set(key, data);
      this.diffs.set(key, data);
    }
    SysEmitter.emit(this.evt);
    this.commit();
  }

}

// --------------------------------------------------------------------------
// --- Generic Settings Hook
// --------------------------------------------------------------------------

function useSettings<A>(
  S: Settings<A>,
  D: Driver,
  K?: string,
): State<A> {
  // Local State
  const [value, setValue] = React.useState<A>(() => (
    JSON.jCatch(S.decoder, S.defaultValue)(D.load(K))
  ));
  // Foreign Settings Update
  React.useEffect(() => {
    const event = D.evt;
    const onUpdate = (): void => {
      const fromSettings = JSON.jCatch(S.decoder, undefined)(D.load(K));
      if (fromSettings !== undefined)
        setValue(fromSettings);
    };
    SysEmitter.on(event, onUpdate);
    return () => { SysEmitter.off(event, onUpdate); };
  });
  // Hooked Settings Update
  const updateValue = React.useCallback((newValue: A) => {
    if (!isEqual(value, newValue)) {
      setValue(newValue);
      if (K) D.save(K, S.encoder(newValue));
    }
  }, [S, D, K, value]);
  // Hook
  return [value, updateValue];
}

// --------------------------------------------------------------------------
// --- Window Settings
// --------------------------------------------------------------------------

const WindowSettingsDriver = new Driver({
  evt: 'dome.settings.window',
  ipc: 'dome.ipc.settings.window',
  globals: false,
  defaults: true,
});

/**
   Returns the current value of the settings (default for undefined key).
 */
export function getWindowSettings<A>(
  key: string | undefined,
  decoder: JSON.Loose<A>,
  defaultValue: A,
): A {
  return key ?
    JSON.jCatch(decoder, defaultValue)(WindowSettingsDriver.load(key))
    : defaultValue;
}

/**
   Updates the current value of the settings (on defined key).
   Most settings are subtypes of `JSON` and do not require any specific
   encoder. If you have some, simply use it before updating the settings.
   See [[useWindowSettings]] and [[useWindowSettingsData]].
 */
export function setWindowSettings(
  key: string | undefined,
  value: JSON.json,
): void {
  if (key) WindowSettingsDriver.save(key, value);
}

/**
   Returns a local state that is saved back to the local window user settings.
   Local window settings are stored in the `.<appName>` file of the working
   directory, or in the closest one in parent directories, if any.
 */
export function useWindowSettings<A>(
  key: string | undefined,
  decoder: JSON.Loose<A & JSON.json>,
  defaultValue: A & JSON.json,
): State<A & JSON.json> {
  return useSettings({
    decoder,
    encoder: JSON.identity,
    defaultValue,
  }, WindowSettingsDriver, key);
}

/** Same as [[useWindowSettings]] with a specific encoder. */
export function useWindowSettingsData<A>(
  key: string | undefined,
  decoder: JSON.Loose<A>,
  encoder: JSON.Encoder<A>,
  defaultValue: A,
): State<A> {
  return useSettings({
    decoder,
    encoder,
    defaultValue,
  }, WindowSettingsDriver, key);
}

/** Call the callback function on window settings events. */
export function useWindowSettingsEvent(callback: () => void): void {
  React.useEffect(() => {
    const { evt } = WindowSettingsDriver;
    SysEmitter.on(evt, callback);
    return () => { SysEmitter.off(evt, callback); };
  });
}

/** @ignore DEPRECATED */
export function onWindowSettings(callback: () => void): void {
  const { evt } = WindowSettingsDriver;
  SysEmitter.on(evt, callback);
}

/** @ignore DEPRECATED */
export function offWindowSettings(callback: () => void): void {
  const { evt } = WindowSettingsDriver;
  SysEmitter.off(evt, callback);
}

// --------------------------------------------------------------------------
// --- Local Storage
// --------------------------------------------------------------------------

const LocalStorageDriver = new Driver({
  evt: 'dome.settings.storage',
  ipc: 'dome.ipc.settings.storage',
  globals: false,
  defaults: false,
});

/**
   Returns the current value of the settings (default for undefined key).
 */
export function getLocalStorage<A>(
  key: string | undefined,
  decoder: JSON.Loose<A>,
  defaultValue: A,
): A {
  return key ?
    JSON.jCatch(decoder, defaultValue)(LocalStorageDriver.load(key))
    : defaultValue;
}

/**
   Updates the current value of the settings (on defined key).
   Most settings are subtypes of `JSON` and do not require any specific
   encoder. If you have some, simply use it before updating the settings.
   See [[useLocalStorage]] and [[useWindowSettingsData]].
 */
export function setLocalStorage(
  key: string | undefined,
  value: JSON.json,
): void {
  if (key) LocalStorageDriver.save(key, value);
}

export function useLocalStorage<A>(
  key: string | undefined,
  decoder: JSON.Loose<A & JSON.json>,
  defaultValue: A & JSON.json,
): State<A & JSON.json> {
  return useSettings<A & JSON.json>({
    decoder,
    encoder: JSON.identity,
    defaultValue,
  }, LocalStorageDriver, key);
}

/** Same as [[useLocalStorage]] with a specific encoder. */
export function useLocalStorageData<A>(
  key: string | undefined,
  decoder: JSON.Loose<A>,
  encoder: JSON.Encoder<A>,
  defaultValue: A,
): State<A> {
  return useSettings({
    decoder,
    encoder,
    defaultValue,
  }, LocalStorageDriver, key);
}

/** Call the callback function on window settings events. */
export function useLocalStorageEvent(callback: () => void): void {
  React.useEffect(() => {
    const { evt } = LocalStorageDriver;
    SysEmitter.on(evt, callback);
    return () => { SysEmitter.off(evt, callback); };
  });
}

// --------------------------------------------------------------------------
// --- Global Settings
// --------------------------------------------------------------------------

const GlobalSettingsDriver = new Driver({
  evt: 'dome.settings.global',
  ipc: 'dome.ipc.settings.global',
  globals: true,
  defaults: true,
});

/**
   Returns a global state, which is synchronized among all windows, and saved
   back in the global user settings. The global user settings file is located in
   the usual place for the application with respect to the underlying system.
 */
export function useGlobalSettings<A>(S: GlobalSettings<A>): State<A> {
  return useSettings(S, GlobalSettingsDriver, S.name);
}

/** Call the callback function on global settings events. */
export function useGlobalSettingsEvent(callback: () => void): void {
  React.useEffect(() => {
    const { evt } = GlobalSettingsDriver;
    SysEmitter.on(evt, callback);
    return () => { SysEmitter.off(evt, callback); };
  });
}

// --------------------------------------------------------------------------
// --- Settings Synchronization
// --------------------------------------------------------------------------

/* @ internal */
export const window = WindowSettingsDriver.evt;

/* @ internal */
export const global = GlobalSettingsDriver.evt;

/* @ internal */
export function synchronize(): void {
  const data = ipcRenderer.sendSync('dome.ipc.settings.sync');
  const storage: store = data.storage ?? {};
  const globals: store = data.globals ?? {};
  const settings: store = data.settings ?? {};
  LocalStorageDriver.sync(storage);
  GlobalSettingsDriver.sync(globals);
  WindowSettingsDriver.sync(settings);
}

// --------------------------------------------------------------------------
