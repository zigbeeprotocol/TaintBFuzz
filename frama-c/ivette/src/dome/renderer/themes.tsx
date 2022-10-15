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
// --- Global Color Theme Management
// --------------------------------------------------------------------------

/**
   @packageDocumentation
   @module dome/themes
 */

//import React from 'react';
import * as Dome from 'dome';
import * as Settings from 'dome/data/settings';
import { State } from 'dome/data/states';
import { ipcRenderer } from 'electron';

/* -------------------------------------------------------------------------- */
/* --- Global Settings                                                    --- */
/* -------------------------------------------------------------------------- */

export type ColorTheme = 'dark' | 'light';
export type ColorSettings = 'dark' | 'light' | 'system';

export const jColorTheme =
  (th: string | undefined): ColorTheme => (th === 'dark' ? 'dark' : 'light');
export const jColorSettings =
  (th: string | undefined): ColorSettings => {
    switch (th) {
      case 'light':
      case 'dark':
      case 'system':
        return th;
      default:
        return 'system';
    }
  };

const ColorThemeSettings = new Settings.GString('dome-color-theme', 'system');
const NativeThemeUpdated = new Dome.Event('dome.theme.updated');
ipcRenderer.on('dome.theme.updated', () => NativeThemeUpdated.emit());

async function getNativeTheme(): Promise<ColorTheme> {
  const th = await ipcRenderer.invoke('dome.ipc.theme');
  return jColorTheme(th);
}

/* -------------------------------------------------------------------------- */
/* --- Color Theme Hooks                                                  --- */
/* -------------------------------------------------------------------------- */

export function useColorTheme(): [ColorTheme, (upd: ColorSettings) => void] {
  Dome.useUpdate(NativeThemeUpdated);
  const { result: current } = Dome.usePromise(getNativeTheme());
  const [pref, setTheme] = Settings.useGlobalSettings(ColorThemeSettings);
  return [current ?? jColorTheme(pref), setTheme];
}

export function useColorThemeSettings(): State<ColorSettings> {
  const [pref, setTheme] = Settings.useGlobalSettings(ColorThemeSettings);
  return [jColorSettings(pref), setTheme];
}

/* -------------------------------------------------------------------------- */
