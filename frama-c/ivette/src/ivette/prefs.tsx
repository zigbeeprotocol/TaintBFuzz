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
// --- Main React Component rendered by './index.js'
// --------------------------------------------------------------------------

/**
   @packageDocumentation
   @module ivette/prefs
 */

import React from 'react';
import * as Dome from 'dome';
import * as Themes from 'dome/themes';
import * as Toolbar from 'dome/frame/toolbars';
import * as Settings from 'dome/data/settings';
import 'codemirror/mode/clike/clike';

/* -------------------------------------------------------------------------- */
/* --- Theme Switcher Button                                              --- */
/* -------------------------------------------------------------------------- */

export function ThemeSwitchTool(): JSX.Element {
  const [theme, setTheme] = Themes.useColorTheme();
  const other = theme === 'dark' ? 'light' : 'dark';
  const position = theme === 'dark' ? 'left' : 'right';
  const title = `Switch to ${other} theme`;
  const onChange = (): void => setTheme(other);
  return (
    <Toolbar.Switch
      disabled={!Dome.DEVEL}
      title={title}
      position={position}
      onChange={onChange}
    />
  );
}

/* -------------------------------------------------------------------------- */
/* --- Font Size Buttons Group                                            --- */
/* -------------------------------------------------------------------------- */

export function FontTools(): JSX.Element {
  const [fontSize, setFontSize] = Settings.useGlobalSettings(EditorFontSize);
  const zoomIn = (): void => setFontSize(fontSize + 2);
  const zoomOut = (): void => setFontSize(fontSize - 2);
  return (
    <Toolbar.ButtonGroup>
      <Toolbar.Button
        icon="ZOOM.OUT"
        onClick={zoomOut}
        enabled={fontSize > 4}
        title="Decrease font size"
      />
      <Toolbar.Button
        icon="ZOOM.IN"
        onClick={zoomIn}
        enabled={fontSize < 48}
        title="Increase font size"
      />
    </Toolbar.ButtonGroup>
  );
}

// --------------------------------------------------------------------------
// --- AST View Preferences
// --------------------------------------------------------------------------

export const EditorFontSize =
  new Settings.GNumber('Editor.fontSize', 12);

export const EditorCommand =
  new Settings.GString('Editor.Command', 'emacs +%n:%c %s');

// --------------------------------------------------------------------------
// --- Console Scrollback configuration
// --------------------------------------------------------------------------

export const ConsoleScrollback =
  new Settings.GNumber('Console.Scrollback', 2000);

export interface ConsoleScrollbackProps {
  scrollback: Settings.GlobalSettings<number>;
}

// --------------------------------------------------------------------------
