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

/**
   Various kind of (modal) dialogs attached to the main application window.
   @packageDocumentation
   @module dome/dialogs
 */

import filepath from 'path';
import { ipcRenderer } from 'electron';
import * as System from 'dome/system';

// --------------------------------------------------------------------------
// --- Message Box
// --------------------------------------------------------------------------

export interface DialogButton<A> {
  label?: string;
  value?: A;
}

const defaultItems: DialogButton<boolean>[] = [
  { value: undefined },
  { value: true, label: 'Ok' },
];

const valueLabel = (v: unknown): string => {
  switch (v) {
    case undefined: return 'Cancel';
    case true: return 'Ok';
    case false: return 'No';
    default: return `${v}`;
  }
};

const itemLabel = ({ value, label }: DialogButton<unknown>): string => (
  (label || valueLabel(value))
);

const isDefault = ({ value, label }: DialogButton<unknown>): boolean => (
  (value === true || label === 'Ok' || label === 'Yes')
);

const isCancel = ({ value, label }: DialogButton<unknown>): boolean => (
  (!value || label === 'Cancel' || label === 'No')
);

export type MessageKind = 'none' | 'info' | 'error' | 'warning';

export interface MessageProps<A> {
  /** Dialog window icon (default is `'none'`. */
  kind?: MessageKind;
  /** Message text (short sentence). */
  message: string;
  /** Message details (short sentence). */
  details?: string;
  /** Message buttons. */
  buttons?: DialogButton<A>[];
  /** Default button's value. */
  defaultValue?: A;
  /** Cancel value. */
  cancelValue?: A;
}

/**
   Show a configurable message box.

   The returned promise object is never rejected, and is asynchronously
   resolved into:
   - the cancel value if the cancel key is pressed,
   - the default value if the enter key is pressed,
   - or the value of the clicked button otherwised.

   The default buttons are `"Ok"` and `"Cancel"` associated to values `true` and
   `undefined`, which are also associated to the enter and cancel keys.
   Unless specified, the default value is associated with the first button
   with 'true' value or 'Ok' or 'Yes' label,
   and the cancel value is the first button with a falsy value or 'Cancel'
   or 'No' label.
 */
export async function showMessageBox<A>(
  props: MessageProps<A>,
): Promise<A | boolean | undefined> {
  const {
    kind,
    message,
    details,
    defaultValue,
    cancelValue,
    buttons = (defaultItems as DialogButton<A | boolean>[]),
  } = props;

  const labels = buttons.map(itemLabel);
  const defaultId =
    defaultValue === undefined
      ? buttons.findIndex(isDefault)
      : buttons.findIndex((a) => a.value === defaultValue);
  let cancelId =
    cancelValue === undefined
      ? buttons.findIndex(isCancel)
      : buttons.findIndex((a) => a.value === cancelValue);

  if (cancelId === defaultId) cancelId = -1;

  return ipcRenderer.invoke('dome.dialog.showMessageBox',
    {
      'type': kind,
      message,
      detail: details,
      defaultId,
      cancelId,
      buttons: labels,
    },
  ).then((result) => {
    const itemIndex = result ? result.response : -1;
    return itemIndex ? buttons[itemIndex].value : cancelValue;
  });
}

// --------------------------------------------------------------------------
// --- File Dialogs
// --------------------------------------------------------------------------

const defaultPath =
  (path: string): string =>
    (filepath.extname(path) ? filepath.dirname(path) : path);

export interface FileFilter {
  /** Filter name. */
  name: string;
  /**
     Allowed extensions, _without_ dot.
     Use `['*']` to accept all files.
   */
  extensions: string[];
}

export interface FileDialogProps {
  /** Prompt message. */
  title?: string;
  /** Open button label (default is « Open »). */
  label?: string;
  /** Initially selected path. */
  path?: string;
}

export interface SaveFileProps extends FileDialogProps {
  /** File filters (default to all). */
  filters?: FileFilter[];
}

export interface OpenFileProps extends SaveFileProps {
  /** Show hidden files (default is `false`). */
  hidden?: boolean;
}

export interface OpenDirProps extends FileDialogProps {
  /** Show hidden directories (default is `false`). */
  hidden?: boolean;
}

// --------------------------------------------------------------------------
// --- openFile dialog
// --------------------------------------------------------------------------

/**
   Show a dialog for opening file.
   A file filter with `extensions:["*"]` would accept any file extension.

   The returned promise object will be asynchronously:
   - either _resolved_ with `undefined` if no file has been selected,
   - or _resolved_ with the selected path

   The promise is never rejected.
 */
export async function showOpenFile(
  props: OpenFileProps,
): Promise<string | undefined> {
  const { title, label, path, hidden = false, filters } = props;
  return ipcRenderer.invoke('dome.dialog.showOpenDialog',
    {
      title,
      buttonLabel: label,
      defaultPath: path && defaultPath(path),
      properties: (hidden ? ['openFile', 'showHiddenFiles'] : ['openFile']),
      filters,
    },
  ).then((result) => {
    if (!result.canceled && result.filePaths && result.filePaths.length > 0)
      return result.filePaths[0];
    return undefined;
  });
}

/**
   Show a dialog for opening files multiple files.
*/
export async function showOpenFiles(
  props: OpenFileProps,
): Promise<string[] | undefined> {
  const { title, label, path, hidden, filters } = props;

  return ipcRenderer.invoke('dome.dialog.showOpenDialog',
    {
      title,
      buttonLabel: label,
      defaultPath: path && defaultPath(path),
      properties: (
        hidden
          ? ['openFile', 'multiSelections', 'showHiddenFiles']
          : ['openFile', 'multiSelections']
      ),
      filters,
    },
  ).then((result) => {
    if (!result.canceled && result.filePaths && result.filePaths.length > 0)
      return result.filePaths;
    return undefined;
  });
}

// --------------------------------------------------------------------------
// --- saveFile dialog
// --------------------------------------------------------------------------

/**
   Show a dialog for saving file.

   The returned promise object will be asynchronously:
   - either _resolved_ with `undefined` when canceled,
   - or _resolved_ with the selected (single) path.

   The promise is never rejected.
*/
export async function showSaveFile(
  props: SaveFileProps,
): Promise<string | undefined> {
  const { title, label, path, filters } = props;
  return ipcRenderer.invoke('dome.dialog.showSaveDialog',
    {
      title,
      buttonLabel: label,
      defaultPath: path,
      filters,
    },
  ).then(({ canceled, filePath }) => (canceled ? undefined : filePath));
}

// --------------------------------------------------------------------------
// --- openDir dialog
// --------------------------------------------------------------------------

type openDirProperty =
  'openDirectory' | 'showHiddenFiles' | 'createDirectory' | 'promptToCreate';

/**
   Show a dialog for selecting directories.
 */
export async function showOpenDir(
  props: OpenDirProps,
): Promise<string | undefined> {
  const { title, label, path, hidden } = props;
  const properties: openDirProperty[] = ['openDirectory'];
  if (hidden) properties.push('showHiddenFiles');

  switch (System.platform) {
    case 'macos': properties.push('createDirectory'); break;
    case 'windows': properties.push('promptToCreate'); break;
    default: break;
  }

  return ipcRenderer.invoke('dome.dialog.showOpenDialog',
    {
      title,
      buttonLabel: label,
      defaultPath: path,
      properties,
    },
  ).then((result) => {
    if (!result.canceled && result.filePaths && result.filePaths.length > 0)
      return result.filePaths[0];
    return undefined;
  });
}

// --------------------------------------------------------------------------
