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

/* --------------------------------------------------------------------------*/
/* --- Frama-C MENU                                                       ---*/
/* --------------------------------------------------------------------------*/

import * as Dome from 'dome';
import * as Dialogs from 'dome/dialogs';
import * as Server from 'frama-c/server';
import * as Services from 'frama-c/kernel/api/services';
import * as Ast from 'frama-c/kernel/api/ast';
import * as Status from 'frama-c/kernel/Status';
import * as States from 'frama-c/states';
import { ipcRenderer } from 'electron';

const cFilter = {
  name: 'C source files',
  extensions: ['c', 'i', 'h'],
};
const allFilter = {
  name: 'all',
  extensions: ['*'],
};

async function parseFiles(files: string[]): Promise<void> {
  Status.setMessage({ text: 'Parsing source files…', kind: 'progress' });
  await Server.send(Ast.setFiles, files);
  await Server.send(Ast.compute, {});
  Status.setMessage({ text: 'Source files parsed.', kind: 'success' });
  return;
}

async function setFiles(): Promise<void> {
  const files = await Dialogs.showOpenFiles({
    title: 'Select C source files',
    filters: [cFilter, allFilter],
  });
  if (files) {
    await parseFiles(files);
    States.resetSelection();
  }
  return;
}

async function addFiles(): Promise<void> {
  const dialog = Dialogs.showOpenFiles({
    title: 'Add C source files',
    filters: [cFilter, allFilter],
  });
  const request = Server.send(Ast.getFiles, {});
  const [oldFiles, newFiles] = await Promise.all([request, dialog]);
  if (newFiles) {
    const files = oldFiles ? oldFiles.concat(newFiles) : newFiles;
    parseFiles(files);
  }
  return;
}

async function reparseFiles(): Promise<void> {
  Status.setMessage({ text: 'Parsing source files…', kind: 'progress' });
  const files = await Server.send(Ast.getFiles, {});
  if (files) {
    await Server.send(Ast.setFiles, []);
    parseFiles(files);
  }
  return;
}

async function loadSession(): Promise<void> {
  const file = await Dialogs.showOpenFile({ title: 'Load a saved session' });
  Status.setMessage({ text: 'Loading session…', kind: 'progress' });
  const error = await Server.send(Services.load, file);
  States.resetSelection();
  if (error) {
    Status.setMessage({
      text: 'Error when loading the session',
      title: error,
      kind: 'error',
    });
    await Dialogs.showMessageBox({
      message: 'An error has occurred when loading the file',
      details: `File: ${file}\nError: ${error}`,
      kind: 'error',
      buttons: [{ label: 'Cancel' }],
    });
  }
  else
    Status.setMessage({
      text: 'Session successfully loaded.',
      kind: 'success',
    });
  return;
}

async function saveSession(): Promise<void> {
  const title = 'Save the current session';
  const file = await Dialogs.showSaveFile({ title });
  Status.setMessage({ text: 'Saving session…', kind: 'progress' });
  const error = await Server.send(Services.save, file);
  if (error) {
    Status.setMessage({
      text: 'Error when saving the session',
      title: error,
      kind: 'error',
    });
    await Dialogs.showMessageBox({
      message: 'An error has occurred when saving the session',
      kind: 'error',
      buttons: [{ label: 'Cancel' }],
    });
  }
  else
    Status.setMessage({ text: 'Session successfully saved.', kind: 'success' });
  return;
}

export function init(): void {
  ipcRenderer.invoke('dome.ipc.updateLearnMore', 'https://frama-c.com/');
  Dome.addMenuItem({
    menu: 'File',
    label: 'Set source files…',
    id: 'file_set',
    onClick: setFiles,
    type: 'normal',
  });
  Dome.addMenuItem({
    menu: 'File',
    label: 'Add source files…',
    id: 'file_add',
    onClick: addFiles,
    type: 'normal',
  });
  Dome.addMenuItem({
    menu: 'File',
    label: 'Reparse',
    id: 'file_reparse',
    onClick: reparseFiles,
    type: 'normal',
  });
  Dome.addMenuItem({
    menu: 'File',
    id: 'file_separator',
    type: 'separator',
  });
  Dome.addMenuItem({
    menu: 'File',
    label: 'Load session…',
    id: 'file_load',
    onClick: loadSession,
    type: 'normal',
  });
  Dome.addMenuItem({
    menu: 'File',
    label: 'Save session…',
    id: 'file_save',
    onClick: saveSession,
    type: 'normal',
  });
}

/* --------------------------------------------------------------------------*/
