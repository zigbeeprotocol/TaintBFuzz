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

/* eslint-disable no-console */

/**
   ## Dome Application (Main Process)

   This module manages the electron main-process of the application.
   Your application will launch on `Dome.start()`:

   @example
   // src/main/index.js:
   import * as Dome from 'dome' ;
   Dome.start();

   @packageDocumentation
   @module dome(main)
*/

import _ from 'lodash';
import fs from 'fs';
import path from 'path';
import {
  app,
  ipcMain,
  BrowserWindow,
  BrowserWindowConstructorOptions,
  IpcMainEvent,
  shell,
  dialog,
  nativeTheme,
  Rectangle,
} from 'electron';
import installExtension, { REACT_DEVELOPER_TOOLS } from 'dome/devtools';
import SYS, * as System from 'dome/system';

// --------------------------------------------------------------------------
// --- Main Window Web Navigation
// --------------------------------------------------------------------------

import { URL } from 'url';
import * as Menubar from './menubar';

// --------------------------------------------------------------------------
// --- System Helpers
// --------------------------------------------------------------------------

function fstat(p: string): fs.Stats | undefined {
  try {
    return fs.statSync(p);
  } catch (_error) {
    return undefined;
  }
}

// --------------------------------------------------------------------------
// --- Helpers
// --------------------------------------------------------------------------

const LOCAL = process.env.DOME_LOCAL;

/** Development mode flag */
export const { DEVEL } = System;

/** System platform */
export const { platform } = System;

// --------------------------------------------------------------------------
// --- Native Theme
// --------------------------------------------------------------------------

ipcMain.handle('dome.ipc.theme', () => {
  return nativeTheme.shouldUseDarkColors ? 'dark' : 'light';
});

nativeTheme.on('updated', () => {
  broadcast('dome.theme.updated');
});

function setNativeTheme(theme: string | undefined): void {
  switch (theme) {
    case 'dark':
    case 'light':
    case 'system':
      nativeTheme.themeSource = theme;
      return;
    default:
      console.warn('[dome] unknown theme', theme);
  }
}

// --------------------------------------------------------------------------
// --- Settings
// --------------------------------------------------------------------------

type json =
  | undefined | null | boolean | number | string
  | { [key: string]: json };
type Store = { [key: string]: json };
type Frame = { x: number, y: number, width: number, height: number };

function loadSettings(file: string): Store {
  try {
    if (!fstat(file))
      return {};
    const text = fs.readFileSync(file, { encoding: 'utf8' });
    return { ...JSON.parse(text) };
  } catch (err) {
    console.error('[Dome] Unable to load settings', file, err);
    return {};
  }
}

function saveSettings(file: string, data: Store = {}): void {
  try {
    const text = JSON.stringify(data, undefined, DEVEL ? 2 : 0);
    fs.writeFileSync(file, text, { encoding: 'utf8' });
  } catch (err) {
    console.error('[Dome] Unable to save settings', file, err);
  }
}

// --------------------------------------------------------------------------
// --- Global Settings
// --------------------------------------------------------------------------

let GlobalSettings = {}; // Current Dictionnary

const APP_DIR = app.getPath('userData');
const PATH_WINDOW_SETTINGS = path.join(APP_DIR, 'WindowSettings.json');
const PATH_GLOBAL_SETTINGS = path.join(APP_DIR, 'GlobalSettings.json');

function saveGlobalSettings(): void {
  try {
    if (!fstat(APP_DIR)) fs.mkdirSync(APP_DIR);
    saveSettings(PATH_GLOBAL_SETTINGS, GlobalSettings);
  } catch (err) {
    console.error('[Dome] Unable to save global settings', err);
  }
}

function obtainGlobalSettings(): Store {
  if (_.isEmpty(GlobalSettings)) {
    GlobalSettings = loadSettings(PATH_GLOBAL_SETTINGS);
  }
  return GlobalSettings;
}

// --------------------------------------------------------------------------
// --- Window Settings & Frames
// --------------------------------------------------------------------------

interface Handle {
  primary: boolean; // Primary window
  window: BrowserWindow; // Also prevents Gc
  frame: Electron.Rectangle | undefined; // Window frame
  devtools: boolean; // Developper tools visible
  reloaded: boolean; // Reloaded window
  config: string; // Path to config file
  settings: Store; // Current settings
  storage: Store; // Local storage
}

const WindowHandles = new Map<number, Handle>(); // Indexed by *webContents* id

function jInt(v: json): number {
  return _.toSafeInteger(v);
}

function jFrame(obj: json | Rectangle): Frame | undefined {
  if (obj && typeof (obj) === 'object')
    return {
      x: jInt(obj.x),
      y: jInt(obj.y),
      width: jInt(obj.width),
      height: jInt(obj.height),
    };
  return undefined;
}

function jStore(obj: json): Store {
  return obj !== null && typeof (obj) === 'object' ? obj : {};
}

function saveWindowConfig(handle: Handle): void {
  const frame = jFrame(handle.frame);
  const configData: Store = {
    frame,
    settings: handle.settings,
    storage: handle.storage,
    devtools: handle.devtools,
  };
  saveSettings(handle.config, configData);
}

function windowSyncSettings(event: IpcMainEvent): void {
  const handle = WindowHandles.get(event.sender.id);
  event.returnValue = {
    globals: obtainGlobalSettings(),
    storage: handle && handle.storage,
    settings: handle && handle.settings,
  };
}

ipcMain.on('dome.ipc.settings.sync', windowSyncSettings);

function applyThemeSettings(settings: Store): void {
  const theme = settings['dome-color-theme'];
  if (typeof (theme) === 'string') setNativeTheme(theme);
}

// --------------------------------------------------------------------------
// --- Patching Settings
// --------------------------------------------------------------------------

type Patch = { key: string; value: json };

function applyPatches(data: Store, args: Patch[]): void {
  args.forEach(({ key, value }) => {
    if (value === null) {
      delete data[key];
    } else {
      data[key] = value;
    }
  });
}

function applyWindowSettings(event: IpcMainEvent, args: Patch[]): void {
  const handle = WindowHandles.get(event.sender.id);
  if (handle) {
    applyPatches(handle.settings, args);
    if (DEVEL) saveWindowConfig(handle);
  }
}

function applyStorageSettings(event: IpcMainEvent, args: Patch[]): void {
  const handle = WindowHandles.get(event.sender.id);
  if (handle) {
    applyPatches(handle.storage, args);
    if (DEVEL) saveWindowConfig(handle);
  }
}

function applyGlobalSettings(event: IpcMainEvent, args: Patch[]): void {
  const settings: Store = obtainGlobalSettings();
  applyPatches(settings, args);
  applyThemeSettings(settings);
  BrowserWindow.getAllWindows().forEach((w: BrowserWindow) => {
    const contents = w.webContents;
    if (contents.id !== event.sender.id) {
      contents.send('dome.ipc.settings.broadcast', args);
    }
  });
  if (DEVEL) saveGlobalSettings();
}

ipcMain.on('dome.ipc.settings.window', applyWindowSettings);
ipcMain.on('dome.ipc.settings.global', applyGlobalSettings);
ipcMain.on('dome.ipc.settings.storage', applyStorageSettings);

// --------------------------------------------------------------------------
// --- Renderer-Process Communication
// --------------------------------------------------------------------------

function broadcast(event: string, ...args: unknown[]): void {
  BrowserWindow.getAllWindows().forEach((w) => {
    w.webContents.send(event, ...args);
  });
}

// --------------------------------------------------------------------------
// --- Window Activities
// --------------------------------------------------------------------------

let appName = 'Dome';
const MODIFIED = '(*) ';

/**
   Sets application window name
 */
export function setName(title: string): void {
  appName = title;
}

function setTitle(event: IpcMainEvent, title: string): void {
  const handle = WindowHandles.get(event.sender.id);
  if (handle) handle.window.setTitle(title || appName);
}

function setModified(event: IpcMainEvent, modified: boolean): void {
  const handle = WindowHandles.get(event.sender.id);
  if (handle) {
    const w = handle.window;
    if (platform === 'macos')
      w.setDocumentEdited(modified);
    else {
      let title = w.getTitle();
      if (title.startsWith(MODIFIED))
        title = title.substring(MODIFIED.length);
      if (modified)
        title = MODIFIED + title;
      w.setTitle(title);
    }
  }
}

ipcMain.on('dome.ipc.window.title', setTitle);
ipcMain.on('dome.ipc.window.modified', setModified);

function getURL(): string {
  if (DEVEL)
    return `http://localhost:${process.env.ELECTRON_WEBPACK_WDS_PORT}`;
  if (LOCAL)
    return `file://${path.join(__dirname, '../renderer/index.html')}`;
  return `file://${__dirname}/index.html`;
}

function navigateURL(sender: Electron.WebContents) {
  return (event: Electron.Event, url: string) => {
    event.preventDefault();
    const href = new URL(url);
    const main = new URL(getURL());
    if (href.origin === main.origin) {
      sender.send('dome.ipc.href', url);
    } else {
      shell.openExternal(url);
    }
  };
}

// --------------------------------------------------------------------------
// --- Lookup for config file
// --------------------------------------------------------------------------

function lookupConfig(pwd = '.'): string {
  const wdir = path.resolve(pwd);
  let cwd = wdir;
  const cfg = `.${appName.toLowerCase()}`;
  for (; ;) {
    const here = path.join(cwd, cfg);
    if (fstat(here)) return here;
    const up = path.dirname(cwd);
    if (up === cwd) break;
    cwd = up;
  }
  const home = path.resolve(app.getPath('home'));
  const user = wdir.startsWith(home) ? wdir : home;
  return path.join(user, cfg);
}

// --------------------------------------------------------------------------
// --- Browser Window SetUp
// --------------------------------------------------------------------------

function createBrowserWindow(
  primary: boolean,
  config: BrowserWindowConstructorOptions,
  argv?: string[],
  wdir?: string,
): BrowserWindow {

  const isAppWindow = (argv !== undefined && wdir !== undefined);

  const browserArguments = isAppWindow
    ? SYS.WINDOW_APPLICATION_ARGV
    : SYS.WINDOW_PREFERENCES_ARGV;

  const options: BrowserWindowConstructorOptions = {
    show: false,
    backgroundColor: '#f0f0f0',
    webPreferences: {
      nodeIntegration: true,
      contextIsolation: false,
      additionalArguments: [browserArguments],
    },
    ...config,
  };

  const configFile = isAppWindow ? lookupConfig(wdir) : PATH_WINDOW_SETTINGS;
  const configData = loadSettings(configFile);

  const frame = jFrame(configData.frame);
  const settings = jStore(configData.settings);
  const storage = jStore(configData.storage);
  const devtools = !!configData.devtools;

  if (frame) {
    options.x = frame.x;
    options.y = frame.y;
    options.width = frame.width;
    options.height = frame.height;
  }

  const theWindow = new BrowserWindow(options);
  const { webContents } = theWindow;
  const wid = webContents.id;

  const handle: Handle = {
    primary,
    window: theWindow,
    config: configFile,
    reloaded: false,
    frame,
    settings,
    storage,
    devtools,
  };

  // Keep the window reference (prevent garbage collection)
  WindowHandles.set(wid, handle);

  // Emitted when the window is closed.
  theWindow.on('closed', () => {
    saveWindowConfig(handle);
    // Dereference the window object (allow garbage collection)
    WindowHandles.delete(wid);
  });

  // Load the index.html of the app.
  if (DEVEL || LOCAL)
    process.env.ELECTRON_DISABLE_SECURITY_WARNINGS = 'true';

  theWindow.loadURL(getURL());

  // Load Finished
  theWindow.once('ready-to-show', () => {
    if (DEVEL || LOCAL)
      process.env.ELECTRON_DISABLE_SECURITY_WARNINGS = 'false';
    if (DEVEL && devtools) {
      webContents.openDevTools();
    }
    theWindow.show();
  });

  // Focus Management
  theWindow.on('focus', () => webContents.send('dome.ipc.focus', true));
  theWindow.on('blur', () => webContents.send('dome.ipc.focus', false));

  // URL Navigation
  webContents.on('will-navigate', navigateURL(webContents));
  webContents.on('did-navigate-in-page', navigateURL(webContents));

  // Application Startup
  webContents.on('did-finish-load', () => {
    if (!handle.reloaded) {
      handle.reloaded = true;
    } else {
      broadcast('dome.ipc.reload');
    }
    webContents.send('dome.ipc.command', argv, wdir);
  });

  // Emitted when the window want's to close.
  theWindow.on('close', () => {
    handle.frame = theWindow.getBounds();
    handle.devtools = webContents.isDevToolsOpened();
    webContents.send('dome.ipc.closing');
  });

  // Keep track of frame positions (in DEVEL)
  if (DEVEL) {
    const saveFrame = _.debounce(() => {
      handle.frame = theWindow.getBounds();
      handle.devtools = webContents.isDevToolsOpened();
      saveWindowConfig(handle);
    }, 300);
    theWindow.on('resize', saveFrame);
    theWindow.on('moved', saveFrame);
  }

  return theWindow;
}

// --------------------------------------------------------------------------
// --- Application Window(s) & Command Line
// --------------------------------------------------------------------------

function stripElectronArgv(argv: string[]): string[] {
  return argv.slice(DEVEL ? 3 : (LOCAL ? 2 : 1)).filter((p) => !!p);
}

function createPrimaryWindow(): void {
  // Initialize Menubar
  Menubar.install();

  // React Developper Tools
  if (DEVEL)
    installExtension(REACT_DEVELOPER_TOOLS, true).catch((err) => {
      console.error('[Dome] Enable to install React dev-tools', err);
    });
  const cwd = process.cwd();
  const wdir = cwd === '/' ? app.getPath('home') : cwd;
  const argv = stripElectronArgv(process.argv);

  // Initialize Theme
  const globals = obtainGlobalSettings();
  applyThemeSettings(globals);

  // Create Window
  createBrowserWindow(true, { title: appName }, argv, wdir);
}

let appCount = 1;

function createSecondaryWindow(
  _event: Electron.Event,
  chromiumArgv: string[],
  wdir: string,
): void {
  const argStart = "--second-instance=";
  let argString = chromiumArgv.find(a => a.startsWith(argStart));
  if (argString) {
    argString = argString.substring(argStart.length);
    const electronArgv = JSON.parse(argString);
    const argv = stripElectronArgv(electronArgv);
    const title = `${appName} #${++appCount}`;
    createBrowserWindow(false, { title }, argv, wdir);
  }
}

function createDesktopWindow(): void {
  const wdir = app.getPath('home');
  const title = `${appName} #${++appCount}`;
  createBrowserWindow(false, { title }, [], wdir);
}

// --------------------------------------------------------------------------
// --- Activate Windows (macOS)
// --------------------------------------------------------------------------

function activateWindows(): void {
  let isFocused = false;
  let toFocus: BrowserWindow | undefined;
  BrowserWindow.getAllWindows().forEach((w) => {
    w.show();
    if (w.isFocused()) isFocused = true;
    else if (!toFocus) toFocus = w;
  });
  if (!isFocused) {
    if (toFocus) toFocus.focus();
    else {
      // No focusable nor focused window
      createDesktopWindow();
    }
  }
}

// --------------------------------------------------------------------------
// --- Settings Window
// --------------------------------------------------------------------------

let PreferenceWindow: BrowserWindow | undefined;

function showSettingsWindow(): void {
  if (!PreferenceWindow)
    PreferenceWindow = createBrowserWindow(
      false, {
      title: `${appName} Settings`,
      width: 256,
      height: 248,
      fullscreen: false,
      maximizable: false,
      minimizable: false,
    });
  PreferenceWindow.setMenuBarVisibility(false);
  PreferenceWindow.show();
  PreferenceWindow.on('closed', () => { PreferenceWindow = undefined; });
}

function restoreDefaultSettings(): void {
  GlobalSettings = {};
  nativeTheme.themeSource = 'system';
  if (DEVEL) saveGlobalSettings();

  WindowHandles.forEach((handle) => {
    // Keep frame for user comfort
    handle.settings = {};
    handle.devtools = handle.window.webContents.isDevToolsOpened();
    if (DEVEL) saveWindowConfig(handle);
  });

  broadcast('dome.ipc.settings.defaults');
}

ipcMain.on('dome.menu.settings', showSettingsWindow);
ipcMain.on('dome.menu.defaults', restoreDefaultSettings);
ipcMain.on('dome.app.paths', (event) => {
  event.returnValue = {
    'home': app.getPath('home'),
    'desktop': app.getPath('desktop'),
    'documents': app.getPath('documents'),
    'downloads': app.getPath('downloads'),
    'temp': app.getPath('temp'),
  };
});

// --------------------------------------------------------------------------
// --- Main Application Starter
// --------------------------------------------------------------------------

/** Starts the main process. */
export function start(): void {

  // Workaround to recover the original commandline of a second instance
  // after chromium messes with the argument order.
  // See https://github.com/electron/electron/issues/20322 for more details.
  app.commandLine.appendSwitch("second-instance", JSON.stringify(process.argv));

  // Ensures second instance triggers the main one
  if (!app.requestSingleInstanceLock()) app.quit();

  // Change default locale
  app.commandLine.appendSwitch('lang', 'en');

  // Listen to application events
  app.on('ready', createPrimaryWindow); // Wait for Electron init
  app.on('activate', activateWindows); // Mac OSX response to dock
  app.on('second-instance', createSecondaryWindow);

  // At-exit callbacks
  app.on('will-quit', () => {
    saveGlobalSettings();
    System.doExit();
  });

  // On macOS the menu bar stays active until the user explicitly quits.
  // On other systems, automatically quit when all windows are closed.
  // Warning: when no event handler is registered, the app automatically
  // quit when all windows are closed.
  app.on('window-all-closed', () => {
    if (System.platform !== 'macos') app.quit();
  });

}

// --------------------------------------------------------------------------
// --- MenuBar Management
// --------------------------------------------------------------------------

/**
   Define a custom main window menu.
*/
export function addMenu(label: string): void {
  Menubar.addMenu(label);
}

/**
   Define a custom menu item.
*/
export function addMenuItem(spec: Menubar.CustomMenuItemSpec): void {
  Menubar.addMenuItem(spec);
}

/**
   Update a menu item.
*/
export function setMenuItem(spec: Menubar.CustomMenuItem): void {
  Menubar.setMenuItem(spec);
}

function isPrimary(evt: IpcMainEvent): boolean {
  const h = WindowHandles.get(evt.sender.id);
  return h ? h.primary : false;
}

ipcMain.on('dome.ipc.menu.addmenu', (evt, label) =>
  isPrimary(evt) && Menubar.addMenu(label)
);
ipcMain.on('dome.ipc.menu.addmenuitem', (evt, spec) =>
  isPrimary(evt) && Menubar.addMenuItem(spec)
);
ipcMain.on('dome.ipc.menu.setmenuitem', (_evt, spec) =>
  // Always update menu items
  Menubar.setMenuItem(spec)
);

// --------------------------------------------------------------------------
// --- Dialogs Management
// --------------------------------------------------------------------------

ipcMain.handle(
  'dome.dialog.showMessageBox',
  (_evt, props) => dialog.showMessageBox(props),
);

ipcMain.handle(
  'dome.dialog.showOpenDialog',
  (_evt, props) => dialog.showOpenDialog(props),
);

ipcMain.handle(
  'dome.dialog.showSaveDialog',
  (_evt, props) => dialog.showSaveDialog(props),
);

// --------------------------------------------------------------------------
