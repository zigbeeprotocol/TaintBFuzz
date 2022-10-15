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

// --------------------------------------------------------------------------
// --- Menus & MenuBar Management
// --------------------------------------------------------------------------

import {
  app,
  ipcMain,
  BrowserWindow,
  Menu,
  MenuItem,
  shell,
  KeyboardEvent,
} from 'electron';
import * as System from 'dome/system';

// --------------------------------------------------------------------------
// --- Special Callbacks
// --------------------------------------------------------------------------

function reloadWindow(): void {
  reset(); // declared below
  BrowserWindow.getAllWindows().forEach((win) => {
    if (win) {
      try {
        win.webContents.send('dome.ipc.closing');
        win.reload();
      } catch (err) {
        console.warn('[Reload]', win.id, err);
      }
    }
  });
}

function toggleFullScreen(
  _item: MenuItem,
  focusedWindow: BrowserWindow | undefined,
  _evt: KeyboardEvent,
): void {
  if (focusedWindow)
    focusedWindow.setFullScreen(!focusedWindow.isFullScreen());
}

function toggleDevTools(
  _item: MenuItem,
  focusedWindow: BrowserWindow | undefined,
  _evt: KeyboardEvent,
): void {
  if (focusedWindow)
    focusedWindow.webContents.toggleDevTools();
}

function userFindInfo(
  _item: MenuItem,
  focusedWindow: BrowserWindow | undefined,
  _evt: KeyboardEvent,
): void {
  if (focusedWindow)
    focusedWindow.webContents.send('dome.ipc.find');
}

// --------------------------------------------------------------------------
// --- Menu Utilities
// --------------------------------------------------------------------------

export type MenuItemSpec = Electron.MenuItemConstructorOptions;
export type MenuSpec = MenuItemSpec[];

const Separator: MenuItemSpec = { type: 'separator' };

function concatSep(...menus: MenuSpec[]): MenuSpec {
  let menu: MenuItemSpec[] = [];
  let needsep = false;
  menus.forEach((items) => {
    const n = items.length;
    if (n > 0) {
      if (needsep) menu.push(Separator);
      menu = menu.concat(items);
      needsep = (items[n - 1].type !== 'separator');
    }
  });
  return menu;
}

// --------------------------------------------------------------------------
// --- MacOS Menu Items
// --------------------------------------------------------------------------

const macosAppMenuItems = (appName: string): MenuSpec => [
  {
    label: `About ${appName}`,
    role: 'about',
  },
  Separator,
  {
    label: 'Preferences…',
    accelerator: 'Command+,',
    click: () => ipcMain.emit('dome.menu.settings'),
  },
  {
    label: 'Restore Defaults',
    click: () => ipcMain.emit('dome.menu.defaults'),
  },
  Separator,
  {
    label: 'Services',
    submenu: [],
    role: 'services',
  },
  Separator,
  {
    label: `Hide ${appName}`,
    accelerator: 'Command+H',
    role: 'hide',
  }, {
    label: 'Hide Others',
    accelerator: 'Command+Alt+H',
    role: 'hideOthers',
  }, {
    label: 'Show All',
    role: 'unhide',
  },
  Separator,
  {
    label: 'Quit',
    accelerator: 'Command+Q',
    role: 'quit',
  },
];

// --------------------------------------------------------------------------
// --- File Menu Items (platform dependant)
// --------------------------------------------------------------------------

const fileMenuItemsCustom: MenuSpec = [];

const fileMenuItemsLinux: MenuSpec = [
  {
    label: 'Preferences…',
    click: () => ipcMain.emit('dome.menu.settings'),
  },
  {
    label: 'Restore Defaults',
    click: () => ipcMain.emit('dome.menu.defaults'),
  },
  Separator,
  {
    label: 'Exit',
    accelerator: 'Ctrl+Q',
    role: 'quit',
  },
];

// --------------------------------------------------------------------------
// --- Edit Menu Items
// --------------------------------------------------------------------------

const editMenuItemsCustom: MenuSpec = [];

const editMenuItems: MenuSpec = [
  {
    label: 'Undo',
    accelerator: 'CmdOrCtrl+Z',
    role: 'undo',
  }, {
    label: 'Redo',
    accelerator: 'Shift+CmdOrCtrl+Z',
    role: 'redo',
  },
  Separator,
  {
    label: 'Cut',
    accelerator: 'CmdOrCtrl+X',
    role: 'cut',
  }, {
    label: 'Copy',
    accelerator: 'CmdOrCtrl+C',
    role: 'copy',
  }, {
    label: 'Paste',
    accelerator: 'CmdOrCtrl+V',
    role: 'paste',
  }, {
    label: 'Select All',
    accelerator: 'CmdOrCtrl+A',
    role: 'selectAll',
  },
  Separator,
  {
    label: 'Find',
    accelerator: 'CmdOrCtrl+F',
    click: userFindInfo,
  },
];

// --------------------------------------------------------------------------
// --- View Menu Items
// --------------------------------------------------------------------------

const viewMenuItemsCustom: MenuSpec = [];

const viewMenuItems = (osx: boolean): MenuSpec => [
  {
    label: 'Reload',
    accelerator: 'CmdOrCtrl+R',
    click: reloadWindow,
  }, {
    label: 'Toggle Full Screen',
    accelerator: (osx ? 'Ctrl+Command+F' : 'F11'),
    click: toggleFullScreen,
  }, {
    label: 'Toggle Developer Tools',
    accelerator: (osx ? 'Alt+Command+I' : 'Ctrl+Shift+I'),
    click: toggleDevTools,
  },
];

// --------------------------------------------------------------------------
// --- Window Menu Items
// --------------------------------------------------------------------------

const windowMenuItemsLinux: MenuSpec = [
  {
    label: 'Minimize',
    accelerator: 'CmdOrCtrl+M',
    role: 'minimize',
  }, {
    label: 'Close',
    accelerator: 'CmdOrCtrl+W',
    role: 'close',
  },
  Separator,
  {
    label: 'Reopen Window',
    accelerator: 'CmdOrCtrl+Shift+T',
    enabled: false,
    click: () => { app.emit('activate'); },
  },
];

const windowMenuItemsMacos: MenuSpec = windowMenuItemsLinux.concat([
  {
    label: 'Bring All to Front',
    role: 'front',
  },
]);

// --------------------------------------------------------------------------
// --- Help Menu Items
// --------------------------------------------------------------------------

let learnMoreLink = '';
ipcMain.handle('dome.ipc.updateLearnMore', (_, link) => {
  if (typeof link === 'string') learnMoreLink = link;
});

const helpMenuItems: MenuSpec = [
  {
    label: 'Learn More',
    click() { shell.openExternal(learnMoreLink); },
  },
];

// --------------------------------------------------------------------------
// --- Update MenuBar (async)
// --------------------------------------------------------------------------

let updateRequired = false;
let updateTriggered = false;

function requestUpdate(): void {
  if (updateRequired && !updateTriggered) {
    updateTriggered = true;
    setImmediate(install);
  }
}

// --------------------------------------------------------------------------
// --- CustomMenus
// --------------------------------------------------------------------------

interface CustomMenu extends Electron.MenuItemConstructorOptions {
  label: string;
  submenu: MenuSpec;
}

const customMenus: CustomMenu[] = [];

type ItemEntry = { spec: MenuItemSpec; item?: MenuItem };

const customItems = new Map<string, ItemEntry>();

function findMenu(label: string): MenuSpec | undefined {
  switch (label) {
    case 'File': return fileMenuItemsCustom;
    case 'Edit': return editMenuItemsCustom;
    case 'View': return viewMenuItemsCustom;
    default: {
      const cm = customMenus.find((m) => m.label === label);
      return cm && cm.submenu;
    }
  }
}

export function addMenu(label: string): void {
  if (findMenu(label)) {
    console.warn(`Already defined menu '${label}'`);
  } else {
    customMenus.push({ label, submenu: [] });
  }
  requestUpdate();
}

export interface CustomMenuItem extends MenuItemSpec {
  menu: string;
  id: string;
  key?: string;
}

export interface SeparatorItem {
  menu: string;
  type: 'separator';
}

export type CustomMenuItemSpec = SeparatorItem | CustomMenuItem;

export function addMenuItem(custom: CustomMenuItemSpec): void {
  const menuSpec = findMenu(custom.menu);
  if (!menuSpec) {
    console.error('[Dome] Unknown menu', custom);
    return;
  }
  if (custom.type === 'separator') {
    menuSpec.push(Separator);
  } else {
    const { id, key, ...spec } = custom;
    if (key) {
      switch (System.platform) {
        case 'macos':
          if (key.startsWith('Cmd+'))
            spec.accelerator = `Cmd+${key.substring(4)}`;
          if (key.startsWith('Alt+'))
            spec.accelerator = `Cmd+Alt+${key.substring(4)}`;
          if (key.startsWith('Meta+'))
            spec.accelerator = `Cmd+Shift+${key.substring(5)}`;
          break;
        case 'windows':
        case 'linux':
        default:
          if (key.startsWith('Cmd+'))
            spec.accelerator = `Ctrl+${key.substring(4)}`;
          if (key.startsWith('Alt+'))
            spec.accelerator = `Alt+${key.substring(4)}`;
          if (key.startsWith('Meta+'))
            spec.accelerator = `Ctrl+Alt+${key.substring(5)}`;
          break;
      }
    }
    const entry = customItems.get(id);
    if (entry) {
      if (!System.DEVEL) {
        console.error('[Dome] Duplicate menu item:', custom);
        return;
      }
      if (entry.spec) Object.assign(entry.spec, spec);
      if (entry.item) Object.assign(entry.item, spec);
    } else {
      if (!spec.click && !spec.role)
        spec.click = (
          _item: MenuItem,
          window: BrowserWindow | undefined,
          _evt: KeyboardEvent,
        ) => window?.webContents.send('dome.ipc.menu.clicked', id);
      customItems.set(id, { spec });
      menuSpec.push(spec);
    }
  }
  requestUpdate();
}

export function setMenuItem({ id, ...options }: CustomMenuItem): void {
  const entry = customItems.get(id);
  if (entry) {
    if (entry.spec) Object.assign(entry.spec, options);
    if (entry.item) Object.assign(entry.item, options);
    requestUpdate();
  } else
    console.warn(`[Dome] unknown menu item #${id}`);
}

// --------------------------------------------------------------------------
// --- Menu Bar Template
// --------------------------------------------------------------------------

function template(): CustomMenu[] {
  switch (System.platform) {
    case 'macos':
      return ([] as CustomMenu[]).concat(
        [
          { label: app.name, submenu: macosAppMenuItems(app.name) },
          {
            label: 'File',
            submenu: fileMenuItemsCustom,
          },
          {
            label: 'Edit',
            submenu: concatSep(editMenuItems, editMenuItemsCustom),
          },
          {
            label: 'View',
            submenu: concatSep(viewMenuItemsCustom, viewMenuItems(true)),
          },
        ],
        customMenus,
        [
          {
            label: 'Window',
            role: 'window',
            submenu: windowMenuItemsMacos,
          },
          {
            label: 'Help',
            role: 'help',
            submenu: helpMenuItems,
          },
        ],
      );
    case 'windows':
    case 'linux':
    default:
      return ([] as CustomMenu[]).concat(
        [
          {
            label: 'File',
            submenu: concatSep(fileMenuItemsCustom, fileMenuItemsLinux),
          },
          {
            label: 'Edit',
            submenu: concatSep(editMenuItems, editMenuItemsCustom),
          },
          {
            label: 'View',
            submenu: concatSep(viewMenuItemsCustom, viewMenuItems(false)),
          },
        ],
        customMenus,
        [
          { label: 'Window', submenu: windowMenuItemsLinux },
          { label: 'Help', submenu: helpMenuItems },
        ],
      );
  }
}

// --------------------------------------------------------------------------
// --- MenuBar SetUp
// --------------------------------------------------------------------------

let menubar: Menu;

function registerCustomItems(menu: Menu): void {
  menu.items.forEach((item: MenuItem) => {
    const entry = customItems.get(item.id);
    if (entry) entry.item = item;
    if (item.submenu) registerCustomItems(item.submenu);
  });
}

// Initialize the menubar machinery
export function install(): void {
  updateRequired = true;
  updateTriggered = false;
  menubar = Menu.buildFromTemplate(template());
  registerCustomItems(menubar);
  Menu.setApplicationMenu(menubar);
}

// Called by reload above
function reset(): void {
  fileMenuItemsCustom.length = 0;
  editMenuItemsCustom.length = 0;
  viewMenuItemsCustom.length = 0;
  customMenus.length = 0;
  customItems.clear();
  install();
}

// --------------------------------------------------------------------------
// --- Popup Menu Management
// --------------------------------------------------------------------------

interface PopupMenuItemProps {
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
}

type PopupMenuItem = PopupMenuItemProps | 'separator';

function handlePopupMenu(_: Event, items: PopupMenuItem[]): Promise<number> {
  return new Promise((resolve) => {
    const menu = new Menu();
    let kid = 0;
    let selected = (-1);
    items.forEach((item, index) => {
      if (item === 'separator')
        menu.append(new MenuItem({ type: 'separator' }));
      else if (item) {
        const { display = true, enabled, checked } = item;
        if (display) {
          const label = item.label || `#${++kid}`;
          const click = (): void => { selected = index; };
          const type = checked !== undefined ? 'checkbox' : 'normal';
          menu.append(new MenuItem({ label, enabled, type, checked, click }));
        }
      }
    });
    menu.popup({ callback: () => resolve(selected) });
  });
}

ipcMain.handle('dome.popup', handlePopupMenu);

// --------------------------------------------------------------------------
