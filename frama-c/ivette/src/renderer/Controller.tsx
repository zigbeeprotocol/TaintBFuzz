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
// --- Server Controller
// --------------------------------------------------------------------------

import React from 'react';
import * as Dome from 'dome';
import * as Json from 'dome/data/json';
import * as Settings from 'dome/data/settings';
import * as Preferences from 'ivette/prefs';
import * as Toolbars from 'dome/frame/toolbars';
import { IconButton } from 'dome/controls/buttons';
import { LED, LEDstatus } from 'dome/controls/displays';
import { Label, Code } from 'dome/controls/labels';
import { RichTextBuffer } from 'dome/text/buffers';
import { Text } from 'dome/text/editors';
import { resolve } from 'dome/system';

import * as Ivette from 'ivette';
import * as Server from 'frama-c/server';

// --------------------------------------------------------------------------
// --- Configure Server
// --------------------------------------------------------------------------

const quoteRe = new RegExp('^[-_./:a-zA-Z0-9]+$');
const quote = (s: string): string =>
  (quoteRe.test(s) ? s : `"${s}"`);

const unquoteRe = new RegExp('^".*"$');
const unquote = (s: string): string =>
  (unquoteRe.test(s) ? s.substring(1, s.length - 1) : s);

function dumpServerConfig(sc: Server.Configuration): string {
  let buffer = '';
  const { working, command, sockaddr, params } = sc;
  if (working) buffer += `--working ${quote(working)}\n`;
  if (command) buffer += `--command ${quote(command)}\n`;
  if (sockaddr) buffer += `--socket ${sockaddr}\n`;
  if (params) {
    params.forEach((v: string, i: number) => {
      if (i > 0) {
        if (v.startsWith('-') || v.endsWith('.c')
          || v.endsWith('.h') || v.endsWith('.i')) {
          buffer += '\n';
        } else
          buffer += ' ';
      }
      buffer += v;
    });
  }
  return buffer;
}

function buildServerConfig(argv: string[], cwd?: string): Server.Configuration {
  const params = [];
  let command;
  let sockaddr;
  let working = cwd ? unquote(cwd) : undefined;
  for (let k = 0; k < (argv ? argv.length : 0); k++) {
    const v = argv[k];
    switch (v) {
      case '-C':
      case '--working':
      case '--cwd': // Deprecated
        k += 1;
        working = resolve(unquote(argv[k]));
        break;
      case '-B':
      case '--command':
        k += 1;
        command = resolve(unquote(argv[k]));
        break;
      case '-U':
      case '--socket':
        k += 1;
        sockaddr = argv[k];
        break;
      default:
        params.push(v);
    }
  }
  return {
    working,
    command,
    sockaddr,
    params,
  };
}

function buildServerCommand(cmd: string): Server.Configuration {
  return buildServerConfig(cmd.trim().split(/[ \t\n]+/));
}

/* -------------------------------------------------------------------------- */
/* --- History Management                                                 --- */
/* -------------------------------------------------------------------------- */

const historySetting = 'Controller.history';
const historyDecoder = Json.jList(Json.jString);

function getHistory(): string[] {
  return Settings.getLocalStorage(historySetting, historyDecoder, []);
}

function setHistory(hs: string[]): void {
  Settings.setLocalStorage(historySetting, hs);
}

function useHistory(): [string[], ((hs: string[]) => void)] {
  return Settings.useLocalStorage(historySetting, historyDecoder, []);
}

function insertConfig(hs: string[], cfg: Server.Configuration): string[] {
  const cmd = dumpServerConfig(cfg).trim();
  const newhs =
    hs.map((h) => h.trim())
      .filter((h: string) => h !== cmd && h !== '')
      .slice(0, 50);
  newhs.unshift(cmd);
  return newhs;
}

// --------------------------------------------------------------------------
// --- Start Server on Command
// --------------------------------------------------------------------------

let reloadCommand: string | undefined;

Dome.reload.on(() => {
  const [lastCmd] = getHistory();
  reloadCommand = lastCmd;
});

Dome.onCommand((argv: string[], cwd: string) => {
  let cfg;
  if (reloadCommand) {
    cfg = buildServerCommand(reloadCommand);
  } else {
    const hs = getHistory();
    if (argv.find((v) => v === '--reload' || v === '-R')) {
      cfg = buildServerCommand(hs[0]);
    } else {
      cfg = buildServerConfig(argv, cwd);
      setHistory(insertConfig(hs, cfg));
    }
  }
  Server.setConfig(cfg);
  Server.start();
});

// --------------------------------------------------------------------------
// --- Server Control
// --------------------------------------------------------------------------

export const Control = (): JSX.Element => {
  const status = Server.useStatus();

  let play = { enabled: false, onClick: () => { /* do nothing */ } };
  let stop = { enabled: false, onClick: () => { /* do nothing */ } };
  let reload = { enabled: false, onClick: () => { /* do nothing */ } };

  switch (status) {
    case Server.Status.OFF:
      play = { enabled: true, onClick: Server.start };
      break;
    case Server.Status.ON:
    case Server.Status.CMD:
    case Server.Status.FAILURE:
      stop = { enabled: true, onClick: Server.stop };
      reload = { enabled: true, onClick: Server.restart };
      break;
    default:
      break;
  }

  return (
    <Toolbars.ButtonGroup>
      <Toolbars.Button
        icon="MEDIA.PLAY"
        enabled={play.enabled}
        onClick={play.onClick}
        title="Start the server"
      />
      <Toolbars.Button
        icon="RELOAD"
        enabled={reload.enabled}
        onClick={reload.onClick}
        title="Re-start the server"
      />
      <Toolbars.Button
        icon="MEDIA.STOP"
        enabled={stop.enabled}
        onClick={stop.onClick}
        title="Shut down the server"
      />
    </Toolbars.ButtonGroup>
  );
};

// --------------------------------------------------------------------------
// --- Server Console
// --------------------------------------------------------------------------

const editor = new RichTextBuffer();

const RenderConsole = (): JSX.Element => {
  const scratch = React.useRef([] as string[]);
  const [cursor, setCursor] = React.useState(-1);
  const [isEmpty, setEmpty] = React.useState(true);
  const [noTrash, setNoTrash] = React.useState(true);
  const [history, setHistory] = useHistory();

  React.useEffect(() => {
    const callback = (): void => {
      const cmd = editor.getValue().trim();
      setEmpty(cmd === '');
      setNoTrash(noTrash && cmd === history[0]);
    };
    editor.on('change', callback);
    return () => { editor.off('change', callback); };
  });

  const [maxLines] = Settings.useGlobalSettings(Preferences.ConsoleScrollback);
  React.useEffect(() => {
    Server.buffer.setMaxlines(maxLines);
  });

  const doReload = (): void => {
    const cfg = Server.getConfig();
    const hst = insertConfig(history, cfg);
    const cmd = hst[0];
    scratch.current = hst.slice();
    editor.setValue(cmd);
    setEmpty(cmd === '');
    setHistory(hst);
    setCursor(0);
  };

  const doSwitch = (): void => {
    if (cursor < 0) doReload();
    else {
      editor.clear();
      scratch.current = [];
      setCursor(-1);
    }
  };

  const doExec = (): void => {
    const cfg = buildServerCommand(editor.getValue());
    const hst = insertConfig(history, cfg);
    setHistory(hst);
    setCursor(-1);
    editor.clear();
    Server.setConfig(cfg);
    Server.restart();
  };

  const doMove = (target: number): (undefined | (() => void)) => {
    if (0 <= target && target < history.length && target !== cursor)
      return (): void => {
        const cmd = editor.getValue();
        const pad = scratch.current;
        pad[cursor] = cmd;
        const cmd2 = pad[target];
        editor.setValue(cmd2);
        setEmpty(cmd2 === '');
        setCursor(target);
      };
    return undefined;
  };

  const doRemove = (): void => {
    const n = history.length;
    if (n <= 1) doReload();
    else {
      const hst = history.slice();
      const pad = scratch.current;
      hst.splice(cursor, 1);
      pad.splice(cursor, 1);
      setHistory(hst);
      const next = cursor > 0 ? cursor - 1 : 0;
      editor.setValue(pad[next]);
      setCursor(next);
    }
  };

  const doPrev = doMove(cursor + 1);
  const doNext = doMove(cursor - 1);
  const edited = 0 <= cursor;
  const n = history.length;

  return (
    <>
      <Ivette.TitleBar label={edited ? 'Command line' : 'Console'}>
        <IconButton
          icon="TRASH"
          display={edited}
          disabled={noTrash}
          onClick={doRemove}
          title="Discard command from history (irreversible)"
        />
        <Toolbars.Space />
        <IconButton
          icon="RELOAD"
          display={edited}
          onClick={doReload}
          title="Discard changes"
        />
        <IconButton
          icon="ANGLE.LEFT"
          display={edited}
          onClick={doPrev}
          title="Previous command"
        />
        <IconButton
          icon="ANGLE.RIGHT"
          display={edited}
          onClick={doNext}
          title="Next command"
        />
        <Toolbars.Space />
        <Label
          className="component-info"
          title="History (last command first)"
          display={edited}
        >
          {1 + cursor} / {n}
        </Label>
        <Toolbars.Space />
        <IconButton
          icon="MEDIA.PLAY"
          display={edited}
          disabled={isEmpty}
          onClick={doExec}
          title="Execute command"
        />
        <IconButton
          icon="TERMINAL"
          selected={edited}
          onClick={doSwitch}
          title="Toggle command line editing"
        />
      </Ivette.TitleBar>
      <Text
        buffer={edited ? editor : Server.buffer}
        mode="text"
        readOnly={!edited}
      />
    </>
  );
};

Ivette.registerComponent({
  id: 'frama-c.console',
  group: 'frama-c.kernel',
  label: 'Console',
  title: 'Frama-C Server Output & Command Line',
  rank: -1,
  children: <RenderConsole />,
});

Ivette.registerView({
  id: 'console',
  rank: -1,
  label: 'Console',
  layout: 'frama-c.console',
});

// --------------------------------------------------------------------------
// --- Status
// --------------------------------------------------------------------------

export const Status = (): JSX.Element => {
  const status = Server.useStatus();
  const pending = Server.getPending();
  let led: LEDstatus = 'inactive';
  let title = undefined;
  let icon = undefined;
  let running = 'OFF';
  let blink = false;

  switch (status) {
    case Server.Status.OFF:
      title = 'Server is off';
      break;
    case Server.Status.STARTING:
      led = 'active';
      blink = true;
      running = 'BOOT';
      title = 'Server is starting';
      break;
    case Server.Status.ON:
      led = 'active';
      blink = pending > 0;
      running = 'ON';
      title = 'Server is running';
      break;
    case Server.Status.CMD:
      led = 'positive';
      blink = true;
      running = 'CMD';
      title = 'Command-line processing';
      break;
    case Server.Status.HALTING:
      led = 'negative';
      blink = true;
      running = 'HALT';
      title = 'Server is halting';
      break;
    case Server.Status.RESTARTING:
      led = 'warning';
      blink = true;
      running = 'REBOOT';
      title = 'Server is restarting';
      break;
    case Server.Status.FAILURE:
      led = 'negative';
      blink = true;
      running = 'ERR';
      title = 'Server halted because of failure';
      icon = 'WARNING';
      break;
  }

  return (
    <>
      <LED status={led} blink={blink} />
      <Code icon={icon} label={running} title={title} />
      <Toolbars.Separator />
    </>
  );
};

// --------------------------------------------------------------------------
// --- Server Stats
// --------------------------------------------------------------------------

export const Stats = (): (null | JSX.Element) => {
  Server.useStatus();
  const pending = Server.getPending();
  return pending > 0 ? <Code>{pending} rq.</Code> : null;
};

// --------------------------------------------------------------------------
