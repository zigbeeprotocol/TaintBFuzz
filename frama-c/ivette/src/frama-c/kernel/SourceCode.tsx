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
// --- Source Code
// --------------------------------------------------------------------------

import React from 'react';
import * as Server from 'frama-c/server';
import * as States from 'frama-c/states';

import * as Dome from 'dome';
import * as System from 'dome/system';
import { RichTextBuffer } from 'dome/text/buffers';
import { Text } from 'dome/text/editors';
import { TitleBar } from 'ivette';
import * as Preferences from 'ivette/prefs';
import { functions, markerInfo, getMarkerAt } from 'frama-c/kernel/api/ast';
import { Code } from 'dome/controls/labels';
import { Hfill } from 'dome/layout/boxes';
import { IconButton } from 'dome/controls/buttons';
import * as Path from 'path';
import * as Settings from 'dome/data/settings';
import * as Status from 'frama-c/kernel/Status';

import CodeMirror from 'codemirror/lib/codemirror';
import 'codemirror/addon/selection/active-line';
import 'codemirror/addon/dialog/dialog.css';
import 'codemirror/addon/search/search';
import 'codemirror/addon/search/searchcursor';

// --------------------------------------------------------------------------
// --- Pretty Printing (Browser Console)
// --------------------------------------------------------------------------

const D = new Dome.Debug('Source Code');

// --------------------------------------------------------------------------
// --- Source Code Printer
// --------------------------------------------------------------------------

// The SourceCode component, producing the GUI part showing the source code
// corresponding to the selected function.
export default function SourceCode(): JSX.Element {

  // Hooks
  const [buffer] = React.useState(() => new RichTextBuffer());
  const [selection, updateSelection] = States.useSelection();
  const theFunction = selection?.current?.fct;
  const theMarker = selection?.current?.marker;
  const markersInfo = States.useSyncArray(markerInfo);
  const functionsData = States.useSyncArray(functions).getArray();

  // Retrieving the file name and the line number from the selection and the
  // synchronized tables.
  const sloc =
    (theMarker && markersInfo.getData(theMarker)?.sloc) ??
    (theFunction && functionsData.find((e) => e.name === theFunction)?.sloc);
  const file = sloc ? sloc.file : '';
  const line = sloc ? sloc.line : 0;
  const filename = Path.parse(file).base;

  // Global Font Size
  const [fontSize] = Settings.useGlobalSettings(Preferences.EditorFontSize);

  // Updating the buffer content.
  const text = React.useMemo(async () => {
    const onError = (): string => {
      if (file)
        D.error(`Fail to load source code file ${file}`);
      return '';
    };
    return System.readFile(file).catch(onError);
  }, [file]);
  const { result } = Dome.usePromise(text);
  React.useEffect(() => buffer.setValue(result), [buffer, result]);

  /* Last location selected by a click in the source code. */
  const selected: React.MutableRefObject<undefined | States.Location> =
    React.useRef();

  /* Updates the cursor position according to the current [selection], except
     when the [selection] is changed according to a click in the source code,
     in which case the cursor should stay exactly where the user clicked. */
  React.useEffect(() => {
    if (selected.current && selected?.current === selection?.current)
      selected.current = undefined;
    else
      buffer.setCursorOnTop(line);
  }, [buffer, selection, line, result]);

  /* CodeMirror types used to bind callbacks to extraKeys. */
  type position = CodeMirror.Position;
  type editor = CodeMirror.Editor;

  const selectCallback = React.useCallback(
    async function select(editor: editor, event: MouseEvent) {
      const pos = editor.coordsChar({ left: event.x, top: event.y });
      if (file === '' || !pos) return;
      const arg = [file, pos.line + 1, pos.ch + 1];
      Server
        .send(getMarkerAt, arg)
        .then(([fct, marker]) => {
          if (fct || marker) {
            const location = { fct, marker } as States.Location;
            selected.current = location;
            updateSelection({ location });
          }
        })
        .catch((err) => {
          D.error(`Failed to get marker from source file position: ${err}`);
          Status.setMessage({
            text: 'Failed request to Frama-C server',
            kind: 'error',
          });
        });
    },
    [file, updateSelection],
  );

  React.useEffect(() => {
    buffer.forEach((cm) => cm.on('mousedown', selectCallback));
    return () => buffer.forEach((cm) => cm.off('mousedown', selectCallback));
  }, [buffer, selectCallback]);

  const [command] = Settings.useGlobalSettings(Preferences.EditorCommand);
  async function launchEditor(_?: editor, pos?: position): Promise<void> {
    if (file !== '') {
      const selectedLine = pos ? (pos.line + 1).toString() : '1';
      const selectedChar = pos ? (pos.ch + 1).toString() : '1';
      const cmd = command
        .replace('%s', file)
        .replace('%n', selectedLine)
        .replace('%c', selectedChar);
      const args = cmd.split(' ');
      const prog = args.shift();
      if (prog) System.spawn(prog, args).catch(() => {
        Status.setMessage({
          text: `An error has occured when opening the external editor ${prog}`,
          kind: 'error',
        });
      });
    }
  }

  async function contextMenu(editor?: editor, pos?: position): Promise<void> {
    if (file !== '') {
      const items = [
        {
          label: 'Open file in an external editor',
          onClick: () => launchEditor(editor, pos),
        },
      ];
      Dome.popupMenu(items);
    }
  }

  const externalEditorTitle =
    'Open the source file in an external editor.\nA Ctrl-click '
    + 'in the source code opens the editor at the selected location.'
    + '\nThe editor used can be configured in Ivette settings.';

  // Building the React component.
  return (
    <>
      <TitleBar>
        <IconButton
          icon="DUPLICATE"
          visible={file !== ''}
          onClick={launchEditor}
          title={externalEditorTitle}
        />
        <Code title={file}>{filename}</Code>
        <Hfill />
      </TitleBar>
      <Text
        buffer={buffer}
        mode="text/x-csrc"
        fontSize={fontSize}
        selection={theMarker}
        lineNumbers={!!theFunction}
        styleActiveLine={!!theFunction}
        extraKeys={{
          'Alt-F': 'findPersistent',
          'Ctrl-LeftClick': launchEditor as (_: CodeMirror.Editor) => void,
          RightClick: contextMenu as (_: CodeMirror.Editor) => void,
        }}
        readOnly
      />
    </>
  );

}

// --------------------------------------------------------------------------
