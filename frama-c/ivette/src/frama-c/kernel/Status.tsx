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
/* --- Frama-C Status Message                                             ---*/
/* --------------------------------------------------------------------------*/

import React from 'react';
import { Code } from 'dome/controls/labels';
import { IconButton } from 'dome/controls/buttons';
import { LED } from 'dome/controls/displays';
import { Icon } from 'dome/controls/icons';
import * as Toolbars from 'dome/frame/toolbars';
import { GlobalState, useGlobalState } from 'dome/data/states';
import * as Server from 'frama-c/server';

export type kind =
  'none' | 'info' | 'warning' | 'error' | 'success' | 'progress';

export interface MessageProps {
  kind: kind;
  text: string;
  title?: string;
}

const emptyMessage: MessageProps = { text: '', kind: 'none' };

const GlobalMessage = new GlobalState(emptyMessage);

export function setMessage(message: MessageProps): void {
  GlobalMessage.setValue(message);
}

export default function Message(): JSX.Element {
  const [message] = useGlobalState(GlobalMessage);
  return (
    <>
      <Toolbars.Space />
      {message.kind === 'progress' && <LED status="active" blink />}
      {message.kind === 'success' && <Icon id="CHECK" fill="green" />}
      {message.kind === 'warning' && <Icon id="ATTENTION" />}
      {message.kind === 'error' && <Icon id="CROSS" fill="red" />}
      {message.kind === 'info' && <Icon id="CIRC.INFO" />}
      <Code label={message.text} title={message.title} />
      <IconButton
        icon="CIRC.CLOSE"
        onClick={() => setMessage(emptyMessage)}
        visible={message !== emptyMessage}
        title="Hide current message"
      />
      <Toolbars.Space />
    </>
  );
}

/* Callback on server events */

{
  Server.onReady(() => setMessage(emptyMessage));
  Server.onShutdown(() => setMessage(emptyMessage));
}

/* --------------------------------------------------------------------------*/
