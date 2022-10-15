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

import * as ZMQ from 'zeromq';
import { Debug } from 'dome';
import { Client } from './client';

const D = new Debug('ZmqServer');

// --------------------------------------------------------------------------
// --- Frama-C Server API
// --------------------------------------------------------------------------

class ZmqClient extends Client {

  queue: string[] = [];
  zmqSocket: ZMQ.Socket | undefined;
  zmqIsBusy = false;

  /** Server CLI */
  commandLine(sockaddr: string, params: string[]): string[] {
    return ['-server-zmq', `ipc://${sockaddr}`, '-then'].concat(params);
  }

  /** Connection */
  connect(sockaddr: string): void {
    if (this.zmqSocket) {
      this.zmqSocket.close();
    }
    this.zmqSocket = new ZMQ.Socket('req');
    this.zmqIsBusy = false;
    this.zmqSocket.connect(`ipc://${sockaddr}`);
    this.zmqSocket.on('message', (msg: string[]) => this._receive(msg));
  }

  disconnect(): void {
    this.zmqIsBusy = false;
    this.queue = [];
    if (this.zmqSocket) {
      this.zmqSocket.close();
      this.zmqSocket = undefined;
    }
  }

  /** Send Request */
  send(kind: string, id: string, request: string, data: string): void {
    if (this.zmqSocket) {
      this.queue.push(kind, id, request, data);
      this._flush();
    }
  }

  /** Signal ON */
  sigOn(id: string): void {
    if (this.zmqSocket) {
      this.queue.push('SIGON', id);
      this._flush();
    }
  }

  /** Signal ON */
  sigOff(id: string): void {
    if (this.zmqSocket) {
      this.queue.push('SIGOFF', id);
      this._flush();
    }
  }

  /** Kill Request */
  kill(id: string): void {
    if (this.zmqSocket) {
      this.queue.push('KILL', id);
      this._flush();
    }
  }

  /** Polling */
  poll(): void {
    if (this.zmqSocket && this.queue.length === 0) {
      this.queue.push('POLL');
    }
    this._flush();
  }

  /** Shutdown the server */
  shutdown(): void {
    this.queue = [];
    if (this.zmqSocket) {
      this.queue.push('SHUTDOWN');
      this._flush();
    }
  }

  // --------------------------------------------------------------------------
  // --- Low-Level Management
  // --------------------------------------------------------------------------

  _flush(): void {
    const socket = this.zmqSocket;
    if (socket) {
      const cmds = this.queue;
      if (cmds && !this.zmqIsBusy) {
        try {
          this.queue = [];
          socket.send(cmds);
          this.zmqIsBusy = true;
        } catch (err) {
          D.error('ZmqSocket', err);
          this.zmqIsBusy = false;
        }
      }
    } else {
      this.queue = [];
    }
  }

  _receive(resp: string[]): void {
    try {
      this._decode(resp);
    } catch (err) {
      D.error('ZmqSocket', err);
    } finally {
      this.zmqIsBusy = false;
      setImmediate(() => this._flush());
    }
  }

  /* eslint-disable @typescript-eslint/indent */
  _decode(resp: string[]): void {
    const shift = (): string => resp.shift() ?? '';
    while (resp.length) {
      const cmd = shift();
      switch (cmd) {
        case 'NONE':
          break;
        case 'DATA':
          {
            const rid = shift();
            const data = JSON.parse(shift());
            this.emitData(rid, data);
          }
          break;
        case 'KILLED':
          {
            const rid = shift();
            this.emitKilled(rid);
          }
          break;
        case 'ERROR':
          {
            const rid = shift();
            const msg = shift();
            this.emitError(rid, msg);
          }
          break;
        case 'REJECTED':
          {
            const rid = shift();
            this.emitRejected(rid);
          }
          break;
        case 'SIGNAL':
          {
            const rid = shift();
            this.emitSignal(rid);
          }
          break;
        case 'WRONG':
          {
            const err = shift();
            D.error(`ZMQ Protocol Error: ${err}`);
          }
          break;
        case 'CMDLINEON':
          this.emitCmdLine(true);
          break;
        case 'CMDLINEOFF':
          this.emitCmdLine(false);
          break;
        default:
          D.error(`Unknown Response: ${cmd}`);
          return;
      }
    }
  }

}

export const client: Client = new ZmqClient();

// --------------------------------------------------------------------------
