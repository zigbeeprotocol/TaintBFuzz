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

import Net from 'net';
import { Debug } from 'dome';
import { json } from 'dome/data/json';
import { Client } from './client';

const D = new Debug('SocketServer');

const RETRIES = 30;
const TIMEOUT = 200;

// --------------------------------------------------------------------------
// --- Frama-C Server API
// --------------------------------------------------------------------------

class SocketClient extends Client {

  retries = 0;
  running = false;
  socket: Net.Socket | undefined;
  timer: NodeJS.Timeout | undefined;
  queue: json[] = [];
  buffer: Buffer = Buffer.from('');

  /** Server CLI */
  commandLine(sockaddr: string, params: string[]): string[] {
    return ['-server-socket', sockaddr, '-then'].concat(params);
  }

  /** Connection */
  connect(sockaddr: string): void {
    this.retries++;
    if (this.socket) {
      this.socket.destroy();
    }
    if (this.timer) {
      clearTimeout(this.timer);
      this.timer = undefined;
    }
    const s = Net.createConnection(sockaddr, () => {
      this.running = true;
      this.retries = 0;
      this.buffer = Buffer.from('');
      this.emitConnect();
      this._flush();
    });
    // Using Buffer data encoding at this level
    s.on('end', () => this.disconnect());
    s.on('data', (data: Buffer) => this._receive(data));
    s.on('error', (err: Error) => {
      s.destroy();
      if (this.retries <= RETRIES && !this.running) {
        this.socket = undefined;
        this.timer = setTimeout(() => this.connect(sockaddr), TIMEOUT);
      } else {
        this.disconnect();
        this.emitConnect(err);
      }
    });
    this.socket = s;
  }

  disconnect(): void {
    this.queue = [];
    this.retries = 0;
    this.running = false;
    this.buffer = Buffer.from('');
    if (this.timer) {
      clearTimeout(this.timer);
      this.timer = undefined;
    }
    if (this.socket) {
      this.socket.destroy();
      this.socket = undefined;
    }
  }

  /** Send Request */
  send(kind: string, id: string, request: string, data: json): void {
    this.queue.push({ cmd: kind, id, request, data });
    this._flush();
  }

  /** Signal ON */
  sigOn(id: string): void {
    this.queue.push({ cmd: 'SIGON', id });
    this._flush();
  }

  /** Signal ON */
  sigOff(id: string): void {
    this.queue.push({ cmd: 'SIGOFF', id });
    this._flush();
  }

  /** Kill Request */
  kill(id: string): void {
    this.queue.push({ cmd: 'KILL', id });
    this._flush();
  }

  /** Polling */
  poll(): void {
    this.queue.push('POLL');
    this._flush();
  }

  /** Shutdown the server */
  shutdown(): void {
    this.queue.push('SHUTDOWN');
    this._flush();
  }

  // --------------------------------------------------------------------------
  // --- Low-Level Management
  // --------------------------------------------------------------------------

  _flush(): void {
    if (this.running) {
      this.queue.forEach((cmd) => {
        this._send(Buffer.from(JSON.stringify(cmd), 'utf8'));
      });
      this.queue = [];
    }
  }

  _send(data: Buffer): void {
    const s = this.socket;
    if (s) {
      const len = data.length;
      const hex = Number(len).toString(16).toUpperCase();
      const padding = '0000000000000000';
      const header =
        len <= 0xFFF ? 'S' + padding.substring(hex.length, 3) :
          len <= 0xFFFFFFF ? 'L' + padding.substring(hex.length, 7) :
            'W' + padding.substring(hex.length, 15);
      s.write(Buffer.from(header + hex));
      s.write(data);
    }
  }

  _fetch(): undefined | string {
    const msg = this.buffer;
    const len = msg.length;
    if (len < 1) return;
    const hd = msg.readInt8(0);
    // 'S': 83, 'L': 76, 'W': 87
    const phex = hd === 83 ? 4 : hd === 76 ? 8 : 16;
    if (len < phex) return;
    const size = Number.parseInt(msg.slice(1, phex).toString('ascii'), 16);
    const offset = phex + size;
    if (len < offset) return;
    this.buffer = msg.slice(offset);
    return msg.slice(phex, offset).toString('utf8');
  }

  _receive(chunk: Buffer): void {
    this.buffer = Buffer.concat([this.buffer, chunk]);
    while (true) {
      const data = this._fetch();
      if (!data) break;
      try {
        // eslint-disable-next-line @typescript-eslint/no-explicit-any
        const cmd: any = JSON.parse(data);
        if (cmd !== null && typeof (cmd) === 'object') {
          switch (cmd.res) {
            case 'DATA': this.emitData(cmd.id, cmd.data); break;
            case 'ERROR': this.emitError(cmd.id, cmd.msg); break;
            case 'KILLED': this.emitKilled(cmd.id); break;
            case 'REJECTED': this.emitRejected(cmd.id); break;
            case 'SIGNAL': this.emitSignal(cmd.id); break;
            default:
              D.warn('Unknown command', cmd);
          }
        } else {
          switch (cmd) {
            case 'CMDLINEON': this.emitCmdLine(true); break;
            case 'CMDLINEOFF': this.emitCmdLine(false); break;
            default:
              D.warn('Misformed data', data);
          }
        }
      } catch (err) {
        D.warn('Misformed JSON', data, err);
      }
    }
  }

}

export const client: Client = new SocketClient();

// --------------------------------------------------------------------------
