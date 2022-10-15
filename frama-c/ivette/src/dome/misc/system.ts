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
   @packageDocumentation
   @module dome/system
*/

/* eslint-disable max-len */
/* eslint-disable no-console */

// --------------------------------------------------------------------------
// --- Evolved Spawn Process
// --------------------------------------------------------------------------

import _ from 'lodash';
import Emitter from 'events';
import Exec from 'child_process';
import fspath from 'path';
import fs from 'fs';

// --------------------------------------------------------------------------
// --- Platform Specificities
// --------------------------------------------------------------------------

let thePlatform = 'linux';
switch (process.platform) {
  case 'darwin':
    thePlatform = 'macos'; break;
  case 'win32':
    thePlatform = 'windows'; break;
  case 'aix':
  case 'freebsd':
  case 'linux':
  case 'openbsd':
  case 'sunos':
    thePlatform = 'linux'; break;
  default:
    console.warn(`Unkwnon '${process.platform}' (fallback to 'linux')`);
    thePlatform = 'linux'; break;
}

/**
   @summary System platform.
   @description
   Similar to `process.platform`, but fall into fewer categories:
   - `'macos'` for Mac OSX,
   - `'windows'` for Windows (32 or 64)
   - `'linux'` for most unix-like platforms

   Non-recognized platforms will fallback to `'linux'` with the
   emission of a warning.
*/
export const platform = thePlatform;

// --------------------------------------------------------------------------
// --- Logging
// --------------------------------------------------------------------------

/** Development mode flag */
export const DEVEL = process.env.NODE_ENV !== 'production';

// --------------------------------------------------------------------------
// --- System Emitter
// --------------------------------------------------------------------------

export const emitter = new Emitter();
emitter.setMaxListeners(250);

// --------------------------------------------------------------------------
// --- At Exit
// --------------------------------------------------------------------------

export type Callback = () => void;

const exitJobs: Callback[] = [];

/**
   Executes a routine at exit.

   Exceptions thrown by the function are captured and reported on the console.
 */
export function atExit(callback: Callback): void {
  exitJobs.push(callback);
}

/** Execute all pending exit jobs (and flush the list). */
export function doExit(): void {
  exitJobs.forEach((fn) => {
    try { fn(); }
    catch (err) { console.error('[Dome] atExit:', err); }
  });
  exitJobs.length = 0;
}

// --------------------------------------------------------------------------
// --- Command Line Arguments
// --------------------------------------------------------------------------

let COMMAND_WDIR = '.';
let COMMAND_ARGV: string[] = [];

function setCommandLine(argv: string[], wdir: string): void {
  COMMAND_ARGV = argv;
  COMMAND_WDIR = wdir;
}

/**
   Working directory (Application Window).

   This the current working directory from where the application window
   was opened.

   The function returns `undefined` until the `dome.command` event has
   been emitted from the `Main` process.

   See also [[dome.onCommand]]
*/
export function getWorkingDir(): string { return COMMAND_WDIR; }

/**
   Returns the current process ID.
 */
export function getPID(): number { return process.pid; }

/**
   Command-line arguments (Application Window).

   This the command-line arguments used to open the application window.

   The function returns `undefined` until the `dome.command`
   event has been emitted from the `Main` process.

   See also [[dome.onCommand]]
*/
export function getArguments(): string[] { return COMMAND_ARGV; }

// --------------------------------------------------------------------------
// --- File Join
// --------------------------------------------------------------------------

/**
   @summary Join file paths.
   @param {string} [...paths] - a sequence of path segments
   @return {string} the joined filepath
   @description
   Same as [Node `path.join`](https://nodejs.org/dist/latest-v12.x/docs/api/path.html#path_path_join_paths)
*/
export const { join } = fspath;

/**
   @summary Absolute (joined) file paths.
   @param {string} [...paths] - a sequence of path segments
   @return {string} the corresponding absolute path
   @description
   Same as [Node `path.resolve`](https://nodejs.org/dist/latest-v12.x/docs/api/path.html#path_path_resolve_paths)
*/
export const { resolve } = fspath;

/**
   @summary Dirname of path.
   @param {string} path - a file path
   @return {string} the dirname of the path
   @description
   Same as [Node `path.dirname`](https://nodejs.org/dist/latest-v12.x/docs/api/path.html#path_path_dirname_path)
*/
export const { dirname } = fspath;

/**
   @summary Basename of path.
   @param {string} path - a file path
   @param {string} [ext] - file extension to remove
   @return {string} the basename of the path
   @description
   Same as [Node `path.basename`](https://nodejs.org/dist/latest-v12.x/docs/api/path.html#path_path_basename_path_ext)
*/
export const { basename } = fspath;

/**
   @summary File extension of path.
   @param {string} path - a file path
   @return {string} the file extension of the path
   @description
   Same as [Node `path.extname`](https://nodejs.org/dist/latest-v12.x/docs/api/path.html#path_path_extname_path)
*/
export const { extname } = fspath;

// --------------------------------------------------------------------------
// --- File Stats
// --------------------------------------------------------------------------

/**
   Returns an `fs.stat()` object for the path.

   Promisified [Node `fs.stat`](https://nodejs.org/dist/latest-v12.x/docs/api/fs.html#fs_fs_stat_path_callback).

   Returns a (promised) [Node `fs.Stats`](https://nodejs.org/dist/latest-v12.x/docs/api/fs.html#fs_class_fs_stats) object,
   including the following usefull fields and methods (and more):
   - `stats.isFile()` returns `true` for a regular file
   - `stats.isDirectory()` returns `true` for a directory
   - `stats.mode` the bitfield (integer) of the file access mode
   - `stats.size` the size of the file (in bytes)
   - `stats.mtime` last modification time stamp (javascript `Date` object)

   The promise is rejected if the file does not exists.
*/
export function fileStat(path: string): Promise<fs.Stats> {
  return new Promise((result, reject) => {
    fs.stat(path, (err, data) => (err ? reject(err) : result(data)));
  });
}

/**
   Checks if a path exists and is a regular file
   (Synchronous check).
*/
export function isFile(path: string): boolean {
  try {
    return !!path && fs.statSync(path).isFile();
  } catch (_err) {
    return false;
  }
}

/**
   Checks if a path exists and is a directory
   (Synchronous check).
*/
export function isDirectory(path: string): boolean {
  try {
    return !!path && fs.statSync(path).isDirectory();
  } catch (_err) {
    return false;
  }
}

/**
   Checks if a path exists and is a file or directory
   (Synchronous check).
*/
export function exists(path: string): boolean {
  try {
    if (!path) return false;
    const stats = fs.statSync(path);
    return stats.isFile() || stats.isDirectory();
  } catch (_err) {
    return false;
  }
}

// --------------------------------------------------------------------------
// --- Read File
// --------------------------------------------------------------------------

/**
   Reads a textual file contents.

   Promisified `fs.readFile` using `utf-8` encoding.
 */
export function readFile(path: string): Promise<string> {
  return fs.promises.readFile(path, { encoding: 'utf-8' });
}

// --------------------------------------------------------------------------
// --- Write File
// --------------------------------------------------------------------------

/**
   Writes a textual content in a file.

   Promisified `fs.writeFile` using `utf-8` encoding.
 */
export async function writeFile(path: string, content: string): Promise<void> {
  return fs.promises.writeFile(path, content, { encoding: 'utf-8' });
}

// --------------------------------------------------------------------------
// --- Copy File
// --------------------------------------------------------------------------

/**
   Copy file to a new path.
   @param srcPath - the source file path
   @param tgtPath - the target file path

   Promisified `fs.copyFile`.
 */
export async function copyFile(srcPath: string, tgtPath: string): Promise<void> {
  return fs.promises.copyFile(srcPath, tgtPath);
}

// --------------------------------------------------------------------------
// --- Read Directory
// --------------------------------------------------------------------------

/**
   Reads a directory.
   @returns directory contents (local names)

   Promisified `fs.readdir`.

   Uses `utf-8` encoding to obtain (relative) file names instead of byte buffers.
   On MacOS, `.DS_Store` entries are filtered out.
*/
export async function readDir(path: string): Promise<string[]> {
  const filterDir = (f: string): boolean => f !== '.DS_Store';
  const entries = await fs.promises.readdir(path, { encoding: 'utf-8', withFileTypes: true });
  return entries.map((fn) => fn.name).filter(filterDir);
}

// --------------------------------------------------------------------------
// --- Make Directory
// --------------------------------------------------------------------------

const CREATE_DIR_OPTIONS: fs.MakeDirectoryOptions = {
  recursive: true,
  mode: 0o777,
};

/**
   Creates a new directory. Defaults permission is recursive `0o777`.

   Promisified
   [Node `fs.mkdir`](https://nodejs.org/dist/latest-v12.x/docs/api/fs.html#fs_fs_mkdir_path_options_callback).

*/
export function mkDir(
  path: string,
  options?: number | fs.MakeDirectoryOptions,
): Promise<void> {
  return new Promise((result, reject) => {
    fs.mkdir(path, options ?? CREATE_DIR_OPTIONS, (err) => {
      if (err) reject(err); else result();
    });
  });
}

// --------------------------------------------------------------------------
// --- Remove File
// --------------------------------------------------------------------------

/**
   Remove a file.

   Promisified
   [Node `fs.unlink`](https://nodejs.org/dist/latest-v12.x/docs/api/fs.html#fs_fs_unlink_path_callback)
*/
export function remove(path: string): Promise<void> {
  return new Promise((result, reject) => {
    fs.unlink(path, (err) => (err ? reject(err) : result()));
  });
}

// --------------------------------------------------------------------------
// --- Remove Directory
// --------------------------------------------------------------------------

// Not (yet) implemented in Node for Electron
function rmDirNonRec(path: string): Promise<void> {
  return new Promise((result, reject) => {
    fs.rmdir(path, (err) => (err ? reject(err) : result()));
  });
}

// Not (yet) implemented in Node for Electron
async function rmDirRec(path: string): Promise<void> {
  try {
    const stats = fs.statSync(path);
    if (stats.isFile()) {
      await remove(path);
      return;
    }
    if (stats.isDirectory()) {
      const rmDirSub = (name: string): void => {
        rmDirRec(fspath.join(path, name));
      };
      const entries = await readDir(path);
      await Promise.all(entries.map(rmDirSub));
      await rmDirNonRec(path);
      return;
    }
  } catch (err) {
    if (DEVEL) console.warn('[Dome.rmDirRec]', err);
  }
}

export interface RmDirOptions {
  recursive: boolean;
}

/**
   Removes a directory.

   Promisified
   [Node `fs.rmdir`](https://nodejs.org/dist/latest-v12.x/docs/api/fs.html#fs_fs_mkdir_path_options_callback).

*/
export function rmDir(path: string, options?: RmDirOptions): Promise<void> {
  return (options?.recursive ?? true) ? rmDirRec(path) : rmDirNonRec(path);
}

// --------------------------------------------------------------------------
// --- Rename File
// --------------------------------------------------------------------------

/**
   Renames of file of direcory.

   Promisified
   [Node `fs.rename`](https://nodejs.org/dist/latest-v12.x/docs/api/fs.html#fs_fs_rename_oldpath_newpath_callback)
*/
export function rename(oldPath: string, newPath: string): Promise<void> {
  return new Promise((result, reject) => {
    fs.rename(oldPath, newPath, (err) => (err ? reject(err) : result()));
  });
}

// --------------------------------------------------------------------------
// --- Child Process
// --------------------------------------------------------------------------

const childprocess = new Map<number, Exec.ChildProcess>();

atExit(() => {
  childprocess.forEach((process, pid) => {
    try { process.kill(); }
    catch (err) {
      if (DEVEL) console.warn('[Dome.atExit] killing process', pid, err);
    }
  });
});

export type StdPipe = { path?: string | undefined; mode?: number; pipe?: boolean };
export type StdOptions = undefined | 'null' | 'ignore' | 'pipe' | StdPipe;

type StdIO = { io: number | 'pipe' | 'ignore' | 'ipc'; fd?: number };

function stdSpec(spec: StdOptions, isOutput: boolean): StdIO {
  switch (spec) {
    case undefined:
      return { io: isOutput ? 'pipe' : 'ignore' };
    case null:
    case 'null':
    case 'ignore':
      return { io: 'ignore' };
    case 'pipe':
      return { io: 'pipe' };
    default: {
      let fd: number | undefined;
      if (spec.path) fd = fs.openSync(spec.path, spec.mode || (isOutput ? 'w' : 'r'));
      return (isOutput && spec.pipe) ? { io: 'pipe', fd } : { io: fd ?? 'ignore' };
    }
  }
}

interface Readable {
  pipe(out: fs.WriteStream): void;
  unpipe(out: fs.WriteStream): void;
}

function pipeTee(std: Readable, fd: number): void {
  if (!fd) return;
  const out = fs.createWriteStream('<ignored>', { fd, encoding: 'utf-8' });
  out.on('error', (err) => {
    console.warn('[Dome] can not pipe:', err);
    std.unpipe(out);
  });
  std.pipe(out);
}

export interface ProcessOptions {
  /** Defaults to the application current working directory. */
  cwd?: string;
  env?: { [VAR: string]: string };
  stdin?: StdOptions;
  stdout?: StdOptions;
  stderr?: StdOptions;
  /** Use a Node child process with inter-node process RPC. */
  fork?: boolean;
}

/**
   Spawn a child process.

   Based on [Node `child_process.spawn`](https://nodejs.org/dist/latest-v12.x/docs/api/child_process.html#child_process_child_process_spawn_command_args_options). The promised process object is a regular [Node `ChildProcess`](https://nodejs.org/api/child_process.html#child_process_class_childprocess) object, for which we recall the main useful methods below:

   - `child.on('exit',(code) => {...})` emitted event when the process is terminated
   - `child.on('close',(code) => {...})` emitted event when the process is fully terminated (all pipes closed)
   - `child.on('message',(...data) => {...})` emitted from the _forked_ process (if applicable)
   - `child.stdout.on('data',(text) => {...})` emitted when the process writes on piped stdout (receives `UTF-8` strings)
   - `child.stderr.on('data',(text) => {...})` emitted when the process writes on piped stderr (receives `UTF-8` strings)
   - `child.kill()` sends a `'SIGTERM'` unix message to the process

   Options is an object similar to the original Node options, with small adaptations.
   The possible option fields are described as follows:

   Environment variables are _added_ to the default `process.env` environment.

   All pipes have their encoding set to `UTF-8`,
   hence all callbacks on process events will receive natural strings instead of raw byte buffers.

   When specifying a file for a process standard stream, an optional mode can be specified.
   Default is `'r'` for input streams and `'w'` for output ones.
   If option `pipe:true` is provided (output streams only), the output of the process is
   also piped through the Process object. The file-path is relative to the current working directory
   of the _application_, not be confused with the `cwd` option of the spawned command.

   When the `fork` flag is set, the child process is spawned using
   [Node `child_process.fork`](https://nodejs.org/dist/latest-v12.x/docs/api/child_process.html#child_process_child_process_fork_modulepath_args_options). This enables Node inter-process communication _via_ the
   `process.send()` and `process.on('message')` methods of the child process object.
*/

export function spawn(
  command: string,
  args?: string[],
  options?: ProcessOptions,
): Promise<Exec.ChildProcess> {
  return new Promise((result, reject) => {

    const cwd = options ? options.cwd : undefined;
    const opt = options ? options.env : undefined;
    const env = // Forces 'PWD' env. variable for executing a non-shell process
      (cwd || opt) ? { ...process.env, ...opt, 'PWD': cwd } : undefined;
    const stdin = stdSpec(options && options.stdin, false);
    const stdout = stdSpec(options && options.stdout, true);
    const stderr = stdSpec(options && options.stderr, true);
    const stdio = [stdin.io, stdout.io, stderr.io];
    const fopt: Exec.ForkOptions = { cwd, env, stdio };
    const forked = options && options.fork;
    const cargs = args ? args.slice() : [];
    let child: Exec.ChildProcess | undefined;

    if (forked) {
      stdio.push('ipc');
      child = Exec.fork(command, cargs, fopt);
    } else {
      child = Exec.spawn(command, cargs, fopt);
    }

    if (!child) reject(new Error(
      `[Dome] Unable to create process ('${command}')`,
    ));

    const { pid } = child;

    if (!pid) {
      // Must defer rejection, otherwise an uncaught exception is raised.
      child.on('error', (err) => reject(err));
      return;
    }

    childprocess.set(pid, child);
    child.on('exit', () => childprocess.delete(pid));

    const out = child.stdout;
    const err = child.stderr;

    if (out && stdout.fd) {
      out.setEncoding('utf-8');
      pipeTee(out, stdout.fd);
    }
    if (err && stderr.fd) {
      err.setEncoding('utf-8');
      pipeTee(err, stderr.fd);
    }

    result(child);
  });
}

// --------------------------------------------------------------------------
// --- Window Management
// --------------------------------------------------------------------------

const WINDOW_APPLICATION_ARGV = '--dome-application-window';
const WINDOW_PREFERENCES_ARGV = '--dome-preferences-window';

// --------------------------------------------------------------------------
// --- Only used for inter-module initialisation
// --------------------------------------------------------------------------

export default {
  setCommandLine,
  WINDOW_APPLICATION_ARGV,
  WINDOW_PREFERENCES_ARGV,
};

// --------------------------------------------------------------------------
