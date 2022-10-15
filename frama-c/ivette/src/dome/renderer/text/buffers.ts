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

/* eslint-disable @typescript-eslint/no-explicit-any */

// --------------------------------------------------------------------------
// --- Text Documents
// --------------------------------------------------------------------------

/**
   @packageDocumentation
   @module dome/text/buffers
*/

import Emitter from 'events';
import CodeMirror from 'codemirror/lib/codemirror';
import { Debug } from 'dome';

const D = new Debug('Dome.text');

export type Range = { from: CodeMirror.Position; to: CodeMirror.Position };

export interface Decorator {
  /** @return a className to apply on markers with the identifier. */
  (id: string): string | undefined;
}

export interface TextMarkerProxy {
  clear(): void;
  changed(): void;
  find(): Range | undefined;
}

/**
   Text Marker options.

   Inherits CodeMirror
   [TextMerkerOptions](https://codemirror.net/doc/manual.html#api_marker).
 */
export interface MarkerProps extends CodeMirror.TextMarkerOptions {
  id?: string;
  hover?: boolean;
  className?: string;
}

export interface CSSMarker {
  /** Hover class `'dome-xHover-nnn'` */
  classNameId: string;
  /** Marker id */
  id: string | undefined;
  /** Hovered marker */
  hover: boolean;
  /** Size in character */
  length: number;
}

// --------------------------------------------------------------------------
// --- Batched Update
// --------------------------------------------------------------------------

const BATCH_OPS = 500;
const BATCH_DELAY = 5;
const BATCH_RMAX = 1000; // max tag range for sorting
const BATCH_MARGINS = 20; // visible lines above the viewport

interface MarkerOptions {
  id?: string;
  hover?: boolean;
  className?: string;
  options: CodeMirror.TextMarkerOptions;
}

interface StackedMarker extends MarkerOptions {
  startIndex: number;
}

interface BufferedMarker extends MarkerOptions {
  startIndex: number;
  stopIndex: number;
}

type BufferedTag = BufferedMarker | undefined;

function rankTag(lmin: number, lmax: number, tg: BufferedTag): number {
  if (tg && (lmin <= tg.stopIndex || tg.startIndex <= lmax)) {
    const size = tg.stopIndex - tg.startIndex;
    return size < BATCH_RMAX ? size : BATCH_RMAX;
  }
  return BATCH_RMAX;
}

const byVisibleTag =
  (lmin: number, lmax: number) =>
    (a: BufferedTag, b: BufferedTag): number => (
      rankTag(lmin, lmax, a) - rankTag(lmin, lmax, b)
    );

// --------------------------------------------------------------------------
// --- Buffer
// --------------------------------------------------------------------------

export type TextMarker = CodeMirror.TextMarker<CodeMirror.MarkerRange>;

export interface RichTextBufferProps {

  /**
   * CodeMirror [mode](https://codemirror.net/mode/index.html) specification.
   */
  mode?: any;

  /** Maximum number of lines in the buffer. */
  maxlines?: number;

}

/**
   Rich Text Content and State.

   A buffer encapsulate a CodeMirror document instance inside an standard
   Node event emitter. CodeMirror signals are automatically linked back to
   the event emitter (on a lazy basis).

   All buffer modifications are stacked and executed asynchronously inside
   CodeMirror batched operations to increase performance.

   The `maxlines` will control the maximum number of lines kept in the buffer.
   By default, it is set to `10000`, but you can use `null`, `0` or any negative
   value to disable this behavior. See also `this.setMaxlines()` method.

   Additionnaly, a Buffer maintains an _edited_ state internally that can
   be manually updated, and that is automatically set to `true` when the
   underlying CodeMirror document is changed. It is associated to an `'edited'`
   event of the buffer, and can be used to manage the « Saved » / « Not-Saved »
   state of an editor, for instance.

   Typically, a sequence of changed events would fire a unique `'edited'` buffer
   event, untill `setEdited(false)` is invoked. The `clear()` method also resets
   the _edited_ state to `false`, but sill emit an `'edited'` event if the
   buffer was not empty.

   Buffers can also be updated programmatically by various methods. In addition
   to specified CodeMirror modes, you can also attach text markers
   programmatically with a push/pop API.

   Text markers can be associated with an identifier, that can be used for
   dynamic highlighting, called Decorations. Decorations are class names that
   add styling attributes upon the current mode. Typically, consider only using
   background colors, underlines and/or strike-through for decorations, since
   font styles and colors are likely to be managed by CodeMirror modes, unless
   you know exactly what your are doing.

   The `setDecorator` method can be used to set or update
   the highlighting function that computes the decoration of a text marker
   from its identifier. When the decorations may have change, you shall either
   set again the highlighting function with a call to `setDecorator()` or call
   the `updateDecorations()` method. This also triggers the `'decorated'` event.

 */

export class RichTextBuffer extends Emitter {

  private document: CodeMirror.Doc;
  private maxlines = 10000;
  private editors: CodeMirror.Editor[] = [];
  private cacheIndex = 0; // document index, negative if not computed
  private bufferedText: string; // buffered text to append
  private bufferedTags: BufferedTag[];
  private stacked: StackedMarker[] = [];
  private batched = false;

  // Indexed by CSS property dome-xHover-nnnn
  private cssmarkers = new Map<string, CSSMarker>();

  // Indexed by marker user identifier
  private textmarkers = new Map<string, TextMarker[]>();

  private decorator?: Decorator;
  private edited = false;
  private focused = false;
  private markid = 0;

  constructor(props: RichTextBufferProps = {}) {
    super();
    const { mode, maxlines } = props;
    this.document = new CodeMirror.Doc('', mode);
    this.cacheIndex = -1;
    this.bufferedTags = [];
    this.bufferedText = '';
    this.setMaxlines(maxlines);
    this.setEdited = this.setEdited.bind(this);
    this.setFocused = this.setFocused.bind(this);
    this.clear = this.clear.bind(this);
    this.append = this.append.bind(this);
    this.setValue = this.setValue.bind(this);
    this.getValue = this.getValue.bind(this);
    this.updateDecorations = this.updateDecorations.bind(this);
    this.onChange = this.onChange.bind(this);
    this.doBatch = this.doBatch.bind(this);
    this.log = this.log.bind(this);
  }

  /**
     Internal CodeMirror
     [document](https://codemirror.net/doc/manual.html#api_doc) instance.
  */
  getDoc(): CodeMirror.Doc { return this.document; }

  // --------------------------------------------------------------------------
  // --- Buffer Manipulation
  // --------------------------------------------------------------------------

  /** Clear buffer contents and resets _edited_ state. */
  clear(): void { this.setValue(''); }

  /**
     Writes in the buffer. All parameters are converted to string and joined
     with spaces.  The generated change event has origin `'buffer'` and it does
     not modifies the _edited_ internal state.
  */
  append(...values: any[]): void {
    if (values.length > 0) {
      const text = values.join(' ');
      this.bufferedText += text;
      this.armBatch();
    }
  }

  /**
     Starts a new line in the buffer. If the current buffer content does not
     finish at the beginning of a fresh line, inserts a newline character.
  */
  flushline(): void {
    const doc = this.document;
    const buf = this.bufferedText;
    if (buf === '') {
      const start = doc.posFromIndex(Infinity);
      if (start.ch > 0) doc.replaceRange('\n', start, undefined, 'buffer');
      this.cacheIndex = -1;
    } else if (buf[buf.length - 1] !== '\n') this.bufferedText += '\n';
  }

  /**
     Appends with newline and auto-scrolling. This is a short-cut to
     `flushline()` followed by `append(...value,'\n')` and `scroll()`.
   */
  log(...values: any[]): void {
    this.flushline();
    this.append(...values, '\n');
    this.scroll();
  }

  /**
     Replace all textual content with the given string.
     Also remove all markers.
   */
  setValue(txt = ''): void {
    this.document.setValue(txt);
    this.cssmarkers.clear();
    this.textmarkers.clear();
    this.stacked = [];
    this.bufferedTags = [];
    this.bufferedText = '';
    this.cacheIndex = 0;
    this.edited = false;
    this.focused = false;
    this.markid = 0;
  }

  /** Return the textual contents of the buffer. */
  getValue(): string { return this.document.getValue(); }

  // --------------------------------------------------------------------------
  // ---  Text Markers
  // --------------------------------------------------------------------------

  /**
     Opens a text marker.

     Opens a text marker at the current (end) position in the buffer.

     The text marker is stacked and would be actually created on the matching
     [[closeTextMarker]] call. It will be applied to the full range of text
     inserted between its associated [[openTextMarker]] and [[closeTextMarker]]
     calls.

     The returned text marker is actually a _proxy_ to the text marker that will
     be eventually created by [[closeTextMarker]]. Its methods are automatically
     forwarded to the actual `CodeMirror.TextMarker` instance, once created.
     Hence, you can safely invoke these methods on either the _proxy_ or the
     _final_ text marker at your convenience.
  */
  openTextMarker(props: MarkerProps): void {
    const { id, hover, className, ...options } = props;
    const startIndex = this.getLastIndex() + this.bufferedText.length;
    this.stacked.push({ startIndex, id, hover, className, options });
  }

  /**
     Closes the last opened marker.
  */
  closeTextMarker(): void {
    const tag = this.stacked.pop();
    if (tag) {
      const stopIndex = this.getLastIndex() + this.bufferedText.length;
      this.bufferedTags.push({ stopIndex, ...tag });
      this.armBatch();
    }
  }

  /** Lookup for the text markers associated with a marker identifier.
      Remove the marked tags from the buffered tag array. */
  findTextMarker(id: string): TextMarker[] {
    this.doFlushText();
    this.bufferedTags.forEach((tg, idx) => {
      if (tg?.id === id) {
        this.doMark(tg);
        this.bufferedTags[idx] = undefined;
      }
    });
    return this.textmarkers.get(id) ?? [];
  }

  /** Lopokup for a hover class. */
  findHover(className: string): CSSMarker | undefined {
    return this.cssmarkers.get(className);
  }

  // --------------------------------------------------------------------------
  // --- Highlighter
  // --------------------------------------------------------------------------

  /**
     Define highlighter.

     @param fn - highlighter, `fn(id)` shall return a className to apply
     on text markers with the provided identifier.
  */
  setDecorator(fn: Decorator): void {
    this.decorator = fn;
    this.emit('decorated');
  }

  /**
     Current highlighter.
   */
  getDecorator(): Decorator | undefined { return this.decorator; }

  /**
     Rehighlight document.

     Emits the `'decorated'` event to make editors
     updating the decorations of identified text markers.

     This can be used when decoration shall be re-computed,
     even if the decoration function was not modified.

     The method is bound to `this`.
  */
  updateDecorations(): void { this.emit('decorated'); }

  // --------------------------------------------------------------------------
  // --- Edited State
  // --------------------------------------------------------------------------

  /**
     Set edited state.

     The method is automatically invoked by editor views when the user actually
     edit the document.  The state is _not_ modified when modifying the document
     from buffer's own methods, _eg._ `append()` and `clear()`.

     The method fires the `'edited'` event on modifications.  This method is
     bound to `this`, hence `this.setEdited` can be used as a valid callback
     function.

     @param state - the new edited state (defaults to `true`).
  */
  setEdited(state = true): void {
    if (state !== this.edited) {
      this.edited = state;
      this.emit('edited', state);
    }
  }

  /**
     Set focused state.

     The method is automatically invoked by editor views when they gain or lose
     focus or when the user actually interact with the view,
     eg. mouse-scrolling, edition, cursor move, etc.  The escape key `ESC`
     explicitly relax the _focused_ state, although the editor view might
     actually keep the _focus_.

     When a buffer is _focused_, shrinking and auto-scrolling are temporarily
     deactivated to avoid confusing user's experience.

     The method fires `'focused'` events on modifications. This method is bound
     to `this`, hence `this.setEdited` can be used as a valid callback function.

     @param focus - the new focused state (defaults to `true`).
  */
  setFocused(state = true): void {
    if (state !== this.focused) {
      this.focused = state;
      this.emit('focused', state);
      this.doShrink();
    }
  }

  /** Returns the current _edited_ state. */
  isEdited(): boolean { return this.edited; }

  /** Returns the current _focused_ state. */
  isFocused(): boolean { return this.focused; }

  // --------------------------------------------------------------------------
  // --- Document Scrolling
  // --------------------------------------------------------------------------

  /**
     Set (or unset) the maximum number of lines.

     By default, the maximum number of lines is set to `10,000` to avoid
     unwanted memory leaks. Setting `null`, `0` of any negative value cancel the
     management of maximum number of lines.

     Although CodeMirror is powerfull enough to manage huge buffers, you should
     turn this limit _off_ with care.
  */
  setMaxlines(maxlines = 10000): void {
    this.maxlines = maxlines > 0 ? 1 + maxlines : 0;
    this.doShrink();
  }

  /**
     Requires all connected views to scroll to the
     specified line or identified marker.

     @param position -
     defaults to the end of buffer (when not focused).
  */
  scroll(position?: string | number): void {
    if (position === undefined) {
      if (!this.focused) {
        this.doFlushText();
        this.emit('scroll', this.document.lastLine());
      }
    } else if (typeof position === 'number') {
      this.doFlushText();
      this.emit('scroll', position);
    } else if (typeof position === 'string') {
      let line = Infinity;
      this.findTextMarker(position).forEach((tm) => {
        const rg = tm.find();
        if (rg && rg.from) {
          const ln = rg.from.line;
          if (ln < line) line = ln;
        }
      });
      if (line !== Infinity)
        this.emit('scroll', line);
    }
  }

  /**
     Requires all connected views to select the specified line and to place it
     at the top of their displays.

     @param line - the line number to select
  */
  setCursorOnTop(line: number): void {
    this.forEach((cm) => {
      cm.setCursor(cm.lastLine());
      cm.setCursor(line - 1);
    });
  }

  // --------------------------------------------------------------------------
  // --- Document Linking
  // --------------------------------------------------------------------------

  private onChange(
    _editor: CodeMirror.Editor,
    change: CodeMirror.EditorChange,
  ): void {
    if (change.origin !== 'buffer') {
      this.setEdited(true);
      this.cacheIndex = -1;
    }
    this.emit('change');
  }

  /**
     Binds this buffer to a CodeMirror instance.

     Uses CodeMirror linked documents to allow several CodeMirror instances to
     be linked to the same buffer. Can be released with [[unlink]].

     @param cm - code mirror instance to link this document in.
  */
  link(cm: CodeMirror.Editor): void {
    const newDoc = this.document.linkedDoc(
      { sharedHist: true, mode: undefined },
    );
    cm.swapDoc(newDoc);
    cm.on('change', this.onChange);
    this.editors.push(cm);
  }

  /**
     Release a linked CodeMirror document previously linked with [[link]].
     @param cm - the code mirror instance to unlink
  */
  unlink(cm: CodeMirror.Editor): void {
    const oldDoc = cm.getDoc();
    this.document.unlinkDoc(oldDoc);
    this.editors = this.editors.filter((cm0) => {
      if (cm === cm0) {
        cm.off('change', this.onChange);
        return false;
      }
      return true;
    });
  }

  /**
     Iterates over each linked CodeMirror instances

     The operation `fn` is performed on each code mirror
     instance currently linked to this buffer.

     Exceptions raised by `fn` are catched and dumped in the console.
   */
  forEach(fn: (editor: CodeMirror.Editor) => void): void {
    this.editors.forEach((cm) => {
      try { fn(cm); } catch (e) { D.error(e); }
    });
  }

  // --------------------------------------------------------------------------
  // --- Update Operations
  // --------------------------------------------------------------------------

  /* Append Operation */
  private doFlushText(): void {
    const text = this.bufferedText;
    if (text.length > 0) {
      this.bufferedText = '';
      const doc = this.document;
      const start = doc.posFromIndex(Infinity);
      doc.replaceRange(text, start, undefined, 'buffer');
      this.cacheIndex = -1;
      this.doShrink();
    }
  }

  /* Shrink Operation */
  private doShrink(): void {
    const lines = this.document.lineCount();
    if (lines > this.maxlines) {
      const p = this.document.firstLine();
      const q = p + lines - this.maxlines;
      this.document.replaceRange(
        '',
        { line: p, ch: 0 },
        { line: q, ch: 0 },
        'buffer',
      );
      this.cacheIndex = -1;
    }
  }

  /* Close Operation */
  private doMark(tag: BufferedMarker): void {
    const { id, hover, className, startIndex, stopIndex } = tag;
    let markerId;
    if (id || hover) {
      markerId = `dome-xHover-${this.markid++}`;
      const cmark = {
        id,
        classNameId: markerId,
        hover: hover ?? (id !== undefined),
        length: stopIndex - startIndex,
      };
      this.cssmarkers.set(markerId, cmark);
    }
    const fullClassName = [
      'dome-xMarked',
      id && (`dome-xMark-${id}`),
      markerId,
      className,
    ].filter((s) => !!s).join(' ');
    const options = {
      shared: true,
      className: fullClassName,
      ...tag.options,
    };
    const doc = this.document;
    const start = doc.posFromIndex(startIndex);
    const stop = doc.posFromIndex(stopIndex);
    const marker = doc.markText(start, stop, options);
    if (id) {
      const markers = this.textmarkers;
      const ms = markers.get(id);
      if (ms === undefined)
        markers.set(id, [marker]);
      else
        ms.push(marker);
    }
  }

  private doFilterTags(): BufferedTag[] {
    const tgs = this.bufferedTags;
    if (tgs.length > 0 && this.editors.length > 0) {
      let lmin = Infinity;
      let lmax = 0;
      this.forEach((cm) => {
        const { from: fr, to } = cm.getViewport();
        if (to > lmax) lmax = to;
        if (fr < lmin) lmin = fr;
      });
      if (lmin <= lmax) tgs.sort(byVisibleTag(lmin, lmax + BATCH_MARGINS));
    }
    return tgs.splice(0, BATCH_OPS);
  }

  private getLastIndex(): number {
    if (this.cacheIndex < 0) {
      const doc = this.document;
      const line = doc.lastLine() + 1;
      this.cacheIndex = doc.indexFromPos({ line, ch: 0 });
    }
    return this.cacheIndex;
  }

  // --------------------------------------------------------------------------
  // --- Batched Operations
  // --------------------------------------------------------------------------

  private armBatch(): void {
    if (!this.batched) {
      this.batched = true;
      setTimeout(this.doBatch, BATCH_DELAY);
    }
  }

  /* Batch Operation */
  private doBatch(): void {
    this.batched = false;
    if (!this.bufferedText.length && !this.bufferedTags.length) return;
    try {
      // Start Operations
      this.forEach((cm) => cm.startOperation());
      // Flush Text
      this.doFlushText();
      // Mark Tags
      this.doFilterTags().forEach((tg) => { if (tg) this.doMark(tg); });
      // End Operations
      this.forEach((cm) => cm.endOperation());
    } finally {
      if (this.bufferedTags.length > 0)
        this.armBatch();
    }
  }

}

// --------------------------------------------------------------------------
