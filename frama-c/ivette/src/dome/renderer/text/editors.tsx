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
// --- Text Documents
// --------------------------------------------------------------------------

/**
   @packageDocumentation
   @module dome/text/editors
*/

import _ from 'lodash';
import React from 'react';
import * as Dome from 'dome';
import * as Themes from 'dome/themes';
import { Vfill } from 'dome/layout/boxes';
import CodeMirror, { EditorConfiguration } from 'codemirror/lib/codemirror';
import { RichTextBuffer, CSSMarker, Decorator } from './buffers';

import './style.css';
import './dark-code.css';
import 'codemirror/lib/codemirror.css';

const CSS_HOVERED = 'dome-xText-hover';
const CSS_SELECTED = 'dome-xText-select';

const D = new Dome.Debug('Dome');

/* --------------------------------------------------------------------------*/
/* --- View Properties                                                   --- */
/* --------------------------------------------------------------------------*/

export interface MarkerCallback {
  (id: string, meta?: boolean): void;
}

/**
   Text Editor configuration.

   Inherits CodeMirror
   [EditorConfiguration](https://codemirror.net/doc/manual.html#config)
   options.
 */

export interface TextProps extends CodeMirror.EditorConfiguration {

  /** The buffer to view. */
  buffer: RichTextBuffer | undefined;

  /** The currently selected marker identifier. */
  selection?: string;

  /** Callback on hovered marker, if some. */
  onHover?: (id?: string) => void;

  /** Callback on identified marker selection. */
  onSelection?: MarkerCallback;

  /** Callback on identified marker right-click. */
  onContextMenu?: MarkerCallback;

  /** Font Size. */
  fontSize?: number;

  /** Display or hide the component (true by default). */
  display?: boolean;

  /** Additional className for the text container. */
  className?: string;

  /** Additional style. */
  style?: React.CSSProperties;

}

/* --------------------------------------------------------------------------*/
/* --- CodeMirror Configuration Utils                                     ---*/
/* --------------------------------------------------------------------------*/

function getConfig(props: TextProps): CodeMirror.EditorConfiguration {
  const {
    buffer,
    selection,
    onSelection,
    onContextMenu,
    fontSize,
    ...config
  } = props;
  return config;
}

type MouseEvt = React.MouseEvent<HTMLDivElement, MouseEvent>;
type CMoption = keyof EditorConfiguration;

function forEachOption(
  config: EditorConfiguration,
  fn: (opt: CMoption) => void,
): void {
  (Object.keys(config) as (keyof EditorConfiguration)[]).forEach(fn);
}

interface _Decoration {
  classNameId: string;
  decoration: string | undefined;
}

// --------------------------------------------------------------------------
// --- Code Mirror Instance Wrapper
// --------------------------------------------------------------------------

class CodeMirrorWrapper extends React.Component<TextProps> {

  private currentParent?: Element | null;
  private currentHeight?: number;
  private currentWidth?: number;
  private rootElement: HTMLDivElement | null = null;
  private codeMirror?: CodeMirror.Editor;
  private refreshPolling?: NodeJS.Timeout;

  // Currently hovered 'dome-xHover-nnn'
  private marker?: CSSMarker;

  // Maps hovered 'dome-xMark-id' to their decorations
  private decorations = new Map<string, string>();

  constructor(props: TextProps) {
    super(props);
    this.mountPoint = this.mountPoint.bind(this);
    this.refresh = this.refresh.bind(this);
    this.autoRefresh = this.autoRefresh.bind(this);
    this.onBlur = this.onBlur.bind(this);
    this.onFocus = this.onFocus.bind(this);
    this.onScroll = this.onScroll.bind(this);
    this.onClick = this.onClick.bind(this);
    this.onContextMenu = this.onContextMenu.bind(this);
    this.onMouseMove = this.onMouseMove.bind(this);
    this.handleKey = this.handleKey.bind(this);
    this.handleUpdate = this.handleUpdate.bind(this);
    this.handleHover = _.throttle(this.handleHover, 50);
    this.handleScrollTo = this.handleScrollTo.bind(this);
  }

  // --------------------------------------------------------------------------
  // --- Mounting
  // --------------------------------------------------------------------------

  mountPoint(elt: HTMLDivElement | null): void {
    this.rootElement = elt;
    if (elt !== null) {
      // Mounting...
      const { buffer } = this.props;
      const config = getConfig(this.props);
      this.codeMirror = CodeMirror(elt, { value: '' });
      if (buffer) {
        buffer.link(this.codeMirror);
        buffer.on('decorated', this.handleUpdate);
        buffer.on('scroll', this.handleScrollTo);
      }
      // Passing all options to constructor does not work (Cf. CodeMirror's BTS)
      forEachOption(
        config, (opt) => this.codeMirror?.setOption(opt, config[opt]),
      );
      // Binding events to view
      this.codeMirror.on('update', this.handleUpdate);
      this.codeMirror.on('keyHandled', this.handleKey);
      Dome.update.on(this.refresh);
      // Auto refresh
      this.refreshPolling = setInterval(this.autoRefresh, 250);
      this.handleUpdate();
    } else {
      // Unmounting...
      if (this.refreshPolling) {
        clearInterval(this.refreshPolling);
        this.refreshPolling = undefined;
      }
      Dome.update.off(this.refresh);
      const { buffer } = this.props;
      if (this.codeMirror && buffer) {
        buffer.unlink(this.codeMirror);
        buffer.off('decorated', this.handleUpdate);
        buffer.off('scroll', this.handleScrollTo);
      }
      this.codeMirror = undefined;
      this.marker = undefined;
      this.decorations.clear();
    }
  }

  // --------------------------------------------------------------------------
  // --- Auto Refresh
  // --------------------------------------------------------------------------

  refresh(): void {
    const elt = this.rootElement;
    const cm = this.codeMirror;
    if (cm && elt) {
      this.currentWidth = elt.offsetWidth;
      this.currentHeight = elt.offsetHeight;
      this.currentParent = elt.offsetParent;
      cm.refresh();
    }
  }

  // Polled every 250ms
  autoRefresh(): void {
    const elt = this.rootElement;
    const cm = this.codeMirror;
    if (cm && elt) {
      const eltW = elt.offsetWidth;
      const eltH = elt.offsetHeight;
      const eltP = elt.offsetParent;
      if (eltW !== this.currentWidth ||
        eltH !== this.currentHeight ||
        eltP !== this.currentParent) {
        this.currentWidth = eltW;
        this.currentHeight = eltH;
        this.currentParent = eltP;
        cm.refresh();
      }
    }
  }

  // --------------------------------------------------------------------------
  // --- Hover
  // --------------------------------------------------------------------------

  _findMarker(elt: Element): CSSMarker | undefined {
    const { buffer } = this.props;
    if (buffer) {
      let best: CSSMarker | undefined;
      elt.classList.forEach((name) => {
        const marker = buffer.findHover(name);
        if (marker && (!best || marker.length < best.length)) best = marker;
      });
      return best;
    }
    return undefined;
  }

  // eslint-disable-next-line class-methods-use-this
  _findDecoration(
    classes: DOMTokenList,
    buffer: RichTextBuffer,
    decorator: Decorator,
  ): _Decoration | undefined {
    let bestMarker: CSSMarker | undefined;
    let bestDecorated: CSSMarker | undefined;
    let bestDecoration: string | undefined;
    classes.forEach((name) => {

      const marker = buffer.findHover(name);
      const id = marker && marker.id;
      const decoration = id && decorator(id);

      if (marker && (!bestMarker || marker.length < bestMarker.length)) {
        bestMarker = marker;
      }

      if (marker && decoration &&
        (!bestDecorated || marker.length < bestDecorated.length)) {
        bestDecorated = marker;
        bestDecoration = decoration;
      }

    });
    return bestMarker ? {
      classNameId: bestMarker.classNameId,
      decoration: bestDecoration,
    } : undefined;
  }

  _markElementsWith(classNameId: string, className: string): void {
    const root = this.rootElement;
    const toMark = root && root.getElementsByClassName(classNameId);
    if (toMark) {
      const n = toMark.length;
      if (n === 0) return;
      for (let k = 0; k < n; k++) toMark[k].classList.add(className);
    }
  }

  _unmarkElementsWith(className: string): void {
    const root = this.rootElement;
    const toUnmark = root && root.getElementsByClassName(className);
    if (toUnmark) {
      const n = toUnmark.length;
      if (n === 0) return;
      const elts: Element[] = new Array(n);
      for (let k = 0; k < n; k++) elts[k] = toUnmark[k];
      elts.forEach((elt) => elt.classList.remove(className));
    }
  }

  handleHover(target: Element): void {
    // Throttled (see constructor)
    const oldMarker = this.marker;
    const newMarker = this._findMarker(target);
    if (oldMarker !== newMarker) {
      if (oldMarker) this._unmarkElementsWith(CSS_HOVERED);
      if (newMarker && newMarker.hover)
        this._markElementsWith(newMarker.classNameId, CSS_HOVERED);
      this.marker = newMarker;
      const callback = this.props.onHover;
      if (callback) callback(newMarker?.id);
    }
  }

  handleUpdate(): void {
    const root = this.rootElement;
    const marked = root && root.getElementsByClassName('dome-xMarked');
    if (!marked) return;
    const n = marked.length;
    if (n === 0) return;
    const { marker } = this;
    const hovered = (marker && marker.hover) ? marker.classNameId : undefined;
    const { selection } = this.props;
    const selected = selection && (`dome-xMark-${selection}`);
    const { buffer } = this.props;
    const decorator = buffer?.getDecorator();
    if (!hovered && !selection && !decorator) return;
    const newDecorations = new Map<string, string>();
    for (let k = 0; k < n; k++) {
      const elt = marked[k];
      const classes = elt.classList;
      if (hovered && classes.contains(hovered)) classes.add(CSS_HOVERED);
      if (selected && classes.contains(selected)) classes.add(CSS_SELECTED);
      if (buffer && decorator) {
        const deco = this._findDecoration(classes, buffer, decorator);
        if (deco) {
          const prev = this.decorations.get(deco.classNameId);
          const curr = deco.decoration;
          if (prev && prev !== curr) classes.remove(prev);
          if (curr) {
            classes.add(curr);
            newDecorations.set(deco.classNameId, curr);
          }
        }
      }
    }
    this.decorations = newDecorations;
  }

  onMouseMove(evt: MouseEvt): void {
    // Not throttled (can not leak Synthetic Events)
    const tgt = evt.target;
    if (tgt instanceof Element) this.handleHover(tgt);
  }

  onMouseClick(evt: MouseEvt, callback: MarkerCallback | undefined): void {
    // No need for throttling
    if (callback) {
      const { target } = evt;
      if (target instanceof Element) {
        const marker = this._findMarker(target);
        if (marker && marker.id) callback(marker.id, evt.altKey);
      }
    }
    this.props.buffer?.setFocused(true);
  }

  onClick(evt: MouseEvt): void {
    this.onMouseClick(evt, this.props.onSelection);
  }

  onContextMenu(evt: MouseEvt): void {
    this.onMouseClick(evt, this.props.onContextMenu);
  }

  // --------------------------------------------------------------------------
  // --- Scrolling
  // --------------------------------------------------------------------------

  handleScrollTo(line: number): void {
    try {
      const cm = this.codeMirror;
      return cm && cm.scrollIntoView({ line, ch: 0 });
    } catch (_error) {
      D.warn(`unable to scroll to line ${line}: out of range.`);
    }
  }

  // --------------------------------------------------------------------------
  // --- Focus
  // --------------------------------------------------------------------------

  handleKey(_cm: CodeMirror.Editor, key: string, _evt: Event): void {
    switch (key) {
      case 'Esc':
        this.props.buffer?.setFocused(false);
        break;
      default:
        this.props.buffer?.setFocused(true);
        break;
    }
  }

  onFocus(): void { this.props.buffer?.setFocused(true); }
  onBlur(): void { this.props.buffer?.setFocused(false); }
  onScroll(): void {
    const cm = this.codeMirror;
    const { buffer } = this.props;
    if (cm && buffer) {
      const rect = cm.getScrollInfo();
      const delta = rect.height - rect.top - rect.clientHeight;
      buffer.setFocused(delta > 0);
    }
  }

  // --------------------------------------------------------------------------
  // --- Rendering
  // --------------------------------------------------------------------------

  shouldComponentUpdate(newProps: TextProps): boolean {
    const cm = this.codeMirror;
    if (cm) {
      // Swap documents if necessary
      const {
        buffer: oldBuffer,
        selection: oldSelect,
        fontSize: oldFont,
      } = this.props;
      const {
        buffer: newBuffer,
        selection: newSelect,
        fontSize: newFont,
      } = newProps;
      if (oldBuffer !== newBuffer) {
        if (oldBuffer) oldBuffer.unlink(cm);
        if (newBuffer) newBuffer.link(cm);
        else cm.setValue('');
      }
      const oldConfig = getConfig(this.props);
      const newConfig = getConfig(newProps);
      // Incremental update options
      forEachOption(oldConfig, (opt) => {
        if (!(opt in newConfig)) {
          const defValue = CodeMirror.defaults[opt];
          if (defValue)
            cm.setOption(opt, defValue);
        }
      });
      forEachOption(newConfig, (opt) => {
        const oldValue = oldConfig[opt];
        const newValue = newConfig[opt];
        if (newValue !== oldValue) {
          cm.setOption(opt, newValue);
        }
      });
      // Update selection
      if (oldSelect !== newSelect) {
        const selected = `dome-xMark-${newSelect}`;
        if (oldSelect) this._unmarkElementsWith(CSS_SELECTED);
        if (newSelect) this._markElementsWith(selected, CSS_SELECTED);
      }
      // Refresh on new font
      if (oldFont !== newFont) setImmediate(this.refresh);
    }
    // Keep mounted node unchanged
    return false;
  }

  render(): JSX.Element {
    return (
      <div
        className="dome-xText"
        ref={this.mountPoint}
        onClick={this.onClick}
        onContextMenu={this.onContextMenu}
        onBlur={this.onBlur}
        onFocus={this.onFocus}
        onScroll={this.onScroll}
        onMouseMove={this.onMouseMove}
        onMouseLeave={this.onMouseMove}
      />
    );
  }

}

// --------------------------------------------------------------------------
// --- Text View
// --------------------------------------------------------------------------

/** #### Text Editor.

   A component rendering the content of a text buffer, that shall be instances
   of the `Buffer` base class.

   The view is based on a [CodeMirror](https://codemirror.net) component linked
   with the internal Code Mirror Document from the associated buffer.

   Multiple views might share the same buffer as source content. The buffer will
   be kept in sync with all its linked views.

   The Text component never update its mounted NODE element, however, all
   property modifications (including buffer) are propagated to the internal
   CodeMirror instance. Undefined properties are set (or reset) to the
   CodeMirror defaults.

   #### Themes

   The CodeMirror `theme` option allow you to style your document, especially
   when using modes.

   By default, CodeMirror uses the `'default'` theme in _light_ theme and the
   `'dark-code'` theme in _dark_ theme. The `'dark-code'` is provided by Dome,
   Cf. `./dark-mode.css` in the source distribution.

   To use other custom themes, you shall load the associated CSS style
   sheet. For instance, to use the `'ambiance'` theme provided with CodeMirror,
   you shall import `'codemirror/theme/ambiance.css'` somewhere in your
   application.

   #### Modes & Adds-On

   You can install modes and adds-on provided by the CodeMirror distribution by
   simply importing (once, before being used) the associated modules in your
   application.  For instance, to use the `'javascript'` mode option, you shall
   import `'codemirror/mode/javascript/javascript.js'` file in your application.

   #### Further Customization

   You can register your own extensions directly into the global `CodeMirror`
   class instance.  However, the correct instance must be retrieved by using
   `import CodeMirror from 'codemirror/lib/codemirror.js'` ; using `from
   'codemirror'` returns a different instance of `CodeMirror` class and will not
   work.  */
export function Text(props: TextProps): JSX.Element {
  const [appTheme] = Themes.useColorTheme();
  let { className, style, fontSize, theme: usrTheme, ...cmprops } = props;
  if (fontSize !== undefined && fontSize < 4) fontSize = 4;
  if (fontSize !== undefined && fontSize > 48) fontSize = 48;
  const theme = usrTheme ?? (appTheme === 'dark' ? 'dark-code' : 'default');
  const display = props.display === false ? 'none' : undefined;
  return (
    <Vfill className={className} style={{ ...style, fontSize, display }}>
      <CodeMirrorWrapper fontSize={fontSize} theme={theme} {...cmprops} />
    </Vfill>
  );
}

// --------------------------------------------------------------------------
