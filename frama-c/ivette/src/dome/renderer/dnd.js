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
   @module dome/dnd
   @description

## Drag & Drop

A Drag & Drop sequence is monitored by a D&D controller.
Drag Sources initiates the a D&D sequence, and the D&D controller will then
notify the Drop Target when they are dragged over.

More precisely, the D&D controller is notified with all events of any D&D sequence.
Drag sources are notified will all events of the D&D sequences they have initiated.
Drop targets are only notified when they are actually participating into some D&D sequence.
For instance, when the dragged item directly moves from one target into another one, both
targets will be notified, but not the others.


## Dragging Events

Many dragging events are triggered during a D&D sequence.
All event listeners will be notified with a single argument,
which is a `Dragging` object with the following properties:
 - `move`: the kind of move (see below);
 - `meta`: a boolean indicating whether Ctrl, Alt or Meta key is pressed during the move;
 - `held`: a boolean indicating whether the mouse is holding over position;
 - `sourceClientRect`: the position of the drag source element;
 - `targetClientRect`: the position of the drop target element;
 - `deltaX`, `deltaY`: the current offset position of the dragged element,
relative to its _initial_ position;
 - `clientX`, `clientY`: the current client position of the _cursor_, as obtained from the dragging event;
 - `position`: the current position from React-Draggable API (see DragSource documentation).

All coordinates are provided in the window coordinate system,
as returned by the `getBoundingClientRect` DOM method.


## Dragging State

During the entire sequence, the D&D controller is responsible for managing a shared
state among source and targets.
The drag source and each drop targets may update the shared state when receiving
events, and will be re-rendered in turn when necessary.

This design eases the separation of concern: each participant in the D&D
sequence is only responsible with its own rendering, while synchronizing between the
participants is ensured through the global state.


## Kind of Moves

During a D&D sequence, different kind of events can be triggered.
They can be distinguished with the `move` property of the dragging events,
as follows:
 - `'START'`: D&D sequence initiated;
 - `'STOP'`: D&D sequence finished without drop target;
 - `'DROP'`: D&D sequence finished over some drop target;
 - `'DRAG'`: the source is dragged over some drop target;
 - `'HOLD'`: the source is holding the position for a while;
 - `'MOVE'`: the source is moving again after holding for a while ;
 - `'ENTER'`: the source is entering a target from _no_ other target;
 - `'LEAVE'`: the source is leaving a target into _no_ other target;
 - `'SWITCH'`: the source is leaving a target into another target.

Notice that in kind of a `'SWITCH'` event, the leaved target will receive a `'LEAVE'` event
and the entered target will receive an `'ENTER'` event.


## Event Callbacks

D&D controllers, drag sources and drop targets can listen to
dragging events _via_ various callbacks.

Each callback has signature `(Dragging) => void` and is sensible to
specific kinds of events, as described below:
 - `onDnd()`: all kind of events;
 - `onStart()`: `START` events;
 - `onEnter()`: `ENTER` and `SWITCH` events;
 - `onLeave()`: `LEAVE` and `SWITCH` events;
 - `onDrag()`: `DRAG` and `MOVE` events;
 - `onHold()`: `HOLD` events;
 - `onMove()`: `MOVE` events;
 - `onDrop()`: `DROP` events;
 - `onStop()`: `STOP` events;
 - `onUpdate()`: only for D&D controllers, see below.

In case of a `SWITCH` event, the `onLeave` listener is called first,
then the `onEnter` listener. This is only relevant for the D&D controller
and the drag source, since drop targets will receive either `ENTER` or `LEAVE` events.

The same `Dragging` object is shared across all the event listeners, but
not among different drag source and drop targets. For each source or target
participating into the event, the `onDnd` listener is called first,
then the more specific ones, when defined. Hence, you can modify the `Dragging`
object during the process of `onDnd` and safely propagate those modifications accross
all listeners.

Inside a D&D sequence, the leaved targets are notified first,
then the source and the target, and finally the D&D controller.
This allow you to maintain the D&D state in sync with the different participants.

Additionally, the D&D controller might be equiped with
an `onUpdate()` handler, which is responsible for listening only to state update events.
This event handler will receive the current D&D state in argument, with the cumulated
updates from all participants merged in.

*/

import _ from 'lodash' ;
import React from 'react' ;
import Draggable, { DraggableCore } from 'react-draggable';

const HOLD_TIME = 100 ; /* time in ms */
const HOLD_FIRE = 6 ;   /* number of HOLD_TIME before « hold » */
const HOLD_MOVE = 3 ;   /* maximum moved pixels for « holding » */

// --------------------------------------------------------------------------
// --- Events Dispatcher
// --------------------------------------------------------------------------

const notify = ( cb, evt ) => cb && cb(evt);

/**
   @method
   @summary Dispatch a dragging event over listeners.
   @param {Dragging} dragging - the Dragging event to dispatch over
   @param {object} [handlers] - an object with (optional) listeners
   @description

Dispatch a `Dragging` event among listeners defined in the `handlers` object,
when defined. For instance, `disptachEvents( evt , { onStop: myCallback } )`
will trigger `myCallback(evt)` if and only if `evt` is a `STOP` event.

See event listeners documentation above for more details on listeners.

You normally don't have to call this function, unless when you need to add
D&D features into your own component. Here is a typical pattern:

    const MyComponent = (props) => (
       <DragSource
          dnd={props.dnd}
          onDnd={(evt) => DnD.dispatchEvent(Object.assign(evt,…),props)} >
          …
       </DragSource>
    );

 */
export const dispatchEvent = ( dragging , handlers ) => {
  if (!handlers) return;
  const dragged = Object.assign( {} , dragging );
  notify( handlers.onDnd , dragged );
  switch( dragged.move ) {
  case 'START':
    notify( handlers.onStart, dragged );
    return;
  case 'STOP':
    notify( handlers.onStop,  dragged );
    return;
  case 'ENTER':
    notify( handlers.onEnter, dragged );
    return;
  case 'SWITCH':
    notify( handlers.onLeave, dragged );
    notify( handlers.onEnter, dragged );
    return;
  case 'LEAVE':
    notify( handlers.onLeave, dragged );
    return;
  case 'DRAG':
    notify( handlers.onDrag,  dragged );
    return;
  case 'MOVE':
    notify( handlers.onMove,  dragged );
    notify( handlers.onDrag,  dragged );
    return;
  case 'HOLD':
    notify( handlers.onHold,  dragged );
    return;
  case 'DROP':
    notify( handlers.onDrop,  dragged );
    return;
  default:
    return;
  }
};

// --------------------------------------------------------------------------
// --- Dnd Controllers
// --------------------------------------------------------------------------

/**
   @class
   @summary D&D Controller.
   @param {object} [handlers] - D&D events callbacks
   @property {object} state - Current D&D state
   @property {Dragging} dragging - Last D&D event
   @description
   D&D controlers are responsible for managing various drop targets
   and dispatching the drag source events among them.

   The handler object shall define listeners to the D&D dragging events.
   Each callback is sensible to specific kind of events, as specified
   in the [[dome/dnd]] documentation.

   You need a D&D controller whenever an element can be dragged
   between different containers. D&D controllers also offers an
   abstraction over dragging events, dispatching among several
   drop targets and the management of « holding » the mouse over
   one drop target.

   Normally, you simply have to create D&D controllers in your global
   (or local) state and pass them around into the hierarchy of your
   components. For lower-level control, see the documentation of
   the exposed methods.

   Having several D&D controllers allows you to assign specific
   sources to specific targets. You shall have one D&D controller
   for each « kind » of data that you can drag over.

   The `state` and `dragging` properties are shared across all partipants
   of a D&D sequence, which are also re-rendered when the state is updated.
   Outside of a D&D sequence, the `state` and `dragging` properties are undefined.

*/

export class DnD {

  constructor(handlers) {
    this.kid = 0 ;
    this.targets = {} ;
    this.tickHold = this.tickHold.bind(this);
    this.triggerUpdate = this.triggerUpdate.bind(this);
    this.triggerDnd = this.triggerDnd.bind(this);
    this.handlers = handlers || {} ;
  }

  /** @summary Update the D&D event handlers.
      @param {object} [handlers] - D&D events callbacks
      @description
      Replace the event handlers by those specified in the `handlers` object.
      Not mentionned callbacks are left unchanged.
      If the `null` object is given, all current handlers are removed.
  */
  setHandlers( handlers ) {
    this.handlers =
      handlers === null ? {} : Object.assign( this.handlers, handlers );
  }

  //--- Registering

  /** @summary Registers a target into the D&D controller.
      @param {React.ref} ref - a referrence on the drop target DOM element
      @param {function} callback - generic D&D events callback
      @return {ident} the target identifier
      @description
      You normally don't call this method by yoursef, it is automatically
      called when `<DropTarget/>` are mounted in the DOM.
  */
  register( ref, callback )
  {
    if (!ref) return undefined;
    const id = 'DOME$' + (++this.kid) ;
    this.targets[id] = { id, ref , callback } ;
    return id;
  }

  //--- Updating

  /** @summary Update the event handlers associated to a drop target.
      @param {ident} id - the drop target identifier
      @param {React.ref} ref - a referrence on the drop target DOM element
      @param {function} callback - generic D&D events callback
      @description
      You normally don't call this method by yoursef, it is automatically
      called when `<DropTarget/>` are updated. If the target data is falsy, the target identifier
      is used instead.
  */
  update( id, ref, callback ) {
    if (this.targets[id]) {
      this.targets[id] = { id, ref, callback };
    }
  }

  //--- Un-Registering

  /** @summary Un-register a target from the D&D controller.
      @param {ident} id - the drop target identifier to remove
      @description
      You normally don't call this method by yoursef, it is automatically
      called when `<DropTarget/>` are unmounted from the DOM.
  */
  remove( id ) {
    delete this.targets[id] ;
  }

  //--- Generic Mouse Event

  handleMouseEvent( evt, x, y ) {
    const d = this.dragging ;
    d.meta = evt.ctrKey || evt.altKey || evt.metaKey ;
    d.deltaX = x - this.rootX ;
    d.deltaY = y - this.rootY ;
    d.position = {x,y} ;
    const ex = d.clientX = evt.clientX ;
    const ey = d.clientY = evt.clientY ;
    d.targetClientRect = undefined ;
    this.leaved = this.target ;
    this.leavedHandler = this.targetHandler ;
    this.target = undefined ;
    this.targetHandler = undefined ;
    const elts = document.elementsFromPoint(ex,ey);
    elts.find((elt) => {
      const target = _.find( this.targets, (tgt) => tgt.ref.current === elt );
      if (target) {
        const { id, callback } = target ;
        this.target = id ;
        this.targetHandler = target.callback ;
        if (id === this.leaved) this.leavedHandler = undefined ;
        d.targetClientRect = elt.getBoundingClientRect();
        return true;
      }
      return false;
    });
  }

  //--- Starting D&D sequence

  /** @summary Initiates a new drag.
      @param {Event} evt - the mouse event originating the drag
      @param {number} x - initial horizontal coordinate
      @param {number} y - initial vertical coordinate
      @param {Element} node - the source DOM element
      @param {function} callback - generic D&D events callback
      @description
You normally don't call this method by sourself, it is automatically
called by `DragSource` objects.

Initial `(x,y)` coordinates can be in any coordinate system, they
are only used to compute relative offsets of further D&D events.
They can be typically taken from React-Draggable events data.

The generic callback shall handle two kind of events:
 - `callback()` when the global D&D state has been updated;
 - `callback(Dragging)` when some D&D event is triggered.

Generally, you shall `forceUpdate()` your component in the first case,
and `dispatchEvent()` the event to D&D listeners in the second case.

  */
  handleStart( evt, x, y, node, callback ) {
    if (this.dragging) {
      this.triggerDnd('STOP');
      if (this.timer) clearInterval(this.timer);
    }
    this.state = {};
    this.dragging = {
      sourceClientRect: node.getBoundingClientRect()
    };
    this.sourceHandler = callback ;
    this.targetHandler = undefined ;
    this.leavedHandler = undefined ;
    this.rootX = x;
    this.rootY = y;
    this.lastX = x;
    this.lastY = y;
    this.ticks = 0;
    this.handleMouseEvent( evt, x, y );
    this.triggerDnd( 'START' );
    this.timer = setInterval( this.tickHold , HOLD_TIME );
  }

  //--- Dragging D&D sequence

  /** @summary Dispatch a drag-event amoung registered drop targets.
      @param {Event} evt - the dragging mouse event
      @param {number} x - the horizontal coordinate
      @param {number} y - the vertical coordinate
      @description
You normally don't call this method by sourself, it is automatically
called by `DragSource` objects.

The `(x,y)` coordinates shall be in the same coordinate system than
when starting the D&D sequence. It is only used to compute relative
the offsets of the associated D&D event.
  */
  handleDrag( evt, x, y ) {
    let kind = 'DRAG' ;
    let delta = Math.abs( x - this.lastX ) + Math.abs( y - this.lastY );
    this.lastX = x ;
    this.lastY = y ;
    if (delta > HOLD_MOVE) {
      this.ticks = 0 ;
      const d = this.dragging ;
      if (d.held) {
        d.held = false ;
        kind = 'MOVE' ;
      }
    }
    this.handleMouseEvent( evt, x, y );
    const target = this.target ;
    const leaved = this.leaved ;
    if (target !== leaved) {
      if (target && !leaved) kind = 'ENTER' ; else
        if (!target && leaved) kind = 'LEAVE' ; else
          if (target && leaved) kind = 'SWITCH' ;
    }
    this.triggerDnd(kind);
  }

  //--- Stopping D&D sequence

  /** @summary Dispatch a drop-event over registered drop targets.
      @param {Event} evt - the dropping mouse event
      @param {number} x - the horizontal coordinate
      @param {number} y - the vertical coordinate
      @description
You normally don't call this method by sourself, it is automatically
called by `DragSource` objects.

The `(x,y)` coordinates shall be in the same coordinate system than
when starting the D&D sequence. It is only used to compute relative
the offsets of the associated D&D event.
  */
  handleStop( evt, x, y ) {
    clearInterval( this.timer );
    this.handleMouseEvent( evt, x, y );
    this.triggerDnd(this.target ? 'DROP' : 'STOP');
    this.dragging = undefined ;
    this.state = undefined ;
    this.timer = undefined;
    this.ticks = undefined;
    this.triggerUpdate();
  }

  //--- Hold Detection

  tickHold() {
    if (this.dragging && (this.ticks++) > HOLD_FIRE)
    {
      this.dragging.held = true ;
      this.triggerDnd('HOLD');
      this.ticks = 0 ;
    }
  }

  //--- Update State

  /**
     @summary Update the controller state.
     @parameter {object} update - the data to update the state with
     @description
     Update the state with the given updates, like React component states.
     This will force the drag source target and drop target components to re-render.
  */
  setState(update) {
    const state = this.state ;
    if (state && update) {
      this.state = Object.assign( state, update );
      if (!this.dirty) {
        this.dirty = true ;
        setImmediate( this.triggerUpdate );
      }
    }
  }

  triggerUpdate() {
    this.dirty = false ;
    notify( this.leavedHandler ); // always different from target
    notify( this.sourceHandler );
    notify( this.targetHandler );
    notify( this.handlers.onUpdate , this.state );
  }

  //--- Trigger Dragging Events

  triggerDnd(move) {
    const d = this.dragging ;
    d.move = move ;
    switch( move ) {
    case 'ENTER':
      notify( this.sourceHandler, d );
      notify( this.targetHandler, d );
      break;
    case 'LEAVE':
      notify( this.leavedHandler, d );
      notify( this.sourceHandler, d );
      break;
    case 'SWITCH':
      d.move = 'LEAVE'  ; notify( this.leavedHandler, d );
      d.move = 'SWITCH' ; notify( this.sourceHandler, d );
      d.move = 'ENTER'  ; notify( this.targetHandler, d );
      d.move = 'SWITCH' ;
      break;
    default:
      notify( this.leavedHandler, d ); // allways different from target
      notify( this.sourceHandler, d );
      notify( this.targetHandler, d );
      break;
    }
    dispatchEvent( d, this.handlers );
  }

}

// --------------------------------------------------------------------------
// --- Drag Overlay
// --------------------------------------------------------------------------

/**
   @summary Display a Drag Source with an Overlay.
   @property {Dragging} [dragging] - current dragging event
   @property {string} [className] - source content class
   @property {object} [style] - source content style
   @property {object} [draggedStyle] - additional style for the source placeholder
   @property {object} [draggingStyle] - additional style for the source being dragged
   @property {number} [offsetX] - horizontal offset during drag (default 4)
   @property {number} [offsetY] - vertical offset during drag (default 4)
   @property {number} [zIndex] - fixed positioning during drag (default 1)
   @property {any} [...divProps] - other properties to inject in the root element
   @property {React.children|function} [children] - drag source content
   @description
   When dragged, a source drag is generally blit by its embedding container.
   Using z-index CSS property might be a solution, but this is generally not
   enough to escape from a positionned parent  `<div>` element.

   The alternative is to separate the internal content of
   a drag source from its outer `<div>`, and to use fixed positionning
   during a D&D sequence.

   The `<Overlay>` component implements this behaviour. The root element is
   normally laid out with the `className`, `style` and `divProps` properties and
   its internal content is wrapped inside an internal `<div>` container.

   During dragging, this normal layout is slightly altered, without causing
   extra React mounting or unmounting.  The outer `<div>` is styled with its
   original class plus the `'dome-dragged'` class which provides by default a
   light-blue background and invisible border style.  The inner class is styled
   with its original class plus the `dome-dragging` class, canceled margins and
   fixed positionning with respect to the dragging event.  You may use those
   additinal classes to add conditional styling when dragging.

   Additionnaly, when dragged around, the source content is offsets
   with `offsetX` and `offsetY`, which defaults to 4 pixels each.

   Finally, you may supply a custom rendering function for rendering the drag
   source content, which is fed with the current dragging event.
 */

export const Overlay = ({
  dragging, className='', style, styleDragged, styleDragging,
  offsetX=4, offsetY=4, insetX=0, insetY=0,
  zIndex=1,
  children,
  ...divProps
}) => {
  let outerClass,outerStyle,innerStyle,innerClass ;
  if (dragging) {
    const { left, top, width, height } = dragging.sourceClientRect ;
    const position = {
      position: 'fixed',
      left:   left + offsetX + dragging.deltaX,
      top:    top  + offsetY + dragging.deltaY,
      width, height, zIndex, margin: 0
    };
    const holder = {
      width, height
    };
    outerClass = 'dome-dragged ' + className ;
    innerClass = 'dome-dragging ' + className ;
    outerStyle = Object.assign( {}, style, styleDragged, holder );
    innerStyle = Object.assign( {}, style, styleDragging, position );
  } else {
    outerClass = className ;
    outerStyle = style ;
    innerClass = undefined ;
    innerStyle = undefined ;
  }
  return (
    <div className={outerClass} style={outerStyle} {...divProps}>
      <div className={innerClass} style={innerStyle}>
        {typeof(children)==='function' ? children(dragging) : children}
      </div>
    </div>
  );
};

// --------------------------------------------------------------------------
// --- Drag Sources
// --------------------------------------------------------------------------

/**
   @class
   @summary Drag Source Component.
   @property {DnD} [dnd] - the associated D&D controller
   @property {string} [handle] - DOM selector initiating the drag (eg. `'.handle'`)
   @property {boolean} [disabled] - cancel D&D events if non falsy value
   @property {object} [draggable] - additional properties for the internal react-draggable wrapper
   @property {function} [onDnd] - callback to D&D generic events
   @property {function} [onXxx] - callback to other D&D specific events
   @property {string} [className] - the class of the internal 'div' component (unless custom rendering)
   @property {object} [style] - the style of the internal 'div' component (unless custom rendering)
   @property {object} [position] - relative position of the internal 'div' component (unless custom rendering)
   @property {boolean|object} [overlay] - use an `Overlay` to display the content
   @property {React.children|function} children - element content or custom rendering function
   @description

Creates a drag source element and manage its dragging state. The component
is rendered by an internal `<div>` element with the given class and style with specific
handlers attached in. You can use the `'position'` property to modify its relative position
_after_ a D&D sequence, the position being `{x:0,y:0}`. This position is set relative to the normal
positioning of the internal `<div>` element, as specified by the provided class and style properties.
Notice that during dragging, your component is attached an additional `'dome-dragging'` class name that
you can use to alter its rendering.

Alternatively, you may provide a custom rendering function as the unique children of the Drag Source element.
The function will be given the current D&D dragging events, or `undefined` when outside a D&D sequence.
The custom rendering _shall_ return a single root element supporting property injection in order for the Drag
Source element to attach its event handlers into it. You are then fully responsible for rendering and positioning
the element both _during_ and _outside_ of a D&D sequence. No internal `<div>` element is inserted for you,
and the `className`, `style` and `position` properties are ignored.

Finally, you may also use an [[Overlay]] component to render
your content, by setting `overlay=true` or passing `overlay` the desired properties.

When dragged, the [[DnD]] controller is informed and dispatches
the dragging events to the registered drop targets. The `handle` selector can be used
to identify which parts of the content may initiate the drag. By default, any drag event
may initiate the drag.

The `onDnd` event listener receives all D&D events associated to this drop target.
See event callbacks documentation for more details on other specific event listeners.

The `draggable` object, when provided, is used to inject additional properties
into the internal `Draggable` or `DraggableCore` wrapper used to manage D&D events.
By default, a full featured `Draggable` component is used.
When a custom rendering function is specified, a `DraggableCore` is used instead.
See [react-draggable](https://github.com/mzabriskie/react-draggable)
documentation for more details.

*/

export class DragSource extends React.Component
{
  constructor(props)
  {
    super(props);
    this.onStart = this.onStart.bind(this);
    this.onDrag = this.onDrag.bind(this);
    this.onStop = this.onStop.bind(this);
    this.handleDnd = this.handleDnd.bind(this);
    this.state = { };
  }

  componentDidMount() {
    this.mounted = true;
  }

  componentWillUnmount() {
    this.mounted = false;
  }

  onStart(evt,drag) {
    const { dnd, disabled } = this.props;
    if (dnd) dnd.handleStart(evt,drag.x,drag.y,drag.node,this.handleDnd);
  }

  onDrag(evt,drag) {
    const { dnd, disabled } = this.props ;
    if (dnd) dnd.handleDrag(evt,drag.x,drag.y);
  }

  onStop(evt,drag) {
    const { dnd, disabled } = this.props ;
    if (dnd) dnd.handleStop(evt,drag.x,drag.y);
  }

  handleDnd(dragging) {
    if (!this.mounted) return;
    if (!dragging)
      this.forceUpdate();
    else {
      dispatchEvent( dragging, this.props );
      switch(dragging.move) {
      case 'STOP':
      case 'DROP':
        this.setState({dragging:undefined});
        break;
      default:
        this.setState({dragging});
        break;
      }
    }
  }

  render() {
    const { dnd, disabled, className, style,
            handle, draggable, overlay,
            children } = this.props ;
    if (overlay || typeof(children)==='function') {
      const dragging = this.state.dragging ;
      return (
        <DraggableCore
          handle={handle}
          disabled={!dnd || disabled}
          onStart={this.onStart}
          onDrag={this.onDrag}
          onStop={this.onStop}
          {...draggable}
          >
          { overlay ?
            (
              <Overlay
                dragging={dragging}
                className={className} style={style}
                {...overlay} >
                {children}
              </Overlay>
            )
            : children(dragging)
          }
        </DraggableCore>
      );
    } else {
      const { className, style, position={x:0,y:0} } = this.props ;
      return (
        <Draggable
          handle={handle}
          disabled={!dnd || disabled}
          position={position}
          defaultClassName=''
          defaultClassNameDragged=''
          defaultClassNameDragging='dome-dragging'
          onStart={this.onStart}
          onDrag={this.onDrag}
          onStop={this.onStop}
          {...draggable}
          >
          <div className={className} style={style}>{children}</div>
        </Draggable>
      );
    }
  }

}

// --------------------------------------------------------------------------
// --- Drop Target
// --------------------------------------------------------------------------

/**
   @class
   @summary Drop Target Container.
   @property {DnD} [dnd] - the associated D&D Controller
   @property {function} [onDnd] - callback to D&D generic events
   @property {function} [onXxx] - callback to other D&D specific events
   @property {string} [className] - class name(s) of the internal `<div>` element (unless custom rendering)
   @property {object} [style] - style property for the internal `<div>` element (unless custom rendering)
   @property {React.ref} [targetRef] - the React ref to use for identifying the target DOM element
   @property {React.children|function} children - element content or custom rendering function
   @description

Crates a drop target container and register its callbacks into the specified
[[DnD]] controller. In case the DnD controller is undefined,
the drag events are just disabled.

The drop target container must inform the D&D controller of its DOM element that is responsible
for reacting to dragging events. By default, the drop target element renders its children elements
inside an internal `<div>` element with the specified class ans style properties. Notice that, during
a D&D sequence, the `dome-dragging` class name is added to this `<div>` element and you can use this selector
for your styling.

Alternatively, you may provide a custom rendering function as the unique children of the Drag Source element.
Your rendering function will receive the current D&D dragging of the D&D sequence, if any.
The [targetRef] property shall be used to identify the target DOM element, otherwize, the drop target
will not respond to dragging events.
In case of custom rendering, the `className` and `style` properties are ignored.

During a D&D sequence, the `onDnd` event listener receives all D&D events associated
to this drop target. See event callbacks documentation for more details on
other specific event listeners.

*/
export class DropTarget extends React.Component
{

  constructor(props) {
    super(props);
    this.targetRef = this.props.targetRef || React.createRef() ;
    this.handleDnd = this.handleDnd.bind(this);
    this.state = {};
  }

  componentDidMount() {
    const { dnd } = this.props ;
    this.id = dnd && dnd.register( this.targetRef, this.handleDnd );
    this.mounted = true ;
  }

  componentDidUpdate() {
    const { dnd } = this.props ;
    dnd && dnd.update(this.id, this.targetRef, this.handleDnd );
  }

  componentWillUnmount() {
    const { dnd } = this.props ;
    dnd && dnd.remove( this.id );
    this.mounted = false ;
  }

  handleDnd(dragging) {
    if (!this.mounted) return;
    if (!dragging)
      this.forceUpdate();
    else {
      dispatchEvent( dragging, this.props );
      switch(dragging.move) {
      case 'STOP':
      case 'DROP':
      case 'LEAVE':
        this.setState({dragging:undefined});
        break;
      default:
        this.setState({dragging});
        break;
      }
    }
  }

  render() {
    const targetRef = this.targetRef ;
    const { children } = this.props ;
    const { dragging } = this.state ;
    if (typeof(children)==='function')
      return children(dragging);
    else {
      let { className='', style } = this.props ;
      return (
        <div ref={targetRef}
             className={ dragging ? className + ' dome-dragging' : className }
             style={style} >
          {children}
        </div>
      );
    }
  }

}

// --------------------------------------------------------------------------
