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
// --- Grid Layout
// --------------------------------------------------------------------------

/**
   @packageDocumentation
   @module dome/layout/grids
*/

import _ from 'lodash' ;
import React from 'react' ;
import * as Json from 'dome/data/json';
import * as Settings from 'dome/data/settings';
import { dispatchEvent, DnD, DragSource, DropTarget } from 'dome/dnd' ;
import { AutoSizer } from 'react-virtualized' ;
import { DraggableCore } from 'react-draggable' ;

import * as Dome from 'dome' ;

import './style.css' ;

// --------------------------------------------------------------------------
// --- Grid Utilities
// --------------------------------------------------------------------------

function flatten( dir, gs )
{
  const content = [] ;
  gs && gs.forEach((g) => {
    let kd = g && g.kind ;
    if (kd)
      if ( kd === dir ) {
        if (g.content.length > 0) content.push( ...g.content );
      } else
        content.push( g );
  });
  return content ;
}

function iter( grid , fn )
{
  function visit(g) {
    if (!g) return;
    if (g.kind === 'ITEM') fn(g);
    else g.content.forEach(visit);
  }
  visit(grid);
}

function get( g, id )
{
  if (g) {
    if (g.id === id) return g;
    switch( g.kind ) {
    case 'HBOX':
    case 'VBOX':
      const gs = g.content ;
      var k = 0;
      while (k < gs.length) {
        let r = get(gs[k],id);
        if (r) return r;
        k++;
      }
    }
  }
  return undefined;
}

/**
   @summary Pretty-print shape.
 */

export function stringOfShape( s )
{
  if (!s) return "<>" ;
  switch(s.kind) {
  case 'ITEM':
    if (s.switch || s.height)
      return s.id + "(" + s.width + "x" + s.height + ")" ;
    else
      return s.id ;
  case 'HBOX': return "H<" + s.content.map(stringOfShape).join(',') + ">" ;
  case 'VBOX': return "V<" + s.content.map(stringOfShape).join(',') + ">" ;
  default: return "<?" + s + "?>";
  }
}

// --------------------------------------------------------------------------
// --- Shape Utilities
// --------------------------------------------------------------------------

/**
   @summary Iterates over items in a shape.
   @parameter {Shape} shape - the shape to iter over
   @parameter {function} job - the function to apply on each
   @description
   The iteree receives `job(id,width,height)` for each `ITEM` in the shape.
 */
export function iterShape( shape, job )
{
  iter( shape , (item) => job(item.id,item.width,item.height) );
}

/**
   @summary Returns the shape element of the given item identifier.
   @parameter {Shape} shape - the shape to look into
   @parameter {string} id - the item identifier
   @return {object} the associated item object, or `undefined`
 */
export function getShapeItem( shape, id )
{
  return get(shape,id);
}

/**
   @summary Remove an item or sub-grid from the shape.
   @parameter {Shape} shape - the shape to filter
   @parameter {string} id - the item or grid identifier to remove
   @return {Shape} the filtered shape
 */
export function removeShapeItem( shape, id )
{
  const visit = (s) => {
    if (s && s.id !== id) {
      switch(s.kind) {
      case 'ITEM':
        return s;
      case 'HBOX':
      case 'VBOX':
        return makeShapeBox( s.kind , s.id, s.content.map(visit) );
        //otherwize continue
      }
    }
    return null;
  };
  return visit(shape);
}


// --------------------------------------------------------------------------
// --- Dimensions
// --------------------------------------------------------------------------

function shareDim( d , ds )
{
  d.min = 0;
  d.size = 0;
  d.next = 0;
  d.ext = 0;
  d.fill = false;
  d.resize = false;
  ds.forEach( (di) => {
    d.min  += di.min ;
    d.size += di.size ;
    if (di.resize) d.resize = true ;
    if (di.fill) {
      d.fill = true ;
      d.ext  += di.min ;
      d.next ++ ;
    } else
      d.ext  += di.size ;
  });
}

function stackDim( d , ds )
{
  d.min = 0;
  d.size = 0;
  d.fill = 0;
  d.resize = 0;
  ds.forEach( (di) => {
    d.min   = Math.max( d.min,  di.min  );
    d.size  = Math.max( d.size, di.size );
    if (di.fill) d.fill = true ;
    if (di.resize) d.resize = true ;
  });
}


// --------------------------------------------------------------------------
// --- Sequence Layout
// --------------------------------------------------------------------------

/* Distributes extra available space w.r.t respective ratio. */
function layoutShare( d0 , ds )
{
  const d = d0.dim ;
  const s = d0.size ;
  const e = d0.ext ;
  const m = d0.min ;

  let flayout ;

  if ( s <= d ) {
    const K = d0.next ;
    flayout = (di) =>
      di.fill ? di.size + ( d - s ) / K : di.size ;
  } else if ( e <= d ) {
    // Have e <= d < s, Hence e < s
    const alpha = (d - e) / (s - e) ;
    flayout = (di) =>
      di.fill ? di.min + alpha * (di.size - di.min) : di.size ;
  } else if ( m <= d ) {
    // Have m <= d < {e,s}, Hence m < e
    const alpha = (d - m) / (e - m) ;
    flayout = (di) =>
      !di.fill ? di.min + alpha * (di.size - di.min) : di.min ;
  } else if ( m > 0 ) {
    const alpha = d / m ;
    flayout = (di) => alpha * di.min ;
  } else {
    flayout = (di) => 0 ;
  }

  var p0 = d0.pos ;
  var p1 = p0 ;
  var ps = 0 ;
  ds.forEach((di) => {
    ps += di.drag ? di.drag : flayout(di) ; // Avoids cumulative rounding
    let p2 = p0 + Math.round(ps) ;
    di.pos = p1 ;
    di.dim = p2-p1 ;
    p1 = p2 ;
  });
}

// --------------------------------------------------------------------------
// --- Parallel Layout
// --------------------------------------------------------------------------

/* Apply available space to all elements */

function layoutStack( d0 , ds )
{
  const p = d0.pos ;
  const d = d0.dim ;
  ds.forEach((di) => {
    di.pos = p ;
    di.dim = di.drag ? di.drag : (di.fill ? d : Math.min( d , di.size )) ;
    di.room = d - di.dim ;
  });
}

// --------------------------------------------------------------------------
// --- Layout Grid
// --------------------------------------------------------------------------

function layoutGrid(grid,width,height)
{
  function visit(g) {
    if (!g) return ;
    switch( g.kind ) {
    case 'ITEM':
      break;
    case 'HBOX':
      layoutShare( g.dx , g.dxs );
      layoutStack( g.dy , g.dys );
      g.content.forEach(visit);
      break;
    case 'VBOX':
      layoutStack( g.dx , g.dxs );
      layoutShare( g.dy , g.dys );
      g.content.forEach(visit);
      break;
    }
  }
  grid.dx.pos = 0; grid.dy.pos = 0;
  grid.dx.dim = width; grid.dy.dim = height;
  visit(grid);
}

// --------------------------------------------------------------------------
// --- Freezing
// --------------------------------------------------------------------------

function freezeGrid( g )
{
  if (!g) return;
  switch(g.kind) {
  case 'ITEM':
    g.dx.size = g.dx.dim ;
    g.dy.size = g.dy.dim ;
    break;
  case 'HBOX':
    g.content.forEach( freezeGrid );
    shareDim(g.dx,g.dxs);
    stackDim(g.dy,g.dys);
    break;
  case 'VBOX':
    g.content.forEach( freezeGrid );
    stackDim(g.dx,g.dxs);
    shareDim(g.dy,g.dys);
    break;
  }
}

function resizeGrid(g,dgx,dgy)
{
  if (!g) return;
  switch(g.kind) {
  case 'ITEM':
    if (dgx && !g.dx.room) g.dx.drag = dgx ;
    if (dgy && !g.dy.room) g.dy.drag = dgy ;
    break;
  case 'HBOX':
    g.content.forEach( (g) => resizeGrid(g,g.dx.drag,dgy) );
    break;
  case 'VBOX':
    g.content.forEach( (g) => resizeGrid(g,dgx,g.dy.drag) );
    break;
  }
}

// --------------------------------------------------------------------------
// --- Grid Constructors
// --------------------------------------------------------------------------

const BOXID = 'DOME$' ;
const MINDIM = 12 ;
const INSETS = 6 ; // For insertion borders

function makeGridItem( content, width, height )
{
  if (content.display !== undefined && !content.display) return undefined ;
  const dimension = (d) => Math.max( d || 0 , MINDIM );
  const w  = dimension(content.width) ;
  const h  = dimension(content.height);
  const mw = dimension(content.minWidth);
  const mh = dimension(content.minHeight);
  const dx = { size: Math.max( mw , w ), min: Math.min( mw , w ), resize:false, fill:false };
  const dy = { size: Math.max( mh , h ), min: Math.min( mh , h ), resize:false, fill:false };
  switch( content && content.fill ) {
  case 'both':       dx.fill = true ; dy.fill = true ; break;
  case 'horizontal': dx.fill = true ; break;
  case 'vertical':   dy.fill = true ; break;
  }
  switch( content && content.resize ) {
  case undefined:    dx.resize = dx.fill ; dy.resize = dy.fill; break;
  case 'both':       dx.resize = true ; dy.resize = true ; break;
  case 'horizontal': dx.resize = true ; break;
  case 'vertical':   dy.resize = true ; break;
  }
  if (width && dx.resize && dx.min <= width)
    dx.size = width ;
  if (height && dy.resize && dy.min <= height)
    dy.size = height ;
  const id = content.id ;
  return { kind: 'ITEM', dx, dy, id, content };
}

function makeGridHbox( id, gs )
{
  const content = flatten( 'HBOX' , gs );
  switch(content.length) {
  case 0: return null ;
  case 1: return content[0];
  default:
    const dxs = content.map((g) => g.dx);
    const dys = content.map((g) => g.dy);
    const dx = {} ;
    const dy = {} ;
    shareDim(dx,dxs);
    stackDim(dy,dys);
    return { kind: 'HBOX', id , dx, dxs, dy, dys, content };
  }
}

function makeGridVbox( id, gs )
{
  const content = flatten( 'VBOX' , gs );
  switch(content.length) {
  case 0: return null ;
  case 1: return content[0];
  default:
    const dxs = content.map((g) => g.dx);
    const dys = content.map((g) => g.dy);
    const dx = {} ;
    const dy = {} ;
    stackDim(dx,dxs);
    shareDim(dy,dys);
    return { kind: 'VBOX', id, dx, dxs, dy, dys, content };
  }
}

function makeGridDir( dir, id, gs )
{
  switch( dir || 'vertical') {
  case 'horizontal':
    return makeGridHbox(id,gs);
  case 'vertical':
    return makeGridVbox(id,gs);
  default:
    return null;
  }
}

function makeShapeDir( dir, id, content )
{
  switch( dir || 'vertical') {
  case 'horizontal':
    return makeShapeBox('HBOX',id,content);
  case 'vertical':
    return makeShapeBox('VBOX',id,content);
  default:
    return null;
  }
}

// --------------------------------------------------------------------------
// --- Shapes
// --------------------------------------------------------------------------

function makeShapeBox( kind, id, gs )
{
  const content = flatten( kind, gs );
  switch(content.length) {
  case 0: return null ;
  case 1: return content[0];
  default: return { kind, id, content };
  }
}

function makeShapeOfGrid( g )
{
  let kind = g && g.kind ;
  switch( kind ) {
  case 'HBOX':
  case 'VBOX':
    return { kind, id: g.id, content: g.content.map(makeShapeOfGrid) };
  case 'ITEM':
    return { kind:'ITEM', id: g.id, width: g.dx.dim, height: g.dy.dim };
  default:
    return null;
  }
}

const BOXINSERT = 'DOME$INSERT' ;
let insertId = 0 ;

function makeShapeInsert( shape,at,dir,item )
{
  const visit = (s) => {
    if (!s || s.id === item.id) return null;
    switch( s.kind ) {
    case 'HBOX':
    case 'VBOX':
      s = makeShapeBox( s.kind , s.id, s.content.map(visit) );
      // then falls through
    }
    if (s.id === at) {
      const id = BOXINSERT + (insertId++) ;
      switch( dir ) {
      case 'NORTH': return makeShapeBox('VBOX', id, [ item , s ]);
      case 'SOUTH': return makeShapeBox('VBOX', id, [ s , item ]);
      case 'EAST':  return makeShapeBox('HBOX', id, [ s , item ]);
      case 'WEST':  return makeShapeBox('HBOX', id, [ item , s ]);
        // otherwize falls through
      }
    }
    return s ;
  };
  return at === '*' ? item : at === item.id ? shape : visit(shape);
}

// --------------------------------------------------------------------------
// --- Insertions
// --------------------------------------------------------------------------

const quadrant = ( dx , dy , x , y ) => {
  let dir, best = 10000 ;
  const qdir = ( d , w ) => { if (0 <= w && w < best) { best = w ; dir = d; } };
  qdir( 'NORTH', y - dy.pos );
  qdir( 'SOUTH', dy.pos + dy.dim - y );
  qdir( 'EAST',  dx.pos + dx.dim - x );
  qdir( 'WEST',  x - dx.pos );
  return dir;
};

const isHead = (d,p) => ( d.pos <= p && p <= d.pos + INSETS );
const isTrail = (d,p) => ( d.pos + d.dim - INSETS <= p && p <= d.pos + d.dim ) ;
const inside = (x,y) => (g) => {
  const dx = g.dx ;
  const dy = g.dy ;
  return ( dx.pos < x && x < dx.pos + dx.dim &&
           dy.pos < y && y < dy.pos + dy.dim );
} ;

const targetAt = ( grid , x , y ) => {
  if (!grid) return undefined;
  const dx = grid.dx ;
  const dy = grid.dy ;
  let dir ;
  switch( grid.kind ) {
  case 'ITEM':
    dir = quadrant(dx,dy,x,y);
    break;
  case 'HBOX':
    if (isHead(dy,y)) { dir = 'NORTH'; break; }
    if (isTrail(dy,y)) { dir = 'SOUTH'; break; }
    return targetAt( grid.content.find(inside(x,y)), x , y );
  case 'VBOX':
    if (isHead(dx,x)) { dir = 'WEST'; break; }
    if (isTrail(dx,x)) { dir = 'EAST'; break; }
    return targetAt( grid.content.find(inside(x,y)), x , y );
  }
  return dir && Object.assign( { at:grid.id, dir } , makePosition(grid) ) ;
};

const TARGET_PLAIN = { at:'*', dir:'*', left:0, top:0 };

// --------------------------------------------------------------------------
// --- Resizing Events
// --------------------------------------------------------------------------

const onResizeStart = ({ id,resizer,dp,dq }) => {
  dp.root = dp.dim ;
  dq.root = dq.dim ;
  freezeGrid( resizer.grid );
  resizer.id = id ;
  resizer.splitters = [resizer.splitters[id]] ;
  resizer.element.setState({ resizer });
};

const onResizeDrag = ({ id,resizer,dp,dq },offset) => {
  offset = Math.max( dp.min - dp.root , offset );
  offset = Math.min( dq.root - dq.min , offset );
  resizer.offset = offset ;
  dp.drag = dp.root + offset ;
  dq.drag = dq.root - offset ;
  resizeGrid( resizer.grid );
  resizer.element.forceUpdate();
};

const onResizeStop = ({ resizer }) => {
  let shape = makeShapeOfGrid( resizer.grid );
  resizer.element.setShape( shape );
};

const onResizeReset = ({ resizer }) => {
  resizer.element.setShape( undefined );
};

// --------------------------------------------------------------------------
// --- Splitters & Targets
// --------------------------------------------------------------------------

const ITEMCLASS = 'dome-xGridLayout-item dome-container' ;
const HDRAGZONE = 'dome-xGridLayout-splitter dome-xGridLayout-hsplit dome-color-dragzone' ;
const HDRAGGING = 'dome-xGridLayout-splitter dome-xGridLayout-hdrag  dome-color-dragging' ;
const VDRAGZONE = 'dome-xGridLayout-splitter dome-xGridLayout-vsplit dome-color-dragzone' ;
const VDRAGGING = 'dome-xGridLayout-splitter dome-xGridLayout-vdrag  dome-color-dragging' ;

class HSPLIT extends React.Component {
  render() {
    let {x,y,width,height,...handler} = this.props ;
    let id = handler.id ;
    let { id:sid , offset=0 } = handler.resizer ;
    return (
      <DraggableCore
        onStart={() => {
          onResizeStart(handler);
          this.forceUpdate();
        }}
        onDrag={(_evt,data) => {
          onResizeDrag(handler,data.x - x + 2);
          this.forceUpdate();
        }}
        onStop={() => onResizeStop(handler)}
        >
        <div className={ id === sid ? HDRAGGING : HDRAGZONE }
             onClick={(evt) => evt.altKey && onResizeReset(handler)}
             style={{ top:y, height, left:x+offset-2, width:4 }} />
      </DraggableCore>
    );
  }
}

class VSPLIT extends React.Component {
  render() {
    let {x,y,width,height,...handler} = this.props ;
    let id = handler.id ;
    let { id:sid , offset=0 } = handler.resizer ;
    return (
      <DraggableCore
        onStart={() => {
          onResizeStart(handler);
          this.forceUpdate();
        }}
        onDrag={(_evt,data) => {
          onResizeDrag(handler,data.y - y + 2);
          this.forceUpdate();
        }}
        onStop={() => onResizeStop(handler)}
        >
        <div className={ id === sid ? VDRAGGING : VDRAGZONE }
             onDoubleClick={(evt) => evt.altKey && onResizeReset(handler)}
             style={{ top:y+offset-2, height:4, left:x, width }} />
      </DraggableCore>
    );
  }
}

const TARGET = ({target:{ dir,left,top,width,height }}) => {
  switch(dir) {
  case 'NORTH':
    top = top - 3 ; height = 6 ;
    break;
  case 'SOUTH':
    top = top + height - 3 ; height = 6 ;
    break;
  case 'WEST':
    left = left -3 ; width = 6 ;
    break;
  case 'EAST':
    left = left + width -3 ; width = 6 ;
    break;
  }
  let style = { left, top, width, height };
  return <div className='dome-xGridLayout-target' style={style} />;
};

const HOLDER = ({position}) => (
  <div className='dome-xGridLayout-holder' style={position} />
);

const ELEMENT = ({id,className,style,children}) => (
  <div key={id} className={className} style={style}>
    { children }
  </div>
);

// --------------------------------------------------------------------------
// --- Grid Splitters
// --------------------------------------------------------------------------

function splitSequence( d,ds,fn )
{
  const n = ds.length || 0 ;
  if (n<=0) return;
  const dt = ds[n-1] ;
  const dn = { resize:false, dim:0, min:0 };
  const trail = d.room ;
  if (trail > 0) {
    dn.resize = true; dn.dim = trail;
    let i,p,di ;
    for (i = 0, p = -1; i < n; i++) {
      di = ds[i];
      p = di.resize ? i : p ;
      if (p>=0) {
        fn(di.pos+di.dim,ds[p],dn);
      }
    }
  } else {
    const dr = ds.slice(1).concat(dn);
    const ps = Array(n);
    const qs = Array(n);
    let i,k ;
    for (i = 0, k = -1; i < n; i++)
      k = ps[i] = ds[i].resize ? i : k ;
    for (i = n-1, k = -1; 0 <= i; i--)
      k = qs[i] = dr[i].resize ? i : k ;
    ds.forEach((di,i) => {
      var p = ps[i];
      var q = qs[i];
      if (p>=0 && q>=0)
        fn(di.pos+di.dim,ds[p],dr[q]);
    });
  }
}

function extendItem( d , fn ) {
  if (d.resize && d.room > 0) {
    const df = { resize:true, dim:d.room, min:0 };
    fn(d.pos + d.dim,d,df);
  }
};

function splitGrid( resizer,grid )
{
  var SID = 0 ;
  const splitters = resizer.splitters ;
  const makeHsplit = (dy) => (x,dp,dq) => {
    var id = SID++;
    var s = (
      <HSPLIT id={id} key={id} resizer={resizer}
              x={x} y={dy.pos} height={dy.dim}
              dp={dp} dq={dq}
              />) ;
    splitters.push(s);
  };
  const makeVsplit = (dx) => (y,dp,dq) => {
    var id = SID++;
    var s = (
      <VSPLIT id={id} key={id} resizer={resizer}
              x={dx.pos} y={y} width={dx.dim}
              dp={dp} dq={dq}
              />) ;
    splitters.push(s);
  };
  function visit(g) {
    if (!g) return;
    switch(g.kind) {
    case 'ITEM':
      extendItem( g.dx , makeHsplit(g.dy) );
      extendItem( g.dy , makeVsplit(g.dx) );
      return;
    case 'HBOX':
      splitSequence( g.dx , g.dxs , makeHsplit(g.dy) );
      g.content.forEach(visit);
      return;
    case 'VBOX':
      splitSequence( g.dy , g.dys , makeVsplit(g.dx) );
      g.content.forEach(visit);
      return;
    }
  }
  visit(grid);
}

// --------------------------------------------------------------------------
// --- Grid Elements
// --------------------------------------------------------------------------

const makePosition = ( {dx,dy}, padding=0 ) => ({
  left:    dx.pos + padding,
  top:     dy.pos + padding,
  width:   dx.dim - padding,
  height:  dy.dim - padding
});

function makeElement( render = ELEMENT, item, padding )
{
  if (!item) return null;
  const { id, content:{className:itemClass,style:itemStyle,children,...itemProps} } = item;
  const position = makePosition( item, padding );
  const className = itemClass ? ITEMCLASS + " " + itemClass : ITEMCLASS ;
  const style = Object.assign( {}, itemStyle , position );
  return render({id,className,style,children,...itemProps});
}

function orderElements( e1 , e2 )
{
  let a = e1.key ;
  let b = e2.key ;
  if (!a || a < b) return -1;
  if (!b || a > b) return 1;
  return 0;
}

// --------------------------------------------------------------------------
// --- GridItem
// --------------------------------------------------------------------------

/**
   @summary Elementary GridLayout Component.
   @property {string} id - Component identifier
   @property {boolean} display - Whether to mount the component
   @property {number} width - Desired component width
   @property {number} height - Desired component height
   @property {number} minWidth - Minimum component width
   @property {number} minHeight - Minium component height
   @property {directions} [fill] - Direction(s) the component fills in
   @property {directions} [resize] - Direction(s) the component can be resized in
   @property {directions} [shrink] - Direction(s) the component can be shrinked in
   @property {string} [className] - Additional class of the component
   @property {string} [handle] - class name of the handler for dragging the component
   @property {object} [style] - Additional style of the component
   @property {React.children} children - grid item content
   @description

   The `id` property is mandatory for the GridLayout container
   to property manage its different components. All items in the same GridLayout shall
   have distinct identifiers.

   Direction properties (with type `directions`) can take the following values:
   `'none'`, `'horizontal'`, `'vertical'` or `'both'`.
 */
export const GridItem = (props) => null;

// --------------------------------------------------------------------------
// --- Grid H/V Boxes
// --------------------------------------------------------------------------

/**
   @property {ident} [id] - the box identifier
   @property {direction} dir - either `'horizontal'` or `'vertical'`
   @property {GridContent} [children] - internal grid contents
   @summary Layout its content in an horizontal or vertical box.
   @description

This container is a _fake_ component thats simply groups several
`GridItem`s or `GridBox`es horizontally or vertically.

It can be used only as direct children of `GridLayout`
and other `GridBox` containers.

See also:
  - [[GridLayout]] top-level container
  - [[GridItem]] elementary component
  - [[GridHbox]] horizontal box
  - [[GridVbox]] vertical box
*/
export const GridBox = (props) => null ;

/**
   [[GridBox]] with horizontal layout
   @property {ident} [id] - the box identifier
*/
export const GridHbox = (props) => null ;

/**
   [[GridBox]] with vertical layout
   @property {ident} [id] - the box identifier
*/
export const GridVbox = (props) => null ;

// --------------------------------------------------------------------------
// --- User Grid & Components Extraction
// --------------------------------------------------------------------------

import { register, classOf } from 'dome/misc/register' ;

register(GridBox,  'DOME_GRIDLAYOUT_BOX');
register(GridHbox, 'DOME_GRIDLAYOUT_HBOX');
register(GridVbox, 'DOME_GRIDLAYOUT_VBOX');
register(GridItem, 'DOME_GRIDLAYOUT_ITEM');

/**
   @summary Extract shape from GridChildren.
   @parameter {GridChildren} children - Grid items elements arranged in grids
   @parameter {direction} [dir] - default direction
   @return {Shape} the associated shape
   @description
   Converts a React JSX-based grid of items into a Shape object.
 */
export function makeChildrenShape( children, dir )
{
  const makeEltShape = (elt) => {
    let { id, width, height } = elt.props ;
    return { kind: 'ITEM', id, width, height };
  };

  const makeBoxShape = (dir,elt) => {
    let { id, children } = elt.props ;
    let gs = makeShapes(children);
    return makeShapeDir(dir,id,gs);
  };

  const makeShapes = (children) => {
    return React.Children.map(children,(elt) => {
      if (!elt) return null;
      switch( classOf(elt) ) {
      case 'DOME_GRIDLAYOUT_ITEM':
        return makeEltShape(elt);
      case 'DOME_GRIDLAYOUT_HBOX':
        return makeBoxShape('horizontal',elt);
      case 'DOME_GRIDLAYOUT_VBOX':
        return makeBoxShape('vertical',elt);
      case 'DOME_GRIDLAYOUT_BOX':
        return makeBoxShape(elt.props.dir,elt);
      default:
        console.warn('[Dome.GridLayout] Unknown grid box', elt);
        return null;
      }
    });
  };

  return makeShapeDir( dir, undefined, makeShapes(children) );
}

function makeChildrenGrid( dir, items, children, shape )
{
  let kid = 0 ;
  let index = {} ;

  const indexElt = (elt) => {
    let { id } = elt.props ;
    let props = index[id];
    if (!props) props = index[id] = {};
    Object.assign( props , elt.props );
    return props;
  };

  const makeGridElt = (elt) => makeGridItem(indexElt(elt));

  const makeGridBox = (dir,elt) => {
    let { id, children } = elt.props ;
    if (!id) id = BOXID + (++kid) ;
    return makeGridDir(dir,id,makeGrids(children));
  };

  const makeGrids = (children) => {
    return React.Children.map(children,(elt) => {
      if (!elt) return null;
      switch( classOf(elt) ) {
      case 'DOME_GRIDLAYOUT_ITEM':
        return makeGridElt(elt);
      case 'DOME_GRIDLAYOUT_HBOX':
        return makeGridBox('horizontal',elt);
      case 'DOME_GRIDLAYOUT_VBOX':
        return makeGridBox('vertical',elt);
      case 'DOME_GRIDLAYOUT_BOX':
        return makeGridBox(elt.props.dir,elt);
      default:
        console.warn('[Dome.GridLayout] Unknown grid box', elt);
        return null;
      }
    });
  };

  const makeShape = (s) => {
    switch( s && s.kind ) {
    case 'ITEM':
      let props = index[ s.id ] ;
      if (!props) return null;
      index[ s.id ] = undefined ;
      return makeGridItem( props, s.width, s.height );
    case 'HBOX':
      return makeGridHbox( s.id, s.content.map(makeShape) );
    case 'VBOX':
      return makeGridVbox( s.id, s.content.map(makeShape) );
    default:
      return null;
    }
  };

  items && items.forEach && items.forEach( indexElt );

  if (shape)
    return makeShape(shape);
  else
    return makeGridDir(dir,BOXID,makeGrids(children));
}

// --------------------------------------------------------------------------
// --- GridLayout Core
// --------------------------------------------------------------------------

/**
   @class
   @summary Grid-based Flexible Container.
   @property {direction} [dir] - Default children layout (`'horizontal'` or `'vertical'`)
   @property {number}    [padding] - Padding between items
   @property {Shape}     [shape] - The desired shape (defaults to children grid)
   @property {GridItem[]} [items] - A collection of items (defaults to children items)
   @property {GridContent} [children] - Grid items arranged in box (used for default items and shape)
   @property {ident}     [dragged]  - Dragged item to materialize
   @property {object}    [dragging] - Dragging event to localize with `onTarget()`
   @property {object}    [target]   - Insertion target to materialze
   @property {function}  [onReshape] - Callback with the updated shape
   @property {function}  [onTarget] - Callback when dragging is a valid target
   @property {function}  [render] - Rendering function for items
   @property {React.ref} [targetRef] - Reference for D&D drop target
   @description

Low-level GridLayout container, with only resizing capabilities.
Additional rendering options are available:

- `dragged` : item being dragged, materialized with a dragging background;
- `dragging` : current D&D event to notify `onTarget()` with;
- `target` : `{at,dir,left,top,width,height}` insertion position to materialize;
- `shape:Shape` : desired reshaping of the children grid;
- `onReshape(Shape)` : notified when grid content has been resized;
- `onTarget(Target)` : notified when `dragging` corresponds to a new target;
- `render({id,className,style,handle,children,...})` : rendering function for the provided item.

The rendering function shall return a keyed React element or fragment.
It receives all properties of the associated item to render, with
class and style merged with the `dome-xGridLayout-item` base class
and the absolute coordinates of the item inside the container.

*/

export class GridLayoutCore extends React.Component
{

  constructor(props) {
    super(props);
    this.state = {};
  }

  setShape( newshape )
  {
    const { onReshape, shape } = this.props ;
    onReshape && onReshape(newshape);
    this.setState({ resizer:undefined });
  }

  render() {
    const { targetRef, padding=0 } = this.props ;
    return (
      <div className='dome-xGridLayout' ref={targetRef}>
        <AutoSizer key='grid'>{({width,height}) => this.renderSized(width-padding,height-padding)}</AutoSizer>
      </div>
    );
  }

  renderSized(width, height)
  {
    const { dragged } = this.props ;
    const { resizer:resizing } = this.state ;
    let grid,markers=[] ;
    if (resizing) {
      // When Resizing
      grid = resizing.grid ;
      markers = resizing.splitters ;
      layoutGrid(grid,width,height);
    } else {
      const {
        shape, dir,
        dragging, onTarget,
        items, children
      } = this.props ;
      // Compute Layout
      grid = makeChildrenGrid( dir, items, children, shape );
      if (grid) layoutGrid(grid,width,height);
      // Compute Dragging & notify Target
      let targetted ;
      if (dragging) {
        if (grid) {
          const r = dragging.targetClientRect ;
          if (r) {
            const x = dragging.clientX - r.left ;
            const y = dragging.clientY - r.top ;
            targetted = targetAt( grid, x, y );
          }
        } else {
          targetted = Object.assign( { width, height } , TARGET_PLAIN ) ;
        }
      }
      if (onTarget) {
        const { at,dir } = targetted || {} ;
        const held = dragging ? dragging.held : false ;
        if ( this.targetAt !== at ||
             this.targetDir !== dir ||
             this.targetHeld !== held )
        {
          this.targetAt = at ;
          this.targetDir = dir ;
          this.targetHeld = held ;
          if (targetted) targetted.shape = makeShapeOfGrid(grid);
          setImmediate(() => onTarget(targetted));
        }
      }
      const { target } = this.props ;
      if (target && target.at !== dragged) {
        markers.push( <TARGET key='target' target={target}/> );
      }
      if (grid && !dragging && !target) {
        // Splitters
        splitGrid( { grid,element:this,splitters:markers } ,grid );
      }
    }
    const elements = [];
    const { render, padding } = this.props ;
    iter(grid,(item) => {
      let e = makeElement(render,item,padding);
      if (e) elements.push(e);
      if (dragged && dragged === item.id)
        markers.push(<HOLDER key='holder' position={makePosition(item)}/>);
    });
    return [
      (<React.Fragment key='items'>{elements.sort(orderElements)}</React.Fragment>),
      (<React.Fragment key='markers'>{markers}</React.Fragment>)
    ];
  };
}

// --------------------------------------------------------------------------
// --- GridLayout Full
// --------------------------------------------------------------------------

const positionOfStyle = ({left,top,width,height}) => ({left,top,width,height});

const DRAGGABLEITEM =
      (dnd,anchor,onSelfDrag,insert) =>
      ({id,className,style,handle,children}) =>
      ( id === insert
        ? ( <HOLDER key='DOME$holder' position={positionOfStyle(style)}/> )
        : (
          <DragSource
            key={id}
            dnd={dnd}
            handle={handle}
            onStart={() => onSelfDrag(id,{x:style.left,y:style.top})}
            >
            {(dragging) => {
              let theStyle = style ;
              if (dragging && anchor) {
                theStyle = Object.assign( {} , style );
                theStyle.left = anchor.x + dragging.deltaX ;
                theStyle.top  = anchor.y + dragging.deltaY ;
                className  += ' dome-dragging' ;
              }
              return (<div className={className} style={theStyle}>{children}</div>);
            }}
          </DragSource>
        )
      );

/**
   @class
   @summary Grid Container.
   @property {direction} [dir] - Default children layout (`'horizontal'` or `'vertical'`)
   @property {number}    [padding] - Padding between items
   @property {Shape}     [shape] - The desired shape (defaults to children grid)
   @property {GridItem[]} [items] - A collection of items (defaults to children items)
   @property {Grid}      [children] - Grid items arranged in box (used for default items and shape)
   @property {string}    [settings] - User-settings key for making the shape persistent
   @property {DnD}       [dnd] - Optional D&D controller to be used
   @property {GridItem}  [holding] - Dragged external element
   @property {function}  [onTarget] - Callback for dragged target proposal
   @property {function}  [onReshape] - Callback on reshaping self content
   @property {function}  [onInsert] - Callback on dropping the holding element
   @property {function}  [onDnd] - Callback on D&D events
   @property {function}  [onXxx] - Other D&D callback events
   @description

Layout several components with nested vertical and horizontal boxes.

Direct children of the container must be either:
- [[GridBox]] and its derivated
- [[GridItem]] for elementary component

Top-level children are laidout vertically (default) or horizontally according
to the `dir` property. Nested boxes of same directions are flattened,
and singleton boxes simply lift-up their content into their parent box.

You may dynamically change the box hierarchy, without causing unmounting
and re-monting the different items. Actually, the container renders all
the collected `GridItem` elements as a flat array ordered by keys.

All item specifications are taken from the provided items. However, the grid
layout of the items is taken from the provided shape, the settings of the
children grix boxes, in this order of priority. Extra items or missing items are
simply ignored from the shape taken into account.

GridLayout containers can be used as drop targets, both for re-arranging
internal grid items, or to insert external drag sources inside.
If you supply an external [[DnD]] controller,
the GridLayout will register itself as a drop target. Otherwize, it will
use its own controller.

The callbacks `onReshape` and `onTarget` are invoked on drag and drop operations:
- `onReshape(Shape)` is invoked when the grid elements are resized or rearranged;
- `onTarget(Target)` in invoked when a drag source targets an element of the grid;
- `onInsert(Shape,Target)` when a drag source is dropped inside the grid, at some
target position, possibly resulting in the given new shape.

When dragging a source over the grid, the grid element specified by the `holding`
property of the grid is used to materialize the insertion of the dragged source
inside the grid. To decline a dragging operation, the `onTarget()` must return a
falsy value other than `undefined` (eg: `false`).

A `Target` is a plain serialisable object with the following properties:
- `at:ident` the box or item identifier where to insert the target,
or `'*'` when targetting an empty shape;
- `dir:'NORTH'|'EAST'|'SOUTH'|'WEST'` the direction to insert the target item along,
or `'*'` when targetting an empty shape;
- `id:ident` the inserted item identifier.

A `Shape` is a plain serializable object with the following properties:
- `{ kind:'HBOX', id, content: [Shape,…] }` for horizontal boxes,
- `{ kind:'VBOX', id, content: [Shape,…] }` for vertical boxes,
- `{ kind:'ITEM', id, height, width }` for leaf items.

*/
export class GridLayout extends React.Component
{

  constructor(props) {
    super(props);
    this.state = {};
    this.dnd = this.props.dnd || new DnD();
    this.onReloadSettings = this.onReloadSettings.bind(this);
    this.onReshape = this.onReshape.bind(this);
    this.onTarget = this.onTarget.bind(this);
    this.onSelfDrag = this.onSelfDrag.bind(this);
    this.onDnd = this.onDnd.bind(this);
    this.container = React.createRef();
  }

  componentDidMount() {
    // DEPRECATED
    Settings.onWindowSettings(this.onReloadSettings);
  }

  componentWillUnmont() {
    // DEPRECATED
    Settings.offWindowSettings(this.onReloadSettings);
  }

  computeTargetProposal(target) {
    if (!target) return undefined;
    const { at,dir } = target ;
    const { dragged } = this.state ;
    if (dragged)
      return at === dragged ? undefined : { id:dragged,at,dir };
    else {
      const { holding } = this.props ;
      const id = holding && holding.props && holding.props.id ;
      return at === id ? undefined : { id,at,dir };
    }
  }

  computeNewShapeForTarget(target) {
    if (!target) return [];
    const { shape,at,dir } = target ;
    const { holding } = this.props ;
    const { dragged,inserted:oldInsert } = this.state ;
    let item,inserted,newShape ;
    if (dragged) {
      item = get(shape,dragged);
      newShape = makeShapeInsert( shape, at, dir, item );
    }
    else if (holding && holding.props) {
      const { id,width,height } = holding.props ;
      if (at === id) {
        inserted = oldInsert ;
        newShape = shape ;
      } else {
        inserted = { at,dir,id } ;
        item = { kind:'ITEM',id,width,height };
        newShape = makeShapeInsert( shape,at,dir,item );
      }
    }
    return [inserted,newShape];
  }

  onReloadSettings() {
    const { settings, onReshape } = this.props ;
    if (!settings) return;
    const newShape = Settings.getWindowSettings( settings, Json.jAny, undefined );
    this.setState({ shape: newShape });
    if (onReshape) onReshape( newShape );
  }

  onReshape(newShape) {
    const { settings, shape:setShape, onReshape } = this.props ;
    if (!setShape) this.setState({ shape: newShape });
    if (settings) Settings.setWindowSettings( settings, newShape );
    if (onReshape) onReshape( newShape );
  }

  onTarget(newTarget) {
    const proposal = this.computeTargetProposal(newTarget);
    if (!proposal) this.setState({target:undefined});
    else {
      const { onTarget } = this.props ;
      const { held } = this.state ;
      const approval = onTarget && onTarget(proposal) ;
      const valid = approval === undefined || approval ;
      if (valid) {
        if ( held ) {
        const [inserted,holdedShape] = this.computeNewShapeForTarget(newTarget);
          this.setState({held:false,target:undefined,inserted,holdedShape});
        } else
          this.setState({target: newTarget});
      } else
        this.setState({target: undefined});
    };
  }

  // Self dragged callback, see DRAGGABLEITEM
  onSelfDrag(dragged,anchor) {
    this.setState({ dragged, anchor });
  }

  // Generic D&D event
  onDnd(dragging) {
    dispatchEvent(dragging,this.props);
    switch( dragging && dragging.move ) {
    case 'HOLD': this.setState({held: true}); break;
    case 'MOVE': this.setState({held: false}); break;
    case 'DROP':
      let { target, inserted, holdedShape:shape } = this.state ;
      if (target)
        [inserted,shape] = this.computeNewShapeForTarget(target);
      if (inserted) {
        const { onInsert } = this.props ;
        const callback = onInsert || this.onReshape ;
        callback && callback(shape,inserted);
      } else {
        shape && this.onReshape(shape);
      }
      // Continue on 'STOP'
    case 'STOP':
      this.setState({
        dragged: undefined,
        anchor: undefined,
        target: undefined,
        held: undefined,
        inserted: undefined,
        holdedShape: undefined
      });
      break;
    }
  }

  render() {
    const { shape:propShape, dir, items, children, holding, padding, settings } = this.props ;
    const { shape:newShape, target, dragged, anchor, holdedShape, inserted } = this.state ;
    const setShape = propShape === null ? {} : propShape ;
    const insert = inserted ? inserted.id : undefined ;
    const render = DRAGGABLEITEM(this.dnd,anchor,this.onSelfDrag,insert);
    const shape = holdedShape || setShape || newShape ||
          Settings.getWindowSettings(settings,Json.jAny,undefined) ;
    return (
      <DropTarget
        dnd={this.dnd}
        targetRef={this.container}
        onDnd={this.onDnd}
        >
        {(dragging) => (
          <GridLayoutCore
            targetRef={this.container}
            dir={dir}
            padding={padding}
            shape={shape}
            items={items}
            dragging={dragging}
            onReshape={this.onReshape}
            onTarget={this.onTarget}
            dragged={dragged}
            target={target}
            render={render}
            >
            {children}
            {inserted ? holding : null}
          </GridLayoutCore>
        )}
      </DropTarget>
    );
  }
}

// --------------------------------------------------------------------------
