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
// --- Dome Classes
// --------------------------------------------------------------------------

import _ from 'lodash' ;
import React from 'react' ;

// --------------------------------------------------------------------------
// --- Register a Dome Class
// --------------------------------------------------------------------------

export function register(Component,NAME) {
  Component._DOME = NAME ;
  Component.istanceOf = (elt) => (elt.type ? elt.type._DOME === NAME : false) ;
}

// --------------------------------------------------------------------------
// --- Get the Dome Class of a Component
// --------------------------------------------------------------------------

export function classOf(elt) {
  return elt && elt.type && elt.type._DOME ;
}

// --------------------------------------------------------------------------
// --- Dispatch Children components among different Dome Classes
// --------------------------------------------------------------------------

/*
   Split a React Children structure according to filter.
   For each field { key: spec } in the filter, returns
   a field { key: selection } with all children satisfying
   the given spec (undefined if none).
   Filter specification can be: a Dome class name,
   an array of Dome class names, or 'undefined' for all non-matched
   children in the filter.

   Relies on React.Children.map instead ot React.Children.toArray
   in order to avoid putting keys in original children when not necessary.
*/
export function dispatch(children,filter)
{

  var others = undefined;

  const acceptor = _.mapValues( filter , (spec,field) => {
    switch(typeof(spec)) {
    case 'string':
      return (elt) => classOf(elt) === spec ;
    case 'undefined':
      others = field ;
      return undefined ;
    default:
      console.error('[Dome.common.register] non-supported filter spec',spec);
      return undefined ;
    }
  } );

  var count = 0 , first = true , accepted = [] ;
  const collected = _.mapValues( acceptor , (accept,_field) => {
    if (accept) {
      var empty = true ;
      var filtered =
          React.Children.map( children , (elt) => {
            var ok = elt && accept(elt);
            if (ok) empty = false ;
            if (others) {
              if (first) accepted.push(ok);
              else {
                if (ok) accepted[count] = ok ;
                count++;
              }
            }
            return ok && elt;
          });
      first = false ; count = 0 ;
      return empty ? undefined : filtered ;
    } else
      return undefined ;
  });

  if (others) {
    var empty = true ;
    var remaining = React.Children.map( children , (elt) => {
      var ok = elt && !accepted[count] ;
      if (ok) empty = false ;
      count++;
      return ok ? elt : null ;
    });
    if (!empty) collected[others] = remaining ;
  }

  return collected;
}

// --------------------------------------------------------------------------
