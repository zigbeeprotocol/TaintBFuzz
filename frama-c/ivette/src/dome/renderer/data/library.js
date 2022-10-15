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
// --- Data Collector
// --------------------------------------------------------------------------

/**
   @packageDocumentation
   @module dome/data/library
   @description
   This module allows to integrate data definitions within React elements.

   Typically, you can use it to define your own structure of logical elements
   and display them at different places in the GUI. For instance, you may
   want to define a custom list of elements, where each element
   will be rendered twice: locally with the currenly selected item, and in a side-bar
   or in the menu-bar, or for any other purpose than rendering. You want to declare
   your list like this:

   * ```jsx
   * <MyList>
   *   <MyItem id={A} ... >...</MyItem>
   *   <MyItem id={B} ... >...</MyItem>
   *   <MyItem id={C} ... >...</MyItem>
   * </MyList>
   * ```

   Dome data libraries, as provided by this module, allows you to define such
   collection of data mixed with rendered elements.

   Data are collected through libraries.
   You create libraries with `createLibrary()` or `useLocalLibrary()` and
   then provide them to `<Data.Item>`, `<Data.Component>`, `<Data.Node>` or
   `<Data.Fragment>` elements.

   At any (other) point of the tree, you can use the collected items
   with the `useLibrary()` custom React hook.

   Libraries are pushed down the React virtual tree _via_ React context,
   so you don't need to re-specify it for children of `<Data.Node/>`
   and `<Data.Fragment/>`.

   Items must be identified with a unique `id` ; they are sorted according
   to their `order` property, although `<Data.Fragment/>` and `<Data.Node/>`
   preserve the order of data collected from each of their children. Items are
   collected when they are actually _mounted_ by React,
   like any other React element.

   Data elements are normal React element, that might be rendered by
   visible elements in the DOM. You may think of data elements as having a
   double rendering: mounted data items are collected into libraries, and normal visible
   elements are collected into the React virtual DOM. Each kind of data element is
   rendered differenly with this respect:

   - `<Data.Item>` renders its children within a React fragment;
   - `<Data.Node>` is like an item, with its data children stored in the registered item;
   - `<Data.Component>` always renders 'null' and capture its React children elements
     in the registered item;
   - `<Data.Fragment>` renders its children within a React fragment, with optional context
     library and specified order.

   See each component for more details.

   As an example of use, the introductory example can be implemented as follows:

   ```jsx
     const lib = createLibrary();

     // To be used at any (possibly repeated) place in the hierarchy of react elements
     // Children items are only added to the library when the list is mounted
     const MyList = ({ children }) => {
       // Actually renders nothing if children only contains items.
       // The fragment makes items keep their declaration ordering.
       return (
          <Data.Fragment lib={lib}>{children}</Data.Fragment>
       );
     };

     // To be used also at any (possibly repeated) place in the hierarchy
     const MyItem = (props) => <Data.Item lib={lib} {...props} /> ;

     // To be used for instance at top-level inside a side-bar
     const MyListIndex = () => {
       let items = Data.useLibrary(lib);
       return (
         <ul>
           { items.map(({id,label}) => (<li key={id}>{label}</li>)) }
         </ul>
       );
     };
   ```
*/

import _ from 'lodash';
import React from 'react';
import * as Dome from 'dome';
import EventEmitter from 'events';

// --------------------------------------------------------------------------
// --- Libraries
// --------------------------------------------------------------------------

const reOrder = (items) =>
  _.sortBy(items, ['order', 'id'])
    .map((item, order) => Object.assign(item, { order }));

/**
    @summary Data Collector.
    @description
    Libraries are used to collect data through the React virtual DOM.
*/
class Library extends EventEmitter {

  constructor() {
    super();
    this.items = {};
    this.lastItems = {};
    this._trigger = _.debounce(this._trigger, 10);
  }

  _trigger() {
    if (!_.isEqual(this.items, this.lastItems)) {
      this.lastItems = this.items;
      this.sorted = undefined;
      this.emit('trigger');
    }
  };

  /**
     @summary Register Item.
     @param {object} item - must have an `'id'` property
   */
  add(item) {
    const id = item.id;
    if (Dome.DEVEL && this.items[id])
      console.warn(`[dome/data] duplicate item identifier (${id})`);
    this.items[id] = item;
    this._trigger();
  }

  /**
     @summary Remove Item.
     @param {string} id - the item identifier to remove
   */
  remove(id) {
    delete this.items[id];
    this._trigger();
  }

  /**
     @summary Bugger Contents.
     @return {Array<object>} items array sorted by `'order'` and `'id'` properties.
   */
  contents() {
    return this.sorted || (this.sorted = reOrder(this.items));
  }

  /**
     @summary Register callback.
     @param {function} callback - invoked when library contents changes
  **/
  on(callback) { this.on('trigger', callback); }

  /**
     @summary Un-register callback.
     @param {function} callback - callback to unregister
  **/
  off(callback) { this.off('trigger', callback); }

}

/**
   @summary Creates a Data library.
   @return {Library} a newly created, empty library.
   @description
   Same as `new Library()`.
 */
export function createLibrary() { return new Library(); }

/**
   @summary Collect living items from the library (Custom React Hook).
   @param {Library} library - the desired library
   @return {Array<items>} items currently mounted in the library
   @description
   This hook is automatically updated whenever an item is added or removed
   from the library.
 */
export function useLibrary(library) {
  const forceUpdate = Dome.useForceUpdate();
  Dome.useEmitter(library, 'trigger', forceUpdate);
  return library.contents();
}

/**
   @summary Use a locally created new library (Custom React Hook).
   @return {object} `{ library, items }` the local library and its collected items
   @description
   This is a combination of a locally created library _and_ its collected items.
   Same as:
   ```
   const library = React.useMemo( createLibrary , [] );
   const items = useLibrary( library );
   ```
 */
export function useLocalLibrary() {
  const library = React.useMemo(createLibrary, []);
  const items = useLibrary(library);
  return { library, items };
}

const CurrentLib = React.createContext();
const CurrentPath = React.createContext([]);

const makePath = (path, order) =>
  order === undefined ? path : path.slice(0, -1).concat(order);

/**
   @summary Current library (Custom React Hook).
   @return {Library} in local context
 */
export function useCurrentLibrary() {
  return React.useContext(CurrentLib);
}

// --------------------------------------------------------------------------
// --- Internals
// --------------------------------------------------------------------------

function useLocalItem({ lib: localLib, id, order, ...itemProps }, children) {
  const currentLib = React.useContext(CurrentLib);
  const currentPath = React.useContext(CurrentPath);
  const path = makePath(currentPath, order);
  React.useEffect(() => {
    const library = localLib || currentLib;
    if (id && library) {
      const item = { id, order: path, ...itemProps };
      if (children) item.children = children;
      library.add(item);
      return () => library.remove(id);
    } else
      return undefined;
  });
  return path;
};

function makeChildren(path, children) {
  const n = React.Children.count(children);
  if (n == 0) return null;
  else {
    const childContext = (elt, k) => {
      if (elt) {
        const newPath = path.concat(1 + k);
        return (
          <CurrentPath.Provider value={newPath}>
            {elt}
          </CurrentPath.Provider>
        );
      } else
        return elt;
    };
    return React.Children.map(children, childContext);
  }
}

// --------------------------------------------------------------------------
// --- Item Definition
// --------------------------------------------------------------------------

/**
   @summary Data Item definition.
   @property {Library} [lib] - data library collecting the item
   @property {string} [id] - item identifier
   @property {number} [order] - item local ordering (default: inherited)
   @property {any} [...props] - other item properties
   @property {React.Children} [children] - rendered elements
   @description
   Register a new item in the library:

   ```
   { id, order, props }
   ```

   If not specified, the current context library is used. If no identifier nor
   library is actually available, the item definition is skipped.

   An `<Item/>` element rendres its children in a nested, ordered fragment,
   but with the same current library than the inherited one, if any.
*/
export const Item = ({ children, ...props }) => {
  let path = useLocalItem(props);
  return (<React.Fragment>{makeChildren(path, children)}</React.Fragment>);
};

// --------------------------------------------------------------------------
// --- Component Definition
// --------------------------------------------------------------------------

/**
   @summary Data Component definition.
   @property {Library} [lib] - data library collecting the item (default: inherited)
   @property {string} id - item identifier (default: skip item definition)
   @property {number} [order] - item order (default: parent fragment ordering)
   @property {any} [...props] - registered item properties
   @property {React.Children} [children] - component _virtual_ elements
   @description
   Register a new item in the library. If enabled and not disabled,
   the collected item data will be:

   ```
   { id, order, props, children: React.Children }
   ```

   The specified order property is used to sort this item among its immediate
   neighbours in the React virtual DOM. The final item order is determined with
   respect to all the other collected items.

   Children elements of the `<Component/>` are _not_ mounted into the React
   virtual DOM.  However, they are stored in the `children` property of the
   item, and can be rendered in other parts of the DOM through
   `useCurrentLibrary()` react hook. The local context will _not_ be propagated
   to these children.

   The component element itself is rendered as `null` when mounted in the virtual DOM by React.
*/
export const Component = ({ children, ...props }) => {
  useLocalItem(props, children);
  return null;
};

// --------------------------------------------------------------------------
// --- Node Definition
// --------------------------------------------------------------------------

/**
   @summary Recursive Data Item definition.
   @property {Library} [lib] - data library collecting the item (default: inherited)
   @property {string} id - item identifier (default: skip item definition)
   @property {number} [order] - item order (default: parent fragment ordering)
   @property {any} [...props] - registered item properties
   @property {React.Children} [children] - sub-data and rendering of the item
   @description
   Register a new item in the library, as follows:

   ```
   { id, order, props, children: Array<item> }
   ```

   The specified order property is used to sort this item among its immediate
   neighbours in the React virtual DOM. The final item order is determined with
   respect to all the other collected items.

   A _new_ local library is created and associated to this `<Node/>` element, and propagated
   in children as the new context library. If necessary, you can obtain this local
   library with the `useContext()` react hook.

   Hence, children elements of the node item _are_ rendered in the virtual React DOM,
   but their data elements are collected and stored in the `children` property of the
   defined `<Node/>` item.
*/
export const Node = ({ children, ...props }) => {
  let { library, items } = useLocalLibrary();
  let path = useLocalItem(props, items);
  return (
    <CurrentLib.Provider value={library}>
      {makeChildren(path, children)}
    </CurrentLib.Provider>
  );
};

// --------------------------------------------------------------------------
// --- Fragment Definition
// --------------------------------------------------------------------------

/**
   @summary Ordered Data Collection.
   @property {Library} [lib] - local library to use
   @property {Sortable} [order] - local order to use (default: inherited)
   @property {boolean} [enabled] - fragment shall be rendered (default: `true`)
   @property {boolean} [disabled] - fragment shal not be rendered (default: `false`)
   @property {React.Children} [children] - sub-data and rendering of the data collection
 */
export const Fragment = ({ lib: localLib, order, enabled = true, disabled = false, children, ...localProps }) => {
  const currentLib = React.useContext(CurrentLib);
  const currentPath = React.useContext(CurrentPath);
  const library = localLib || currentLib;
  if (enabled && !disabled && React.Children.count(children) > 0) {
    const path = makePath(currentPath, order);
    return (
      <CurrentLib.Provider value={library}>
        {makeChildren(path, children)}
      </CurrentLib.Provider>
    );
  } else
    return null;
};

// --------------------------------------------------------------------------
