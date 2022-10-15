---
subtitle: Live Code Editing
---

The **Dome** framework comes with live-editing facilities, provided by a
combination of
[Webpack Hot Module Reloading](https://webpack.js.org/concepts/hot-module-replacement)
and [React Hot Loader](http://gaearon.github.io/react-hot-loader).
This allows you to live edit your code and style sheets in real time while application
is running. This feature is only enabled in development mode, not in production mode
used when packaging the application for some platform.

Hot reloading for **React** components is known to be a fragile feature and to
suffer from certain limitations. Typically, files that can trigger live updates
must be reachable from the `./src` directory, without traversing symbolic links.
Style sheets in `*.css` files can be live edited, and **React** components in
`*.js` files as well. Most **React** components can be live-edited, provided
they are defined in top-level variables or exported by modules. Generally, the
component states are preserved during live-editing.

For live-editing to work properly, your source code must follow strict
configuration settings. These rules are enforced when using configuration files
and application entry points generated from **Dome** templates. Pay attention to
the provided comments in generated files when modifying them.

By default, we suggest to install the **Dome** framework in the sub-directory `./dome`
of your project. Being outside `./src`, this normally prevents **Dome** files to
be live-edited. If you want to also live-edit the framework, you shall move the
`$(DOME)` directory inside your own `./src`.
In particular, you might install the framework with `DOME=src/dome` for instance.

**State Management:** hot-reloading on **React** components preserves application
states _only_ when they are stored outside the reloaded module. This is the case
for local states maintained in **React** components, as they live in the virtual DOM.
However, for global application state stored in global variables of modules,
they simply vanish when a module is hot-reloaded. Worst, the virtual DOM will
be still bound to the _old_ versions of the modules. However, you usually don't
want to live-edit the global state of your application and mix new data with
old ones. A good practice is to separate files holding global state from files
implementing views. Hence, live-editing the views will not cause the global state
modules to reload, and views will stay in sync with your data. If you ever modify
the global state, you will have to reload the application window (`CmdOrCtrl-R`).

**Versioning Note:** the framework currently sticks on `webpack` version 3 and
`react-hot-loader` version 3, because of limitations and issues when using
`electron-webpack` with most recent versions of those libraries. However, we
hope to be able to migrate to newer versions as soon as possible.
