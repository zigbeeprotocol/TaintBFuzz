---
subtitle: Application Design
---

This tutorial introduces how to design a **Dome** application within the
**Electron** & **React** frameworks.  You shall be reasonably familiar with
**React** concepts, but no knowledge of **Electron** is required.

A desktop **Dome** application looks like a native application, but is actually
a static web page rendered in a **Chrome** web browser. This is what provides
the **Electron** framework by default. **Dome** is simply a library of **React**
components and development templates tuned together to enable professional
application development.

This tutorial provides an overview of this environment and how to design a typical
**Dome** application.

## System Architecture

Following the **Electron** framework design, your application will consists of
two different processes interacting with each others.
One is responsible for the management of the main GUI resources
(windows, menu-bar, desktop interaction, user settings, etc.)
and is named the `Main` process.
The second one will be responsible for running the
web page holding the main application window, and is named the `Renderer` process.
Both kind of process communicates through the message-passing API provided by
the **Electron** framework.

When several instances of your application are running simultaneously, each invokation
have its own window, running its owan, separate `Renderer` process. However, the
**Dome** framework automatically makes them sharing the same `Main` process.

Hence, each application instance has its own working directory and command-line arguments,
depending on how its has been launched by the user. The **Dome** framework build
both command-line and desktop entry points, depending on each target platform.

## Event Driven Design

On the renderer process side, the **React** framework induces a natural design where
_Application State_ is separated from _Application Rendering_. Moreover,
following a popular design introduced with **Redux**, application rendering tend
to be written like a pure function (or _view_) on  the state, where user
actions are just state updater callbacks. Each time the state is modified, the
entire application rendering is recomputed, and **React** computes a minimal
diff to apply on the web page displayed in the main application window.

Putting everything together, its is recommended to design **Dome** application
into two different parts, both running in the `Renderer` process of each
application instance:

- **Application Internals (State)**
holding your application state and data and updating it in response to user or
system events;

- **Application Components (View)**
responsible for rendering the application main window and
binding callbacks to application services.

<img src="dataflow.png" style="float: right; width: 30em"/>

Such an architecture is typical of a _Model-View-Controller_ design, but
revisited to scale. In particular, data flow between those three different
layers shall follow a unique-direction pattern in order to avoid the
combinatorial explosion of interactions between components that is generally
observed in most Model-View-Controller designs.

Hence, data-flow shall follow one of the following routes between these
three layers, illustrated above:

- from `State` to `View` : your rendering components shall only access the
current application state and data;
- from `View` to `State` or `System` : user action callbacks shall only trigger
state update or system operation, not any other view direct modification.
- from `System` to `State` : upon completion, system services shall trigger state
updates that would in turn trigger new requests and view re-rendering.

## Data Management

To implement the recommended data-flow described above, you may use a full
featured [Redux](https://redux.js.org) platform or any other framework of your
choice. However, **Dome** provides you with many facilities for implementing
your data flow.

- **Global States** are necessary to implement the unidirectional data-flow. These
  data are stored in the renderer process, but outside of the view hierarchy of
  **React** components actually mounted in the DOM. Hence, it remains consistent whatever
  the evolution of the view. See `dome/state` module and the associated custom **React** hooks
  to implement global states. You may also use global JavaScript variables and emit events
  on your own.

- **View Updates** to make your views listening for updates of the various data
  sources, we encourage to use the **React** hooks we provide, since they
  transparently make your components to re-render when required. However,
  sometimes you will need to respond to special events by hand. For this purpose,
  you can use **Dome** as a central event emitter, by using `Dome.emit()`,
  `Dome.on()` and `Dome.off()` functions. Moreover, the `Dome.useUpdate()` and
  `Dome.useEvent()` hooks can be used to make your components being notified by
  events.

- **Window Settings** are stored a local file at the root of user's project, and
  remains generally unnoticed by most users. They typically include the window's
  position and dimension, resizable items position, fold/unfold states,
  presentation options, etc. Most
  **Dome** components with presentation options can be assigned a `settings` key
  to make their state persistent. Contrary to Global Settings, however, they are
  not shared across several windows. You may also access these data by using
  `Settings.setWindowSetting()` and `Settings.getWindowSetting()`, or the **React** hook
  `Settings.useWindowSetting()`. See also helpers `Dome.useXxxSettings()`.
  It is possible, from the application main menu, to reset all the window settings to their
  default values.

- **Local Storage** are stored in the same file than window settings, although
  they are not automatically reset to their initial values.
  This is very convenient to store persistent user data on a per-project basis.
  See `Settings.xxxLocalStorage()` functions for more details.

- **Global Settings** are stored in the user's home directory and automatically
  saved and load with your application; they are typically modified _via_ the
  Settings Window, which is accessible from the application menubar. In **Dome**,
  you can shall define a global settings by creating an instance of
  `Settings.GlobalSettings` class and use it with
  the `Settings.useGlobalSettings()` hook.
