Dive is a Frama-C plugin specialized in the visualization of data dependencies.
It is intended to help the user find the origin of an imprecision in an Eva
analysis.


Dependencies
============

The front-end of Dive relies on several external tools and libraries :

- Node.js: a runtime environment for javascript to run programs outside a
  browser
- yarn: a package manager for javascript modules written for Node.js
- electron: a javascript framework for gui applications
- Ivette: the future Frama-C GUI
- Cytoscape: a javascript library to display graphs and interact with them
- Zmq: a multilanguage framework for common simple networking patterns
