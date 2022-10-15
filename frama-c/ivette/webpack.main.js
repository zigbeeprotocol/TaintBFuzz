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
// --- Webpack extension for electron main-process
// --------------------------------------------------------------------------

/*
   Template of ./webpack.main.js from $(DOME)/template/webpack.main.js

   This webpack definitions will be merged into electron-webpack
   ones thanks to electron-webpack.json configuration file.

   You may extend it with your own additions.
*/

const path = require('path');
const DOME = process.env.DOME || path.resolve(__dirname , 'dome');
const ENV = process.env.DOME_ENV ;

// Do not use electron-devtools-installer in production mode
function domeDevtools() {
  switch(ENV) {
  case 'dev':
    return 'electron-devtools-installer';
  default:
    return path.resolve( DOME , 'misc/devtools.js' );
  }
}

// --------------------------------------------------------------------------

module.exports = {
  module: {
    rules: [
      { test: /\.(ts|js)x?$/, use: [ 'babel-loader' ], exclude: /node_modules/ }
    ],
    strictExportPresence: true
  },
  resolve: {
    extensions: ['.ts', '.tsx', '.js', 'jsx', '.json'],
    alias: {
      'dome$':         path.resolve( DOME , 'main/dome.ts' ),
      'dome/system$':  path.resolve( DOME , 'misc/system.ts' ),
      'dome/devtools': domeDevtools()
    }
  },
  devServer: {
    watchOptions: {
      ignored: '**/.#'
    }
  }
} ;

// --------------------------------------------------------------------------
