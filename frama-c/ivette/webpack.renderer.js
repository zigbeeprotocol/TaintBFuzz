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
   Template from $(DOME)/template/webpack.main.js

   This webpack definitions will be merged into electron-webpack
   ones thanks to electron-webpack.json configuration file.

   You may extend it with your own additions.
*/

const path = require('path');
const DOME = process.env.DOME || path.resolve( __dirname , 'dome' );

// --------------------------------------------------------------------------

module.exports = {
  module: {
    rules: [
      { test: /\.css$/, use: [ 'css-loader' ] },
      { test: /\.(ts|js)x?$/, use: [ 'babel-loader' ], exclude: /node_modules/ }
    ],
    strictExportPresence: true
  },
  resolve: {
    extensions: ['.ts', '.tsx', '.js', 'jsx', '.json'],
    alias: {
      'frama-c/api':  path.resolve( __dirname , 'src/frama-c/api/generated' ),
      'frama-c':      path.resolve( __dirname , 'src/frama-c' ),
      'ivette@ext':   path.resolve( __dirname , 'src/renderer/Extensions' ),
      'ivette@lab':   path.resolve( __dirname , 'src/renderer/Laboratory' ),
      'ivette':       path.resolve( __dirname , 'src/ivette' ),
      'dome/misc':    path.resolve( DOME , 'misc' ),
      'dome/system':  path.resolve( DOME , 'misc/system.ts' ),
      'dome$':        path.resolve( DOME , 'renderer/dome.tsx' ),
      'dome':         path.resolve( DOME , 'renderer' ),
      'react-dom':    '@hot-loader/react-dom'
    }
  },
  devServer: {
    watchOptions: {
      ignored: '**/.#*'
    }
  }
} ;

// --------------------------------------------------------------------------
