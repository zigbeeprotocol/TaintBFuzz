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
// --- Managing Errors
// --------------------------------------------------------------------------

/**
   @packageDocumentation
   @module dome/errors
*/

import React from 'react';
import { Debug } from 'dome';
import { Label } from 'dome/controls/labels';
import { Button } from 'dome/controls/buttons';

const D = new Debug('Dome');

// --------------------------------------------------------------------------
// --- Error Boundaries
// --------------------------------------------------------------------------

/**
   Alternative renderer in case of error.
   @param reload - callback for re-rendering the faulty component
 */
export interface ErrorRenderer {
  (error: unknown, info: unknown, reload: () => void): JSX.Element;
}

export interface CatchProps {
  /** Name of the error boundary. */
  label?: string;
  /** Alternative renderer callback in case of errors. */
  onError?: JSX.Element | ErrorRenderer;
}

interface CatchState {
  error?: unknown;
  info?: unknown;
}

/**
   React Error Boundaries.
 */
export class Catch extends React.Component<CatchProps, CatchState, unknown> {

  constructor(props: CatchProps) {
    super(props);
    this.state = {};
    this.logerr = this.logerr.bind(this);
    this.reload = this.reload.bind(this);
  }

  componentDidCatch(error: unknown, info: unknown): void {
    this.setState({ error, info });
  }

  logerr(): void {
    const { error, info } = this.state;
    D.error('catched error:', error, info);
  }

  reload(): void {
    this.setState({ error: undefined, info: undefined });
  }

  render(): JSX.Element {
    const { error, info } = this.state;
    if (error) {
      const { onError, label = 'Error' } = this.props;
      if (typeof (onError) === 'function')
        return onError(error, info, this.reload);
      return (
        <div>
          <Button
            icon="WARNING"
            kind="warning"
            title={typeof(error) === 'string' ? error : undefined}
            onClick={this.logerr}
          />
          <Button icon="RELOAD" onClick={this.reload} />
          <Label>{label}</Label>
        </div>
      );
    }
    return (<>{this.props.children}</>);
  }
}

// --------------------------------------------------------------------------
