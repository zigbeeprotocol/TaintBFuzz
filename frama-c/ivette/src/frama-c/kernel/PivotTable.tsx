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
// --- Pivot Table
// --------------------------------------------------------------------------

import React from 'react';
import { TitleBar } from 'ivette';
import * as Server from 'frama-c/server';
import { Button } from 'dome/controls/buttons';
import { LED } from 'dome/controls/displays';
import { Scroll } from 'dome/layout/boxes';
import * as Status from 'frama-c/kernel/Status';
import * as States from 'frama-c/states';
import { GlobalState, useGlobalState } from 'dome/data/states';
import * as PivotState from 'frama-c/plugins/pivot/api/general';
import PivotTableUI from 'react-pivottable/PivotTableUI';
import 'frama-c/kernel/PivotTable-style.css';

// --------------------------------------------------------------------------
// --- Pivot Table for Properties
// --------------------------------------------------------------------------

interface PivotTableProps {
  data: string[][];
}

const PivotGlobalState = new GlobalState({});

export function Pivot(props: PivotTableProps): JSX.Element {
  const [state, setState] = useGlobalState(PivotGlobalState);
  return (
    <PivotTableUI
      data={props.data}
      onChange={setState}
      {...state}
    />
  );
}

function PivotTable(rawData: PivotState.tableStateType): JSX.Element {
  const data = new Array(rawData.length > 0 ? rawData.length - 1 : 0);
  if (rawData.length > 0) {
    const headers = rawData[0];
    for (let i = 1; i < rawData.length; i++) {
      const src = rawData[i];
      data[i - 1] = {};
      for (let j = 0; j < headers.length; j++) {
        data[i - 1][headers[j]] = src[j];
      }
    }
  }
  return (<Pivot data={data} />);
}

function PivotTableBuild(): JSX.Element {
  const rawData = States.useSyncValue(PivotState.pivotState);
  const [computing, setComputing] = React.useState(false);
  const [error, setError] = React.useState('');
  async function handleError(err: string): Promise<void> {
    const msg =
      `The pivot table could not be built: an error has occured (${err}).`;
    setError(msg);
    Status.setMessage({ text: msg, kind: 'error' });
  }
  async function compute(): Promise<void> {
    setComputing(true);
    setError('');
    Server.send(PivotState.compute, [])
      .then(() => setComputing(false))
      .catch((err) => { setComputing(false); handleError(err); });
  }
  if (rawData && rawData.length > 0) {
    return (PivotTable(rawData));
  }
  if (computing) {
    return (
      <div className="pivot-centered">
        <div>
          <LED status="active" blink /> Computing…
        </div>
      </div>
    );
  }
  const err = error ? <div className="part"> {error} </div> : undefined;
  return (
    <div className="pivot-centered">
      {err}
      <div className="part">
        <Button
          icon="EXECUTE"
          label="Compute"
          title="Builds the pivot table. This may take a few moments."
          onClick={compute}
        />
      </div>
    </div>
  );
}

export default function PivotTableComponent(): JSX.Element {
  return (
    <>
      <TitleBar />
      <Scroll>
        <PivotTableBuild />
      </Scroll>
    </>
  );
}

// --------------------------------------------------------------------------
