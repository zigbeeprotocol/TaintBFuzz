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

import React from 'react';
import * as Json from 'dome/data/json';
import { Table, Column } from 'dome/table/views';
import { CompactModel } from 'dome/table/arrays';
import * as Arrays from 'dome/table/arrays';
import * as Compare from 'dome/data/compare';
import * as Ivette from 'ivette';
import * as States from 'frama-c/states';

import * as Eva from 'frama-c/plugins/eva/api/general';
import CoverageMeter, { percent } from './CoverageMeter';

type key = Json.key<'#fundec'>;
type stats = Eva.functionStatsData;

// --- Coverage Table ---

const ordering: Arrays.ByColumns<stats> = {
  fct: Compare.byFields({ key: Compare.string }),
  alarms: Compare.byFields({
    alarmStatuses: Compare.lift(
      (x) => x.unknown + x.invalid,
      Compare.number,
    ),
  }),
  sureAlarms: Compare.byFields(
    { alarmStatuses: Compare.byFields({ invalid: Compare.number }) },
  ),
  deadStatements: Compare.byFields({
    coverage: Compare.byFields(
      { dead: Compare.number },
    ),
  }),
  reachableStatements: Compare.byFields({
    coverage: Compare.byFields(
      { reachable: Compare.number },
    ),
  }),
  totalStatements: Compare.byFields(
    { coverage: Compare.lift((x) => x.reachable + x.dead, Compare.number) },
  ),
  coverage: Compare.byFields(
    {
      coverage: Compare.lift(
        (x) => x.reachable / (x.reachable + x.dead),
        Compare.number,
      ),
    },
  ),
};

class Model extends CompactModel<key, stats> {
  constructor() {
    super(Eva.functionStats.getkey);
    this.setColumnOrder(ordering);
    this.setSorting({ sortBy: 'coverage', sortDirection: 'ASC' });
  }
}

export function CoverageTable(): JSX.Element {
  const data = States.useSyncArray(Eva.functionStats).getArray();
  const [selection, updateSelection] = States.useSelection();

  const model = React.useMemo(() => new Model(), []);
  React.useEffect(() => model.replaceAllDataWith(data), [model, data]);

  const onSelection = ({ key }: stats): void => {
    updateSelection({ location: { fct: key } });
  };

  return (
    <Table
      model={model}
      sorting={model}
      selection={selection?.current?.fct}
      onSelection={onSelection}
      settings="ivette.coverage.table"
    >
      <Column
        id="fct"
        label="Function"
        align="left"
        width={200}
        fill
        getter={({ key }: stats) => key}
      />
      <Column
        id="alarms"
        label="Alarms"
        title="Number of alarms emitted by the Eva analysis"
        align="center"
        width={80}
        getter={({ alarmStatuses }: stats) => (
          alarmStatuses.invalid + alarmStatuses.unknown
        )}
      />
      <Column
        id="sureAlarms"
        label="Sure alarms"
        title="Number of sure alarms emitted by the Eva analysis"
        align="center"
        width={80}
        getter={({ alarmStatuses }: stats) => alarmStatuses.invalid}
      />
      <Column
        id="deadStatements"
        label="Dead"
        title="Number of statements unreachable to the Eva analysis"
        align="center"
        visible={false}
        width={80}
        getter={({ coverage }: stats) => coverage.dead}
      />
      <Column
        id="reachableStatements"
        label="Reachable"
        title="Number of statements reached by the Eva analysis"
        align="center"
        visible={false}
        width={80}
        getter={({ coverage }: stats) => coverage.reachable}
      />
      <Column
        id="totalStatements"
        label="Total"
        title="Total number of statements"
        align="center"
        visible={false}
        width={80}
        getter={({ coverage }: stats) => coverage.dead + coverage.reachable}
      />
      <Column
        id="coverage"
        label="Coverage"
        title="Coverage of the Eva analysis"
        align="center"
        width={80}
        getter={({ coverage }: stats) => coverage}
        render={(coverage) => <>{percent(coverage)}</>}
      />
      <Column
        id="coverage-meter"
        label=""
        align="center"
        width={80}
        getter={({ coverage }: stats) => coverage}
        render={(coverage) => (<CoverageMeter coverage={coverage} />)}
      />
    </Table>
  );
}

// --- Coverage Component ---

export default function CoverageComponent(): JSX.Element {
  return (
    <>
      <Ivette.TitleBar />
      <CoverageTable />
    </>
  );
}

Ivette.registerComponent({
  id: 'frama-c.plugins.eva_coverage',
  group: 'frama-c.plugins',
  rank: 10,
  label: 'Eva Coverage',
  title: 'Detailed coverage of the Eva analysis',
  children: <CoverageComponent />,
});

// --------------------------------------------------------------------------
