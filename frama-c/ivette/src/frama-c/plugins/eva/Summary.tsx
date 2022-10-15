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

// React & Dome
import React from 'react';
import { LED } from 'dome/controls/displays';
import * as Ivette from 'ivette';
import * as States from 'frama-c/states';
import * as Eva from 'frama-c/plugins/eva/api/general';

import CoverageMeter, { percent } from './CoverageMeter';

import './style_summary.css';

function CoverageTable(data: Eva.programStatsType): JSX.Element {
  const { progFunCoverage: functions, progStmtCoverage: statements } = data;
  const functionsTotal = functions.reachable + functions.dead;
  const statementsTotal = statements.reachable + statements.dead;
  return (
    <table className="coverage-table">
      <thead>
        <tr>
          <th aria-label="Category" />
          <th>Analyzed</th>
          <th>Total</th>
          <th>Coverage</th>
          <th aria-label="Coverage Meter" />
        </tr>
      </thead>
      <tbody>
        <tr>
          <th>Functions</th>
          <td>{functions.reachable}</td>
          <td>{functionsTotal}</td>
          <td>{percent(functions)}</td>
          <td>
            <CoverageMeter coverage={functions} />
          </td>
        </tr>
        <tr>
          <th>Statements</th>
          <td>{statements.reachable}</td>
          <td>{statementsTotal}</td>
          <td>{percent(statements)}</td>
          <td>
            <CoverageMeter coverage={statements} />
          </td>
        </tr>
      </tbody>
    </table>
  );
}

function plural(count: number): string {
  return count === 1 ? '' : 's';
}

function Errors(data: Eva.programStatsType): JSX.Element {
  const { evaEvents: eva, kernelEvents: kernel } = data;
  const total = eva.warnings + eva.errors + kernel.warnings + kernel.errors;
  return (total > 0 ? (
    <>
      Some errors and warnings have been raised during the analysis:
      <table className="errors-table">
        <thead>
          <tr>
            <th aria-label="Plugin" />
            <th>Errors</th>
            <th>Warnings</th>
          </tr>
        </thead>
        <tbody>
          <tr>
            <th>Eva analyzer</th>
            <td>{eva.errors}</td>
            <td>{eva.warnings}</td>
          </tr>
          <tr>
            <th>Frama-C kernel</th>
            <td>{kernel.errors}</td>
            <td>{kernel.warnings}</td>
          </tr>
        </tbody>
      </table>
    </>
  ) :
    <>No errors or warnings raised during the analysis.</>
  );
}

function Alarms(data: Eva.programStatsType,
  categories: Map<string, States.Tag>): JSX.Element {
  const { progAlarms, alarmsStatuses: { invalid, unknown } } = data;
  const total = unknown + invalid;

  const label = (category: Eva.alarmCategory): string | undefined => (
    categories.get(category)?.descr
  );

  function order(e1: Eva.alarmEntry, e2: Eva.alarmEntry): number {
    const { other } = Eva.alarmCategory;
    const d = e2.count - e1.count;
    if (e1.category === other && e2.category === other)
      return d;
    if (e1.category === other)
      return 1;
    if (e2.category === other)
      return -1;
    return d || Eva.byAlarmCategory(e1.category, e2.category);
  }

  return (
    <>
      <span>{total}</span> alarm{plural(total)} generated by the analysis :
      <table className="alarms-table">
        <tbody>
          {progAlarms.sort(order).map((entry) => (
            <tr key={entry.category}>
              <td>{entry.count}</td>
              <td>{label(entry.category)}</td>
            </tr>
          ))}
        </tbody>
      </table>
      {invalid > 0 && (
        <div>
          {invalid} of them {invalid === 1 ? 'is a' : 'are'} sure
          alarm{plural(invalid)}.
        </div>
      )}
    </>
  );
}

function Statuses(data: Eva.programStatsType): JSX.Element {
  const { assertionsStatuses: assertions, precondsStatuses: preconds } = data;
  const all = (entry: Eva.statusesEntry): number => (
    entry.valid + entry.unknown + entry.invalid
  );
  const totalAssertions = all(assertions);
  const totalPreconds = all(preconds);
  const total = totalAssertions + totalPreconds;
  if (total > 0) {
    return (
      <>
        <table className="statuses-table">
          <thead>
            <tr>
              <th aria-label="Kind" />
              <th>Valid</th>
              <th>Unknown</th>
              <th>Invalid</th>
              <th>Total</th>
            </tr>
          </thead>
          <tbody>
            <tr>
              <th>Assertions</th>
              <td>{assertions.valid}</td>
              <td>{assertions.unknown}</td>
              <td>{assertions.invalid}</td>
              <td>{totalAssertions}</td>
            </tr>
            <tr>
              <th>Preconditions</th>
              <td>{preconds.valid}</td>
              <td>{preconds.unknown}</td>
              <td>{preconds.invalid}</td>
              <td>{totalPreconds}</td>
            </tr>
          </tbody>
        </table>
      </>
    );
  }

  return (<>No logical properties have been reached by the analysis.</>);

}

export function EvaSummary(): JSX.Element {
  const alarmCategories = States.useTags(Eva.alarmCategoryTags);
  const data = States.useSyncValue(Eva.programStats);
  const state = States.useSyncValue(Eva.computationState);

  if (state === 'not_computed')
    return (
      <div className="eva-summary-status">
        No Eva analysis has been run yet.
      </div>
    );

  if (state === 'computing')
    return (
      <div className="eva-summary-status">
        <LED status="active" blink />
        Eva analysis in progress…
      </div>
    );

  if (state === 'computed' && data && alarmCategories)
    return (
      <div className="eva-summary-box">
        <div className="eva-summary">
          <h1>Analysis Summary</h1>
          <h2>Coverage</h2>
          {CoverageTable(data)}
          <h2>Errors</h2>
          {Errors(data)}
          <h2>Alarms</h2>
          {Alarms(data, alarmCategories)}
          <h2>Statuses</h2>
          {Statuses(data)}
        </div>
      </div>
    );

  return (<></>);
}

function EvaSummaryComponent(): JSX.Element {
  return (
    <>
      <Ivette.TitleBar />
      <EvaSummary />
    </>
  );
}

Ivette.registerComponent({
  id: 'frama-c.plugins.eva_summary',
  group: 'frama-c.plugins',
  rank: 10,
  label: 'Eva Summary',
  title: 'Summary of the Eva analysis',
  children: <EvaSummaryComponent />,
});

// --------------------------------------------------------------------------
