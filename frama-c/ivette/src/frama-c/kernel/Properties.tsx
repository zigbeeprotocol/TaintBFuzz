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
// --- Properties
// --------------------------------------------------------------------------

import _ from 'lodash';
import React, { useEffect } from 'react';
import * as Dome from 'dome';
import * as Json from 'dome/data/json';
import * as States from 'frama-c/states';
import * as Compare from 'dome/data/compare';
import * as Settings from 'dome/data/settings';
import { Label, Code } from 'dome/controls/labels';
import { Icon } from 'dome/controls/icons';
import { IconButton, Checkbox } from 'dome/controls/buttons';
import * as Models from 'dome/table/models';
import * as Arrays from 'dome/table/arrays';
import { Table, Column, ColumnProps, Renderer } from 'dome/table/views';
import { TitleBar } from 'ivette';
import { Scroll, Folder } from 'dome/layout/boxes';

import { RSplit } from 'dome/layout/splitters';

import * as Ast from 'frama-c/kernel/api/ast';
import { statusData } from 'frama-c/kernel/api/properties';
import * as Properties from 'frama-c/kernel/api/properties';
import * as Eva from 'frama-c/plugins/eva/api/general';

type Property = statusData & Eva.propertiesData;

// --------------------------------------------------------------------------
// --- Filters
// --------------------------------------------------------------------------

const DEFAULTS: { [key: string]: boolean } = {
  currentFunction: false,
  'status.valid': true,
  'status.valid_hyp': true,
  'status.unknown': true,
  'status.invalid': true,
  'status.invalid_hyp': true,
  'status.considered_valid': false,
  'status.untried': false,
  'status.dead': false,
  'status.inconsistent': true,
  'kind.assert': true,
  'kind.invariant': true,
  'kind.variant': true,
  'kind.requires': true,
  'kind.ensures': true,
  'kind.instance': true,
  'kind.assumes': true,
  'kind.assigns': true,
  'kind.froms': true,
  'kind.allocates': true,
  'kind.behavior': false,
  'kind.reachable': false,
  'kind.axiomatic': true,
  'kind.pragma': true,
  'kind.others': true,
  'alarms.alarms': true, // show properties that are alarms
  'alarms.others': true, // show properties that are not alarms
  'alarms.overflow': true,
  'alarms.division_by_zero': true,
  'alarms.mem_access': true,
  'alarms.index_bound': true,
  'alarms.pointer_value': true,
  'alarms.shift': true,
  'alarms.ptr_comparison': true,
  'alarms.differing_blocks': true,
  'alarms.separation': true,
  'alarms.overlap': true,
  'alarms.initialization': true,
  'alarms.dangling_pointer': true,
  'alarms.special_float': true,
  'alarms.float_to_int': true,
  'alarms.function_pointer': true,
  'alarms.union_initialization': true,
  'alarms.bool_value': true,
  'eva.priority_only': false,
  'eva.data_tainted_only': false,
  'eva.ctrl_tainted_only': false,
};

function filter(path: string): boolean {
  const defaultValue = DEFAULTS[path] ?? true;
  return Settings.getWindowSettings(
    `ivette.properties.filter.${path}`,
    Json.jBoolean,
    defaultValue,
  );
}

function useFilter(path: string): [boolean, () => void] {
  const defaultValue = DEFAULTS[path] ?? true;
  return Dome.useFlipSettings(
    `ivette.properties.filter.${path}`,
    defaultValue,
  );
}

function filterStatus(
  status: Properties.propStatus,
): boolean {
  switch (status) {
    case 'valid':
      return filter('status.valid');
    case 'valid_under_hyp':
      return filter('status.valid_hyp');
    case 'invalid':
      return filter('status.invalid');
    case 'invalid_under_hyp':
      return filter('status.invalid_hyp');
    case 'inconsistent':
      return filter('status.inconsistent');
    case 'unknown':
      return filter('status.unknown');
    case 'considered_valid':
      return filter('status.considered_valid');
    case 'never_tried':
      return filter('status.untried');
    case 'valid_but_dead':
    case 'unknown_but_dead':
    case 'invalid_but_dead':
      return filter('status.dead');
    default:
      return true;
  }
}

function filterKind(
  kind: Properties.propKind,
): boolean {
  switch (kind) {
    case 'assert': return filter('kind.assert');
    case 'loop_invariant': return filter('kind.invariant');
    case 'loop_variant': return filter('kind.variant');
    case 'requires': return filter('kind.requires');
    case 'ensures': return filter('kind.ensures');
    case 'instance': return filter('kind.instance');
    case 'assigns': return filter('kind.assigns');
    case 'froms': return filter('kind.froms');
    case 'allocates': return filter('kind.allocates');
    case 'behavior': return filter('kind.behavior');
    case 'reachable': return filter('kind.reachable');
    case 'axiomatic': return filter('kind.axiomatic');
    case 'loop_pragma': return filter('kind.pragma');
    case 'assumes': return filter('kind.assumes');
    default: return filter('kind.others');
  }
}

function filterAlarm(alarm: string | undefined): boolean {
  if (alarm) {
    if (!filter('alarms.alarms')) return false;
    switch (alarm) {
      case 'overflow': return filter('alarms.overflow');
      case 'division_by_zero': return filter('alarms.division_by_zero');
      case 'mem_access': return filter('alarms.mem_access');
      case 'index_bound': return filter('alarms.index_bound');
      case 'pointer_value': return filter('alarms.pointer_value');
      case 'shift': return filter('alarms.shift');
      case 'ptr_comparison': return filter('alarms.ptr_comparison');
      case 'differing_blocks': return filter('alarms.differing_blocks');
      case 'separation': return filter('alarms.separation');
      case 'overlap': return filter('alarms.overlap');
      case 'initialization': return filter('alarms.initialization');
      case 'dangling_pointer': return filter('alarms.dangling_pointer');
      case 'is_nan_or_infinite':
      case 'is_nan': return filter('alarms.special_float');
      case 'float_to_int': return filter('alarms.float_to_int');
      case 'function_pointer': return filter('alarms.function_pointer');
      case 'initialization_of_union':
        return filter('alarms.union_initialization');
      case 'bool_value': return filter('alarms.bool_value');
      default: return false;
    }
  }
  return filter('alarms.others');
}

function filterEva(p: Property): boolean {
  let b = true;
  if (p.priority === false && filter('eva.priority_only'))
    b = false;
  switch (p.taint) {
    case 'not_tainted':
    case 'not_applicable':
      if (filter('eva.data_tainted_only') || filter('eva.ctrl_tainted_only'))
        b = false;
      break;
    case 'data_tainted':
      if (filter('eva.ctrl_tainted_only'))
        b = false;
      break;
    case 'control_tainted':
      if (filter('eva.data_tainted_only'))
        b = false;
      break;
  }
  return b;
}

function filterProperty(p: Property): boolean {
  return filterStatus(p.status)
    && filterKind(p.kind)
    && filterAlarm(p.alarm)
    && filterEva(p);
}

// --------------------------------------------------------------------------
// --- Property Columns
// --------------------------------------------------------------------------

const renderCode: Renderer<string> =
  (text: string): JSX.Element =>
    (<Code className="code-column" title={text}>{text}</Code>);

const renderTag: Renderer<States.Tag> =
  (d: States.Tag): JSX.Element =>
    (<Label label={d.label ?? d.name} title={d.descr} />);

const renderNames: Renderer<string[]> =
  (names: string[]): JSX.Element | null => {
    const label = names?.join(': ');
    return (label ? <Label label={label} /> : null);
  };

const renderDir: Renderer<Ast.source> =
  (loc: Ast.source): JSX.Element =>
    (<Code className="code-column" label={loc.dir} title={loc.file} />);

const renderFile: Renderer<Ast.source> =
  (loc: Ast.source): JSX.Element =>
    (<Code className="code-column" label={loc.base} title={loc.file} />);

const renderPriority: Renderer<boolean> =
  (prio: boolean): JSX.Element | null =>
    (prio ? <Icon id="ATTENTION" /> : null);

const renderTaint: Renderer<States.Tag> =
  (taint: States.Tag): JSX.Element | null => {
    let id = null;
    let color = 'black';
    switch (taint.name) {
      case 'not_tainted': id = 'DROP.EMPTY'; color = '#00B900'; break;
      case 'data_tainted': id = 'DROP.FILLED'; color = '#FF8300'; break;
      case 'control_tainted': id = 'DROP.FILLED'; color = '#73BBBB'; break;
      case 'error': id = 'HELP'; break;
      case 'not_applicable': id = 'MINUS'; break;
      default:
    }
    return (id ? <Icon id={id} fill={color} title={taint.descr} /> : null);
  };

function ColumnCode<Row>(props: ColumnProps<Row, string>): JSX.Element {
  return <Column render={renderCode} {...props} />;
}

function ColumnTag<Row>(props: ColumnProps<Row, States.Tag>): JSX.Element {
  return <Column render={renderTag} {...props} />;
}

// --------------------------------------------------------------------------
// --- Properties Table
// -------------------------------------------------------------------------

const bySource =
  Compare.byFields<Ast.source>({ file: Compare.alpha, line: Compare.number });

const byStatus =
  Compare.byRank(
    'inconsistent',
    'invalid',
    'invalid_under_hyp',
    'unknown',
    'valid_under_hyp',
    'valid',
    'invalid_but_dead',
    'unknown_but_dead',
    'valid_but_dead',
    'never_tried',
    'considered_valid',
  );

const byTaint =
  Compare.byRank(
    'data_tainted',
    'control_tainted',
    'not_tainted',
    'error',
    'not_applicable',
    'not_computed',
  );

const byProperty: Compare.ByFields<Property> = {
  status: byStatus,
  fct: Compare.defined(Compare.alpha),
  source: bySource,
  kind: Compare.structural,
  alarm: Compare.defined(Compare.alpha),
  names: Compare.array(Compare.alpha),
  predicate: Compare.defined(Compare.alpha),
  key: Compare.string,
  kinstr: Compare.structural,
  priority: Compare.structural,
  taint: byTaint,
};

const byDir = Compare.byFields<Ast.source>({ dir: Compare.alpha });
const byFile = Compare.byFields<Ast.source>({ base: Compare.alpha });

const byColumn: Arrays.ByColumns<Property> = {
  dir: Compare.byFields<Property>({ source: byDir }),
  file: Compare.byFields<Property>({ source: byFile }),
};

class PropertyModel
  extends Arrays.CompactModel<Json.key<'#property'>, Property> {

  private filterFun?: string;

  constructor() {
    super((p: Property) => p.key);
    this.setOrderingByFields(byProperty);
    this.setColumnOrder(byColumn);
    this.setFilter(this.filterItem.bind(this));
  }

  setFilterFunction(kf?: string): void {
    this.filterFun = kf;
    if (filter('currentFunction')) this.reload();
  }

  filterItem(prop: Property): boolean {
    const kf = prop.fct;
    const cf = this.filterFun;
    const filteringFun = cf && filter('currentFunction');
    const filterFunction = filteringFun ? kf === cf : true;
    return filterFunction && filterProperty(prop);
  }

}

// --------------------------------------------------------------------------
// --- Property Filter Form
// -------------------------------------------------------------------------

const Reload = new Dome.Event('ivette.properties.reload');

interface SectionProps {
  label: string;
  unfold?: boolean;
  children: React.ReactNode;
}

function Section(props: SectionProps): JSX.Element {
  const settings = `properties-section-${props.label}`;
  return (
    <Folder
      label={props.label}
      settings={settings}
      defaultUnfold={props.unfold}
    >
      {props.children}
    </Folder>
  );
}

interface CheckFieldProps {
  label: string;
  title?: string;
  highligh?: boolean; // Highlights the label when the value is [highligh]
  path: string;
}

function CheckField(props: CheckFieldProps): JSX.Element {
  const [value, setValue] = useFilter(props.path);
  const onChange = (): void => { setValue(); Reload.emit(); };
  return (
    <Checkbox
      style={{
        display: 'block',
        color: (props.highligh === value) ? 'red' : '',
      }}
      label={props.label}
      title={props.title}
      value={value}
      onChange={onChange}
    />
  );
}

/* eslint-disable max-len */

function PropertyFilter(): JSX.Element {
  return (
    <Scroll>
      <CheckField label="Current function" path="currentFunction" />
      <Section label="Status" unfold>
        <CheckField label="Valid" path="status.valid" />
        <CheckField label="Valid under hyp." path="status.valid_hyp" />
        <CheckField label="Unknown" path="status.unknown" />
        <CheckField label="Invalid" path="status.invalid" />
        <CheckField label="Invalid under hyp." path="status.invalid_hyp" />
        <CheckField label="Considered valid" path="status.considered_valid" />
        <CheckField label="Untried" path="status.untried" />
        <CheckField label="Dead" path="status.dead" />
        <CheckField label="Inconsistent" path="status.inconsistent" />
      </Section>
      <Section label="Property kind">
        <CheckField label="Assertions" path="kind.assert" />
        <CheckField label="Invariants" path="kind.invariant" />
        <CheckField label="Variants" path="kind.variant" />
        <CheckField label="Preconditions" path="kind.requires" />
        <CheckField label="Postconditions" path="kind.ensures" />
        <CheckField label="Instance" path="kind.instance" />
        <CheckField label="Assigns clauses" path="kind.assigns" />
        <CheckField label="From clauses" path="kind.froms" />
        <CheckField label="Allocates" path="kind.allocates" />
        <CheckField label="Behaviors" path="kind.behavior" />
        <CheckField label="Reachables" path="kind.reachable" />
        <CheckField label="Axiomatics" path="kind.axiomatic" />
        <CheckField label="Pragma" path="kind.pragma" />
        <CheckField label="Assumes" path="kind.assumes" />
        <CheckField label="Others" path="kind.others" />
      </Section>
      <Section label="Alarms">
        <CheckField label="Alarms" path="alarms.alarms" />
        <CheckField label="Others" path="alarms.others" />
      </Section>
      <Section label="Alarms kind">
        <CheckField label="Overflows" path="alarms.overflow" />
        <CheckField label="Divisions by zero" path="alarms.division_by_zero" />
        <CheckField label="Shifts" path="alarms.shift" />
        <CheckField label="Special floats" path="alarms.special_float" />
        <CheckField label="Float to int" path="alarms.float_to_int" />
        <CheckField label="_Bool values" path="alarms.bool_value" />
        <CheckField label="Memory accesses" path="alarms.mem_access" />
        <CheckField label="Index bounds" path="alarms.index_bound" />
        <CheckField label="Initializations" path="alarms.initialization" />
        <CheckField label="Dangling pointers" path="alarms.dangling_pointer" />
        <CheckField label="Pointer values" path="alarms.pointer_value" />
        <CheckField label="Function pointers" path="alarms.function_pointer" />
        <CheckField label="Pointer comparisons" path="alarms.ptr_comparison" />
        <CheckField label="Differing blocks" path="alarms.differing_blocks" />
        <CheckField label="Separations" path="alarms.separation" />
        <CheckField label="Overlaps" path="alarms.overlap" />
        <CheckField label="Initialization of unions" path="alarms.union_initialization" />
      </Section>
      <Section label="Eva">
        <CheckField
          label="High-priority only"
          path="eva.priority_only"
          title="Show only high-priority properties for the Eva analysis"
        />
        <CheckField
          label="Data-tainted only"
          path="eva.data_tainted_only"
          title="Show only data-tainted properties according to the Eva taint domain"
        />
        <CheckField
          label="Control-tainted only"
          path="eva.ctrl_tainted_only"
          title="Show only control-tainted properties according to the Eva taint domain"
        />
      </Section>
    </Scroll>
  );
}

/* eslint-enable max-len */

// -------------------------------------------------------------------------
// --- Property Columns
// -------------------------------------------------------------------------

function PropertyColumns(): JSX.Element {
  const statusDict = States.useTags(Properties.propStatusTags);
  const kindDict = States.useTags(Properties.propKindTags);
  const alarmDict = States.useTags(Properties.alarmsTags);
  const taintDict = States.useTags(Eva.taintStatusTags);
  const getStatus = React.useCallback(
    ({ status: st }: Property) => (statusDict.get(st) ?? { name: st }),
    [statusDict],
  );
  const getKind = React.useCallback(
    ({ kind: kd }: Property) => (kindDict.get(kd) ?? { name: kd }),
    [kindDict],
  );
  const getAlarm = React.useCallback(
    ({ alarm }: Property) => (
      alarm === undefined ? alarm : (alarmDict.get(alarm) ?? { name: alarm })
    ),
    [alarmDict],
  );
  const getTaint = React.useCallback(
    ({ taint }: Property) => (taintDict.get(taint) ?? { name: taint }),
    [taintDict],
  );
  return (
    <>
      <Column
        id="dir"
        label="Directory"
        width={240}
        visible={false}
        getter={(prop: Property) => prop?.source}
        render={renderDir}
      />
      <Column
        id="file"
        label="File"
        width={120}
        getter={(prop: Property) => prop?.source}
        render={renderFile}
      />
      <ColumnCode id="fct" label="Function" width={120} />
      <ColumnTag id="kind" label="Property kind" getter={getKind} width={120} />
      <ColumnTag id="alarm" label="Alarms" getter={getAlarm} width={160} />
      <Column
        id="names"
        label="Names"
        width={240}
        visible={false}
        render={renderNames}
      />
      <ColumnCode id="predicate" label="Predicate" fill />
      <ColumnCode id="descr" label="Property" fill visible={false} />
      <Column
        id="priority"
        label="Priority"
        title="Properties invalid in some context of the Eva analysis"
        icon="ATTENTION"
        width={30}
        visible={false}
        align="center"
        getter={(prop: Eva.propertiesData) => prop?.priority}
        render={renderPriority}
      />
      <ColumnTag
        id="taint"
        label="Taint"
        title="Properties tainted according to the Eva taint domain"
        icon="PAINTBRUSH"
        width={30}
        visible={false}
        align="center"
        getter={getTaint}
        render={renderTaint}
      />
      <ColumnTag
        id="status"
        label="Status"
        fixed
        width={100}
        align="center"
        getter={getStatus}
      />
    </>
  );
}

function FilterRatio({ model }: { model: PropertyModel }): JSX.Element {
  Models.useModel(model);
  const [filtered, total] = [model.getRowCount(), model.getTotalRowCount()];
  return (
    <Label
      className="component-info"
      title="Displayed Properties / Total"
      display={filtered !== total || true}
    >
      {filtered} / {total}
    </Label>
  );
}

// -------------------------------------------------------------------------
// --- Properties Table
// -------------------------------------------------------------------------

export default function RenderProperties(): JSX.Element {

  // Hooks
  const model = React.useMemo(() => new PropertyModel(), []);
  const kernelData = States.useSyncArray(Properties.status).getArray();
  const evaData = States.useSyncArray(Eva.properties).getArray();

  useEffect(() => {
    model.removeAllData();
    const data = new Array(kernelData.length);
    for (let i = 0; i < kernelData.length; i++) {
      const kernel = kernelData[i];
      const { key } = kernel;
      const eva = evaData.find((elt) => elt.key === key);
      data[i] = { ...kernel, ...eva };
    }
    model.updateData(data);
    model.reload();
  }, [model, kernelData, evaData]);

  const [selection, updateSelection] = States.useSelection();

  const [showFilter, flipFilter] =
    Dome.useFlipSettings('ivette.properties.showFilter', true);

  // Updating the filter
  Dome.useEvent(Reload, model.reload);
  const selectedFunction = selection?.current?.fct;
  React.useEffect(() => {
    model.setFilterFunction(selectedFunction);
  }, [model, selectedFunction]);

  // Callbacks

  const onPropertySelection = React.useCallback(
    ({ key: marker, fct }: Property) => {
      const location = { fct, marker };
      updateSelection({ location });
    }, [updateSelection],
  );

  const propertySelection = selection?.current?.marker;

  return (
    <>
      <TitleBar>
        <FilterRatio model={model} />
        <IconButton
          icon="CLIPBOARD"
          selected={showFilter}
          onClick={flipFilter}
          title="Toggle filters panel"
        />
      </TitleBar>
      <RSplit
        settings="ivette.properties.filterSplit"
        defaultPosition={200}
        unfold={showFilter}
      >
        <Table<string, Property>
          model={model}
          sorting={model}
          selection={propertySelection}
          onSelection={onPropertySelection}
          settings="ivette.properties.table"
        >
          <PropertyColumns />
        </Table>
        <PropertyFilter />
      </RSplit>
    </>
  );
}

// --------------------------------------------------------------------------
