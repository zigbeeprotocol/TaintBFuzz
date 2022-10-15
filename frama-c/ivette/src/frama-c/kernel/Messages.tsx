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

import * as React from 'react';
import * as Dome from 'dome';

import { IconButton } from 'dome/controls/buttons';
import { Label, Cell } from 'dome/controls/labels';
import { Page } from 'dome/text/pages';
import { Icon } from 'dome/controls/icons';
import { Scroll, Vbox } from 'dome/layout/boxes';
import { RSplit, BSplit } from 'dome/layout/splitters';
import * as Forms from 'dome/layout/forms';
import * as Arrays from 'dome/table/arrays';
import { Table, Column, Renderer } from 'dome/table/views';
import * as Compare from 'dome/data/compare';
import { State, GlobalState, useGlobalState } from 'dome/data/states';

import { TitleBar } from 'ivette';
import * as States from 'frama-c/states';
import * as Ast from 'frama-c/kernel/api/ast';
import * as Kernel from 'frama-c/kernel/api/services';

type Message = Kernel.messageData;
type logkind = Kernel.logkind;

// --------------------------------------------------------------------------
// --- Filters
// --------------------------------------------------------------------------

interface Search {
  category?: string;
  message?: string;
}

type KindFilter = Record<logkind, boolean>;
type PluginFilter = { [key: string]: boolean };
type EmitterFilter = {
  kernel: boolean;
  plugins: PluginFilter;
  others: boolean; // default for Frama-C plugins not in the plugins field.
};

interface Filter {
  currentFct: boolean;
  search: Search;
  kind: KindFilter;
  emitter: EmitterFilter;
}

/* Only warnings and errors are shown by default. */
const kindFilter: KindFilter = {
  RESULT: false,
  FEEDBACK: false,
  DEBUG: false,
  WARNING: true,
  ERROR: true,
  FAILURE: true,
};

/* The fields must be exactly the short names of Frama-C plugins used in
   messages. They are all shown by default. */
const pluginFilter: PluginFilter = {
  'aorai': true,
  'dive': true,
  'e-acsl': true,
  'eva': true,
  'from': true,
  'impact': true,
  'inout': true,
  'metrics': true,
  'nonterm': true,
  'pdg': true,
  'report': true,
  'rte': true,
  'scope': true,
  'server': true,
  'slicing': true,
  'variadic': true,
  'wp': true,
};

const emitterFilter = {
  kernel: true,
  plugins: pluginFilter,
  others: true,
};

const defaultFilter: Filter = {
  currentFct: false,
  search: {},
  kind: kindFilter,
  emitter: emitterFilter,
};

function filterKind(filter: KindFilter, msg: Message): boolean {
  return filter[msg.kind];
}

function filterEmitter(filter: EmitterFilter, msg: Message): boolean {
  if (msg.plugin === 'kernel')
    return filter.kernel;
  if (msg.plugin in filter.plugins)
    return filter.plugins[msg.plugin];
  return filter.others;
}

function searchCategory(
  search: string | undefined,
  msg: string | undefined
): boolean {
  if (!search || search.length < 2)
    return true;
  if (!msg)
    return false;
  const message = msg.toLowerCase();
  const array = search.toLowerCase().split(' ');
  let empty = true;
  let show = false;
  let hide = false;
  array.forEach((str: string) => {
    if (str.length > 1) {
      if (str.charAt(0) === '-') {
        if (message.includes(str.substring(1)))
          hide = true;
      }
      else if (message.includes(str))
        show = true;
      else
        empty = false;
    }
  });
  return (empty || show) && !hide;
}

function searchString(search: string | undefined, msg: string): boolean {
  if (!search || search.length < 3)
    return true;
  if (search.charAt(0) === '"' && search.slice(-1) === '"') {
    const exact = search.slice(1, -1);
    return msg.includes(exact);
  }
  const message = msg.toLowerCase();
  const array = search.toLowerCase().split(' ');
  let show = true;
  array.forEach((str: string) => {
    if (str.length > 1 && !message.includes(str))
      show = false;
  });
  return show;
}

function filterSearched(search: Search, msg: Message): boolean {
  return (searchString(search.message, msg.message) &&
    searchCategory(search.category, msg.category));
}

function filterFunction(
  filter: Filter,
  kf: string | undefined,
  msg: Message
): boolean {
  if (filter.currentFct)
    return (kf === msg.fct);
  return true;
}

function filterMessage(
  filter: Filter,
  kf: string | undefined,
  msg: Message
): boolean {
  return (filterFunction(filter, kf, msg) &&
    filterSearched(filter.search, msg) &&
    filterKind(filter.kind, msg) &&
    filterEmitter(filter.emitter, msg));
}

// --------------------------------------------------------------------------
// --- Filters panel and ratio
// --------------------------------------------------------------------------

function Section(p: Forms.SectionProps): JSX.Element {
  const settings = `ivette.messages.filter.${p.label}`;
  return (
    <Forms.Section label={p.label} unfold settings={settings}>
      {p.children}
    </Forms.Section>
  );
}

function Checkbox(p: Forms.CheckboxFieldProps): JSX.Element {
  const lbl = p.label.charAt(0).toUpperCase() + p.label.slice(1).toLowerCase();
  return <Forms.CheckboxField label={lbl} state={p.state} />;
}

function MessageKindCheckbox(props: {
  kind: logkind,
  kindState: Forms.FieldState<KindFilter>,
}): JSX.Element {
  const { kind, kindState } = props;
  const state = Forms.useProperty(kindState, kind);
  return <Checkbox label={kind} state={state} />;
}

function PluginCheckbox(props: {
  plugin: string,
  pluginState: Forms.FieldState<PluginFilter>,
}): JSX.Element {
  const state = Forms.useProperty(props.pluginState, props.plugin);
  return <Checkbox label={props.plugin} state={state} />;
}

function MessageFilter(props: { filter: State<Filter> }): JSX.Element {
  const state = Forms.useValid(props.filter);
  const search = Forms.useProperty(state, 'search');
  const categoryState = Forms.useProperty(search, 'category');
  const messageState = Forms.useProperty(search, 'message');
  const kindState = Forms.useProperty(state, 'kind');
  const kindCheckboxes =
    Object.keys(kindFilter).map((k) => (
      <MessageKindCheckbox key={k} kind={k as logkind} kindState={kindState} />
    ));
  const emitterState = Forms.useProperty(state, 'emitter');
  const kernelState = Forms.useProperty(emitterState, 'kernel');
  const othersState = Forms.useProperty(emitterState, 'others');
  const pluginState = Forms.useProperty(emitterState, 'plugins');
  const pluginCheckboxes =
    Object.keys(pluginFilter).map((p) => (
      <PluginCheckbox key={p} plugin={p} pluginState={pluginState} />
    ));

  return (
    <Forms.Page className="message-search">
      <Forms.CheckboxField
        label="Current function"
        title="Only show messages emitted at the current function"
        state={Forms.useProperty(state, 'currentFct')}
      />
      <Section label="Search">
        <Forms.TextField
          label="Category"
          state={categoryState}
          placeholder="Category"
          title={'Search in message category.\n'
            + 'Use -<name> to hide some categories.'}
        />
        <Forms.TextField
          label="Message"
          state={messageState}
          placeholder="Message"
          title={'Search in message text.\n'
            + 'Case-insensitive by default.\n'
            + 'Use "text" for an exact case-sensitive search.'}
        />
      </Section>
      <Section label="Kind">
        {kindCheckboxes}
      </Section>
      <Section label="Emitter">
        <div className="message-emitter-category">
          <Forms.CheckboxField label='Kernel' state={kernelState} />
        </div>
        <div className="message-emitter-category">
          {pluginCheckboxes}
        </div>
        <div className="message-emitter-category">
          <Forms.CheckboxField label='Others' state={othersState} />
        </div>
      </Section>
    </Forms.Page>
  );
}

function FilterRatio<K, R>(
  { model }: { model: Arrays.ArrayModel<K, R> }
): JSX.Element {
  const [filtered, total] = [model.getRowCount(), model.getTotalRowCount()];
  const title = `${filtered} displayed messages / ${total} total messages`;
  return (
    <Label className="component-info" title={title}>
      {filtered} / {total}
    </Label>
  );
}

// --------------------------------------------------------------------------
// --- Messages Columns
// --------------------------------------------------------------------------

const renderKind: Renderer<logkind> =
  (kind: logkind): JSX.Element => {
    const label = kind.toLocaleLowerCase();
    let icon = '';
    let color = 'black';
    switch (kind) {
      case 'RESULT': icon = 'ANGLE.RIGHT'; break;
      case 'FEEDBACK': icon = 'CIRC.INFO'; break;
      case 'DEBUG': icon = 'HELP'; break;
      case 'WARNING': icon = 'ATTENTION'; color = '#C00000'; break;
      case 'ERROR': case 'FAILURE': icon = 'WARNING'; color = '#C00000'; break;
    }
    return <Icon title={label} id={icon} fill={color} />;
  };

const renderCell: Renderer<string> =
  (text: string): JSX.Element => (<Cell title={text}>{text}</Cell>);

const renderMessage: Renderer<string> =
  (text: string): JSX.Element =>
    (<div title={text} className="message-cell"> {text} </div>);

const renderDir: Renderer<Ast.source> =
  (loc: Ast.source): JSX.Element =>
    (<Cell label={loc.dir} title={loc.file} />);

const renderFile: Renderer<Ast.source> =
  (loc: Ast.source): JSX.Element => (
    <Cell label={`${loc.base}:${loc.line}`} title={loc.file} />
  );

const MessageColumns = (): JSX.Element => (
  <>
    <Column
      id="kind"
      title="Message kind"
      label="Kind"
      width={42}
      align="center"
      render={renderKind}
    />
    <Column
      id="plugin"
      label="Emitter"
      title="Frama-C kernel or plugin"
      width={75}
      render={renderCell}
    />
    <Column
      id="category"
      label="Category"
      title="Only for warning and debug messages"
      width={150}
      render={renderCell}
    />
    <Column
      id="message"
      label="Message"
      fill
      render={renderMessage}
    />
    <Column
      id="fct"
      label="Function"
      width={150}
      render={renderCell}
    />
    <Column
      id="dir"
      label="Directory"
      width={240}
      visible={false}
      getter={(msg: Message) => msg?.source}
      render={renderDir}
    />
    <Column
      id="file"
      label="File"
      width={150}
      getter={(msg: Message) => msg?.source}
      render={renderFile}
    />
    <Column
      id="key"
      label="Id"
      title="Message emission order"
      width={42}
      visible={false}
    />
  </>
);

// -------------------------------------------------------------------------
// --- Mesages Table
// -------------------------------------------------------------------------

const bySource =
  Compare.byFields<Ast.source>({ file: Compare.alpha, line: Compare.number });

const byMessage: Compare.ByFields<Message> = {
  key: Compare.lift(parseInt, Compare.bignum),
  kind: Compare.structural,
  plugin: Compare.string,
  category: Compare.defined(Compare.string),
  fct: Compare.defined(Compare.alpha),
  source: Compare.defined(bySource),
};

const globalFilterState = new GlobalState(defaultFilter);

export default function RenderMessages(): JSX.Element {

  const [model] = React.useState(() => {
    const f = (msg: Message): string => msg.key;
    const m = new Arrays.CompactModel<string, Message>(f);
    m.setOrderingByFields(byMessage);
    return m;
  });

  const data = States.useSyncArray(Kernel.message).getArray();

  React.useEffect(() => {
    model.removeAllData();
    model.updateData(data);
    model.reload();
  }, [model, data]);

  const filterState = useGlobalState(globalFilterState);
  const [filter] = filterState;
  const [selection, updateSelection] = States.useSelection();
  const selectedFct = selection?.current?.fct;
  const [selectedMsg, selectMsg] = React.useState<Message|undefined>(undefined);
  const [text, setText] = React.useState('');

  React.useEffect(() => {
    if (selectedFct !== selectedMsg?.fct)
      selectMsg(undefined);
  }, [selectedFct, selectedMsg?.fct]);

  React.useEffect(() => {
    model.setFilter((msg: Message) => filterMessage(filter, selectedFct, msg));
  }, [model, filter, selectedFct]);

  const onMessageSelection = React.useCallback(
    (msg: Message) => {
      selectMsg(msg);
      setText(msg.message);
      if (msg.fct && msg.marker) {
        const location = { fct:msg.fct, marker:msg.marker };
        updateSelection({ location });
      }
    }, [updateSelection],
  );

  const [showFilter, flipFilter] =
    Dome.useFlipSettings('ivette.messages.showFilter', true);

  const MessagePanel = (
    <Vbox style={{ height: '100%' }}>
      <IconButton
        icon="CROSS"
        title="Close"
        onClick={() => setText('')}
        style={{ margin: '0 auto' }}
      />
      <Scroll>
        <Page className="message-page"> {text} </Page>
      </Scroll>
    </Vbox>
  );

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
        settings="ivette.messages.filterSplit"
        defaultPosition={225}
        unfold={showFilter}
      >
        <BSplit
          settings="ivette.messages.messageSplit"
          defaultPosition={90}
          unfold={text !== ''}
        >
          <Table<string, Message>
            model={model}
            sorting={model}
            selection={selectedMsg?.key}
            onSelection={onMessageSelection}
            settings="ivette.messages.table"
          >
            <MessageColumns />
          </Table>
          {MessagePanel}
        </BSplit>
        <Scroll>
          <MessageFilter filter={filterState} />
        </Scroll>
      </RSplit>
    </>
  );
}
