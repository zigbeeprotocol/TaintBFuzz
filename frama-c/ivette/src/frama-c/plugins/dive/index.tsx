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

import React, { useState, useEffect } from 'react';
import _ from 'lodash';
import { renderToString } from 'react-dom/server';
import * as Dome from 'dome';
import * as Ivette from 'ivette';
import * as Server from 'frama-c/server';
import * as States from 'frama-c/states';

import * as API from 'frama-c/plugins/dive/api';

import Cytoscape from 'cytoscape';
import CytoscapeComponent from 'react-cytoscapejs';
import './cytoscape_libs';
import 'cytoscape-panzoom/cytoscape.js-panzoom.css';

import tippy, * as Tippy from 'tippy.js';
import 'tippy.js/dist/tippy.css';
import 'tippy.js/themes/light-border.css';
import 'tippy.js/animations/shift-away.css';
import './tippy.css';

import { IconButton } from 'dome/controls/buttons';
import { Space } from 'dome/frame/toolbars';

import '@fortawesome/fontawesome-free/js/all';

import style from './style.json';
import layouts from './layouts.json';


const Debug = new Dome.Debug('dive');

interface Cxtcommand {
  content: string;
  select: () => void;
  enabled: boolean;
}

interface CytoscapeExtended extends Cytoscape.Core {
  cxtmenu(options: unknown): void;
  panzoom(options: unknown): void;
}

function callstackToString(callstack: API.callstack): string {
  return callstack.map((cs) => `${cs.fun}:${cs.instr}`).join('/');
}

function buildCxtMenu(
  commands: Cxtcommand[],
  content?: JSX.Element,
  action?: () => void,
): void {
  commands.push({
    content: content ? renderToString(content) : '',
    select: action || (() => { /* Do nothing */ }),
    enabled: !!action,
  });
}

/* double click events for Cytoscape */

function enableDoubleClickEvents(cy: Cytoscape.Core, delay = 350): void {
  let last: Cytoscape.EventObject | undefined;
  cy.on('click', (e) => {
    if (last && last.target === e.target &&
      e.timeStamp - last.timeStamp < delay) {
      e.target.trigger('double-click', e);
    }
    last = e;
  });
}

/* The Dive class handles the selection of nodes according to user actions.
   To prevent cytoscape to automatically select (and unselect) nodes wrongly,
   we make some nodes unselectable. We then use the functions below to make
   the nodes selectable before (un)selecting them. */

function select(node: Cytoscape.NodeSingular): void {
  node.selectify();
  node.select();
}

function unselect(node: Cytoscape.NodeSingular): void {
  node.selectify();
  node.unselect();
}

export type mode = 'explore' | 'overview';

class Dive {
  headless: boolean;
  cy: Cytoscape.Core;
  mode: mode = 'explore';
  _layout = '';
  layoutOptions: Cytoscape.LayoutOptions | undefined;
  currentSelection: string | null = null;
  onSelect: ((_: States.Location[]) => void) | null = null;
  selectedLocation: (States.Location | undefined) = undefined;

  constructor(cy: Cytoscape.Core | null = null) {
    this.cy = cy || Cytoscape();
    this.headless = this.cy.container() === null;
    this.cy.elements().remove();

    // Remove previous listeners
    this.cy.off('click');
    this.cy.off('double-click');

    // Add new listeners
    enableDoubleClickEvents(this.cy);
    this.cy.on('click', 'node', (event) => this.clickNode(event.target));
    this.cy.on('double-click', '$node > node', // compound nodes
      (event) => this.doubleClickNode(event.target));
    (this.cy as CytoscapeExtended).panzoom({});

    this.layout = 'cose-bilkent';

    if (!this.headless) {
      this.cy.scratch('cxtmenu')?.destroy?.(); // Remove previous menu
      this.cy.scratch('cxtmenu', (this.cy as CytoscapeExtended).cxtmenu({
        selector: 'node',
        commands: (node: Cytoscape.NodeSingular) => this.onCxtMenu(node),
      }));
    }

    this.refresh();
  }

  onCxtMenu(node: Cytoscape.NodeSingular): Cxtcommand[] {
    const data = node.data();
    const commands = [] as Cxtcommand[];
    buildCxtMenu(commands,
      <><div className="fas fa-binoculars fa-2x" />Explore</>,
      () => { this.explore(node); });
    if (data.kind === 'composite')
      buildCxtMenu(commands,
        <><div className="fa fa-expand-arrows-alt fa-2x" />Unfold</>);
    else
      buildCxtMenu(commands);
    if (data.backward_explored === 'no')
      buildCxtMenu(commands,
        <div><div className="fa fa-eye fa-2x" />Show</div>,
        () => this.show(node));
    else
      buildCxtMenu(commands,
        <><div className="fa fa-eye-slash fa-2x" />Hide</>,
        () => this.hide(node));
    return commands;
  }

  remove(node: Cytoscape.NodeSingular): void {
    const parent = node.parent();
    node.remove();
    this.cy.$id(`${node.id()}-more`).remove();
    if (parent.nonempty() && parent.children().empty())
      this.remove(parent as Cytoscape.NodeSingular); // Recursively remove parents
  }

  referenceFile(fileName: string): Cytoscape.NodeSingular {
    const id = `file_${fileName}`;
    const node = this.cy.$id(id);
    if (node.nonempty()) {
      return node;
    }

    return this.cy.add({ data: { id, label: fileName }, classes: 'file' });
  }

  referenceCallstack(callstack: API.callstack): Cytoscape.NodeSingular | null {
    const name = callstackToString(callstack);
    const elt = callstack.shift();

    if (!elt)
      return null;

    const id = `callstack_${name}`;
    const node = this.cy.$id(id);
    if (node.nonempty()) {
      return node;
    }

    const parentNode = this.referenceCallstack(callstack);
    const parent = parentNode?.id();
    const label = elt.fun;
    return this.cy.add({ data: { id, label, parent }, classes: 'function' });
  }

  createTips(node: Cytoscape.NodeSingular): Tippy.Instance[] {
    const container = this.cy.container();
    if (!container)
      return [];

    const common = {
      interactive: true,
      multiple: true,
      animation: 'shift-away',
      duration: 500,
      trigger: 'manual',
      appendTo: document.body,
      lazy: false,
      // Cytoscape extensions are not typed yet
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      onCreate: (instance: any) => {
        const { popperInstance } = instance;
        if (popperInstance) {
          // eslint-disable-next-line @typescript-eslint/no-explicit-any
          popperInstance.reference = (node as any).popperRef();
        }
      },
    };

    const tips = [];

    if (node.data().values) {
      tips.push(tippy(container, {
        ...common,
        content: node.data().values,
        placement: 'top',
        //distance: 10,
        offset: [10, 10],
        arrow: true,
      }));
    }

    if (node.data().type) {
      tips.push(tippy(container, {
        ...common,
        content: node.data().type,
        placement: 'bottom',
        //distance: 20,
        offset: [20, 20],
        theme: 'light-border',
        arrow: false,
      }));
    }

    return tips;
  }

  addTips(node: Cytoscape.NodeSingular): void {
    let timeout: NodeJS.Timeout;
    let tips: Tippy.Instance[];

    // Create tips lazily
    node.on('mouseover', () => {
      if (tips === undefined)
        tips = this.createTips(node);
      clearTimeout(timeout);
      timeout = setTimeout(() => tips?.forEach((tip) => { tip.show(); }), 200);
    });

    node.on('mouseout', () => {
      clearTimeout(timeout);
      timeout = setTimeout(() => tips?.forEach((tip) => { tip.hide(); }), 1000);
    });
  }

  receiveGraph(data: API.graphData): Cytoscape.CollectionReturnValue {
    let newNodes = this.cy.collection();

    for (const node of data.nodes) {
      let stops = undefined;
      if (typeof node.range === 'number')
        stops = `0% ${node.range}% ${node.range}% 100%`;

      let ele = this.cy.$id(node.id.toString());
      if (ele.nonempty()) {
        ele.removeData();
        ele.data(node);
        ele.neighborhood('edge').remove();
      }
      else {
        let parent = null;
        if (node.locality.callstack)
          parent = this.referenceCallstack(node.locality.callstack)?.id();
        else
          parent = this.referenceFile(node.locality.file).id();

        ele = this.cy.add({
          group: 'nodes',
          data: { ...(node as { [k: string]: unknown }), stops, parent },
          classes: 'new',
        });
        this.addTips(ele);
        newNodes = ele.union(newNodes);
      }

      // Add a node for the user to ask for more dependencies
      const idmore = `${node.id}-more`;
      this.cy.$id(idmore).remove();
      if (node.backward_explored === 'partial') {
        const elemore = this.cy.add({
          group: 'nodes',
          data: { id: idmore, parent: ele.data('parent') },
          classes: 'new more',
        });
        newNodes = elemore.union(newNodes);
        this.cy.add({
          group: 'edges',
          data: { source: idmore, target: node.id },
          classes: 'new',
        });
      }
    }

    for (const dep of data.deps) {
      const src = this.cy.$id(dep.src.toString());
      const dst = this.cy.$id(dep.dst.toString());
      this.cy.add({
        data: {
          ...(dep as { [k: string]: unknown }),
          source: dep.src,
          target: dep.dst
        },
        group: 'edges',
        classes: src?.hasClass('new') || dst?.hasClass('new') ? 'new' : '',
      });
    }

    return newNodes;
  }

  receiveData(data: API.diffData): Cytoscape.NodeSingular | undefined {
    this.cy.startBatch();

    for (const id of data.sub)
      this.remove(this.cy.$id(id.toString()));

    const newNodes = this.receiveGraph(data.add);

    this.cy.endBatch();

    this.recomputeLayout(newNodes);

    const root = data.root;
    return root ? this.cy.$id(root.toString()) : undefined;
  }

  get layout(): string {
    return this._layout;
  }

  set layout(layout: string) {
    let extendedOptions = {};
    if (layout in layouts)
      extendedOptions = (layouts as { [key: string]: object })[layout];
    this._layout = layout;
    this.layoutOptions = {
      name: layout,
      fit: true,
      animate: true,
      randomize: false, /* Keep previous positions if layout supports it */
      ...extendedOptions,
    };

    this.recomputeLayout();
  }

  recomputeLayout(newNodes?: Cytoscape.Collection): void {
    if (this.layoutOptions && this.cy.container() &&
      (newNodes === undefined || !newNodes.empty())) {
      this.cy.layout({
        animationEasing: 'ease-in-out-quad',
        /* Do not move new nodes */
        animateFilter: (node: Cytoscape.Singular) => newNodes === undefined ||
          !newNodes.contains(node),
        stop: () => {
          this.cy.$('.new').addClass('old').removeClass('new');
        },
        ...this.layoutOptions,
      } as unknown as Cytoscape.LayoutOptions).run();
    }
  }

  async exec<In>(
    request: Server.ExecRequest<In, API.diffData | null>,
    param: In): Promise<Cytoscape.NodeSingular | undefined> {
    try {
      if (Server.isRunning()) {
        await this.setMode();
        const data = await Server.send(request, param);
        if (data)
          return this.receiveData(data);
      }
    }
    catch (err) {
      Debug.error(err);
    }

    return undefined;
  }

  async refresh(): Promise<void> {
    try {
      if (Server.isRunning()) {
        const data = await Server.send(API.graph, {});
        this.cy.startBatch();
        const newNodes = this.receiveGraph(data);
        this.cy.endBatch();
        this.recomputeLayout(newNodes);
      }
    }
    catch (err) {
      Debug.error(err);
    }
  }

  static async setWindow(window: API.explorationWindow): Promise<void> {
    if (Server.isRunning())
      await Server.send(API.window, window);
  }

  async setMode(): Promise<void> {
    switch (this.mode) {
      case 'explore':
        await Dive.setWindow({
          perception: { backward: 3, forward: 1 },
          horizon: { backward: 3, forward: 1 },
        });
        break;
      case 'overview':
        await Dive.setWindow({
          perception: { backward: 4, forward: 1 },
          horizon: { backward: undefined, forward: undefined },
        });
        break;
      default: /* This is useless and impossible if the program is correctly
                  typed, but the linter wants it */
    }
  }

  clear(): void {
    this.cy.elements().remove();
    this.exec(API.clear, null);
  }

  async add(marker: string): Promise<void> {
    const node = await this.exec(API.add, marker);
    if (node)
      this.updateNodeSelection(node);
  }

  async explore(node: Cytoscape.NodeSingular): Promise<void> {
    const id = parseInt(node.id(), 10);
    if (id)
      await this.exec(API.explore, id);
  }

  show(node: Cytoscape.NodeSingular): void {
    const id = parseInt(node.id(), 10);
    if (id)
      this.exec(API.show, id);
  }

  hide(node: Cytoscape.NodeSingular): void {
    const id = parseInt(node.id(), 10);
    if (id)
      this.exec(API.hide, id);
  }

  async clickNode(node: Cytoscape.NodeSingular): Promise<void> {
    this.updateNodeSelection(node);
    await this.explore(node);

    const writes = node.data()?.writes;
    if (writes && writes.length)
      this.onSelect?.(writes);

    /* Cytoscape automatically selects the node clicked, and unselects all other
       nodes and edges. As we want some incoming edges to remain selected, we
       make the node unselectable, preventing cytoscape to select it. */
    node.unselectify();
  }

  doubleClickNode(node: Cytoscape.NodeSingular): void {
    this.cy.animate({ fit: { eles: node, padding: 10 } });
  }

  selectLocation(
    location: States.Location | undefined,
    doExplore: boolean): void {
    if (!location) {
      // Reset whole graph if no location is selected.
      this.clear();
    } else if (location !== this.selectedLocation) {
      this.selectedLocation = location;
      const selectNode = this.cy.$('node:selected');
      const writes = selectNode?.data()?.writes;
      if (doExplore && location.marker && !_.some(writes, location)) {
        this.add(location.marker);
      }
      else {
        this.updateNodeSelection(selectNode);
      }
    }
  }

  updateNodeSelection(node: Cytoscape.NodeSingular): void {
    const hasOrigin = (ele: Cytoscape.NodeSingular): boolean => (
      _.some(ele.data().origins, this.selectedLocation)
    );
    this.cy.$(':selected').forEach(unselect);
    this.cy.$('.multiple-selection').removeClass('multiple-selection');
    this.cy.$('.selection').removeClass('selection');
    select(node);
    const edges = node.incomers('edge');
    const relevantEdges = edges.filter(hasOrigin);
    edges.addClass('multiple-selection');
    relevantEdges.addClass('selection');
  }
}

function GraphView(): JSX.Element {

  // Hooks
  const [dive, setDive] = useState(() => new Dive());
  const [selection, updateSelection] = States.useSelection();
  const [lock, flipLock] =
    Dome.useFlipSettings('dive.lock');
  const [selectionMode, setSelectionMode] =
    Dome.useStringSettings('dive.selectionMode', 'follow');

  function setCy(cy: Cytoscape.Core): void {
    if (cy !== dive.cy)
      setDive(new Dive(cy));
  }

  useEffect(() => {
    setDive(new Dive(dive.cy));
  }, [Dive]); // eslint-disable-line react-hooks/exhaustive-deps

  // Follow mode
  useEffect(() => {
    dive.mode = selectionMode === 'follow' ? 'explore' : 'overview';
  }, [dive, selectionMode]);

  useEffect(() => {
    /* When clicking on a node, select its writes locations as a multiple
       selection. If these locations were already selected, select the next
       location in the multiple selection. */
    dive.onSelect = (locations) => {
      if (_.isEqual(locations, selection?.multiple?.allSelections))
        updateSelection('MULTIPLE_CYCLE');
      else
        updateSelection({ locations, index: 0 });
    };

    // Updates the graph according to the selected marker.
    dive.selectLocation(selection?.current, !lock);
  }, [dive, lock, selection, updateSelection]);

  // Layout selection
  const selectLayout = (layout?: string): void => {
    if (layout) {
      dive.layout = layout;
    }
  };
  const layoutsNames = ['cose-bilkent', 'dagre', 'cola', 'klay'];
  const layoutItem = (id: string): Dome.PopupMenuItem => (
    { id, label: id, checked: (id === dive.layout) }
  );
  const layoutMenu = (): void => {
    Dome.popupMenu(layoutsNames.map(layoutItem), selectLayout);
  };

  // Selection mode
  const selectMode = (id?: string) => void (id && setSelectionMode(id));
  const modes = [
    { id: 'follow', label: 'Follow selection' },
    { id: 'add', label: 'Add selection to the graph' },
  ];
  const checkMode =
    (item: { id: string; label: string }): Dome.PopupMenuItem => (
      { checked: item.id === selectionMode, ...item }
    );
  const modeMenu = (): void => {
    Dome.popupMenu(modes.map(checkMode), selectMode);
  };

  // Component
  return (
    <>
      <Ivette.TitleBar>
        <IconButton
          icon="LOCK"
          onClick={flipLock}
          kind={lock ? 'negative' : 'positive'}
          title={lock ?
            'Unlock the graph: update the graph with the selection' :
            'Lock the graph: do not update the graph with the selection'}
        />
        <IconButton
          icon="SETTINGS"
          onClick={modeMenu}
          title="Choose the selection mode"
        />
        <IconButton
          icon="DISPLAY"
          onClick={layoutMenu}
          title="Choose the graph layout"
        />
        <Space />
        <IconButton
          icon="TRASH"
          onClick={() => dive.clear()}
          title="Clear the graph"
        />
      </Ivette.TitleBar>
      <CytoscapeComponent
        stylesheet={style}
        cy={setCy}
        style={{ width: '100%', height: '100%' }}
      />
    </>
  );

}

// --------------------------------------------------------------------------
// --- Export Component
// --------------------------------------------------------------------------

Ivette.registerComponent({
  id: 'frama-c.plugins.dive',
  label: 'Dive Dataflow',
  group: 'frama-c.plugins',
  rank: 2,
  title:
    'Data dependency graph according to an Eva analysis.\nNodes color ' +
    'represents the precision of the values inferred by Eva.',
  children: <GraphView />,
});

Ivette.registerView({
  id: 'dive',
  label: 'Dive Dataflow',
  rank: 5,
  layout: [
    ['frama-c.astview', 'frama-c.plugins.dive'],
    ['frama-c.properties', 'frama-c.locations'],
  ],
});

// --------------------------------------------------------------------------
