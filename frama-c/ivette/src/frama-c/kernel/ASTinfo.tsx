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
// --- AST Information
// --------------------------------------------------------------------------

import React from 'react';
import * as Dome from 'dome';
import { classes } from 'dome/misc/utils';
import * as States from 'frama-c/states';
import * as DATA from 'frama-c/kernel/api/data';
import * as AST from 'frama-c/kernel/api/ast';
import { Text } from 'frama-c/richtext';
import { Icon } from 'dome/controls/icons';
import { Code } from 'dome/controls/labels';
import { IconButton } from 'dome/controls/buttons';
import * as Boxes from 'dome/layout/boxes';
import { TitleBar } from 'ivette';

// --------------------------------------------------------------------------
// --- Marker Kinds
// --------------------------------------------------------------------------

import Kind = AST.markerKind;
import Var = AST.markerVar

function getMarkerKind (props: AST.markerInfoData): [string, string] {
  switch (props.kind) {
    case Kind.declaration:
      switch (props.var) {
        case Var.function: return ["Declaration", "Function declaration"];
        case Var.variable: return ["Declaration", "Variable declaration"];
        case Var.none: return ["Declaration", "Declaration"];
      }
      break;
    case Kind.global: return ["Global", "Global declaration or definition"];
    case Kind.lvalue:
      switch (props.var) {
        case Var.function: return ["Function", "Function"];
        case Var.variable: return ["Variable", "C variable"];
        case Var.none: return ["Lvalue", "C lvalue"];
      }
      break;
    case Kind.expression: return ["Expression", "C expression"];
    case Kind.statement: return ["Statement", "C statement"];
    case Kind.property: return ["Property", "ACSL property"];
    case Kind.term: return ["Term", "ACSL term"];
  }
}

function markerKind (props: AST.markerInfoData): JSX.Element {
  const [label, title] = getMarkerKind(props);
  return <span className="astinfo-markerkind" title={title}>{label}</span>;
}

// --------------------------------------------------------------------------
// --- Information Details
// --------------------------------------------------------------------------

interface InfoItemProps {
  label: string;
  title: string;
  descr: DATA.text;
}

function InfoItem(props: InfoItemProps): JSX.Element {
  return (
    <div className="astinfo-infos">
      <div
        className="dome-text-label astinfo-kind"
        title={props.title}
      >
        {props.label}
      </div>
      <div className="dome-text-cell astinfo-data">
        <Text text={props.descr} />
      </div>
    </div>
  );
}

interface ASTinfos {
  id: string;
  label: string;
  title: string;
  descr: DATA.text;
}

interface InfoSectionProps {
  marker: AST.marker;
  markerInfo: AST.markerInfoData;
  filter: string;
  selected: boolean;
  hovered: boolean;
  pinned: boolean;
  onPin: () => void;
  onHover: (hover: boolean) => void;
  onSelect: () => void;
  onRemove: () => void;
}

function MarkInfos(props: InfoSectionProps): JSX.Element {
  const [unfold, setUnfold] = React.useState(true);
  const [more, setMore] = React.useState(false);
  const { marker, markerInfo } = props;
  const allInfos: ASTinfos[] =
    States.useRequest(AST.getInformation, marker) ?? [];
  const highlight = classes(
    props.selected && 'selected',
    props.hovered && 'hovered',
  );
  const descr = markerInfo.descr ?? markerInfo.name;
  const kind = markerKind(markerInfo);
  const fs = props.filter.split(':');
  const filtered = allInfos.filter((info) => !fs.some((m) => m === info.id));
  const infos = more ? allInfos : filtered;
  const hasMore = filtered.length < allInfos.length;
  const pinButton =
    (!props.pinned || props.selected) ?
    {
      icon: "PIN", selected: props.pinned, onClick: props.onPin,
      title: "Pin/unpin marker information"
    } : {
      icon: "CIRC.CLOSE", onClick: props.onRemove,
      title:"Remove marker information"
    };
  return (
    <div
      className={`astinfo-section ${highlight}`}
      onMouseEnter={() => props.onHover(true)}
      onMouseLeave={() => props.onHover(false)}
      onDoubleClick={props.onSelect}
    >
      <div
        key="MARKER"
        className={`astinfo-markerbar ${highlight}`}
        title={descr}
      >
        <Icon
          className="astinfo-folderbutton"
          style={{ visibility: infos.length ? 'visible' : 'hidden' }}
          size={9}
          offset={-2}
          id={unfold ? 'TRIANGLE.DOWN' : 'TRIANGLE.RIGHT'}
          onClick={() => setUnfold(!unfold)}
        />
        <Code className="astinfo-markercode">
          {kind}{descr}
        </Code>
        <IconButton
          style={{ display: hasMore ? undefined : 'none' }}
          className="astinfo-markerbutton"
          title="Show all available information"
          size={9}
          offset={0}
          icon="CIRC.PLUS"
          selected={more}
          onClick={() => setMore(!more)}
        />
        <IconButton
          className="astinfo-markerbutton"
          size={9}
          offset={0}
          {...pinButton}
        />
      </div>
      {unfold && infos.map((info) => <InfoItem key={info.id} {...info} />)}
    </div>
  );
}

// --------------------------------------------------------------------------
// --- Information Selection State
// --------------------------------------------------------------------------

type Mark = { fct: string; marker: AST.marker };

const reload = new Dome.Event('frama-c.astinfo');

class InfoMarkers {

  private selection: Mark[] = [];
  private mSelected: AST.marker | undefined;
  private mHovered: AST.marker | undefined;
  private pinned = new Set<string>();

  isPinned(marker: AST.marker): boolean {
    return this.pinned.has(marker);
  }

  setPinned(marker: AST.marker, pinned: boolean): void {
    const oldpin = this.isPinned(marker);
    if (oldpin !== pinned) {
      if (pinned)
        this.pinned.add(marker);
      else
        this.pinned.delete(marker);
      reload.emit();
    }
  }

  addMarker(s: Mark[], marker: AST.marker, fct: string): Mark[] {
    if (s.some((m) => m.marker === marker))
      return s;
    else
      return s.concat({ marker, fct });
  }

  setLocations(
    selected: States.Location | undefined,
    hovered: States.Location | undefined
  ): void {
    const sm = selected?.marker;
    const sf = selected?.fct;
    const hm = hovered?.marker;
    const hf = hovered?.fct;
    const s0 = this.mSelected;
    const h0 = this.mHovered;
    let s = this.selection.filter((mark): boolean => {
      const m = mark.marker;
      return this.isPinned(m) || (m !== s0 && m !== h0);
    });
    if (sm && sf) s = this.addMarker(s, sm, sf);
    if (hm && hf) s = this.addMarker(s, hm, hf);
    this.selection = s;
    this.mSelected = sm;
    this.mHovered = hm;
    reload.emit();
  }

  removeMarker(marker: AST.marker): void {
    if (marker === this.mSelected) this.mSelected = undefined;
    if (marker === this.mHovered) this.mHovered = undefined;
    this.selection = this.selection.filter((m) => m.marker !== marker);
    this.pinned.delete(marker);
    reload.emit();
  }

  getSelected(): Mark[] { return this.selection; }

}

// --------------------------------------------------------------------------
// --- Context Menu Filter
// --------------------------------------------------------------------------

function openFilter(
  infos: ASTinfos[],
  filter: string,
  onChange: (f: string) => void,
): void {
  const fs = filter.split(':');
  const menuItems = infos.map((info) => {
    const checked = !fs.some((m) => m === info.id);
    const onClick = (): void => {
      const newFs =
        checked
          ? fs.concat(info.id)
          : fs.filter((m) => m !== info.id);
      onChange(newFs.join(':'));
    };
    return {
      id: info.id,
      label: `${info.title} (${info.label})`,
      checked,
      onClick,
    };
  });
  Dome.popupMenu(menuItems);
  return;
}

// --------------------------------------------------------------------------
// --- Information Panel
// --------------------------------------------------------------------------

export default function ASTinfo(): JSX.Element {
  // Hooks
  Dome.useUpdate(reload);
  const markers = React.useMemo(() => new InfoMarkers(), []);
  const markerInfos = States.useSyncArray(AST.markerInfo, false);
  const [selection] = States.useSelection();
  const [hoveredLoc] = States.useHovered();
  const information = States.useRequest(AST.getInformation, null) ?? [];
  const [filter, setFilter] =
    Dome.useStringSettings('frama-c.sidebar.astinfo.filter', '');
  const selectedLoc = selection?.current;
  const selected = selectedLoc?.marker;
  const hovered = hoveredLoc?.marker;
  React.useEffect(() => {
    markers.setLocations(selectedLoc, hoveredLoc);
  }, [markers, selectedLoc, hoveredLoc]);
  const pinMarker = React.useCallback((location: States.Location) => {
    if (location?.marker)
      markers.setPinned(location?.marker, true);
  }, [markers]);
  React.useEffect(() => {
    States.MetaSelection.on(pinMarker);
    return () => States.MetaSelection.off(pinMarker);
  }, [pinMarker]);
  const scrollTarget = React.useRef<HTMLInputElement>(null);
  React.useEffect(() => {
    scrollTarget.current?.scrollIntoView({ block: 'nearest' });
  });
  // Rendering
  const renderMark = (mark: Mark): JSX.Element | null => {
    const { marker } = mark;
    const markerInfo = markerInfos.getData(marker);
    if (!markerInfo) return null;
    const pinned = markers.isPinned(marker);
    const isSelected = selected === marker;
    const isHovered = hovered === marker;
    const onPin = () => void markers.setPinned(marker, !pinned);
    const onRemove = () => void markers.removeMarker(marker);
    const onSelect = () => void States.setSelection(mark);
    const onHover =
      (h: boolean): void => States.setHovered(h ? mark : undefined);
    const ref = isHovered ? scrollTarget : undefined;
    const markInfo =
      <MarkInfos
        key={marker}
        marker={marker}
        markerInfo={markerInfo}
        pinned={pinned}
        selected={isSelected}
        filter={filter}
        hovered={isHovered}
        onPin={onPin}
        onRemove={onRemove}
        onHover={onHover}
        onSelect={onSelect}
      />;
    return <div ref={ref}>{markInfo}</div>;
  };
  return (
    <>
      <TitleBar>
        <IconButton
          icon="CLIPBOARD"
          onClick={() => openFilter(information, filter, setFilter)}
          title="Information Filters"
        />
      </TitleBar>
      <Boxes.Scroll>
        {markers.getSelected().map(renderMark)}
      </Boxes.Scroll>
    </>
  );
}

// --------------------------------------------------------------------------
