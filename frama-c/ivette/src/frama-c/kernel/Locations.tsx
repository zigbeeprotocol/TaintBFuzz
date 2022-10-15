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
// --- Table of (multiple) locations
// --------------------------------------------------------------------------

import React from 'react';
import * as States from 'frama-c/states';

import * as Json from 'dome/data/json';
import { CompactModel } from 'dome/table/arrays';
import { Table, Column, Renderer } from 'dome/table/views';
import { Label } from 'dome/controls/labels';
import { IconButton } from 'dome/controls/buttons';
import { Space } from 'dome/frame/toolbars';
import { TitleBar } from 'ivette';
import { markerInfo } from 'frama-c/kernel/api/ast';

// --------------------------------------------------------------------------
// --- Locations Panel
// --------------------------------------------------------------------------

type LocationId = States.Location & { id: number };

export default function LocationsTable(): JSX.Element {

  // Hooks
  const [selection, updateSelection] = States.useSelection();
  const model = React.useMemo(() => (
    new CompactModel<number, LocationId>(({ id }: LocationId) => id)
  ), []);
  const multipleSelections = selection?.multiple;
  const numberOfSelections = multipleSelections?.allSelections?.length;
  const markersInfo = States.useSyncArray(markerInfo);

  // Renderer for statement markers.
  const renderMarker: Renderer<string> =
    (loc: string) => {
      const markerId = (loc as Json.key<'#markerInfo'>);
      const info = markersInfo.getData(markerId);
      const sloc = info?.sloc;
      const position = `${sloc?.base}:${sloc?.line}`;
      return <Label label={position} title={info?.descr} />;
    };

  // Updates [[model]] with the current multiple selections.
  React.useEffect(() => {
    if (numberOfSelections > 0) {
      const data: LocationId[] =
        multipleSelections.allSelections.map((d, i) => ({ ...d, id: i }));
      model.replaceAllDataWith(data);
    } else
      model.clear();
  }, [numberOfSelections, multipleSelections, model]);

  // Callbacks
  const onTableSelection = React.useCallback(
    ({ id }) => updateSelection({ index: id }),
    [updateSelection],
  );

  const reload = (): void => {
    const location = multipleSelections.allSelections[multipleSelections.index];
    updateSelection({ location });
  };

  // Component
  return (
    <>
      <TitleBar>
        <IconButton
          icon="RELOAD"
          onClick={reload}
          enabled={numberOfSelections > 0}
          title="Reload the current location"
        />
        <IconButton
          icon="ANGLE.LEFT"
          onClick={() => updateSelection('MULTIPLE_PREV')}
          enabled={numberOfSelections > 1 && multipleSelections?.index > 0}
          title="Previous location"
        />
        <IconButton
          icon="ANGLE.RIGHT"
          onClick={() => updateSelection('MULTIPLE_NEXT')}
          enabled={
            numberOfSelections > 1 &&
            multipleSelections?.index < numberOfSelections - 1
          }
          title="Next location"
        />
        <Space />
        <Label
          className="component-info"
          title={
            `${numberOfSelections} selected ` +
            `location${numberOfSelections > 1 ? 's' : ''}`
          }
        >
          {multipleSelections?.allSelections.length === 0 ?
            '0 / 0' :
            `${multipleSelections?.index + 1} / ${numberOfSelections}`}
        </Label>
        <Space />
        <IconButton
          icon="TRASH"
          onClick={() => updateSelection('MULTIPLE_CLEAR')}
          enabled={numberOfSelections > 0}
          title={`Clear location${numberOfSelections > 1 ? 's' : ''}`}
        />
      </TitleBar>
      <Label
        label={multipleSelections?.name}
        title={multipleSelections?.title}
        style={{ textAlign: 'center' }}
      />
      <Table
        model={model}
        selection={multipleSelections?.index}
        onSelection={onTableSelection}
      >
        <Column
          id="id"
          label="#"
          align="center"
          width={25}
          getter={(r: { id: number }) => r.id + 1}
        />
        <Column id="fct" label="Function" width={120} />
        <Column
          id="marker"
          label="Statement"
          fill
          render={renderMarker}
        />
      </Table>
    </>
  );
}

// --------------------------------------------------------------------------
