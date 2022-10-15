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
import { Meter } from 'dome/controls/displays';

export interface Coverage {
  reachable: number;
  dead: number;
}

export interface CoverageProps {
  coverage: Coverage;
}


export function percent(coverage: Coverage): string {
  const q = coverage.reachable / (coverage.reachable + coverage.dead);
  return `${(q * 100).toFixed(1)}%`;
}

export default function CoverageMeter(props: CoverageProps): JSX.Element {
  const { reachable, dead } = props.coverage;
  const total = reachable + dead;

  return (
    <Meter
      min={0}
      max={total}
      low={0.50 * total}
      high={0.85 * total}
      optimum='HIGH'
      value={reachable}
    />
  );
}
