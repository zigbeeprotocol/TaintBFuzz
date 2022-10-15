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

/* eslint-disable @typescript-eslint/no-explicit-any, no-console */

// --------------------------------------------------------------------------
// --- JSON Utilities
// --------------------------------------------------------------------------

/**
   Safe JSON utilities.
   @packageDocumentation
   @module dome/data/json
*/

import { DEVEL } from 'dome/system';

export type json =
  undefined | null | boolean | number | string |
  json[] | { [key: string]: json };

export type jobject = { [key: string]: json };

/**
   Parse without _revivals_.
   Returned data is guaranteed to have only [[json]] type.
   If an error occurs and `noError` is set to `true`,
   the function returns `undefined` and logs the error in console
   (DEVEL mode only).
 */
export function parse(text: string, noError = false): json {
  if (noError) {
    try {
      return JSON.parse(text);
    } catch (err) {
      if (DEVEL) console.error('[Dome.json] Invalid format:', err);
      return undefined;
    }
  } else
    return JSON.parse(text);
}

/**
   Export JSON (or any data) as a compact string.
*/
export function stringify(js: any): string {
  return JSON.stringify(js, undefined, 0);
}

/**
   Export JSON (or any data) as a string with indentation.
 */
export function pretty(js: any): string {
  return JSON.stringify(js, undefined, 2);
}

// --------------------------------------------------------------------------
// --- SAFE Decoder
// --------------------------------------------------------------------------

/** Decoder for values of type `D`.
    You can abbreviate `Safe<D | undefined>` with `Loose<D>`. */
export interface Safe<D> {
  (js?: json): D;
}

/** Decoder for values of type `D`, if any.
    Same as `Safe<D | undefined>`. */
export interface Loose<D> {
  (js?: json): D | undefined;
}

/**
   Encoder for value of type `D`.
   In most cases, you only need [[identity]].
 */
export interface Encoder<D> {
  (v: D): json;
}

/** Can be used for most encoders. */
export function identity<A>(v: A): A { return v; }

// --------------------------------------------------------------------------
// --- Primitives
// --------------------------------------------------------------------------

/** 'null' or 'undefined'. */
export const jNull: Loose<null> = (js: json) =>
  js === null ? null : undefined;

/** Identity. */
export const jAny: Safe<json> = (js: json) => js;

/** JSON Object. */
export const jObj: Loose<jobject> = (js: json) => (
  typeof js === 'object' && !Array.isArray(js) && js !== null ? js : undefined
);

/** Primitive JSON number or `undefined`. */
export const jNumber: Loose<number> = (js: json) => (
  typeof js === 'number' && !Number.isNaN(js) ? js : undefined
);

/** Primitive JSON number, rounded to integer, or `undefined`. */
export const jInt: Loose<number> = (js: json) => (
  typeof js === 'number' && !Number.isNaN(js) ? Math.round(js) : undefined
);

/** Primitive JSON number or `0`. */
export const jZero: Safe<number> = (js: json) => (
  typeof js === 'number' && !Number.isNaN(js) ? js : 0
);

/** Primitive JSON boolean or `undefined`. */
export const jBoolean: Loose<boolean> = (js: json) => (
  typeof js === 'boolean' ? js : undefined
);

/** Primitive JSON boolean or `true`. */
export const jTrue: Safe<boolean> = (js: json) => (
  typeof js === 'boolean' ? js : true
);

/** Primitive JSON boolean or `false`. */
export const jFalse: Safe<boolean> = (js: json) => (
  typeof js === 'boolean' ? js : false
);

/** Primitive JSON string or `undefined`. */
export const jString: Loose<string> = (js: json) => (
  typeof js === 'string' ? js : undefined
);

/** JSON constant.
    Capture the tag or returns `undefined`.
    Can be used with [[jUnion]], although [[jEnum]]
    might be more efficient.
*/
export function jTag<A>(tg: A): Loose<A> {
  return (js: json) => (Object.is(js, tg) ? tg : undefined);
}

/**
   Lookup tags in a dictionary.
   Can be used directly for enum types, eg. `jEnum(myEnumType)`.
 */
export function jEnum<A>(d: { [tag: string]: A }): Loose<A> {
  return (v: json) => (typeof v === 'string' ? d[v] : undefined);
}

/**
   One of the enumerated _constants_ or `undefined`.
   The typechecker will prevent you from listing values that are not in
   type `A`. However, it will not protected you from missings constants in `A`.
*/
export function jTags<A>(...values: ((string | number) & A)[]): Loose<A> {
  const m = new Map<string | number, A>();
  values.forEach((v) => m.set(v, v));
  return (v: json) => (typeof v === 'string' ? m.get(v) : undefined);
}

/**
   Refine a loose decoder with some default value.
   The default value is returned when the provided JSON is `undefined` or
   when the loose decoder returns `undefined`.
 */
export function jDefault<A>(
  fn: Loose<A>,
  defaultValue: A,
): Safe<A> {
  return (js: json) => (
    js === undefined ? defaultValue : (fn(js) ?? defaultValue)
  );
}

/**
   Force returning `undefined` or a default value for
   `undefined` _or_ `null` JSON input.
   Typically useful to leverage an existing `Safe<A>` decoder.
 */
export function jOption<A>(fn: Safe<A>, defaultValue?: A): Loose<A> {
  return (js: json) => (
    js === undefined || js === null ? defaultValue : fn(js)
  );
}

/**
   Fail when the loose decoder returns `undefined`.
   See also [[jCatch]] and [[jTry]].
 */
export function jFail<A>(fn: Loose<A>, error: string | Error): Safe<A> {
  return (js: json) => {
    const d = fn(js);
    if (d !== undefined) return d;
    throw (typeof (error) === 'string' ? new Error(error) : error);
  };
}

/**
   Provide a fallback value in case of undefined value or error.
   See also [[jFail]] and [[jTry]].
 */
export function jCatch<A>(fn: Loose<A>, fallBack: A): Safe<A> {
  return (js: json) => {
    try {
      return fn(js) ?? fallBack;
    } catch (err) {
      if (DEVEL) console.warn('[Dome.json]', err);
      return fallBack;
    }
  };
}

/**
   Provides an (optional) default value in case of error or undefined value.
   See also [[jFail]] and [[jCatch]].
 */
export function jTry<A>(fn: Loose<A>, defaultValue?: A): Loose<A> {
  return (js: json) => {
    try {
      return fn(js) ?? defaultValue;
    } catch (err) {
      if (DEVEL) console.warn('[Dome.json]', err);
      return defaultValue;
    }
  };
}

/**
   Converts maps to dictionaries.
 */
export function jMap<A>(fn: Loose<A>): Safe<Map<string, A>> {
  return (js: json) => {
    const m = new Map<string, A>();
    if (js !== null && typeof js === 'object' && !Array.isArray(js)) {
      const keys = Object.keys(js);
      keys.forEach((k) => {
        const v = fn(js[k]);
        if (v !== undefined) m.set(k, v);
      });
    }
    return m;
  };
}

/**
   Converts dictionaries to maps.
 */
export function eMap<A>(fn: Encoder<A>): Encoder<Map<string, undefined | A>> {
  return (m) => {
    const js: json = {};
    m.forEach((v, k) => {
      if (v !== undefined) {
        const u = fn(v);
        if (u !== undefined) js[k] = u;
      }
    });
    return js;
  };
}

/**
   Apply the decoder on each item of a JSON array, or return `[]` otherwise.
   Can be also applied on a _loose_ decoder, but you will get
   an array with possibly `undefined` elements. Use [[jList]]
   to discard undefined elements, or use a true _safe_ decoder.
 */
export function jArray<A>(fn: Safe<A>): Safe<A[]> {
  return (js: json) => (Array.isArray(js) ? js.map(fn) : []);
}

/**
   Apply the loose decoder on each item of a JSON array, discarding
   all `undefined` elements. To keep the all possibly undefined array entries,
   use [[jArray]] instead.
 */
export function jList<A>(fn: Loose<A>): Safe<A[]> {
  return (js: json) => {
    const buffer: A[] = [];
    if (Array.isArray(js)) js.forEach((vj) => {
      const d = fn(vj);
      if (d !== undefined) buffer.push(d);
    });
    return buffer;
  };
}

/**
   Exports all non-undefined elements.
 */
export function eList<A>(fn: Encoder<A>): Encoder<(A | undefined)[]> {
  return (m) => {
    const js: json[] = [];
    m.forEach((v) => {
      if (v !== undefined) {
        const u = fn(v);
        if (u !== undefined) js.push(u);
      }
    });
    return js;
  };
}

/** Apply a pair of decoders to JSON pairs, or return `undefined`. */
export function jPair<A, B>(
  fa: Safe<A>,
  fb: Safe<B>,
): Loose<[A, B]> {
  return (js: json) => (Array.isArray(js) ? [
    fa(js[0]),
    fb(js[1]),
  ] : undefined);
}

/** Similar to [[jPair]]. */
export function jTriple<A, B, C>(
  fa: Safe<A>,
  fb: Safe<B>,
  fc: Safe<C>,
): Loose<[A, B, C]> {
  return (js: json) => (Array.isArray(js) ? [
    fa(js[0]),
    fb(js[1]),
    fc(js[2]),
  ] : undefined);
}

/** Similar to [[jPair]]. */
export function jTuple4<A, B, C, D>(
  fa: Safe<A>,
  fb: Safe<B>,
  fc: Safe<C>,
  fd: Safe<D>,
): Loose<[A, B, C, D]> {
  return (js: json) => (Array.isArray(js) ? [
    fa(js[0]),
    fb(js[1]),
    fc(js[2]),
    fd(js[3]),
  ] : undefined);
}

/** Similar to [[jPair]]. */
export function jTuple5<A, B, C, D, E>(
  fa: Safe<A>,
  fb: Safe<B>,
  fc: Safe<C>,
  fd: Safe<D>,
  fe: Safe<E>,
): Loose<[A, B, C, D, E]> {
  return (js: json) => (Array.isArray(js) ? [
    fa(js[0]),
    fb(js[1]),
    fc(js[2]),
    fd(js[3]),
    fe(js[4]),
  ] : undefined);
}

/**
   Decoders for each property of object type `A`.
   Optional fields in `A` can be assigned a loose decoder.
*/
export type Props<A> = {
  [P in keyof A]: Safe<A[P]>;
};

/**
   Decode an object given the decoders of its fields.
   Returns `undefined` for non-object JSON.
 */
export function jObject<A>(fp: Props<A>): Loose<A> {
  return (js: json) => {
    if (js !== null && typeof js === 'object' && !Array.isArray(js)) {
      const buffer = {} as A;
      const keys = Object.keys(fp);
      keys.forEach((k) => {
        const fn = fp[k as keyof A];
        if (fn !== undefined) {
          const fj = js[k];
          if (fj !== undefined) {
            const fv = fn(fj);
            if (fv !== undefined) buffer[k as keyof A] = fv;
          }
        }
      });
      return buffer;
    }
    return undefined;
  };
}

/**
   Returns the first decoder result that is not undefined.
 */
export function jUnion<A>(...cases: Loose<A>[]): Loose<A> {
  return (js: json) => {
    for (let i = 0; i < cases.length; i++) {
      const fv = cases[i](js);
      if (fv !== undefined) return fv;
    }
    return undefined;
  };
}

/**
   Encoders for each property of object type `A`.
*/
export type EProps<A> = {
  [P in keyof A]?: Encoder<A[P]>;
};

/**
   Encode an object given the provided encoders by fields.
   The exported JSON object has only original
   fields with some specified encoder.
 */
export function eObject<A>(fp: EProps<A>): Encoder<A> {
  return (m: A) => {
    const js: json = {};
    const keys = Object.keys(fp);
    keys.forEach((k) => {
      const fn = fp[k as keyof A];
      if (fn !== undefined) {
        const fv = m[k as keyof A];
        if (fv !== undefined) {
          const r = fn(fv);
          if (r !== undefined) js[k] = r;
        }
      }
    });
    return js;
  };
}

// Intentionnaly internal and only declared
// eslint-disable-next-line @typescript-eslint/no-unused-vars
declare const tag: unique symbol;

/** Phantom type. */
export type phantom<K, A> = A & { tag: K };

export function forge<K, A>(_tag: K, data: A): phantom<K, A> {
  return data as any;
}

/** String key with kind.
    Can be used as a `string` but shall be created with [forge]. */
export type key<K> = phantom<K, string>;

/** Number index with kind.
    Can be used as a `number` but shall be created with [forge]. */
export type index<K> = phantom<K, number>;

/** Decoder for `key<K>` strings. */
export function jKey<K>(kd: K): Loose<key<K>> {
  return (js: json) => (typeof js === 'string' ? forge(kd, js) : undefined);
}

/** Decoder for `index<K>` numbers. */
export function jIndex<K>(kd: K): Loose<index<K>> {
  return (js: json) => (typeof js === 'number' ? forge(kd, js) : undefined);
}

/** Dictionaries. */
export type dict<A> = { [key: string]: A };

/**
   Decode a JSON dictionary, discarding all inconsistent entries.
   If the JSON contains no valid entry, still returns `{}`.
*/
export function jDict<A>(fn: Loose<A>): Safe<dict<A>> {
  return (js: json) => {
    const buffer: dict<A> = {};
    if (js !== null && typeof js === 'object' && !Array.isArray(js)) {
      const keys = Object.keys(js);
      keys.forEach((key) => {
        const fd = js[key];
        if (fd !== undefined) {
          const fv = fn(fd);
          if (fv !== undefined) buffer[key] = fv;
        }
      });
    }
    return buffer;
  };
}

/**
   Encode a dictionary into JSON, discarding all inconsistent entries.
   If the dictionary contains no valid entry, still returns `{}`.
*/
export function eDict<A>(fn: Encoder<A>): Encoder<dict<A>> {
  return (d: dict<A>) => {
    const js: json = {};
    const keys = Object.keys(d);
    keys.forEach((k) => {
      const fv = d[k];
      if (fv !== undefined) {
        const fr = fn(fv);
        if (fr !== undefined) js[k] = fr;
      }
    });
    return js;
  };
}

// --------------------------------------------------------------------------
