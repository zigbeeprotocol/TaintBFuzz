#!/usr/bin/env python3
#-*- coding: utf-8 -*-

# Perform some sanity checks related to the compliance JSON files

import json
import sys
from pathlib import Path

if len(sys.argv) < 2:
    sys.exit(f"usage: {sys.argv[0]} dir (where dir is FRAMAC_SHARE/compliance)")

compliance_dir = sys.argv[1]

posix_ids_path = Path(compliance_dir) / "posix_identifiers.json"
posix_headers = set()
posix_dict = {}
with open(posix_ids_path) as data:
    js = json.load(data)
    posix_dict = js["data"]
    id_types = set(e["type"] for e in js["id_types"])
    posix_headers = set(js["headers"].keys())
    extension_names = set(js["extension_names"].keys())
    unique_ids = set()
    for (i, v) in posix_dict.items():
        if i in unique_ids:
            sys.exit("duplicate id {i}")
        unique_ids.add(i)
        id_type = v["id_type"]
        if id_type not in id_types:
            sys.exit(f"error: unknown id_type '{id_type}' for id {i}")
        header = v["header"]
        if header not in posix_headers:
            sys.exit(f"error: unknown header {header} for id {i}")
        exts = set(v["extensions"])
        unknown_exts = exts - extension_names
        if unknown_exts:
            sys.exit(f"error: unknown extension(s) {unknown_exts} for id {i}")
print(f"{posix_ids_path.name} checked.")

c11_headers_path = Path(compliance_dir) / "c11_headers.json"
c11_headers = []
with open(c11_headers_path) as data:
    js = json.load(data)
    c11_headers = js["data"]

c11_funs_path = Path(compliance_dir) / "c11_functions.json"
c11_funs = []
with open(c11_funs_path) as data:
    js = json.load(data)
    c11_funs = js["data"]

for (i, v) in c11_funs.items():
    header = v["header"]
    if header not in c11_headers:
        sys.exit(f"error: unknown header {header} for id {i}")
    if i not in posix_dict:
        if "notes" in v:
            if "not-in-posix" not in v["notes"]:
                print(f"warning: C11 identifier unexpectedly not in POSIX: {i}")
    else:
        if "notes" in v and "not-in-posix" in v["notes"]:
            print(f"warning: C11 identifier unexpectedly found in POSIX: {i}")
        id_type = posix_dict[i]["id_type"]
        if id_type != "function":
            if "notes" in v and "macro" in v["notes"]:
                if id_type != "macro":
                    print(f"warning: C11 macro {i} is not a macro in POSIX, but a {id_type}")
            else:
                print(f"warning: C11 function {i} is not a function in POSIX, but a {id_type}")
        posix_header = posix_dict[i]["header"]
        if header != posix_header:
            sys.exit(f"error: C11 function {i} mapped to header {header}, but in POSIX it is mapped to header {posix_header}")
print(f"{c11_funs_path.name} checked.")
