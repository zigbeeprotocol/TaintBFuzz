#!/bin/sh
ocamlopt.opt -shared -o ./Script.cmxs -w Ly -warn-error A -I /usr/local/lib/frama-c -I . script.ml
