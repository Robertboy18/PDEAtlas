/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Commands.DependencyGraph

/-!
# Dependency atlas

Every curated statement card in the Blueprint, drawn as one dependency graph.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false in
#doc (Manual) "Dependency Atlas" =>
%%%
htmlSplit := .never
%%%

The graph collects the definitions and theorems presented in the book.
An arrow points from a prerequisite to a statement that uses it. Dashed groups
organize statements by subject; they are not additional theorems.
The graph records the dependencies attached to the statement and proof cards,
rather than every auxiliary lemma in the Lean source.

For weak derivatives, the
{bpref "sobolev.weak_derivative_unique"}[uniqueness theorem] says that two
functions satisfying the same
{bpref "sobolev.weak_derivative"}[test-function identity] agree almost everywhere.
That explains why Sobolev derivatives can be stored as $`L^p` classes rather
than as pointwise functions.

{leanpde_dependency_graph}
