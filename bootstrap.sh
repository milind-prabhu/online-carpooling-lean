#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lake exe cache get \
  Mathlib.Analysis.SpecialFunctions.Pow.Real \
  Mathlib.Data.Real.Archimedean \
  Mathlib.Data.Finset.Powerset \
  Mathlib.Data.Finset.Max \
  Mathlib.Algebra.Order.BigOperators.Ring.Finset \
  Mathlib.Tactic.Linarith \
  Mathlib.Tactic.Ring \
  Mathlib.Tactic.NormNum \
  Mathlib.Tactic.FieldSimp \
  Mathlib.Tactic.Positivity \
  Mathlib.Data.Tree.Basic \
  Mathlib.Data.Sym.Sym2 \
  Mathlib.Data.Nat.Log \
  Mathlib.Data.List.OfFn \
  Mathlib.Data.Fintype.BigOperators \
  Mathlib.Data.Fintype.EquivFin \
  Mathlib.Data.Fintype.Pigeonhole \
  Mathlib.Algebra.Group.Fin.Basic \
  Mathlib.Data.Nat.Find \
  Mathlib.Combinatorics.SimpleGraph.Sum \
  Mathlib.Algebra.BigOperators.Field \
  Mathlib.Algebra.Order.Field.GeomSum \
  Mathlib.Combinatorics.Enumerative.Catalan \
  Mathlib.Data.Nat.Choose.Bounds \
  Mathlib.Combinatorics.SimpleGraph.DegreeSum
