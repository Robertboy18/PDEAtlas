/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import CAS.Analysis.Approximation.Splines.PiecewisePolynomial

/-!
# Strict mesh knots lie outside open panels

A point of the open panel `(mesh.panelLeft i, mesh.panelRight i)` of a strict knot mesh is none of
the knots of the mesh (`CAS.Splines.StrictKnotMesh.ne_knot_of_mem_open_panel`), because the knots
increase strictly.
-/

@[expose] public section

open Set

namespace CAS.Splines.StrictKnotMesh

/-- An open panel contains no knot of a strict mesh. -/
theorem ne_knot_of_mem_open_panel {n : ℕ} (mesh : StrictKnotMesh n) (i : Fin n)
    {x : ℝ} (hx : x ∈ Ioo (mesh.panelLeft i) (mesh.panelRight i)) (k : Fin (n + 1)) :
    x ≠ mesh.knot k := by
  intro h
  rw [h] at hx
  have hleft : i.castSucc < k := mesh.strictMono_knot.lt_iff_lt.mp hx.1
  have hright : k < i.succ := mesh.strictMono_knot.lt_iff_lt.mp hx.2
  change i.val < k.val at hleft
  change k.val < i.val + 1 at hright
  omega

end CAS.Splines.StrictKnotMesh
