/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Orthogonal families compatible with a continuous linear map

If a family has dense linear span and is orthogonal before and after a continuous
linear map, its two coefficient functionals differ by the squared basis norms.
Consequently, projection onto the span of any subfamily has an orthogonal residual
after applying the map as well.
-/

@[expose] public section

open Set

namespace ContinuousLinearMap

variable {V H ι : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (J : V →L[ℝ] H) {w : ι → V}

/-- The coefficient functionals of a densely spanning family orthogonal in both
inner products agree after multiplication by the corresponding squared norms. -/
theorem inner_map_mul_inner_self_of_orthogonal
    (hw : Pairwise (fun i j ↦ inner ℝ (w i) (w j) = 0))
    (hJw : Pairwise (fun i j ↦ inner ℝ (J (w i)) (J (w j)) = 0))
    (hdense : Dense (Submodule.span ℝ (range w) : Set V)) (i : ι) (v : V) :
    inner ℝ (J (w i)) (J v) * inner ℝ (w i) (w i) =
      inner ℝ (w i) v * inner ℝ (J (w i)) (J (w i)) := by
  have h :
      inner ℝ (w i) (w i) • ((innerSL ℝ (J (w i))).comp J) =
        inner ℝ (J (w i)) (J (w i)) • innerSL ℝ (w i) := by
    apply ContinuousLinearMap.ext_on hdense
    rintro _ ⟨j, rfl⟩
    by_cases hij : i = j
    · subst j
      simp [mul_comm]
    · simp [hw hij, hJw hij]
  simpa [mul_comm] using DFunLike.congr_fun h v

/-- Projection onto a subfamily has an orthogonal image residual when the whole
family is densely spanning and orthogonal for both inner products. -/
theorem inner_map_sub_starProjection_eq_zero
    (hw : Pairwise (fun i j ↦ inner ℝ (w i) (w j) = 0))
    (hJw : Pairwise (fun i j ↦ inner ℝ (J (w i)) (J (w j)) = 0))
    (hdense : Dense (Submodule.span ℝ (range w) : Set V)) (s : Set ι)
    [(Submodule.span ℝ (w '' s)).HasOrthogonalProjection]
    (v z : V) (hz : z ∈ Submodule.span ℝ (w '' s)) :
    inner ℝ (J (v - (Submodule.span ℝ (w '' s)).starProjection v)) (J z) = 0 := by
  let S := Submodule.span ℝ (w '' s)
  let L := (innerSL ℝ (J (v - S.starProjection v))).comp J
  have hzero : EqOn L 0 (w '' s) := by
    rintro _ ⟨i, hi, rfl⟩
    have hV := S.starProjection_inner_eq_zero v (w i)
      (Submodule.subset_span ⟨i, hi, rfl⟩)
    by_cases hwi : w i = 0
    · simp [L, hwi]
    · have h := J.inner_map_mul_inner_self_of_orthogonal hw hJw hdense i
        (v - S.starProjection v)
      rw [real_inner_comm (v - S.starProjection v) (w i), hV, zero_mul] at h
      have hJ := (mul_eq_zero.mp h).resolve_right (inner_self_ne_zero.mpr hwi)
      exact inner_eq_zero_symm.mp hJ
  exact LinearMap.eqOn_span' (f := L.toLinearMap) (g := 0) hzero hz

end ContinuousLinearMap
