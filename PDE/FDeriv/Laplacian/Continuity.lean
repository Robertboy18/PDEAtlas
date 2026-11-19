/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators

/-!
# Continuity of the coordinate Laplacian

The iterated coordinate Laplacian `∑ᵢ ∂ᵢ∂ᵢ f` of a map into a real normed space is continuous
at every point of local `C²` regularity. The proof uses the continuous second Fréchet derivative and
identifies its coordinate contractions on a neighborhood of the point.
-/

@[expose] public noncomputable section

open PDE (laplacian)

open Filter
open scoped Topology

/-- Local `C²` regularity makes the native coordinate Laplacian continuous at the point. -/
theorem ContDiffAt.continuousAt_coordinate_laplacian {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {u : ℝ^n → E} {x : ℝ^n}
    (hu : ContDiffAt ℝ 2 u x) : ContinuousAt (laplacian u) x := by
  have hnear : laplacian u =ᶠ[𝓝 x] fun y ↦
      ∑ i : Fin n, fderiv ℝ (fderiv ℝ u) y
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
    filter_upwards [hu.eventually (by norm_num)] with y hy
    unfold laplacian
    exact Finset.sum_congr rfl fun i _ ↦
      PDE.secondPartialDeriv_eq_fderiv i i
        ((hy.fderiv_right (m := 1) (by norm_num)).differentiableAt_one)
  apply ContinuousAt.congr_of_eventuallyEq (f := fun y ↦
    ∑ i : Fin n, fderiv ℝ (fderiv ℝ u) y
      (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) _ hnear
  exact tendsto_finsetSum _ fun _ _ ↦
    (((hu.fderiv_right (m := 1) (by norm_num)).continuousAt_fderiv one_ne_zero).clm_apply
      continuousAt_const).clm_apply continuousAt_const

/-- A `C²` map into a real normed space has a continuous native coordinate Laplacian. -/
theorem ContDiff.continuous_coordinate_laplacian {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {u : ℝ^n → E}
    (hu : ContDiff ℝ 2 u) : Continuous (laplacian u) :=
  continuous_iff_continuousAt.mpr fun _ ↦ hu.contDiffAt.continuousAt_coordinate_laplacian
