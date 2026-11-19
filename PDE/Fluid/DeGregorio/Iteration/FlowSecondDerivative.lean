/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.AmplitudeRegularity

/-!
# C² spatial coordinates for the bounded H² transport class

The flow has a positive C¹ spatial Jacobian. Its spatial slices and
those of its Eulerian inverse are therefore C², on the same closed time
interval as the original construction. This gives the chart regularity
needed for weak second-order change of variables.

The second-order statements concern spatial slices. The input curve is
continuous in L² and bounded in weak H².
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis
open scoped ContDiff Topology

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- The Hilbert flow has C² spatial slices at every time in the
prescribed closed interval. -/
theorem contDiff_two_hkCurve_flow_slice
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B))
    {c X : ℝ → ℝ → ℝ} (hchar : HkForwardCharacteristics hT f c X)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ContDiff ℝ 2 (fun x ↦ X x t) := by
  have hJ := contDiff_one_hkCurve_jacobian_slice hT f hchar ht
  have hderiv (x : ℝ) := hasDerivAt_hkCurve_hilbert_flow_space hT f hchar.velocity_derivative
    hchar.flow_initial hchar.flow_derivative x t ht
  have heq : deriv (fun x ↦ X x t) =
      fun x ↦ Real.exp (∫ s in 0..t, c (X x s) s) := funext fun x ↦ (hderiv x).deriv
  change ContDiff ℝ ((1 : ℕ∞ω) + 1) (fun x ↦ X x t)
  apply contDiff_succ_iff_deriv.mpr
  exact ⟨fun x ↦ (hderiv x).differentiableAt, by simp, heq.symm ▸ hJ⟩

/-- The constructed Eulerian inverse has C² spatial slices, including
both time endpoints. Its reciprocal Jacobian is derived from the
positive flow Jacobian. -/
theorem contDiff_two_hkCurve_inverse_slice
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B))
    {c X Y : ℝ → ℝ → ℝ} (hchar : HkForwardCharacteristics hT f c X)
    (hY : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ Y p.1 p.2))
    (hXY : ∀ y t, t ∈ Icc (0 : ℝ) T → X (Y y t) t = y)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ContDiff ℝ 2 (fun y ↦ Y y t) := by
  let J : ℝ → ℝ := fun x ↦ Real.exp (∫ s in 0..t, c (X x s) s)
  have hJ : ContDiff ℝ 1 J :=
    contDiff_one_hkCurve_jacobian_slice hT f hchar ht
  have hJne (x : ℝ) : J x ≠ 0 := Real.exp_ne_zero _
  have hderiv (y : ℝ) :=
    hasDerivAt_hkCurve_inverse_space hT f hchar.velocity_derivative hchar.flow_initial
      hchar.flow_derivative hY hXY y t ht
  have heq : deriv (fun y ↦ Y y t) = fun y ↦ (J (Y y t))⁻¹ :=
    funext fun y ↦ (hderiv y).deriv
  have hYs : Continuous (fun y ↦ Y y t) :=
    hY.comp (continuous_id.prodMk (continuous_const (y := (⟨t, ht⟩ : Icc 0 T))))
  have hYone : ContDiff ℝ 1 (fun y ↦ Y y t) := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun y ↦ (hderiv y).differentiableAt, ?_⟩
    rw [heq]
    exact (hJ.continuous.comp hYs).inv₀ (fun y ↦ hJne (Y y t))
  change ContDiff ℝ ((1 : ℕ∞ω) + 1) (fun y ↦ Y y t)
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun y ↦ (hderiv y).differentiableAt, by simp, ?_⟩
  rw [heq]
  exact (hJ.comp hYone).inv (fun y ↦ hJne (Y y t))

end DeGregorio.Iteration
