/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.CompactParametricIntegral.Interval
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Cylinder
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Square integrals from classical cylinder closure data

The derivative is taken on the finite time interval. Continuous representatives
of the coordinate jets supply domination, while the resulting integral contains
the interior coordinate derivative.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open MeasureTheory PDE.Common Set SobolevSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ} {u : ℝ^(n + 1) → ℝ}

/-- Continuous closure values give a continuous spatial square integral. -/
theorem continuousOn_integral_sq_of_cylinder_closure
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hc : ContinuousOn u (closure (spaceTimeCylinder Ω (Ioo a b)))) :
    ContinuousOn (fun t ↦ ∫ x in Ω, u (timeSpaceCons t x) ^ 2) (Icc a b) := by
  have hv := ContDiffUpToBoundary.continuousOn_uncurry_closure hc
  rw [closure_Ioo hab.ne] at hv
  apply continuousOn_setIntegral_of_compact_interval hΩ.measurableSet
    hbounded.isCompact_closure
    (measure_ne_top_of_subset subset_closure hbounded.isCompact_closure.measure_lt_top.ne)
  exact (hv.comp continuous_swap.continuousOn (fun _ hp ↦ ⟨hp.2, hp.1⟩)).pow 2

/-- Differentiate the square integral using only joint C¹ closure data
and continuity of the prescribed values on the closed cylinder. -/
theorem hasDerivAt_integral_sq_of_cylinder_closure
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hu : ContDiffUpToBoundary 1 u (spaceTimeCylinder Ω (Ioo a b)))
    (hc : ContinuousOn u (closure (spaceTimeCylinder Ω (Ioo a b))))
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s ↦ ∫ x in Ω, u (timeSpaceCons s x) ^ 2)
      (2 * ∫ x in Ω, u (timeSpaceCons t x) * (∂[0] u) (timeSpaceCons t x)) t := by
  have hQ : IsOpen (spaceTimeCylinder Ω (Ioo a b)) := isOpen_spaceTimeCylinder hΩ isOpen_Ioo
  let hd := hu.partialDeriv_of_succ hQ 0
  let D := hd.continuousRepresentative
  have hD : Continuous D := hd.continuous_continuousRepresentative
  have hDeq : EqOn D (∂[0] u) (spaceTimeCylinder Ω (Ioo a b)) :=
    hd.continuousRepresentative_eqOn
  have hv := ContDiffUpToBoundary.continuousOn_uncurry_closure hc
  rw [closure_Ioo (ht.1.trans ht.2).ne] at hv
  have hv' : ContinuousOn (fun p : ℝ × ℝ^n ↦ u (timeSpaceCons p.1 p.2))
      (Icc a b ×ˢ closure Ω) :=
    hv.comp continuous_swap.continuousOn (fun _ hp ↦ ⟨hp.2, hp.1⟩)
  have hdc : Continuous (fun p : ℝ × ℝ^n ↦ D (timeSpaceCons p.1 p.2)) :=
    hD.comp (timeSpaceContinuousLinearEquiv n).symm.continuous
  have hint := hasDerivAt_setIntegral_of_compact_interval
    (μ := volume) (f := fun s x ↦ u (timeSpaceCons s x) ^ 2)
    (a := a) (b := b) hΩ.measurableSet
    hbounded.isCompact_closure
    (measure_ne_top_of_subset subset_closure hbounded.isCompact_closure.measure_lt_top.ne)
    (by simpa only [Function.uncurry_def, Pi.pow_apply] using! hv'.pow 2)
    (by simpa only [Function.uncurry_def, Pi.mul_apply] using!
      (continuousOn_const.mul hv').mul hdc.continuousOn) (D := fun s x ↦
      2 * u (timeSpaceCons s x) * D (timeSpaceCons s x)) ?_ ht
  · convert hint using 1
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    rw [hDeq (timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨ht, hx⟩)]
    ring
  · intro x hx s hs
    have hp : timeSpaceCons s x ∈ spaceTimeCylinder Ω (Ioo a b) :=
      timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨hs, hx⟩
    have h := hasDerivAt_timeSpaceCons u s x
      ((hu.contDiffOn.contDiffAt (hQ.mem_nhds hp)).differentiableAt (by simp))
    simpa only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, Pi.pow_apply, hDeq hp] using!
      h.pow 2

end PDE.Analysis
