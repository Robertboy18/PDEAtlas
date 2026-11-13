/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.SpaceTime
import PDE.Analysis.Calculus.HalfSpaceGluing

/-!
# First derivatives on the closed forward half-space

The derivative within the half-space has a continuous extension to all time
parameters by clipping negative times to zero. Zero displacement on an open
initial set and zero actual right velocity force this entire differential to
vanish there.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Filter Set PDE.Common
open scoped Topology

variable {n : ℕ}

/-- The closed forward half-space has unique derivatives, including at initial time. -/
theorem uniqueDiffOn_forward_halfSpace :
    UniqueDiffOn ℝ {p : ℝ^(n + 1) | 0 ≤ p 0} :=
  uniqueDiffOn_coordinateHalfSpace 0

/-- Forward `C¹` regularity gives an actual right derivative at the initial time. -/
theorem differentiableWithinAt_initial_time {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiffOn ℝ 1 u {p | 0 ≤ p 0}) (x : ℝ^n) :
    DifferentiableWithinAt ℝ (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 := by
  have hd := (hu.differentiableOn_one (timeSpaceCons 0 x) (by simp)).hasFDerivWithinAt
  exact (hd.comp_hasDerivWithinAt 0
    (hasDerivAt_timeSpaceCons_time n 0 x).hasDerivWithinAt
    (show MapsTo (fun t ↦ timeSpaceCons t x) (Ici 0) {p | 0 ≤ p 0} from
      fun t ht ↦ by simpa using ht)).differentiableWithinAt

/-- The actual differential within forward time, extended continuously by clipping time. -/
def forwardDifferential (u : ℝ^(n + 1) → ℝ) (t : ℝ) (x : ℝ^n) :
    ℝ^(n + 1) →L[ℝ] ℝ :=
  fderivWithin ℝ u {p | 0 ≤ p 0} (timeSpaceCons (max 0 t) x)

/-- Forward `C¹` regularity gives joint continuity of the clipped differential. -/
theorem continuous_forwardDifferential {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiffOn ℝ 1 u {p | 0 ≤ p 0}) :
    Continuous (Function.uncurry (forwardDifferential u)) := by
  apply (hu.continuousOn_fderivWithin uniqueDiffOn_forward_halfSpace le_rfl).comp_continuous
    ((contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
      ((continuous_const.max continuous_fst).prodMk continuous_snd))
  intro p
  exact le_max_left 0 p.1

/-- At positive time the clipped differential is the ordinary Fréchet derivative. -/
theorem forwardDifferential_eq_fderiv (u : ℝ^(n + 1) → ℝ) {t : ℝ} (ht : 0 < t)
    (x : ℝ^n) :
    forwardDifferential u t x = fderiv ℝ u (timeSpaceCons t x) := by
  unfold forwardDifferential
  rw [max_eq_right ht.le, fderivWithin_of_mem_nhds]
  apply Filter.mem_of_superset
    ((isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).mem_nhds
      (show (0 : ℝ) < (timeSpaceCons t x) 0 by simpa using ht))
  exact fun _ h ↦ h.le

/-- Zero initial displacement and actual right velocity determine the full initial differential. -/
theorem forwardDifferential_initial_eq_zero {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiffOn ℝ 1 u {p | 0 ≤ p 0}) {S : Set (ℝ^n)} (hS : IsOpen S)
    (hpos : ∀ x ∈ S, u (timeSpaceCons 0 x) = 0)
    (hvel : ∀ x ∈ S, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = 0)
    {x : ℝ^n} (hx : x ∈ S) :
    forwardDifferential u 0 x = 0 := by
  let D := fderivWithin ℝ u {p | 0 ≤ p 0} (timeSpaceCons 0 x)
  have hD : HasFDerivWithinAt u D {p | 0 ≤ p 0} (timeSpaceCons 0 x) :=
    (hu.differentiableOn_one _ (by simp)).hasFDerivWithinAt
  have htime : D (EuclideanSpace.single 0 1) = 0 := by
    have hd := hD.comp_hasDerivWithinAt 0
      (hasDerivAt_timeSpaceCons_time n 0 x).hasDerivWithinAt
      (show MapsTo (fun t ↦ timeSpaceCons t x) (Ici 0) {p | 0 ≤ p 0} from
        fun t ht ↦ by simpa using ht)
    rw [← hvel x hx]
    exact (hd.derivWithin (uniqueDiffOn_Ici 0 0 (by simp))).symm
  have hspace : D.comp (embedWithTimeZeroCLM n) = 0 := by
    have hd := hD.comp_hasFDerivAt x (hasFDerivAt_timeSpaceCons_spatial n 0 x)
      (Filter.Eventually.of_forall fun y ↦
        (show (0 : ℝ) ≤ (timeSpaceCons 0 y) 0 by simp))
    have heq : (fun _ : ℝ^n ↦ (0 : ℝ)) =ᶠ[𝓝 x] u ∘ timeSpaceCons 0 := by
      filter_upwards [hS.mem_nhds hx] with y hy using (hpos y hy).symm
    exact (hd.congr_of_eventuallyEq heq).unique (hasFDerivAt_const 0 x)
  change fderivWithin ℝ u {p | 0 ≤ p 0} (timeSpaceCons (max 0 0) x) = 0
  rw [max_self]
  change D = 0
  ext v
  have hv : v = v 0 • EuclideanSpace.single 0 1 +
      embedWithTimeZeroCLM n (spatialPart v) := by
    ext i
    cases i using Fin.cases <;> simp
  have hs := congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L (spatialPart v)) hspace
  rw [hv, map_add, map_smul, htime, smul_zero, zero_add]
  simpa using hs

end PDE.Analysis
