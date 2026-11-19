/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Localized
import PDE.DistributionTheory.TestFunction.CompactCutoff

/-!
# Nested cutoffs for interior difference quotients

A compactly supported cutoff in an open set admits a larger cutoff equal
to one on a neighborhood of its support. One positive radius works for
every coordinate, both signs of the step, and the backward-test collar.
The construction involves no function or equation data.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open Set

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Choose the larger cutoff and all translation collars before choosing
any Sobolev field. The coordinate quantifier includes dimension zero. -/
theorem exists_interior_cutoff_collar
    (hΩ : IsOpen Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hη : tsupport η.toFun ⊆ Ω) :
    ∃ (χ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (S : Set (ℝ^n)) (ρ : ℝ),
      IsOpen S ∧ S ⊆ Ω ∧ tsupport χ.toFun ⊆ Ω ∧
      (∀ x ∈ S, χ.toFun x = 1) ∧ tsupport η.toFun ⊆ S ∧ 0 < ρ ∧
      Metric.thickening ρ (tsupport η.toFun) ⊆ Ω ∧
      ∀ (k : Fin n) (h : ℝ), |h| < ρ →
        MapsTo (fun x ↦ x + coordinateStep k h) (tsupport η.toFun) S ∧
        Metric.cthickening ρ
          (shiftedSupport (coordinateStep k (-h)) (tsupport η.toFun)) ⊆ Ω := by
  have hK : IsCompact (tsupport η.toFun) := η.hasCompactSupport
  obtain ⟨r, hr, hrΩ⟩ := hK.exists_cthickening_subset_open hΩ hη
  obtain ⟨χ, hχ, hone, _, _⟩ :=
    TestFunction.exists_eq_one_on_compact hΩ hK.cthickening hrΩ
  let S := Metric.thickening r (tsupport η.toFun)
  have hSK : S ⊆ Metric.cthickening r (tsupport η.toFun) :=
    Metric.thickening_subset_cthickening _ _
  refine ⟨χ, S, r / 2, Metric.isOpen_thickening, hSK.trans hrΩ,
    hχ, (fun x hx ↦ hone x (hSK hx)), Metric.self_subset_thickening hr _,
    half_pos hr, ?_, ?_⟩
  · exact ((Metric.thickening_mono (by linarith : r / 2 ≤ r) _).trans hSK).trans hrΩ
  · intro k h hh
    constructor
    · intro x hx
      apply Metric.mem_thickening_iff.mpr
      refine ⟨x, hx, ?_⟩
      rw [dist_eq_norm, add_sub_cancel_left, norm_coordinateStep]
      linarith
    · calc
        _ ⊆ Metric.cthickening (r / 2)
            (Metric.cthickening |h| (tsupport η.toFun)) := by
          apply Metric.cthickening_subset_of_subset
          simpa only [abs_neg] using
            shiftedSupport_coordinateStep_subset_cthickening k (-h) (tsupport η.toFun)
        _ ⊆ Metric.cthickening (r / 2 + |h|) (tsupport η.toFun) :=
          Metric.cthickening_cthickening_subset (half_pos hr).le (abs_nonneg h) _
        _ ⊆ Metric.cthickening r (tsupport η.toFun) :=
          Metric.cthickening_mono (by linarith) _
        _ ⊆ Ω := hrΩ

end SobolevSpace.GraphSpace.DifferenceQuotient
