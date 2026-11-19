/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.Operator
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Compact C1 cutoffs in the intrinsic fractional space

Compact support and C1 regularity supply both bounds required by the
fractional multiplier estimate. The hypotheses are properties of the cutoff,
not an assumed bounded action on a Sobolev space.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace SobolevSpace.Fractional.Localization

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)} {φ u : ℝ^n → ℝ}

/-- Compact C1 cutoffs have finite Lipschitz and uniform bounds. -/
theorem exists_cutoff_bounds_of_contDiff
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    ∃ L M : ℝ≥0, LipschitzWith L φ ∧ ∀ x, ‖φ x‖ ≤ M := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hφ (by norm_num)
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hφ.continuous
  exact ⟨L, ⟨max C 0, le_max_right _ _⟩, hL, fun x ↦ (hC x).trans (le_max_left _ _)⟩

/-- A compact C1 scalar cutoff preserves the intrinsic condition for normed real targets. -/
theorem memGagliardo_smul_of_contDiff_hasCompactSupport {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {u : ℝ^n → F} {p : ℝ≥0∞}
    (hs0 : 0 < s) (hs1 : s < 1) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hu : MemGagliardo n s Ω u (p := p)) (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    MemGagliardo n s Ω (fun x ↦ φ x • u x) (p := p) := by
  obtain ⟨L, M, hL, hM⟩ := exists_cutoff_bounds_of_contDiff hφ hc
  exact memGagliardo_smul_cutoff hs0 hs1 hL hM hu hp0 hp

/-- A compact C1 cutoff preserves the intrinsic scalar condition on any domain. -/
theorem memGagliardo_mul_of_contDiff_hasCompactSupport {p : ℝ≥0∞}
    (hs0 : 0 < s) (hs1 : s < 1) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hu : MemGagliardo n s Ω u (p := p))
    (hp0 : p ≠ 0 := by norm_num) (hp : p ≠ ∞ := by norm_num) :
    MemGagliardo n s Ω (fun x ↦ φ x * u x) (p := p) := by
  simpa only [smul_eq_mul] using
    memGagliardo_smul_of_contDiff_hasCompactSupport hs0 hs1 hφ hc hu hp0 hp

/-- The bounded action of a compact C1 cutoff has the ordinary physical formula. -/
theorem exists_mulCutoffCLM_of_contDiff_hasCompactSupport
    (hs0 : 0 < s) (hs1 : s < 1) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    ∃ T : GagliardoSpace n s Ω →L[ℝ] GagliardoSpace n s Ω,
      ∀ u, (GagliardoSpace.toLp n s Ω (T u) : ℝ^n → ℝ) =ᵐ[volume.restrict Ω]
        fun x ↦ φ x * GagliardoSpace.toLp n s Ω u x := by
  obtain ⟨L, M, hL, hM⟩ := exists_cutoff_bounds_of_contDiff hφ hc
  exact ⟨GagliardoSpace.mulCutoffCLM hs0 hs1 hL hM,
    GagliardoSpace.toLp_mulCutoffCLM_apply_ae hs0 hs1 hL hM⟩

end SobolevSpace.Fractional.Localization
