/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension.Cubic.Rescaling

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import PDE.Analysis.Calculus.LocalExtension.RescaledBump
import CAS.ExactTactic
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# A fixed compactly supported cubic profile

A Mathlib bump with inner radius `3 / 2` and outer radius `2` multiplies the
cubic polynomial. Compact support of its derivatives supplies one finite bound
for the three scalar jets, before any rescaling parameter is chosen.

The rescaled profile is exactly cubic on `|s| ≤ ε` and has topological support
in `|s| ≤ 2 * ε`. These facts reuse the production rescaled-bump owner after a
scalar algebraic identification; no new cutoff primitive is introduced.
-/

@[expose] public noncomputable section

open Function Metric Set
open scoped ContDiff Topology

namespace PDE.Analysis

/-- One smooth compact profile has uniformly bounded jets, vanishing lower jets
at zero, and cubic rescalings on every smaller signed interval. The profile and
its bound are chosen once, before all positive scales and all state inputs. -/
theorem exists_cubic_cutoff_profile :
    ∃ (φ : ℝ → ℝ) (C : ℝ), 1 ≤ C ∧
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      EqOn φ (fun s ↦ s ^ 3) (closedBall 0 (3 / 2 : ℝ)) ∧
      (∀ s, ‖φ s‖ ≤ C) ∧
      (∀ s, ‖deriv φ s‖ ≤ C) ∧
      (∀ s, ‖deriv (deriv φ) s‖ ≤ C) ∧
      φ 0 = 0 ∧ deriv φ 0 = 0 ∧ deriv (deriv φ) 0 = 0 ∧
      ∀ ε : ℝ, 0 < ε →
        (∀ s : ℝ, |s| ≤ ε → cubicRescale φ ε s = s ^ 3) ∧
        tsupport (cubicRescale φ ε) ⊆ closedBall 0 (2 * ε) ∧
        HasCompactSupport (cubicRescale φ ε) := by
  let χ : ContDiffBump (0 : ℝ) :=
    { rIn := 3 / 2
      rOut := 2
      rIn_pos := by cas
      rIn_lt_rOut := by cas }
  let φ : ℝ → ℝ := fun s ↦ χ s * s ^ 3
  have hφ : ContDiff ℝ ∞ φ := χ.contDiff.mul (contDiff_id.pow 3)
  have hcompact : HasCompactSupport φ := χ.hasCompactSupport.mul_right
  have hagree : EqOn φ (fun s ↦ s ^ 3) (closedBall 0 (3 / 2 : ℝ)) := by
    intro s hs
    have hχ : χ s = 1 := χ.one_of_mem_closedBall hs
    change χ s * s ^ 3 = s ^ 3
    rw [hχ, one_mul]
  have hd : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hdd : ContDiff ℝ ∞ (deriv (deriv φ)) := (contDiff_infty_iff_deriv.mp hd).2
  obtain ⟨C₀, hC₀⟩ := hcompact.exists_bound_of_continuous hφ.continuous
  obtain ⟨C₁, hC₁⟩ := hcompact.deriv.exists_bound_of_continuous hd.continuous
  obtain ⟨C₂, hC₂⟩ := hcompact.deriv.deriv.exists_bound_of_continuous hdd.continuous
  let C : ℝ := max 1 (max C₀ (max C₁ C₂))
  have h0C : C₀ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have h1C : C₁ ≤ C :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h2C : C₂ ≤ C :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hnear : φ =ᶠ[𝓝 (0 : ℝ)] (fun s ↦ s ^ 3) :=
    χ.eventuallyEq_one.mono fun s hs ↦ by
      change χ s = 1 at hs
      change χ s * s ^ 3 = s ^ 3
      rw [hs, one_mul]
  have hz0 : φ 0 = 0 := by simpa using hnear.eq_of_nhds
  have hz1 : deriv φ 0 = 0 := by
    rw [hnear.deriv_eq]
    cas
  have hcube_deriv : deriv (fun s : ℝ ↦ s ^ 3) = fun s ↦ (3 : ℝ) * s ^ 2 := by
    funext s
    cas
  have hz2 : deriv (deriv φ) 0 = 0 := by
    rw [hnear.deriv.deriv_eq, hcube_deriv]
    cas
  have hscale (ε : ℝ) (hε : 0 < ε) :
      cubicRescale φ ε = fun s : ℝ ↦ χ (ε⁻¹ • s) • s ^ 3 := by
    funext s
    change ε ^ 3 * (χ (s / ε) * (s / ε) ^ 3) = χ (ε⁻¹ * s) * s ^ 3
    rw [div_eq_inv_mul]
    cas using [hε.ne']
  refine ⟨φ, C, le_max_left _ _, hφ, hcompact, hagree,
    fun s ↦ (hC₀ s).trans h0C, fun s ↦ (hC₁ s).trans h1C,
    fun s ↦ (hC₂ s).trans h2C, hz0, hz1, hz2, ?_⟩
  intro ε hε
  have hsupport : tsupport (cubicRescale φ ε) ⊆ closedBall 0 (2 * ε) := by
    rw [hscale ε hε]
    simpa only [χ, mul_comm] using
      χ.tsupport_rescaled_smul_subset (fun s : ℝ ↦ s ^ 3) hε
  refine ⟨?_, hsupport, ?_⟩
  · intro s hs
    rw [hscale ε hε]
    apply χ.rescaled_smul_eqOn (fun s : ℝ ↦ s ^ 3) hε
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs]
    have hinner : ε ≤ ε * χ.rIn := by
      change ε ≤ ε * (3 / 2 : ℝ)
      cas using [hε]
    exact hs.trans hinner
  · exact (isCompact_closedBall (0 : ℝ) (2 * ε)).of_isClosed_subset
      (isClosed_tsupport (cubicRescale φ ε)) hsupport

end PDE.Analysis
