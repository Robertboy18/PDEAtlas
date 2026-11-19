/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension.SmallDerivative
import CAS.ExactTactic

/-!
# A small-Lipschitz cutoff of a nonzero quadratic map

On `Fin 2 → ℝ` with its sup norm, the map `x ↦ (x 0) ^ 2` has a smooth compactly
supported cutoff that agrees with it on a neighborhood of zero, although the global
Lipschitz constant of the cutoff can be prescribed arbitrarily small.
-/

@[expose] public section

open Function Metric
open scoped ContDiff NNReal

namespace PDE.Examples.Calculus

/-- The squared coordinate on `Fin 2 → ℝ` has a smooth cutoff with any positive Lipschitz
constant, equal to it near zero and taking positive values there. -/
theorem exists_quadratic_small_lipschitz_cutoff {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    ∃ (ρ : ℝ) (g : (Fin 2 → ℝ) → ℝ), 0 < ρ ∧ ρ < r ∧
      ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ ball 0 r ∧
      (∀ x ∈ ball 0 ρ, g x = (x 0) ^ 2) ∧ LipschitzWith ⟨ε, hε.le⟩ g ∧
      g 0 = 0 ∧ fderiv ℝ g 0 = 0 ∧
      (∃ M K : ℝ≥0, LipschitzWith M (fderiv ℝ g) ∧
        LipschitzWith K (fderiv ℝ (fderiv ℝ g))) ∧
      ∃ x ∈ ball 0 ρ, 0 < g x := by
  let p : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hq : HasDerivAt (fun t : ℝ ↦ t ^ 2) 0 0 := by cas
  have hD : fderiv ℝ (fun x : Fin 2 → ℝ ↦ (x 0) ^ 2) 0 = 0 := by
    simpa only [p, ContinuousLinearMap.proj_apply, Function.comp_def, zero_smul] using
      (hq.comp_hasFDerivAt_of_eq (0 : Fin 2 → ℝ) p.hasFDerivAt (by simp)).fderiv
  have hN : ContDiff ℝ ∞ (fun x : Fin 2 → ℝ ↦ (x 0) ^ 2) :=
    p.contDiff.pow 2
  obtain ⟨ρ, g, hρ, hρr, hg, hgc, hgs, hnear, hLip, hg0, hDg, M, K, hM, hK⟩ :=
    hN.exists_compactSupport_small_lipschitz (by norm_num) hD hε hr
  have hx : (fun _ : Fin 2 ↦ ρ / 2) ∈ ball 0 ρ := by
    simpa only [mem_ball_zero_iff, pi_norm_const, Real.norm_eq_abs,
      abs_of_pos (half_pos hρ)] using half_lt_self hρ
  refine ⟨ρ, g, hρ, hρr, hg, hgc, hgs, hnear, hLip, hg0, hDg, ⟨M, K, hM, hK⟩,
    (fun _ ↦ ρ / 2), hx, ?_⟩
  rw [hnear _ hx]
  exact sq_pos_of_pos (half_pos hρ)

end PDE.Examples.Calculus
