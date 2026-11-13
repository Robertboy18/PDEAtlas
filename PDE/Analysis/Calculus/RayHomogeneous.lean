/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Euler's identity for functions homogeneous along a ray

If `g(c p) = c^m g(p)` for every `c ≥ 1` and `g` is differentiable at `p`, then
`∑ⱼ pⱼ ∂ⱼ g(p) = m g(p)`: the derivative of `c ↦ g(c p)` at `c = 1` within `[1, ∞)` is
`Dg(p) p` by the chain rule and `m g(p)` from the power.

## Main results

* `sum_mul_partialDeriv_eq_of_rayScale`: `∑ⱼ pⱼ ∂ⱼ g(p) = m g(p)` when `g(c p) = c^m g(p)` for
  `c ≥ 1`.
-/

@[expose] public section

namespace PDE.Analysis

open Set PDE.FDeriv

/-- **Euler's identity along a ray**: a function differentiable at `p` with
`g(c p) = c^m g(p)` for `c ≥ 1` satisfies `∑ⱼ pⱼ ∂ⱼ g(p) = m g(p)`. -/
theorem sum_mul_partialDeriv_eq_of_rayScale {n : ℕ} {g : ℝ^n → ℝ} {p : ℝ^n} {m : ℝ}
    (hg : DifferentiableAt ℝ g p) (hscale : ∀ c : ℝ, 1 ≤ c → g (c • p) = c ^ m * g p) :
    ∑ j : Fin n, p j * (∂[j] g) p = m * g p := by
  have hline : HasDerivAt (fun c : ℝ ↦ c • p) p 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const p
  have hg' : HasFDerivAt g (fderiv ℝ g p) ((1 : ℝ) • p) := by
    rw [one_smul]; exact hg.hasFDerivAt
  have h1 : HasDerivWithinAt (fun c : ℝ ↦ g (c • p)) ((fderiv ℝ g p) p) (Ici 1) 1 :=
    (hg'.comp_hasDerivAt (1 : ℝ) hline).hasDerivWithinAt
  have h2 : HasDerivWithinAt (fun c : ℝ ↦ c ^ m * g p) (m * g p) (Ici 1) 1 := by
    have := ((Real.hasDerivAt_rpow_const (p := m) (Or.inl one_ne_zero)).mul_const (g p))
    simpa using this.hasDerivWithinAt
  have h2' : HasDerivWithinAt (fun c : ℝ ↦ g (c • p)) (m * g p) (Ici 1) 1 :=
    h2.congr (fun c hc ↦ hscale c hc) (by simp)
  have huniq := (uniqueDiffWithinAt_Ici (1 : ℝ)).eq_deriv _ h1 h2'
  rw [← huniq, fderiv_apply_eq_sum_partialDeriv_mul]
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

end PDE.Analysis
