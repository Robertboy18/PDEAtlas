/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Prod.SliceDerivative

/-!
# Differentiating a level-event map

Suppose a differentiable event time keeps a parameterized function at a fixed
level. Differentiating this identity expresses the event-time derivative in terms
of the function's parameter and time derivatives. A nonzero time derivative
allows us to solve the resulting scalar equation.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace PDE.Analysis

/-- Differentiating an already supplied constant-level graph. Only a neighborhood
identity and differentiability at the reference points are needed. The numerator
holds time fixed at `τ p₀`; it is not the derivative of the moving graph. -/
theorem fderiv_level_event_apply
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {f : P × ℝ → ℝ} {τ : P → ℝ} {p₀ : P} {c v : ℝ}
    (hf : DifferentiableAt ℝ f (p₀, τ p₀))
    (hτ : DifferentiableAt ℝ τ p₀)
    (hlevel : ∀ᶠ p in 𝓝 p₀, f (p, τ p) = c)
    (ht : HasDerivAt (fun t ↦ f (p₀, t)) v (τ p₀))
    (hv : v ≠ 0) (ξ : P) :
    fderiv ℝ τ p₀ ξ = -(fderiv ℝ (fun p ↦ f (p, τ p₀)) p₀ ξ) / v := by
  have hgraph := hf.hasFDerivAt.comp p₀
    ((hasFDerivAt_id (𝕜 := ℝ) p₀).prodMk hτ.hasFDerivAt)
  have hconst : HasFDerivAt (fun p ↦ f (p, τ p)) 0 p₀ :=
    (hasFDerivAt_const (𝕜 := ℝ) c p₀).congr_of_eventuallyEq hlevel
  have hzero : fderiv ℝ f (p₀, τ p₀) (ξ, fderiv ℝ τ p₀ ξ) = 0 := by
    exact congrArg (fun D : P →L[ℝ] ℝ ↦ D ξ) (hgraph.unique hconst)
  have htime : fderiv ℝ f (p₀, τ p₀) (0, 1) = v :=
    (deriv_prod_timeSlice f p₀ (τ p₀) hf).symm.trans ht.deriv
  have hspace := fderiv_prod_firstSlice f p₀ ξ (τ p₀) hf
  have hsplit : (ξ, fderiv ℝ τ p₀ ξ) =
      (ξ, (0 : ℝ)) + (fderiv ℝ τ p₀ ξ) • ((0 : P), (1 : ℝ)) := by
    simp
  rw [hsplit, map_add, map_smul, htime, ← hspace, smul_eq_mul] at hzero
  apply (eq_div_iff hv).2
  linarith only [hzero]

end PDE.Analysis
