/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.InitialValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Cauchy barriers for a nonconvex Hamiltonian

A Lipschitz initial datum gives the barriers `g(x) ± C t` whenever `|H(p)| ≤ C`
on the ball containing its possible test gradients. No convexity is used.
The gradient bound follows from the Lipschitz inequality along a ray through
the contact point; the time derivative is fixed by contact along the time line.
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi.Cauchy

open Set Filter
open scoped Topology Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- An upper touching test to a Lipschitz function has gradient bounded by the same
Lipschitz constant. Where the test is not differentiable its gradient is `0`. -/
theorem norm_gradient_le_of_lipschitz_upper_contact {g φ : E → ℝ} {K : NNReal} {x : E}
    (hg : LipschitzWith K g) (hcontact : IsLocalMax (fun y ↦ g y - φ y) x) :
    ‖∇ φ x‖ ≤ K := by
  by_cases hφ : DifferentiableAt ℝ φ x
  swap
  · simp [gradient, fderiv_zero_of_not_differentiableAt hφ]
  let p := ∇ φ x
  have hd : HasDerivAt (fun t : ℝ ↦ φ (x + t • (-p)))
      (fderiv ℝ φ x (-p)) 0 := by
    have hline := (((hasDerivAt_id (0 : ℝ)).smul_const (-p)).const_add x)
    have hφ' : HasFDerivAt φ (fderiv ℝ φ x) (x + (0 : ℝ) • (-p)) := by
      simpa using hφ.hasFDerivAt
    simpa only [Function.comp_def, zero_smul, add_zero, one_smul] using!
      hφ'.comp_hasDerivAt (0 : ℝ) hline
  have hnear : ∀ᶠ t : ℝ in 𝓝 0,
      g (x + t • (-p)) - φ (x + t • (-p)) ≤ g x - φ x := by
    have hc : Tendsto (fun t : ℝ ↦ x + t • (-p)) (𝓝 0) (𝓝 x) := by
      have hc : ContinuousAt (fun t : ℝ ↦ x + t • (-p)) 0 := by fun_prop
      change Tendsto _ _ (𝓝 (x + (0 : ℝ) • (-p))) at hc
      simpa using hc
    exact hc hcontact
  have hlower : -(K : ℝ) * ‖p‖ ≤ fderiv ℝ φ x (-p) := by
    apply ge_of_tendsto hd.tendsto_slope_zero_right
    filter_upwards [mem_nhdsWithin_of_mem_nhds hnear, self_mem_nhdsWithin] with t ht htpos
    have hdist := hg.norm_sub_le (x + t • (-p)) x
    simp only [Real.norm_eq_abs, add_sub_cancel_left, norm_smul, norm_neg,
      abs_of_pos htpos] at hdist
    have hdiff := (abs_le.mp hdist).1
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul, ← div_eq_inv_mul]
    apply (le_div_iff₀ htpos).2
    nlinarith only [hdiff, ht]
  have hinner : fderiv ℝ φ x (-p) = -‖p‖ ^ 2 := by
    rw [← inner_gradient_left]
    simp [p]
  rw [hinner] at hlower
  change ‖p‖ ≤ K
  nlinarith [norm_nonneg p, K.coe_nonneg]

/-- The corresponding test-gradient bound at a lower contact. -/
theorem norm_gradient_le_of_lipschitz_lower_contact {g φ : E → ℝ} {K : NNReal} {x : E}
    (hg : LipschitzWith K g) (hcontact : IsLocalMin (fun y ↦ g y - φ y) x) :
    ‖∇ φ x‖ ≤ K := by
  have hmax : IsLocalMax (fun y ↦ -g y - -φ y) x := by
    filter_upwards [hcontact] with y hy
    linarith only [hy]
  have h := norm_gradient_le_of_lipschitz_upper_contact hg.neg hmax
  simpa [gradient, fderiv_neg, map_neg] using h

/-- The lower Cauchy barrier is a viscosity subsolution. The hypothesis on
`H` is needed only on the ball of possible test gradients. -/
theorem isSpatialViscositySubsolution_lower_barrier {H g : E → ℝ} {K : NNReal} {C : ℝ}
    (hg : LipschitzWith K g) (hH : ∀ p, ‖p‖ ≤ K → |H p| ≤ C) :
    IsSpatialViscositySubsolution (fun p _ ↦ H p) positiveTimeDomain
      (fun z : E × ℝ ↦ g z.1 - C * z.2) := by
  refine ⟨isOpen_positiveTimeDomain, fun z hz φ hφ hcontact ↦ ?_⟩
  have hmax := hcontact.isLocalMax (isOpen_positiveTimeDomain.mem_nhds hz)
  have hspace : IsLocalMax (fun x ↦ g x - φ (x, z.2)) z.1 := by
    have h := hmax.comp_continuous (continuousAt_id.prodMk (continuousAt_const (y := z.2)))
    filter_upwards [h] with x hx
    dsimp at hx
    linarith only [hx]
  have hp := norm_gradient_le_of_lipschitz_upper_contact hg hspace
  have ht : IsLocalMax (fun t ↦ g z.1 - C * t - φ (z.1, t)) z.2 :=
    hmax.comp_continuous (continuousAt_const.prodMk continuousAt_id)
  have hd := hφ.differentiableAt_one.hasFDerivAt.comp_hasDerivAt z.2
    ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
  have heq := ht.hasDerivAt_eq_zero (((hasDerivAt_id z.2).const_mul C).const_sub (g z.1) |>.sub hd)
  have hbound := (abs_le.mp (hH _ hp)).2
  linarith only [heq, hbound]

/-- The upper Cauchy barrier is a viscosity supersolution. -/
theorem isSpatialViscositySupersolution_upper_barrier {H g : E → ℝ} {K : NNReal} {C : ℝ}
    (hg : LipschitzWith K g) (hH : ∀ p, ‖p‖ ≤ K → |H p| ≤ C) :
    IsSpatialViscositySupersolution (fun p _ ↦ H p) positiveTimeDomain
      (fun z : E × ℝ ↦ g z.1 + C * z.2) := by
  refine ⟨isOpen_positiveTimeDomain, fun z hz φ hφ hcontact ↦ ?_⟩
  have hmin := hcontact.isLocalMin (isOpen_positiveTimeDomain.mem_nhds hz)
  have hspace : IsLocalMin (fun x ↦ g x - φ (x, z.2)) z.1 := by
    have h := hmin.comp_continuous (continuousAt_id.prodMk (continuousAt_const (y := z.2)))
    filter_upwards [h] with x hx
    dsimp at hx
    linarith only [hx]
  have hp := norm_gradient_le_of_lipschitz_lower_contact hg hspace
  have ht : IsLocalMin (fun t ↦ g z.1 + C * t - φ (z.1, t)) z.2 :=
    hmin.comp_continuous (continuousAt_const.prodMk continuousAt_id)
  have hd := hφ.differentiableAt_one.hasFDerivAt.comp_hasDerivAt z.2
    ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
  have heq := ht.hasDerivAt_eq_zero ((((hasDerivAt_id z.2).const_mul C).const_add (g z.1)).sub hd)
  have hbound := (abs_le.mp (hH _ hp)).1
  linarith only [heq, hbound]

end HamiltonJacobi.Cauchy
