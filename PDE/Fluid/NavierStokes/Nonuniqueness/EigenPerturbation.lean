/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.WeakEquations
public import PDE.Fluid.NavierStokes.Stationary.SolenoidalDensity
public import PDE.Fluid.NavierStokes.Stationary.Trilinear
import PDE.Fluid.NavierStokes.Stationary.ConvectionHolder

/-!
# Perturbation of the weak eigenvalue equation by a correction of the profile

The density `weakEigenDensity U μ v φ` of the weak eigenvalue equation is affine in the
profile `U`. Replacing `U` by `U + D`, where `D` is the chosen representative of a correction
`d ∈ H¹(ℝ³)³`, adds the density

`Σᵢⱼ Dⱼ ∂ⱼvᵢ φᵢ - (div v) D·φ - D·(Dφ v)`

(`weakEigenDensity_add_representative`). For divergence-free `v` the middle term vanishes
almost everywhere, and the other two integrate to `b(d, v, φ) - b(v, φ, d)`, where
`b(u, v, w) = ∫ (u·∇)v·w` is the convection form and `φ` is identified with its class in
`H¹(ℝ³)³`. The bilinear form `eigenPerturbation d v w = b(d, v, w) - b(v, w, d)` is therefore
the change of the tested eigenvalue equation (`integral_weakEigenDensity_add_representative`).

Two bounds on the perturbation form follow. In the weighted norm
`‖h‖_s² = s² ‖h‖₂² + ‖∇h‖₂²`, Ladyzhenskaya's inequality, through the trilinear bound
`Stationary.norm_convectionTrilinear_le_weighted`, gives
`|eigenPerturbation d v w| ≤ t/2 ‖d‖_s ‖v‖_s ‖w‖_s` whenever `t² s ≥ 1`
(`abs_eigenPerturbation_le_weighted`). If the representative of `d` is bounded by `S` almost
everywhere, the two bounds of the convection form with one bounded factor
(`Stationary.abs_convectionTrilinear_le_of_norm_le_left` and
`Stationary.abs_convectionTrilinear_le_of_norm_le_right`) give
`|eigenPerturbation d v w| ≤ S (‖∇v‖₂ ‖w‖₂ + ‖v‖₂ ‖∇w‖₂)`
(`abs_eigenPerturbation_le_of_norm_le`).
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped RealInnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert ContDiff

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

local notation "H" => PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))

/-- The change of the tested eigenvalue equation under a correction `d` of the profile:
`eigenPerturbation d v w = b(d, v, w) - b(v, w, d)`, where `b(u, v, w) = ∫ (u·∇)v·w` is the
convection form on `H¹(ℝ³)³`. -/
def eigenPerturbation (d : H) : H →L[ℝ] H →L[ℝ] ℝ :=
  Stationary.convectionTrilinear d -
    (ContinuousLinearMap.compL ℝ H (H →L[ℝ] ℝ) ℝ (ContinuousLinearMap.apply ℝ ℝ d)).comp
      Stationary.convectionTrilinear

/-- The perturbation form is `b(d, v, w) - b(v, w, d)`. -/
theorem eigenPerturbation_apply (d v w : H) :
    eigenPerturbation d v w =
      Stationary.convectionTrilinear d v w - Stationary.convectionTrilinear v w d :=
  rfl

/-- The perturbation form is additive in the correction. -/
theorem eigenPerturbation_add (d d' v w : H) :
    eigenPerturbation (d + d') v w = eigenPerturbation d v w + eigenPerturbation d' v w := by
  simp only [eigenPerturbation_apply, map_add, add_apply]
  ring

/-- Replacing the profile `U` by `U + D`, with `D` the representative of `d`, adds the density
`Σᵢⱼ Dⱼ ∂ⱼvᵢ φᵢ - (div v) D·φ - D·(Dφ v)` to the eigenvalue density, pointwise. -/
theorem weakEigenDensity_add_representative (U : ℝ^3 → ℝ^3) (d : H) (μ : ℝ) (v : H)
    (φ : ℝ^3 → ℝ^3) (x : ℝ^3) :
    weakEigenDensity (U + Stationary.representative d) μ v φ x = weakEigenDensity U μ v φ x +
      (∑ i, ∑ j, Stationary.representative d x j * Stationary.gradientRepresentative v x i j *
        φ x i) -
      (∑ j, Stationary.gradientRepresentative v x j j) * ⟪Stationary.representative d x, φ x⟫ -
      ⟪Stationary.representative d x, fderiv ℝ φ x (Stationary.representative v x)⟫ := by
  have hsum : ∑ i, ∑ j, ((U + Stationary.representative d) x j - (1 / 2 : ℝ) * x j) *
      Stationary.gradientRepresentative v x i j * φ x i =
      (∑ i, ∑ j, (U x j - (1 / 2 : ℝ) * x j) * Stationary.gradientRepresentative v x i j *
        φ x i) +
      ∑ i, ∑ j, Stationary.representative d x j * Stationary.gradientRepresentative v x i j *
        φ x i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Pi.add_apply, PiLp.add_apply]
    ring
  rw [weakEigenDensity, weakEigenDensity, hsum, Pi.add_apply, inner_add_left, inner_add_left]
  ring

/-- For divergence-free `v` and a smooth compactly supported test field `φ`, the tested
eigenvalue equation at the profile `U + D`, with `D` the representative of `d`, differs from the
one at `U` by `eigenPerturbation d v φ`, with `φ` read as an element of `H¹(ℝ³)³`. -/
theorem integral_weakEigenDensity_add_representative (U : ℝ^3 → ℝ^3) (d : H) (μ : ℝ) {v : H}
    (hv : Stationary.divergenceCLM v = 0) {φ : ℝ^3 → ℝ^3} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hU : Integrable (weakEigenDensity U μ v φ)) :
    Integrable (weakEigenDensity (U + Stationary.representative d) μ v φ) ∧
      ∫ x, weakEigenDensity (U + Stationary.representative d) μ v φ x =
        (∫ x, weakEigenDensity U μ v φ x) +
          eigenPerturbation d v (Stationary.testFieldH1 φ hφ hc) := by
  set D := Stationary.representative d
  set ψ := Stationary.testFieldH1 φ hφ hc
  have hψ : ∀ᵐ x ∂volume, ∀ i, Stationary.representative ψ x i = φ x i :=
    ae_all_iff.mpr fun i ↦ Stationary.testFieldH1_base_ae hφ hc i
  have hdψ : ∀ᵐ x ∂volume, ∀ k i, Stationary.gradientRepresentative ψ x k i =
      PDE.partialDeriv i (fun y ↦ φ y k) x :=
    ae_all_iff.mpr fun k ↦ ae_all_iff.mpr fun i ↦ Stationary.testFieldH1_partial_ae hφ hc k i
  have htr : ∀ᵐ x ∂volume, ∑ j, Stationary.gradientRepresentative v x j j = 0 :=
    Stationary.ae_sum_gradientRepresentative_self_eq_zero hv
  -- the first-order term
  set f₁ : ℝ^3 → ℝ := fun x ↦
    ∑ i, ∑ j, D x j * Stationary.gradientRepresentative v x i j * φ x i with hf₁
  have he₁ : (fun x ↦ ∑ k : Fin 3, ∑ i : Fin 3, D x i * Stationary.gradientRepresentative v x k i *
      Stationary.representative ψ x k) =ᵐ[volume] f₁ := by
    filter_upwards [hψ] with x hx
    simp only [hf₁, hx]
  have hi₁ : Integrable f₁ := (Stationary.integrable_convectionDensity d v ψ).congr he₁
  have hI₁ : ∫ x, f₁ x = Stationary.convectionTrilinear d v ψ := by
    rw [Stationary.convectionTrilinear_eq_integral]
    exact (integral_congr_ae he₁).symm
  -- the divergence term
  set f₂ : ℝ^3 → ℝ := fun x ↦
    (∑ j, Stationary.gradientRepresentative v x j j) * ⟪D x, φ x⟫ with hf₂
  have he₂ : f₂ =ᵐ[volume] 0 := by
    filter_upwards [htr] with x hx
    simp only [hf₂, hx, zero_mul, Pi.zero_apply]
  have hi₂ : Integrable f₂ := (integrable_zero _ _ _).congr he₂.symm
  have hI₂ : ∫ x, f₂ x = 0 := by
    rw [integral_congr_ae he₂]
    exact integral_zero _ _
  -- the transport term
  set f₃ : ℝ^3 → ℝ := fun x ↦ ⟪D x, fderiv ℝ φ x (Stationary.representative v x)⟫ with hf₃
  have he₃ : (fun x ↦ ∑ k : Fin 3, ∑ i : Fin 3, Stationary.representative v x i *
      Stationary.gradientRepresentative ψ x k i * D x k) =ᵐ[volume] f₃ := by
    filter_upwards [hdψ] with x hx
    simp only [hf₃]
    rw [PDE.inner_fderiv_apply_eq_sum ((hφ.differentiable (by simp)) x)]
    refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hx k i]
    ring
  have hi₃ : Integrable f₃ := (Stationary.integrable_convectionDensity v ψ d).congr he₃
  have hI₃ : ∫ x, f₃ x = Stationary.convectionTrilinear v ψ d := by
    rw [Stationary.convectionTrilinear_eq_integral]
    exact (integral_congr_ae he₃).symm
  have hpt : weakEigenDensity (U + D) μ v φ = weakEigenDensity U μ v φ + f₁ - f₂ - f₃ :=
    funext fun x ↦ weakEigenDensity_add_representative U d μ v φ x
  refine ⟨hpt ▸ ((hU.add hi₁).sub hi₂).sub hi₃, ?_⟩
  rw [hpt, integral_sub' ((hU.add hi₁).sub hi₂) hi₃, integral_sub' (hU.add hi₁) hi₂,
    integral_add' hU hi₁, hI₁, hI₂, hI₃, eigenPerturbation_apply]
  ring

/-- **Weighted bound.** In the norm `‖h‖_s² = s² ‖h‖₂² + ‖∇h‖₂²`, for `s > 0` and `t ≥ 0`
with `t² s ≥ 1`, `|eigenPerturbation d v w| ≤ t/2 ‖d‖_s ‖v‖_s ‖w‖_s`. -/
theorem abs_eigenPerturbation_le_weighted (d v w : H) {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t)
    (hst : 1 ≤ t ^ 2 * s) :
    |eigenPerturbation d v w| ≤ t / 2 *
      √(s ^ 2 * ‖Stationary.massCLM d‖ ^ 2 + ‖Stationary.gradientCLM d‖ ^ 2) *
      √(s ^ 2 * ‖Stationary.massCLM v‖ ^ 2 + ‖Stationary.gradientCLM v‖ ^ 2) *
      √(s ^ 2 * ‖Stationary.massCLM w‖ ^ 2 + ‖Stationary.gradientCLM w‖ ^ 2) := by
  have hN (u : H) : ‖Stationary.gradientCLM u‖ ≤
      √(s ^ 2 * ‖Stationary.massCLM u‖ ^ 2 + ‖Stationary.gradientCLM u‖ ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (s * ‖Stationary.massCLM u‖)])
  have h₁ := Stationary.norm_convectionTrilinear_le_weighted d v w hs ht hst
  have h₂ := Stationary.norm_convectionTrilinear_le_weighted v w d hs ht hst
  rw [Real.norm_eq_abs] at h₁ h₂
  have hNd := Real.sqrt_nonneg (s ^ 2 * ‖Stationary.massCLM d‖ ^ 2 +
    ‖Stationary.gradientCLM d‖ ^ 2)
  have hNv := Real.sqrt_nonneg (s ^ 2 * ‖Stationary.massCLM v‖ ^ 2 +
    ‖Stationary.gradientCLM v‖ ^ 2)
  have hNw := Real.sqrt_nonneg (s ^ 2 * ‖Stationary.massCLM w‖ ^ 2 +
    ‖Stationary.gradientCLM w‖ ^ 2)
  rw [eigenPerturbation_apply]
  calc _ ≤ |Stationary.convectionTrilinear d v w| + |Stationary.convectionTrilinear v w d| :=
        abs_sub _ _
    _ ≤ _ := add_le_add h₁ h₂
    _ ≤ t / 4 * √(s ^ 2 * ‖Stationary.massCLM d‖ ^ 2 + ‖Stationary.gradientCLM d‖ ^ 2) *
          √(s ^ 2 * ‖Stationary.massCLM v‖ ^ 2 + ‖Stationary.gradientCLM v‖ ^ 2) *
          √(s ^ 2 * ‖Stationary.massCLM w‖ ^ 2 + ‖Stationary.gradientCLM w‖ ^ 2) +
        t / 4 * √(s ^ 2 * ‖Stationary.massCLM v‖ ^ 2 + ‖Stationary.gradientCLM v‖ ^ 2) *
          √(s ^ 2 * ‖Stationary.massCLM w‖ ^ 2 + ‖Stationary.gradientCLM w‖ ^ 2) *
          √(s ^ 2 * ‖Stationary.massCLM d‖ ^ 2 + ‖Stationary.gradientCLM d‖ ^ 2) := by
        gcongr
        exacts [hN v, hN w]
    _ = _ := by ring

/-- **Bound with a bounded coefficient.** If the representative of `d` has Euclidean length at
most `S` almost everywhere, then
`|eigenPerturbation d v w| ≤ S (‖∇v‖₂ ‖w‖₂ + ‖v‖₂ ‖∇w‖₂)`. -/
theorem abs_eigenPerturbation_le_of_norm_le (d v w : H) {S : ℝ}
    (hS : ∀ᵐ x ∂volume, ‖Stationary.representative d x‖ ≤ S) :
    |eigenPerturbation d v w| ≤ S * (‖Stationary.gradientCLM v‖ * ‖Stationary.massCLM w‖ +
      ‖Stationary.massCLM v‖ * ‖Stationary.gradientCLM w‖) := by
  rw [eigenPerturbation_apply]
  calc _ ≤ |Stationary.convectionTrilinear d v w| + |Stationary.convectionTrilinear v w d| :=
        abs_sub _ _
    _ ≤ S * ‖Stationary.gradientCLM v‖ * ‖Stationary.massCLM w‖ +
        S * ‖Stationary.massCLM v‖ * ‖Stationary.gradientCLM w‖ :=
      add_le_add (Stationary.abs_convectionTrilinear_le_of_norm_le_left d v w hS)
        (Stationary.abs_convectionTrilinear_le_of_norm_le_right v w d hS)
    _ = _ := by ring

end NavierStokes.Nonuniqueness
