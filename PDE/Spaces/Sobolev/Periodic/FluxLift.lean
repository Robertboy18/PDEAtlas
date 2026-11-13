/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Periodic.TestPeriodization
public import PDE.Spaces.Sobolev.Periodic.Definitions

/-!
# Euclidean tests for periodic divergence-free fields

Orthogonality to periodic Sobolev gradients implies the divergence identity
against compactly supported Euclidean C¹ functions. The proof periodizes the
test and unfolds its pairing. Every nonzero dilation preserves this identity.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology InnerProductSpace Gradient

namespace SobolevSpace.Periodic

/-- A periodic L² field orthogonal to periodic Sobolev gradients is divergence-free
against compactly supported Euclidean C¹ tests. -/
theorem integral_inner_gradient_toTorus_eq_zero {n : ℕ}
    (v : Lp (ℝ^n) 2 (cellMeasure n))
    (hv : ∀ u : h1Space n, ⟪v, gradientCLM n u⟫_ℝ = 0)
    {φ : ℝ^n → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫ x, ⟪v (toTorus n x), ∇ φ x⟫_ℝ) = 0 := by
  let G := periodizeTorus (∇ φ) (PDE.Analysis.continuous_gradient_of_contDiff hφ)
    hφc.gradient
  let U := ofContinuous (periodizeTorus φ hφ.continuous hφc) G
    (hasDerivAt_periodizeTorus hφ hφc)
  have hu := hv U
  change ⟪v, ContinuousMap.toLp 2 (cellMeasure n) ℝ G⟫_ℝ = 0 at hu
  rw [L2.inner_def] at hu
  have he : (∫ y, ⟪v y, G y⟫_ℝ ∂cellMeasure n) = 0 := by
    convert hu using 1
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (cellMeasure n) G] with y hy
    rw [hy]
  exact (integral_inner_periodizeTorus v (PDE.Analysis.continuous_gradient_of_contDiff hφ)
    hφc.gradient).symm.trans he

/-- Dilation preserves the vanishing divergence identity for compact C¹ tests. -/
theorem integral_inner_gradient_comp_smul_eq_zero {n : ℕ} (v : ℝ^n → ℝ^n)
    (hv : ∀ φ : ℝ^n → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ x, ⟪v x, ∇ φ x⟫_ℝ) = 0)
    (c : ℝ) (hc : c ≠ 0) {φ : ℝ^n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫ x, ⟪v (c • x), ∇ φ x⟫_ℝ) = 0 := by
  let e : ℝ^n ≃L[ℝ] ℝ^n := ContinuousLinearEquiv.smulLeft (Units.mk0 c⁻¹ (inv_ne_zero hc))
  let ψ : ℝ^n → ℝ := φ ∘ e
  have hψ : ContDiff ℝ 1 ψ := hφ.comp e.contDiff
  have hψc : HasCompactSupport ψ := hφc.comp_homeomorph e.toHomeomorph
  have hg (x : ℝ^n) : ∇ ψ x = c⁻¹ • ∇ φ (c⁻¹ • x) := by
    apply (InnerProductSpace.toDual ℝ (ℝ^n)).injective
    rw [toDual_gradient, map_smul, toDual_gradient]
    have hd := ((hφ.differentiable (by simp)) (c⁻¹ • x)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul c⁻¹)
    change fderiv ℝ ψ x = _
    rw [show fderiv ℝ ψ x = (fderiv ℝ φ (c⁻¹ • x)).comp
      (c⁻¹ • ContinuousLinearMap.id ℝ (ℝ^n)) from hd.fderiv]
    ext y
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul]
  have hz := hv ψ hψ hψc
  simp only [hg, inner_smul_right, integral_const_mul] at hz
  have hz' : (∫ x, ⟪v x, ∇ φ (c⁻¹ • x)⟫_ℝ) = 0 :=
    (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hc)
  have he := Measure.integral_comp_smul volume (fun x ↦ ⟪v x, ∇ φ (c⁻¹ • x)⟫_ℝ) c
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul, hz', smul_zero] using he

/-- Every nonzero rescaling of a periodic divergence-free L² field remains
Euclidean divergence-free. -/
theorem integral_inner_gradient_toTorus_smul_eq_zero {n : ℕ}
    (v : Lp (ℝ^n) 2 (cellMeasure n))
    (hv : ∀ u : h1Space n, ⟪v, gradientCLM n u⟫_ℝ = 0)
    (c : ℝ) (hc : c ≠ 0) {φ : ℝ^n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫ x, ⟪v (toTorus n (c • x)), ∇ φ x⟫_ℝ) = 0 :=
  integral_inner_gradient_comp_smul_eq_zero (fun x ↦ v (toTorus n x))
    (fun _ hφ hφc ↦ integral_inner_gradient_toTorus_eq_zero v hv hφ hφc) c hc hφ hφc

end SobolevSpace.Periodic
