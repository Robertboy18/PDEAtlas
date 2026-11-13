/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Pullback.Dilation.WeakDerivative
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Gradient

/-!
# Dilation on first-order Sobolev spaces

We rescale the function and its weak derivatives in the same graph space used by
the rest of the library. Each first derivative acquires one factor of the scalar.
The change of variables formula gives a bounded map on the finite product of
`Lᵖ` coordinates, and the weak chain rule shows that this map preserves the graph.

No domain regularity or compact support is needed here. Boundary conditions enter
later, when a function on an open domain is extended by zero.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal Sobolev

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "μ" => domainMeasure n univ

/-- Dilation of every derivative row with its literal derivative-word scaling factor. -/
def dilationWkpAmbientCLM (a : ℝ) (ha : a ≠ 0) :
    W^{k,p}(ℝ^n) →L[ℝ] WkpAmbientOn n k p univ :=
  (PiLp.continuousLinearEquiv p ℝ
    (fun _ : DerivIndex n k ↦ DerivLp n p univ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun α ↦
        a ^ α.toList.length • (Lp.compSMul μ p a ha).comp (wkpCoordinateCLM α))

/-- The ambient dilation uses the ordinary Lp pullback in each coordinate. -/
theorem dilationWkpAmbientCLM_coordinate (a : ℝ) (ha : a ≠ 0)
    (u : W^{k,p}(ℝ^n)) (α : DerivIndex n k) :
    dilationWkpAmbientCLM a ha u α =
      a ^ α.toList.length • Lp.compSMul μ p a ha (wkpCoordinateCLM α u) :=
  rfl

/-- The base row of the ambient dilation is the literal dilation of the value. -/
theorem dilationWkpAmbientCLM_base_ae (a : ℝ) (ha : a ≠ 0) (u : W^{k,p}(ℝ^n)) :
    (dilationWkpAmbientCLM a ha u (baseIndex n k) : ℝ^n → ℝ) =ᵐ[μ]
      fun x ↦ baseRepresentative u (a • x) := by
  simpa only [dilationWkpAmbientCLM_coordinate, baseIndex_toList, List.length_nil,
    pow_zero, one_smul, baseRepresentative, wkpCoordinateCLM_apply] using
    Lp.coeFn_compSMul μ p a ha (wkpCoordinateCLM (baseIndex n k) u)

/-- The dilated coordinates still satisfy the defining weak derivative identities. -/
theorem dilationWkpAmbientCLM_one_mem (hp : p ≠ ∞) (a : ℝ) (ha : a ≠ 0)
    (u : W^{1,p}(ℝ^n)) : dilationWkpAmbientCLM a ha u ∈ wkpSubmoduleOn n 1 p univ := by
  intro α
  have hbase := dilationWkpAmbientCLM_base_ae a ha u
  rcases α.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
  · simpa only [baseIndex_toList] using
      hasWeakDerivativeOn_nil
        (memLp_locallyIntegrableOn_domain
          (Lp.memLp (dilationWkpAmbientCLM a ha u (baseIndex n 1))) (Fact.out : 1 ≤ p))
  · have hrow :
        (dilationWkpAmbientCLM a ha u (singleDerivIndex n i) : ℝ^n → ℝ) =ᵐ[μ]
          fun x ↦ a * wkpCoordinateCLM (singleDerivIndex n i) u (a • x) := by
      simp only [dilationWkpAmbientCLM_coordinate, singleDerivIndex_toList,
        List.length_singleton, pow_one]
      filter_upwards [Lp.coeFn_smul a
        (Lp.compSMul μ p a ha (wkpCoordinateCLM (singleDerivIndex n i) u)),
        Lp.coeFn_compSMul μ p a ha (wkpCoordinateCLM (singleDerivIndex n i) u)]
        with x hs hc
      simp only [hs, Pi.smul_apply, smul_eq_mul, hc]
    have hweak (j : Fin n) :
        HasWeakDerivativeOn univ [j] (baseRepresentative u)
          (wkpCoordinateCLM (singleDerivIndex n j) u : ℝ^n → ℝ) := by
      simpa only [singleDerivIndex_toList, baseRepresentative, wkpCoordinateCLM_apply] using
        u.property (singleDerivIndex n j)
    simpa only [singleDerivIndex_toList] using
      (WeakChangeOfVariables.hasWeakDerivativeOn_comp_smul hp a ha
        (Lp.memLp (wkpCoordinateCLM (baseIndex n 1) u))
        (fun j ↦ Lp.memLp (wkpCoordinateCLM (singleDerivIndex n j) u)) hweak i).congr_ae
          hbase.symm hrow.symm

/-- Nonzero scalar dilation as a bounded operator on the W¹ᵖ graph. -/
def dilationW1pCLM (hp : p ≠ ∞) (a : ℝ) (ha : a ≠ 0) : W^{1,p}(ℝ^n) →L[ℝ] W^{1,p}(ℝ^n) :=
  (dilationWkpAmbientCLM a ha).codRestrict
    (wkpSubmoduleOn n 1 p univ) (dilationWkpAmbientCLM_one_mem hp a ha)

/-- Each graph coordinate has the scale prescribed by its derivative order. -/
theorem dilationW1pCLM_coordinate (hp : p ≠ ∞) (a : ℝ) (ha : a ≠ 0)
    (u : W^{1,p}(ℝ^n)) (α : DerivIndex n 1) :
    wkpCoordinateCLM α (dilationW1pCLM hp a ha u) =
      a ^ α.toList.length • Lp.compSMul μ p a ha (wkpCoordinateCLM α u) :=
  rfl

/-- The value represented by the dilated Sobolev graph is the dilated original value. -/
theorem dilationW1pCLM_base_ae (hp : p ≠ ∞) (a : ℝ) (ha : a ≠ 0) (u : W^{1,p}(ℝ^n)) :
    baseRepresentative (dilationW1pCLM hp a ha u) =ᵐ[μ]
      fun x ↦ baseRepresentative u (a • x) :=
  dilationWkpAmbientCLM_base_ae a ha u

/-- Each first weak derivative is the dilated original derivative times the scalar. -/
theorem dilationW1pCLM_derivative_ae (hp : p ≠ ∞) (a : ℝ) (ha : a ≠ 0)
    (u : W^{1,p}(ℝ^n)) (i : Fin n) :
    (wkpCoordinateCLM (singleDerivIndex n i) (dilationW1pCLM hp a ha u) : ℝ^n → ℝ)
      =ᵐ[μ] fun x ↦ a * wkpCoordinateCLM (singleDerivIndex n i) u (a • x) := by
  simp only [dilationW1pCLM_coordinate, singleDerivIndex_toList,
    List.length_singleton, pow_one]
  filter_upwards [Lp.coeFn_smul a
    (Lp.compSMul μ p a ha (wkpCoordinateCLM (singleDerivIndex n i) u)),
    Lp.coeFn_compSMul μ p a ha (wkpCoordinateCLM (singleDerivIndex n i) u)] with x hs hc
  simp only [hs, Pi.smul_apply, smul_eq_mul, hc]

/-- The vector-valued weak gradient obeys the same dilation rule as its coordinates. -/
theorem wkpGradientCLM_dilationW1pCLM (hp : p ≠ ∞) (a : ℝ) (ha : a ≠ 0) (u : W^{1,p}(ℝ^n)) :
    ∇ (dilationW1pCLM hp a ha u) =
      a • Lp.compSMul μ p a ha (∇ u) := by
  apply Lp.ext
  have hrows : ∀ᵐ x ∂μ, ∀ i : Fin n,
      wkpCoordinateCLM (singleDerivIndex n i) (dilationW1pCLM hp a ha u) x =
        a * wkpCoordinateCLM (singleDerivIndex n i) u (a • x) :=
    ae_all_iff.mpr fun i ↦ dilationW1pCLM_derivative_ae hp a ha u i
  have hgradient : ∀ᵐ x ∂μ, ∀ i : Fin n,
      ∇ u (a • x) i = wkpCoordinateCLM (singleDerivIndex n i) u (a • x) :=
    (Measure.quasiMeasurePreserving_smul μ ha).ae (wkpGradientCLM_apply_ae u)
  filter_upwards [wkpGradientCLM_apply_ae (dilationW1pCLM hp a ha u), hrows, hgradient,
    Lp.coeFn_smul a (Lp.compSMul μ p a ha (∇ u)),
    Lp.coeFn_compSMul μ p a ha (∇ u)] with x hl hr hg hs hc
  apply PiLp.ext
  intro i
  simp only [hs, Pi.smul_apply, hc, PiLp.smul_apply, smul_eq_mul, hl,
    ← wkpCoordinateCLM_apply, hr, hg]

/-- Exact scaling of the Euclidean weak-gradient norm, at every finite Sobolev exponent. -/
theorem norm_wkpGradientCLM_dilationW1pCLM
    (hp : p ≠ ∞) (a : ℝ) (ha : a ≠ 0) (u : W^{1,p}(ℝ^n)) :
    ‖∇ (dilationW1pCLM hp a ha u)‖ =
      |a| * |(a ^ n)⁻¹| ^ (1 / p).toReal * ‖∇ u‖ := by
  rw [wkpGradientCLM_dilationW1pCLM, norm_smul, Lp.norm_compSMul]
  simp only [Real.norm_eq_abs, finrank_euclideanSpace_fin, mul_assoc]

/-- Reciprocal dilation recovers the original Sobolev element, including its weak gradient. -/
@[simp] theorem dilationW1pCLM_inv_dilationW1pCLM
    (hp : p ≠ ∞) (a : ℝ) (ha : a ≠ 0) (u : W^{1,p}(ℝ^n)) :
    dilationW1pCLM hp a⁻¹ (inv_ne_zero ha) (dilationW1pCLM hp a ha u) = u := by
  apply Subtype.ext
  apply PiLp.ext
  intro α
  change wkpCoordinateCLM α
    (dilationW1pCLM hp a⁻¹ (inv_ne_zero ha) (dilationW1pCLM hp a ha u)) =
      wkpCoordinateCLM α u
  rw [dilationW1pCLM_coordinate, dilationW1pCLM_coordinate, map_smul,
    Lp.compSMul_inv_compSMul, smul_smul, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero _ ha), one_smul]

end SobolevSpace.GraphSpace
