/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.RealLine.SecondOrder

/-!
# Weak H² pullback on the real line

The derivative of a pullback is the Jacobian-weighted pullback of the
original first derivative. The weak H¹ weighted pullback theorem
therefore supplies the second derivative without a classical second
derivative of the input. The estimate only requires a Lipschitz inverse
and bounded first and second derivatives of the coordinate map.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Sobolev

namespace SobolevSpace.GraphSpace

/-- A positive C² change of coordinates with bounded derivatives preserves
weak H². The resulting graph represents the pullback of the given continuous
representative, with a bound depending only on the coordinate map. -/
theorem exists_h2_comp_of_bounded_positive_jacobian
    (e : ℝ ≃ₜ ℝ) {K : NNReal} (he : LipschitzWith K e.symm)
    {J J' : ℝ → ℝ} {M N : ℝ}
    (hJ : Continuous J) (hJ' : Continuous J')
    (hJpos : ∀ x, 0 ≤ J x) (he' : ∀ x, HasDerivAt e (J x) x)
    (hderiv : ∀ x, HasDerivAt J (J' x) x)
    (hJbound : ∀ x, ‖J x‖ ≤ M) (hJ'bound : ∀ x, ‖J' x‖ ≤ N)
    (W₀ : W^{2,2}(ℝ^1)) {v : ℝ → ℝ} (hv : Continuous v)
    (hW₀ : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W₀) : ℝ → ℝ)
      =ᵐ[volume] v) :
    ∃ W : W^{2,2}(ℝ^1),
      (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) : ℝ → ℝ) =ᵐ[volume]
        (fun x ↦ v (e x)) ∧
      ‖W‖ ≤ succOrderAssemblyNormBound 1 1 *
        (Real.sqrt K * (1 + 2 * (M + N + M * M)) * ‖W₀‖) := by
  let U := lowerOrderCLM (by decide : 1 ≤ 2) W₀
  let V := ∂[0] W₀
  have hUV : realLineCoordinateCLM (baseIndex 1 1) V =
      realLineCoordinateCLM (singleDerivIndex 1 0) U := by
    apply congrArg oneDimensionalPushforwardL2
    change (V : WkpAmbientOn 1 1 2 univ) (baseIndex 1 1) =
      (U : WkpAmbientOn 1 1 2 univ) (singleDerivIndex 1 0)
    simp only [V, U, partialDerivCLM, derivativeWordCLM_apply,
      derivativeWordIndex_singleton_baseIndex, lowerOrderCLM_apply,
      DerivIndex.castOrder_singleDerivIndex]
  have hUbase : realLineCoordinateCLM (baseIndex 1 1) U =
      oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W₀) := by
    apply congrArg oneDimensionalPushforwardL2
    change (U : WkpAmbientOn 1 1 2 univ) (baseIndex 1 1) =
      (W₀ : WkpAmbientOn 1 2 2 univ) (baseIndex 1 2)
    simp only [U, lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex]
  have hUrep : realLineRepresentative U = v :=
    (Continuous.ae_eq_iff_eq volume (continuous_realLineRepresentative U) hv).mp
      ((hUbase ▸ realLineCoordinate_ae_representative U).symm.trans hW₀)
  have hVrep : (realLineCoordinateCLM (singleDerivIndex 1 0) U : ℝ → ℝ)
      =ᵐ[volume] realLineRepresentative V := hUV ▸ realLineCoordinate_ae_representative V
  obtain ⟨D, hDnorm, hDrep, _hDrow⟩ :=
    exists_h1_jacobian_weighted_pullback e he hJ hJ' hJpos he' hderiv hJbound hJ'bound V
  have hcomp := hasWeakTimeDerivativeOn_comp_of_positive_jacobian e he hJ hJpos he'
    hJbound (continuous_realLineRepresentative U) (memLp_realLineRepresentative V)
    ((hasWeakTimeDerivativeOn_realLineRepresentative U).congr_ae .rfl hVrep)
  rw [← hDrep] at hcomp
  have hbase := memLp_comp_of_lipschitz_inverse e he (memLp_realLineRepresentative U)
  let S := mkW12OfWeakDerivative hbase (memLp_realLineRepresentative D) hcomp
  have hSD : realLineCoordinateCLM (baseIndex 1 1) D =
      realLineCoordinateCLM (singleDerivIndex 1 0) S := by
    change _ = realLineCoordinateCLM (singleDerivIndex 1 0)
      (mkW12OfWeakDerivative hbase (memLp_realLineRepresentative D) hcomp)
    rw [realLineCoordinateCLM_mkW12_single, toLp_realLineRepresentative]
  obtain ⟨W, hWbase, hWnorm⟩ := exists_h2_of_realLine_h1_derivative S D hSD
  have hSrep : realLineRepresentative S = fun x ↦ v (e x) :=
    (realLineRepresentative_mkW12 hbase (memLp_realLineRepresentative D) hcomp
      ((continuous_realLineRepresentative U).comp e.continuous)).trans
        (funext fun x ↦ congrFun hUrep (e x))
  have hM : 0 ≤ M := (norm_nonneg (J 0)).trans (hJbound 0)
  have hN : 0 ≤ N := (norm_nonneg (J' 0)).trans (hJ'bound 0)
  have hV (α) : ‖realLineCoordinateCLM α V‖ ≤ ‖W₀‖ :=
    (norm_realLineCoordinateCLM_le _ V).trans (norm_derivativeWordCLM_apply_le _ _ W₀)
  have hD : ‖D‖ ≤ Real.sqrt K * ((M + N + M * M) * ‖W₀‖) := by
    refine hDnorm.trans ?_
    rw [add_mul (M + N)]
    have := add_nonneg hM hN
    gcongr <;> exact hV _
  have hS : ‖S‖ ≤ Real.sqrt K * ‖W₀‖ + ‖D‖ := by
    change ‖realLineH1Jet _ _‖ ≤ _
    refine (norm_realLineH1Jet_le _ _).trans ?_
    have h := norm_toLp_comp_of_lipschitz_inverse e he (memLp_realLineRepresentative U)
    rw [toLp_realLineRepresentative] at h ⊢
    have hU := (norm_realLineCoordinateCLM_le (baseIndex 1 1) U).trans
      (norm_lowerOrderCLM_apply_le _ W₀)
    exact add_le_add (h.trans (by gcongr)) (norm_realLineCoordinateCLM_le _ D)
  refine ⟨W, hWbase ▸ (realLineCoordinate_ae_representative S).trans (.of_eq hSrep),
    hWnorm.trans (mul_le_mul_of_nonneg_left ?_ succOrderAssemblyNormBound_nonneg)⟩
  linarith

/-- Positive scalar pullback and amplitude multiplication preserve the weak H² graph, with the bound
from the existing real-line pullback theorem. -/
theorem exists_h2_scaled_representative
    (W : W^{2,2}(ℝ^1)) {v : ℝ → ℝ} (hv : Continuous v)
    (hW : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) : ℝ → ℝ) =ᵐ[volume] v)
    (A : ℝ) {L : ℝ} (hL : 0 < L) :
    ∃ V : W^{2,2}(ℝ^1),
      (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM V) : ℝ → ℝ) =ᵐ[volume]
        (fun x ↦ A * v (L * x)) ∧
      ‖V‖ ≤ |A| * (succOrderAssemblyNormBound 1 1 *
        (Real.sqrt L⁻¹ * (1 + 2 * (L + L * L)) * ‖W‖)) := by
  let e : ℝ ≃ₜ ℝ := Homeomorph.mulLeft₀ L hL.ne'
  have he : LipschitzWith ‖L⁻¹‖₊ e.symm := by
    simpa only [e, Homeomorph.mulLeft₀_symm_apply, smul_eq_mul] using
      (lipschitzWith_smul (β := ℝ) L⁻¹)
  obtain ⟨P, hP, hnorm⟩ := exists_h2_comp_of_bounded_positive_jacobian e he
    (J := fun _ ↦ L) (J' := fun _ ↦ 0) (M := L) (N := 0)
    continuous_const continuous_const (fun _ ↦ hL.le)
    (fun x ↦ ((hasDerivAt_id x).const_mul L).congr_deriv (mul_one L))
    (fun x ↦ hasDerivAt_const x L) (fun _ ↦ (Real.norm_of_nonneg hL.le).le)
    (fun _ ↦ norm_zero.le) W hv hW
  refine ⟨A • P, ?_, ?_⟩
  · rw [map_smul, map_smul]
    filter_upwards [Lp.coeFn_smul A (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM P)),
      hP] with x hs hp
    simp only [hs, Pi.smul_apply, smul_eq_mul, hp, e, Homeomorph.coe_mulLeft₀]
  · rw [norm_smul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left ?_ (abs_nonneg A)
    simpa only [coe_nnnorm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL), add_zero]
      using hnorm

end SobolevSpace.GraphSpace
