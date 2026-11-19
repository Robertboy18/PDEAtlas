/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarResolventVector
public import PDE.Fluid.NavierStokes.Stationary.WeakUniqueness
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Existence of `H²` solutions of the shifted linearized profile equation

Let `w ∈ H¹(ℝ³)³` be divergence free and let `R_μ = (μ + L₀)⁻¹` be the free self-similar resolvent,
`L₀ = -1/2 - (1/2) x·∇ - Δ`. For every large `μ` and every `G ∈ L²(ℝ³)³` there is a field
`z ∈ H²(ℝ³)³` with divergence-free first-order part and `(μ + L₀) z + Π((w·∇) z) = Π G` against
smooth compactly supported divergence-free fields (`exists_vectorH2_weak_shifted_convection`). No
smallness of `w` is needed.

## How it works

The convection `N_w z = ∑ⱼ wⱼ ∂ⱼ z` maps `H²` into `L²` (`convectionCLM`) because products of
`H¹(ℝ³)` functions lie in `L²`. Approximating each `wⱼ` in `H¹` by a bounded smooth function splits
`‖wⱼ g‖` into `ε ‖g‖_{H¹}` plus a bounded multiple of `‖g‖_{L²}` (`exists_norm_mulH1_le`). The
resolvent is bounded from `L²` into `H²` uniformly in `μ` and its first-order part is `O(μ^{-1/2})`,
so `K = Π N_w R_μ` has norm at most `1/2` for large `μ`
(`exists_norm_projectedConvectionResolvent_le`). The equation `h + K h = Π G` is then solved by the
invertibility of `1 - t` for `‖t‖ < 1` in Mathlib (`Units.oneSub`, used in
`exists_add_projectedConvectionResolvent_eq`), and we take `z = R_μ h`. The weak equation follows
from the adjoint identity of the resolvent, since the Leray projection drops out against solenoidal
test fields (`sum_integral_leraySobolev_mul`) and the convection pairing is integrated by parts
(`sum_integral_convectionCLM_mul`).
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace HeatEquation.WholeSpace
open SobolevSpace.Fractional
open scoped ENNReal NNReal Sobolev ContDiff SobolevSpace.WholeSpaceHilbert


namespace NavierStokes.Stationary

theorem norm_mulH1_le (V U : H¹(ℝ^3)) :
    ‖mulH1 V U‖ ≤ SobolevSpace.Inequalities.exists_eLpNorm_mul_le_H1.choose * ‖V‖ * ‖U‖ := by
  have hC := SobolevSpace.Inequalities.exists_eLpNorm_mul_le_H1.choose_spec.1
  refine ((mulH1 V).le_opNorm U).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- Splitting the multiplier: `V U = (V - Ψ) U + Ψ U`. -/
theorem mulH1_eq_add (V Ψ U : H¹(ℝ^3)) :
    mulH1 V U = mulH1 (V - Ψ) U + mulH1 Ψ U := by
  apply Lp.ext
  have hV : baseRepresentative V =ᵐ[volume]
      fun x ↦ baseRepresentative (V - Ψ) x + baseRepresentative Ψ x := by
    have h := baseRepresentative_add_ae (V - Ψ) Ψ
    rw [sub_add_cancel] at h
    simpa [domainMeasure] using h
  have hadd := Lp.coeFn_add (mulH1 (V - Ψ) U) (mulH1 Ψ U)
  have key : (mulH1 V U : ℝ^3 → ℝ) =ᵐ[volume] ⇑(mulH1 (V - Ψ) U + mulH1 Ψ U) := by
    have hadd' : ⇑(mulH1 (V - Ψ) U + mulH1 Ψ U) =ᵐ[volume]
        ⇑(mulH1 (V - Ψ) U) + ⇑(mulH1 Ψ U) := by simpa [domainMeasure] using hadd
    filter_upwards [mulH1_ae V U, mulH1_ae (V - Ψ) U, mulH1_ae Ψ U, hadd', hV]
      with x h1 h2 h3 h4 h5
    rw [h1, h4, Pi.add_apply, h2, h3, h5]
    ring
  simpa [domainMeasure] using key

/-- Multiplication by a fixed `H¹(ℝ³)` function is a small multiple of the `H¹` norm plus a
bounded multiple of the `L²` norm. -/
theorem exists_norm_mulH1_le (W : H¹(ℝ^3)) {ε : ℝ} (hε : 0 < ε) :
    ∃ M, 0 ≤ M ∧ ∀ U : H¹(ℝ^3), ‖mulH1 W U‖ ≤ ε * ‖U‖ + M * ‖wkpBaseCoordinateCLM U‖ := by
  set C := SobolevSpace.Inequalities.exists_eLpNorm_mul_le_H1.choose
  have hC0 : 0 ≤ C := SobolevSpace.Inequalities.exists_eLpNorm_mul_le_H1.choose_spec.1
  obtain ⟨f, hf, hc, hconv⟩ := globalApproximation_WkpSpace (n := 3) (p := 2)
    (Approximation.standardMollifier 3) (by norm_num) 1 W
  have hδ : 0 < ε / (C + 1) := by positivity
  obtain ⟨m, hm⟩ := (hconv.eventually (gt_mem_nhds hδ)).exists
  set Ψ := mkWkpSpaceOnOfContDiff (n := 3) (k := 1) (p := 2) (Ω := univ) (f m) (hf m) (hc m)
  obtain ⟨M, hM⟩ := (hf m).continuous.bounded_above_of_compact_support (hc m)
  refine ⟨max M 0, le_max_right _ _, fun U ↦ ?_⟩
  have hbase : baseRepresentative Ψ =ᵐ[volume] f m := by
    have h := mkWkpSpaceOnOfContDiff_apply_ae (n := 3) (k := 1) (p := 2) (Ω := univ)
      (f m) (hf m) (hc m) (baseIndex 3 1)
    simpa [domainMeasure, baseRepresentative, iteratedPartialDeriv] using h
  have hsmall : ‖mulH1 (W - Ψ) U‖ ≤ ε * ‖U‖ := by
    refine (norm_mulH1_le _ _).trans ?_
    have h1 : ‖W - Ψ‖ ≤ ε / (C + 1) := by rw [norm_sub_rev]; exact hm.le
    have h2 : C * (ε / (C + 1)) ≤ ε := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    calc C * ‖W - Ψ‖ * ‖U‖ ≤ C * (ε / (C + 1)) * ‖U‖ := by gcongr
      _ ≤ ε * ‖U‖ := by gcongr
  have hbdd : ‖mulH1 Ψ U‖ ≤ max M 0 * ‖wkpBaseCoordinateCLM U‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    have hb : (wkpBaseCoordinateCLM U : ℝ^3 → ℝ) = baseRepresentative U := rfl
    have key : ∀ᵐ x ∂volume, ‖(mulH1 Ψ U : ℝ^3 → ℝ) x‖ ≤
        max M 0 * ‖(wkpBaseCoordinateCLM U : ℝ^3 → ℝ) x‖ := by
      filter_upwards [mulH1_ae Ψ U, hbase] with x h1 h2
      rw [h1, h2, hb, norm_mul]
      exact mul_le_mul_of_nonneg_right ((hM x).trans (le_max_left _ _)) (norm_nonneg _)
    simpa [domainMeasure] using key
  calc ‖mulH1 W U‖ = ‖mulH1 (W - Ψ) U + mulH1 Ψ U‖ := by rw [← mulH1_eq_add]
    _ ≤ ‖mulH1 (W - Ψ) U‖ + ‖mulH1 Ψ U‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hsmall hbdd

/-- The weak derivative `∂ⱼ U ∈ H¹` of `U ∈ H²`. -/
abbrev partialH2 {n : ℕ} (j : Fin n) : W^{2,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n) :=
  derivativeWordCLM (n := n) (Ω := univ) (p := 2) [j] (by simp)

theorem wkpBaseCoordinateCLM_partialH2 {n : ℕ} (j : Fin n) (U : W^{2,2}(ℝ^n)) :
    wkpBaseCoordinateCLM (partialH2 j U) = wkpCoordinateCLM (singleDerivIndex n j)
      (lowerOrderCLM (n := n) (p := 2) (Ω := univ) (by norm_num : 1 ≤ 2) U) := by
  have h := derivIndexOfList_toList ((singleDerivIndex n j).castOrder (by norm_num : 1 ≤ 2))
    ((singleDerivIndex n j).castOrder (by norm_num : 1 ≤ 2)).toList_length_le
  simp only [DerivIndex.castOrder_toList, singleDerivIndex_toList] at h
  rw [wkpBaseCoordinateCLM_apply, wkpCoordinateCLM_apply, derivativeWordCLM_apply,
    lowerOrderCLM_apply, derivativeWordIndex_baseIndex, h]

/-- The convection `(w·∇) z = ∑ⱼ wⱼ ∂ⱼ z` of a vector `H²` field by a vector `H¹` field, as a
bounded map into vector `L²`. -/
def convectionCLM (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) : VectorH 3 2 →L[ℝ] VectorH 3 0 :=
  ContinuousLinearMap.piLpMap 2 (fun _ : Fin 3 ↦ ∑ j : Fin 3,
    ((lpEquivZeroOrder (n := 3) (p := 2) (Ω := univ)).toContinuousLinearEquiv :
        DerivLp 3 2 univ →L[ℝ] W^{0,2}(ℝ^3)).comp ((mulH1 (w j)).comp (partialH2 j)))

theorem wkpBaseCoordinateCLM_convectionCLM (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)))
    (z : VectorH 3 2) (i : Fin 3) :
    wkpBaseCoordinateCLM (convectionCLM w z i) = ∑ j, mulH1 (w j) (partialH2 j (z i)) := by
  simp only [convectionCLM, ContinuousLinearMap.piLpMap_apply, sum_apply,
    ContinuousLinearMap.comp_apply, map_sum]
  rfl

theorem norm_convectionCLM_apply_le (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) (z : VectorH 3 2)
    (i : Fin 3) : ‖convectionCLM w z i‖ ≤ ∑ j, ‖mulH1 (w j) (partialH2 j (z i))‖ := by
  have h : convectionCLM w z i = ∑ j, lpEquivZeroOrder (n := 3) (p := 2) (Ω := univ)
      (mulH1 (w j) (partialH2 j (z i))) := by
    simp only [convectionCLM, ContinuousLinearMap.piLpMap_apply, sum_apply,
      ContinuousLinearMap.comp_apply]
    rfl
  rw [h]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp only [LinearIsometryEquiv.norm_map]

/-- Convection by a vector `H¹(ℝ³)` field is small on `H²` up to a bounded multiple of the
`H¹` norm. -/
theorem exists_norm_convectionCLM_le (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) {ε : ℝ}
    (hε : 0 < ε) : ∃ M, 0 ≤ M ∧ ∀ (z : VectorH 3 2) (i : Fin 3), ‖convectionCLM w z i‖ ≤
      3 * ε * ‖z i‖ +
        M * ‖lowerOrderCLM (n := 3) (p := 2) (Ω := univ) (by norm_num : 1 ≤ 2) (z i)‖ := by
  have h := fun j : Fin 3 ↦ exists_norm_mulH1_le (w j) hε
  choose M hM0 hM using h
  refine ⟨∑ j, M j, Finset.sum_nonneg fun j _ ↦ hM0 j, fun z i ↦ ?_⟩
  refine (norm_convectionCLM_apply_le w z i).trans ?_
  have hj : ∀ j, ‖mulH1 (w j) (partialH2 j (z i))‖ ≤ ε * ‖z i‖ +
      M j * ‖lowerOrderCLM (n := 3) (p := 2) (Ω := univ) (by norm_num : 1 ≤ 2) (z i)‖ := by
    intro j
    refine (hM j _).trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_left (norm_derivativeWordCLM_apply_le _ _ _) hε.le
    · apply mul_le_mul_of_nonneg_left _ (hM0 j)
      rw [wkpBaseCoordinateCLM_partialH2, wkpCoordinateCLM_apply]
      exact PiLp.norm_apply_le _ _
  refine (Finset.sum_le_sum fun j _ ↦ hj j).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.sum_mul]
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-- The projected convection of the resolvent, `K = Π N_w R_μ`, on vector `L²`. -/
def projectedConvectionResolvent (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) {μ : ℝ}
    (hμ : 1 / 2 ≤ μ) : VectorH 3 0 →L[ℝ] VectorH 3 0 :=
  (IncompressibleFlow.leraySobolev 3 0).comp
    ((convectionCLM w).comp (vectorSelfsimilarResolventH2 3 (by norm_num) hμ))

theorem projectedConvectionResolvent_apply (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) {μ : ℝ}
    (hμ : 1 / 2 ≤ μ) (h : VectorH 3 0) :
    projectedConvectionResolvent w hμ h = IncompressibleFlow.leraySobolev 3 0
      (convectionCLM w (vectorSelfsimilarResolventH2 3 (by norm_num) hμ h)) :=
  rfl

/-- A three-component field with components of norm at most `a` has norm at most `2a`. -/
theorem norm_le_two_mul_of_forall_norm_le {k : ℕ} (x : VectorH 3 k) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ i, ‖x i‖ ≤ a) : ‖x‖ ≤ 2 * a := by
  have hsq : ‖x‖ ^ 2 ≤ 3 * a ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin 3, a ^ 2 :=
          Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (h i) 2
      _ = 3 * a ^ 2 := by simp
  nlinarith [norm_nonneg x]

/-- For large `μ` the projected convection of the resolvent is a contraction. -/
theorem exists_norm_projectedConvectionResolvent_le (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) :
    ∃ μ₀, 1 ≤ μ₀ ∧ ∀ μ (hμ : 1 / 2 ≤ μ), μ₀ ≤ μ →
      ‖projectedConvectionResolvent w hμ‖ ≤ 1 / 2 := by
  set T₂ := toWkpSpaceNormBound 3 2
  set T₁ := toWkpSpaceNormBound 3 1
  have hT₂ : 0 ≤ T₂ := toWkpSpaceNormBound_nonneg
  have hT₁ : 0 ≤ T₁ := toWkpSpaceNormBound_nonneg
  set ε := 1 / (48 * (T₂ + 1))
  have hε : 0 < ε := by positivity
  obtain ⟨M, hM0, hM⟩ := exists_norm_convectionCLM_le w hε
  refine ⟨(16 * M * T₁ + 1) ^ 2, by nlinarith [mul_nonneg hM0 hT₁], fun μ hμ' hμ ↦ ?_⟩
  have hμ1 : 1 ≤ μ := le_trans (by nlinarith [mul_nonneg hM0 hT₁]) hμ
  have hμ0 : 0 < μ := by linarith
  have hsq : 16 * M * T₁ + 1 ≤ Real.sqrt μ := by
    rw [show 16 * M * T₁ + 1 = Real.sqrt ((16 * M * T₁ + 1) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hμ
  have hsqpos : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ0
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro h
  set z := vectorSelfsimilarResolventH2 3 (by norm_num) hμ' h
  have hz : ‖z‖ ≤ 2 * T₂ * ‖h‖ := by
    refine (norm_vectorSelfsimilarResolventH2_apply_le _ _ h).trans ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [mul_comm 2 T₂]
    apply mul_le_mul_of_nonneg_left _ hT₂
    have h1 : μ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hμ1
    have h2 : (4 * Real.pi ^ 2)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      nlinarith [Real.pi_gt_three]
    linarith
  have hlow : ∀ i, ‖lowerOrderCLM (n := 3) (p := 2) (Ω := univ) (by norm_num : 1 ≤ 2) (z i)‖ ≤
      2 * T₁ * (Real.sqrt μ)⁻¹ * ‖h‖ := by
    intro i
    refine (norm_lowerOrder_vectorSelfsimilarResolventH2_le _ _ h i).trans ?_
    have h1 : μ⁻¹ ≤ (Real.sqrt μ)⁻¹ := by
      apply inv_anti₀ hsqpos
      calc Real.sqrt μ ≤ Real.sqrt μ * Real.sqrt μ := by
            nlinarith [Real.one_le_sqrt.mpr hμ1]
        _ = μ := Real.mul_self_sqrt hμ0.le
    have h2 : (2 * Real.pi)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      nlinarith [Real.pi_gt_three]
    have h3 : (2 * Real.pi)⁻¹ * (Real.sqrt μ)⁻¹ ≤ (Real.sqrt μ)⁻¹ := by
      calc (2 * Real.pi)⁻¹ * (Real.sqrt μ)⁻¹ ≤ 1 * (Real.sqrt μ)⁻¹ :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = _ := one_mul _
    calc T₁ * ((μ⁻¹ + (2 * Real.pi)⁻¹ * (Real.sqrt μ)⁻¹) * ‖h‖) ≤
          T₁ * ((2 * (Real.sqrt μ)⁻¹) * ‖h‖) := by gcongr; linarith
      _ = _ := by ring
  have hcomp : ∀ i, ‖convectionCLM w z i‖ ≤ (1 / 4) * ‖h‖ := by
    intro i
    refine (hM z i).trans ?_
    have hzi : ‖z i‖ ≤ 2 * T₂ * ‖h‖ := (PiLp.norm_apply_le z i).trans hz
    have hA : 3 * ε * ‖z i‖ ≤ 1 / 8 * ‖h‖ := by
      calc 3 * ε * ‖z i‖ ≤ 3 * ε * (2 * T₂ * ‖h‖) := by gcongr
        _ = (6 * T₂ / (48 * (T₂ + 1))) * ‖h‖ := by simp only [ε]; field_simp; ring
        _ ≤ 1 / 8 * ‖h‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [div_le_iff₀ (by positivity)]
          nlinarith
    have hB : M * ‖lowerOrderCLM (n := 3) (p := 2) (Ω := univ) (by norm_num : 1 ≤ 2) (z i)‖ ≤
        1 / 8 * ‖h‖ := by
      calc _ ≤ M * (2 * T₁ * (Real.sqrt μ)⁻¹ * ‖h‖) := by gcongr; exact hlow i
        _ = (2 * M * T₁ / Real.sqrt μ) * ‖h‖ := by field_simp
        _ ≤ 1 / 8 * ‖h‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [div_le_iff₀ hsqpos]
          nlinarith [mul_nonneg hM0 hT₁]
    linarith
  rw [projectedConvectionResolvent_apply]
  calc ‖IncompressibleFlow.leraySobolev 3 0 (convectionCLM w z)‖ ≤ ‖convectionCLM w z‖ :=
        IncompressibleFlow.norm_leraySobolev_le _
    _ ≤ 2 * ((1 / 4) * ‖h‖) := norm_le_two_mul_of_forall_norm_le _ (by positivity) hcomp
    _ = 1 / 2 * ‖h‖ := by ring

/-- For `‖K‖ ≤ 1/2` the equation `h + K h = g` has a solution. -/
theorem exists_add_projectedConvectionResolvent_eq (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)))
    {μ : ℝ} (hμ : 1 / 2 ≤ μ) (hK : ‖projectedConvectionResolvent w hμ‖ ≤ 1 / 2)
    (g : VectorH 3 0) : ∃ h : VectorH 3 0, h + projectedConvectionResolvent w hμ h = g := by
  set K := projectedConvectionResolvent w hμ
  have hlt : ‖-K‖ < 1 := by
    rw [ContinuousLinearMap.opNorm_neg]; linarith
  let u := Units.oneSub (-K) hlt
  refine ⟨(↑u⁻¹ : VectorH 3 0 →L[ℝ] VectorH 3 0) g, ?_⟩
  have h1 : (↑u : VectorH 3 0 →L[ℝ] VectorH 3 0) = 1 - (-K) := Units.val_oneSub (-K) hlt
  have h2 : (↑u : VectorH 3 0 →L[ℝ] VectorH 3 0) ((↑u⁻¹ : VectorH 3 0 →L[ℝ] VectorH 3 0) g) =
      g := congrArg (fun T : VectorH 3 0 →L[ℝ] VectorH 3 0 ↦ T g) u.mul_inv
  rw [h1] at h2
  simpa [sub_neg_eq_add] using h2

/-- The `L²` class of the base row of a solenoidal test field is divergence free. -/
theorem l2SobolevRow_testFieldH1_mem_l2Solenoidal {φ : ℝ^3 → ℝ^3} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hdiv : ∀ x, PDE.divergence φ x = 0) :
    l2SobolevRow (baseIndex 3 1) (testFieldH1 φ hφ hc) ∈ IncompressibleFlow.l2Solenoidal 3 := by
  set T := testFieldH1 φ hφ hc
  apply (IncompressibleFlow.mem_l2Solenoidal_iff_inner _).mpr
  intro ψ
  rw [IncompressibleFlow.inner_l2TestGradient_eq_weakDivergencePairing,
    IncompressibleFlow.weakDivergencePairing]
  have hrow := Lp.euclideanTuple_apply_ae (fun j ↦ wkpCoordinateCLM (baseIndex 3 1) (T j))
  simp only [domainMeasure, Measure.restrict_univ] at hrow
  have hψ := ψ.1.contDiff
  have hψc := ψ.1.hasCompactSupport
  have hcont : ∀ j : Fin 3, Continuous (PDE.partialDeriv j ψ.1.toFun) := fun j ↦
    (PDE.contDiff_top_partialDeriv (i := j) hψ).continuous
  calc ∫ x, IncompressibleFlow.weakDivergencePairingDensity
        (fun x ↦ l2SobolevRow (baseIndex 3 1) T x) ψ.1.toFun x =
      ∫ x, ∑ j, (wkpBaseCoordinateCLM (T j) : ℝ^3 → ℝ) x * PDE.partialDeriv j ψ.1.toFun x := by
        apply integral_congr_ae
        filter_upwards [hrow] with x hx
        rw [IncompressibleFlow.weakDivergencePairingDensity_eq_sum, l2SobolevRow_apply]
        apply Finset.sum_congr rfl
        intro j _
        rw [hx j]
        rfl
    _ = ∑ j, ∫ x, (wkpBaseCoordinateCLM (T j) : ℝ^3 → ℝ) x * PDE.partialDeriv j ψ.1.toFun x := by
        rw [integral_finsetSum]
        intro j _
        exact integrable_base_mul (T j) (hcont j) (hψc.partialDeriv j)
    _ = 0 := sum_integral_base_mul_partialDeriv_eq_zero T
        (divergenceCLM_testFieldH1 hφ hc hdiv) hψ hψc

/-- Pairing a vector field with a test field through the `L²` base rows. -/
theorem sum_integral_mul_eq_inner_l2SobolevRow {k : ℕ} (V : VectorH 3 k) {φ : ℝ^3 → ℝ^3}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∑ i, ∫ x, (wkpBaseCoordinateCLM (V i) : ℝ^3 → ℝ) x * φ x i =
      inner ℝ (l2SobolevRow (baseIndex 3 k) V)
        (l2SobolevRow (baseIndex 3 1) (testFieldH1 φ hφ hc)) := by
  rw [l2SobolevRow_apply, l2SobolevRow_apply, Lp.inner_euclideanTuple]
  apply Finset.sum_congr rfl
  intro i _
  have hT := testFieldH1_coord_ae hφ hc i (baseIndex 3 1)
  simp only [baseIndex_toList, iteratedPartialDeriv] at hT
  exact (inner_eq_integral_mul_of_ae (Filter.EventuallyEq.refl _ _) hT).symm

/-- The Leray projection drops out of pairings with solenoidal test fields. -/
theorem sum_integral_leraySobolev_mul (U : VectorH 3 0) {φ : ℝ^3 → ℝ^3} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hdiv : ∀ x, PDE.divergence φ x = 0) :
    ∑ i, ∫ x, (wkpBaseCoordinateCLM (IncompressibleFlow.leraySobolev 3 0 U i) : ℝ^3 → ℝ) x *
        φ x i = ∑ i, ∫ x, (wkpBaseCoordinateCLM (U i) : ℝ^3 → ℝ) x * φ x i := by
  rw [sum_integral_mul_eq_inner_l2SobolevRow _ hφ hc,
    sum_integral_mul_eq_inner_l2SobolevRow _ hφ hc,
    IncompressibleFlow.l2SobolevRow_leraySobolev, IncompressibleFlow.inner_lerayProjection_eq _ _
      (l2SobolevRow_testFieldH1_mem_l2Solenoidal hφ hc hdiv)]

/-- Polarized convection energy: `∑ⱼ (⟨wⱼ a, ∂ⱼ b⟩ + ⟨wⱼ b, ∂ⱼ a⟩) = 0` for divergence-free `w`. -/
theorem sum_inner_mulH1_partial_add_eq_zero (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)))
    (hw : divergenceCLM w = 0) (a b : H¹(ℝ^3)) :
    ∑ j, (inner ℝ (mulH1 (w j) a) (wkpCoordinateCLM (singleDerivIndex 3 j) b) +
      inner ℝ (mulH1 (w j) b) (wkpCoordinateCLM (singleDerivIndex 3 j) a)) = 0 := by
  have hab := sum_inner_mulH1_partial_self_eq_zero w hw (a + b)
  have ha := sum_inner_mulH1_partial_self_eq_zero w hw a
  have hb := sum_inner_mulH1_partial_self_eq_zero w hw b
  simp only [map_add, inner_add_left, inner_add_right] at hab
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ha, hb] at hab
  rw [Finset.sum_add_distrib]
  linarith

/-- The convection pairing after integration by parts. -/
theorem sum_integral_convectionCLM_mul (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)))
    (hw : divergenceCLM w = 0) (z : VectorH 3 2) {φ : ℝ^3 → ℝ^3} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    ∑ i, ∫ x, (wkpBaseCoordinateCLM (convectionCLM w z i) : ℝ^3 → ℝ) x * φ x i =
      -∑ i, ∑ j, ∫ x, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x *
        (wkpBaseCoordinateCLM (z i) : ℝ^3 → ℝ) x * PDE.partialDeriv j (fun y ↦ φ y i) x := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  set T := testFieldH1 φ hφ hc
  set a := lowerOrderCLM (n := 3) (p := 2) (Ω := univ) (by norm_num : 1 ≤ 2) (z i)
  have hT1 : ∀ j, (wkpCoordinateCLM (singleDerivIndex 3 j) (T i) : ℝ^3 → ℝ) =ᵐ[volume]
      fun x ↦ PDE.partialDeriv j (fun y ↦ φ y i) x := fun j ↦ testFieldH1_partial_ae hφ hc i j
  have hbT : (wkpBaseCoordinateCLM (T i) : ℝ^3 → ℝ) =ᵐ[volume] fun x ↦ φ x i :=
    testFieldH1_base_ae hφ hc i
  -- the convection pairing as a sum of inner products
  have h1 : ∫ x, (wkpBaseCoordinateCLM (convectionCLM w z i) : ℝ^3 → ℝ) x * φ x i =
      ∑ j, inner ℝ (mulH1 (w j) (T i)) (wkpCoordinateCLM (singleDerivIndex 3 j) a) := by
    rw [← inner_eq_integral_mul_of_ae (Filter.EventuallyEq.refl _ _) hbT,
      wkpBaseCoordinateCLM_convectionCLM, sum_inner]
    apply Finset.sum_congr rfl
    intro j _
    rw [← wkpBaseCoordinateCLM_partialH2]
    rw [inner_eq_integral_mul_of_ae (mulH1_ae (w j) _) hbT,
      inner_eq_integral_mul_of_ae (mulH1_ae (w j) (T i)) (Filter.EventuallyEq.refl _ _)]
    apply integral_congr_ae
    filter_upwards [hbT] with x hx
    have e1 : baseRepresentative (T i) x = φ x i := hx
    have e2 : baseRepresentative (partialH2 j (z i)) x =
        (wkpBaseCoordinateCLM (partialH2 j (z i)) : ℝ^3 → ℝ) x := rfl
    rw [e1, e2]
    ring
  have h2 : ∀ j, inner ℝ (mulH1 (w j) a) (wkpCoordinateCLM (singleDerivIndex 3 j) (T i)) =
      ∫ x, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x * (wkpBaseCoordinateCLM (z i) : ℝ^3 → ℝ) x *
        PDE.partialDeriv j (fun y ↦ φ y i) x := by
    intro j
    rw [inner_eq_integral_mul_of_ae (mulH1_ae (w j) a) (hT1 j)]
    simp only [baseRepresentative, a]
    congr 1
  have hpol := sum_inner_mulH1_partial_add_eq_zero w hw a (T i)
  rw [h1]
  have h3 : ∑ j, ∫ x, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x *
      (wkpBaseCoordinateCLM (z i) : ℝ^3 → ℝ) x * PDE.partialDeriv j (fun y ↦ φ y i) x =
      ∑ j, inner ℝ (mulH1 (w j) a) (wkpCoordinateCLM (singleDerivIndex 3 j) (T i)) :=
    Finset.sum_congr rfl fun j _ ↦ (h2 j).symm
  rw [h3]
  rw [Finset.sum_add_distrib] at hpol
  linarith

/-- Existence of `H²` solutions of the shifted linearized equation. For a divergence-free
`w ∈ H¹(ℝ³)³` and every large `μ`, each `G ∈ L²(ℝ³)³` gives a field `z ∈ H²(ℝ³)³` with
divergence-free first-order part and
`(μ + L₀) z + Π((w·∇) z) = Π G` against smooth compactly supported divergence-free fields. -/
theorem exists_vectorH2_weak_shifted_convection (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)))
    (hw : divergenceCLM w = 0) :
    ∃ μ₀, 1 ≤ μ₀ ∧ ∀ μ, μ₀ ≤ μ → ∀ G : VectorH 3 0, ∃ z : VectorH 3 2,
      divergenceCLM (vectorLower 3 1 z) = 0 ∧
      ∀ φ : ℝ^3 → ℝ^3, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∀ x, PDE.divergence φ x = 0) →
        ∑ i, ∫ x, (wkpBaseCoordinateCLM (z i) : ℝ^3 → ℝ) x *
          ((μ + 1) * φ x i + (1 / 2) * fderiv ℝ φ x x i - PDE.laplacian (fun y ↦ φ y i) x) =
        (∑ i, ∫ x, (wkpBaseCoordinateCLM (G i) : ℝ^3 → ℝ) x * φ x i) +
          ∑ i, ∑ j, ∫ x, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x *
            (wkpBaseCoordinateCLM (z i) : ℝ^3 → ℝ) x * PDE.partialDeriv j (fun y ↦ φ y i) x := by
  obtain ⟨μ₀, hμ₀, hK⟩ := exists_norm_projectedConvectionResolvent_le w
  refine ⟨μ₀, hμ₀, fun μ hμ G ↦ ?_⟩
  have hμ' : 1 / 2 ≤ μ := by linarith
  obtain ⟨h, hh⟩ := exists_add_projectedConvectionResolvent_eq w hμ' (hK μ hμ' hμ)
    (IncompressibleFlow.leraySobolev 3 0 G)
  set z := vectorSelfsimilarResolventH2 3 (by norm_num) hμ' h with hz
  have hKh : projectedConvectionResolvent w hμ' h =
      IncompressibleFlow.leraySobolev 3 0 (convectionCLM w z) :=
    projectedConvectionResolvent_apply w hμ' h
  have hh' : h = IncompressibleFlow.leraySobolev 3 0 (G - convectionCLM w z) := by
    rw [map_sub, ← hKh]
    exact eq_sub_of_add_eq hh
  have hhP : IncompressibleFlow.leraySobolev 3 0 h = h := by
    conv_lhs => rw [hh']
    rw [IncompressibleFlow.leraySobolev_idempotent, ← hh']
  refine ⟨z, ?_, ?_⟩
  · rw [divergenceCLM_apply]
    exact sum_partial_vectorLower_vectorSelfsimilarResolventH2 (by norm_num) hμ' hhP
  · intro φ hφ hc hdiv
    have h1 := sum_integral_vectorSelfsimilarResolventH2_mul_adjoint (n := 3) (by norm_num)
      (show 1 / 2 < μ by linarith) h hφ hc
    have hcoef : (μ + (((3 : ℕ) : ℝ) - 1) / 2) = μ + 1 := by norm_num
    rw [hcoef] at h1
    rw [h1, hh', sum_integral_leraySobolev_mul _ hφ hc hdiv,
      sum_integral_mul_eq_inner_l2SobolevRow _ hφ hc, map_sub, inner_sub_left,
      ← sum_integral_mul_eq_inner_l2SobolevRow _ hφ hc,
      ← sum_integral_mul_eq_inner_l2SobolevRow _ hφ hc,
      sum_integral_convectionCLM_mul w hw z hφ hc]
    ring

end NavierStokes.Stationary
