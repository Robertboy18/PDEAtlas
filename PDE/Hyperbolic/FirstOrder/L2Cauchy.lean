/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.H1Trajectories
public import PDE.Analysis.Evolution.Integrated.TimeTestFunction
import PDE.Spaces.Sobolev.Approximation.Mollification.H1DataApproximation
import PDE.Analysis.Evolution.Compactness.UniformCompletion
import PDE.Analysis.Evolution.Compactness.WeakUniformLimit
import PDE.Analysis.Evolution.Compactness.WeakLimitTesting

/-!
# The symmetric Cauchy problem with L2 initial data and forcing

Spatial mollification approximates the L2 initial state and Bochner L2 load by H1 data.
The symmetric H1 existence theorem solves the corresponding transport problems. The L2
difference estimate makes their continuous representatives Cauchy in the uniform norm
on the closed time interval.

The limit has the prescribed initial value and the L2 energy bound with exponent `C + 1`.
Its weak equation is tested against every fixed H1 spatial vector and every
`TimeTest a b`, including the initial boundary term. Spatial integration by parts uses the
coefficient derivatives. Measurability of those tested terms follows from the
approximant equations and their pointwise limit, without assuming time continuity of the
coefficient derivatives.

The uniform spatial-gradient bound on the coefficients is inherited from the H1
construction.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open Filter MeasureTheory Set
open scoped BoundedContinuousFunction ENNReal InnerProductSpace Topology

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation

open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ} {a b : ℝ}

local notation "D" => DerivLp n 2 univ
local notation "H" => PiLp 2 (fun _ : Fin m ↦ D)
local notation "V" => PiLp 2 (fun _ : Fin m ↦ H¹(ℝ^n))
local notation "ν" => volume.restrict (Ioc a b)

/-- Construct a continuous L2 solution of the original symmetric transport system from
arbitrary L2 data and Bochner L2 forcing. Coefficient values are continuous only on the
closed time interval; their spatial derivatives need only satisfy the displayed uniform
bounds. The weak equation includes the initial trace and the divergence term.

The construction uses H1 data density and uniform L2 completion. -/
theorem exists_symmetric_cauchy_l2 (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a < b)
    (hsym : ∀ t ∈ Icc a b, ∀ j p q, (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) =
      (A t j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hdiv : ∀ t ∈ Icc a b, coefficientDerivativeBound (A t) ≤ C)
    (hgrad : ∀ t ∈ Icc a b, coefficientGradientBound (A t) ≤ L) (x : H) (f : Lp H 2 ν) :
    ∃ u : ℝ → H,
      ContinuousOn u (Icc a b) ∧
      u a = x ∧
      (∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤
        (‖x‖ ^ 2 + ‖f‖ ^ 2) * Real.exp ((C + 1) * (t - a))) ∧
      ∀ (φ : V) (τ : TimeTest a b),
        Integrable (fun t ↦ transportTestFunctional (A t) φ (u t) * τ.toFun t) ν ∧
        -(∫ t in Ioc a b, ⟪u t, transportBaseCLM φ⟫_ℝ * τ.derivFun t) =
          (∫ t in Ioc a b, transportTestFunctional (A t) φ (u t) * τ.toFun t) +
            (∫ t in Ioc a b, ⟪f t, transportBaseCLM φ⟫_ℝ * τ.toFun t) +
              ⟪x, transportBaseCLM φ⟫_ℝ * τ.toFun a := by
  classical
  let J : V →L[ℝ] H := transportBaseCLM
  let ε : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := by positivity
  obtain ⟨X, F, hX, hF, _⟩ :=
    exists_h1_product_initial_forcing_approximation ν (standardMollifier n) ε hε
      tendsto_one_div_add_atTop_nhds_zero_nat x f
  change Tendsto (fun k ↦ J (X k)) atTop (𝓝 x) at hX
  change Tendsto (fun k ↦ J.compLpL 2 ν (F k)) atTop (𝓝 f) at hF
  let fseq : ℕ → Lp H 2 ν := fun k ↦ J.compLpL 2 ν (F k)
  choose U z g hz hzU hg hzg heq hzX using fun k ↦
    exists_h1_transport_trajectory A hA hab hsym hC hL hdiv hgrad (F k) (X k)
  have hzeq (k : ℕ) : ∀ᵐ t ∂ν,
      HasDerivAt (z k) (transportDrift (A t) (U k t) + fseq k t) t := by
    filter_upwards [hzg k, heq k] with t hzt hgt
    rwa [hgt] at hzt
  have hzcont (k : ℕ) : ContinuousOn (z k) (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using (hz k).continuousOn
  let Z : ℕ → (Icc a b) →ᵇ H := fun k ↦
    BoundedContinuousFunction.mkOfCompact ⟨fun t ↦ z k t, (hzcont k).domRestrict⟩
  have hstab (i j : ℕ) : ∀ t ∈ Icc a b, ‖z i t - z j t‖ ^ 2 ≤
        (‖J (X i) - J (X j)‖ ^ 2 + ‖fseq i - fseq j‖ ^ 2) *
          Real.exp ((C + 1) * (t - a)) := by
    simpa only [hzX] using h1_transport_trajectory_stability A hab.le hsym hC hdiv
      (fseq i) (fseq j) (hz i) (hz j) (hzU i) (hzU j) (hzeq i) (hzeq j)
  have hstable (i j : ℕ) (t : Icc a b) : dist (Z i t) (Z j t) ^ 2 ≤ Real.exp ((C + 1) * (b - a)) *
        (dist (J (X i)) (J (X j)) ^ 2 + dist (fseq i) (fseq j) ^ 2) := by
    simp only [dist_eq_norm]
    change ‖z i t - z j t‖ ^ 2 ≤ _
    apply (hstab i j t t.property).trans
    rw [mul_comm (Real.exp _)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (sub_le_sub_right t.property.2 a) (by positivity))
  obtain ⟨v, hv, hv₀⟩ := exists_uniform_limit_with_initial_of_sq_stability
    hX hF (Real.exp_pos _).le hstable (⟨a, left_mem_Icc.mpr hab.le⟩ : Icc a b) (fun k ↦ hzX k)
  let u : ℝ → H := fun t ↦ if ht : t ∈ Icc a b then v ⟨t, ht⟩ else 0
  have huval (t : ℝ) (ht : t ∈ Icc a b) : u t = v ⟨t, ht⟩ := dite_eq_left ht
  have hucont : ContinuousOn u (Icc a b) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact v.continuous.congr fun t ↦ (huval t t.property).symm
  have hinit : u a = x := (huval a (left_mem_Icc.mpr hab.le)).trans hv₀
  have hlim (t : ℝ) (ht : t ∈ Icc a b) :
      Tendsto (fun k ↦ z k t) atTop (𝓝 (u t)) := by
    rw [huval t ht]
    exact ((BoundedContinuousFunction.lipschitz_eval_const
      (⟨t, ht⟩ : Icc a b)).continuous.continuousAt.tendsto).comp hv
  have henergy (k : ℕ) (t : ℝ) (ht : t ∈ Icc a b) : ‖z k t‖ ^ 2 ≤
        (‖J (X k)‖ ^ 2 + ‖fseq k‖ ^ 2) * Real.exp ((C + 1) * (t - a)) := by
    simpa only [hzX] using h1_transport_trajectory_energy A hab.le hsym hC hdiv
        (fseq k) (hz k) (hzU k) (hzeq k) t ht
  have hlimitEnergy (t : ℝ) (ht : t ∈ Icc a b) :
      ‖u t‖ ^ 2 ≤ (‖x‖ ^ 2 + ‖f‖ ^ 2) * Real.exp ((C + 1) * (t - a)) :=
    le_of_tendsto_of_tendsto ((hlim t ht).norm.pow 2)
      (((hX.norm.pow 2).add (hF.norm.pow 2)).mul tendsto_const_nhds)
      (Eventually.of_forall fun k ↦ henergy k t ht)
  obtain ⟨M, _, hM⟩ := hv.cauchySeq.isBounded_range.exists_pos_norm_le
  have hbound (k : ℕ) : ∀ᵐ t ∂ν, ‖z k t‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ((Z k).norm_coe_le_norm ⟨t, ht.1.le, ht.2⟩).trans (hM (Z k) (mem_range_self k))
  have hlimAE : ∀ᵐ t ∂ν, Tendsto (fun k ↦ z k t) atTop (𝓝 (u t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using hlim t ⟨ht.1.le, ht.2⟩
  refine ⟨u, hucont, hinit, hlimitEnergy, fun φ τ ↦ ?_⟩
  let B : ℝ → H →L[ℝ] ℝ := fun t ↦ transportTestFunctional (A t) φ
  have hweak (k : ℕ) : AEStronglyMeasurable (fun t ↦ B t (z k t)) ν ∧
        Integrable (fun t ↦ B t (z k t) * τ.toFun t) ν ∧
        -(∫ t in Ioc a b, ⟪z k t, J φ⟫_ℝ * τ.derivFun t) =
          (∫ t in Ioc a b, B t (z k t) * τ.toFun t) +
            (∫ t in Ioc a b, ⟪fseq k t, J φ⟫_ℝ * τ.toFun t) +
              ⟪z k a, J φ⟫_ℝ * τ.toFun a := by
    apply weak_identity_of_ac_velocity hab.le (J φ) B (hz k) (hg k) (Lp.memLp (fseq k)) (hzg k) _ τ
    filter_upwards [heq k, hzU k] with t hgt hut
    rw [hgt, inner_add_left, inner_transportDrift_eq, hut]
  obtain ⟨K, hK, hKB⟩ := exists_bound_transportTestFunctional A hA hC hdiv φ
  have hBK : ∀ᵐ t ∂ν, ‖B t‖ ≤ K := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using hKB t ⟨ht.1.le, ht.2⟩
  obtain ⟨hBi, hBtendsto⟩ := integrable_and_tendsto_integral_linear_tests B hK
    hBK hbound (fun k ↦ (hweak k).1) hlimAE (τ.memLp.integrable (by norm_num))
  have htime : Tendsto (fun k ↦ ∫ t in Ioc a b, ⟪z k t, J φ⟫_ℝ * τ.derivFun t) atTop
        (𝓝 (∫ t in Ioc a b, ⟪u t, J φ⟫_ℝ * τ.derivFun t)) := by
    have hzmeas (k : ℕ) : AEStronglyMeasurable (fun t ↦ (innerSL ℝ (J φ)) (z k t)) ν :=
      (innerSL ℝ (J φ)).continuous.comp_aestronglyMeasurable
        (memLp_restrict_Ioc_of_continuousOn (hzcont k)).aestronglyMeasurable
    have hconstant : ∀ᵐ t ∂ν, ‖innerSL ℝ (J φ)‖ ≤ ‖innerSL ℝ (J φ)‖ :=
      Eventually.of_forall fun _ ↦ le_rfl
    have h := (integrable_and_tendsto_integral_linear_tests
      (fun _ ↦ innerSL ℝ (J φ)) (norm_nonneg _) hconstant hbound hzmeas hlimAE
        (τ.derivMemLp.integrable (by norm_num))).2
    simpa only [innerSL_apply_apply, real_inner_comm (J φ)] using h
  have hforcing := tendsto_forcing_timeTest hF (J φ) τ
  have hinitial : Tendsto (fun k ↦ ⟪z k a, J φ⟫_ℝ * τ.toFun a) atTop
      (𝓝 (⟪x, J φ⟫_ℝ * τ.toFun a)) := by
    simpa only [hzX] using (hX.inner (tendsto_const_nhds (x := J φ))).mul
        (tendsto_const_nhds (x := τ.toFun a))
  refine ⟨hBi, ?_⟩
  have hclosed := limit_integrated_initial_identity
    (timeTerm := fun k ↦ ∫ t in Ioc a b, ⟪z k t, J φ⟫_ℝ * τ.derivFun t)
    (formTerm := fun k ↦ -(∫ t in Ioc a b, B t (z k t) * τ.toFun t))
    (forcingTerm := fun k ↦ ∫ t in Ioc a b, ⟪fseq k t, J φ⟫_ℝ * τ.toFun t)
    (initialTerm := fun k ↦ ⟪z k a, J φ⟫_ℝ * τ.toFun a)
    (fun k ↦ by linarith only [(hweak k).2.2]) htime hBtendsto.neg hforcing hinitial
  linarith only [hclosed]

end PDE.Hyperbolic.FirstOrder
