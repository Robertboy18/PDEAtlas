/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.MollifiedWeakEvolution
public import PDE.Hyperbolic.FirstOrder.TransportCommutator
import PDE.Analysis.Evolution.Time.MovingTests
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Signed energy of weak transport solutions

Spatial mollification permits testing an L² transport equation by its own state.
The commutator tends to zero in Bochner L², while symmetric integration by parts
leaves the coefficient divergence. Thus the energy identity needs no
spatial derivative of the unmollified state. Weak continuity specifies its endpoint
traces: scalar pairings identify the absolutely continuous mollified representative
at every time.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace Topology

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace
  SobolevSpace.Approximation

open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ} {a b : ℝ}

local notation "D" => DerivLp n 2 univ
local notation "H" => PiLp 2 (fun _ : Fin m ↦ D)
local notation "V" => PiLp 2 (fun _ : Fin m ↦ H¹(ℝ^n))
local notation "ν" => volume.restrict (Ioc a b)

/-- The signed divergence production in the squared L² energy of
`u_t = -Aʲ ∂ⱼu + f`. The derivatives are the weak coefficient coordinates. -/
def transportDivergencePairing
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) (u : H) : ℝ :=
  ∑ j, ∑ p, ∑ q,
    ⟪((A j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) • u q, u p⟫_ℝ

/-- Symmetry removes all derivatives of the H¹ state from the energy pairing. -/
theorem two_inner_transportDrift (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hsym : ∀ j p q, (A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) =
      (A j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    (U : V) :
    2 * ⟪transportDrift A U, transportBaseCLM U⟫_ℝ =
      transportDivergencePairing A (transportBaseCLM U) := by
  classical
  have h (j : Fin n) := symmetric_matrix_transport_energy_identity (A j) (hsym j) j (fun p ↦ U p)
  dsimp only at h
  have he : ⟪transportDrift A U, transportBaseCLM U⟫_ℝ =
        (1 / 2 : ℝ) * transportDivergencePairing A (transportBaseCLM U) := by
    simp only [transportDrift, PiLp.inner_apply, inner_neg_left, sum_inner, Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    change (∑ j : Fin n, -(∑ p : Fin m, ∑ q : Fin m,
      ⟪((A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
        wkpCoordinateCLM (singleDerivIndex n j) (U q),
        wkpCoordinateCLM (baseIndex n 1) (U p)⟫_ℝ)) = _
    simp only [wkpCoordinateCLM_apply]
    simp_rw [h]
    simp only [transportDivergencePairing, ← Finset.mul_sum,
      transportBaseCLM_apply, wkpCoordinateCLM_apply]
  linarith only [he]

/-- Divergence production is continuous on L² at each fixed coefficient field. -/
theorem continuous_transportDivergencePairing
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) :
    Continuous (transportDivergencePairing A) := by
  unfold transportDivergencePairing
  exact continuous_finsetSum _ fun j _ ↦ continuous_finsetSum _ fun p _ ↦
    continuous_finsetSum _ fun q _ ↦ ((mulLpLeft _).continuous.comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ D) q).continuous).inner
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ D) p).continuous

private theorem integrable_inner_of_memLp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u v : ℝ → E} (hu : MemLp u 2 ν) (hv : MemLp v 2 ν) :
    Integrable (fun t ↦ ⟪u t, v t⟫_ℝ) ν :=
  (hu.norm.integrable_mul hv.norm).mono' (hu.aestronglyMeasurable.inner hv.aestronglyMeasurable)
    (Eventually.of_forall fun t ↦ norm_inner_le_norm (u t) (v t))

/-- Bochner L² states give integrable divergence production with bounded weak
coefficient derivatives. -/
theorem integrable_transportDivergencePairing (hab : a ≤ b)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b, ∀ j p q,
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L)
    {u : ℝ → H} (hu : MemLp u 2 ν) :
    Integrable (fun t ↦ transportDivergencePairing (A t) (u t)) ν := by
  classical
  have hp (p : Fin m) : MemLp (fun t ↦ u t p) 2 ν :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ D) p).comp_memLp' hu
  exact integrable_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun p _ ↦
    integrable_finsetSum _ fun q _ ↦ integrable_inner_of_memLp
      (memLp_coefficientDerivative_mul hab (fun t ↦ A t j p q) (hA j p q)
        j L (fun t ht ↦ hL t ht j p q) (hp q)) (hp p)

private def energyMollifier (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) : H →L[ℝ] H :=
  transportBaseCLM.comp (mollifierProductH1CLM μ hε)

private theorem energyMollifier_apply (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (u : H) (p : Fin m) :
    energyMollifier μ hε u p = mollifierRowCLM μ hε (u p) :=
  mollifierH1CLM_base μ hε (u p)

private theorem norm_energyMollifier_le (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (u : H) :
    ‖energyMollifier μ hε u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [PiLp.norm_sq_eq_of_L2, energyMollifier_apply]
  exact Finset.sum_le_sum fun p _ ↦ (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (norm_mollifierRowCLM_apply_le μ hε (u p))

private theorem tendsto_energyMollifier (μ : Mollifier n) (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k)
    (hε0 : Tendsto ε atTop (𝓝 0)) (u : H) :
    Tendsto (fun k ↦ energyMollifier μ (hε k) u) atTop (𝓝 u) := by
  have h := ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ D)).symm.continuous.tendsto
    (fun p ↦ u p)).comp (tendsto_pi_nhds.mpr fun p ↦ tendsto_mollifierRowCLM μ ε hε hε0 (u p))
  rw [show (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ D)).symm (fun p ↦ u p) = u from
    PiLp.ext fun p ↦ rfl] at h
  exact h.congr fun k ↦ PiLp.ext fun p ↦ (energyMollifier_apply μ (hε k) u p).symm

private theorem norm_transportDivergencePairing_le
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) (u : H) :
    ‖transportDivergencePairing A u‖ ≤ (∑ j, ∑ p, ∑ q, ‖(A j p q : WkpAmbientOn n 1 ∞ univ)
      (singleDerivIndex n j)‖) * ‖u‖ ^ 2 := by
  classical
  unfold transportDivergencePairing
  calc
    _ ≤ ∑ j, ‖∑ p, ∑ q, ⟪((A j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) •
          u q, u p⟫_ℝ‖ := norm_sum_le _ _
    _ ≤ ∑ j, (∑ p, ∑ q,
        ‖(A j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖) * ‖u‖ ^ 2 := by
      refine Finset.sum_le_sum fun j _ ↦ ?_
      simpa only [Real.norm_eq_abs, PiLp.norm_sq_eq_of_L2] using Lp.abs_sum_inner_lpSMul_le
          (fun p q ↦ (A j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) (fun p ↦ u p)
    _ = _ := (Finset.sum_mul ..).symm

private theorem mollified_energy_sub_eq_integral {ε : ℝ} (hε : 0 < ε)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a < b)
    (hsym : ∀ t ∈ Icc a b, ∀ j p q, (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) =
      (A t j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b, ∀ j p q,
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L)
    (u f R : Lp H 2 ν) (U : ℝ → H) (hU : ∀ ℓ : H →L[ℝ] ℝ, ContinuousOn (fun t ↦ ℓ (U t)) (Icc a b))
    (hUae : U =ᵐ[ν] fun t ↦ u t)
    (hweak : ∀ (φ : V) (τ : TimeTest a b), -(∫ t, ⟪u t, transportBaseCLM φ⟫_ℝ * τ.derivFun t ∂ν) =
      (∫ t, transportTestFunctional (A t) φ (u t) * τ.toFun t ∂ν) +
      (∫ t, ⟪f t, transportBaseCLM φ⟫_ℝ * τ.toFun t ∂ν) + ⟪U a, transportBaseCLM φ⟫_ℝ * τ.toFun a)
    (hR : (R : ℝ → H) =ᵐ[ν] fun t ↦ transportCommutator (standardMollifier n) hε (A t) (u t)) :
    let J : H →L[ℝ] H := energyMollifier (standardMollifier n) hε; ‖J (U b)‖ ^ 2 - ‖J (U a)‖ ^ 2 =
      (∫ t, transportDivergencePairing (A t) (J (u t)) ∂ν) + 2 * ⟪R + J.compLpL 2 ν f,
      J.compLpL 2 ν u⟫_ℝ := by
  classical
  intro J
  let S : H →L[ℝ] V := mollifierProductH1CLM (standardMollifier n) hε
  let F : Lp H 2 ν := J.compLpL 2 ν f
  let v : Lp H 2 ν := J.compLpL 2 ν u
  obtain ⟨w, hwcont, hwae, _hwinit, hwac, hwderiv⟩ :=
    exists_mollified_absolutelyContinuous_of_weak_equation hε A hA hab L hL u f (U a) hweak
  have hwU : w =ᵐ[ν] fun t ↦ J (U t) := by
    filter_upwards [hwae, hUae] with t ht hUt
    rw [hUt]
    exact ht
  have hwEq : EqOn w (fun t ↦ J (U t)) (Icc a b) := by
    intro t ht
    refine ext_inner_left ℝ fun z ↦ ?_
    have hscalar : EqOn (fun s ↦ ⟪z, w s⟫_ℝ) (fun s ↦ ⟪z, J (U s)⟫_ℝ) (Icc a b) :=
      Measure.eqOn_Icc_of_ae_eq volume hab.ne
        (by
          rw [← restrict_Ioc_eq_restrict_Icc]
          exact hwU.mono fun s hs ↦ congrArg (fun y ↦ ⟪z, y⟫_ℝ) hs)
        (continuousOn_const.inner hwcont) (hU ((innerSL ℝ z).comp J))
    exact hscalar ht
  let g : ℝ → H := fun t ↦ mollifiedTransportDrift (standardMollifier n) hε (A t) (u t) + J (f t)
  have hg : ∀ᵐ t ∂volume.restrict (uIoc a b), HasDerivAt w (g t) t := by
    simpa only [uIoc_of_le hab.le, g, J, energyMollifier] using hwderiv
  have he := integrated_inner_product_of_ae_hasDerivAt hwac hwac hg hg
  rw [hwEq (right_mem_Icc.mpr hab.le), hwEq (left_mem_Icc.mpr hab.le),
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    intervalIntegral.integral_of_le hab.le] at he
  have hpair : (fun t ↦ ⟪w t, g t⟫_ℝ + ⟪g t, w t⟫_ℝ) =ᵐ[ν]
        (fun t ↦ transportDivergencePairing (A t) (J (u t)) +
          2 * ⟪(R + F) t, v t⟫_ℝ) := by
    filter_upwards [hwae, hR, J.coeFn_compLpL f, J.coeFn_compLpL u,
      Lp.coeFn_add R F, ae_restrict_mem measurableSet_Ioc] with t hwt hRt hFt hvt hsum ht
    rw [hsum, Pi.add_apply, hFt, hvt, hRt, hwt, real_inner_comm]
    rw [← two_mul]
    change 2 * ⟪mollifiedTransportDrift (standardMollifier n) hε (A t) (u t) +
        J (f t), J (u t)⟫_ℝ = _
    rw [mollifiedTransportDrift_eq_transportDrift_add]
    have hsp := two_inner_transportDrift (A t) (hsym t (Ioc_subset_Icc_self ht)) (S (u t))
    change 2 * ⟪transportDrift (A t) (S (u t)), J (u t)⟫_ℝ =
      transportDivergencePairing (A t) (J (u t)) at hsp
    simp only [inner_add_left]
    linarith only [hsp]
  have hQ := integrable_transportDivergencePairing hab.le A hA L hL (J.comp_memLp u)
  simp only [Function.comp_def] at hQ
  calc
    _ = ∫ t, (transportDivergencePairing (A t) (J (u t)) +
        2 * ⟪(R + F) t, v t⟫_ℝ) ∂ν := he.trans (integral_congr_ae hpair)
    _ = _ := (integral_add hQ ((L2.integrable_inner (R + F) v).const_mul 2)).trans
      (by rw [integral_const_mul, ← L2.inner_def])

/-- The exact signed energy identity for an L² weak transport solution.
Only weak continuity of the L² representative supplies endpoint values. The weak equation supplies
the drift. All first coefficient derivatives are bounded uniformly on the finite time interval, and
coefficient values are continuous in L∞. -/
theorem energy_sub_eq_integral_of_transport_weak_equation_of_weaklyContinuous
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a < b)
    (hsym : ∀ t ∈ Icc a b, ∀ j p q, (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) =
      (A t j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b, ∀ j p q,
      (∑ l : Fin n, ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)‖) ≤ L)
    (u f : Lp H 2 ν) (U : ℝ → H) (hU : ∀ ℓ : H →L[ℝ] ℝ, ContinuousOn (fun t ↦ ℓ (U t)) (Icc a b))
    (hUae : U =ᵐ[ν] fun t ↦ u t)
    (hweak : ∀ (φ : V) (τ : TimeTest a b), -(∫ t, ⟪u t, transportBaseCLM φ⟫_ℝ * τ.derivFun t ∂ν) =
      (∫ t, transportTestFunctional (A t) φ (u t) * τ.toFun t ∂ν) +
      (∫ t, ⟪f t, transportBaseCLM φ⟫_ℝ * τ.toFun t ∂ν) + ⟪U a, transportBaseCLM φ⟫_ℝ * τ.toFun a) :
    ‖U b‖ ^ 2 - ‖U a‖ ^ 2 = (∫ t, transportDivergencePairing (A t) (u t) ∂ν) + 2 * ⟪f, u⟫_ℝ := by
  classical
  let ε : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := by positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let J (k : ℕ) : H →L[ℝ] H := energyMollifier (standardMollifier n) (hε k)
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) (j : Fin n) (p q : Fin m) :
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L :=
    (Finset.single_le_sum (fun l _ ↦ norm_nonneg
      ((A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)))
      (Finset.mem_univ j)).trans (hL t ht j p q)
  obtain ⟨R, hR, hRlim⟩ := exists_transportCommutatorLp_sequence (standardMollifier n) ε hε hε0
      hab.le A hA L hL u
  have hJ (z : H) : Tendsto (fun k ↦ J k z) atTop (𝓝 z) :=
    tendsto_energyMollifier (standardMollifier n) ε hε hε0 z
  have hJLp (z : Lp H 2 ν) : Tendsto (fun k ↦ (J k).compLpL 2 ν z) atTop (𝓝 z) :=
    tendsto_compLpL_of_tendsto_strongly J 1 zero_le_one
      (fun k z ↦ by simpa only [one_mul] using
        norm_energyMollifier_le (standardMollifier n) (hε k) z) hJ z
  have hforce : Tendsto (fun k ↦ 2 * ⟪R k + (J k).compLpL 2 ν f, (J k).compLpL 2 ν u⟫_ℝ)
        atTop (𝓝 (2 * ⟪f, u⟫_ℝ)) := by
    simpa only [zero_add] using (tendsto_const_nhds.mul ((hRlim.add (hJLp f)).inner (hJLp u)))
  let C : ℝ := ∑ _j : Fin n, ∑ _p : Fin m, ∑ _q : Fin m, (L : ℝ)
  have hC : 0 ≤ C := by positivity
  have hbound (t : ℝ) (ht : t ∈ Icc a b) (z : H) :
      ‖transportDivergencePairing (A t) z‖ ≤ C * ‖z‖ ^ 2 := by
    apply (norm_transportDivergencePairing_le (A t) z).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun p _ ↦
      Finset.sum_le_sum fun q _ ↦ hderiv t ht j p q
  have hQlim : Tendsto (fun k ↦ ∫ t, transportDivergencePairing (A t) (J k (u t)) ∂ν)
        atTop (𝓝 (∫ t, transportDivergencePairing (A t) (u t) ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun t ↦ C * ‖u t‖ ^ 2)
    · exact fun k ↦ (integrable_transportDivergencePairing hab.le A hA L hderiv
        ((J k).comp_memLp u)).aestronglyMeasurable
    · exact ((Lp.memLp u).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).const_mul C
    · intro k
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (hbound t (Ioc_subset_Icc_self ht) _).trans (mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
            (norm_energyMollifier_le (standardMollifier n) (hε k) (u t))) hC)
    · exact Eventually.of_forall fun t ↦
        (continuous_transportDivergencePairing (A t)).continuousAt.tendsto.comp (hJ (u t))
  have he (k : ℕ) := mollified_energy_sub_eq_integral (hε k) A hA hab hsym L hderiv
    u f (R k) U hU hUae hweak (hR k)
  exact tendsto_nhds_unique ((hJ (U b)).norm.pow 2 |>.sub ((hJ (U a)).norm.pow 2))
    ((hQlim.add hforce).congr fun k ↦ (he k).symm)

/-- The representative-level energy identity for a weakly continuous L² path.
Bochner L² integrability and the exact weak equation suffice; endpoint norm
continuity and an energy identity are not hypotheses. -/
theorem energy_sub_eq_integral_of_weaklyContinuous_transport_weak_equation
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a < b)
    (hsym : ∀ t ∈ Icc a b, ∀ j p q, (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) =
      (A t j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b, ∀ j p q,
      (∑ l : Fin n, ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)‖) ≤ L)
    (U F : ℝ → H) (hU : ∀ ℓ : H →L[ℝ] ℝ, ContinuousOn (fun t ↦ ℓ (U t)) (Icc a b))
    (hU2 : MemLp U 2 ν) (hF : MemLp F 2 ν)
    (hweak : ∀ (φ : V) (τ : TimeTest a b), -(∫ t, ⟪U t, transportBaseCLM φ⟫_ℝ * τ.derivFun t ∂ν) =
      (∫ t, transportTestFunctional (A t) φ (U t) * τ.toFun t ∂ν) +
      (∫ t, ⟪F t, transportBaseCLM φ⟫_ℝ * τ.toFun t ∂ν) + ⟪U a, transportBaseCLM φ⟫_ℝ * τ.toFun a) :
    ‖U b‖ ^ 2 - ‖U a‖ ^ 2 = ∫ t, transportDivergencePairing (A t) (U t) + 2 * ⟪F t, U t⟫_ℝ ∂ν := by
  let u := hU2.toLp U
  let f := hF.toLp F
  have hu : (fun t ↦ u t) =ᵐ[ν] U := hU2.coeFn_toLp
  have hf : (fun t ↦ f t) =ᵐ[ν] F := hF.coeFn_toLp
  have hw (φ : V) (τ : TimeTest a b) : -(∫ t, ⟪u t, transportBaseCLM φ⟫_ℝ * τ.derivFun t ∂ν) =
        (∫ t, transportTestFunctional (A t) φ (u t) * τ.toFun t ∂ν) +
          (∫ t, ⟪f t, transportBaseCLM φ⟫_ℝ * τ.toFun t ∂ν) +
            ⟪U a, transportBaseCLM φ⟫_ℝ * τ.toFun a := by
    convert hweak φ τ using 2
    · exact integral_congr_ae (hu.mono fun t ht ↦ by dsimp only at ht ⊢; rw [ht])
    · congr 1
      · exact integral_congr_ae (hu.mono fun t ht ↦ by dsimp only at ht ⊢; rw [ht])
      · exact integral_congr_ae (hf.mono fun t ht ↦ by dsimp only at ht ⊢; rw [ht])
  have he := energy_sub_eq_integral_of_transport_weak_equation_of_weaklyContinuous
    A hA hab hsym L hL u f U hU hu.symm hw
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) (j : Fin n) (p q : Fin m) :
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L :=
    (Finset.single_le_sum (fun l _ ↦ norm_nonneg
      ((A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)))
      (Finset.mem_univ j)).trans (hL t ht j p q)
  rw [L2.inner_def] at he
  calc
    _ = (∫ t, transportDivergencePairing (A t) (U t) ∂ν) +
        2 * ∫ t, ⟪F t, U t⟫_ℝ ∂ν := he.trans (by
      congr 1
      · exact integral_congr_ae (hu.mono fun t ht ↦ by dsimp only at ht ⊢; rw [ht])
      · congr 1
        exact integral_congr_ae (by filter_upwards [hu, hf] with t hut hft; rw [hut, hft]))
    _ = _ := by
      rw [integral_add (integrable_transportDivergencePairing hab.le A hA L hderiv hU2)
        ((integrable_inner_of_memLp hF hU2).const_mul 2), integral_const_mul]

end PDE.Hyperbolic.FirstOrder
