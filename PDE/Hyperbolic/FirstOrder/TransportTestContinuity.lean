/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.MollifiedTesting
public import PDE.Spaces.Sobolev.Approximation.SpatialTestDensity

/-!
# Extending transport pairings to arbitrary H¹ tests

For fixed coefficients and state, the transport pairing is a bounded linear functional
of the H¹ test. For Bochner L² states, measurability of this pairing follows by smoothing
the test and using the constructed mollified transport velocity. Strong H¹ convergence
then identifies its pointwise limit. No time continuity of the coefficient derivatives
is assumed.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace Topology

namespace PDE.Hyperbolic.FirstOrder

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation

open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ} {a b : ℝ}

local notation "D" => DerivLp n 2 univ
local notation "H" => PiLp 2 (fun _ : Fin m ↦ D)
local notation "V" => PiLp 2 (fun _ : Fin m ↦ H¹(ℝ^n))
local notation "ν" => volume.restrict (Ioc a b)

/-- The same transport pairing, regarded as a continuous linear functional of the
spatial test. Multiplication uses the L∞-by-L² continuous linear map. -/
def transportTestInTestCLM
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) (u : H) : V →L[ℝ] ℝ :=
  ∑ p, ∑ j, ∑ q, (innerSL ℝ (u q)).comp
    (((mulLpLeft ((A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))).comp
        (wkpCoordinateCLM (singleDerivIndex n j)) +
      (mulLpLeft ((A j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j))).comp
        (wkpCoordinateCLM (baseIndex n 1))).comp
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ H¹(ℝ^n)) p))

/-- The test-variable map evaluates to the canonical transport functional. -/
@[simp]
theorem transportTestInTestCLM_apply
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) (u : H) (φ : V) :
    transportTestInTestCLM A u φ = transportTestFunctional A φ u := by
  simp only [transportTestInTestCLM, sum_apply, ContinuousLinearMap.comp_apply,
    add_apply, PiLp.proj_apply, mulLpLeft_apply, innerSL_apply_apply, transportTestFunctional_apply]

/-- Each base or first-derivative coordinate of one component is bounded by the
product H¹ graph norm. -/
private theorem coordinate_norm_le (φ : V) (p : Fin m) (d : DerivIndex n 1) :
    ‖wkpCoordinateCLM d (φ p)‖ ≤ ‖φ‖ :=
  (PiLp.norm_apply_le (φ p : WkpAmbientOn n 1 2 univ) d).trans (PiLp.norm_apply_le φ p)

/-- The transport functional has a bound uniform over all spatial tests and times in
Icc. Base coefficients are continuous; the indicated spatial derivatives are bounded. -/
theorem exists_uniform_bound_transportTestFunctional
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q, ContinuousOn (fun t ↦
      (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b, ∀ j p q,
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L) :
    ∃ K ≥ 0, ∀ t ∈ Icc a b, ∀ φ : V, ‖transportTestFunctional (A t) φ‖ ≤ K * ‖φ‖ := by
  classical
  have hb (j : Fin n) (p q : Fin m) := isCompact_Icc.exists_bound_of_continuousOn (hA j p q)
  choose M hM using hb
  let R : ℝ := ∑ j, ∑ p, ∑ q, max 0 (M j p q)
  have hR : 0 ≤ R := by positivity
  have hbase (t : ℝ) (ht : t ∈ Icc a b) (j : Fin n) (p q : Fin m) :
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)‖ ≤ R := by
    apply (hM j p q t ht).trans
    apply (le_max_right 0 (M j p q)).trans
    exact (Finset.single_le_sum (fun _ _ ↦ le_max_left _ _) (Finset.mem_univ q)).trans
      ((Finset.single_le_sum (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ le_max_left _ _)
        (Finset.mem_univ p)).trans (Finset.single_le_sum (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
          Finset.sum_nonneg fun _ _ ↦ le_max_left _ _) (Finset.mem_univ j)))
  let K : ℝ := ∑ _p : Fin m, ∑ _j : Fin n, ∑ _q : Fin m, (R + L)
  refine ⟨K, by positivity, fun t ht φ ↦ ?_⟩
  apply (norm_transportTestFunctional_le (A t) φ hR L.coe_nonneg (hbase t ht) (hL t ht)).trans
  calc
    _ ≤ ∑ _p : Fin m, ∑ _j : Fin n, ∑ _q : Fin m, (R + L) * ‖φ‖ := by
      refine Finset.sum_le_sum fun p _ ↦ ?_
      refine Finset.sum_le_sum fun j _ ↦ ?_
      refine Finset.sum_le_sum fun q _ ↦ ?_
      rw [add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left
        (coordinate_norm_le φ p (singleDerivIndex n j)) hR)
        (mul_le_mul_of_nonneg_left (coordinate_norm_le φ p (baseIndex n 1)) L.coe_nonneg)
    _ = K * ‖φ‖ := by simp only [K, Finset.sum_mul]

/-- Every fixed H¹ transport test applied to a Bochner L² state is scalar L² in time.
Its measurability is obtained as the limit of the mollified transport pairings. -/
theorem memLp_transportTestFunctional (hab : a ≤ b)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b, ∀ j p q,
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L)
    {u : ℝ → H} (hu : MemLp u 2 ν) (φ : V) :
    MemLp (fun t ↦ transportTestFunctional (A t) φ (u t)) 2 ν := by
  let ε : ℕ → ℝ := fun k ↦ 1 / (k + 1 : ℝ)
  have hε (k : ℕ) : 0 < ε k := by dsimp only [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let φk (k : ℕ) : V := mollifierProductH1CLM (standardMollifier n) (hε k) (transportBaseCLM φ)
  have hφk : Tendsto φk atTop (𝓝 φ) := by
    let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ H¹(ℝ^n))
    have hc : Tendsto (fun k p ↦ φk k p) atTop (𝓝 (fun p ↦ φ p)) := by
      refine tendsto_pi_nhds.mpr fun p ↦ ?_
      simpa only [φk, mollifierProductH1CLM_apply, transportBaseCLM_apply] using
        tendsto_mollifierH1CLM_base (standardMollifier n) ε hε hε0 (φ p)
    exact e.symm.continuous.continuousAt.tendsto.comp hc
  have hmeas (k : ℕ) : AEStronglyMeasurable
      (fun t ↦ transportTestFunctional (A t) (φk k) (u t)) ν := by
    have h := (innerSL ℝ (transportBaseCLM φ)).comp_memLp'
      (memLp_mollifiedTransportDrift (standardMollifier n) (hε k) hab A hA L hL hu)
    apply h.aestronglyMeasurable.congr
    filter_upwards with t
    change inner ℝ (transportBaseCLM φ)
      (mollifiedTransportDrift (standardMollifier n) (hε k) (A t) (u t)) = _
    rw [real_inner_comm, inner_mollifiedTransportDrift]
  have hlim : ∀ᵐ t ∂ν, Tendsto (fun k ↦ transportTestFunctional (A t) (φk k) (u t)) atTop
        (𝓝 (transportTestFunctional (A t) φ (u t))) := by
    filter_upwards with t
    convert (transportTestInTestCLM (A t) (u t)).continuous.continuousAt.tendsto.comp hφk using 1
    · funext k
      exact (transportTestInTestCLM_apply (A t) (u t) (φk k)).symm
    · rw [transportTestInTestCLM_apply]
  have hmeas' := aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim
  obtain ⟨K, _hK, hbound⟩ := exists_uniform_bound_transportTestFunctional A hA L hL
  refine hu.of_le_mul (c := K * ‖φ‖) hmeas' ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact ((transportTestFunctional (A t) φ).le_opNorm (u t)).trans
    (mul_le_mul_of_nonneg_right (hbound t (Ioc_subset_Icc_self ht) φ) (norm_nonneg _))

end PDE.Hyperbolic.FirstOrder
