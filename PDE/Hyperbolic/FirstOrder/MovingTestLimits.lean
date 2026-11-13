/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.TransportTestContinuity
public import PDE.Spaces.Sobolev.Approximation.Mollification.H1Contraction

/-!
# Removing spatial mollification from moving tests

A continuous H¹-valued test has a bounded graph norm on a compact time interval.
Mollification preserves that bound and converges in H¹ at each time. These facts give
dominated convergence for both the L² pairing and the transport pairing with a Bochner
L² state.

The transport integrands are measurable by their mollified-velocity identity, not by
any measurability of a chosen representative of the weak coefficient derivatives.
Continuity is required only for the coefficient base rows;
the indicated weak spatial derivative rows satisfy a uniform bound.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace NNReal Topology

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation

open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ} {a b : ℝ}

local notation "D" => DerivLp n 2 univ
local notation "H" => PiLp 2 (fun _ : Fin m ↦ D)
local notation "V" => PiLp 2 (fun _ : Fin m ↦ H¹(ℝ^n))
local notation "ν" => volume.restrict (Ioc a b)

/-- The integral L² pairing with a continuous H¹ moving test is the limit of its
spatially mollified pairings. Only Bochner L² regularity is required of the state. -/
theorem tendsto_integral_inner_mollified_test (μ : Mollifier n) (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k)
    (hε0 : Tendsto ε atTop (𝓝 0)) {u : ℝ → H} (hu : MemLp u 2 ν) (φ : ℝ → V)
    (hφ : ContinuousOn φ (Icc a b)) :
    Tendsto (fun k ↦ ∫ t, inner ℝ (u t)
      (transportBaseCLM (mollifierProductH1CLM μ (hε k) (transportBaseCLM (φ t)))) ∂ν)
      atTop (𝓝 (∫ t, inner ℝ (u t) (transportBaseCLM (φ t)) ∂ν)) := by
  let B : V →L[ℝ] H := transportBaseCLM
  let S (k : ℕ) : H →L[ℝ] V := mollifierProductH1CLM μ (hε k)
  let φk (k : ℕ) (t : ℝ) : V := S k (B (φ t))
  have hnorm (k : ℕ) (t : ℝ) : ‖φk k t‖ ≤ ‖φ t‖ := norm_mollifierProductH1CLM_base_le μ (hε k) (φ t)
  have hlim (t : ℝ) : Tendsto (fun k ↦ φk k t) atTop (𝓝 (φ t)) :=
    tendsto_mollifierProductH1CLM_base μ ε hε hε0 (φ t)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
  let C : ℝ := max M 0
  have hbound (k : ℕ) (t : ℝ) (ht : t ∈ Icc a b) : ‖φk k t‖ ≤ C :=
    (hnorm k t).trans ((hM t ht).trans (le_max_left M 0))
  have hφLp : MemLp φ 2 ν := memLp_restrict_Ioc_of_continuousOn hφ
  have hmeas (k : ℕ) : AEStronglyMeasurable (fun t ↦ inner ℝ (u t) (B (φk k t))) ν :=
    ((innerSL ℝ (E := H)).memLp_of_bilin 1 hu
      (B.comp_memLp' ((S k).comp_memLp' (B.comp_memLp' hφLp)))).aestronglyMeasurable
  have hu1 : Integrable u ν := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) hu
  apply tendsto_integral_of_dominated_convergence
    (fun t ↦ (‖B‖ * C) * ‖u t‖) hmeas (hu1.norm.const_mul _)
  · intro k
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    calc
      ‖inner ℝ (u t) (B (φk k t))‖ ≤ ‖u t‖ * ‖B (φk k t)‖ := norm_inner_le_norm _ _
      _ ≤ ‖u t‖ * (‖B‖ * ‖φk k t‖) := mul_le_mul_of_nonneg_left (B.le_opNorm _) (norm_nonneg _)
      _ ≤ ‖u t‖ * (‖B‖ * C) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hbound k t (Ioc_subset_Icc_self ht)) (norm_nonneg _))
        (norm_nonneg _)
      _ = (‖B‖ * C) * ‖u t‖ := mul_comm _ _
  · filter_upwards with t
    exact tendsto_const_nhds.inner (B.continuous.continuousAt.tendsto.comp (hlim t))

/-- Transport tested on a continuous H¹ curve is the integral limit of the
mollified tests. Measurability comes from mollified velocities, while the H¹ contraction
supplies a scale-independent integrable bound. -/
theorem tendsto_integral_transport_mollified_test (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k)
    (hε0 : Tendsto ε atTop (𝓝 0)) (hab : a ≤ b)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b, ∀ j p q,
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L)
    {u : ℝ → H} (hu : MemLp u 2 ν) (φ : ℝ → V) (hφ : ContinuousOn φ (Icc a b)) :
    Tendsto (fun k ↦ ∫ t, transportTestFunctional (A t)
      (mollifierProductH1CLM (standardMollifier n) (hε k) (transportBaseCLM (φ t))) (u t) ∂ν)
      atTop (𝓝 (∫ t, transportTestFunctional (A t) (φ t) (u t) ∂ν)) := by
  let B : V →L[ℝ] H := transportBaseCLM
  let S (k : ℕ) : H →L[ℝ] V := mollifierProductH1CLM (standardMollifier n) (hε k)
  let φk (k : ℕ) (t : ℝ) : V := S k (B (φ t))
  have hnorm (k : ℕ) (t : ℝ) : ‖φk k t‖ ≤ ‖φ t‖ :=
    norm_mollifierProductH1CLM_base_le (standardMollifier n) (hε k) (φ t)
  have hlim (t : ℝ) : Tendsto (fun k ↦ φk k t) atTop (𝓝 (φ t)) :=
    tendsto_mollifierProductH1CLM_base (standardMollifier n) ε hε hε0 (φ t)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
  let C : ℝ := max M 0
  have hbound (k : ℕ) (t : ℝ) (ht : t ∈ Icc a b) : ‖φk k t‖ ≤ C :=
    (hnorm k t).trans ((hM t ht).trans (le_max_left M 0))
  have hyLp : MemLp (fun t ↦ B (φ t)) 2 ν := B.comp_memLp' (memLp_restrict_Ioc_of_continuousOn hφ)
  have hmeas (k : ℕ) : AEStronglyMeasurable
      (fun t ↦ transportTestFunctional (A t) (φk k t) (u t)) ν := by
    have h := (innerSL ℝ (E := H)).memLp_of_bilin 1
      (memLp_mollifiedTransportDrift (standardMollifier n) (hε k) hab A hA L hL hu) hyLp
    apply h.aestronglyMeasurable.congr
    filter_upwards with t
    exact inner_mollifiedTransportDrift (hε k) (A t) (u t) (B (φ t))
  obtain ⟨K, hK, hKbound⟩ := exists_uniform_bound_transportTestFunctional A hA L hL
  have hu1 : Integrable u ν := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) hu
  apply tendsto_integral_of_dominated_convergence
    (fun t ↦ (K * C) * ‖u t‖) hmeas (hu1.norm.const_mul _)
  · intro k
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    calc
      ‖transportTestFunctional (A t) (φk k t) (u t)‖ ≤
          ‖transportTestFunctional (A t) (φk k t)‖ * ‖u t‖ :=
        (transportTestFunctional (A t) (φk k t)).le_opNorm _
      _ ≤ (K * ‖φk k t‖) * ‖u t‖ := mul_le_mul_of_nonneg_right
        (hKbound t (Ioc_subset_Icc_self ht) (φk k t)) (norm_nonneg _)
      _ ≤ (K * C) * ‖u t‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hbound k t (Ioc_subset_Icc_self ht)) hK) (norm_nonneg _)
  · filter_upwards with t
    simpa only [Function.comp_def, transportTestInTestCLM_apply] using
      (transportTestInTestCLM (A t) (u t)).continuous.continuousAt.tendsto.comp (hlim t)

end PDE.Hyperbolic.FirstOrder
