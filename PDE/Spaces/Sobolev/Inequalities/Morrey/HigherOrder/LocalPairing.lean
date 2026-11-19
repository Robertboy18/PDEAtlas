/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.CutoffEmbedding

/-!
# Local Sobolev pairings with integrable weights

On a compact subset of an open domain, the supercritical Hilbert Sobolev
embedding is a bounded map into L∞. Thus an L¹ weight defines a continuous
pairing of two local Sobolev bases. No boundedness or differentiability of the
weight is required. Bounded weights also pair arbitrary local L² rows.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal BoundedContinuousFunction Sobolev

namespace SobolevSpace

open GraphSpace CompactSupportLocalization.HigherOrderLocalizedCutoff

variable {n k : ℕ} {Ω : Set (ℝ^n)} {K : Compacts (ℝ^n)}

/-- A supercritical local Sobolev base restricts continuously into L∞ on
every compact subset of its open domain. The map preserves the base. -/
theorem exists_local_hk_base_Linfty (hn : 0 < n) (hk : 1 + n / 2 ≤ k)
    (hΩ : IsOpen Ω) (hK : (K : Set (ℝ^n)) ⊆ Ω) :
    ∃ E : W^{k,2}(Ω) →L[ℝ] Lp ℝ ∞ (domainMeasure n K),
      ∀ U, (E U : ℝ^n → ℝ) =ᵐ[domainMeasure n K] baseRepresentative U := by
  obtain ⟨ψ, hψΩ, hψone, _, _⟩ :=
    TestFunction.exists_eq_one_on_compact hΩ K.isCompact hK
  let A := extendByCutoffCLM (by omega : 0 < k)
    hΩ isOpen_univ (subset_univ Ω) ψ hψΩ
  let J := (cutoffContinuousEmbedding hn hk ψ).comp A
  have : IsFiniteMeasure (domainMeasure n K) :=
    ⟨by simpa only [domainMeasure, Measure.restrict_apply_univ] using
      K.isCompact.measure_lt_top (μ := (volume : Measure (ℝ^n)))⟩
  let E := (BoundedContinuousFunction.toLp ∞ (domainMeasure n K) ℝ).comp J
  refine ⟨E, fun U ↦ ?_⟩
  have h₁ := cutoffContinuousEmbedding_ae hn hk ψ (A U)
  have h₂ : baseRepresentative (A U) =ᵐ[volume]
      fun x ↦ ψ.toFun x * baseRepresentative U x := by
    simpa only [A, extendByCutoffCLM_apply, domainMeasure, Measure.restrict_univ] using
      extendByCutoff_base_ae hΩ (subset_univ Ω) ψ hψΩ U
  filter_upwards [BoundedContinuousFunction.coeFn_toLp ∞ (domainMeasure n K) ℝ (J U),
    h₁.filter_mono (ae_mono Measure.restrict_le_self),
    h₂.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem K.isCompact.measurableSet] with x hx h₁x h₂x hxK
  change E U x = baseRepresentative U x
  change E U x = J U x at hx
  rw [hx]
  change cutoffContinuousEmbedding hn hk ψ (A U) x = _
  rw [h₁x, h₂x, hψone x hxK, one_mul, one_mul]

/-- An L¹ weight pairs two supercritical Sobolev bases on a compact set.
For each fixed first input the pairing is a continuous linear functional of
the second input, and its defining integral is absolutely integrable. -/
theorem exists_local_hk_weighted_pairing (hn : 0 < n) (hk : 1 + n / 2 ≤ k)
    (hΩ : IsOpen Ω) (hK : (K : Set (ℝ^n)) ⊆ Ω)
    {a : ℝ^n → ℝ} (ha : Integrable a (domainMeasure n K)) (U : W^{k,2}(Ω)) :
    ∃ T : W^{k,2}(Ω) →L[ℝ] ℝ, ∀ V,
      Integrable (fun x ↦ baseRepresentative U x * a x * baseRepresentative V x)
        (domainMeasure n K) ∧
      T V = ∫ x, baseRepresentative U x * a x * baseRepresentative V x
        ∂domainMeasure n K := by
  obtain ⟨E, hE⟩ := exists_local_hk_base_Linfty hn hk hΩ hK
  have hb : Integrable (fun x ↦ baseRepresentative U x * a x)
      (domainMeasure n K) := by
    have h := (Lp.memLp (E U)).integrable_mul (memLp_one_iff_integrable.mpr ha)
    exact h.congr ((hE U).fun_mul (EventuallyEq.refl _ _))
  let b := (memLp_one_iff_integrable.mpr hb).toLp
    (fun x ↦ baseRepresentative U x * a x)
  let T := ((ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n K) 1 ∞ b).comp E
  have hpair (V : W^{k,2}(Ω)) :
      (fun x ↦ b x * E V x) =ᵐ[domainMeasure n K]
        fun x ↦ baseRepresentative U x * a x * baseRepresentative V x :=
    (memLp_one_iff_integrable.mpr hb).coeFn_toLp.fun_mul (hE V)
  refine ⟨T, fun V ↦ ⟨((Lp.memLp b).integrable_mul (Lp.memLp (E V))).congr
    (hpair V), ?_⟩⟩
  change (ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n K) 1 ∞ b (E V) = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  exact integral_congr_ae (hpair V)

/-- A bounded compact weight pairs any two local L² rows continuously.
No weak derivatives of either row or the coefficient are required. -/
theorem exists_local_L2_weighted_pairing (hK : (K : Set (ℝ^n)) ⊆ Ω)
    {a : ℝ^n → ℝ} (ha : MemLp a ∞ (domainMeasure n K)) (u : DerivLp n 2 Ω) :
    ∃ T : DerivLp n 2 Ω →L[ℝ] ℝ, ∀ v,
      Integrable (fun x ↦ u x * a x * v x) (domainMeasure n K) ∧
      T v = ∫ x, u x * a x * v x ∂domainMeasure n K := by
  let R : DerivLp n 2 Ω →L[ℝ] DerivLp n 2 K := restrictDerivLp hK
  have hu : MemLp (u : ℝ^n → ℝ) 2 (domainMeasure n K) :=
    (Lp.memLp u).mono_measure (domainMeasure_le hK)
  have hb : MemLp (fun x ↦ u x * a x) 2 (domainMeasure n K) := hu.mul ha
  let b := hb.toLp (fun x ↦ u x * a x)
  let T := ((ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n K) 2 2 b).comp R
  have hpair (v : DerivLp n 2 Ω) :
      (fun x ↦ b x * R v x) =ᵐ[domainMeasure n K] fun x ↦ u x * a x * v x :=
    hb.coeFn_toLp.fun_mul (restrictDerivLp_apply_ae hK v)
  refine ⟨T, fun v ↦ ⟨((Lp.memLp b).integrable_mul (Lp.memLp (R v))).congr
    (hpair v), ?_⟩⟩
  change (ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n K) 2 2 b (R v) = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  exact integral_congr_ae (hpair v)

end SobolevSpace
