/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonlinearity.BoundedTransport
public import PDE.Spaces.Sobolev.GraphSpace.Operators.VectorMultiplier
import PDE.Analysis.MeasureTheory.Lp.EssentialSupremum

/-!
# Cutting off transport coefficients

Bounded-coefficient transport is linear in its coefficients, and multiplying the output by an
`L∞` function `φ` is transport with the coefficients multiplied by `φ`. If the coefficients
vanish at infinity, then multiplication of the output by the indicator of a large ball changes
the transport by an operator of small norm.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev Topology

namespace NavierStokes.BoundedTransport

variable {n : ℕ}

/-- Transport coefficients vanish at infinity if, for every `ε > 0`, all of them are bounded by
`ε` almost everywhere outside some ball. -/
def CoefficientsVanishAtInfinity (b : Fin n → DerivLp n ∞ Set.univ)
    (c : Fin n → Fin n → DerivLp n ∞ Set.univ) : Prop :=
  ∀ ε > 0, ∃ R : ℝ, ∀ᵐ x ∂volume, R < ‖x‖ → (∀ i, |b i x| ≤ ε) ∧ ∀ j i, |c j i x| ≤ ε

/-- Coefficients whose representatives tend to zero at infinity vanish at infinity. -/
theorem CoefficientsVanishAtInfinity.of_tendsto {b : Fin n → DerivLp n ∞ Set.univ}
    {c : Fin n → Fin n → DerivLp n ∞ Set.univ} {f : Fin n → ℝ^n → ℝ}
    {g : Fin n → Fin n → ℝ^n → ℝ} (hb : ∀ i, (b i : ℝ^n → ℝ) =ᵐ[volume] f i)
    (hc : ∀ j i, (c j i : ℝ^n → ℝ) =ᵐ[volume] g j i)
    (hf : ∀ i, Tendsto (f i) (cocompact (ℝ^n)) (𝓝 0))
    (hg : ∀ j i, Tendsto (g j i) (cocompact (ℝ^n)) (𝓝 0)) :
    CoefficientsVanishAtInfinity b c := by
  intro ε hε
  have hsmall {h : ℝ^n → ℝ} (hh : Tendsto h (cocompact (ℝ^n)) (𝓝 0)) :
      ∀ᶠ x in cocompact (ℝ^n), |h x| ≤ ε := by
    filter_upwards [hh.eventually (Metric.closedBall_mem_nhds (0 : ℝ) hε)] with x hx
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hx
  have hev : ∀ᶠ x in cocompact (ℝ^n), (∀ i, |f i x| ≤ ε) ∧ ∀ j i, |g j i x| ≤ ε :=
    (eventually_all.2 fun i ↦ hsmall (hf i)).and
      (eventually_all.2 fun j ↦ eventually_all.2 fun i ↦ hsmall (hg j i))
  rw [← Metric.cobounded_eq_cocompact] at hev
  obtain ⟨R, -, hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hev
  refine ⟨R, ?_⟩
  filter_upwards [ae_all_iff.2 hb, ae_all_iff.2 fun j ↦ ae_all_iff.2 (hc j)] with x hbx hcx hxR
  obtain ⟨h1, h2⟩ := hR (show R ≤ ‖x‖ from hxR.le)
  exact ⟨fun i ↦ (hbx i).symm ▸ h1 i, fun j i ↦ (hcx j i).symm ▸ h2 j i⟩

/-- Transport is additive in its coefficients, in the form of a difference. -/
theorem transport_sub (b b' : Fin n → DerivLp n ∞ Set.univ)
    (c c' : Fin n → Fin n → DerivLp n ∞ Set.univ) :
    transport (b - b') (c - c') = transport b c - transport b' c' := by
  apply ContinuousLinearMap.ext
  intro v
  apply VectorH.ext_base
  intro j
  rw [sub_apply, PiLp.sub_apply, map_sub, transport_base, transport_base,
    transport_base, scalarTransport_apply, scalarTransport_apply, scalarTransport_apply,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, mulLpLeft_apply, sub_eq_add_neg, Lp.smul_add, Lp.neg_smul]
  abel

/-- Multiplying the output of transport by `φ` multiplies every coefficient by `φ`. -/
theorem transport_smul (φ : DerivLp n ∞ Set.univ) (b : Fin n → DerivLp n ∞ Set.univ)
    (c : Fin n → Fin n → DerivLp n ∞ Set.univ) :
    transport (fun i ↦ (φ • b i : DerivLp n ∞ Set.univ))
        (fun j i ↦ (φ • c j i : DerivLp n ∞ Set.univ)) =
      (vectorMul n φ).comp (transport b c) := by
  apply ContinuousLinearMap.ext
  intro v
  apply VectorH.ext_base
  intro j
  rw [ContinuousLinearMap.comp_apply, wkpBaseCoordinateCLM_vectorMul, transport_base,
    transport_base, scalarTransport_apply, scalarTransport_apply, ← mulLpLeft_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mulLpLeft_apply, Lp.add_smul, lpSMul_top_top_two_assoc]

/-- If the coefficients vanish at infinity, then for every `ε > 0` there is a bounded function
`ψ` with compact essential support, the indicator of a large ball, such that multiplying the
transport output by `ψ` changes the transport by at most `ε` in operator norm. -/
theorem exists_vectorMul_cutoff {b : Fin n → DerivLp n ∞ Set.univ}
    {c : Fin n → Fin n → DerivLp n ∞ Set.univ} (h : CoefficientsVanishAtInfinity b c) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (ψ : DerivLp n ∞ Set.univ) (K : Set (ℝ^n)), IsCompact K ∧
      (∀ᵐ x ∂volume, ψ x = 0 ∨ x ∈ K) ∧
      ‖transport b c - (vectorMul n ψ).comp (transport b c)‖ ≤ ε := by
  set ε' := ε / (2 * (n : ℝ) ^ 2 + 1) with hε'
  have hε'pos : 0 < ε' := div_pos hε (by positivity)
  obtain ⟨R, hR⟩ := h ε' hε'pos
  have hfin : domainMeasure n Set.univ (Metric.closedBall (0 : ℝ^n) R) ≠ ⊤ := by
    simp only [domainMeasure, Measure.restrict_univ]
    exact measure_closedBall_lt_top.ne
  let ψ : DerivLp n ∞ Set.univ := indicatorConstLp ∞ Metric.isClosed_closedBall.measurableSet
    hfin (1 : ℝ)
  have hψ : (ψ : ℝ^n → ℝ) =ᵐ[volume] (Metric.closedBall (0 : ℝ^n) R).indicator fun _ ↦ 1 := by
    have h := indicatorConstLp_coeFn (p := ∞) (hs := Metric.isClosed_closedBall.measurableSet)
      (hμs := hfin) (c := (1 : ℝ))
    simpa only [domainMeasure, Measure.restrict_univ] using h
  have hcut (f : DerivLp n ∞ Set.univ)
      (hf : ∀ᵐ x ∂volume, R < ‖x‖ → |f x| ≤ ε') : ‖f - ψ • f‖ ≤ ε' := by
    refine Lp.norm_top_le_of_ae_bound hε'pos.le ?_
    have hsmul := Lp.coeFn_lpSMul (r := ∞) ψ f
    have hsub := Lp.coeFn_sub f (ψ • f : DerivLp n ∞ Set.univ)
    simp only [domainMeasure, Measure.restrict_univ] at hsmul hsub ⊢
    filter_upwards [hf, hψ, hsmul, hsub] with x hfx hψx hsx hdx
    rw [Real.norm_eq_abs, hdx, Pi.sub_apply, hsx, Pi.smul_apply', hψx, smul_eq_mul]
    by_cases hx : x ∈ Metric.closedBall (0 : ℝ^n) R
    · rw [indicator_of_mem hx, one_mul, sub_self, abs_zero]
      exact hε'pos.le
    · rw [indicator_of_notMem hx, zero_mul, sub_zero]
      apply hfx
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  refine ⟨ψ, Metric.closedBall 0 R, isCompact_closedBall 0 R, ?_, ?_⟩
  · filter_upwards [hψ] with x hx
    by_cases hmem : x ∈ Metric.closedBall (0 : ℝ^n) R
    · exact Or.inr hmem
    · left
      rw [hx, indicator_of_notMem hmem]
  · rw [← transport_smul, ← transport_sub]
    refine (norm_transport_le _ _).trans ?_
    unfold coefficientBound
    calc
      _ ≤ ∑ _j : Fin n, ∑ _i : Fin n, (ε' + ε') := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro i _
        apply add_le_add
        · exact hcut (b i) (by filter_upwards [hR] with x hx hxR using (hx hxR).1 i)
        · exact hcut (c j i) (by filter_upwards [hR] with x hx hxR using (hx hxR).2 j i)
      _ = 2 * (n : ℝ) ^ 2 * ε' := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ ≤ ε := by
        rw [hε', ← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith

end NavierStokes.BoundedTransport
