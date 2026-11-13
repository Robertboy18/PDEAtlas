/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import PDE.Analysis.MeasureTheory.Lp.Superposition

/-!
# Lower semicontinuity of integral energies on `Lᵖ`

For an integrand `F x z` continuous in `z` almost everywhere, strong `Lᵖ`
convergence gives an almost-everywhere convergent subsequence. Fatou's lemma
then shows that the integral energy has closed sublevel sets, provided the
densities have a common integrable lower bound.

The real Bochner integral is totalized at nonintegrable functions. The general
theorem therefore requires integrability of each density. The growth theorem
proves this hypothesis from joint measurability and
`|F x z| ≤ a x + C * ‖z‖ ^ p.toReal`, where `a` is integrable and `1 ≤ p < ∞`.
The lower bound may be negative; take it to be zero for nonnegative energies.
No finiteness assumption on the measure or convexity assumption on `F` is needed.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] {p : ℝ≥0∞}

/-- Integral energies with continuous integrands and a common integrable lower
bound are lower semicontinuous for the norm topology on `Lᵖ`. Every density is
assumed integrable, so the energies are finite.
This version includes `p = ∞` and does not require a measurable structure on `E`. -/
theorem lowerSemicontinuous_integral_Lp_of_integrable
    [Fact (1 ≤ p)] {F : α → E → ℝ} {b : α → ℝ}
    (hcont : ∀ᵐ x ∂μ, Continuous (F x))
    (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, ∀ z, b x ≤ F x z)
    (hF : ∀ u : Lp E p μ, Integrable (fun x ↦ F x (u x)) μ) :
    LowerSemicontinuous (fun u : Lp E p μ ↦ ∫ x, F x (u x) ∂μ) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro c
  refine IsSeqClosed.isClosed fun u v hu huv ↦ ?_
  change (∫ x, F x (v x) ∂μ) ≤ c
  have huc (n : ℕ) : (∫ x, F x (u n x) ∂μ) ≤ c := hu n
  obtain ⟨s, _, hs⟩ := (tendstoInMeasure_of_tendsto_Lp huv).exists_seq_tendsto_ae
  let G : Lp E p μ → α → ℝ := fun w x ↦ F x (w x) - b x
  have hG (w : Lp E p μ) : Integrable (G w) μ := (hF w).sub hb
  have hG_nonneg (w : Lp E p μ) : 0 ≤ᵐ[μ] G w :=
    hlower.mono fun x hx ↦ sub_nonneg.mpr (hx (w x))
  have hG_integral (w : Lp E p μ) :
      (∫ x, G w x ∂μ) = (∫ x, F x (w x) ∂μ) - ∫ x, b x ∂μ :=
    integral_sub (hF w) hb
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun n ↦ ENNReal.ofReal (G (u (s n)) x)) atTop
        (𝓝 (ENNReal.ofReal (G v x))) := by
    filter_upwards [hs, hcont] with x hx hcx
    exact ENNReal.tendsto_ofReal
      (((hcx.tendsto (v x)).comp hx).sub tendsto_const_nhds)
  have hfatou :
      (∫⁻ x, ENNReal.ofReal (G v x) ∂μ) ≤
        liminf (fun n ↦ ∫⁻ x, ENNReal.ofReal (G (u (s n)) x) ∂μ) atTop :=
    calc
      _ = ∫⁻ x, liminf (fun n ↦ ENNReal.ofReal (G (u (s n)) x)) atTop ∂μ :=
        lintegral_congr_ae (hlim.mono fun _ hx ↦ hx.liminf_eq.symm)
      _ ≤ _ := lintegral_liminf_le'
        (fun n ↦ (hG (u (s n))).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hshift (n : ℕ) : (∫ x, G (u n) x ∂μ) ≤ c - ∫ x, b x ∂μ := by
    rw [hG_integral]
    exact sub_le_sub_right (huc n) _
  have hc : 0 ≤ c - ∫ x, b x ∂μ :=
    (integral_nonneg_of_ae (hG_nonneg (u 0))).trans (hshift 0)
  have hsub : (∫ x, G v x ∂μ) ≤ c - ∫ x, b x ∂μ := by
    apply (ENNReal.ofReal_le_ofReal_iff hc).mp
    rw [ofReal_integral_eq_lintegral_ofReal (hG v) (hG_nonneg v)]
    refine hfatou.trans (liminf_le_of_frequently_le' (.of_forall fun n ↦ ?_))
    rw [← ofReal_integral_eq_lintegral_ofReal (hG (u (s n))) (hG_nonneg (u (s n)))]
    exact ENNReal.ofReal_le_ofReal (hshift (s n))
  rw [hG_integral] at hsub
  exact (sub_le_sub_iff_right _).mp hsub

/-- A continuous, jointly measurable integrand with integrable `p`-growth and
a common integrable lower bound defines a finite, norm-lower-semicontinuous
energy on `Lᵖ`, for `1 ≤ p < ∞`. All pointwise hypotheses are almost everywhere
in the spatial variable and hold for every value of the dependent variable. -/
theorem lowerSemicontinuous_integral_Lp_of_growth
    [Fact (1 ≤ p)] [MeasurableSpace E] [BorelSpace E]
    (hp_top : p ≠ ∞) {F : α → E → ℝ} {a b : α → ℝ} {C : ℝ}
    (hF : Measurable (Function.uncurry F))
    (hcont : ∀ᵐ x ∂μ, Continuous (F x))
    (ha : Integrable a μ) (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, ∀ z, b x ≤ F x z)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, |F x z| ≤ a x + C * ‖z‖ ^ p.toReal) :
    LowerSemicontinuous (fun u : Lp E p μ ↦ ∫ x, F x (u x) ∂μ) :=
  lowerSemicontinuous_integral_Lp_of_integrable hcont hb hlower fun u ↦
    (Lp.memLp u).integrable_comp_of_norm_rpow_le
      (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp_top hF ha
      (by simpa only [Real.norm_eq_abs] using hgrowth)

end MeasureTheory
