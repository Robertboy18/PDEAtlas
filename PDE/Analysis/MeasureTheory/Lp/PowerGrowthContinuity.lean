/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.PowerSuperposition
public import PDE.Analysis.ENNReal.Holder

/-!
# Continuity of integral densities and conjugate-growth fields

A jointly measurable density, almost everywhere continuous in its value variable,
with growth `a(x) + C |z|^p` and `a ∈ L¹`, has a continuous integral on `Lᵖ`
for `1 ≤ p < ∞`. A continuous field with
growth `b(x) + L |z|^(p-1)`, where `b ∈ Lᵠ` and `1/p + 1/q = 1`, defines a
continuous map from `Lᵖ` to `Lᵠ` for `1 < p < ∞`.

The growth estimates prove the required integrability. Continuity follows
from the norm-power superposition theorem, after identifying its divided
exponent with one or the conjugate exponent. The measure need not be finite.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A continuous density with an integrable `p`-growth bound has a continuous
integral on `Lᵖ`, including `p = 1`. Joint measurability and the bound prove
integrability at every field; no finite-measure assumption is needed. -/
theorem continuous_integral_Lp_of_rpow_growth
    (hp_top : p ≠ ∞) {G : α → E → ℝ} {a : α → ℝ} {C : ℝ}
    (hG : Measurable (Function.uncurry G))
    (hcont : ∀ᵐ x ∂μ, Continuous (G x)) (ha : Integrable a μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, |G x z| ≤ a x + C * ‖z‖ ^ p.toReal) :
    Continuous (fun u : Lp E p μ ↦ ∫ x, G x (u x) ∂μ) := by
  have hp_zero : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp_zero hp_top
  have hdiv : p / ENNReal.ofReal p.toReal = 1 := by
    rw [ENNReal.ofReal_toReal hp_top, ENNReal.div_self hp_zero hp_top]
  have hint (u : Lp E p μ) : MemLp (fun x ↦ G x (u x)) 1 μ := by
    apply memLp_one_iff_integrable.mpr
    exact (Lp.memLp u).integrable_comp_of_norm_rpow_le hp_zero hp_top hG ha
      (by simpa only [Real.norm_eq_abs] using hgrowth)
  -- Identify the target exponent before constructing its `Lp` topology.
  have hsuper (q : ℝ≥0∞) [Fact (1 ≤ q)]
      (hq : p / ENNReal.ofReal p.toReal = q)
      (hmem : ∀ u : Lp E p μ, MemLp (fun x ↦ G x (u x)) q μ)
      (ha' : MemLp a q μ) : Continuous (Lp.superposition G hmem) := by
    subst q
    exact Lp.continuous_superposition_of_rpow_growth hp_top hr hmem
      hcont ha' (by simpa only [Real.norm_eq_abs] using hgrowth)
  convert L1.continuous_integral.comp
    (hsuper 1 hdiv hint (memLp_one_iff_integrable.mpr ha)) using 1
  ext u
  rw [Function.comp_apply, L1.integral_eq_integral]
  exact integral_congr_ae (Lp.coeFn_superposition G hint u).symm

namespace Lp

/-- A continuous field of conjugate growth sends `Lᵖ` continuously to `Lᵠ`.
Membership of the image is derived from joint measurability and the bound
`b(x) + C |z|^(p-1)`, with `b ∈ Lᵠ`. The restriction `p > 1` makes the
norm power positive, while `p < ∞` permits the Vitali convergence argument. -/
theorem continuous_superposition_of_conjugate_growth
    {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {q : ℝ≥0∞} [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp_one : 1 < p) (hp_top : p ≠ ∞)
    {G : α → E → F} {b : α → ℝ} {C : ℝ}
    (hG : Measurable (Function.uncurry G))
    (hcont : ∀ᵐ x ∂μ, Continuous (G x)) (hb : MemLp b q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖G x z‖ ≤ b x + C * ‖z‖ ^ (p.toReal - 1)) :
    Continuous (superposition G (fun u : Lp E p μ ↦
      (Lp.memLp u).comp_of_norm_rpow_sub_one_le hp_top hG hb hgrowth)) := by
  have hr : 0 < p.toReal - 1 := sub_pos.mpr (by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (by simp) hp_top).mpr hp_one)
  have hdiv := ENNReal.HolderConjugate.div_ofReal_toReal_sub_one p q hp_top
  subst q
  exact continuous_superposition_of_rpow_growth hp_top hr
    (fun u : Lp E p μ ↦
      (Lp.memLp u).comp_of_norm_rpow_sub_one_le hp_top hG hb hgrowth)
    hcont hb hgrowth

end Lp

end MeasureTheory
