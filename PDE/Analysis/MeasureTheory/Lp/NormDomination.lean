/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Norm estimates from sums of pointwise bounds

Pointwise domination by a sum of norms yields the corresponding sum of `Lp` norms. Taking
the norms before adding prevents cancellation in the dominating functions.
-/

@[expose] public section

namespace MeasureTheory.Lp

open Filter
open scoped ENNReal

section EssentialBound

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup E]

/-- The norm of an `L∞` representative is bounded almost everywhere by its `L∞` norm. -/
theorem norm_apply_ae_le (f : Lp E ∞ μ) : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖f‖ := by
  have hfinite : eLpNormEssSup f μ ≠ ⊤ := by
    simpa only [eLpNorm_exponent_top (Lp.aestronglyMeasurable f)] using Lp.eLpNorm_ne_top f
  filter_upwards [ae_le_eLpNormEssSup (f := f)] with x hx
  have h := ENNReal.toReal_mono hfinite hx
  simpa only [enorm, ENNReal.coe_toReal, coe_nnnorm, Lp.norm_def,
    eLpNorm_exponent_top (Lp.aestronglyMeasurable f)] using h

end EssentialBound

section FiniteSums

variable {X F ι : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞}
  [NormedAddCommGroup F]

/-- The sum of pointwise norms of finitely many `Lp` fields, as a real `Lp` element. -/
noncomputable def sumNorms (s : Finset ι) (f : ι → Lp F p μ) : Lp ℝ p μ :=
  ∑ i ∈ s, lipschitzWith_one_norm.compLp (_root_.norm_zero : ‖(0 : F)‖ = 0) (f i)

/-- The chosen representative of `sumNorms` is the pointwise sum almost everywhere. -/
theorem sumNorms_ae (s : Finset ι) (f : ι → Lp F p μ) :
    sumNorms s f =ᵐ[μ] fun x ↦ ∑ i ∈ s, ‖f i x‖ := by
  have hn : ∀ᵐ x ∂μ, ∀ i ∈ s,
      lipschitzWith_one_norm.compLp (_root_.norm_zero : ‖(0 : F)‖ = 0) (f i) x = ‖f i x‖ :=
    (ae_ball_iff s.finite_toSet.countable).mpr fun i _ ↦
      lipschitzWith_one_norm.coeFn_compLp (_root_.norm_zero : ‖(0 : F)‖ = 0) (f i)
  filter_upwards [coeFn_fun_finsetSum s
    (fun i ↦ lipschitzWith_one_norm.compLp (_root_.norm_zero : ‖(0 : F)‖ = 0) (f i)), hn]
    with x hs hx
  exact hs.trans (Finset.sum_congr rfl hx)

/-- The norm of a finite pointwise norm sum is bounded by the sum of the input norms. -/
theorem norm_sumNorms_le [Fact (1 ≤ p)] (s : Finset ι) (f : ι → Lp F p μ) :
    ‖sumNorms s f‖ ≤ ∑ i ∈ s, ‖f i‖ := by
  refine (norm_sum_le s _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  simpa only [NNReal.coe_one, one_mul] using
    lipschitzWith_one_norm.norm_compLp_le (_root_.norm_zero : ‖(0 : F)‖ = 0) (f i)

end FiniteSums

variable {X E F G : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞}
  [Fact (1 ≤ p)] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedAddCommGroup G]

/-- An almost-everywhere bound by two pointwise norms gives the sum of their `Lp` norms. -/
theorem mul_norm_le_add_of_ae_le_add
    {c : ℝ} (hc : 0 ≤ c) (f : Lp E p μ) (g : Lp F p μ) (h : Lp G p μ)
    (hbound : ∀ᵐ x ∂μ, c * ‖f x‖ ≤ ‖g x‖ + ‖h x‖) :
    c * ‖f‖ ≤ ‖g‖ + ‖h‖ := by
  let g' := lipschitzWith_one_norm.compLp (_root_.norm_zero : ‖(0 : F)‖ = 0) g
  let h' := lipschitzWith_one_norm.compLp (_root_.norm_zero : ‖(0 : G)‖ = 0) h
  have hgeq : (g' : X → ℝ) =ᵐ[μ] fun x ↦ ‖g x‖ :=
    lipschitzWith_one_norm.coeFn_compLp (_root_.norm_zero : ‖(0 : F)‖ = 0) g
  have hheq : (h' : X → ℝ) =ᵐ[μ] fun x ↦ ‖h x‖ :=
    lipschitzWith_one_norm.coeFn_compLp (_root_.norm_zero : ‖(0 : G)‖ = 0) h
  have hdom : ∀ᵐ x ∂μ, ‖(c • f) x‖ ≤ ‖(g' + h') x‖ := by
    filter_upwards [hbound, coeFn_smul c f, coeFn_add g' h', hgeq, hheq]
      with x hx hf hg hgn hhn
    simpa only [hf, hg, Pi.smul_apply, Pi.add_apply, hgn, hhn, Function.comp_apply,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hc,
      abs_of_nonneg (add_nonneg (norm_nonneg (g x)) (norm_nonneg (h x)))] using hx
  calc
    c * ‖f‖ = ‖c • f‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ ‖g' + h'‖ := norm_le_norm_of_ae_le hdom
    _ ≤ ‖g'‖ + ‖h'‖ := norm_add_le _ _
    _ ≤ ‖g‖ + ‖h‖ := add_le_add
      (by simpa only [one_mul, NNReal.coe_one] using
        lipschitzWith_one_norm.norm_compLp_le (_root_.norm_zero : ‖(0 : F)‖ = 0) g)
      (by simpa only [one_mul, NNReal.coe_one] using
        lipschitzWith_one_norm.norm_compLp_le (_root_.norm_zero : ‖(0 : G)‖ = 0) h)

end MeasureTheory.Lp
