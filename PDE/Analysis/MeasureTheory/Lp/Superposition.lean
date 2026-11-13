/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import PDE.Analysis.MeasureTheory.DominatedLp
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Tactic.Positivity.Finset

/-!
# Continuous superposition operators and integral energies

The nonlinear expression `G x (u x)` often belongs to a different space from `u`.
Linear growth preserves `Lᵖ`, while quadratic growth sends `L²` to `L¹`.
For `1 ≤ p < ∞`, the linear-growth map is continuous when `G x` is continuous
almost everywhere; the quadratic-growth map is continuous under the same
continuity hypothesis. In both cases, membership in the output space is
assumed or proved from joint measurability, and the growth offset belongs
to the output `Lᵖ` or `L¹` space. No Lipschitz condition on `G x` is required.

The proof uses Mathlib's Vitali theorem. Strongly convergent inputs have uniformly
integrable, uniformly tight norm bounds. These two properties pass to the outputs
through the growth estimate, while an almost-everywhere convergent subsequence
identifies the limit. Keeping uniform tightness in the argument lets the theorem
work on arbitrary measure spaces, including domains of infinite measure.

The general continuity theorem takes a continuously varying `Lᵠ` bound on the
output norms. Linear bounds use Mathlib's norm map on `Lᵖ`; quadratic bounds use
its continuous Hölder pairing on `L² × L²`. Composing the latter superposition
operator with the Bochner integral proves continuity of quadratic-growth
integral energies. A separate integrability theorem handles general `p`-growth.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] {p q : ℝ≥0∞}

/-- Joint measurability and a linear norm bound with an `Lᵖ` offset ensure that
the pointwise nonlinear expression belongs to `Lᵖ`. Continuity is not needed for
this integrability statement, and the exponent may be infinite. -/
theorem MemLp.comp_of_norm_le
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {u : α → E} (hu : MemLp u p μ)
    {G : α → E → F} {a : α → ℝ} {C : ℝ}
    (hG : Measurable (Function.uncurry G)) (ha : MemLp a p μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖G x z‖ ≤ a x + C * ‖z‖) :
    MemLp (fun x ↦ G x (u x)) p μ := by
  refine (ha.add (hu.norm.const_mul C)).mono' ?_ ?_
  · exact (hG.comp_aemeasurable
      (aemeasurable_id.prodMk hu.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  · exact hgrowth.mono fun x hx ↦ hx (u x)

/-- A jointly measurable integrand with an integrable `p`-growth bound sends
`Lᵖ` functions to integrable vector-valued densities, for `0 < p < ∞`.
Neither finiteness of the measure nor positivity of `C` is required. -/
theorem MemLp.integrable_comp_of_norm_rpow_le
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {u : α → E} (hu : MemLp u p μ) (hp_zero : p ≠ 0) (hp_top : p ≠ ∞)
    {G : α → E → F} {a : α → ℝ} {C : ℝ}
    (hG : Measurable (Function.uncurry G)) (ha : Integrable a μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖G x z‖ ≤ a x + C * ‖z‖ ^ p.toReal) :
    Integrable (fun x ↦ G x (u x)) μ := by
  refine (ha.add ((hu.integrable_norm_rpow hp_zero hp_top).const_mul C)).mono'
    (hG.comp_aemeasurable
      (aemeasurable_id.prodMk hu.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable ?_
  exact hgrowth.mono fun x hx ↦ hx (u x)

namespace Lp

/-- Apply a spatially dependent nonlinear map pointwise to an `Lᵖ` function.
The integrability argument is separate from the construction; for linear growth,
it is supplied by `MemLp.comp_of_norm_le`. -/
def superposition (G : α → E → F)
    (hG : ∀ u : Lp E p μ, MemLp (fun x ↦ G x (u x)) q μ)
    (u : Lp E p μ) : Lp F q μ :=
  (hG u).toLp (fun x ↦ G x (u x))

/-- The representative chosen for a superposition operator agrees almost
everywhere with the pointwise expression. -/
theorem coeFn_superposition (G : α → E → F)
    (hG : ∀ u : Lp E p μ, MemLp (fun x ↦ G x (u x)) q μ)
    (u : Lp E p μ) :
    superposition G hG u =ᵐ[μ] fun x ↦ G x (u x) :=
  (hG u).coeFn_toLp

/-- A superposition operator with `Lᵠ` outputs is continuous when the integrand
is continuous in its input at almost every spatial point and the output norms
admit a bound varying continuously in a finite-exponent `Lᵠ` space. This separates
the Vitali argument from the growth estimate used to construct the bound.
The input exponent may be infinite, and the measure need not be finite. -/
theorem continuous_superposition_of_continuous_bound
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hq_top : q ≠ ∞)
    {G : α → E → F}
    (hG : ∀ u : Lp E p μ, MemLp (fun x ↦ G x (u x)) q μ)
    (hcont : ∀ᵐ x ∂μ, Continuous (G x))
    (B : Lp E p μ → Lp ℝ q μ) (hBcont : Continuous B)
    (hbound : ∀ u : Lp E p μ, ∀ᵐ x ∂μ, ‖G x (u x)‖ ≤ ‖B u x‖) :
    Continuous (superposition G hG) := by
  rw [continuous_iff_seqContinuous]
  intro u v huv
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _
    (fun n ↦ hG (u n)) _ (hG v)).mpr
  have hBconv := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp
    (hBcont.continuousAt.tendsto.comp huv)
  obtain ⟨_, hui, hut⟩ := (tendstoInMeasure_iff_tendsto_Lp
    (Fact.out : 1 ≤ q) hq_top (fun n ↦ Lp.memLp (B (u n))) (Lp.memLp (B v))).mpr hBconv
  have huiG := hui.mono_norm (fun n ↦ (hG (u n)).aestronglyMeasurable)
    (fun n ↦ hbound (u n))
  have hutG := hut.mono_norm (fun n ↦ (hG (u n)).aestronglyMeasurable)
    (fun n ↦ hbound (u n))
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨ms, _, hms⟩ :=
    ((tendstoInMeasure_of_tendsto_Lp huv).comp hns).exists_seq_tendsto_ae
  refine ⟨ms, tendsto_Lp_of_tendsto_ae (Fact.out : 1 ≤ q) hq_top
    (fun n ↦ (hG (u (ns (ms n)))).aestronglyMeasurable) (hG v) ?_ ?_ ?_⟩
  · exact huiG.comp (fun i ↦ ns (ms i))
  · exact hutG.comp (fun i ↦ ns (ms i))
  · filter_upwards [hms, hcont] with x hx hcx
    exact (hcx.tendsto (v x)).comp hx

/-- A continuous integrand with linear norm growth gives a continuous
superposition operator on `Lᵖ`, for `1 ≤ p < ∞`. All pointwise hypotheses are
almost everywhere in space and hold for every value of the input.

No finiteness assumption on the measure is needed. The offset must itself
belong to `Lᵖ`; a nonzero constant offset is therefore insufficient on a domain
of infinite measure. -/
theorem continuous_superposition [Fact (1 ≤ p)] (hp_top : p ≠ ∞)
    {G : α → E → F}
    (hG : ∀ u : Lp E p μ, MemLp (fun x ↦ G x (u x)) p μ)
    (hcont : ∀ᵐ x ∂μ, Continuous (G x)) {a : α → ℝ} {C : ℝ}
    (ha : MemLp a p μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖G x z‖ ≤ a x + C * ‖z‖) :
    Continuous (superposition G hG) := by
  let B : Lp E p μ → Lp ℝ p μ := fun u ↦
    ha.toLp a + C • lipschitzWith_one_norm.compLp (_root_.norm_zero) u
  have hB (u : Lp E p μ) :
      B u =ᵐ[μ] fun x ↦ a x + C * ‖u x‖ := by
    filter_upwards [Lp.coeFn_add (ha.toLp a)
        (C • lipschitzWith_one_norm.compLp (_root_.norm_zero) u),
      ha.coeFn_toLp,
      Lp.coeFn_smul C (lipschitzWith_one_norm.compLp (_root_.norm_zero) u),
      lipschitzWith_one_norm.coeFn_compLp (_root_.norm_zero) u] with x hadd ha' hsmul hnorm
    simp only [B, hadd, Pi.add_apply, ha', hsmul, Pi.smul_apply, hnorm,
      Function.comp_apply, smul_eq_mul]
  have hBcont : Continuous B :=
    continuous_const.add
      ((lipschitzWith_one_norm.continuous_compLp (_root_.norm_zero)).const_smul C)
  refine continuous_superposition_of_continuous_bound hp_top hG hcont B hBcont ?_
  intro u
  filter_upwards [hgrowth, hB u] with x hx hBx
  rw [hBx, Real.norm_eq_abs]
  exact (hx (u x)).trans (le_abs_self _)

/-- A continuous integrand with quadratic norm growth sends `L²` continuously
to `L¹`. The square bound is constructed using Mathlib's continuous Hölder
pairing on `L² × L²`, so the theorem works for arbitrary measures and for
inputs in any normed additive group. -/
theorem continuous_superposition_of_quadratic_growth
    {G : α → E → F}
    (hG : ∀ u : Lp E 2 μ, MemLp (fun x ↦ G x (u x)) 1 μ)
    (hcont : ∀ᵐ x ∂μ, Continuous (G x)) {a : α → ℝ} {C : ℝ}
    (ha : MemLp a 1 μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖G x z‖ ≤ a x + C * ‖z‖ ^ 2) :
    Continuous (superposition G hG) := by
  let N : Lp E 2 μ → Lp ℝ 2 μ :=
    lipschitzWith_one_norm.compLp (_root_.norm_zero)
  let P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] Lp ℝ 1 μ :=
    (ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1
  let B : Lp E 2 μ → Lp ℝ 1 μ := fun u ↦ ha.toLp a + C • P (N u) (N u)
  have hNcont : Continuous N :=
    lipschitzWith_one_norm.continuous_compLp (_root_.norm_zero)
  have hBcont : Continuous B :=
    continuous_const.add ((P.continuous.comp hNcont).clm_apply hNcont |>.const_smul C)
  have hB (u : Lp E 2 μ) :
      B u =ᵐ[μ] fun x ↦ a x + C * ‖u x‖ ^ 2 := by
    filter_upwards [Lp.coeFn_add (ha.toLp a) (C • P (N u) (N u)),
      ha.coeFn_toLp, Lp.coeFn_smul C (P (N u) (N u)),
      (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 1) (N u) (N u),
      lipschitzWith_one_norm.coeFn_compLp (_root_.norm_zero) u]
      with x hadd ha' hsmul hprod hnorm
    simp only [B, hadd, Pi.add_apply, ha', hsmul, Pi.smul_apply, smul_eq_mul]
    change a x + C * (P (N u) (N u) x) = _
    rw [show P (N u) (N u) x = N u x * N u x from hprod]
    simp only [N, hnorm, Function.comp_apply, pow_two]
  refine continuous_superposition_of_continuous_bound (by simp) hG hcont B hBcont ?_
  intro u
  filter_upwards [hgrowth, hB u] with x hx hBx
  rw [hBx, Real.norm_eq_abs]
  exact (hx (u x)).trans (le_abs_self _)

end Lp

/-- A jointly measurable, almost-everywhere continuous integrand with quadratic
growth defines a finite continuous integral energy on `L²`. The offset is
integrable, so this also applies on domains of infinite measure. -/
theorem continuous_integral_L2_of_quadratic_growth
    [MeasurableSpace E] [BorelSpace E]
    {G : α → E → ℝ} {a : α → ℝ} {C : ℝ}
    (hG : Measurable (Function.uncurry G))
    (hcont : ∀ᵐ x ∂μ, Continuous (G x)) (ha : Integrable a μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, |G x z| ≤ a x + C * ‖z‖ ^ 2) :
    Continuous (fun u : Lp E 2 μ ↦ ∫ x, G x (u x) ∂μ) := by
  have hint (u : Lp E 2 μ) : MemLp (fun x ↦ G x (u x)) 1 μ := by
    apply memLp_one_iff_integrable.mpr
    apply (Lp.memLp u).integrable_comp_of_norm_rpow_le (by simp) (by simp) hG ha
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs] using hgrowth
  have hsuper := Lp.continuous_superposition_of_quadratic_growth hint hcont
    (memLp_one_iff_integrable.mpr ha) (by simpa only [Real.norm_eq_abs] using hgrowth)
  convert L1.continuous_integral.comp hsuper using 1
  ext u
  rw [Function.comp_apply, L1.integral_eq_integral]
  exact integral_congr_ae (Lp.coeFn_superposition G hint u).symm

end MeasureTheory

namespace MeasureTheory

variable {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] {p q : ℝ≥0∞}
  [ENNReal.HolderConjugate p q]

/-- The power `|u|^(p-1)` belongs to the conjugate-exponent space when
`u ∈ Lᵖ` and `p` is finite. This also covers `p = 1`, with output
exponent infinity and the usual real-power convention `0^0 = 1`. -/
theorem MemLp.norm_rpow_sub_one {u : α → E} (hu : MemLp u p μ)
    (hp_top : p ≠ ∞) :
    MemLp (fun x ↦ ‖u x‖ ^ (p.toReal - 1)) q μ := by
  have hdiv : p / (p - 1) = q := by
    apply inv_inj.mp
    rw [ENNReal.inv_div (Or.inr hp_top)
        (Or.inr (ENNReal.HolderConjugate.ne_zero p q)),
      div_eq_mul_inv, ENNReal.HolderConjugate.sub_one_mul_inv p q hp_top]
  simpa only [hdiv,
    ENNReal.toReal_sub_of_le (ENNReal.HolderConjugate.one_le p q) hp_top,
    ENNReal.toReal_one] using hu.norm_rpow_div (p - 1)

/-- Hölder makes the power-growth bound on an `Lᵖ` line integrable. This common
majorant controls differentiation under the integral and weak flux hemicontinuity.
The two inputs may take values in different normed spaces, and the measure is arbitrary.
For `p = 1, q = ∞`, the power is `0` and the bound reduces to
`(‖h x‖ + |C|) * ‖v x‖`, with the convention `0^0 = 1`. -/
theorem MemLp.integrable_rpow_growth_bound {u : α → E} {v : α → F}
    (hu : MemLp u p μ) (hv : MemLp v p μ) (hp_top : p ≠ ∞)
    {h : α → ℝ} (hh : MemLp h q μ) (C : ℝ) :
    Integrable (fun x ↦
      (‖h x‖ + |C| * (‖u x‖ + ‖v x‖) ^ (p.toReal - 1)) * ‖v x‖) μ := by
  have hsum : MemLp (fun x ↦ ‖u x‖ + ‖v x‖) p μ := hu.norm.add hv.norm
  have hpower : MemLp (fun x ↦ (‖u x‖ + ‖v x‖) ^ (p.toReal - 1)) q μ := by
    apply MemLp.ae_eq (hf_Lp := hsum.norm_rpow_sub_one (q := q) hp_top)
    exact ae_of_all μ fun x ↦ by
      change ‖‖u x‖ + ‖v x‖‖ ^ (p.toReal - 1) =
        (‖u x‖ + ‖v x‖) ^ (p.toReal - 1)
      rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact (hh.norm.add (hpower.const_mul |C|)).integrable_mul hv.norm

/-- A jointly measurable map with growth `h + C |z|^(p-1)`,
where `h ∈ Lᵠ` and `1 ≤ p < ∞` has conjugate exponent `q`, sends `Lᵖ` to `Lᵠ`.
No continuity or finiteness of the measure is required. -/
theorem MemLp.comp_of_norm_rpow_sub_one_le
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {u : α → E} (hu : MemLp u p μ) (hp_top : p ≠ ∞)
    {a : α → E → F} {h : α → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1)) :
    MemLp (fun x ↦ a x (u x)) q μ := by
  refine (hh.add ((hu.norm_rpow_sub_one hp_top).const_mul C)).mono' ?_ ?_
  · exact (hmeas.comp_aemeasurable
      (aemeasurable_id.prodMk hu.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  · exact hgrowth.mono fun x hx ↦ hx (u x)

end MeasureTheory
