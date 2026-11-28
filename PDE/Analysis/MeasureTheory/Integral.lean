/-
Authors: Levent Alpöge, Tristan Buckmaster

The lemmas of this file come from modules of the Lean package of the paper
"Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where they were steps of longer proofs. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Data.List.GetD
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.UniformSpace.Uniformizable
public import PDE.Analysis.Calculus.FDeriv
public import PDE.Analysis.Lp.Functions
public import PDE.Analysis.MeasureTheory.Integrability
public import PDE.Analysis.MeasureTheory.IntervalIntegral
public import PDE.Analysis.MeasureTheory.Lintegral
public import PDE.Analysis.Topology.Compactness

set_option linter.style.header false

/-!
# Identities and bounds for integrals

The lemmas split an integral over a union or a sum, change variables by a translation or a dilation,
pull constants and linear maps out of an integral, and bound an integral by the integral of a bound.
The proofs use `integral_add`, `setIntegral_congr_fun`, `integral_mono` and dominated convergence.

## Main results

* `PDE.Analysis.integral_Icc_coe_addCircle`: For `g : AddCircle (1 : ℝ) → E` with values in a real
  normed space, the Bochner integral of `σ ↦ g ↑σ` over `Icc 0 1` equals the integral of `g` over
  the circle: `∫ σ in Icc 0 1, g ↑σ = ∫ t, g t`. There is no integrability hypothesis.
* `PDE.Analysis.setIntegral_Icc_prod_eq_sum_of_partition`: Let the closed intervals
  `Icc (lo s) (hi s)`, `s ∈ T`, with `T` a finite set, cover `Icc r₁ r₂`, satisfy `r₁ ≤ lo s` and
  `hi s ≤ r₂`, and overlap pairwise at most at endpoints (`hi s ≤ lo s'` or `hi s' ≤ lo s` for
  `s ≠ s'`). If `A ⊆ ℝ` is measurable and `f : ℝ × ℝ → ℂ` is integrable on `Icc r₁ r₂ ×ˢ A`, then
  `∫ p in Icc r₁ r₂ ×ˢ A, f p = ∑ s ∈ T, ∫ p in Icc (lo s) (hi s) ×ˢ A, f p`.
* `PDE.Analysis.setIntegral_prod_Icc_eq_sum_of_partition`: Let the closed intervals
  `Icc (lo s) (hi s)`, `s ∈ T`, with `T` a finite set, cover `Icc z₁ z₂`, satisfy `z₁ ≤ lo s` and
  `hi s ≤ z₂`, and overlap pairwise at most at endpoints (`hi s ≤ lo s'` or `hi s' ≤ lo s` for
  `s ≠ s'`). If `A ⊆ ℝ` is measurable and `f : ℝ × ℝ → ℂ` is integrable on `A ×ˢ Icc z₁ z₂`, then
  `∫ p in A ×ˢ Icc z₁ z₂, f p = ∑ s ∈ T, ∫ p in A ×ˢ Icc (lo s) (hi s), f p`.
* `PDE.Analysis.integral_mul_eq_neg_of_tendsto_bounded`: Passage to the limit in an integral
  identity on `ℝ × ℝ`. Let `F`, `G` be complex functions integrable on a measurable set `S`, let
  `u n`, `v n` be continuous real functions with `|u n p| ≤ C` and `|v n p| ≤ C` that vanish outside
  `S` for large `n`, and let `u n p` tend to `d p` for almost every `p` and `v n p` tend to `e p`
  for every `p`, where `d` and `e` vanish outside `S`; if `∫ p, u n p * F p = -∫ p, v n p * G p` for
  large `n`, then `∫ p, d p * F p = -∫ p, e p * G p`.
* `PDE.Analysis.integral_mul_const_mul_eq_neg`: For complex functions `A`, `B`, `c`, `d` on `ℝ × ℝ`
  and a complex constant `k`, if `∫ p, c p * A p = -∫ p, d p * B p` then
  `∫ p, c p * (k * A p) = -∫ p, d p * (k * B p)`. The constant `k` is taken out of both integrals.
* `PDE.Analysis.sq_enorm_integral_le_mul_lintegral_sq`: For every `f : ℝ → ℂ`, with no measurability
  hypothesis,
  `‖∫ θ in Ioo (-π) π, f θ‖ₑ ^ 2 ≤ ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo (-π) π, ‖f θ‖ₑ ^ 2`. When
  `f` is not almost everywhere strongly measurable on the interval, the integral on the left is zero
  by definition.
* `PDE.Analysis.abs_integral_le_of_le_mul`: A Cauchy-Schwarz bound for an integral: let
  `a b : X → ℝ` be almost everywhere measurable and pointwise nonnegative, and let `h : X → ℝ`
  satisfy `|h x| ≤ a x * b x` for almost every `x`. If `0 ≤ A`, `0 ≤ B`,
  `∫⁻ x, ENNReal.ofReal (a x ^ 2) ∂μ ≤ ENNReal.ofReal (A ^ 2)` and
  `∫⁻ x, ENNReal.ofReal (b x ^ 2) ∂μ ≤ ENNReal.ofReal (B ^ 2)`, then `|∫ x, h x ∂μ| ≤ A * B`.
* `PDE.Analysis.integral_mul_norm_sq_sum_of_orthonormal`: Parseval identity for a finite family
  `e k`, `k ∈ s`, of complex functions orthonormal for a real weight `ρ` and a measure `μ`. Suppose
  that for `k, k' ∈ s` the function `fun x ↦ (ρ x : ℂ) * (e k x * conj (e k' x))` is integrable with
  integral `1` if `k = k'` and `0` otherwise; then for all complex coefficients `a k`,
  `∫ x, ρ x * ‖∑ k ∈ s, a k * e k x‖ ^ 2 ∂μ = ∑ k ∈ s, ‖a k‖ ^ 2`.

There are 61 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff ENNReal

namespace PDE.Analysis

/-- A Cauchy-Schwarz bound for an integral: let `a b : X → ℝ` be almost everywhere measurable and
pointwise nonnegative, and let `h : X → ℝ` satisfy `|h x| ≤ a x * b x` for almost every `x`. If
`0 ≤ A`, `0 ≤ B`, `∫⁻ x, ENNReal.ofReal (a x ^ 2) ∂μ ≤ ENNReal.ofReal (A ^ 2)` and
`∫⁻ x, ENNReal.ofReal (b x ^ 2) ∂μ ≤ ENNReal.ofReal (B ^ 2)`, then `|∫ x, h x ∂μ| ≤ A * B`. The
proof bounds `|∫ x, h x ∂μ|` by the lower integral of `|h|` and applies Hölder's inequality with
both exponents equal to `2` to `a` and `b`. -/
theorem abs_integral_le_of_le_mul {X : Type*} [MeasurableSpace X] {μ : Measure X} {h a b : X → ℝ}
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ x, 0 ≤ b x)
    (hh : ∀ᵐ x ∂μ, |h x| ≤ a x * b x) {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∫⁻ x, ENNReal.ofReal (a x ^ 2) ∂μ ≤ ENNReal.ofReal (A ^ 2))
    (hB : ∫⁻ x, ENNReal.ofReal (b x ^ 2) ∂μ ≤ ENNReal.ofReal (B ^ 2)) :
    |∫ x, h x ∂μ| ≤ A * B := by
  have h1 : |∫ x, h x ∂μ| ≤ (∫⁻ x, ENNReal.ofReal ‖h x‖ ∂μ).toReal := by
    rw [← Real.norm_eq_abs]; exact norm_integral_le_lintegral_norm h
  have h2 : ∫⁻ x, ENNReal.ofReal ‖h x‖ ∂μ ≤ ∫⁻ x, ((fun x ↦ ENNReal.ofReal (a x)) * fun x ↦
      ENNReal.ofReal (b x)) x ∂μ := by
    refine lintegral_mono_ae (hh.mono fun x hx ↦ ?_)
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (ha0 x), Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal hx
  have h3 := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two ha.ennreal_ofReal
      hb.ennreal_ofReal
  have e : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t ^ (2 : ℝ) = ENNReal.ofReal (t ^ 2) := fun t ht ↦ by
    rw [ENNReal.ofReal_rpow_of_nonneg ht (by norm_num)]
    norm_cast
  have hA' : (∫⁻ x, ENNReal.ofReal (a x) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal A := by
    rw [lintegral_congr fun x ↦ e _ (ha0 x)]
    calc (∫⁻ x, ENNReal.ofReal (a x ^ 2) ∂μ) ^ (1 / (2 : ℝ)) ≤
             ENNReal.ofReal (A ^ 2) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow hA (by norm_num)
      _ = ENNReal.ofReal A := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
            Real.sqrt_sq hA0]
  have hB' : (∫⁻ x, ENNReal.ofReal (b x) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal B := by
    rw [lintegral_congr fun x ↦ e _ (hb0 x)]
    calc (∫⁻ x, ENNReal.ofReal (b x ^ 2) ∂μ) ^ (1 / (2 : ℝ)) ≤
             ENNReal.ofReal (B ^ 2) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow hB (by norm_num)
      _ = ENNReal.ofReal B := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
            Real.sqrt_sq hB0]
  have h4 : ∫⁻ x, ENNReal.ofReal ‖h x‖ ∂μ ≤ ENNReal.ofReal (A * B) := by
    rw [ENNReal.ofReal_mul hA0]
    exact h2.trans (h3.trans (mul_le_mul' hA' hB'))
  refine h1.trans ?_
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h4
  rwa [ENNReal.toReal_ofReal (mul_nonneg hA0 hB0)] at this

/-- Let `f ι : α → ℝ`, for `ι : ℤ × ℤ`, be integrable for a measure `μ`, with `ι ↦ ∫ a, ‖f ι a‖ ∂μ`
summable. Then `ι ↦ f ι a` is summable for almost every `a`, the function `a ↦ ∑' ι, f ι a` is
integrable, and `∫ a, ∑' ι, f ι a ∂μ = ∑' ι, ∫ a, f ι a ∂μ`. The proof shows that
`∑' ι, ∫⁻ a, ‖f ι a‖ₑ ∂μ` is finite, which gives summability almost everywhere and bounds the lower
integral of the norm of the sum. -/
theorem ae_summable_integrable_integral_tsum {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℤ × ℤ → α → ℝ}
    (hi : ∀ ι, Integrable (f ι) μ) (hs : Summable fun ι ↦ ∫ a, ‖f ι a‖ ∂μ) :
    (∀ᵐ a ∂μ, Summable fun ι ↦ f ι a) ∧ Integrable (fun a ↦ ∑' ι, f ι a) μ ∧
      ∫ a, ∑' ι, f ι a ∂μ = ∑' ι, ∫ a, f ι a ∂μ := by
  have hl : ∀ ι, ∫⁻ a, ‖f ι a‖ₑ ∂μ = ENNReal.ofReal (∫ a, ‖f ι a‖ ∂μ) := fun ι ↦
    (ofReal_integral_norm_eq_lintegral_eNorm (hi ι)).symm
  have hfin : ∑' ι, ∫⁻ a, ‖f ι a‖ₑ ∂μ ≠ ⊤ := by
    rw [tsum_congr hl, ← ENNReal.ofReal_tsum_of_nonneg (fun ι ↦ integral_nonneg fun a ↦
        norm_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  have hm : ∀ ι, AEMeasurable (fun a ↦ ‖f ι a‖ₑ) μ := fun ι ↦ (hi ι).1.eNorm
  have hlt : ∀ᵐ a ∂μ, ∑' ι, ‖f ι a‖ₑ < ⊤ := by
    refine ae_lt_top' (AEMeasurable.tsum hm) ?_
    rwa [lintegral_tsum hm]
  have hsum : ∀ᵐ a ∂μ, Summable fun ι ↦ f ι a := by
    filter_upwards [hlt] with a ha
    exact (tsum_eNorm_ne_top_iff_summable_norm.1 ha.ne).of_norm
  have hmeas : AEStronglyMeasurable (fun a ↦ ∑' ι, f ι a) μ := by
    refine aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (f := fun (s : Finset (ℤ × ℤ)) a ↦ ∑ ι ∈ s, f ι a)
      (fun s ↦ Finset.aestronglyMeasurable_fun_sum _ fun ι _ ↦ (hi ι).1) ?_
    filter_upwards [hsum] with a ha
    exact ha.hasSum
  refine ⟨hsum, ⟨hmeas, ?_⟩, integral_tsum (fun ι ↦ (hi ι).1) hfin⟩
  unfold HasFiniteIntegral
  calc ∫⁻ a, ‖∑' ι, f ι a‖ₑ ∂μ ≤ ∫⁻ a, ∑' ι, ‖f ι a‖ₑ ∂μ :=
           lintegral_mono fun a ↦ eNorm_tsum_le_tsum_eNorm
    _ = ∑' ι, ∫⁻ a, ‖f ι a‖ₑ ∂μ := lintegral_tsum hm
    _ < ⊤ := lt_top_iff_ne_top.2 hfin

/-- If `f : ℝ × ℝ → ℂ` satisfies `(starRingEnd ℂ) (f p) = f p` for all `p`, then
`(starRingEnd ℂ) (∫ p in s, f p) = ∫ p in s, f p` for every set `s`. In words, the integral of a
function fixed by complex conjugation is fixed by complex conjugation. -/
theorem conj_setIntegral_eq (s : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℂ)
    (hf : ∀ p, starRingEnd ℂ (f p) = f p) :
    starRingEnd ℂ (∫ p in s, f p) = ∫ p in s, f p := by
  rw [← integral_conj]
  congr 1
  funext p
  exact hf p

/-- Let `s` be a measurable set in `ℝ × ℝ`, let `p ↦ p.1 * S p` be integrable on `s`, and let
`f : ℝ × ℝ → ℝ` be almost everywhere strongly measurable on `s`. If `‖f p‖ ≤ M * (p.1 * S p)` for
all `p ∈ s`, then `f` is integrable on `s` and `‖∫ p in s, f p‖ ≤ M * ∫ p in s, p.1 * S p`. -/
theorem integrableOn_and_norm_setIntegral_le_of_le {f : ℝ × ℝ → ℝ} {S : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) {M : ℝ}
    (hS : IntegrableOn (fun p ↦ p.1 * S p) s) (hf : AEStronglyMeasurable f (volume.restrict s))
    (hb : ∀ p ∈ s, ‖f p‖ ≤ M * (p.1 * S p)) :
    IntegrableOn f s ∧ ‖∫ p in s, f p‖ ≤ M * ∫ p in s, p.1 * S p := by
  have hg : Integrable (fun p ↦ M * (p.1 * S p)) (volume.restrict s) := hS.const_mul M
  have hae : ∀ᵐ p ∂(volume.restrict s), ‖f p‖ ≤ M * (p.1 * S p) :=
    (ae_restrict_iff' hs).2 (Filter.Eventually.of_forall hb)
  refine ⟨hg.mono' hf hae, ?_⟩
  calc ‖∫ p in s, f p‖ ≤ ∫ p in s, M * (p.1 * S p) := norm_integral_le_of_norm_le hg hae
    _ = M * ∫ p in s, p.1 * S p := integral_const_mul M _

/-- Linearity of the Bochner integral for one combination of six terms: if the real functions `f1`,
`f2`, `f4`, `f5`, every `f3 i` with `i ∈ s` and every `f6 l` with `l ∈ t` are integrable, then
`z ↦ f1 z + f2 z + (∑ i ∈ s, a i * f3 i z) + f4 z - c * f5 z + ∑ l ∈ t, b l * f6 l
z` is integrable, and its integral is `(∫ z, f1 z ∂μ) + (∫ z, f2 z ∂μ) + (∑ i ∈ s, a i * ∫ z, f3 i z
∂μ) + (∫ z, f4 z ∂μ) - c * (∫ z, f5 z ∂μ) + ∑ l ∈ t, b l * ∫ z, f6 l z
∂μ`. The proof adds the terms one at a time. -/
theorem integrable_and_integral_six_terms {α ι κ : Type*} [MeasurableSpace α] {μ : Measure α}
    {f1 f2 f4 f5 : α → ℝ}
    {f3 : ι → α → ℝ} {f6 : κ → α → ℝ} (s : Finset ι) (t : Finset κ) (a : ι → ℝ) (b : κ → ℝ) (c : ℝ)
    (h1 : Integrable f1 μ) (h2 : Integrable f2 μ) (h3 : ∀ i ∈ s, Integrable (f3 i) μ)
        (h4 : Integrable f4 μ)
    (h5 : Integrable f5 μ) (h6 : ∀ l ∈ t, Integrable (f6 l) μ) :
    Integrable (fun z ↦ f1 z + f2 z + (∑ i ∈ s, a i * f3 i z) + f4 z - c * f5 z + ∑ l ∈ t,
        b l * f6 l z) μ ∧
    ∫ z, (f1 z + f2 z + (∑ i ∈ s, a i * f3 i z) + f4 z - c * f5 z + ∑ l ∈ t, b l * f6 l z) ∂μ =
      (∫ z, f1 z ∂μ) + (∫ z, f2 z ∂μ) + (∑ i ∈ s, a i * ∫ z, f3 i z ∂μ) + (∫ z, f4 z ∂μ) - c *
          (∫ z, f5 z ∂μ)
        + ∑ l ∈ t, b l * ∫ z, f6 l z ∂μ := by
  have i3 : Integrable (fun z ↦ ∑ i ∈ s, a i * f3 i z) μ :=
    integrable_finsetSum s fun i hi ↦ (h3 i hi).const_mul (a i)
  have i6 : Integrable (fun z ↦ ∑ l ∈ t, b l * f6 l z) μ :=
    integrable_finsetSum t fun l hl ↦ (h6 l hl).const_mul (b l)
  have i5 : Integrable (fun z ↦ c * f5 z) μ := h5.const_mul c
  have i12 : Integrable (fun z ↦ f1 z + f2 z) μ := h1.add h2
  have i123 : Integrable (fun z ↦ f1 z + f2 z + ∑ i ∈ s, a i * f3 i z) μ := i12.add i3
  have i1234 : Integrable (fun z ↦ f1 z + f2 z + (∑ i ∈ s, a i * f3 i z) + f4 z) μ := i123.add h4
  have i12345 : Integrable (fun z ↦ f1 z + f2 z + (∑ i ∈ s, a i * f3 i z) + f4 z - c * f5 z) μ :=
      i1234.sub i5
  refine ⟨i12345.add i6, ?_⟩
  rw [integral_add i12345 i6, integral_sub i1234 i5, integral_add i123 h4, integral_add i12 i3,
    integral_add h1 h2, integral_finsetSum s (fun i hi ↦ (h3 i hi).const_mul (a i)),
    integral_finsetSum t (fun l hl ↦ (h6 l hl).const_mul (b l)), integral_const_mul]
  simp only [integral_const_mul]

/-- For `g : AddCircle (1 : ℝ) → E` with values in a real normed space, the Bochner integral of
`σ ↦ g ↑σ` over `Icc 0 1` equals the integral of `g` over the circle:
`∫ σ in Icc 0 1, g ↑σ = ∫ t, g t`. There is no integrability hypothesis. -/
theorem integral_Icc_coe_addCircle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : AddCircle (1 : ℝ) → E) :
    ∫ σ in Set.Icc (0 : ℝ) 1, g (σ : AddCircle (1 : ℝ)) = ∫ t, g t := by
  have h := AddCircle.integral_preimage 1 0 g
  rw [zero_add] at h
  rw [← h, Measure.restrict_congr_set Ioc_ae_eq_Icc]

/-- Let `a b c : ℝ × ℝ → ℝ` be integrable for a measure `μ`. If `a p + 2 * b p + 2 * c p = f p` for
almost every `p`, then `∫ p, a p ∂μ + 2 * ∫ p, b p ∂μ + 2 * ∫ p, c p ∂μ = ∫ p, f p ∂μ`. -/
theorem integral_add_add_eq_of_ae_eq {μ : Measure (ℝ × ℝ)} {a b c f : ℝ × ℝ → ℝ}
    (ia : Integrable a μ) (ib : Integrable b μ)
    (ic : Integrable c μ) (h : ∀ᵐ p ∂μ, a p + 2 * b p + 2 * c p = f p) :
    ∫ p, a p ∂μ + 2 * ∫ p, b p ∂μ + 2 * ∫ p, c p ∂μ = ∫ p, f p ∂μ := by
  have ib2 : Integrable (fun p ↦ 2 * b p) μ := ib.const_mul 2
  have ic2 : Integrable (fun p ↦ 2 * c p) μ := ic.const_mul 2
  have iab : Integrable (fun p ↦ a p + 2 * b p) μ := ia.add ib2
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add ia ib2, ← integral_add iab ic2]
  exact integral_congr_ae h

/-- For complex functions `f g h` integrable on a set `s` in `ℝ × ℝ`,
`∫ p in s, (f p + g p + h p) = (∫ p in s, f p) + (∫ p in s, g p) + ∫ p in s, h p`. -/
theorem integral_add_three {s : Set (ℝ × ℝ)} {f g h : ℝ × ℝ → ℂ} (hf : IntegrableOn f s)
    (hg : IntegrableOn g s)
    (hh : IntegrableOn h s) :
    ∫ p in s, (f p + g p + h p) = (∫ p in s, f p) + (∫ p in s, g p) + ∫ p in s, h p := by
  have e1 := integral_add (Integrable.add hf hg) hh
  have e2 := integral_add hf hg
  simp only [Pi.add_apply] at e1
  rw [e1, e2]

/-- For twelve functions `a1` to `a12` from `ℝ × ℝ` to `ℝ`, all integrable for a measure `μ`, the
integral of the sum
`a1 p + a2 p + a3 p + a4 p + a5 p + a6 p + a7 p + a8 p + a9 p + a10 p + a11 p + a12
p` equals the sum of the twelve integrals `∫ p, a1 p ∂μ` to `∫ p, a12 p
∂μ`. The proof applies additivity of the integral eleven times. -/
theorem integral_add_twelve {μ : Measure (ℝ × ℝ)}
    {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : ℝ × ℝ → ℝ}
    (h1 : Integrable a1 μ) (h2 : Integrable a2 μ) (h3 : Integrable a3 μ) (h4 : Integrable a4 μ)
        (h5 : Integrable a5 μ) (h6 : Integrable a6 μ) (h7 : Integrable a7 μ) (h8 : Integrable a8 μ)
            (h9 : Integrable a9 μ) (h10 : Integrable a10 μ) (h11 : Integrable a11 μ)
                (h12 : Integrable a12 μ) :
    ∫ p, (a1 p + a2 p + a3 p + a4 p + a5 p + a6 p + a7 p + a8 p + a9 p + a10 p + a11 p + a12 p) ∂μ
      = ∫ p, a1 p ∂μ + ∫ p, a2 p ∂μ + ∫ p, a3 p ∂μ + ∫ p, a4 p ∂μ + ∫ p, a5 p ∂μ + ∫ p,
          a6 p ∂μ + ∫ p, a7 p ∂μ + ∫ p, a8 p ∂μ + ∫ p, a9 p ∂μ + ∫ p, a10 p ∂μ + ∫ p,
              a11 p ∂μ + ∫ p, a12 p ∂μ := by
  have g2 : Integrable (fun p ↦ a1 p + a2 p) μ := h1.add h2
  have g3 : Integrable (fun p ↦ a1 p + a2 p + a3 p) μ := g2.add h3
  have g4 : Integrable (fun p ↦ a1 p + a2 p + a3 p + a4 p) μ := g3.add h4
  have g5 : Integrable (fun p ↦ a1 p + a2 p + a3 p + a4 p + a5 p) μ := g4.add h5
  have g6 : Integrable (fun p ↦ a1 p + a2 p + a3 p + a4 p + a5 p + a6 p) μ := g5.add h6
  have g7 : Integrable (fun p ↦ a1 p + a2 p + a3 p + a4 p + a5 p + a6 p + a7 p) μ := g6.add h7
  have g8 : Integrable (fun p ↦ a1 p + a2 p + a3 p + a4 p + a5 p + a6 p + a7 p + a8 p) μ :=
      g7.add h8
  have g9 : Integrable (fun p ↦ a1 p + a2 p + a3 p + a4 p + a5 p + a6 p + a7 p + a8 p + a9 p) μ :=
      g8.add h9
  have g10 : Integrable (fun p ↦ a1 p + a2 p + a3 p + a4 p + a5 p + a6 p + a7 p + a8 p + a9 p +
      a10 p) μ := g9.add h10
  have g11 : Integrable (fun p ↦ a1 p + a2 p + a3 p + a4 p + a5 p + a6 p + a7 p + a8 p + a9 p +
      a10 p + a11 p) μ := g10.add h11
  rw [integral_add g11 h12, integral_add g10 h11, integral_add g9 h10, integral_add g8 h9,
      integral_add g7 h8, integral_add g6 h7, integral_add g5 h6, integral_add g4 h5,
          integral_add g3 h4, integral_add g2 h3, integral_add h1 h2]

/-- For `a b c : ℝ × ℝ → ℝ` integrable for a measure `μ`,
`∫ p, (a p + 2 * b p + 2 * c p) ∂μ = ∫ p, a p ∂μ + 2 * ∫ p, b p ∂μ + 2 * ∫ p, c p ∂μ`. -/
theorem integral_add_two_mul_add_two_mul {μ : Measure (ℝ × ℝ)} {a b c : ℝ × ℝ → ℝ}
    (ha : Integrable a μ) (hb : Integrable b μ)
    (hc : Integrable c μ) :
    ∫ p, (a p + 2 * b p + 2 * c p) ∂μ = ∫ p, a p ∂μ + 2 * ∫ p, b p ∂μ + 2 * ∫ p, c p ∂μ := by
  have h2 : Integrable (fun p ↦ 2 * b p) μ := hb.const_mul 2
  have h3 : Integrable (fun p ↦ 2 * c p) μ := hc.const_mul 2
  have h12 : Integrable (fun p ↦ a p + 2 * b p) μ := ha.add h2
  rw [integral_add h12 h3, integral_add ha h2, integral_const_mul, integral_const_mul]

/-- Let `a b : ℝ × ℝ → ℝ` be integrable for a measure `μ`. If `a p + 2 * b p = f p` for all `p`,
then `∫ p, a p ∂μ + 2 * ∫ p, b p ∂μ = ∫ p, f p ∂μ`. -/
theorem integral_add_two_mul_eq_of_eq {μ : Measure (ℝ × ℝ)} {a b f : ℝ × ℝ → ℝ}
    (ia : Integrable a μ) (ib : Integrable b μ)
    (h : ∀ p, a p + 2 * b p = f p) : ∫ p, a p ∂μ + 2 * ∫ p, b p ∂μ = ∫ p, f p ∂μ := by
  have ib2 : Integrable (fun p ↦ 2 * b p) μ := ib.const_mul 2
  rw [← integral_const_mul, ← integral_add ia ib2]
  exact integral_congr_ae (ae_of_all _ h)

/-- Integration by parts against a primitive: if `θ : ℝ → ℝ` is smooth with compact support and
`bt : ℝ → ℝ` is integrable and vanishes on `Set.Iic l`, then
`∫ t, deriv θ t * ∫ τ in l..t, bt τ = -∫ t, θ t * bt t`. The primitive is written as
`∫ τ in Set.Iic t, bt τ`, the two integrals are exchanged with Fubini's theorem, and
`∫ t in Set.Ici τ, deriv θ t = -θ τ` is used. -/
theorem integral_deriv_mul_primitive {θ bt : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθc : HasCompactSupport θ) (hb : Integrable bt) (l : ℝ) (hbl : ∀ τ, τ ≤ l → bt τ = 0) :
    ∫ t, deriv θ t * ∫ τ in l..t, bt τ = -∫ t, θ t * bt t := by
  have hprim : ∀ t, ∫ τ in l..t, bt τ = ∫ τ in Iic t, bt τ := by
    intro t
    rw [← intervalIntegral.integral_Iic_sub_Iic hb.integrableOn hb.integrableOn,
      setIntegral_eq_zero_of_forall_eq_zero (t := Iic l) (fun x hx ↦ hbl x hx), sub_zero]
  have hi : Integrable (deriv θ) :=
    (hθ.continuous_deriv (by simp)).integrable_of_hasCompactSupport hθc.deriv
  set f : ℝ × ℝ → ℝ := Set.indicator {p : ℝ × ℝ | p.2 ≤ p.1}
    (fun p ↦ deriv θ p.1 * bt p.2) with hf
  have hfi : Integrable f (volume.prod volume) :=
    (hi.mul_prod hb).indicator (measurableSet_le measurable_snd measurable_fst)
  have e1 : ∀ t, deriv θ t * ∫ τ in l..t, bt τ = ∫ τ, f (t, τ) := by
    intro t
    rw [hprim, ← integral_const_mul, ← integral_indicator measurableSet_Iic]
    congr 1
  have e2 : ∀ τ, ∫ t, f (t, τ) = -(θ τ * bt τ) := by
    intro τ
    have : (fun t ↦ f (t, τ)) = Set.indicator (Ici τ) (fun t ↦ deriv θ t * bt τ) := by
      funext t
      simp only [hf, Set.indicator_apply, mem_ofPred_eq, mem_Ici]
    rw [this, integral_indicator measurableSet_Ici, integral_mul_const,
        integral_Ici_deriv_of_hasCompactSupport hθ hθc]
    ring
  simp_rw [e1]
  rw [integral_integral_swap (f := fun t τ ↦ f (t, τ)) hfi]
  simp_rw [e2]
  rw [integral_neg]

/-- Integration by parts against a primitive on the real line. If `B : ℝ → ℂ` is locally integrable
and `χ : ℝ → ℝ` is smooth with compact support, then
`∫ z, deriv χ z • (∫ u in 0..z, B u) = -∫ z, χ z • B z`. The proof restricts both integrals to an
interval `Icc (-R) R` containing the support of `χ` and integrates by parts there. -/
theorem integral_deriv_smul_primitive_eq_neg {B : ℝ → ℂ} (hB : LocallyIntegrable B volume)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) :
    ∫ z, deriv χ z • (∫ u in (0 : ℝ)..z, B u) = -∫ z, χ z • B z := by
  obtain ⟨R, hR0, hR⟩ := exists_pos_tsupport_subset_Ioo_neg hc
  have hχ0 : ∀ z, z ∉ Ioo (-R) R → χ z = 0 := fun z hz ↦
    image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hR h))
  have hd0 : ∀ z, z ∉ Icc (-R) R → deriv χ z = 0 := fun z hz ↦
    image_eq_zero_of_notMem_tsupport (fun h ↦ hz (Ioo_subset_Icc_self
        (hR (tsupport_deriv_subset h))))
  have hC1 : ContDiff ℝ 1 χ := hχ.of_le (by exact_mod_cast le_top)
  have hdc : Continuous (deriv χ) := hC1.continuous_deriv le_rfl
  have L1 : ∫ z, deriv χ z • (∫ u in (0 : ℝ)..z, B u) = ∫ z in Icc (-R) R,
      deriv χ z • (∫ u in (0 : ℝ)..z, B u) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz ↦ by simp [hd0 z hz])).symm
  have L2 : ∫ z, χ z • B z = ∫ z in Icc (-R) R, χ z • B z :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz ↦ by simp [hχ0 z (fun h ↦ hz (Ioo_subset_Icc_self h))])).symm
  rw [L1, L2]
  have hBI : IntegrableOn B (Icc (-R) R) := hB.integrableOn_isCompact isCompact_Icc
  have hR' : -R ≤ R := by linarith
  have hPc : Continuous (fun z ↦ ∫ u in (-R)..z, B u) :=
      intervalIntegral.continuous_primitive (intervalIntegrable_of_locallyIntegrable hB) _
  have e : ∀ z, deriv χ z • (∫ u in (0 : ℝ)..z, B u) =
      (∫ u in (-R)..z, B u) * ((deriv χ z : ℝ) : ℂ) - (∫ u in (-R)..0, B u) *
          ((deriv χ z : ℝ) : ℂ) := by
    intro z
    rw [← intervalIntegral.integral_interval_sub_left (intervalIntegrable_of_locallyIntegrable hB _
        _) (intervalIntegrable_of_locallyIntegrable hB _ _), Complex.real_smul]
    ring
  simp_rw [e]
  have hdC : Continuous (fun z ↦ ((deriv χ z : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hdc
  have j1 : IntegrableOn (fun z ↦ (∫ u in (-R)..z, B u) * ((deriv χ z : ℝ) : ℂ)) (Icc (-R) R) :=
    (hPc.mul hdC).continuousOn.integrableOn_compact isCompact_Icc
  have j2 : IntegrableOn (fun z ↦ (∫ u in (-R)..0, B u) * ((deriv χ z : ℝ) : ℂ)) (Icc (-R) R) :=
    (continuous_const.mul hdC).continuousOn.integrableOn_compact isCompact_Icc
  rw [integral_sub j1 j2,
    setIntegral_primitive_mul_deriv_eq_neg hBI hC1 (hχ0 R (fun h ↦ lt_irrefl _ h.2)),
        integral_const_mul]
  have hz : ∫ z in Icc (-R) R, ((deriv χ z : ℝ) : ℂ) = 0 := by
    rw [integral_complex_ofReal, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hR',
      intervalIntegral.integral_deriv_eq_sub' χ rfl (fun x _ ↦
          (hC1.differentiable one_ne_zero).differentiableAt)
        hdc.continuousOn, hχ0 R (fun h ↦ lt_irrefl _ h.2), hχ0 (-R) (fun h ↦ lt_irrefl _ h.1)]
    simp
  rw [hz, mul_zero, sub_zero]
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc (fun z _ ↦ ?_)
  rw [Complex.real_smul, mul_comm]

/-- Let `g : ℝ × ℝ → ℝ` be `C^1`, let `W₁`, `W₂` be `C^1` on an open set `U` that contains the box
`Icc (a₁, a₂) (b₁, b₂)`, where `a₁ ≤ b₁` and `a₂ ≤ b₂`, and for `x ∈ U` let `D₁ x` be the derivative
of `fun t ↦ W₁ (t, x.2)` at `x.1` and `D₂ x` the derivative of `fun t ↦ W₂ (x.1, t)` at `x.2`.
Then `fun x ↦ 2 * g x * (fderiv ℝ g x (1, 0) * W₁ x + fderiv ℝ g x (0, 1) * W₂ x) +
g x ^ 2 * (D₁ x + D₂ x)` is integrable on the box, and its integral over the box equals
`(((∫ t in a₁..b₁, g (t, b₂) ^ 2 * W₂ (t, b₂)) - ∫ t in a₁..b₁, g (t, a₂) ^ 2 * W₂ (t, a₂)) +
∫ t in a₂..b₂, g (b₁, t) ^ 2 * W₁ (b₁, t)) - ∫ t in a₂..b₂, g (a₁, t) ^ 2 * W₁ (a₁,
t)`. The proof recognizes the integrand as the divergence of `(g ^ 2 * W₁, g ^ 2 *
W₂)` and applies the divergence theorem on a rectangle. -/
theorem integral_divergence_sq_mul_prod_Icc {g W₁ W₂ D₁ D₂ : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U)
    (hg : ContDiff ℝ 1 g) (hW₁ : ContDiffOn ℝ 1 W₁ U) (hW₂ : ContDiffOn ℝ 1 W₂ U)
    (hD₁ : ∀ x ∈ U, HasDerivAt (fun t ↦ W₁ (t, x.2)) (D₁ x) x.1)
    (hD₂ : ∀ x ∈ U, HasDerivAt (fun t ↦ W₂ (x.1, t)) (D₂ x) x.2)
    {a₁ a₂ b₁ b₂ : ℝ} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (hsub : Icc (a₁, a₂) (b₁, b₂) ⊆ U) :
    IntegrableOn (fun x ↦ 2 * g x * (fderiv ℝ g x (1, 0) * W₁ x + fderiv ℝ g x (0, 1) * W₂ x)
        + g x ^ 2 * (D₁ x + D₂ x)) (Icc (a₁, a₂) (b₁, b₂)) ∧
    ∫ x in Icc (a₁, a₂) (b₁, b₂), (2 * g x * (fderiv ℝ g x (1, 0) * W₁ x + fderiv ℝ g x (0, 1) *
        W₂ x)
        + g x ^ 2 * (D₁ x + D₂ x)) =
      (((∫ t in a₁..b₁, g (t, b₂) ^ 2 * W₂ (t, b₂)) - ∫ t in a₁..b₁, g (t, a₂) ^ 2 * W₂ (t, a₂))
        + ∫ t in a₂..b₂, g (b₁, t) ^ 2 * W₁ (b₁, t)) - ∫ t in a₂..b₂, g (a₁, t) ^ 2 * W₁ (a₁, t) :=
            by
  have hF₁ : ContDiffOn ℝ 1 (fun x ↦ g x ^ 2 * W₁ x) U := (hg.contDiffOn.pow 2).mul hW₁
  have hF₂ : ContDiffOn ℝ 1 (fun x ↦ g x ^ 2 * W₂ x) U := (hg.contDiffOn.pow 2).mul hW₂
  have hd₁ : ∀ x ∈ U, DifferentiableAt ℝ (fun x ↦ g x ^ 2 * W₁ x) x := fun x hx ↦
    (hF₁.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)
  have hd₂ : ∀ x ∈ U, DifferentiableAt ℝ (fun x ↦ g x ^ 2 * W₂ x) x := fun x hx ↦
    (hF₂.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have heq : ∀ x ∈ U, fderiv ℝ (fun x ↦ g x ^ 2 * W₁ x) x (1, 0)
      + fderiv ℝ (fun x ↦ g x ^ 2 * W₂ x) x (0, 1)
      = 2 * g x * (fderiv ℝ g x (1, 0) * W₁ x + fderiv ℝ g x (0, 1) * W₂ x)
        + g x ^ 2 * (D₁ x + D₂ x) := by
    intro x hx
    rw [fderiv_apply_one_zero_eq_of_hasDerivAt (hd₁ x hx)
        (((hasDerivAt_comp_prodMk_left_fderiv hgd x).pow 2).mul (hD₁ x hx)),
      fderiv_apply_zero_one_eq_of_hasDerivAt (hd₂ x hx)
          (((hasDerivAt_comp_prodMk_right_fderiv hgd x).pow 2).mul (hD₂ x hx))]
    norm_num
    ring
  have hi : IntegrableOn (fun x ↦ fderiv ℝ (fun x ↦ g x ^ 2 * W₁ x) x (1, 0)
      + fderiv ℝ (fun x ↦ g x ^ 2 * W₂ x) x (0, 1)) (Icc (a₁, a₂) (b₁, b₂)) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc (ContinuousOn.mono ?_ hsub)
    exact ((hF₁.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const).add
      ((hF₂.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const)
  have hcongr := setIntegral_congr_fun (μ := volume) measurableSet_Icc (fun x hx ↦ heq x (hsub hx))
  refine ⟨hi.congr_fun (fun x hx ↦ heq x (hsub hx)) measurableSet_Icc, ?_⟩
  rw [← hcongr]
  have hint : ∀ x ∈ Ioo a₁ b₁ ×ˢ Ioo a₂ b₂ \ (∅ : Set (ℝ × ℝ)), x ∈ U := fun x hx ↦
    hsub ⟨⟨hx.1.1.1.le, hx.1.2.1.le⟩, ⟨hx.1.1.2.le, hx.1.2.2.le⟩⟩
  exact integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le _ _ _ _ (a₁, a₂) (b₁, b₂)
    ⟨h₁, h₂⟩ ∅ countable_empty (hF₁.continuousOn.mono hsub) (hF₂.continuousOn.mono hsub)
    (fun x hx ↦ (hd₁ x (hint x hx)).hasFDerivAt) (fun x hx ↦ (hd₂ x (hint x hx)).hasFDerivAt) hi

/-- Let `s` and `t` be finite sets of pairs of integers and let `f i j : ℝ × ℝ → ℝ` be integrable
for a measure `μ` for all `i ∈ s` and `j ∈ t`. Then
`∫ p, ∑ i ∈ s, ∑ j ∈ t, f i j p ∂μ = ∑ i ∈ s, ∑ j ∈ t, ∫ p, f i j p ∂μ`. -/
theorem integral_double_sum {μ : Measure (ℝ × ℝ)} (s t : Finset (ℤ × ℤ))
    (f : ℤ × ℤ → ℤ × ℤ → ℝ × ℝ → ℝ)
    (hf : ∀ i ∈ s, ∀ j ∈ t, Integrable (f i j) μ) :
    ∫ p, ∑ i ∈ s, ∑ j ∈ t, f i j p ∂μ = ∑ i ∈ s, ∑ j ∈ t, ∫ p, f i j p ∂μ := by
  rw [integral_finsetSum _ fun i hi ↦ integrable_finsetSum _ fun j hj ↦ hf i hi j hj]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [integral_finsetSum _ fun j hj ↦ hf i hi j hj]

/-- Let `fc fs gc gs : ℝ × ℝ → ℂ` be integrable for a measure `μ`, and let
`f p = fc p + Complex.I * fs p` and `g p = gc p + Complex.I * gs p` for almost every `p`. If
`∫ p, fc p ∂μ = -∫ p, gc p ∂μ` and `∫ p, fs p ∂μ = -∫ p, gs p ∂μ`, then
`∫ p, f p ∂μ = -∫ p, g p ∂μ`. -/
theorem integral_eq_neg_of_add_I_mul {μ : Measure (ℝ × ℝ)} {f g fc fs gc gs : ℝ × ℝ → ℂ}
    (hf : ∀ᵐ p ∂μ, f p = fc p + Complex.I * fs p) (hg : ∀ᵐ p ∂μ, g p = gc p + Complex.I * gs p)
    (hfc : Integrable fc μ) (hfs : Integrable fs μ) (hgc : Integrable gc μ) (hgs : Integrable gs μ)
    (hc : ∫ p, fc p ∂μ = -∫ p, gc p ∂μ) (hs : ∫ p, fs p ∂μ = -∫ p, gs p ∂μ) :
    ∫ p, f p ∂μ = -∫ p, g p ∂μ := by
  rw [integral_congr_ae hf, integral_congr_ae hg, integral_add hfc (hfs.const_mul _),
    integral_add hgc (hgs.const_mul _), integral_const_mul, integral_const_mul, hc, hs]
  ring

/-- Let `S` be a measurable set of `ℝ × ℝ` and `F`, `G : ℝ × ℝ → ℂ`. If `F p = S.indicator G p` for
almost every `p`, then `∫ p, F p = ∫ p in S, G p`. -/
theorem integral_eq_setIntegral_of_ae_eq_indicator {F G : ℝ × ℝ → ℂ} {S : Set (ℝ × ℝ)}
    (hS : MeasurableSet S)
    (h : ∀ᵐ p, F p = S.indicator G p) : ∫ p, F p = ∫ p in S, G p := by
  rw [← integral_indicator hS]
  exact integral_congr_ae h

/-- If the topological support of `ψ : ℝ → ℝ` is contained in a set `S`, then for every `F : ℝ → ℂ`,
`∫ x, F x * (ψ x : ℂ) = ∫ x in S, F x * (ψ x : ℂ)`. -/
theorem integral_eq_setIntegral_of_tsupport {F : ℝ → ℂ} {ψ : ℝ → ℝ} {S : Set ℝ}
    (hs : tsupport ψ ⊆ S) :
    ∫ x, F x * ((ψ x : ℝ) : ℂ) = ∫ x in S, F x * ((ψ x : ℝ) : ℂ) := by
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_).symm
  rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))]
  simp

/-- Let `ψ : ℝ × ℝ → ℝ` have topological support inside the interior of a set `R`, and let
`G Gz : ℝ × ℝ → ℂ`. If `∫ p in R, G p * (fderiv ℝ ψ p (0, 1) : ℂ) = -∫ p in R, Gz p * (ψ p : ℂ)`,
then `∫ p, (fderiv ℝ ψ p (0, 1) : ℂ) * G p = -∫ p, (ψ p : ℂ) * Gz p`. The proof uses that `ψ` and
its derivative vanish outside `R`. -/
theorem integral_fderiv_mul_eq_neg_of_setIntegral {G Gz : ℝ × ℝ → ℂ} {R : Set (ℝ × ℝ)}
    {ψ : ℝ × ℝ → ℝ}
    (ht : tsupport ψ ⊆ interior R)
    (hw : ∫ p in R, G p * Complex.ofReal (fderiv ℝ ψ p (0, 1)) = -∫ p in R,
        Gz p * Complex.ofReal (ψ p)) :
    ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * G p = -∫ p, (ψ p : ℂ) * Gz p := by
  have hout : ∀ p, p ∉ R → p ∉ tsupport ψ := fun p hp hm ↦ hp (interior_subset (ht hm))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp ↦ by
      rw [fderiv_of_notMem_tsupport ℝ (hout p hp)]; simp),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp ↦ by
      rw [image_eq_zero_of_notMem_tsupport (hout p hp)]; simp)] at hw
  simpa only [mul_comm] using hw

/-- For `A : ℝ × ℝ → ℂ`, `χ : ℝ × ℝ → ℝ` and a set `R`,
`∫ p in R, A p * (χ p : ℂ) = ∫ p in R, (χ p : ℂ) * A p`. -/
theorem integral_mul_comm_real (A : ℝ × ℝ → ℂ) (χ : ℝ × ℝ → ℝ) (R : Set (ℝ × ℝ)) :
    ∫ p in R, A p * ((χ p : ℝ) : ℂ) = ∫ p in R, ((χ p : ℝ) : ℂ) * A p :=
  integral_congr_ae (Eventually.of_forall fun _ ↦ mul_comm _ _)

/-- Let `c ≠ 0` be complex and let `A p = c * C p` and `B p = c * D p` for all `p : ℝ × ℝ`. If
`∫ p, w p * A p = -∫ p, u p * B p`, then `∫ p, w p * C p = -∫ p, u p * D p`. -/
theorem integral_mul_eq_neg_cancel_const_mul {A B C D : ℝ × ℝ → ℂ} (c : ℂ) (hc : c ≠ 0)
    (hA : ∀ p, A p = c * C p)
    (hB : ∀ p, B p = c * D p) (w u : ℝ × ℝ → ℂ) (h : ∫ p, w p * A p = -∫ p, u p * B p) :
    ∫ p, w p * C p = -∫ p, u p * D p := by
  simp_rw [hA, hB, show ∀ p, w p * (c * C p) = c * (w p * C p) from fun p ↦ by ring,
    show ∀ p, u p * (c * D p) = c * (u p * D p) from fun p ↦ by ring, integral_const_mul] at h
  rw [← mul_neg] at h
  exact mul_left_cancel₀ hc h

/-- Passage to the limit in an integral identity on `ℝ × ℝ`. Let `F`, `G` be complex functions
integrable on a measurable set `S`, let `u n`, `v n` be continuous real functions with `|u n p| ≤ C`
and `|v n p| ≤ C` that vanish outside `S` for large `n`, and let `u n p` tend to `d p` for almost
every `p` and `v n p` tend to `e p` for every `p`, where `d` and `e` vanish outside `S`; if
`∫ p, u n p * F p = -∫ p, v n p * G p` for large `n`, then `∫ p, d p * F p = -∫ p, e p * G p`. The
proof applies dominated convergence to both sides after replacing `F` and `G` by their indicators on
`S`. -/
theorem integral_mul_eq_neg_of_tendsto_bounded {F G : ℝ × ℝ → ℂ} {S : Set (ℝ × ℝ)}
    (hS : MeasurableSet S)
    (hFS : IntegrableOn F S) (hGS : IntegrableOn G S) (u v : ℕ → ℝ × ℝ → ℝ) (d e : ℝ × ℝ → ℝ)
        (C : ℝ)
    (hu : ∀ n, Continuous (u n)) (hv : ∀ n, Continuous (v n))
    (hout : ∀ᶠ n in atTop, ∀ p, p ∉ S → u n p = 0 ∧ v n p = 0)
    (hde : ∀ p, p ∉ S → d p = 0 ∧ e p = 0)
    (hb : ∀ n p, |u n p| ≤ C ∧ |v n p| ≤ C)
    (hlu : ∀ᵐ p, Tendsto (fun n ↦ u n p) atTop (𝓝 (d p)))
    (hlv : ∀ p, Tendsto (fun n ↦ v n p) atTop (𝓝 (e p)))
    (heq : ∀ᶠ n in atTop, ∫ p, (u n p : ℂ) * F p = -∫ p, (v n p : ℂ) * G p) :
    ∫ p, (d p : ℂ) * F p = -∫ p, (e p : ℂ) * G p := by
  have hF' : Integrable (S.indicator F) := (integrable_indicator_iff hS).2 hFS
  have hG' : Integrable (S.indicator G) := (integrable_indicator_iff hS).2 hGS
  have sw : ∀ (w : ℝ × ℝ → ℝ) (H : ℝ × ℝ → ℂ), (∀ p, p ∉ S → w p = 0) →
      (fun p ↦ (w p : ℂ) * S.indicator H p) = fun p ↦ (w p : ℂ) * H p := by
    intro w H hw; funext p
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp]
    · rw [hw p hp]; simp
  have L1 : Tendsto (fun n ↦ ∫ p, (u n p : ℂ) * S.indicator F p) atTop
      (𝓝 (∫ p, (d p : ℂ) * S.indicator F p)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun p ↦ C * ‖S.indicator F p‖) ?_ ?_
      (hF'.norm.const_mul C) ?_
    · exact Eventually.of_forall fun n ↦
        (Complex.continuous_ofReal.comp (hu n)).aestronglyMeasurable.mul hF'.aestronglyMeasurable
    · refine Eventually.of_forall fun n ↦ Eventually.of_forall fun p ↦ ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hb n p).1 (norm_nonneg _)
    · filter_upwards [hlu] with p hp
      exact ((Complex.continuous_ofReal.tendsto _).comp hp).mul_const _
  have L2 : Tendsto (fun n ↦ ∫ p, (v n p : ℂ) * S.indicator G p) atTop
      (𝓝 (∫ p, (e p : ℂ) * S.indicator G p)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun p ↦ C * ‖S.indicator G p‖) ?_ ?_
      (hG'.norm.const_mul C) ?_
    · exact Eventually.of_forall fun n ↦
        (Complex.continuous_ofReal.comp (hv n)).aestronglyMeasurable.mul hG'.aestronglyMeasurable
    · refine Eventually.of_forall fun n ↦ Eventually.of_forall fun p ↦ ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hb n p).2 (norm_nonneg _)
    · exact Eventually.of_forall fun p ↦ ((Complex.continuous_ofReal.tendsto _).comp
          (hlv p)).mul_const _
  have E : ∀ᶠ n in atTop, -∫ p, (v n p : ℂ) * S.indicator G p = ∫ p,
      (u n p : ℂ) * S.indicator F p := by
    filter_upwards [heq, hout] with n hn ho
    rw [sw (u n) F (fun p hp ↦ (ho p hp).1), sw (v n) G (fun p hp ↦ (ho p hp).2)]
    exact hn.symm
  have := tendsto_nhds_unique (L1.congr' (E.mono fun n h ↦ h.symm) |>.congr'
      (Eventually.of_forall fun _ ↦ rfl)) L2.neg
  rw [← sw d F (fun p hp ↦ (hde p hp).1), ← sw e G (fun p hp ↦ (hde p hp).2)]
  exact this

/-- Let `w`, `M`, `om : ℝ × ℝ → ℂ` with `om p = (2 * π : ℂ) * M p` for all `p`. Then
`∫ p, w p * om p = (2 * π : ℂ) * ∫ p, w p * M p`. -/
theorem integral_mul_eq_two_pi_mul_integral {w M : ℝ × ℝ → ℂ} {om : ℝ × ℝ → ℂ}
    (hom : ∀ p, om p = (2 * Real.pi : ℂ) * M p) :
    ∫ p, w p * om p = (2 * Real.pi : ℂ) * ∫ p, w p * M p := by
  rw [← integral_const_mul]
  congr 1
  funext p
  rw [hom]
  ring

/-- Let `a : ℝ × ℝ → ℝ` satisfy `a p ≠ 0 → 0 < p.1`, and let `A`, `B : ℝ × ℝ → ℝ → ℂ` satisfy
`A p θ = B p θ` for all `θ` whenever `0 < p.1`. Then
`∫ p, (a p : ℂ) * ∫ θ in 0..2 * π, A p θ = ∫ p, (a p : ℂ) * ∫ θ in 0..2 * π, B p θ`. -/
theorem integral_mul_integral_congr_of_fst_pos (a : ℝ × ℝ → ℝ) (ha : ∀ p, a p ≠ 0 → 0 < p.1)
    (A B : ℝ × ℝ → ℝ → ℂ)
    (h : ∀ p, 0 < p.1 → ∀ θ, A p θ = B p θ) :
    ∫ p, (a p : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), A p θ =
      ∫ p, (a p : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), B p θ := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun p ↦ ?_)
  by_cases hp : a p = 0
  · simp [hp]
  · simp only
    rw [intervalIntegral.integral_congr (fun θ _ ↦ h p (ha p hp) θ)]

/-- Parseval identity for a finite family `e k`, `k ∈ s`, of complex functions orthonormal for a
real weight `ρ` and a measure `μ`. Suppose that for `k, k' ∈ s` the function
`fun x ↦ (ρ x : ℂ) * (e k x * conj (e k' x))` is integrable with integral `1` if `k = k'` and `0`
otherwise; then for all complex coefficients `a k`,
`∫ x, ρ x * ‖∑ k ∈ s, a k * e k x‖ ^ 2 ∂μ = ∑ k ∈ s, ‖a k‖ ^ 2`. The proof expands the squared norm
as a double sum and integrates term by term. -/
theorem integral_mul_norm_sq_sum_of_orthonormal {α ι : Type*} [DecidableEq ι] [MeasurableSpace α]
    {μ : Measure α} (s : Finset ι) (ρ : α → ℝ)
    (e : ι → α → ℂ) (a : ι → ℂ)
    (hint : ∀ k ∈ s, ∀ k' ∈ s, Integrable (fun x ↦ (ρ x : ℂ) * (e k x * (starRingEnd ℂ) (e k' x)))
        μ)
    (horth : ∀ k ∈ s, ∀ k' ∈ s, ∫ x, (ρ x : ℂ) * (e k x * (starRingEnd ℂ) (e k' x)) ∂μ = if k =
        k' then 1 else 0) :
    ∫ x, ρ x * ‖∑ k ∈ s, a k * e k x‖ ^ 2 ∂μ = ∑ k ∈ s, ‖a k‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have hpt : ∀ x, ((ρ x * ‖∑ k ∈ s, a k * e k x‖ ^ 2 : ℝ) : ℂ)
      = ∑ k ∈ s, ∑ k' ∈ s, (a k * (starRingEnd ℂ) (a k')) *
          ((ρ x : ℂ) * (e k x * (starRingEnd ℂ) (e k' x))) := by
    intro x
    rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum,
        Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k' _ ↦ ?_
    rw [map_mul]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun k hk ↦ integrable_finsetSum _ fun k' hk' ↦
      (hint k hk k' hk').const_mul _)]
  push_cast
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [integral_finsetSum _ (fun k' hk' ↦ (hint k hk k' hk').const_mul _)]
  simp_rw [integral_const_mul]
  rw [Finset.sum_congr rfl fun k' hk' ↦ by rw [horth k hk k' hk']]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, hk, ite_true]
  rw [Complex.mul_conj']

/-- Cauchy-Schwarz inequality for pointwise norms: for `F` in `Lp E 2 μ` and `G` in `Lp E' 2 μ`,
with `E` and `E'` real inner product spaces, `∫ t, ‖F t‖ * ‖G t‖ ∂μ ≤ ‖F‖ * ‖G‖`. The proof is
Hölder's inequality with both exponents equal to `2`. -/
theorem integral_norm_mul_norm_le_Lp_two {α E E' : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (F : Lp E 2 μ) (G : Lp E' 2 μ) :
    ∫ t, ‖F t‖ * ‖G t‖ ∂μ ≤ ‖F‖ * ‖G‖ := by
  have h2 : ENNReal.ofReal 2 = 2 := by norm_num
  have hF : MemLp (fun t ↦ ‖F t‖) (ENNReal.ofReal 2) μ := by rw [h2]; exact (Lp.memLp F).norm
  have hG : MemLp (fun t ↦ ‖G t‖) (ENNReal.ofReal 2) μ := by rw [h2]; exact (Lp.memLp G).norm
  have := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ fun t ↦ norm_nonneg (F t)) (ae_of_all _ fun t ↦ norm_nonneg (G t)) hF hG
  rwa [rpow_integral_norm_rpow_two_Lp, rpow_integral_norm_rpow_two_Lp] at this

/-- If `f`, `g : ℝ × ℝ → ℂ` are integrable on a set `s` and `h p = f p + Complex.I * g p` for all
`p`, then `∫ p in s, h p = (∫ p in s, f p) + Complex.I * ∫ p in s, g p`. -/
theorem integral_pair_of {s : Set (ℝ × ℝ)} {f g h : ℝ × ℝ → ℂ} (hf : IntegrableOn f s)
    (hg : IntegrableOn g s) (hh : ∀ p, h p = f p + Complex.I * g p) :
    ∫ p in s, h p = (∫ p in s, f p) + Complex.I * ∫ p in s, g p := by
  rw [← integral_const_mul, ← integral_add hf (hg.const_mul _)]
  exact congrArg _ (funext hh)

/-- The integral over the circle `AddCircle T` (`0 < T`, Haar probability measure) commutes with a
fivefold sum over `Fin 3`: if every `f i l x y z : AddCircle T → ℂ` is integrable, then
`∫ t, ∑ i, ∑ l, ∑ x, ∑ y, ∑ z, f i l x y z t = ∑ i, ∑ l, ∑ x, ∑ y, ∑ z, ∫ t, f i l x y z
t`. The proof exchanges the integral with one finite sum at a time. -/
theorem integral_quintuple_sum_fin_three {T : ℝ} [hT : Fact (0 < T)]
    {f : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → AddCircle T → ℂ}
    (h : ∀ i l x y z, Integrable (f i l x y z) AddCircle.haarAddCircle) :
    ∫ t, ∑ i, ∑ l, ∑ x, ∑ y, ∑ z, f i l x y z t ∂AddCircle.haarAddCircle
      = ∑ i, ∑ l, ∑ x, ∑ y, ∑ z, ∫ t, f i l x y z t ∂AddCircle.haarAddCircle := by
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun l _ ↦
      integrable_finsetSum _ fun x _ ↦
    integrable_finsetSum _ fun y _ ↦ integrable_finsetSum _ fun z _ ↦ h i l x y z]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum _ fun l _ ↦ integrable_finsetSum _ fun x _ ↦
    integrable_finsetSum _ fun y _ ↦ integrable_finsetSum _ fun z _ ↦ h i l x y z]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [integral_finsetSum _ fun x _ ↦ integrable_finsetSum _ fun y _ ↦
      integrable_finsetSum _ fun z _ ↦ h i l x y z]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [integral_finsetSum _ fun y _ ↦ integrable_finsetSum _ fun z _ ↦ h i l x y z]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [integral_finsetSum _ fun z _ ↦ h i l x y z]

/-- For complex functions `a l c d q` on `ℝ × ℝ` that are integrable for a measure `μ`,
`∫ x, a x - l x + c x + d x + q x ∂μ = (∫ x, a x ∂μ) - (∫ x, l x ∂μ) + (∫ x, c x ∂μ) +
(∫ x, d x ∂μ) + ∫ x, q x ∂μ`. -/
theorem integral_sub_add_add_add {μ : Measure (ℝ × ℝ)} {a l c d q : ℝ × ℝ → ℂ} (ha : Integrable a μ)
    (hl : Integrable l μ) (hc : Integrable c μ) (hd : Integrable d μ) (hq : Integrable q μ) :
    ∫ x, a x - l x + c x + d x + q x ∂μ
      = (∫ x, a x ∂μ) - (∫ x, l x ∂μ) + (∫ x, c x ∂μ) + (∫ x, d x ∂μ) + ∫ x, q x ∂μ := by
  have h4 : Integrable (fun x ↦ a x - l x + c x + d x) μ := ((ha.sub hl).add hc).add hd
  have h3 : Integrable (fun x ↦ a x - l x + c x) μ := (ha.sub hl).add hc
  have h2 : Integrable (fun x ↦ a x - l x) μ := ha.sub hl
  rw [integral_add h4 hq, integral_add h3 hd, integral_add h2 hc, integral_sub ha hl]

/-- Linearity of the integral for a measure `μ` on `ℝ × ℝ` and a finite set `s` of integers: if all
the complex functions `f1 i j`, `f2 i`, `g1 n i j`, `g2 n i` (with `i j : Fin 3`, `n : ℤ`) are
integrable, then the integral of
`∑ i, ∑ j, f1 i j p + ∑ i, f2 i p + ∑ n ∈ s, (∑ i, ∑ j, g1 n i j p + ∑ i, g2 n i p)` equals
`∑ i, ∑ j, ∫ p, f1 i j p ∂μ + ∑ i, ∫ p, f2 i p ∂μ + ∑ n ∈ s, (∑ i, ∑ j, ∫ p, g1 n i j p ∂μ + ∑ i, ∫
p, g2 n i p ∂μ)`. The proof applies additivity of the integral and its commutation with finite sums
to each group of terms. -/
theorem integral_sum_sum_add_sum_add_sum {μ : Measure (ℝ × ℝ)} (s : Finset ℤ)
    (f1 : Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (f2 : Fin 3 → ℝ × ℝ → ℂ) (g1 : ℤ → Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (g2 : ℤ → Fin 3 → ℝ × ℝ → ℂ)
    (h1 : ∀ i j, Integrable (f1 i j) μ) (h2 : ∀ i, Integrable (f2 i) μ)
    (h3 : ∀ n i j, Integrable (g1 n i j) μ) (h4 : ∀ n i, Integrable (g2 n i) μ) :
    ∫ p, (∑ i, ∑ j, f1 i j p + ∑ i, f2 i p + ∑ n ∈ s, (∑ i, ∑ j, g1 n i j p + ∑ i, g2 n i p)) ∂μ =
      ∑ i, ∑ j, ∫ p, f1 i j p ∂μ + ∑ i, ∫ p, f2 i p ∂μ +
        ∑ n ∈ s, (∑ i, ∑ j, ∫ p, g1 n i j p ∂μ + ∑ i, ∫ p, g2 n i p ∂μ) := by
  have i1 : Integrable (fun p ↦ ∑ i, ∑ j, f1 i j p) μ :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ h1 i j
  have i2 : Integrable (fun p ↦ ∑ i, f2 i p) μ := integrable_finsetSum _ fun i _ ↦ h2 i
  have i3 : ∀ n, Integrable (fun p ↦ ∑ i, ∑ j, g1 n i j p) μ := fun n ↦
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ h3 n i j
  have i4 : ∀ n, Integrable (fun p ↦ ∑ i, g2 n i p) μ :=
      fun n ↦ integrable_finsetSum _ fun i _ ↦ h4 n i
  have i12 : Integrable (fun p ↦ ∑ i, ∑ j, f1 i j p + ∑ i, f2 i p) μ := i1.add i2
  have i34 : ∀ n, Integrable (fun p ↦ ∑ i, ∑ j, g1 n i j p + ∑ i, g2 n i p) μ :=
      fun n ↦ (i3 n).add (i4 n)
  have iS : Integrable (fun p ↦ ∑ n ∈ s, (∑ i, ∑ j, g1 n i j p + ∑ i, g2 n i p)) μ :=
    integrable_finsetSum _ fun n _ ↦ i34 n
  rw [integral_add i12 iS, integral_add i1 i2, integral_finsetSum _ fun n _ ↦ i34 n,
    integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ h1 i j,
        integral_finsetSum _ fun i _ ↦ h2 i]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun i _ ↦ integral_finsetSum _ fun j _ ↦ h1 i j
  · refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [integral_add (i3 n) (i4 n), integral_finsetSum _ fun i _ ↦
        integrable_finsetSum _ fun j _ ↦ h3 n i j,
      integral_finsetSum _ fun i _ ↦ h4 n i]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ integral_finsetSum _ fun j _ ↦ h3 n i j

/-- For a decidable proposition `c`, a set `s` in `ℝ × ℝ` and `f : ℝ × ℝ → ℝ`,
`(if c then ∫ p in s, f p else 0) = ∫ p in s, (if c then f p else 0)`. -/
theorem ite_setIntegral_eq_setIntegral_ite (c : Prop) [Decidable c] (s : Set (ℝ × ℝ))
    (f : ℝ × ℝ → ℝ) :
    (if c then ∫ p in s, f p else 0) = ∫ p in s, (if c then f p else 0) := by
  split_ifs <;> simp

/-- Let `X` be a complete real normed space, `f : ℝ × ℝ → X`, `Φ : ℝ → X →L[ℝ] ℝ`, `c : ℝ → ℝ`
continuous, and `θ` a real number such that `τ ↦ f (τ, θ)` is integrable on `Ioc 0 1`. Then for
every `w : ℂ`, `w * ((Φ θ (∫ τ in Icc 0 1, c τ • f (τ, θ)) : ℝ) : ℂ) = ∫ τ in Ioc 0 1, w *
(c τ : ℂ) * ((Φ θ (f (τ, θ)) : ℝ) : ℂ)`. The proof commutes the continuous linear functional `Φ
θ` with the integral. -/
theorem mul_ofReal_clm_apply_setIntegral_smul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (f : ℝ × ℝ → X) (Φ : ℝ → X →L[ℝ] ℝ) (θ : ℝ) (c : ℝ → ℝ) (hc : Continuous c)
    (hθ : Integrable (fun τ ↦ f (τ, θ)) (volume.restrict (Set.Ioc (0 : ℝ) 1))) (w : ℂ) :
    w * ((Φ θ (∫ τ in Set.Icc (0 : ℝ) 1, c τ • f (τ, θ)) : ℝ) : ℂ)
      = ∫ τ in Set.Ioc (0 : ℝ) 1, w * ((c τ : ℝ) : ℂ) * ((Φ θ (f (τ, θ)) : ℝ) : ℂ) := by
  have hi : Integrable (fun τ ↦ c τ • f (τ, θ)) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    IntegrableOn.continuousOn_smul (by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]; exact hθ) hc.continuousOn isCompact_Icc
  rw [← ContinuousLinearMap.integral_comp_comm _ hi]
  simp only [map_smul, smul_eq_mul]
  rw [← integral_complex_ofReal, ← integral_const_mul, ← setIntegral_congr_set Ioc_ae_eq_Icc]
  refine integral_congr_ae (Eventually.of_forall fun τ ↦ ?_)
  simp only
  push_cast
  ring

/-- Let `X`, `Y : ℝ × ℝ → ℝ` be integrable and almost everywhere nonnegative on a set `S`, and let
`j : ℝ × ℝ → ℂ` satisfy `‖j p‖ ≤ √(X p) * √(Y p)` for almost every `p` in `S`. Then
`‖∫ p in S, j p‖ ^ 2 ≤ (∫ p in S, X p) * ∫ p in S, Y p`. The proof applies Hölder's inequality with
exponents `2` and `2` to `√X` and `√Y`. -/
theorem norm_setIntegral_sq_le_integral_mul_integral {S : Set (ℝ × ℝ)} {j : ℝ × ℝ → ℂ}
    {X Y : ℝ × ℝ → ℝ}
    (hX : IntegrableOn X S) (hY : IntegrableOn Y S) (hX0 : ∀ᵐ p ∂(volume.restrict S), 0 ≤ X p)
    (hY0 : ∀ᵐ p ∂(volume.restrict S), 0 ≤ Y p) (hj : ∀ᵐ p ∂(volume.restrict S),
        ‖j p‖ ≤ Real.sqrt (X p) * Real.sqrt (Y p)) :
    ‖∫ p in S, j p‖ ^ 2 ≤ (∫ p in S, X p) * ∫ p in S, Y p := by
  have hsX : MemLp (fun p ↦ Real.sqrt (X p)) (ENNReal.ofReal 2) (volume.restrict S) := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    refine (memLp_two_iff_integrable_sq_norm (Real.continuous_sqrt.comp_aestronglyMeasurable
        hX.1)).2 ?_
    exact hX.congr (hX0.mono fun p hp ↦ by
      simp only [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hp])
  have hsY : MemLp (fun p ↦ Real.sqrt (Y p)) (ENNReal.ofReal 2) (volume.restrict S) := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    refine (memLp_two_iff_integrable_sq_norm (Real.continuous_sqrt.comp_aestronglyMeasurable
        hY.1)).2 ?_
    exact hY.congr (hY0.mono fun p hp ↦ by
      simp only [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hp])
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun p ↦ Real.sqrt_nonneg (X p))
        (Eventually.of_forall fun p ↦ Real.sqrt_nonneg (Y p))
    hsX hsY
  have e1 : ∫ p in S, Real.sqrt (X p) ^ (2 : ℝ) = ∫ p in S, X p :=
    integral_congr_ae (hX0.mono fun p hp ↦ by simp only [Real.rpow_two, Real.sq_sqrt hp])
  have e2 : ∫ p in S, Real.sqrt (Y p) ^ (2 : ℝ) = ∫ p in S, Y p :=
    integral_congr_ae (hY0.mono fun p hp ↦ by simp only [Real.rpow_two, Real.sq_sqrt hp])
  rw [e1, e2] at hH
  have hIX : 0 ≤ ∫ p in S, X p := integral_nonneg_of_ae hX0
  have hIY : 0 ≤ ∫ p in S, Y p := integral_nonneg_of_ae hY0
  have hprod : Integrable (fun p ↦ Real.sqrt (X p) * Real.sqrt (Y p)) (volume.restrict S) := by
    refine ((hX.add hY).div_const 2).mono' ((Real.continuous_sqrt.comp_aestronglyMeasurable
        hX.1).mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hY.1)) ((hX0.and hY0).mono fun p hp ↦ ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), Pi.add_apply]
    nlinarith [Real.sq_sqrt hp.1, Real.sq_sqrt hp.2, sq_nonneg (Real.sqrt (X p) - Real.sqrt (Y p))]
  have h1 : ‖∫ p in S, j p‖ ≤ ∫ p in S, Real.sqrt (X p) * Real.sqrt (Y p) :=
    (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
        (Eventually.of_forall fun p ↦ norm_nonneg _)
      hprod hj)
  have h2 := h1.trans hH
  have h3 : (0 : ℝ) ≤ ‖∫ p in S, j p‖ := norm_nonneg _
  calc ‖∫ p in S, j p‖ ^ 2 ≤ ((∫ p in S, X p) ^ (1 / (2 : ℝ)) * (∫ p in S, Y p) ^ (1 / (2 : ℝ))) ^
           2 :=
        pow_le_pow_left₀ h3 h2 2
    _ = (∫ p in S, X p) * ∫ p in S, Y p := by
        rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hIX, Real.sq_sqrt hIY]

/-- For every real function `g` on a measure space,
`ENNReal.ofReal |∫ x, g x ∂μ| ≤ ∫⁻ x, ENNReal.ofReal |g x| ∂μ`. No measurability or integrability of
`g` is assumed. -/
theorem ofReal_abs_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ) :
    ENNReal.ofReal |∫ x, g x ∂μ| ≤ ∫⁻ x, ENNReal.ofReal |g x| ∂μ := by
  have h := norm_integral_le_lintegral_norm (μ := μ) g
  simp only [Real.norm_eq_abs] at h
  exact (ENNReal.ofReal_le_ofReal h).trans ENNReal.ofReal_toReal_le

/-- For `f : ℝ → ℝ` with `0 ≤ f t` for all `t`,
`ENNReal.ofReal (∫ t, f t) ≤ ∫⁻ t, ENNReal.ofReal (f t)`. No integrability of `f` is assumed. -/
theorem ofReal_integral_le_lintegral {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t) :
    ENNReal.ofReal (∫ t, f t) ≤ ∫⁻ t, ENNReal.ofReal (f t) := by
  by_cases hi : Integrable f
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf)]
  · rw [integral_undef hi]
    simp

/-- If `H ι : ℝ × ℝ → ℂ` is integrable on a set `S` for every `ι` in a finite set `T`, then
`(∑ ι ∈ T, ∫ p in S, H ι p).re = ∑ ι ∈ T, ∫ p in S, (H ι p).re`. -/
theorem re_sum_integral {S : Set (ℝ × ℝ)} {α : Type*} (T : Finset α) (H : α → ℝ × ℝ → ℂ)
    (hH : ∀ ι ∈ T, IntegrableOn (H ι) S) :
    (∑ ι ∈ T, ∫ p in S, H ι p).re = ∑ ι ∈ T, ∫ p in S, (H ι p).re := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun ι hι ↦ ?_
  exact (integral_re (hH ι hι)).symm

/-- For any `g : ℝ × ℝ → ℂ` and real `a b`,
`∫ p in Icc a b ×ˢ Icc (min 0 (-0)) (max 0 (-0)), g p = 0`, because the second factor is the single
point `0` and so the rectangle has Lebesgue measure zero. -/
theorem setIntegral_Icc_prod_degenerate_eq_zero (g : ℝ × ℝ → ℂ) (a b : ℝ) :
    ∫ p in Set.Icc a b ×ˢ Set.Icc (min (0 : ℝ) (-0)) (max 0 (-0)), g p = 0 := by
  apply setIntegral_measure_zero
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  simp

/-- Let `B ⊆ ℝ` be measurable, `lo ≤ mid` and `mid ≤ hi`, and `g : ℝ × ℝ → ℂ` integrable on
`Icc lo hi ×ˢ B`. Then
`∫ p in Icc lo hi ×ˢ B, g p = (∫ p in Icc lo mid ×ˢ B, g p) + ∫ p in Icc mid hi ×ˢ B, g
p`. The proof uses that the two pieces meet inside the null set `{mid} ×ˢ univ`. -/
theorem setIntegral_Icc_prod_eq_add (B : Set ℝ) (hB : MeasurableSet B) {lo mid hi : ℝ}
    (h1 : lo ≤ mid) (h2 : mid ≤ hi)
    (g : ℝ × ℝ → ℂ) (hg : IntegrableOn g (Set.Icc lo hi ×ˢ B)) :
    ∫ p in Set.Icc lo hi ×ˢ B, g p = (∫ p in Set.Icc lo mid ×ˢ B, g p) +
        ∫ p in Set.Icc mid hi ×ˢ B, g p := by
  have hs1 : Set.Icc lo mid ×ˢ B ⊆ Set.Icc lo hi ×ˢ B :=
      Set.prod_mono (Set.Icc_subset_Icc le_rfl h2) le_rfl
  have hs2 : Set.Icc mid hi ×ˢ B ⊆ Set.Icc lo hi ×ˢ B :=
      Set.prod_mono (Set.Icc_subset_Icc h1 le_rfl) le_rfl
  have hi1 := hg.mono_set hs1
  have hi2 := hg.mono_set hs2
  rw [← Set.Icc_union_Icc_eq_Icc h1 h2, Set.union_prod]
  refine setIntegral_union₀ ?_ (measurableSet_Icc.prod hB).nullMeasurableSet hi1 hi2
  unfold AEDisjoint
  apply measure_mono_null (t := {mid} ×ˢ Set.univ)
  · rintro ⟨a, b⟩ ⟨⟨ha1, _⟩, ⟨ha2, _⟩⟩
    exact ⟨le_antisymm ha1.2 ha2.1, trivial⟩
  · rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp

/-- Let the closed intervals `Icc (lo s) (hi s)`, `s ∈ T`, with `T` a finite set, cover `Icc r₁ r₂`,
satisfy `r₁ ≤ lo s` and `hi s ≤ r₂`, and overlap pairwise at most at endpoints (`hi s ≤ lo s'` or
`hi s' ≤ lo s` for `s ≠ s'`). If `A ⊆ ℝ` is measurable and `f : ℝ × ℝ → ℂ` is integrable on
`Icc r₁ r₂ ×ˢ A`, then `∫ p in Icc r₁ r₂ ×ˢ A, f p = ∑ s ∈ T, ∫ p in Icc (lo s) (hi s) ×ˢ A, f p`.
The proof writes the product set as a finite union of sets `Icc (lo s) (hi s) ×ˢ A` whose pairwise
intersections lie in null sets `{x} ×ˢ A`. -/
theorem setIntegral_Icc_prod_eq_sum_of_partition {ι : Type*} (T : Finset ι) (lo hi : ι → ℝ)
    {r₁ r₂ : ℝ}
    (hcov : ∀ u ∈ Icc r₁ r₂, ∃ s ∈ T, lo s ≤ u ∧ u ≤ hi s) (hin : ∀ s ∈ T, r₁ ≤ lo s ∧ hi s ≤ r₂)
    (hdis : ∀ s ∈ T, ∀ s' ∈ T, s ≠ s' → hi s ≤ lo s' ∨ hi s' ≤ lo s) {A : Set ℝ}
        (hA : MeasurableSet A)
    {f : ℝ × ℝ → ℂ} (hf : IntegrableOn f (Icc r₁ r₂ ×ˢ A)) :
    ∫ p in Icc r₁ r₂ ×ˢ A, f p = ∑ s ∈ T, ∫ p in Icc (lo s) (hi s) ×ˢ A, f p := by
  classical
  have hU : Icc r₁ r₂ ×ˢ A = ⋃ i : T, Icc (lo i) (hi i) ×ˢ A := by
    ext p
    simp only [mem_prod, mem_iUnion, Subtype.exists, exists_prop, mem_Icc]
    constructor
    · rintro ⟨hp, hA⟩
      obtain ⟨s, hs, h1, h2⟩ := hcov p.1 hp
      exact ⟨s, hs, ⟨h1, h2⟩, hA⟩
    · rintro ⟨s, hs, ⟨h1, h2⟩, hA⟩
      exact ⟨⟨(hin s hs).1.trans h1, h2.trans (hin s hs).2⟩, hA⟩
  have hnull : ∀ (x : ℝ), (volume : Measure (ℝ × ℝ)) ({x} ×ˢ A) = 0 := by
    intro x
    rw [Measure.volume_eq_prod]
    exact measure_mono_null (prod_mono subset_rfl (subset_univ A)) (by rw [Measure.prod_prod]; simp)
  rw [hU, integral_iUnion_ae]
  · rw [tsum_fintype]
    exact Finset.sum_coe_sort T (fun s ↦ ∫ p in Icc (lo s) (hi s) ×ˢ A, f p)
  · intro i
    exact (measurableSet_Icc.prod hA).nullMeasurableSet
  · intro i j hij
    have hne : (i : ι) ≠ j := fun e ↦ hij (Subtype.ext e)
    rcases hdis i i.2 j j.2 hne with h | h
    · refine measure_mono_null ?_ (hnull (hi i))
      rintro p ⟨⟨⟨_, h2⟩, hA⟩, ⟨h3, _⟩, _⟩
      exact ⟨le_antisymm h2 (h.trans h3), hA⟩
    · refine measure_mono_null ?_ (hnull (hi j))
      rintro p ⟨⟨⟨h1, _⟩, hA⟩, ⟨_, h4⟩, _⟩
      exact ⟨le_antisymm h4 (h.trans h1), hA⟩
  · rw [← hU]; exact hf

/-- For `F`, `dF : ℝ × ℝ → ℂ` and real `a b o R z₁ z₂`, the integral over `Icc a b ×ˢ Icc z₁ z₂` of
`((1 / (R - o)) * F p + ((p.1 - o) / (R - o)) * dF p) * 1` equals the integral of
`(1 / (R - o)) * F p + (1 / (R - o) * p.1 + -o / (R - o)) * dF p`, the real coefficients being cast
to `ℂ`. The two integrands agree pointwise, so no integrability hypothesis is needed. -/
theorem setIntegral_Icc_prod_sub_div_mul_eq (F dF : ℝ × ℝ → ℂ) (a b o R z₁ z₂ : ℝ) :
    ∫ p in Icc a b ×ˢ Icc z₁ z₂,
        ((((1 / (R - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (R - o) : ℝ) : ℂ) * dF p) * (((1 : ℝ)) : ℂ)
      = ∫ p in Icc a b ×ˢ Icc z₁ z₂,
          (((1 / (R - o) : ℝ) : ℂ) * F p + ((1 / (R - o) * p.1 + -o / (R - o) : ℝ) : ℂ) * dF p) :=
              by
  refine setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) (fun p _ ↦ ?_)
  rw [show (p.1 - o) / (R - o) = 1 / (R - o) * p.1 + -o / (R - o) by
    ring, Complex.ofReal_one, mul_one]

/-- Let `S` be a measurable set in `ℝ × ℝ` and `h : ℝ × ℝ → ℝ` integrable on `S`. If `f` and `g` are
nonnegative on `S` and `f p + g p ≤ h p` for all `p ∈ S`, then
`(∫ p in S, f p) + (∫ p in S, g p) ≤ ∫ p in S, h p`, with no integrability assumption on `f` or `g`.
The proof splits on whether `f` and `g` are integrable on `S`, since a function that is not
integrable has integral `0`. -/
theorem setIntegral_add_le_of_nonneg {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) {f g h : ℝ × ℝ → ℝ}
    (hf0 : ∀ p ∈ S, 0 ≤ f p) (hg0 : ∀ p ∈ S, 0 ≤ g p) (hfg : ∀ p ∈ S, f p + g p ≤ h p)
    (hh : IntegrableOn h S) : (∫ p in S, f p) + (∫ p in S, g p) ≤ ∫ p in S, h p := by
  have hh0 : 0 ≤ ∫ p in S, h p :=
    setIntegral_nonneg hS fun p hp ↦ (add_nonneg (hf0 p hp) (hg0 p hp)).trans (hfg p hp)
  by_cases hf : IntegrableOn f S
  · by_cases hg : IntegrableOn g S
    · rw [← integral_add hf hg]
      exact setIntegral_mono_on (hf.add hg) hh hS hfg
    · rw [integral_undef hg, add_zero]
      exact setIntegral_mono_on hf hh hS fun p hp ↦ (le_add_of_nonneg_right (hg0 p hp)).trans
          (hfg p hp)
  · rw [integral_undef hf, zero_add]
    by_cases hg : IntegrableOn g S
    · exact setIntegral_mono_on hg hh hS fun p hp ↦ (le_add_of_nonneg_left (hf0 p hp)).trans
          (hfg p hp)
    · rw [integral_undef hg]
      exact hh0

/-- If `q ↦ k (q.1, |q.2|)` is integrable for Lebesgue measure on `ℝ × ℝ`, where `k : ℝ × ℝ → ℝ`,
then `∫ q in Ioi 0 ×ˢ univ, k (q.1, |q.2|) = 2 * ∫ q in Ioi 0 ×ˢ Ioi 0, k q`. The proof splits the
half plane at `q.2 = 0`, reflects the lower part with the measure preserving map `q ↦ (q.1, -q.2)`,
and discards the boundary line, which is a null set. -/
theorem setIntegral_comp_abs_snd_eq_two_mul (k : ℝ × ℝ → ℝ)
    (hk : Integrable fun q : ℝ × ℝ ↦ k (q.1, |q.2|)) :
    ∫ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), k (q.1, |q.2|) =
      2 * ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), k q := by
  rw [← Set.Ioi_union_Iic (a := (0 : ℝ)), Set.prod_union,
    setIntegral_union (Set.disjoint_prod.2 (Or.inr (Set.Iic_disjoint_Ioi le_rfl).symm))
      (measurableSet_Ioi.prod measurableSet_Iic) hk.integrableOn hk.integrableOn]
  have h1 : ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), k (q.1, |q.2|) =
      ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), k q :=
    setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioi) fun q hq ↦ by
      simp only [abs_of_pos (show (0 : ℝ) < q.2 from hq.2), Prod.mk.eta]
  have hmp : MeasurePreserving (fun q : ℝ × ℝ ↦ (q.1, -q.2)) volume volume := by
    have := (MeasurePreserving.id (volume : Measure ℝ)).prod
        (Measure.measurePreserving_neg (volume : Measure ℝ))
    rw [← Measure.volume_eq_prod] at this
    exact this
  have hemb : MeasurableEmbedding (fun q : ℝ × ℝ ↦ (q.1, -q.2)) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.neg ℝ)).measurableEmbedding
  have hpre : (fun q : ℝ × ℝ ↦ (q.1, -q.2)) ⁻¹' (Set.Ioi (0 : ℝ) ×ˢ Set.Ici 0) =
      Set.Ioi 0 ×ˢ Set.Iic 0 := by
    ext q; simp
  have h2 : ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Iic (0 : ℝ), k (q.1, |q.2|) =
      ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ici (0 : ℝ), k q := by
    rw [← hmp.setIntegral_preimage_emb hemb k, hpre]
    exact setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Iic) fun q hq ↦ by
      simp only [abs_of_nonpos (show q.2 ≤ 0 from hq.2)]
  have h3 : (Set.Ioi (0 : ℝ) ×ˢ Set.Ici (0 : ℝ) : Set (ℝ × ℝ)) =ᵐ[volume] Set.Ioi 0 ×ˢ Set.Ioi 0 :=
      by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null (t := Set.Ioi (0 : ℝ) ×ˢ ({0} : Set ℝ)) ?_ ?_
      · rintro ⟨r, z⟩ ⟨⟨hr, hz⟩, hn⟩
        exact ⟨hr, Set.mem_singleton_iff.2 (le_antisymm (not_lt.1 fun h ↦ hn ⟨hr, h⟩) hz)⟩
      · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]
    · rw [Set.sdiff_eq_empty.2 (Set.prod_mono le_rfl Set.Ioi_subset_Ici_self), measure_empty]
  rw [h1, h2, setIntegral_congr_set h3]
  ring

/-- Let `I2` and `IU` be complex functions integrable on a set `s` in `ℝ × ℝ`, and let `k : ℂ`. If
`I1 p = I2 p + k * IU p` for almost every `p` in `s`, then
`∫ p in s, I1 p = (∫ p in s, I2 p) + k * ∫ p in s, IU p`. -/
theorem setIntegral_eq_add_const_mul_setIntegral {s : Set (ℝ × ℝ)} {I1 I2 IU : ℝ × ℝ → ℂ} (k : ℂ)
    (h : ∀ᵐ p ∂(volume.restrict s), I1 p = I2 p + k * IU p) (h2 : IntegrableOn I2 s)
        (hU : IntegrableOn IU s) :
    ∫ p in s, I1 p = (∫ p in s, I2 p) + k * ∫ p in s, IU p := by
  rw [integral_congr_ae h, integral_add h2 (hU.const_mul k), integral_const_mul]

/-- Let `f₁` and `f₂` be complex functions integrable on a set `s` in `ℝ × ℝ`. If `f p = f₁ p +
Complex.I * f₂ p` for almost every `p` in `s`, then `(∫ p in s, f₁ p) + Complex.I * ∫ p in s, f₂ p =
∫ p in s, f p`. A case of `PDE.Analysis.setIntegral_eq_add_const_mul_setIntegral`. -/
theorem setIntegral_add_I_mul_setIntegral_eq {s : Set (ℝ × ℝ)} {f f₁ f₂ : ℝ × ℝ → ℂ}
    (h₁ : IntegrableOn f₁ s)
    (h₂ : IntegrableOn f₂ s) (he : ∀ᵐ p ∂(volume.restrict s), f p = f₁ p + Complex.I * f₂ p) :
    (∫ p in s, f₁ p) + Complex.I * ∫ p in s, f₂ p = ∫ p in s, f p :=
  Eq.symm (setIntegral_eq_add_const_mul_setIntegral Complex.I he h₁ h₂)

/-- If `p ↦ (p.1 : ℂ) * S p` is integrable on a set `s` in `ℝ × ℝ`, where `S : ℝ × ℝ → ℂ`, then for
every `c : ℂ`, `∫ p in s, p.1 * (c * S p).re = (c * ∫ p in s, (p.1 : ℂ) * S p).re`. -/
theorem setIntegral_fst_mul_re_const_mul (s : Set (ℝ × ℝ)) (S : ℝ × ℝ → ℂ)
    (hS : IntegrableOn (fun p ↦ (p.1 : ℂ) * S p) s) (c : ℂ) :
    ∫ p in s, p.1 * (c * S p).re = (c * ∫ p in s, (p.1 : ℂ) * S p).re := by
  have h := integral_re (𝕜 := ℂ) (hS.const_mul c)
  simp only [RCLike.re_to_complex] at h
  rw [← integral_const_mul, ← h]
  congr 1
  funext p
  rw [show c * ((p.1 : ℂ) * S p) = (p.1 : ℂ) * (c * S p) by ring, Complex.re_ofReal_mul]

/-- Let `s` and `t i`, for `i` in a finite type, be measurable sets in `ℝ × ℝ` with `s ⊆ ⋃ i, t i`.
If `f : ℝ × ℝ → ℝ` is nonnegative on `s`, then `∫ p in s, f p ≤ ∑ i, ∫ p in s ∩ t i, f p`, with no
integrability assumption on `f`. When `f` is integrable on `s` the proof passes to lower integrals
of `ENNReal.ofReal (f p)` and uses subadditivity over the cover, and otherwise the left side is `0`.
-/
theorem setIntegral_le_sum_inter_of_cover {ι : Type*} [Fintype ι] {s : Set (ℝ × ℝ)}
    {t : ι → Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (ht : ∀ i, MeasurableSet (t i)) (hcov : s ⊆ ⋃ i, t i)
    {f : ℝ × ℝ → ℝ} (hf : ∀ p ∈ s, 0 ≤ f p) :
    ∫ p in s, f p ≤ ∑ i, ∫ p in s ∩ t i, f p := by
  by_cases hint : IntegrableOn f s volume
  · have each : ∀ i, IntegrableOn f (s ∩ t i) volume := fun i ↦ hint.mono_set Set.inter_subset_left
    have hnn : ∀ i, 0 ≤ᵐ[volume.restrict (s ∩ t i)] f := fun i ↦
      ae_restrict_of_forall_mem (hs.inter (ht i)) (fun p hp ↦ hf p hp.1)
    have hfin : ∀ i, ∫⁻ p in s ∩ t i, ENNReal.ofReal (f p) ≠ ⊤ := fun i ↦
      (Integrable.lintegral_lt_top (each i)).ne
    rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem hs hf)
        hint.aestronglyMeasurable]
    rw [Finset.sum_congr rfl (fun i _ ↦ integral_eq_lintegral_of_nonneg_ae (hnn i)
        (each i).aestronglyMeasurable)]
    rw [← ENNReal.toReal_sum (fun i _ ↦ hfin i)]
    apply ENNReal.toReal_mono (ENNReal.sum_ne_top.2 (fun i _ ↦ hfin i))
    have hsub : s ⊆ ⋃ i, s ∩ t i := by
      intro p hp
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov hp)
      exact Set.mem_iUnion.2 ⟨i, hp, hi⟩
    calc ∫⁻ p in s, ENNReal.ofReal (f p)
        ≤ ∫⁻ p in ⋃ i, s ∩ t i, ENNReal.ofReal (f p) := lintegral_mono_set hsub
      _ ≤ ∑' i, ∫⁻ p in s ∩ t i, ENNReal.ofReal (f p) := lintegral_iUnion_le _ _
      _ = ∑ i, ∫⁻ p in s ∩ t i, ENNReal.ofReal (f p) := tsum_fintype _
  · rw [integral_undef hint]
    exact Finset.sum_nonneg fun i _ ↦ setIntegral_nonneg (hs.inter (ht i)) (fun p hp ↦ hf p hp.1)

/-- For real functions `f₁` to `f₇` integrable on a set `S` in `ℝ × ℝ` and real `s t u`,
`∫ p in S, (f₁ p + f₂ p + f₃ p + s * f₄ p + t * f₅ p + u * f₆ p - f₇ p) = (∫ p in S, f₁ p) + (∫ p in
S, f₂ p) + (∫ p in S, f₃ p) + s * (∫ p in S, f₄ p) + t * (∫ p in S, f₅ p) + u * (∫ p in S, f₆ p) - ∫
p in S, f₇ p`. The proof applies additivity and homogeneity of the integral term by term. -/
theorem setIntegral_linear_combination_seven {S : Set (ℝ × ℝ)} {f₁ f₂ f₃ f₄ f₅ f₆ f₇ : ℝ × ℝ → ℝ}
    (h₁ : IntegrableOn f₁ S) (h₂ : IntegrableOn f₂ S)
    (h₃ : IntegrableOn f₃ S) (h₄ : IntegrableOn f₄ S) (h₅ : IntegrableOn f₅ S)
        (h₆ : IntegrableOn f₆ S)
    (h₇ : IntegrableOn f₇ S) (s t u : ℝ) :
    ∫ p in S, (f₁ p + f₂ p + f₃ p + s * f₄ p + t * f₅ p + u * f₆ p - f₇ p)
      = (∫ p in S, f₁ p) + (∫ p in S, f₂ p) + (∫ p in S, f₃ p) + s * (∫ p in S, f₄ p)
        + t * (∫ p in S, f₅ p) + u * (∫ p in S, f₆ p) - ∫ p in S, f₇ p := by
  rw [integral_sub, integral_add, integral_add, integral_add, integral_add, integral_add,
    integral_const_mul, integral_const_mul, integral_const_mul]
  · exact h₁
  · exact h₂
  · exact h₁.add h₂
  · exact h₃
  · exact (h₁.add h₂).add h₃
  · exact h₄.const_mul s
  · exact ((h₁.add h₂).add h₃).add (h₄.const_mul s)
  · exact h₅.const_mul t
  · exact (((h₁.add h₂).add h₃).add (h₄.const_mul s)).add (h₅.const_mul t)
  · exact h₆.const_mul u
  · exact ((((h₁.add h₂).add h₃).add (h₄.const_mul s)).add (h₅.const_mul t)).add (h₆.const_mul u)
  · exact h₇

/-- If `χ : ℝ × ℝ → ℝ` vanishes outside a set `R`, then for every `A : ℝ × ℝ → ℂ`,
`∫ p in R, A p * (χ p : ℂ) = ∫ p, (χ p : ℂ) * A p`. -/
theorem setIntegral_mul_ofReal_eq_integral {R : Set (ℝ × ℝ)} {χ : ℝ × ℝ → ℝ} (A : ℝ × ℝ → ℂ)
    (hχ : ∀ p, p ∉ R → χ p = 0) :
    ∫ p in R, A p * Complex.ofReal (χ p) = ∫ p, ((χ p : ℝ) : ℂ) * A p := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp ↦ by simp [hχ p hp])]
  exact integral_congr_ae (Eventually.of_forall fun p ↦ mul_comm _ _)

/-- Let `Q j r = ∑ i ∈ Finset.range (j + 1), cf j i * r ^ i` with `0 < cf j j`, and suppose that
`∫ r in s, ρ r * Q j r * Q j' r` is `1` if `j = j'` and `0` otherwise, and that every
`fun r ↦ ρ r * r ^ i * Q j r` is integrable on `s`. Then `∫ r in s, ρ r * r ^ a * Q j r = 0`
whenever `a < j`. The proof is by strong induction on `a`, expanding `Q a` in monomials and solving
for the term with `r ^ a`. -/
theorem setIntegral_pow_mul_orthonormal_eq_zero (s : Set ℝ) (ρ : ℝ → ℝ) (Q : ℕ → ℝ → ℝ)
    (cf : ℕ → ℕ → ℝ)
    (hQ : ∀ j r, Q j r = ∑ i ∈ Finset.range (j + 1), cf j i * r ^ i) (hlead : ∀ j, 0 < cf j j)
    (horth : ∀ j j', ∫ r in s, ρ r * Q j r * Q j' r = if j = j' then 1 else 0)
    (hint : ∀ i j, IntegrableOn (fun r ↦ ρ r * r ^ i * Q j r) s) :
    ∀ a j, a < j → ∫ r in s, ρ r * r ^ a * Q j r = 0 := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro j haj
    have hexp : ∀ r, ρ r * Q a r * Q j r =
        ∑ i ∈ Finset.range (a + 1), cf a i * (ρ r * r ^ i * Q j r) := by
      intro r
      rw [hQ a r, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    have h1 : ∫ r in s, ρ r * Q a r * Q j r =
        ∑ i ∈ Finset.range (a + 1), cf a i * ∫ r in s, ρ r * r ^ i * Q j r := by
      simp_rw [hexp]
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl ?_
        intro i _
        rw [integral_const_mul]
      · intro i _
        exact Integrable.const_mul (hint i j) _
    rw [horth a j, ite_eq_right (Nat.ne_of_lt haj), Finset.sum_range_succ] at h1
    have h2 : ∑ i ∈ Finset.range a, cf a i * ∫ r in s, ρ r * r ^ i * Q j r = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      rw [ih i (Finset.mem_range.mp hi) j (lt_trans (Finset.mem_range.mp hi) haj), mul_zero]
    rw [h2, zero_add] at h1
    have := hlead a
    rcases mul_eq_zero.mp h1.symm with h | h
    · linarith
    · exact h

/-- Let `A ⊆ ℝ` be measurable, `lo ≤ mid` and `mid ≤ hi`, and `g : ℝ × ℝ → ℂ` integrable on
`A ×ˢ Icc lo hi`. Then
`∫ p in A ×ˢ Icc lo hi, g p = (∫ p in A ×ˢ Icc lo mid, g p) + ∫ p in A ×ˢ Icc mid hi, g
p`. The proof uses that the two pieces meet inside the null set `univ ×ˢ {mid}`. -/
theorem setIntegral_prod_Icc_eq_add (A : Set ℝ) (hA : MeasurableSet A) {lo mid hi : ℝ}
    (h1 : lo ≤ mid) (h2 : mid ≤ hi)
    (g : ℝ × ℝ → ℂ) (hg : IntegrableOn g (A ×ˢ Set.Icc lo hi)) :
    ∫ p in A ×ˢ Set.Icc lo hi, g p = (∫ p in A ×ˢ Set.Icc lo mid, g p) +
        ∫ p in A ×ˢ Set.Icc mid hi, g p := by
  have hs1 : A ×ˢ Set.Icc lo mid ⊆ A ×ˢ Set.Icc lo hi :=
      Set.prod_mono le_rfl (Set.Icc_subset_Icc le_rfl h2)
  have hs2 : A ×ˢ Set.Icc mid hi ⊆ A ×ˢ Set.Icc lo hi :=
      Set.prod_mono le_rfl (Set.Icc_subset_Icc h1 le_rfl)
  have hi1 := hg.mono_set hs1
  have hi2 := hg.mono_set hs2
  rw [← Set.Icc_union_Icc_eq_Icc h1 h2, Set.prod_union]
  refine setIntegral_union₀ ?_ (hA.prod measurableSet_Icc).nullMeasurableSet hi1 hi2
  unfold AEDisjoint
  apply measure_mono_null (t := Set.univ ×ˢ {mid})
  · rintro ⟨a, b⟩ ⟨⟨_, hb1⟩, ⟨_, hb2⟩⟩
    exact ⟨trivial, le_antisymm hb1.2 hb2.1⟩
  · rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp

/-- Let the closed intervals `Icc (lo s) (hi s)`, `s ∈ T`, with `T` a finite set, cover `Icc z₁ z₂`,
satisfy `z₁ ≤ lo s` and `hi s ≤ z₂`, and overlap pairwise at most at endpoints (`hi s ≤ lo s'` or
`hi s' ≤ lo s` for `s ≠ s'`). If `A ⊆ ℝ` is measurable and `f : ℝ × ℝ → ℂ` is integrable on
`A ×ˢ Icc z₁ z₂`, then `∫ p in A ×ˢ Icc z₁ z₂, f p = ∑ s ∈ T, ∫ p in A ×ˢ Icc (lo s) (hi s), f p`.
The proof writes the product set as a finite union of sets `A ×ˢ Icc (lo s) (hi s)` whose pairwise
intersections lie in null sets `A ×ˢ {x}`. -/
theorem setIntegral_prod_Icc_eq_sum_of_partition {ι : Type*} (T : Finset ι) (lo hi : ι → ℝ)
    {z₁ z₂ : ℝ}
    (hcov : ∀ u ∈ Icc z₁ z₂, ∃ s ∈ T, lo s ≤ u ∧ u ≤ hi s) (hin : ∀ s ∈ T, z₁ ≤ lo s ∧ hi s ≤ z₂)
    (hdis : ∀ s ∈ T, ∀ s' ∈ T, s ≠ s' → hi s ≤ lo s' ∨ hi s' ≤ lo s) {A : Set ℝ}
        (hA : MeasurableSet A) {f : ℝ × ℝ → ℂ}
    (hf : IntegrableOn f (A ×ˢ Icc z₁ z₂)) :
    ∫ p in A ×ˢ Icc z₁ z₂, f p = ∑ s ∈ T, ∫ p in A ×ˢ Icc (lo s) (hi s), f p := by
  classical
  have hU : A ×ˢ Icc z₁ z₂ = ⋃ i : T, A ×ˢ Icc (lo i) (hi i) := by
    ext p
    simp only [mem_prod, mem_iUnion, Subtype.exists, exists_prop, mem_Icc]
    constructor
    · rintro ⟨hA, hp⟩
      obtain ⟨s, hs, h1, h2⟩ := hcov p.2 hp
      exact ⟨s, hs, hA, h1, h2⟩
    · rintro ⟨s, hs, hA, h1, h2⟩
      exact ⟨hA, (hin s hs).1.trans h1, h2.trans (hin s hs).2⟩
  have hnull : ∀ (x : ℝ), (volume : Measure (ℝ × ℝ)) (A ×ˢ {x}) = 0 := by
    intro x
    rw [Measure.volume_eq_prod]
    exact measure_mono_null (prod_mono (subset_univ A) subset_rfl) (by rw [Measure.prod_prod]; simp)
  rw [hU, integral_iUnion_ae]
  · rw [tsum_fintype]
    exact Finset.sum_coe_sort T (fun s ↦ ∫ p in A ×ˢ Icc (lo s) (hi s), f p)
  · intro i
    exact (hA.prod measurableSet_Icc).nullMeasurableSet
  · intro i j hij
    have hne : (i : ι) ≠ j := fun e ↦ hij (Subtype.ext e)
    rcases hdis i i.2 j j.2 hne with h | h
    · refine measure_mono_null ?_ (hnull (hi i))
      rintro p ⟨⟨hA, _, h2⟩, _, h3, _⟩
      exact ⟨hA, le_antisymm h2 (h.trans h3)⟩
    · refine measure_mono_null ?_ (hnull (hi j))
      rintro p ⟨⟨hA, h1, _⟩, _, _, h4⟩
      exact ⟨hA, le_antisymm h4 (h.trans h1)⟩
  · rw [← hU]; exact hf

/-- Let `g : α → ℂ` and `e : ι → α → ℂ` satisfy
`∫ x in s, g x * e i x * e k x ∂μ = if i = k then 1 else 0` for all `i`, `k` in a finset `I`, with
each `fun x ↦ g x * e i x * e k x` integrable on `s` for `μ`. Then for `k ∈ I` and any `b : ι → ℂ`,
`∫ x in s, g x * (∑ i ∈ I, b i * e i x) * e k x ∂μ = b k`. The proof expands the sum, exchanges it
with the integral, and keeps only the term `i = k`. -/
theorem setIntegral_sum_mul_eq_coeff_of_orthonormal {α ι : Type*} [MeasurableSpace α]
    [DecidableEq ι] (μ : Measure α) (s : Set α)
    (I : Finset ι) (g : α → ℂ) (e : ι → α → ℂ)
    (hint : ∀ i ∈ I, ∀ k ∈ I, IntegrableOn (fun x ↦ g x * e i x * e k x) s μ)
    (hON : ∀ i ∈ I, ∀ k ∈ I, ∫ x in s, g x * e i x * e k x ∂μ = if i = k then 1 else 0)
    (b : ι → ℂ) (k : ι) (hk : k ∈ I) :
    ∫ x in s, g x * (∑ i ∈ I, b i * e i x) * e k x ∂μ = b k := by
  have h : (fun x ↦ g x * (∑ i ∈ I, b i * e i x) * e k x) =
      fun x ↦ ∑ i ∈ I, b i * (g x * e i x * e k x) := by
    funext x
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [h, integral_finsetSum _ fun i hi ↦ (hint i hi k hk).const_mul (b i)]
  rw [Finset.sum_eq_single k]
  · rw [integral_const_mul, hON k hk k hk, ite_eq_left rfl, mul_one]
  · intro i hi hik
    rw [integral_const_mul, hON i hi k hk, ite_eq_right hik, mul_zero]
  · intro h
    exact absurd hk h

/-- Let `S ⊆ ℝ × ℝ` and let `Y a b : ℝ × ℝ → ℂ` be integrable on `S` for all `a b : Fin 3`. Then for
all complex coefficients `C a b`,
`∫ p in S, ∑ a, ∑ b, C a b * Y a b p = ∑ a, ∑ b, C a b * ∫ p in S, Y a b p`. -/
theorem setIntegral_sum_sum_const_mul (S : Set (ℝ × ℝ)) (C : Fin 3 → Fin 3 → ℂ)
    (Y : Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (h : ∀ a b, IntegrableOn (Y a b) S) :
    ∫ p in S, ∑ a, ∑ b, C a b * Y a b p = ∑ a, ∑ b, C a b * ∫ p in S, Y a b p := by
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun a _ ↦ ?_)
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl (fun b _ ↦ integral_const_mul _ _)
    · intro b _; exact (h a b).const_mul _
  · intro a _; exact integrable_finsetSum _ (fun b _ ↦ (h a b).const_mul _)

/-- For every `f : ℝ → ℂ`, with no measurability hypothesis,
`‖∫ θ in Ioo (-π) π, f θ‖ₑ ^ 2 ≤ ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo (-π) π, ‖f θ‖ₑ ^
2`. When `f` is not almost everywhere strongly measurable on the interval, the integral on the left
is zero by definition. -/
theorem sq_enorm_integral_le_mul_lintegral_sq (f : ℝ → ℂ) :
    ‖∫ θ in Ioo (-π) π, f θ‖ₑ ^ 2 ≤ ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo (-π) π, ‖f θ‖ₑ ^ 2 := by
  by_cases hf : AEStronglyMeasurable f (volume.restrict (Ioo (-π) π))
  · exact (pow_le_pow_left₀ (by
      positivity) (eNorm_integral_le_lintegral_eNorm _) 2).trans
          (sq_lintegral_enorm_le_mul_lintegral_sq hf)
  · rw [integral_non_aestronglyMeasurable hf, eNorm_zero]
    simp

/-- Let `n` be a finite type, `T` a finite set of indices, `y : n → ℂ`, and `h i ι : ℝ × ℝ → ℂ`
integrable on a set `S` for all `i` and all `ι ∈ T`. Then
`star y ⬝ᵥ (fun i ↦ ∑ ι ∈ T, ∫ p in S, h i ι p) = ∑ ι ∈ T, ∫ p in S, ∑ i, star (y i) * h i ι p`. -/
theorem star_dotProduct_sum_setIntegral {S : Set (ℝ × ℝ)} {n α : Type*} [Fintype n] (T : Finset α)
    (y : n → ℂ) (h : n → α → ℝ × ℝ → ℂ)
    (hh : ∀ i, ∀ ι ∈ T, IntegrableOn (h i ι) S) :
    star y ⬝ᵥ (fun i ↦ ∑ ι ∈ T, ∫ p in S, h i ι p) = ∑ ι ∈ T, ∫ p in S, ∑ i,
        star (y i) * h i ι p := by
  simp only [dotProduct, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ι hι ↦ ?_
  rw [integral_finsetSum _ (fun i _ ↦ (hh i ι hι).const_mul _)]
  simp only [integral_const_mul]

/-- Let `n` be a finite type, `T` a finite set of indices, `c : n → ℂ`, and `g i ι : ℝ × ℝ → ℂ`
integrable on a set `S` for all `i` and all `ι ∈ T`. Then
`∑ i, (∑ ι ∈ T, ∫ p in S, g i ι p) * c i = ∑ ι ∈ T, ∫ p in S, ∑ i, g i ι p * c i`. -/
theorem sum_integral_mul {S : Set (ℝ × ℝ)} {n α : Type*} [Fintype n] (T : Finset α) (c : n → ℂ)
    (g : n → α → ℝ × ℝ → ℂ)
    (hg : ∀ i, ∀ ι ∈ T, IntegrableOn (g i ι) S) :
    ∑ i, (∑ ι ∈ T, ∫ p in S, g i ι p) * c i = ∑ ι ∈ T, ∫ p in S, ∑ i, g i ι p * c i := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ι hι ↦ ?_
  rw [integral_finsetSum _ (fun i _ ↦ (hg i ι hι).mul_const _)]
  simp only [integral_mul_const]

/-- Bessel inequality for a weight `ρ` that is nonnegative almost everywhere and real functions
`e k`, `k ∈ s`, with `s` a finite set of natural numbers and `∫ x, ρ x * e k x * e k' x ∂μ` equal to
`1` if `k = k'` and `0` otherwise. If `g : α → ℂ` and the functions `fun x ↦ ρ x * ‖g x‖ ^ 2`,
`fun x ↦ (ρ x : ℂ) * g x * (e k x : ℂ)` and `fun x ↦ ρ x * e k x * e k' x` are integrable for
`k, k' ∈ s`, then `∑ k ∈ s, ‖∫ x, (ρ x : ℂ) * g x * (e k x : ℂ) ∂μ‖ ^ 2 ≤ ∫ x, ρ x * ‖g x‖ ^ 2 ∂μ`.
The proof expands the nonnegative integral of `ρ x * ‖g x - ∑ k ∈ s, a k * (e k x : ℂ)‖ ^ 2`, where
`a k` is the `k`-th integral on the left. -/
theorem sum_norm_sq_integral_le_of_orthonormal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ℕ) (ρ : α → ℝ) (e : ℕ → α → ℝ)
    (g : α → ℂ) (hρ : ∀ᵐ x ∂μ, 0 ≤ ρ x)
    (hgg : Integrable (fun x ↦ ρ x * ‖g x‖ ^ 2) μ)
    (hge : ∀ k ∈ s, Integrable (fun x ↦ (ρ x : ℂ) * g x * (e k x : ℂ)) μ)
    (hee : ∀ k ∈ s, ∀ k' ∈ s, Integrable (fun x ↦ ρ x * e k x * e k' x) μ)
    (horth : ∀ k ∈ s, ∀ k' ∈ s, ∫ x, ρ x * e k x * e k' x ∂μ = if k = k' then 1 else 0) :
    ∑ k ∈ s, ‖∫ x, (ρ x : ℂ) * g x * (e k x : ℂ) ∂μ‖ ^ 2 ≤ ∫ x, ρ x * ‖g x‖ ^ 2 ∂μ := by
  set a : ℕ → ℂ := fun k ↦ ∫ x, (ρ x : ℂ) * g x * (e k x : ℂ) ∂μ with ha
  have hpt : ∀ x, ((ρ x * ‖g x - ∑ k ∈ s, a k * (e k x : ℂ)‖ ^ 2 : ℝ) : ℂ)
      = ((ρ x * ‖g x‖ ^ 2 : ℝ) : ℂ)
        - ∑ k ∈ s, (starRingEnd ℂ) (a k) * ((ρ x : ℂ) * g x * (e k x : ℂ))
        - ∑ k ∈ s, a k * (starRingEnd ℂ) ((ρ x : ℂ) * g x * (e k x : ℂ))
        + ∑ k ∈ s, ∑ k' ∈ s, (a k * (starRingEnd ℂ) (a k')) * ((ρ x * e k x * e k' x : ℝ) : ℂ) := by
    intro x
    have hS' : (starRingEnd ℂ) (∑ k ∈ s, a k * (e k x : ℂ)) = ∑ k ∈ s,
        (starRingEnd ℂ) (a k) * (e k x : ℂ) := by
      rw [map_sum]; simp only [map_mul, Complex.conj_ofReal]
    have h1 : (ρ x : ℂ) * (g x * ∑ k ∈ s, (starRingEnd ℂ) (a k) * (e k x : ℂ))
        = ∑ k ∈ s, (starRingEnd ℂ) (a k) * ((ρ x : ℂ) * g x * (e k x : ℂ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ ↦ by ring
    have h2 : (ρ x : ℂ) * ((∑ k ∈ s, a k * (e k x : ℂ)) * (starRingEnd ℂ) (g x))
        = ∑ k ∈ s, a k * (starRingEnd ℂ) ((ρ x : ℂ) * g x * (e k x : ℂ)) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by simp only [map_mul, Complex.conj_ofReal]; ring
    have h3 : (ρ x : ℂ) * ((∑ k ∈ s, a k * (e k x : ℂ)) * ∑ k' ∈ s,
        (starRingEnd ℂ) (a k') * (e k' x : ℂ))
        = ∑ k ∈ s, ∑ k' ∈ s, (a k * (starRingEnd ℂ) (a k')) * ((ρ x * e k x * e k' x : ℝ) : ℂ) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k' _ ↦ ?_
      push_cast; ring
    have h4 : ((ρ x * ‖g x - ∑ k ∈ s, a k * (e k x : ℂ)‖ ^ 2 : ℝ) : ℂ)
        = (ρ x : ℂ) * ((g x - ∑ k ∈ s, a k * (e k x : ℂ)) *
            (starRingEnd ℂ) (g x - ∑ k ∈ s, a k * (e k x : ℂ))) := by
      rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.mul_conj']
    have h5 : ((ρ x * ‖g x‖ ^ 2 : ℝ) : ℂ) = (ρ x : ℂ) * (g x * (starRingEnd ℂ) (g x)) := by
      rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.mul_conj']
    rw [h4, h5, map_sub, hS', ← h1, ← h2, ← h3]
    ring
  have hI1 : Integrable (fun x ↦ ((ρ x * ‖g x‖ ^ 2 : ℝ) : ℂ)) μ := hgg.ofReal
  have hI2 : Integrable (fun x ↦ ∑ k ∈ s, (starRingEnd ℂ) (a k) * ((ρ x : ℂ) * g x * (e k x : ℂ)))
      μ :=
    integrable_finsetSum _ fun k hk ↦ (hge k hk).const_mul _
  have hconj : ∀ k ∈ s, Integrable (fun x ↦ (starRingEnd ℂ) ((ρ x : ℂ) * g x * (e k x : ℂ))) μ := by
    intro k hk
    exact (Complex.conjCLE.toContinuousLinearMap).integrable_comp (hge k hk)
  have hI3 : Integrable (fun x ↦ ∑ k ∈ s, a k * (starRingEnd ℂ) ((ρ x : ℂ) * g x * (e k x : ℂ)))
      μ :=
    integrable_finsetSum _ fun k hk ↦ (hconj k hk).const_mul _
  have hI4 : Integrable (fun x ↦ ∑ k ∈ s, ∑ k' ∈ s, (a k * (starRingEnd ℂ) (a k')) *
      ((ρ x * e k x * e k' x : ℝ) : ℂ)) μ :=
    integrable_finsetSum _ fun k hk ↦ integrable_finsetSum _ fun k' hk' ↦
        ((hee k hk k' hk').ofReal).const_mul _
  have hint : (((∫ x, ρ x * ‖g x - ∑ k ∈ s, a k * (e k x : ℂ)‖ ^ 2 ∂μ) : ℝ) : ℂ)
      = ((∫ x, ρ x * ‖g x‖ ^ 2 ∂μ : ℝ) : ℂ) - ((∑ k ∈ s, ‖a k‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp_rw [hpt]
    have hI12 : Integrable (fun x ↦ ((ρ x * ‖g x‖ ^ 2 : ℝ) : ℂ)
        - ∑ k ∈ s, (starRingEnd ℂ) (a k) * ((ρ x : ℂ) * g x * (e k x : ℂ))) μ := hI1.sub hI2
    have hI123 : Integrable (fun x ↦ ((ρ x * ‖g x‖ ^ 2 : ℝ) : ℂ)
        - ∑ k ∈ s, (starRingEnd ℂ) (a k) * ((ρ x : ℂ) * g x * (e k x : ℂ))
        - ∑ k ∈ s, a k * (starRingEnd ℂ) ((ρ x : ℂ) * g x * (e k x : ℂ))) μ := hI12.sub hI3
    rw [integral_add hI123 hI4, integral_sub hI12 hI3, integral_sub hI1 hI2,
      integral_complex_ofReal, integral_finsetSum _ fun k hk ↦ (hge k hk).const_mul _,
      integral_finsetSum _ fun k hk ↦ (hconj k hk).const_mul _,
      integral_finsetSum _ fun k hk ↦ integrable_finsetSum _ fun k' hk' ↦
          ((hee k hk k' hk').ofReal).const_mul _]
    simp only [integral_const_mul, integral_conj]
    have e4 : ∀ k ∈ s, ∫ x, ∑ k' ∈ s, (a k * (starRingEnd ℂ) (a k')) *
        ((ρ x * e k x * e k' x : ℝ) : ℂ) ∂μ
        = a k * (starRingEnd ℂ) (a k) := by
      intro k hk
      rw [integral_finsetSum _ fun k' hk' ↦ ((hee k hk k' hk').ofReal).const_mul _]
      simp only [integral_const_mul, integral_complex_ofReal]
      rw [Finset.sum_congr rfl fun k' hk' ↦ by rw [horth k hk k' hk']]
      rw [Finset.sum_eq_single_of_mem k hk (fun k' _ hne ↦ by
        rw [ite_eq_right (Ne.symm hne)]; simp)]
      simp
    rw [Finset.sum_congr rfl e4]
    have hak : ∀ k, (∫ x, (ρ x : ℂ) * g x * (e k x : ℂ) ∂μ) = a k := fun k ↦ rfl
    simp only [hak]
    have e5 : ∀ k, (starRingEnd ℂ) (a k) * a k = ((‖a k‖ ^ 2 : ℝ) : ℂ) := fun k ↦ by
      rw [mul_comm, Complex.mul_conj']; push_cast; ring
    have e6 : ∀ k, a k * (starRingEnd ℂ) (a k) = ((‖a k‖ ^ 2 : ℝ) : ℂ) := fun k ↦ by
      rw [Complex.mul_conj']; push_cast; ring
    simp only [e5, e6]
    push_cast
    ring
  have hnn : 0 ≤ ∫ x, ρ x * ‖g x - ∑ k ∈ s, a k * (e k x : ℂ)‖ ^ 2 ∂μ :=
    integral_nonneg_of_ae (hρ.mono fun x hx ↦ mul_nonneg hx (by positivity))
  have hre := congrArg Complex.re hint
  simp only [Complex.ofReal_re, Complex.sub_re] at hre
  linarith

/-- For a `C^1` function `g : ℝ → ℝ` with compact support and any real `b`,
`2 * |g b| ≤ ∫ t, |deriv g t|`. The proof writes `g b` as the integral of `deriv g` over `Iic b` and
as minus its integral over `Ioi b`, and adds the two resulting bounds. -/
theorem two_abs_le_integral_abs_deriv {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (b : ℝ) : 2 * |g b| ≤ ∫ t, |deriv g t| := by
  have hd : ∀ x, HasDerivAt g (deriv g x) x := fun x ↦
    (hg.differentiable one_ne_zero x).hasDerivAt
  have hint : Integrable (deriv g) :=
    (hg.continuous_deriv le_rfl).integrable_of_hasCompactSupport hc.deriv
  have hlim : Tendsto g atTop (𝓝 0) := by
    have h := hc
    rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact] at h
    exact (h.filter_mono atTop_le_cocompact).tendsto
  have h1 : ∫ x in Iic b, deriv g x = g b := hc.integral_Iic_deriv_eq hg b
  have h2 : ∫ x in Ioi b, deriv g x = 0 - g b :=
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ ↦ hd x) hint.integrableOn hlim
  have e1 : |g b| ≤ ∫ x in Iic b, |deriv g x| := by
    rw [← h1]
    exact abs_integral_le_integral_abs
  have e2 : |g b| ≤ ∫ x in Ioi b, |deriv g x| := by
    have h3 : |g b| = |∫ x in Ioi b, deriv g x| := by
      rw [h2, zero_sub, abs_neg]
    rw [h3]
    exact abs_integral_le_integral_abs
  have hsplit : ∫ t, |deriv g t| =
      (∫ x in Iic b, |deriv g x|) + ∫ x in Ioi b, |deriv g x| := by
    rw [← setIntegral_univ, ← Iic_union_Ioi (a := b),
      setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hint.abs.integrableOn
        hint.abs.integrableOn]
  linarith

/-- Let `ψ χ : ℝ × ℝ → ℝ` vanish outside a set `R`, and let `A B : ℝ × ℝ → ℂ`. If
`∫ p, (χ p : ℂ) * A p = -∫ p, (ψ p : ℂ) * B p`, then
`∫ p in R, A p * (χ p : ℂ) = -∫ p in R, B p * (ψ p : ℂ)`. -/
theorem setIntegral_mul_eq_neg_of_support_subset {A B : ℝ × ℝ → ℂ} {ψ χ : ℝ × ℝ → ℝ}
    {R : Set (ℝ × ℝ)}
    (hψ : ∀ p, p ∉ R → ψ p = 0) (hχ : ∀ p, p ∉ R → χ p = 0)
    (h : ∫ p, ((χ p : ℝ) : ℂ) * A p = -∫ p, ((ψ p : ℝ) : ℂ) * B p) :
    ∫ p in R, A p * ((χ p : ℝ) : ℂ) = -∫ p in R, B p * ((ψ p : ℝ) : ℂ) := by
  rw [integral_mul_comm_real, integral_mul_comm_real,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp ↦ by rw [hχ p hp]; simp,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp ↦ by rw [hψ p hp]; simp]
  exact h

/-- Let `ρ : ℝ → ℝ` and the functions `P l : ℝ → ℝ` be continuous, with
`∫ x in Icc a b, ρ x * P l x * P l' x` equal to `1` if `l = l'` and `0` otherwise. Then for a finite
type `C`, a finite set `s` of natural numbers and complex coefficients `A c l`,
`∫ x in Icc a b, ρ x * ∑ c, ‖∑ l ∈ s, A c l * (P l x : ℂ)‖ ^ 2 = ∑ c, ∑ l ∈ s, ‖A c l‖ ^
2`. The proof exchanges the integral with the sum over `c` and applies the Parseval identity for a
weighted orthonormal family to each term. -/
theorem setIntegral_mul_sum_norm_sq_orthonormal (a b : ℝ) (ρ : ℝ → ℝ) (hρ : Continuous ρ)
    (P : ℕ → ℝ → ℝ) (hP : ∀ l, Continuous (P l))
    (horth : ∀ l l', ∫ x in Set.Icc a b, ρ x * P l x * P l' x = if l = l' then 1 else 0)
    {C : Type*} [Fintype C] (s : Finset ℕ) (A : C → ℕ → ℂ) :
    ∫ x in Set.Icc a b, ρ x * ∑ c, ‖∑ l ∈ s, A c l * (P l x : ℂ)‖ ^ 2 = ∑ c, ∑ l ∈ s,
        ‖A c l‖ ^ 2 := by
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun c _ ↦ Continuous.integrableOn_Icc (by
    exact hρ.mul ((continuous_finsetSum _ fun l _ ↦ continuous_const.mul
      (Complex.continuous_ofReal.comp (hP l))).norm.pow 2)))]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  refine integral_mul_norm_sq_sum_of_orthonormal s ρ (fun l x ↦ (P l x : ℂ)) (A c)
      (fun k _ k' _ ↦ ?_) (fun k _ k' _ ↦ ?_)
  · exact Continuous.integrableOn_Icc (by fun_prop)
  · have e : ∀ x, (ρ x : ℂ) * ((P k x : ℂ) * (starRingEnd ℂ) (P k' x : ℂ)) =
        ((ρ x * P k x * P k' x : ℝ) : ℂ) := by
      intro x; rw [Complex.conj_ofReal]; push_cast; ring
    simp_rw [e]
    rw [integral_complex_ofReal, horth k k']
    split_ifs <;> simp

/-- Let `f : α → ℝ` be almost everywhere strongly measurable for `μ` with
`∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ⊤` and `∫⁻ x, ENNReal.ofReal (-f x) ∂μ ≠ ⊤`. Then
`∫ x, f x ∂μ = (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal - (∫⁻ x, ENNReal.ofReal (-f x) ∂μ).toReal`. -/
theorem integral_eq_lintegral_sub_of_ne_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (hp : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ⊤)
    (hn : ∫⁻ x, ENNReal.ofReal (-f x) ∂μ ≠ ⊤) :
    ∫ x, f x ∂μ = (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal -
        (∫⁻ x, ENNReal.ofReal (-f x) ∂μ).toReal :=
  integral_eq_lintegral_pos_part_sub_lintegral_neg_part
      (integrable_of_lintegral_pos_neg_ne_top hf hp hn)

/-- Let `f₁` and `f₂` be complex functions integrable on a set `s` in `ℝ × ℝ`. If `f p = f₁ p +
Complex.I * f₂ p` for almost every `p` in `s`, then `∫ p in s, f p = (∫ p in s, f₁ p) + Complex.I *
∫ p in s, f₂ p`. A case of `PDE.Analysis.setIntegral_eq_add_const_mul_setIntegral`. -/
theorem setIntegral_eq_add_I_mul_setIntegral {s : Set (ℝ × ℝ)} {f f₁ f₂ : ℝ × ℝ → ℂ}
    (h₁ : IntegrableOn f₁ s)
    (h₂ : IntegrableOn f₂ s) (he : ∀ᵐ p ∂(volume.restrict s), f p = f₁ p + Complex.I * f₂ p) :
    ∫ p in s, f p = (∫ p in s, f₁ p) + Complex.I * ∫ p in s, f₂ p :=
  setIntegral_eq_add_const_mul_setIntegral Complex.I he h₁ h₂

/-- Let `S` be a set in `ℝ × ℝ` with `0 < p.1` for almost every `p` in `S`, let
`s : ℝ × ℝ → ℝ → ℝ → ℝ` be jointly almost everywhere strongly measurable for the product of Lebesgue
measure restricted to `S`, to `Icc 0 1` and to `Icc 0 (2 * π)`, and write `L g` for
`∫⁻ p in S, (ENNReal.ofReal (1 / (2 * π)) * ∫⁻ τ in Icc 0 1, ∫⁻ φ in Icc 0 (2 * π), ENNReal.ofReal
(g p τ φ)) * ENNReal.ofReal p.1`. If `L s ≠ ⊤` and `L (-s) ≠ ⊤`, then `∫ p in S, ((1 / (2 * π)) * ∫
τ in 0..1, ∫ φ in 0..2 * π, s p τ φ) * p.1 = (L s).toReal - (L
(-s)).toReal`. The proof shows that for almost every `p` the slice `(τ, φ) ↦ s p τ
φ` is integrable and its integral is the difference of the two inner lower integrals, then
integrates over `S`. -/
theorem setIntegral_mean_mul_fst_eq_lintegral_sub {S : Set (ℝ × ℝ)}
    (hS : ∀ᵐ p ∂(volume.restrict S), 0 < p.1) (s : ℝ × ℝ → ℝ → ℝ → ℝ)
    (hs : AEStronglyMeasurable (fun z : (ℝ × ℝ) × ℝ × ℝ ↦ s z.1 z.2.1 z.2.2)
      ((volume.restrict S).prod
        ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))))))
    (hP : ∫⁻ p in S, (ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Icc (0 : ℝ) 1,
      ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (s p τ φ)) * ENNReal.ofReal p.1 ≠ ⊤)
    (hN : ∫⁻ p in S, (ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Icc (0 : ℝ) 1,
      ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (-s p τ φ)) * ENNReal.ofReal p.1 ≠ ⊤) :
    ∫ p in S, ((1 / (2 * Real.pi)) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi), s p τ φ) *
        p.1
      = (∫⁻ p in S, (ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Icc (0 : ℝ) 1,
          ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (s p τ φ)) * ENNReal.ofReal p.1).toReal
        - (∫⁻ p in S, (ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ τ in Icc (0 : ℝ) 1,
          ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (-s p τ φ)) *
              ENNReal.ofReal p.1).toReal := by
  set c : ℝ := 1 / (2 * Real.pi) with hcdef
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  set ν : Measure (ℝ × ℝ) := (volume.restrict (Icc (0 : ℝ) 1)).prod
      (volume.restrict (Icc (0 : ℝ) (2 * Real.pi)))
    with hνdef
  set Sp : ℝ × ℝ → ℝ≥0∞ := fun p ↦ ∫⁻ y, ENNReal.ofReal (s p y.1 y.2) ∂ν with hSp
  set Sn : ℝ × ℝ → ℝ≥0∞ := fun p ↦ ∫⁻ y, ENNReal.ofReal (-s p y.1 y.2) ∂ν with hSn
  have hsec := hs.prodMk_left
  have hSpm : AEMeasurable Sp (volume.restrict S) :=
    hs.aemeasurable.ennreal_ofReal.lintegral_prod_right'
  have hSnm : AEMeasurable Sn (volume.restrict S) :=
    hs.aemeasurable.neg.ennreal_ofReal.lintegral_prod_right'
  have hit : ∀ᵐ p ∂(volume.restrict S),
      (∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (s p τ φ)) = Sp p ∧
      (∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (-s p τ φ)) =
          Sn p := by
    filter_upwards [hsec] with p hp
    exact ⟨(lintegral_prod (fun y : ℝ × ℝ ↦ ENNReal.ofReal (s p y.1 y.2))
        hp.aemeasurable.ennreal_ofReal).symm,
      (lintegral_prod (fun y : ℝ × ℝ ↦ ENNReal.ofReal (-s p y.1 y.2))
          hp.aemeasurable.neg.ennreal_ofReal).symm⟩
  set A : ℝ × ℝ → ℝ≥0∞ := fun p ↦ ENNReal.ofReal c * Sp p * ENNReal.ofReal p.1 with hA
  set B : ℝ × ℝ → ℝ≥0∞ := fun p ↦ ENNReal.ofReal c * Sn p * ENNReal.ofReal p.1 with hB
  have hAm : AEMeasurable A (volume.restrict S) :=
    (hSpm.const_mul _).mul measurable_fst.ennreal_ofReal.aemeasurable
  have hBm : AEMeasurable B (volume.restrict S) :=
    (hSnm.const_mul _).mul measurable_fst.ennreal_ofReal.aemeasurable
  have eA : (∫⁻ p in S, (ENNReal.ofReal c * ∫⁻ τ in Icc (0 : ℝ) 1,
      ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (s p τ φ)) * ENNReal.ofReal p.1) =
          ∫⁻ p in S, A p := by
    refine lintegral_congr_ae ?_
    filter_upwards [hit] with p hp
    rw [hp.1]
  have eB : (∫⁻ p in S, (ENNReal.ofReal c * ∫⁻ τ in Icc (0 : ℝ) 1,
      ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (-s p τ φ)) * ENNReal.ofReal p.1) =
          ∫⁻ p in S, B p := by
    refine lintegral_congr_ae ?_
    filter_upwards [hit] with p hp
    rw [hp.2]
  rw [eA] at hP ⊢
  rw [eB] at hN ⊢
  have hAl := ae_lt_top' hAm hP
  have hBl := ae_lt_top' hBm hN
  have hpt : ∀ᵐ p ∂(volume.restrict S),
      (c * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi), s p τ φ) * p.1 = (A p).toReal -
          (B p).toReal := by
    filter_upwards [hsec, hS, hAl, hBl] with p hp h1 hAp hBp
    have hcn : ENNReal.ofReal c ≠ 0 := by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hc0
    have h1n : ENNReal.ofReal p.1 ≠ 0 := by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact h1
    have hSpf : Sp p ≠ ⊤ := by
      intro h
      have : A p = ⊤ := by
        simp only [hA, h, ENNReal.mul_top hcn, ENNReal.top_mul h1n]
      exact absurd hAp (by rw [this]; exact lt_irrefl _)
    have hSnf : Sn p ≠ ⊤ := by
      intro h
      have : B p = ⊤ := by
        simp only [hB, h, ENNReal.mul_top hcn, ENNReal.top_mul h1n]
      exact absurd hBp (by rw [this]; exact lt_irrefl _)
    have hint : Integrable (fun y : ℝ × ℝ ↦ s p y.1 y.2) ν :=
        integrable_of_lintegral_pos_neg_ne_top hp hSpf hSnf
    have hval : ∫ y, s p y.1 y.2 ∂ν = (Sp p).toReal - (Sn p).toReal :=
        integral_eq_lintegral_sub_of_ne_top hp hSpf hSnf
    rw [integral_prod _ hint] at hval
    have hiv : (∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi), s p τ φ)
        = ∫ τ in Icc (0 : ℝ) 1, ∫ φ in Icc (0 : ℝ) (2 * Real.pi), s p τ φ := by
      simp only [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le h2pi,
        ← integral_Icc_eq_integral_Ioc]
    rw [hiv, hval]
    simp only [hA, hB, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0.le,
        ENNReal.toReal_ofReal h1.le]
    ring
  rw [integral_congr_ae hpt, integral_sub (integrable_toReal_of_lintegral_ne_top hAm hP)
    (integrable_toReal_of_lintegral_ne_top hBm hN), integral_toReal hAm hAl,
        integral_toReal hBm hBl]

/-- If `Iz p = a * Ix p + b * Iy p + K * Iu p` for almost every `p` of a set `s` in `ℝ × ℝ`, with
complex constants `a`, `b`, `K` and `Ix`, `Iy`, `Iu` integrable on `s`, then
`∫ p in s, Iz p = a * ∫ p in s, Ix p + b * ∫ p in s, Iy p + K * ∫ p in s, Iu p`. -/
theorem setIntegral_linear_combination_three_of_ae_eq {s : Set (ℝ × ℝ)} {Iz Ix Iy Iu : ℝ × ℝ → ℂ}
    {a b K : ℂ}
    (h : ∀ᵐ p ∂(volume.restrict s), Iz p = a * Ix p + b * Iy p + K * Iu p)
    (hx : IntegrableOn Ix s) (hy : IntegrableOn Iy s) (hu : IntegrableOn Iu s) :
    ∫ p in s, Iz p = a * (∫ p in s, Ix p) + b * (∫ p in s, Iy p) + K * (∫ p in s, Iu p) := by
  have h1 : Integrable (fun p ↦ a * Ix p + b * Iy p) (volume.restrict s) :=
      (hx.const_mul a).add (hy.const_mul b)
  rw [integral_congr_ae h, integral_add h1 (hu.const_mul K),
    integral_add (hx.const_mul a) (hy.const_mul b), integral_const_mul, integral_const_mul,
    integral_const_mul]

/-- For complex functions `A`, `B`, `c`, `d` on `ℝ × ℝ` and a complex constant `k`, if
`∫ p, c p * A p = -∫ p, d p * B p` then `∫ p, c p * (k * A p) = -∫ p, d p * (k * B p)`. The
constant `k` is taken out of both integrals. -/
theorem integral_mul_const_mul_eq_neg {A B c d : ℝ × ℝ → ℂ} (k : ℂ)
    (h : ∫ p, c p * A p = -∫ p, d p * B p) :
    ∫ p, c p * (k * A p) = -∫ p, d p * (k * B p) := by
  have e1 : (fun p ↦ c p * (k * A p)) = fun p ↦ k * (c p * A p) := funext fun p ↦ by ring
  have e2 : (fun p ↦ d p * (k * B p)) = fun p ↦ k * (d p * B p) := funext fun p ↦ by ring
  rw [e1, e2, integral_const_mul, integral_const_mul, h, mul_neg]

/-- Let `p j r = ∑ i ∈ range (j + 1), cf j i * r ^ i`, with `cf j j ≠ 0` for all `j`, and let `w`
be continuous with `∫ r in Icc s t, w r * p j r * p j' r` equal to one if `j = j'` and to zero
otherwise. Then `∫ r in Icc s t, w r * r ^ a * p j r = 0` for all `a < j`. By strong induction
on `a`: `r ^ a` is `p a r` minus lower monomials, divided by `cf a a`. -/
theorem setIntegral_Icc_pow_mul_orthonormal_eq_zero (s t : ℝ) (w : ℝ → ℝ) (hw : Continuous w)
    (cf : ℕ → ℕ → ℝ)
    (hlead : ∀ j, cf j j ≠ 0)
    (horth : ∀ j j', ∫ r in Set.Icc s t, w r * (∑ i ∈ Finset.range (j + 1), cf j i * r ^ i) *
      (∑ i ∈ Finset.range (j' + 1), cf j' i * r ^ i) = if j = j' then 1 else 0) (j : ℕ) :
    ∀ a, a < j → ∫ r in Set.Icc s t, w r * r ^ a * (∑ i ∈ Finset.range (j + 1), cf j i * r ^ i) =
        0 := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro haj
    have h0 := horth a j
    rw [ite_eq_right (ne_of_lt haj)] at h0
    have hexp : ∀ r, w r * (∑ i ∈ Finset.range (a + 1), cf a i * r ^ i) *
        (∑ i ∈ Finset.range (j + 1), cf j i * r ^ i) =
        (∑ i ∈ Finset.range a, cf a i * (w r * r ^ i * (∑ i ∈ Finset.range (j + 1),
            cf j i * r ^ i))) +
          cf a a * (w r * r ^ a * (∑ i ∈ Finset.range (j + 1), cf j i * r ^ i)) := by
      intro r
      rw [Finset.sum_range_succ, mul_add, add_mul]
      congr 1
      · rw [Finset.mul_sum (s := Finset.range a), Finset.sum_mul (s := Finset.range a)]
        apply Finset.sum_congr rfl
        intro i _
        ring
      · ring
    simp_rw [hexp] at h0
    have hc : ∀ f : ℝ → ℝ, Continuous f → IntegrableOn f (Set.Icc s t) :=
        fun f hf ↦ hf.integrableOn_Icc
    rw [integral_add (hc _ (by fun_prop)) (hc _ (by fun_prop)),
      integral_finsetSum _ (fun i _ ↦ hc _ (by fun_prop)), integral_const_mul] at h0
    have hz : ∑ i ∈ Finset.range a, ∫ r in Set.Icc s t,
        cf a i * (w r * r ^ i * (∑ i ∈ Finset.range (j + 1), cf j i * r ^ i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [integral_const_mul, ih i (Finset.mem_range.mp hi)
          (lt_trans (Finset.mem_range.mp hi) haj), mul_zero]
    rw [hz, zero_add] at h0
    exact (mul_eq_zero.mp h0).resolve_left (hlead a)

/-- Let `f : ℝ → ℂ` be a.e. strongly measurable on `(-π, π]` and `g : ℝ → ℝ` integrable there, with
`‖f θ‖ ^ 2 ≤ g θ` for every `θ`. Then
`‖∫ θ in Ioc (-π) π, f θ‖ ^ 2 ≤ 2 * π * ∫ θ in Ioc (-π) π, g θ`. With `m = ∫ ‖f‖`, the bound
`m * ‖f θ‖ ≤ m ^ 2 / (4 * π) + π * ‖f θ‖ ^ 2` is integrated over the interval. -/
theorem sq_norm_setIntegral_le_two_pi_setIntegral {f : ℝ → ℂ} {g : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hg : IntegrableOn g (Ioc (-Real.pi) Real.pi)) (hfg : ∀ θ, ‖f θ‖ ^ 2 ≤ g θ) :
    ‖∫ θ in Ioc (-Real.pi) Real.pi, f θ‖ ^ 2 ≤ 2 * Real.pi * ∫ θ in Ioc (-Real.pi) Real.pi, g θ :=
        by
  have hp := Real.pi_pos
  have hsq : IntegrableOn (fun θ ↦ ‖f θ‖ ^ 2) (Ioc (-Real.pi) Real.pi) :=
    hg.mono' (hf.norm.pow 2) (ae_of_all _ fun θ ↦ by
      rw [Real.norm_of_nonneg (by positivity)]; exact hfg θ)
  have h1 : ‖∫ θ in Ioc (-Real.pi) Real.pi, f θ‖ ≤ ∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖ :=
    norm_integral_le_integral_norm _
  have hs0 : 0 ≤ ∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖ := integral_nonneg fun _ ↦ norm_nonneg _
  have hc : IntegrableOn (fun θ : ℝ ↦ (∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖) ^ 2 / (4 * Real.pi))
      (Ioc (-Real.pi) Real.pi) := integrableOn_const (by simp)
  have h2 : (∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖) * (∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖) ≤
      ∫ θ in Ioc (-Real.pi) Real.pi,
        ((∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖) ^ 2 / (4 * Real.pi) + Real.pi * ‖f θ‖ ^ 2) := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (ae_of_all _ fun θ ↦ by positivity)
      (hc.add (hsq.const_mul Real.pi)) (ae_of_all _ fun θ ↦ ?_)
    have e : (∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖) ^ 2 / (4 * Real.pi) + Real.pi * ‖f θ‖ ^ 2
        - (∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖) * ‖f θ‖ =
        ((∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖) - 2 * Real.pi * ‖f θ‖) ^ 2 / (4 * Real.pi) := by
      field_simp
      ring
    have : 0 ≤ ((∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖) - 2 * Real.pi * ‖f θ‖) ^ 2 /
        (4 * Real.pi) := by
      positivity
    linarith
  rw [integral_add hc (hsq.const_mul Real.pi), setIntegral_const, integral_const_mul,
    measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul] at h2
  have h3 : ∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖ ^ 2 ≤ ∫ θ in Ioc (-Real.pi) Real.pi, g θ :=
    integral_mono hsq hg hfg
  have e2 : (Real.pi - -Real.pi) * ((∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖) ^ 2 / (4 * Real.pi)) =
      (∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖) ^ 2 / 2 := by
    field_simp
    ring
  rw [e2] at h2
  have h4 : ‖∫ θ in Ioc (-Real.pi) Real.pi, f θ‖ ^ 2 ≤ (∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith

/-- For a `1`-periodic `k : ℝ → ℝ` and every real `τ`, the integral over one period is invariant
under translation: `∫ σ in Icc 0 1, k (σ + τ) = ∫ σ in Icc 0 1, k σ`. No integrability of `k` is
assumed. The proof lifts `k` to `AddCircle 1` and uses the translation invariance of the measure on
the circle. -/
theorem integral_Icc_add_right_of_periodic (k : ℝ → ℝ) (hk : Function.Periodic k 1) (τ : ℝ) :
    ∫ σ in Icc (0 : ℝ) 1, k (σ + τ) = ∫ σ in Icc (0 : ℝ) 1, k σ := by
  have e : ∀ f : AddCircle (1 : ℝ) → ℝ, ∫ σ in Icc (0 : ℝ) 1, f σ = ∫ t, f t := by
    intro f
    have h := AddCircle.integral_preimage 1 0 f
    rw [zero_add] at h
    rw [← h, Measure.restrict_congr_set Ioc_ae_eq_Icc]
  have h1 : (fun σ ↦ k (σ + τ)) = fun σ : ℝ ↦ hk.lift
      ((σ : AddCircle (1 : ℝ)) + (τ : AddCircle (1 : ℝ))) := by
    funext σ
    rw [← AddCircle.coe_add, Function.Periodic.lift_coe]
  have h2 : k = fun σ : ℝ ↦ hk.lift (σ : AddCircle (1 : ℝ)) := by
    funext σ
    rw [Function.Periodic.lift_coe]
  rw [h1, e (fun t ↦ hk.lift (t + (τ : AddCircle (1 : ℝ)))), integral_add_right_eq_self]
  conv_rhs => rw [h2]
  rw [e hk.lift]

/-- Let `B`, `C : ℝ → ℂ` be locally integrable with `∫ z, deriv χ z • C z = -∫ z, χ z • B z` for
every smooth compactly supported `χ : ℝ → ℝ`, so that `B` is the weak derivative of `C`. Then for
`z₁ ≤ z₂` and every `C^1` function `s : ℝ → ℝ` with `s z₁ = 0` and `s z₂ = 0`,
`∫ z in Icc z₁ z₂, (s z • B z + deriv s z • C z) = 0`. The proof shows that `C` differs from the
primitive `fun z ↦ ∫ u in 0..z, B u` by a constant almost everywhere and then integrates by parts
on `Icc z₁ z₂`. -/
theorem setIntegral_smul_add_deriv_smul_eq_zero {B C : ℝ → ℂ} (hB : LocallyIntegrable B volume)
    (hC : LocallyIntegrable C volume)
    (hyp : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∫ z, deriv χ z • C z = -∫ z, χ z • B z)
    {z₁ z₂ : ℝ} (hz : z₁ ≤ z₂) (s : ℝ → ℝ) (hs : ContDiff ℝ 1 s) (hs1 : s z₁ = 0) (hs2 : s z₂ = 0) :
    ∫ z in Icc z₁ z₂, (s z • B z + deriv s z • C z) = 0 := by
  set P : ℝ → ℂ := fun z ↦ ∫ u in (0 : ℝ)..z, B u with hP
  have hPc : Continuous P := intervalIntegral.continuous_primitive
      (intervalIntegrable_of_locallyIntegrable hB) 0
  have hX : LocallyIntegrable (fun z ↦ C z - P z) volume := hC.sub hPc.locallyIntegrable
  have hE : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → ∫ z, deriv χ z • (C z - P z) = 0 :=
      by
    intro χ hχ hc
    have hdc : Continuous (deriv χ) := hχ.continuous_deriv (by exact_mod_cast le_top)
    have hdcs : HasCompactSupport (deriv χ) := hc.deriv
    simp_rw [smul_sub]
    rw [integral_sub (MeasureTheory.LocallyIntegrable.integrable_smul_left_of_hasCompactSupport hC
        hdc hdcs) (MeasureTheory.LocallyIntegrable.integrable_smul_left_of_hasCompactSupport
            hPc.locallyIntegrable hdc hdcs), hyp χ hχ hc,
      integral_deriv_smul_primitive_eq_neg hB hχ hc]
    ring
  let η : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  set e : ℝ → ℝ := η.normed volume with he_def
  have he : ContDiff ℝ ∞ e := η.contDiff_normed
  have hec : HasCompactSupport e := η.hasCompactSupport_normed
  have he1 : ∫ z, e z = 1 := η.integral_normed
  set c : ℂ := ∫ z, e z • (C z - P z) with hc_def
  have hloc : LocallyIntegrable (fun z ↦ C z - P z - c) volume :=
      hX.sub (locallyIntegrable_const c)
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
  · have hCe : ∀ᵐ z ∂(volume.restrict (Icc z₁ z₂)), s z • B z + deriv s z • C z =
        (s z • B z + deriv s z • (∫ u in z₁..z, B u)) + deriv s z •
            ((∫ u in (0 : ℝ)..z₁, B u) + c) := by
      refine ae_restrict_of_ae (hae.mono fun z hz ↦ ?_)
      have h1 : C z = P z + c := by linear_combination hz
      rw [h1, hP]
      simp only
      rw [← intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_of_locallyIntegrable hB 0 z₁)
              (intervalIntegrable_of_locallyIntegrable hB z₁ z)]
      simp only [smul_add]
      ring
    rw [integral_congr_ae hCe]
    have hBI : IntegrableOn B (Icc z₁ z₂) := hB.integrableOn_isCompact isCompact_Icc
    have hsc : Continuous s := hs.continuous
    have hdsc : Continuous (deriv s) := hs.continuous_deriv le_rfl
    have hPc1 : Continuous (fun z ↦ ∫ u in z₁..z, B u) :=
        intervalIntegral.continuous_primitive (intervalIntegrable_of_locallyIntegrable hB) _
    have iA : IntegrableOn (fun z ↦ s z • B z) (Icc z₁ z₂) := by
      simp_rw [Complex.real_smul]
      exact hBI.continuousOn_mul (Complex.continuous_ofReal.comp hsc).continuousOn isCompact_Icc
    have iB : IntegrableOn (fun z ↦ deriv s z • (∫ u in z₁..z, B u)) (Icc z₁ z₂) :=
      (hdsc.smul hPc1).continuousOn.integrableOn_compact isCompact_Icc
    have iC : IntegrableOn (fun z ↦ deriv s z • ((∫ u in (0 : ℝ)..z₁, B u) + c)) (Icc z₁ z₂) :=
      (hdsc.smul continuous_const).continuousOn.integrableOn_compact isCompact_Icc
    have iAB : IntegrableOn (fun z ↦ s z • B z + deriv s z • (∫ u in z₁..z, B u)) (Icc z₁ z₂) :=
        iA.add iB
    rw [integral_add iAB iC, integral_add iA iB, integral_smul_const]
    have hds : ∫ z in Icc z₁ z₂, deriv s z = 0 := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hz,
        intervalIntegral.integral_deriv_eq_sub' s rfl (fun x _ ↦
            (hs.differentiable one_ne_zero).differentiableAt)
          hdsc.continuousOn, hs1, hs2, sub_zero]
    have hpr := setIntegral_primitive_mul_deriv_eq_neg hBI hs hs2
    have e2 : ∫ z in Icc z₁ z₂, deriv s z • (∫ u in z₁..z, B u) =
        ∫ z in Icc z₁ z₂, (∫ u in z₁..z, B u) * ((deriv s z : ℝ) : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Icc (fun z _ ↦ ?_)
      rw [Complex.real_smul, mul_comm]
    have e1 : ∫ z in Icc z₁ z₂, s z • B z = ∫ z in Icc z₁ z₂, B z * ((s z : ℝ) : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Icc (fun z _ ↦ ?_)
      rw [Complex.real_smul, mul_comm]
    rw [hds, zero_smul, add_zero, e2, hpr, e1]
    ring
  intro g hg hgc
  set mg : ℝ := ∫ z, g z with hmg
  set q : ℝ → ℝ := fun z ↦ g z - mg * e z with hq_def
  have hq : ContDiff ℝ ∞ q := hg.sub (contDiff_const.mul he)
  have hqc : HasCompactSupport q := hgc.sub (hec.mul_left)
  obtain ⟨R, hR0, hR⟩ := exists_pos_tsupport_subset_Ioo_neg hqc
  have hq0 : ∀ z, z ∉ Ioo (-R) R → q z = 0 := fun z hz ↦
    image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hR h))
  set h : ℝ → ℝ := fun z ↦ ∫ u in (-R)..z, q u with hh_def
  have hder : ∀ z, HasDerivAt h (q z) z := fun z ↦
    (hq.continuous.integral_hasStrictDerivAt (-R) z).hasDerivAt
  have hderiv : deriv h = q := funext fun z ↦ (hder z).deriv
  have hhs : ContDiff ℝ ∞ h :=
    contDiff_infty_iff_deriv.2 ⟨fun z ↦ (hder z).differentiableAt, by rw [hderiv]; exact hq⟩
  have hgI : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have heI : Integrable e := he.continuous.integrable_of_hasCompactSupport hec
  have hqint : ∫ z, q z = 0 := by
    rw [integral_sub hgI (heI.const_mul mg), integral_const_mul, he1]
    ring
  have hhc : HasCompactSupport h := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) (fun z hz ↦ ?_)
    simp only [mem_Icc, not_and_or, not_le] at hz
    rcases hz with hz | hz
    · change ∫ u in (-R)..z, q u = 0
      rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hz.le, neg_eq_zero]
      rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ ↦ (0 : ℝ))
        (fun u hu ↦ hq0 u (fun h' ↦ by linarith [hu.2, h'.1]))]
      simp
    · change ∫ u in (-R)..z, q u = 0
      rw [intervalIntegral.integral_of_le (by linarith),
        setIntegral_eq_integral_of_forall_compl_eq_zero
            (fun u hu ↦ hq0 u (fun h' ↦ hu (show u ∈ Ioc (-R) z from ⟨h'.1, by
              linarith [h'.2]⟩))),
        hqint]
  have key := hE h hhs hhc
  rw [hderiv] at key
  have iG : Integrable (fun z ↦ g z • (C z - P z)) :=
    MeasureTheory.LocallyIntegrable.integrable_smul_left_of_hasCompactSupport hX hg.continuous hgc
  have iE : Integrable (fun z ↦ e z • (C z - P z)) :=
    MeasureTheory.LocallyIntegrable.integrable_smul_left_of_hasCompactSupport hX he.continuous hec
  have k2 : ∫ z, q z • (C z - P z) = (∫ z, g z • (C z - P z)) - mg • c := by
    simp_rw [hq_def, sub_smul, mul_smul]
    have iE' : Integrable (fun z ↦ mg • (e z • (C z - P z))) := iE.smul mg
    rw [integral_sub iG iE', integral_smul]
  rw [k2, sub_eq_zero] at key
  have iGc : Integrable (fun z ↦ g z • c) := hgI.smul_const c
  rw [show (fun z ↦ g z • (C z - P z - c)) = fun z ↦ g z • (C z - P z) - g z • c from
    funext fun z ↦ smul_sub _ _ _, integral_sub iG iGc, key, integral_smul_const, sub_self]

end PDE.Analysis
