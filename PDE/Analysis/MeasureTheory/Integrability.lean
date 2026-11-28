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
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Data.List.GetD
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import Mathlib.Topology.Separation.CompletelyRegular
public import PDE.Analysis.Calculus.Deriv
public import PDE.Analysis.Complex.Numbers
public import PDE.Analysis.MeasureTheory.AlmostEverywhere
public import PDE.Analysis.MeasureTheory.Measurability
public import PDE.Analysis.MeasureTheory.Product
public import PDE.Analysis.Scalar.Powers
public import PDE.Analysis.Scalar.Powers.Basic
public import PDE.Analysis.Topology.Compactness
public import PDE.Analysis.Topology.Continuity
public import PDE.Analysis.Topology.Limits

set_option linter.style.header false

/-!
# Integrability of functions

The lemmas state `Integrable` and `IntegrableOn` for products of an integrable function with a
bounded one, for functions dominated by an integrable function, and for continuous functions on
compact sets. The proofs use `Integrable.mono'`, `Integrable.bdd_mul` and
`ContinuousOn.integrableOn_compact`.

## Main results

* `PDE.Analysis.integrableOn_add_mul_continuous_of_isCompact`: Let `s` be a compact set in `ℝ × ℝ`,
  let `F dF : ℝ × ℝ → ℂ` be integrable on `s`, and let `wt t : ℝ → ℝ` be continuous. Then for all
  real `c` and `o`, the function `p ↦ (((1 / (c - o) : ℝ) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) :
  ℂ) * dF p) * ((wt p.1 * t p.1 : ℝ) : ℂ)` is integrable on `s`.
* `PDE.Analysis.integrableOn_prod_of_integrableOn_fst_mul`: Let `0 < δ` and `F : ℝ × ℝ → ℂ`. If
  `fun p ↦ (p.1 : ℂ) * F p` is integrable on `Icc 0 R ×ˢ Icc (-Z) Z` and `F` is almost everywhere
  strongly measurable on `Ioi 0 ×ˢ univ`, then `F` is integrable on `Icc δ R ×ˢ Icc (-Z) Z`.
* `PDE.Analysis.integrable_mul_mul_of_integrableOn_prod`: Let `s1`, `s2 ⊆ ℝ` be measurable and
  `H : ℝ × ℝ → ℂ` integrable on `s1 ×ˢ s2`. If `u`, `v : ℝ → ℝ` are measurable with `|u x| ≤ Cu` and
  `|v x| ≤ Cv` for all `x`, `u` vanishes outside `s1` and `v` vanishes outside `s2`, then
  `fun p ↦ ((u p.1 * v p.2 : ℝ) : ℂ) * H p` is integrable on `ℝ × ℝ`.
* `PDE.Analysis.integrableOn_Icc_prod_Icc_of_continuous`: A continuous function `f : ℝ × ℝ → ℂ` is
  integrable on every closed rectangle `Icc a b ×ˢ Icc c d`.
* `PDE.Analysis.integrableOn_add_mul_fst_mul_of_isCompact`: Let `s` be a compact measurable set in
  `ℝ × ℝ`, let `F` and `p ↦ (p.1 : ℂ) * dF p` be integrable on `s`, where `F dF : ℝ × ℝ → ℂ`, and
  let `t : ℝ → ℝ` be continuous. Then for all real `c` and `o`, the function `p ↦ (((1 / (c - o) :
  ℝ) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p) * ((p.1 * t p.1 : ℝ) : ℂ)` is integrable
  on `s`.
* `PDE.Analysis.integrable_norm_mul_norm_Lp_two`: For `F` in `Lp E 2 μ` and `G` in `Lp E' 2 μ`, with
  `E` and `E'` normed groups, the product of the pointwise norms `t ↦ ‖F t‖ * ‖G t‖` is integrable.
* `PDE.Analysis.integrable_ofReal_mul_sum_mul_conj`: Let `w : ℝ × ℝ → ℝ` be integrable and almost
  everywhere nonnegative for a measure `μ`, and for every `j` in a finite set `Js` let the complex
  functions `p ↦ f p j` and `p ↦ φ i p j`, for all `i` in a finite type, be almost everywhere
  strongly measurable, with `p ↦ w p * ‖f p j‖ ^ 2` integrable. If at almost every `p` the bound
  `‖φ i p j‖ ≤ C` holds for all `i` and all `j ∈ Js`, then
  `p ↦ (w p : ℂ) * ∑ j ∈ Js, f p j * (starRingEnd ℂ) (φ i p j)` is integrable for every `i`.
* `PDE.Analysis.integrable_weight_mul_conj`: Let `w : X → ℝ` be almost everywhere strongly
  measurable and almost everywhere nonnegative for a measure `μ`, and let `a b : X → ℂ` be almost
  everywhere strongly measurable. If `x ↦ w x * ‖a x‖ ^ 2` and `x ↦ w x * ‖b x‖ ^ 2` are integrable,
  then `x ↦ (w x : ℂ) * (a x * (starRingEnd ℂ) (b x))` is integrable.

There are 54 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Real ComplexConjugate

namespace PDE.Analysis

/-- A continuous function `f : ℝ × ℝ → ℂ` is integrable on every closed rectangle
`Icc a b ×ˢ Icc c d`. -/
theorem integrableOn_Icc_prod_Icc_of_continuous {f : ℝ × ℝ → ℂ} (hf : Continuous f) (a b c d : ℝ) :
    IntegrableOn f (Icc a b ×ˢ Icc c d) :=
  hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

/-- If `f : ℝ × ℝ → ℂ` satisfies `MemLp f 2` for Lebesgue measure restricted to the rectangle
`Icc ρ R ×ˢ Icc (-R) R`, then `f` is integrable on this rectangle. The rectangle has finite measure,
so `L²` is contained in `L¹` there. -/
theorem integrableOn_Icc_prod_Icc_of_memLp_two {f : ℝ × ℝ → ℂ} {ρ R : ℝ}
    (h : MemLp f 2 (volume.restrict (Icc ρ R ×ˢ Icc (-R) R))) :
    IntegrableOn f (Icc ρ R ×ˢ Icc (-R) R) := by
  have := isFiniteMeasure_restrict_Icc_prod_Icc ρ R
  exact h.integrable (by norm_num)

/-- For real `C`, `M`, `N` and `c ≥ 0`, the function `r ↦ C * (r ^ (-(3 / 4 : ℝ)) + 1) * M * N` is
integrable on `Set.Ioc 0 c` for Lebesgue measure. -/
theorem integrableOn_Ioc_mul_rpow_add_one_mul (C M N : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    IntegrableOn (fun r : ℝ ↦ C * (r ^ (-(3 / 4 : ℝ)) + 1) * M * N) (Ioc 0 c) := by
  have h := (((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := c) (by
    norm_num : (-1 : ℝ) < -(3 / 4))).add
    (intervalIntegrable_const (c := (1 : ℝ)))).const_mul C).mul_const M |>.mul_const N
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hc).1 h

/-- For every real `K` and every `c ≥ 0`, the function `r ↦ K * r ^ (-(3 / 4 : ℝ))` is integrable on
`Set.Ioc 0 c` for Lebesgue measure. -/
theorem integrableOn_Ioc_mul_rpow_neg_three_quarters (K : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    IntegrableOn (fun r : ℝ ↦ K * r ^ (-(3 / 4 : ℝ))) (Ioc 0 c) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hc).1
    ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul K)

/-- For `0 ≤ b`, the function `fun τ : ℝ ↦ τ ^ (-(1 / 2 : ℝ))` is integrable on `Ioc 0 b`. -/
theorem integrableOn_Ioc_rpow_neg_half (b : ℝ) (hb : 0 ≤ b) :
    IntegrableOn (fun τ : ℝ ↦ τ ^ (-(1 / 2 : ℝ))) (Ioc 0 b) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num))

/-- For `0 < a` and `0 < b`, the function `r ↦ (a + b * r ^ 2)⁻¹` is integrable on `Ioi 0`. -/
theorem integrableOn_Ioi_inv_add_mul_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun r : ℝ ↦ (a + b * r ^ 2)⁻¹) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun r _ ↦ hasDerivAt_arctan_sqrt_mul_div ha hb r)
    (fun r _ ↦ by positivity) (tendsto_arctan_sqrt_mul_div_atTop ha hb)

/-- For a natural number `n` with `2 ≤ n` and a real `τ` with `0 < τ`, the function
`fun ρ : ℝ ↦ (ρ ^ n)⁻¹` is integrable on `Ioi τ`. -/
theorem integrableOn_Ioi_inv_pow_of_two_le (n : ℕ) (hn : 2 ≤ n) {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun ρ : ℝ ↦ (ρ ^ n)⁻¹) (Ioi τ) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h := integrableOn_Ioi_rpow_of_lt (a := -(n : ℝ)) (by linarith) hτ
  refine h.congr_fun (fun ρ hρ ↦ ?_) measurableSet_Ioi
  change ρ ^ (-(n : ℝ)) = (ρ ^ n)⁻¹
  rw [Real.rpow_neg (le_of_lt (hτ.trans hρ)), Real.rpow_natCast]

/-- The function `τ ↦ τ ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / 4) * τ) + Real.exp (-(1 / 4) * τ)` is
integrable on `Ioi 0`. -/
theorem integrableOn_Ioi_rpow_mul_exp_add_exp :
    IntegrableOn (fun τ : ℝ ↦ τ ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / 4) * τ) +
        Real.exp (-(1 / 4) * τ))
      (Ioi 0) := by
  have h1 : IntegrableOn (fun τ : ℝ ↦ τ ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / 4) * τ ^ (1 : ℝ)))
      (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) one_pos (by norm_num)
  simp only [Real.rpow_one] at h1
  exact h1.add (exp_neg_integrableOn_Ioi 0 (by norm_num))

/-- A continuous function `f : ℝ → ℂ` is integrable with respect to Lebesgue measure restricted to
the open interval `Ioo (-π) π`. -/
theorem integrableOn_Ioo_neg_pi_pi_of_continuous {f : ℝ → ℂ} (hf : Continuous f) :
    Integrable f (volume.restrict (Ioo (-Real.pi) Real.pi)) :=
  (hf.integrableOn_Icc (a := -Real.pi) (b := Real.pi)).mono_set Ioo_subset_Icc_self

/-- If `F : ℝ → ℂ` is integrable on `Ioo (-a) a`, then so is `fun x ↦ F (-x)`. The proof uses that
negation preserves Lebesgue measure and maps `Ioo (-a) a` onto itself. -/
theorem integrableOn_Ioo_symm_comp_neg {a : ℝ} {F : ℝ → ℂ} (hF : IntegrableOn F (Set.Ioo (-a) a)) :
    IntegrableOn (fun x ↦ F (-x)) (Set.Ioo (-a) a) := by
  have hpre : (fun x : ℝ ↦ -x) ⁻¹' Set.Ioo (-a) a = Set.Ioo (-a) a := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have h := ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding (f := F) (s := Set.Ioo (-a) a)).2 hF
  rw [hpre] at h
  exact h

/-- Let `s` be a compact set in `ℝ × ℝ`, let `F dF : ℝ × ℝ → ℂ` be integrable on `s`, and let
`wt t : ℝ → ℝ` be continuous. Then for all real `c` and `o`, the function
`p ↦ (((1 / (c - o) : ℝ) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p) * ((wt p.1 * t p.1 :
ℝ) : ℂ)` is integrable on `s`. -/
theorem integrableOn_add_mul_continuous_of_isCompact {s : Set (ℝ × ℝ)} (hs : IsCompact s)
    {F dF : ℝ × ℝ → ℂ} (hF : IntegrableOn F s)
    (hdF : IntegrableOn dF s) (c o : ℝ) {wt t : ℝ → ℝ} (hwt : Continuous wt) (ht : Continuous t) :
    IntegrableOn (fun p : ℝ × ℝ ↦ ((((1 / (c - o) : ℝ)) : ℂ) * F p +
        (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p)
      * ((wt p.1 * t p.1 : ℝ) : ℂ)) s := by
  have h1 : ContinuousOn (fun _ : ℝ × ℝ ↦ (((1 / (c - o) : ℝ)) : ℂ)) s := continuousOn_const
  have h2 : ContinuousOn (fun p : ℝ × ℝ ↦ (((p.2 - o) / (c - o) : ℝ) : ℂ)) s :=
    (Complex.continuous_ofReal.comp ((continuous_snd.sub continuous_const).div_const
        _)).continuousOn
  have h3 : ContinuousOn (fun p : ℝ × ℝ ↦ ((wt p.1 * t p.1 : ℝ) : ℂ)) s :=
    (Complex.continuous_ofReal.comp ((hwt.comp continuous_fst).mul
        (ht.comp continuous_fst))).continuousOn
  exact ((hF.continuousOn_mul h1 hs).add (hdF.continuousOn_mul h2 hs)).mul_continuousOn h3 hs

/-- Let `s` be a compact measurable set in `ℝ × ℝ`, let `F` and `p ↦ (p.1 : ℂ) * dF p` be integrable
on `s`, where `F dF : ℝ × ℝ → ℂ`, and let `t : ℝ → ℝ` be continuous. Then for all real `c` and `o`,
the function `p ↦ (((1 / (c - o) : ℝ) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p) * ((p.1 *
t p.1 : ℝ) : ℂ)` is integrable on `s`. The proof moves the factor `p.1` onto `dF` and multiplies
each integrable term by a continuous function. -/
theorem integrableOn_add_mul_fst_mul_of_isCompact {s : Set (ℝ × ℝ)} (hs : IsCompact s)
    {F dF : ℝ × ℝ → ℂ}
    (hF : IntegrableOn F s) (hdF : IntegrableOn (fun p : ℝ × ℝ ↦ (p.1 : ℂ) * dF p) s) (c o : ℝ)
        {t : ℝ → ℝ}
    (ht : Continuous t) (hm : MeasurableSet s) :
    IntegrableOn (fun p : ℝ × ℝ ↦ ((((1 / (c - o) : ℝ)) : ℂ) * F p +
        (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p)
      * ((p.1 * t p.1 : ℝ) : ℂ)) s := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ ↦ (((1 / (c - o) : ℝ)) : ℂ) * ((p.1 * t p.1 : ℝ) : ℂ)) s :=
    (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_fst.mul (ht.comp continuous_fst)))).continuousOn
  have h2 : ContinuousOn (fun p : ℝ × ℝ ↦ (((p.2 - o) / (c - o) : ℝ) : ℂ) * ((t p.1 : ℝ) : ℂ)) s :=
    ((Complex.continuous_ofReal.comp ((continuous_snd.sub continuous_const).div_const _)).mul
      (Complex.continuous_ofReal.comp (ht.comp continuous_fst))).continuousOn
  refine ((hF.continuousOn_mul h1 hs).add (hdF.continuousOn_mul h2 hs)).congr_fun (fun p _ ↦ ?_) hm
  simp only [Pi.add_apply]
  push_cast
  ring

/-- Let `0 < δ` and let `χ : ℝ → ℝ` be continuous with `|χ r| ≤ C` for all `r` and `χ r = 0`
whenever `|r| < δ`. If `fun p ↦ (p.1 : ℂ) * G p` is integrable on `Icc (-R) R ×ˢ S`, where
`G : ℝ × ℝ → ℂ` and `S` is a set of reals, then so is `fun p ↦ (χ p.1 : ℂ) * G p`. The proof writes
`χ p.1` as `χ p.1 / p.1` times `p.1` and uses the bound `|χ r / r| ≤ C / δ`. -/
theorem integrableOn_comp_fst_mul_of_fst_mul {G : ℝ × ℝ → ℂ} {χ : ℝ → ℝ} {R δ C : ℝ} {S : Set ℝ}
    (hδ : 0 < δ)
    (hG : IntegrableOn (fun p : ℝ × ℝ ↦ (p.1 : ℂ) * G p) (Icc (-R) R ×ˢ S))
    (hχ : Continuous χ) (hC : ∀ r, |χ r| ≤ C) (hχ0 : ∀ r, |r| < δ → χ r = 0) :
    IntegrableOn (fun p : ℝ × ℝ ↦ (χ p.1 : ℂ) * G p) (Icc (-R) R ×ˢ S) := by
  have hm : Measurable (fun r : ℝ ↦ χ r / r) := hχ.measurable.div measurable_id
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have h1 := hG.bdd_mul (c := C / δ) ((Complex.measurable_ofReal.comp
      (hm.comp measurable_fst)).aestronglyMeasurable)
    (Eventually.of_forall fun p ↦ ?_)
  · refine h1.congr (Eventually.of_forall fun p ↦ ?_)
    by_cases hp : p.1 = 0
    · simp [hp, hχ0 0 (by simp [hδ])]
    · simp only [Function.comp_apply]
      have : (p.1 : ℂ) ≠ 0 := by exact_mod_cast hp
      push_cast
      field_simp
  · simp only [Function.comp_apply]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div]
    by_cases hp : |p.1| < δ
    · rw [hχ0 _ hp, abs_zero, zero_div]
      positivity
    · replace hp := not_lt.1 hp
      have hpos : 0 < |p.1| := hδ.trans_le hp
      rw [div_le_div_iff₀ hpos hδ]
      calc |χ p.1| * δ ≤ C * δ := mul_le_mul_of_nonneg_right (hC _) hδ.le
        _ ≤ C * |p.1| := mul_le_mul_of_nonneg_left hp hC0

/-- Let `E` be a real normed space and `φ : ℝ → E → ℂ` such that `fun q ↦ φ q.1 q.2` is continuous
on `ℝ × E` and `‖φ θ e‖ ≤ ‖e‖` for all `θ`, `e`. If `f : ℝ → E` is integrable on a set `s`, then
`fun θ ↦ φ θ (f θ)` is integrable on `s`. -/
theorem integrableOn_comp_of_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℝ → E → ℂ} (hφc : Continuous (fun q : ℝ × E ↦ φ q.1 q.2)) (hφb : ∀ θ e, ‖φ θ e‖ ≤ ‖e‖)
    {f : ℝ → E} {s : Set ℝ} (hf : IntegrableOn f s) : IntegrableOn (fun θ ↦ φ θ (f θ)) s :=
  Integrable.mono' hf.norm (hφc.comp_aestronglyMeasurable
      (aestronglyMeasurable_id.prodMk hf.aestronglyMeasurable))
    (ae_of_all _ fun θ ↦ hφb θ (f θ))

/-- For every real `c`, the constant function `fun _ : ℝ ↦ c` is integrable on the open interval
`Ioo (-π) π`. -/
theorem integrableOn_const_Ioo_neg_pi_pi (c : ℝ) : IntegrableOn (fun _ : ℝ ↦ c) (Ioo (-π) π) :=
    integrableOn_const (by simp)

/-- Suppose `fun p ↦ (p.1 : ℂ) * K p` is integrable on `Icc 0 R ×ˢ Icc (-Z) Z` for all real `R` and
`Z`, and `f p = c * K p` for all `p : ℝ × ℝ`. Then for `0 < a`, `f` is integrable on
`Icc a R ×ˢ Icc (-Z) Z`. The proof multiplies by `c * (p.1 : ℂ)⁻¹`, which is continuous on this
compact rectangle because `a ≤ p.1` there. -/
theorem integrableOn_const_mul_of_fst_mul {f K : ℝ × ℝ → ℂ} (c : ℂ)
    (hK : ∀ R Z : ℝ, IntegrableOn (fun p : ℝ × ℝ ↦ (p.1 : ℂ) * K p) (Icc 0 R ×ˢ Icc (-Z) Z))
    (heq : ∀ p : ℝ × ℝ, f p = c * K p) {a R Z : ℝ} (ha : 0 < a) :
    IntegrableOn f (Icc a R ×ˢ Icc (-Z) Z) := by
  have hsub : Icc a R ×ˢ Icc (-Z) Z ⊆ Icc 0 R ×ˢ Icc (-Z) Z :=
    prod_mono (Icc_subset_Icc ha.le le_rfl) subset_rfl
  have hcont : ContinuousOn (fun p : ℝ × ℝ ↦ c * ((p.1 : ℂ))⁻¹) (Icc a R ×ˢ Icc (-Z) Z) := by
    refine continuousOn_const.mul
      (ContinuousOn.inv₀ (Complex.continuous_ofReal.comp continuous_fst).continuousOn fun p hp ↦
          ?_)
    exact_mod_cast (ha.trans_le hp.1.1).ne'
  have h := IntegrableOn.continuousOn_mul hcont ((hK R Z).mono_set hsub)
      (isCompact_Icc.prod isCompact_Icc)
  refine h.congr_fun (fun p hp ↦ ?_) (measurableSet_Icc.prod measurableSet_Icc)
  have hp0 : (p.1 : ℂ) ≠ 0 := by exact_mod_cast (ha.trans_le hp.1.1).ne'
  rw [heq p]
  field_simp

/-- Let `wt`, `t : ℝ → ℝ` be continuous and `0 < h`. If `g : ℝ × ℝ → ℂ` is integrable on
`Icc lo hi ×ˢ Icc 0 h`, then `fun p ↦ ((wt p.1 * t p.1 : ℝ) : ℂ) * g p` is integrable on
`Icc lo hi ×ˢ Icc (min 0 h) (max 0 h)`. -/
theorem integrableOn_continuous_fst_mul_Icc_min_max {g : ℝ × ℝ → ℂ} {wt t : ℝ → ℝ} {lo hi h : ℝ}
    (hwt : Continuous wt) (ht : Continuous t) (hh : 0 < h)
        (hg : IntegrableOn g (Icc lo hi ×ˢ Icc 0 h)) :
    IntegrableOn (fun p ↦ ((wt p.1 * t p.1 : ℝ) : ℂ) * g p)
        (Icc lo hi ×ˢ Icc (min 0 h) (max 0 h)) := by
  rw [min_eq_left hh.le, max_eq_right hh.le]
  exact hg.continuousOn_mul (continuousOn_ofReal_mul_comp_fst hwt ht _)
      (isCompact_Icc.prod isCompact_Icc)

/-- If `f : ℝ × ℝ → ℂ` is integrable on the rectangle `Icc ρ R ×ˢ Icc (-R) R`, then so is
`fun p ↦ (p.1 : ℂ) * f p`. -/
theorem integrableOn_fst_mul_Icc_prod_Icc {f : ℝ × ℝ → ℂ} {ρ R : ℝ}
    (h : IntegrableOn f (Icc ρ R ×ˢ Icc (-R) R)) :
    IntegrableOn (fun p : ℝ × ℝ ↦ (p.1 : ℂ) * f p) (Icc ρ R ×ˢ Icc (-R) R) := by
  refine h.bdd_mul (c := |ρ| + |R|) (Complex.continuous_ofReal.comp
      continuous_fst).aestronglyMeasurable ?_
  refine (ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)).2
      (Eventually.of_forall fun p hp ↦ ?_)
  rw [Complex.norm_real, Real.norm_eq_abs]
  rcases le_total 0 p.1 with h0 | h0
  · rw [abs_of_nonneg h0]; linarith [hp.1.2, le_abs_self R, abs_nonneg ρ]
  · rw [abs_of_nonpos h0]; linarith [hp.1.1, neg_abs_le ρ, abs_nonneg R]

/-- If `F : ℝ × ℝ → ℂ` is integrable on a compact set `s`, then `fun p ↦ (p.1 : ℂ) * F p` is
integrable on `s`. -/
theorem integrableOn_fst_mul_of_isCompact {F : ℝ × ℝ → ℂ} {s : Set (ℝ × ℝ)} (hs : IsCompact s)
    (h : IntegrableOn F s) :
    IntegrableOn (fun p : ℝ × ℝ ↦ (p.1 : ℂ) * F p) s :=
  IntegrableOn.continuousOn_mul (Complex.continuous_ofReal.comp continuous_fst).continuousOn h hs

/-- The function `fun τ : ℝ ↦ (1 + τ)⁻¹ * τ ^ (-(1 / 2 : ℝ))` is integrable on `Ioi 0`. The proof
bounds it by `τ ^ (-(1 / 2 : ℝ))` on `Ioc 0 1` and by `τ ^ (-(3 / 2 : ℝ))` on `Ioi 1`. -/
theorem integrableOn_inv_one_add_mul_rpow :
    IntegrableOn (fun τ : ℝ ↦ (1 + τ)⁻¹ * τ ^ (-(1 / 2 : ℝ))) (Ioi 0) := by
  have hmeas : Measurable (fun τ : ℝ ↦ (1 + τ)⁻¹ * τ ^ (-(1 / 2 : ℝ))) :=
    (measurable_const.add measurable_id).inv.mul (measurable_id.pow_const _)
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun τ : ℝ ↦ τ ^ (-(1 / 2 : ℝ))) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
    refine h1.mono' hmeas.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun τ hτ ↦ ?_))
    have hτ0 : 0 < τ := hτ.1
    have hr : 0 ≤ τ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hτ0.le _
    have hinv : (1 + τ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have hinv0 : 0 ≤ (1 + τ)⁻¹ := inv_nonneg.2 (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hinv0 hr)]
    calc (1 + τ)⁻¹ * τ ^ (-(1 / 2 : ℝ)) ≤ 1 * τ ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hinv hr
      _ = τ ^ (-(1 / 2 : ℝ)) := one_mul _
  · have h2 : IntegrableOn (fun τ : ℝ ↦ τ ^ (-(3 / 2 : ℝ))) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
    refine h2.mono' hmeas.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun τ hτ ↦ ?_))
    have hτ0 : 0 < τ := lt_trans zero_lt_one hτ
    have hr : 0 ≤ τ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hτ0.le _
    have hinv0 : 0 ≤ (1 + τ)⁻¹ := inv_nonneg.2 (by linarith)
    have hinv : (1 + τ)⁻¹ ≤ τ ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg_one]
      exact inv_anti₀ hτ0 (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hinv0 hr)]
    calc (1 + τ)⁻¹ * τ ^ (-(1 / 2 : ℝ)) ≤ τ ^ (-(1 : ℝ)) * τ ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hinv hr
      _ = τ ^ (-(3 / 2 : ℝ)) := by
          rw [← Real.rpow_add hτ0]
          norm_num

/-- Let `H : ℝ × ℝ → ℂ` be integrable on the rectangle `Icc lo hi ×ˢ Icc (-Z) Z`, let `u : ℝ → ℝ` be
continuous, and let `v : ℝ → ℝ` be measurable with `|v x| ≤ Cv` for all `x`. Then
`p ↦ (u p.1 : ℂ) * (v p.2 : ℂ) * H p` is integrable on the same rectangle. The proof bounds `u` on
the compact interval `Icc lo hi` and multiplies the integrable `H` by a bounded measurable factor.
-/
theorem integrableOn_mul_mul_of_continuous_of_bounded {H : ℝ × ℝ → ℂ} {lo hi Z : ℝ}
    (hH : IntegrableOn H (Icc lo hi ×ˢ Icc (-Z) Z)) {u v : ℝ → ℝ} (hu : Continuous u)
    (hv : Measurable v) {Cv : ℝ} (hbv : ∀ x, |v x| ≤ Cv) :
    IntegrableOn (fun p ↦ (u p.1 : ℂ) * (v p.2 : ℂ) * H p) (Icc lo hi ×ˢ Icc (-Z) Z) := by
  obtain ⟨Cu, hCu⟩ := (isCompact_Icc (a := lo) (b := hi)).exists_bound_of_continuousOn
      hu.continuousOn
  refine Integrable.bdd_mul (c := Cu * Cv) hH ?_ ?_
  · exact ((Complex.measurable_ofReal.comp (hu.measurable.comp measurable_fst)).mul
      (Complex.measurable_ofReal.comp (hv.comp measurable_snd))).aestronglyMeasurable
  · refine (ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)).2
        (Eventually.of_forall fun p hp ↦ ?_)
    have h1 := hCu p.1 hp.1
    rw [Real.norm_eq_abs] at h1
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul h1 (hbv _) (abs_nonneg _) ((abs_nonneg _).trans h1)

/-- If `F : ℝ × ℝ → ℂ` is integrable on a compact set `s ⊆ ℝ × ℝ` and `W : ℝ × ℝ → ℝ` is continuous,
then `fun p ↦ F p * (W p : ℂ)` is integrable on `s`. -/
theorem integrableOn_mul_ofReal_of_continuous {s : Set (ℝ × ℝ)} (hs : IsCompact s) {F : ℝ × ℝ → ℂ}
    {W : ℝ × ℝ → ℝ} (hW : Continuous W)
    (hF : IntegrableOn F s) : IntegrableOn (fun p ↦ F p * ((W p : ℝ) : ℂ)) s :=
  hF.mul_continuousOn (Complex.continuous_ofReal.comp hW).continuousOn hs

/-- Let `0 < h`, let `t₀ : ℝ → ℝ` be continuous and suppose `wt r * t r = r * t₀ r` for all real
`r`. If `fun p ↦ (p.1 : ℂ) * g p` is integrable on `Icc 0 hi ×ˢ Icc 0 h`, then
`fun p ↦ ((wt p.1 * t p.1 : ℝ) : ℂ) * g p` is integrable on `Icc 0 hi ×ˢ Icc (min 0 h) (max 0 h)`.
The proof rewrites this function as `(t₀ p.1 : ℂ) * ((p.1 : ℂ) * g p)`. -/
theorem integrableOn_mul_of_eq_fst_mul_continuous {g : ℝ × ℝ → ℂ} {wt t t₀ : ℝ → ℝ} {hi h : ℝ}
    (hh : 0 < h)
    (ht₀ : Continuous t₀) (he : ∀ r, wt r * t r = r * t₀ r)
    (hg : IntegrableOn (fun p ↦ (p.1 : ℂ) * g p) (Icc 0 hi ×ˢ Icc 0 h)) :
    IntegrableOn (fun p ↦ ((wt p.1 * t p.1 : ℝ) : ℂ) * g p)
        (Icc 0 hi ×ˢ Icc (min 0 h) (max 0 h)) := by
  rw [min_eq_left hh.le, max_eq_right hh.le]
  have e : (fun p : ℝ × ℝ ↦ ((wt p.1 * t p.1 : ℝ) : ℂ) * g p)
      = fun p ↦ ((t₀ p.1 : ℝ) : ℂ) * ((p.1 : ℂ) * g p) := by
    funext p
    rw [he p.1]
    push_cast
    ring
  rw [e]
  exact hg.continuousOn_mul (Complex.continuous_ofReal.comp (ht₀.comp continuous_fst)).continuousOn
    (isCompact_Icc.prod isCompact_Icc)

/-- Let `S` be a measurable set of `ℝ × ℝ` and `X : ℝ × ℝ → ℂ` integrable on `S`. If `f : ℝ × ℝ → ℂ`
is almost everywhere strongly measurable for Lebesgue measure restricted to `S` and `‖f p‖ ≤ M` for
all `p ∈ S`, then `fun p ↦ f p * X p` is integrable on `S`. -/
theorem integrableOn_mul_of_forall_mem_norm_le {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    {f X : ℝ × ℝ → ℂ} {M : ℝ} (hX : IntegrableOn X S)
    (hf : AEStronglyMeasurable f (volume.restrict S)) (hb : ∀ p ∈ S, ‖f p‖ ≤ M) :
    IntegrableOn (fun p ↦ f p * X p) S :=
  hX.bdd_mul hf ((ae_restrict_iff' hS).2 (Eventually.of_forall hb))

/-- If `f fz : ℝ → ℂ` are integrable on `Icc 0 h`, for a real `h`, then
`z ↦ fz z * ((1 - z / h : ℝ) : ℂ) - f z / (h : ℂ)` is integrable on `Icc 0 h`. -/
theorem integrableOn_mul_one_sub_div_sub_div (f fz : ℝ → ℂ) (h : ℝ)
    (hf : IntegrableOn f (Set.Icc 0 h)) (hfz : IntegrableOn fz (Set.Icc 0 h)) :
    IntegrableOn (fun z ↦ fz z * ((1 - z / h : ℝ) : ℂ) - f z / (h : ℂ)) (Set.Icc 0 h) := by
  refine (hfz.mul_continuousOn ?_ isCompact_Icc).sub (hf.div_const _)
  fun_prop

/-- Let `S ⊆ ℝ × ℝ` be measurable, `w : ℝ × ℝ → ℝ` measurable with `0 ≤ w p` on `S`, and
`fun p ↦ (w p : ℂ) * f p` integrable on `S`. If `c : ℝ × ℝ → ℝ` is almost everywhere strongly
measurable on `S` and `|c p| ≤ C * w p` for `p ∈ S`, then `fun p ↦ (c p : ℂ) * f p` is integrable
on `S`. The proof writes `c * f` as the bounded factor `c / w` times `w * f`. -/
theorem integrableOn_ofReal_mul_of_abs_le_mul {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    {f : ℝ × ℝ → ℂ} {w c : ℝ × ℝ → ℝ}
    (hw : Measurable w) (hw0 : ∀ p ∈ S, 0 ≤ w p) (hW : IntegrableOn (fun p ↦ (w p : ℂ) * f p) S)
    (hc : AEStronglyMeasurable c (volume.restrict S)) {C : ℝ} (hC : ∀ p ∈ S, |c p| ≤ C * w p) :
    IntegrableOn (fun p ↦ (c p : ℂ) * f p) S := by
  have hβ : AEStronglyMeasurable (fun p ↦ ((c p / w p : ℝ) : ℂ)) (volume.restrict S) :=
    (Complex.measurable_ofReal.comp_aemeasurable (hc.aemeasurable.div
        hw.aemeasurable)).aestronglyMeasurable
  have hb : ∀ p ∈ S, ‖((c p / w p : ℝ) : ℂ)‖ ≤ max C 0 := by
    intro p hp
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div]
    rcases (hw0 p hp).eq_or_lt with h | h
    · rw [← h]; simp
    · rw [abs_of_pos h, div_le_iff₀ h]
      exact (hC p hp).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) h.le)
  refine (Integrable.bdd_mul (c := max C 0) hW hβ ((ae_restrict_iff' hS).2
      (Eventually.of_forall hb))).congr ?_
  refine (ae_restrict_iff' hS).2 (Eventually.of_forall fun p hp ↦ ?_)
  rcases (hw0 p hp).eq_or_lt with h | h
  · have h0 : c p = 0 := by
      have := hC p hp
      rw [← h, mul_zero] at this
      exact abs_nonpos_iff.mp this
    simp [h0, ← h]
  · have : (w p : ℂ) ≠ 0 := by exact_mod_cast h.ne'
    push_cast
    field_simp

/-- Let `s` be a compact measurable set in `ℝ × ℝ`, let `A B : ℝ × ℝ → ℂ` be integrable on `s`, and
let `g₁ g₂ : ℝ × ℝ → ℂ` be continuous on `s`. If `g₁ p * A p + g₂ p * B p = f p` for all `p ∈ s`,
then `f` is integrable on `s`. -/
theorem integrableOn_of_eq_continuousOn_mul_add {s : Set (ℝ × ℝ)} (hs : IsCompact s)
    (hsm : MeasurableSet s) {A B f g₁ g₂ : ℝ × ℝ → ℂ}
    (h₁ : IntegrableOn A s) (h₂ : IntegrableOn B s) (c₁ : ContinuousOn g₁ s)
        (c₂ : ContinuousOn g₂ s)
    (he : ∀ p ∈ s, g₁ p * A p + g₂ p * B p = f p) : IntegrableOn f s :=
  ((h₁.continuousOn_mul c₁ hs).add (h₂.continuousOn_mul c₂ hs)).congr_fun he hsm

/-- Let `A`, `B ⊆ ℝ` be compact and `F : ℝ × ℝ → ℂ` integrable on `A ×ˢ B`. Then for every
continuous `k : ℝ × ℝ → ℝ`, the function `fun p ↦ (k p : ℂ) * F p` is integrable on `A ×ˢ B`. -/
theorem integrableOn_prod_ofReal_mul_of_continuous {F : ℝ × ℝ → ℂ} {A B : Set ℝ} (hA : IsCompact A)
    (hB : IsCompact B)
    (hF : IntegrableOn F (A ×ˢ B)) {k : ℝ × ℝ → ℝ} (hk : Continuous k) :
    IntegrableOn (fun p ↦ ((k p : ℝ) : ℂ) * F p) (A ×ˢ B) :=
  hF.continuousOn_mul (Complex.continuous_ofReal.comp hk).continuousOn (hA.prod hB)

/-- Let `0 < δ` and `F : ℝ × ℝ → ℂ`. If `fun p ↦ (p.1 : ℂ) * F p` is integrable on
`Icc 0 R ×ˢ Icc (-Z) Z` and `F` is almost everywhere strongly measurable on `Ioi 0 ×ˢ univ`, then
`F` is integrable on `Icc δ R ×ˢ Icc (-Z) Z`. The proof bounds `‖F p‖` by `δ⁻¹ * ‖(p.1 : ℂ) * F p‖`
on the smaller rectangle, where `δ ≤ p.1`. -/
theorem integrableOn_prod_of_integrableOn_fst_mul (δ R Z : ℝ) (hδ : 0 < δ) {F : ℝ × ℝ → ℂ}
    (hw : IntegrableOn (fun p : ℝ × ℝ ↦ (p.1 : ℂ) * F p) (Icc 0 R ×ˢ Icc (-Z) Z))
    (hm : AEStronglyMeasurable F (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)))) :
    IntegrableOn F (Icc δ R ×ˢ Icc (-Z) Z) := by
  have hsub : Icc δ R ×ˢ Icc (-Z) Z ⊆ Icc 0 R ×ˢ Icc (-Z) Z :=
    prod_mono (Icc_subset_Icc_left hδ.le) le_rfl
  have hsub' : Icc δ R ×ˢ Icc (-Z) Z ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) :=
    fun p hp ↦ ⟨hδ.trans_le hp.1.1, trivial⟩
  have hS : MeasurableSet (Icc δ R ×ˢ Icc (-Z) Z) := measurableSet_Icc.prod measurableSet_Icc
  refine Integrable.mono' (((hw.mono_set hsub).norm).const_mul δ⁻¹)
    (hm.mono_measure (Measure.restrict_mono hsub' le_rfl)) ?_
  filter_upwards [ae_restrict_mem hS] with p hp
  have h1 : δ ≤ p.1 := hp.1.1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hδ.trans_le h1)]
  have h2 : 1 ≤ δ⁻¹ * p.1 := by rw [inv_mul_eq_div, le_div_iff₀ hδ]; linarith
  nlinarith [norm_nonneg (F p)]

/-- Let `s` be a measurable set of `ℝ × ℝ` on which `0 ≤ p.1` and `0 ≤ p.2`, and let `φ : ℝ × ℝ → ℝ`
be measurable. If `|φ p| ≤ C` for all `p ∈ s` with `p.1 ≤ L`, and `φ p = 0` whenever `L ≤ p.1` or
`L ≤ p.2`, then `φ` is integrable on `s`. The proof restricts to `s ∩ Icc (0, 0) (L, L)`, a set of
finite measure on which `φ` is bounded, and uses that `φ` vanishes on the rest of `s`. -/
theorem integrableOn_quadrant_of_bounded_of_support {φ : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s)
    (hm : Measurable φ) {L C : ℝ} (h0 : ∀ p ∈ s, 0 ≤ p.1 ∧ 0 ≤ p.2)
    (hC : ∀ p ∈ s, p.1 ≤ L → |φ p| ≤ C) (hz : ∀ p : ℝ × ℝ, (L ≤ p.1 ∨ L ≤ p.2) → φ p = 0) :
    IntegrableOn φ s := by
  have hK : IntegrableOn φ (s ∩ Icc (0, 0) (L, L)) := by
    refine Measure.integrableOn_of_bounded (M := C) ?_ hm.aestronglyMeasurable ?_
    · exact ((measure_mono inter_subset_right).trans_lt isCompact_Icc.measure_lt_top).ne
    · filter_upwards [ae_restrict_mem (hs.inter measurableSet_Icc)] with p hp
      rw [Real.norm_eq_abs]
      exact hC p hp.1 hp.2.2.1
  refine hK.of_forall_sdiff_eq_zero hs (fun p hp ↦ hz p ?_)
  by_contra h
  push Not at h
  exact hp.2 ⟨hp.1, ⟨(h0 p hp.1).1, (h0 p hp.1).2⟩, h.1.le, h.2.le⟩

/-- If `F : ℝ × ℝ → ℂ` is integrable on a set `S` and `f : ℝ × ℝ → ℝ` satisfies `f p = c * (F p).re`
for all `p`, with `c` real, then `f` is integrable on `S`. -/
theorem integrableOn_scaled_re {S : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ} {F : ℝ × ℝ → ℂ}
    (hF : IntegrableOn F S) (c : ℝ)
    (h : ∀ p, f p = c * (F p).re) : IntegrableOn f S := by
  have e : f = fun p ↦ c * RCLike.re (F p) := funext fun p ↦ by rw [h p]; rfl
  rw [e]
  exact hF.re.const_mul c

/-- Let `S ⊆ ℝ × ℝ` and let `Y a b : ℝ × ℝ → ℂ` be integrable on `S` for all `a b : Fin 3`. Then for
all complex coefficients `C a b`, the function `fun p ↦ ∑ a, ∑ b, C a b * Y a b p` is integrable on
`S`. -/
theorem integrableOn_sum_sum_const_mul (S : Set (ℝ × ℝ)) (C : Fin 3 → Fin 3 → ℂ)
    (Y : Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (h : ∀ a b, IntegrableOn (Y a b) S) : IntegrableOn (fun p ↦ ∑ a, ∑ b, C a b * Y a b p) S :=
  integrable_finsetSum _ (fun a _ ↦ integrable_finsetSum _ (fun b _ ↦ (h a b).const_mul _))

/-- On the circle `AddCircle T` (`0 < T`) with its Haar probability measure, for `X` in `Lp ℂ 2` and
`Z : AddCircle T → ℂ` with `MemLp Z 2`, the function `t ↦ conj (X t) * Z t` is integrable. -/
theorem integrable_conj_mul_haarAddCircle {T : ℝ} [hT : Fact (0 < T)]
    (X : Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) (Z : AddCircle T → ℂ)
    (hZ : MemLp Z 2 AddCircle.haarAddCircle) :
    Integrable (fun t ↦ conj (X t) * Z t) AddCircle.haarAddCircle := by
  have h := L2.integrable_inner (𝕜 := ℂ) X (hZ.toLp Z)
  refine h.congr ?_
  filter_upwards [hZ.coeFn_toLp] with t ht
  rw [ht]
  simp [mul_comm]

/-- For a smooth bump function `φ : ContDiffBump (0 : ℝ × ℝ)`, a continuous `g : ℝ × ℝ → ℂ` and a
point `x`, the function `fun t ↦ φ.normed volume t • g (x - t)` is integrable. -/
theorem integrable_contDiffBump_normed_smul_comp_sub (φ : ContDiffBump (0 : ℝ × ℝ)) {g : ℝ × ℝ → ℂ}
    (hg : Continuous g) (x : ℝ × ℝ) :
    Integrable (fun t ↦ φ.normed volume t • g (x - t)) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (φ.contDiff_normed (n := 0)).continuous.smul (hg.comp
        (continuous_const.sub continuous_id))
  · exact φ.hasCompactSupport_normed.smul_right

/-- Let `s` and `t` be finite sets of pairs of integers and let `f i j : ℝ × ℝ → ℝ` be integrable
for a measure `μ` for all `i ∈ s` and `j ∈ t`. Then `p ↦ ∑ i ∈ s, ∑ j ∈ t, f i j p` is integrable
for `μ`. -/
theorem integrable_double_sum {μ : Measure (ℝ × ℝ)} (s t : Finset (ℤ × ℤ))
    (f : ℤ × ℤ → ℤ × ℤ → ℝ × ℝ → ℝ)
    (hf : ∀ i ∈ s, ∀ j ∈ t, Integrable (f i j) μ) :
    Integrable (fun p ↦ ∑ i ∈ s, ∑ j ∈ t, f i j p) μ :=
  integrable_finsetSum _ fun i hi ↦ integrable_finsetSum _ fun j hj ↦ hf i hi j hj

/-- For every real `C`, the function `τ ↦ Real.exp (-(1 / 4) * τ) * C` is integrable for Lebesgue
measure restricted to `Ioi 0`. -/
theorem integrable_exp_neg_mul_mul_const_Ioi (C : ℝ) :
    Integrable (fun τ : ℝ ↦ Real.exp (-(1 / 4) * τ) * C) (volume.restrict (Ioi (0 : ℝ))) :=
  (exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 4)).mul_const C

/-- For a `C^1` function `g : ℝ × ℝ → ℝ` with compact support,
`fun p ↦ (fderiv ℝ g p (1, 0) ^ 2 + fderiv ℝ g p (0, 1) ^ 2) * p.1` is integrable. -/
theorem integrable_fderiv_sq_add_sq_mul_fst {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hs : HasCompactSupport g) :
    Integrable (fun p : ℝ × ℝ ↦ (fderiv ℝ g p (1, 0) ^ 2 + fderiv ℝ g p (0, 1) ^ 2) * p.1) := by
  have c1 : Continuous fun p ↦ fderiv ℝ g p (1, 0) :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have c2 : Continuous fun p ↦ fderiv ℝ g p (0, 1) :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
  exact (hs.fderiv (𝕜 := ℝ)).mono' (fun p hp ↦ subset_tsupport _ fun h ↦ hp (by simp [h]))

/-- If `f : ℝ × ℝ → ℝ` is integrable for a measure `μ` and `c` is a decidable proposition, then
`p ↦ if c then f p else 0` is integrable for `μ`. -/
theorem integrable_ite_of_integrable {μ : Measure (ℝ × ℝ)} (c : Prop) [Decidable c] {f : ℝ × ℝ → ℝ}
    (hf : Integrable f μ) :
    Integrable (fun p ↦ if c then f p else 0) μ := by
  split_ifs
  · exact hf
  · exact integrable_zero _ _ _

/-- Let `s1`, `s2 ⊆ ℝ` be measurable and `H : ℝ × ℝ → ℂ` integrable on `s1 ×ˢ s2`. If `u`,
`v : ℝ → ℝ` are measurable with `|u x| ≤ Cu` and `|v x| ≤ Cv` for all `x`, `u` vanishes outside `s1`
and `v` vanishes outside `s2`, then `fun p ↦ ((u p.1 * v p.2 : ℝ) : ℂ) * H p` is integrable on
`ℝ × ℝ`. The proof replaces `H` by its indicator on `s1 ×ˢ s2` and multiplies an integrable function
by a bounded measurable one. -/
theorem integrable_mul_mul_of_integrableOn_prod {H : ℝ × ℝ → ℂ} {s1 s2 : Set ℝ}
    (h1 : MeasurableSet s1) (h2 : MeasurableSet s2)
    (hH : IntegrableOn H (s1 ×ˢ s2)) {u v : ℝ → ℝ} (hu : Measurable u) (hv : Measurable v)
        {Cu Cv : ℝ}
    (hbu : ∀ x, |u x| ≤ Cu) (hbv : ∀ x, |v x| ≤ Cv) (hzu : ∀ x, x ∉ s1 → u x = 0)
    (hzv : ∀ x, x ∉ s2 → v x = 0) :
    Integrable (fun p : ℝ × ℝ ↦ ((u p.1 * v p.2 : ℝ) : ℂ) * H p) := by
  have e : (fun p : ℝ × ℝ ↦ ((u p.1 * v p.2 : ℝ) : ℂ) * H p) =
      fun p ↦ ((u p.1 * v p.2 : ℝ) : ℂ) * (s1 ×ˢ s2).indicator H p := by
    funext p
    by_cases hp : p ∈ s1 ×ˢ s2
    · rw [Set.indicator_of_mem hp]
    · rcases not_and_or.1 (show ¬ (p.1 ∈ s1 ∧ p.2 ∈ s2) from hp) with h | h
      · simp [hzu _ h]
      · simp [hzv _ h]
  rw [e]
  have hCu : 0 ≤ Cu := (abs_nonneg _).trans (hbu 0)
  refine ((integrable_indicator_iff (h1.prod h2)).2 hH).bdd_mul (c := Cu * Cv)
    (Complex.measurable_ofReal.comp ((hu.comp measurable_fst).mul
        (hv.comp measurable_snd))).aestronglyMeasurable
    (Eventually.of_forall fun p ↦ ?_)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hbu _) (hbv _) (abs_nonneg _) hCu

/-- Let `X` be a complete real normed space and `f : ℝ × ℝ → X` integrable for a measure `μ`. If
`Φ : ℝ → X →L[ℝ] ℝ` is continuous with `‖Φ φ x‖ ≤ ‖x‖` for all `φ` and `x`, and `K : ℝ × ℝ → ℂ` is
continuous with `‖K q‖ ≤ 1` for all `q`, then `q ↦ K q * ((Φ q.2 (f q) : ℝ) : ℂ)` is integrable for
`μ`. The proof dominates its norm by `‖f q‖`. -/
theorem integrable_mul_ofReal_clm_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (f : ℝ × ℝ → X) {μ : Measure (ℝ × ℝ)} (hf : Integrable f μ)
    (Φ : ℝ → X →L[ℝ] ℝ)
    (hΦc : Continuous Φ) (hΦb : ∀ φ x, ‖Φ φ x‖ ≤ ‖x‖) (K : ℝ × ℝ → ℂ) (hKc : Continuous K)
    (hKb : ∀ q, ‖K q‖ ≤ 1) :
    Integrable (fun q ↦ K q * ((Φ q.2 (f q) : ℝ) : ℂ)) μ := by
  refine hf.norm.mono' ?_ (Eventually.of_forall fun q ↦ ?_)
  · have hc : Continuous (fun w : (ℝ × ℝ) × X ↦ K w.1 * ((Φ w.1.2 w.2 : ℝ) : ℂ)) :=
      (hKc.comp continuous_fst).mul (Complex.continuous_ofReal.comp
        ((hΦc.comp (continuous_snd.comp continuous_fst)).clm_apply continuous_snd))
    exact hc.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk hf.aestronglyMeasurable)
  · rw [norm_mul, Complex.norm_real]
    calc ‖K q‖ * ‖Φ q.2 (f q)‖ ≤ 1 * ‖f q‖ :=
          mul_le_mul (hKb q) (hΦb q.2 (f q)) (norm_nonneg _) zero_le_one
      _ = ‖f q‖ := one_mul _

/-- If `u : ℝ → ℝ` is continuous with compact support and `F : ℝ → ℝ` is locally integrable for
Lebesgue measure, then `s ↦ u s * F s` is integrable. This is
`LocallyIntegrable.integrable_smul_left_of_hasCompactSupport` for real-valued `F` on the real line,
with the scalar multiplication written as a product. -/
theorem integrable_mul_of_hasCompactSupport {u : ℝ → ℝ} (hu : Continuous u)
    (hus : HasCompactSupport u) {F : ℝ → ℝ}
    (hF : LocallyIntegrable F volume) : Integrable (fun s ↦ u s * F s) volume := by
  simpa [smul_eq_mul] using hF.integrable_smul_left_of_hasCompactSupport hu hus

/-- If `u v : α → ℝ` both satisfy `MemLp _ 2 μ`, then the product `a ↦ u a * v a` is integrable.
This is `MemLp.integrable_mul` applied to two functions in `L²`. -/
theorem integrable_mul_of_memLp_two {α : Type*} [MeasurableSpace α] {μ : Measure α} {u v : α → ℝ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) : Integrable (fun a ↦ u a * v a) μ :=
  (L2.integrable_inner (𝕜 := ℝ) (hu.toLp u) (hv.toLp v)).congr (by
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with a h1 h2
    rw [h1, h2, Real.inner_apply])

/-- For `F` in `Lp E 2 μ` and `G` in `Lp E' 2 μ`, with `E` and `E'` normed groups, the product of
the pointwise norms `t ↦ ‖F t‖ * ‖G t‖` is integrable. The proof bounds it by
`‖F t‖ ^ 2 + ‖G t‖ ^ 2`. -/
theorem integrable_norm_mul_norm_Lp_two {α E E' : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedAddCommGroup E'] (F : Lp E 2 μ) (G : Lp E' 2 μ) :
    Integrable (fun t ↦ ‖F t‖ * ‖G t‖) μ := by
  refine Integrable.mono' (((Lp.memLp F).integrable_norm_pow two_ne_zero).add
    ((Lp.memLp G).integrable_norm_pow two_ne_zero))
    ((Lp.aestronglyMeasurable F).norm.mul (Lp.aestronglyMeasurable G).norm)
        (ae_of_all _ fun t ↦ ?_)
  change ‖‖F t‖ * ‖G t‖‖ ≤ ‖F t‖ ^ 2 + ‖G t‖ ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  nlinarith [sq_nonneg (‖F t‖ - ‖G t‖), norm_nonneg (F t), norm_nonneg (G t)]

/-- For `u` in `Lp E 2 μ`, with `E` a real inner product space, the function `a ↦ ‖u a‖ ^ 2` is
integrable. -/
theorem integrable_norm_sq_Lp_two {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : Lp E 2 μ) :
    Integrable (fun a ↦ ‖u a‖ ^ 2) μ :=
  (L2.integrable_inner (𝕜 := ℝ) u u).congr (Eventually.of_forall fun _ ↦
      real_inner_self_eq_norm_sq _)

/-- Let `S` be a measurable set of `ℝ × ℝ`, `G : ℝ × ℝ → ℂ` integrable on `S`, and `θ : ℝ × ℝ → ℝ`
continuous with compact support and zero outside `S`. Then `fun p ↦ (θ p : ℂ) * G p` is integrable.
The proof bounds `θ` by a constant and writes the product as `(θ p : ℂ) * S.indicator G p`. -/
theorem integrable_ofReal_mul_of_integrableOn {G : ℝ × ℝ → ℂ} {θ : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)}
    (hG : IntegrableOn G S)
    (hS : MeasurableSet S) (hθ : Continuous θ) (hθc : HasCompactSupport θ)
        (hts : ∀ x, x ∉ S → θ x = 0) :
    Integrable (fun p ↦ (θ p : ℂ) * G p) := by
  obtain ⟨C, hC⟩ := hθc.exists_bound_of_continuous hθ
  have h1 : Integrable (fun t ↦ (θ t : ℂ) * S.indicator G t) :=
    ((integrable_indicator_iff hS).2 hG).bdd_mul (c := C)
      (Complex.continuous_ofReal.comp hθ).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ by rw [Complex.norm_real]; exact hC t)
  refine h1.congr (Eventually.of_forall fun t ↦ ?_)
  by_cases ht : t ∈ S
  · simp [indicator_of_mem ht]
  · simp [hts t ht]

/-- Let `f : ℝ → ℂ` be integrable on `Ioo l u` and `θ : ℝ → ℝ` continuous with compact support and
zero outside `Ioo l u`. Then `fun t ↦ (θ t : ℂ) * f t` is integrable. The proof bounds `θ` by a
constant and writes the product as `(θ t : ℂ) * (Ioo l u).indicator f t`. -/
theorem integrable_ofReal_mul_of_integrableOn_Ioo {f : ℝ → ℂ} {θ : ℝ → ℝ} {l u : ℝ}
    (hf : IntegrableOn f (Ioo l u))
    (hθ : Continuous θ) (hθc : HasCompactSupport θ) (hts : ∀ x, x ∉ Ioo l u → θ x = 0) :
    Integrable (fun t ↦ (θ t : ℂ) * f t) := by
  obtain ⟨C, hC⟩ := hθc.exists_bound_of_continuous hθ
  have h1 : Integrable (fun t ↦ (θ t : ℂ) * (Ioo l u).indicator f t) :=
    ((integrable_indicator_iff measurableSet_Ioo).2 hf).bdd_mul (c := C)
      (Complex.continuous_ofReal.comp hθ).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ by rw [Complex.norm_real]; exact hC t)
  refine h1.congr (Eventually.of_forall fun t ↦ ?_)
  by_cases ht : t ∈ Ioo l u
  · simp [indicator_of_mem ht]
  · simp [hts t ht]

/-- Let `w : ℝ × ℝ → ℝ` be integrable and almost everywhere nonnegative for a measure `μ`. If
`F : ℝ × ℝ → ℂ` is almost everywhere strongly measurable and `‖F p‖ ≤ D` for almost every `p`, then
`p ↦ (w p : ℂ) * F p` is integrable. -/
theorem integrable_ofReal_mul_of_norm_le {μ : Measure (ℝ × ℝ)} (w : ℝ × ℝ → ℝ)
    (hwi : Integrable w μ) (hw0 : ∀ᵐ p ∂μ, 0 ≤ w p) {F : ℝ × ℝ → ℂ}
    (hF : AEStronglyMeasurable F μ) (D : ℝ) (hFb : ∀ᵐ p ∂μ, ‖F p‖ ≤ D) :
    Integrable (fun p ↦ (w p : ℂ) * F p) μ := by
  refine (hwi.mul_const D).mono' ((Complex.continuous_ofReal.comp_aestronglyMeasurable hwi.1).mul
      hF) ?_
  filter_upwards [hw0, hFb] with p h0 hb
  rw [norm_mul, Complex.norm_of_nonneg h0]
  exact mul_le_mul_of_nonneg_left hb h0

/-- Let `w : ℝ × ℝ → ℝ` be integrable and almost everywhere nonnegative for a measure `μ`, and for
every `j` in a finite set `Js` let the complex functions `p ↦ f p j` and `p ↦ φ i p j`, for all `i`
in a type `n`, be almost everywhere strongly measurable, with `p ↦ w p * ‖f p j‖ ^ 2` integrable.
If at almost every `p` the bound `‖φ i p j‖ ≤ C` holds for all `i` and all `j ∈ Js`, then
`p ↦ (w p : ℂ) * ∑ j ∈ Js, f p j * (starRingEnd ℂ) (φ i p j)` is integrable for every `i`. The proof
dominates the norm by `C * (Js.card * w p + ∑ j ∈ Js, w p * ‖f p j‖ ^ 2)`, using
`‖f p j‖ ≤ 1 + ‖f p j‖ ^ 2`. -/
theorem integrable_ofReal_mul_sum_mul_conj {n : Type*} {J : Type*} {μ : Measure (ℝ × ℝ)}
    (Js : Finset J) (w : ℝ × ℝ → ℝ) (f : ℝ × ℝ → J → ℂ) (φ : n → ℝ × ℝ → J → ℂ)
    (hwi : Integrable w μ) (hw0 : ∀ᵐ p ∂μ, 0 ≤ w p)
    (hfm : ∀ j ∈ Js, AEStronglyMeasurable (fun p ↦ f p j) μ)
    (hfi : ∀ j ∈ Js, Integrable (fun p ↦ w p * ‖f p j‖ ^ 2) μ)
    (hφm : ∀ i, ∀ j ∈ Js, AEStronglyMeasurable (fun p ↦ φ i p j) μ)
    {C : ℝ} (hφb : ∀ᵐ p ∂μ, ∀ i, ∀ j ∈ Js, ‖φ i p j‖ ≤ C) (i : n) :
    Integrable (fun p ↦ (w p : ℂ) * ∑ j ∈ Js, f p j * (starRingEnd ℂ) (φ i p j)) μ := by
  have hdom : Integrable (fun p ↦ C * (↑Js.card * w p + ∑ j ∈ Js, w p * ‖f p j‖ ^ 2)) μ :=
    ((hwi.const_mul _).add (integrable_finsetSum _ hfi)).const_mul C
  refine hdom.mono' ((Complex.continuous_ofReal.comp_aestronglyMeasurable hwi.1).mul
    (Finset.aestronglyMeasurable_fun_sum _ fun j hj ↦
      (hfm j hj).mul (Complex.continuous_conj.comp_aestronglyMeasurable (hφm i j hj)))) ?_
  filter_upwards [hφb, hw0] with p hp h0
  rw [norm_mul, Complex.norm_of_nonneg h0]
  have hb : ‖∑ j ∈ Js, f p j * (starRingEnd ℂ) (φ i p j)‖ ≤ C * ∑ j ∈ Js, (1 + ‖f p j‖ ^ 2) := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj ↦ ?_)
    rw [norm_mul, Complex.norm_conj]
    have h1 : ‖f p j‖ ≤ 1 + ‖f p j‖ ^ 2 := by
      nlinarith [sq_nonneg (‖f p j‖ - 1), norm_nonneg (f p j)]
    calc ‖f p j‖ * ‖φ i p j‖ ≤ (1 + ‖f p j‖ ^ 2) * C :=
          mul_le_mul h1 (hp i j hj) (norm_nonneg _) (by positivity)
      _ = C * (1 + ‖f p j‖ ^ 2) := by ring
  calc w p * ‖∑ j ∈ Js, f p j * (starRingEnd ℂ) (φ i p j)‖ ≤ w p *
           (C * ∑ j ∈ Js, (1 + ‖f p j‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hb h0
    _ = C * (↑Js.card * w p + ∑ j ∈ Js, w p * ‖f p j‖ ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
        ring

/-- Let `X` be a Hausdorff topological space whose open sets are measurable, `f : X → E` locally
integrable for a measure `μ` with values in a real normed space, and `c : X → ℝ` continuous with
compact support. If `h : X → ℝ` is almost everywhere strongly measurable and
`|h x| ≤ K * ‖f x‖ * c x` for all `x`, with `0 ≤ K`, then `h` is integrable. The proof dominates `h`
by `K` times the norm of the integrable function `c • f`. -/
theorem integrable_of_local_bound {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [T2Space X] {μ : Measure X} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : X → E} (hf : LocallyIntegrable f μ) {c : X → ℝ} (hc : Continuous c)
        (hcs : HasCompactSupport c)
    {h : X → ℝ} (hm : AEStronglyMeasurable h μ) {K : ℝ} (hK : 0 ≤ K)
        (hb : ∀ x, |h x| ≤ K * ‖f x‖ * c x) :
    Integrable h μ := by
  have hi := (hf.integrable_smul_left_of_hasCompactSupport hc hcs).norm.const_mul K
  refine hi.mono' hm (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, norm_smul, Real.norm_eq_abs]
  calc |h x| ≤ K * ‖f x‖ * c x := hb x
    _ ≤ K * ‖f x‖ * |c x| := mul_le_mul_of_nonneg_left (le_abs_self _)
        (mul_nonneg hK (norm_nonneg _))
    _ = K * (|c x| * ‖f x‖) := by ring

/-- Let `w : X → ℝ` be almost everywhere strongly measurable and almost everywhere nonnegative for a
measure `μ`, and let `a b : X → ℂ` be almost everywhere strongly measurable. If
`x ↦ w x * ‖a x‖ ^ 2` and `x ↦ w x * ‖b x‖ ^ 2` are integrable, then
`x ↦ (w x : ℂ) * (a x * (starRingEnd ℂ) (b x))` is integrable. The proof dominates its norm by
`(w x * ‖a x‖ ^ 2 + w x * ‖b x‖ ^ 2) / 2`. -/
theorem integrable_weight_mul_conj {X : Type*} [MeasurableSpace X] {μ : Measure X} {w : X → ℝ}
    {a b : X → ℂ} (hw : ∀ᵐ x ∂μ, 0 ≤ w x) (hwm : AEStronglyMeasurable w μ)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hai : Integrable (fun x ↦ w x * ‖a x‖ ^ 2) μ) (hbi : Integrable
        (fun x ↦ w x * ‖b x‖ ^ 2) μ) :
    Integrable (fun x ↦ (w x : ℂ) * (a x * (starRingEnd ℂ) (b x))) μ := by
  refine Integrable.mono' ((hai.add hbi).div_const 2) ?_ ?_
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hwm).mul
      (ha.mul (Complex.continuous_conj.comp_aestronglyMeasurable hb))
  · filter_upwards [hw] with x hx
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hx]
    have h1 : 0 ≤ (‖a x‖ - ‖b x‖) ^ 2 := sq_nonneg _
    have h2 : w x * (‖a x‖ * ‖b x‖) ≤ w x * ((‖a x‖ ^ 2 + ‖b x‖ ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hx
    simp only [Pi.add_apply]
    linarith

/-- For `0 < δ`, the function `fun t : ℝ ↦ t⁻¹` is not integrable on `Ioo 0 δ`. The proof reduces
to interval integrability of the inverse on `0..δ`, which fails because this interval is
nondegenerate and contains `0`. -/
theorem not_integrableOn_inv_Ioo_zero {δ : ℝ} (hδ : 0 < δ) : ¬ IntegrableOn (fun t : ℝ ↦ t⁻¹)
    (Ioo 0 δ) := by
  intro h
  have : IntervalIntegrable (fun t : ℝ ↦ t⁻¹) volume 0 δ := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hδ.le]
    exact h
  rw [intervalIntegrable_inv_iff] at this
  rcases this with h1 | h1
  · exact hδ.ne h1
  · exact h1 (by simp [hδ.le])

/-- Let `T τ` be continuous linear maps on a real Hilbert space `E` with
`‖T τ‖ ≤ Real.exp (-(τ / 4))` for all `τ ≥ 0` and with `τ ↦ T τ y` continuous on `Ici 0` for every
`y`, and let `G : ℝ → E` be continuous with `‖G σ‖ ≤ C` for all `σ`. Then for all real `σ` and `P`,
the function `τ ↦ T τ (G (σ - τ / P))` is integrable for Lebesgue measure restricted to `Ioi 0`. -/
theorem integrable_Ioi_apply_comp_sub_div {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (T : ℝ → E →L[ℝ] E)
    (hnorm : ∀ τ, 0 ≤ τ → ‖T τ‖ ≤ Real.exp (-(τ / 4)))
    (hcont : ∀ y, ContinuousOn (fun τ ↦ T τ y) (Ici 0))
    (G : ℝ → E) (hG : Continuous G) (C : ℝ) (hC : ∀ σ, ‖G σ‖ ≤ C) {P : ℝ} (σ : ℝ) :
    Integrable (fun τ ↦ T τ (G (σ - τ / P))) (volume.restrict (Ioi (0 : ℝ))) :=
  (integrable_exp_neg_mul_mul_const_Ioi C).mono' (aestronglyMeasurable_Ioi_apply_comp_sub_div T
      hnorm hcont G hG σ)
    (ae_Ioi_norm_apply_le_exp_mul T hnorm G C hC σ)

/-- For `0 < a` and `0 < b`, `∫ r in Ioi 0, (a + b * r ^ 2)⁻¹ = π / (2 * Real.sqrt (a * b))`. -/
theorem integral_Ioi_inv_add_mul_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ r in Ioi (0 : ℝ), (a + b * r ^ 2)⁻¹ = π / (2 * Real.sqrt (a * b)) := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun r _ ↦ hasDerivAt_arctan_sqrt_mul_div ha hb r)
    (integrableOn_Ioi_inv_add_mul_sq ha hb) (tendsto_arctan_sqrt_mul_div_atTop ha hb)]
  rw [mul_sqrt_div_eq_sqrt_mul ha hb]
  simp only [mul_zero, arctan_zero, zero_div, sub_zero]
  ring

/-- Let `E` be a real normed space and `φ : ℝ → E → ℂ` such that `fun q ↦ φ q.1 q.2` is continuous,
`‖φ θ e‖ ≤ ‖e‖`, and `φ θ (a • u + b • u') = a * φ θ u + b * φ θ u'` for all real `a`, `b`. If `f`,
`f' : ℝ → E` are integrable on `s`, then
`∫ θ in s, φ θ (a • f θ + b • f' θ) = a * (∫ θ in s, φ θ (f θ)) + b * ∫ θ in s, φ θ (f'
θ)` for all real `a`, `b`. The proof uses the linearity hypothesis pointwise and the integrability
of `fun θ ↦ φ θ (f θ)` and `fun θ ↦ φ θ (f' θ)`. -/
theorem setIntegral_comp_smul_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℝ → E → ℂ} (hφc : Continuous (fun q : ℝ × E ↦ φ q.1 q.2)) (hφb : ∀ θ e, ‖φ θ e‖ ≤ ‖e‖)
    (hlin : ∀ θ (a b : ℝ) u u', φ θ (a • u + b • u') = (a : ℂ) * φ θ u + (b : ℂ) * φ θ u')
    {f f' : ℝ → E} {s : Set ℝ} (hf : IntegrableOn f s) (hf' : IntegrableOn f' s) (a b : ℝ) :
    ∫ θ in s, φ θ (a • f θ + b • f' θ) = (a : ℂ) * (∫ θ in s, φ θ (f θ)) + (b : ℂ) * ∫ θ in s,
        φ θ (f' θ) := by
  simp_rw [hlin]
  have h1 : ∫ θ in s, (a : ℂ) * φ θ (f θ) = (a : ℂ) * ∫ θ in s, φ θ (f θ) := by
    simpa only [smul_eq_mul] using integral_smul (μ := volume.restrict s) (a : ℂ)
        (fun θ ↦ φ θ (f θ))
  have h2 : ∫ θ in s, (b : ℂ) * φ θ (f' θ) = (b : ℂ) * ∫ θ in s, φ θ (f' θ) := by
    simpa only [smul_eq_mul] using integral_smul (μ := volume.restrict s) (b : ℂ)
        (fun θ ↦ φ θ (f' θ))
  rw [integral_add ((integrableOn_comp_of_norm_le hφc hφb hf).const_mul (a : ℂ))
      ((integrableOn_comp_of_norm_le hφc hφb hf').const_mul (b : ℂ)), h1, h2]

/-- Let `F`, `g : ℝ × ℝ → ℂ` be such that `F` and `fun p ↦ (p.1 : ℂ) * g p` are integrable on every
rectangle `Icc 0 R ×ˢ Icc (-Z) Z`. If `α : ℝ → ℝ` is `C^1` with `tsupport α ⊆ Ioo 0 R`, then for
every real `Z` both `fun p ↦ (deriv α p.1 : ℂ) * F p` and `fun p ↦ (α p.1 : ℂ) * g p` are
integrable on `univ ×ˢ Icc (-Z) Z`. The proof multiplies by the continuous factors `deriv α p.1` and
`α p.1 / p.1` on the compact rectangle and uses that both products vanish outside it. -/
theorem integrableOn_deriv_mul_and_mul_of_tsupport {F : ℝ × ℝ → ℂ} {g : ℝ × ℝ → ℂ}
    (hF : ∀ R Z, IntegrableOn F (Icc 0 R ×ˢ Icc (-Z) Z))
    (hg : ∀ R Z, IntegrableOn (fun p : ℝ × ℝ ↦ (p.1 : ℂ) * g p) (Icc 0 R ×ˢ Icc (-Z) Z))
    {α : ℝ → ℝ} (hα : ContDiff ℝ 1 α) {R : ℝ} (hs : tsupport α ⊆ Ioo 0 R) (Z : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ ↦ ((deriv α p.1 : ℝ) : ℂ) * F p) (univ ×ˢ Icc (-Z) Z) ∧
      IntegrableOn (fun p : ℝ × ℝ ↦ (α p.1 : ℂ) * g p) (univ ×ˢ Icc (-Z) Z) := by
  have hpos : ∀ x ∈ tsupport α, 0 < x := fun x hx ↦ (hs hx).1
  have hK : IsCompact (Icc (0 : ℝ) R ×ˢ Icc (-Z) Z) := isCompact_Icc.prod isCompact_Icc
  have hmeas : MeasurableSet (univ ×ˢ Icc (-Z) Z : Set (ℝ × ℝ)) :=
      MeasurableSet.univ.prod measurableSet_Icc
  have hout : ∀ p ∈ (univ ×ˢ Icc (-Z) Z : Set (ℝ × ℝ)) \ (Icc 0 R ×ˢ Icc (-Z) Z),
      p.1 ∉ tsupport α := by
    intro p hp h
    exact hp.2 ⟨⟨(hs h).1.le, (hs h).2.le⟩, hp.1.2⟩
  constructor
  · have h1 := (hF R Z).continuousOn_mul
      (g := fun p : ℝ × ℝ ↦ ((deriv α p.1 : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp ((hα.continuous_deriv le_rfl).comp
          continuous_fst)).continuousOn hK
    refine h1.of_forall_sdiff_eq_zero hmeas (fun p hp ↦ ?_)
    simp [deriv_of_notMem_tsupport (hout p hp)]
  · have h1 := (hg R Z).continuousOn_mul
      (g := fun p : ℝ × ℝ ↦ ((α p.1 / p.1 : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp ((continuous_div_id_of_tsupport_pos hα.continuous hpos).comp
          continuous_fst)).continuousOn hK
    have h2 : IntegrableOn (fun p : ℝ × ℝ ↦ (α p.1 : ℂ) * g p) (Icc 0 R ×ˢ Icc (-Z) Z) := by
      refine IntegrableOn.congr_fun h1 (fun p _ ↦ ?_) hK.measurableSet
      conv_rhs => rw [eq_div_mul_self_of_tsupport_pos hpos p.1]
      push_cast
      ring
    refine h2.of_forall_sdiff_eq_zero hmeas (fun p hp ↦ ?_)
    simp [image_eq_zero_of_notMem_tsupport (hout p hp)]

/-- Let `0 < r₁` and `F : ℝ × ℝ → ℂ`. If `p ↦ p.1 * F p` is integrable on the rectangle
`[r₁, r₂] × [z₁, z₂]`, then `F` is integrable on that rectangle. The factor `p.1⁻¹` is
continuous on the compact rectangle. -/
theorem integrableOn_of_integrableOn_fst_mul {r₁ r₂ z₁ z₂ : ℝ} (h0 : 0 < r₁) {F : ℝ × ℝ → ℂ}
    (h : IntegrableOn (fun p : ℝ × ℝ ↦ (p.1 : ℂ) * F p) (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂)) :
    IntegrableOn F (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂) := by
  have hs := isCompact_Icc_prod_Icc r₁ r₂ z₁ z₂
  have hc : ContinuousOn (fun p : ℝ × ℝ ↦ ((p.1⁻¹ : ℝ) : ℂ)) (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂) :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuous_fst.continuousOn.inv₀ (fun p hp ↦ (h0.trans_le hp.1.1).ne'))
  refine (IntegrableOn.continuousOn_mul hc h hs).congr_fun (fun p hp ↦ ?_) hs.measurableSet
  have hp0 : (p.1 : ℂ) ≠ 0 := by exact_mod_cast (h0.trans_le hp.1.1).ne'
  push_cast
  field_simp

/-- If `s` is a compact set of `ℝ × ℝ`, `B : ℝ × ℝ → ℝ` is continuous and `F : ℝ × ℝ → ℂ` is
integrable on `s`, then `p ↦ B p * F p`, with `B p` seen in `ℂ`, is integrable on `s`. -/
theorem integrableOn_ofReal_mul_of_continuous {s : Set (ℝ × ℝ)} (hs : IsCompact s) {B : ℝ × ℝ → ℝ}
    (hB : Continuous B)
    {F : ℝ × ℝ → ℂ} (h : IntegrableOn F s) : IntegrableOn (fun p ↦ ((B p : ℝ) : ℂ) * F p) s :=
  IntegrableOn.continuousOn_mul (Complex.continuous_ofReal.comp hB).continuousOn h hs

/-- Let `t : ℝ → ℝ` be continuous, `c ≠ 0` and `0 ≤ min c o`, and let `dF : ℝ × ℝ → ℂ`. If
`p ↦ (p.1 : ℂ) * dF p` is integrable on the rectangle `Icc (min c o) (max c o) ×ˢ Icc lo hi`, then
so is `p ↦ (((p.1 - o) / (c - o) * t p.2 : ℝ) : ℂ) * dF p`. The proof treats `o = 0`, where the new
weight is `p.1` times the continuous function `t p.2 / c`, and `o ≠ 0`, where `0 < min c o ≤ p.1` on
the rectangle and the weight `p.1` can be removed. -/
theorem integrableOn_sub_div_mul_of_fst_mul {c o lo hi : ℝ} {t : ℝ → ℝ} (ht : Continuous t)
    {dF : ℝ × ℝ → ℂ}
    (hc : c ≠ 0) (hmin : 0 ≤ min c o)
    (hw : IntegrableOn (fun p : ℝ × ℝ ↦ (p.1 : ℂ) * dF p) (Icc (min c o) (max c o) ×ˢ Icc lo hi)) :
    IntegrableOn (fun p : ℝ × ℝ ↦ ((((p.1 - o) / (c - o)) * t p.2 : ℝ) : ℂ) * dF p)
      (Icc (min c o) (max c o) ×ˢ Icc lo hi) := by
  have hs := isCompact_Icc_prod_Icc (min c o) (max c o) lo hi
  by_cases ho : o = 0
  · subst ho
    refine (integrableOn_ofReal_mul_of_continuous hs (B := fun p ↦ t p.2 / c) (by
      fun_prop) hw).congr_fun (fun p _ ↦ ?_)
      hs.measurableSet
    push_cast
    ring
  · have hne : min c o ≠ 0 := by
      rcases min_choice c o with h | h <;> rw [h]
      · exact hc
      · exact ho
    exact integrableOn_ofReal_mul_of_continuous hs (by
      fun_prop) (integrableOn_of_integrableOn_fst_mul (lt_of_le_of_ne hmin (Ne.symm hne)) hw)

/-- Let `w`, `M`, `om : ℝ × ℝ → ℂ` with `om p = (2 * π : ℂ) * M p` for all `p`. If
`fun p ↦ w p * om p` is integrable, then `fun p ↦ w p * M p` is integrable. -/
theorem integrable_mul_of_two_pi_mul {w M : ℝ × ℝ → ℂ} {om : ℝ × ℝ → ℂ}
    (hom : ∀ p, om p = (2 * Real.pi : ℂ) * M p)
    (h : Integrable fun p ↦ w p * om p) : Integrable fun p ↦ w p * M p := by
  have h2 := h.const_mul (1 / (2 * Real.pi) : ℂ)
  refine h2.congr (Filter.Eventually.of_forall fun p ↦ ?_)
  simp only [hom]
  field_simp [two_mul_ofReal_pi_ne_zero]

/-- Let `c ≠ 0` and `0 ≤ min c o`, and write `S = Icc (min c o) (max c o) ×ˢ Icc lo hi`. If
`fun p ↦ (p.1 : ℂ) * dF p` is integrable on `S`, then
`fun p ↦ (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p` is integrable on `S`. The proof treats `o = 0`,
where the factor is `p.1 / c`, and `o ≠ 0`, where `0 < p.1` on `S` and the factor divided by `p.1`
is continuous on the compact set `S`. -/
theorem integrableOn_sub_div_mul_of_integrableOn {c o lo hi : ℝ} {dF : ℝ × ℝ → ℂ} (hc : c ≠ 0)
    (hmin : 0 ≤ min c o)
    (h1 : IntegrableOn (fun p : ℝ × ℝ ↦ (p.1 : ℂ) * dF p)
        (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi)) :
    IntegrableOn (fun p : ℝ × ℝ ↦ (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p)
      (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi) := by
  have hs := isCompact_Icc_prod_Icc (min c o) (max c o) lo hi
  by_cases ho : o = 0
  · subst ho
    refine (integrableOn_mul_ofReal_of_continuous hs (W := fun _ ↦ 1 / c) continuous_const
        h1).congr_fun (fun p _ ↦ ?_) hs.measurableSet
    simp only [sub_zero]
    push_cast
    ring
  · have hpos : 0 < min c o := by
      refine lt_of_le_of_ne hmin ?_
      rcases min_choice c o with h | h <;> rw [h]
      · exact Ne.symm hc
      · exact Ne.symm ho
    have hne : ∀ p ∈ Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi, p.1 ≠ 0 :=
      fun p hp ↦ (hpos.trans_le hp.1.1).ne'
    have hg : ContinuousOn (fun p : ℝ × ℝ ↦ (((p.1 - o) / (c - o) / p.1 : ℝ) : ℂ))
        (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi) := by
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      refine ContinuousOn.div ?_ continuous_fst.continuousOn hne
      exact (Continuous.continuousOn (by fun_prop))
    refine (h1.mul_continuousOn hg hs).congr_fun (fun p hp ↦ ?_) hs.measurableSet
    have h0 : (p.1 : ℂ) ≠ 0 := by exact_mod_cast hne p hp
    push_cast
    field_simp

/-- Let `f : α → ℝ` be a.e. strongly measurable for `μ`. If `∫⁻ x, ENNReal.ofReal (f x) ∂μ` and
`∫⁻ x, ENNReal.ofReal (-f x) ∂μ` are both finite, then `f` is integrable for `μ`. The norm
`|f x|` is the sum of the positive part and the negative part. -/
theorem integrable_of_lintegral_pos_neg_ne_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (hp : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ⊤)
    (hn : ∫⁻ x, ENNReal.ofReal (-f x) ∂μ ≠ ⊤) : Integrable f μ := by
  refine ⟨hf, ?_⟩
  unfold HasFiniteIntegral
  have e : ∀ x, ‖f x‖ₑ = ENNReal.ofReal (f x) + ENNReal.ofReal (-f x) := by
    intro x
    rw [Real.eNorm_eq_ofReal_abs]
    rcases le_total 0 (f x) with h | h
    · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (neg_nonpos.2 h), add_zero]
    · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]
  simp_rw [e]
  rw [lintegral_add_left' hf.aemeasurable.ennreal_ofReal]
  exact ENNReal.add_lt_top.2 ⟨hp.lt_top, hn.lt_top⟩

/-- For `α > 1` the function `τ ↦ exp (-τ) ^ (1 - 1 / (2 α)) * (1 - exp (-τ)) ^ (-(1 / (2 α)))` is
integrable on `(0, ∞)`. On `(0, 1]` it is at most `2 τ ^ (-(1 / (2 α)))`, and for `τ > 1` it
decays exponentially. -/
theorem integrableOn_exp_neg_rpow_mul_sub_rpow {α : ℝ} (hα1 : 1 < α) :
    IntegrableOn (fun τ : ℝ ↦ Real.exp (-τ) ^ (1 - 1 / (2 * α)) *
      (1 - Real.exp (-τ)) ^ (-(1 / (2 * α)))) (Ioi 0) := by
  set s : ℝ := 1 / (2 * α) with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have hs1 : s < 1 := by rw [hs, div_lt_one (by linarith)]; linarith
  have hmeas : Measurable (fun τ : ℝ ↦ Real.exp (-τ) ^ (1 - s) * (1 - Real.exp (-τ)) ^ (-s)) := by
    fun_prop
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have hint : IntegrableOn (fun τ : ℝ ↦ τ ^ (-s)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    refine (hint.const_mul 2).mono' hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun τ hτ ↦ ?_)
    have hτ0 : 0 < τ := hτ.1
    have hge := half_le_one_sub_exp_neg hτ0 hτ.2
    have hp : 0 < 1 - Real.exp (-τ) := by linarith
    have ha : Real.exp (-τ) ^ (1 - s) ≤ 1 :=
      Real.rpow_le_one (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith)) (by linarith)
    have hb : (1 - Real.exp (-τ)) ^ (-s) ≤ (2⁻¹ * τ) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have hc : (2⁻¹ * τ) ^ (-s) = (2 : ℝ) ^ s * τ ^ (-s) := by
      rw [Real.mul_rpow (by
        norm_num) hτ0.le, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num),
        inv_inv]
    have hd : (2 : ℝ) ^ s ≤ 2 := by
      calc (2 : ℝ) ^ s ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1.le
        _ = 2 := Real.rpow_one 2
    have hn : 0 ≤ Real.exp (-τ) ^ (1 - s) * (1 - Real.exp (-τ)) ^ (-s) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    have hτs : 0 ≤ τ ^ (-s) := Real.rpow_nonneg hτ0.le _
    have hq : 0 ≤ (1 - Real.exp (-τ)) ^ (-s) := Real.rpow_nonneg hp.le _
    calc Real.exp (-τ) ^ (1 - s) * (1 - Real.exp (-τ)) ^ (-s) ≤ 1 * (1 - Real.exp (-τ)) ^ (-s) :=
          mul_le_mul_of_nonneg_right ha hq
      _ ≤ 1 * ((2 : ℝ) ^ s * τ ^ (-s)) := by rw [← hc]; linarith
      _ ≤ 2 * τ ^ (-s) := by nlinarith
  · have hc : 0 < 1 - s := by linarith
    have hint := (exp_neg_integrableOn_Ioi 1 hc).const_mul ((1 - Real.exp (-1)) ^ (-s))
    refine hint.mono' hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun τ hτ ↦ ?_)
    have hτ1 : 1 < τ := hτ
    have hp1 : 0 < 1 - Real.exp (-1) := sub_pos.mpr (exp_neg_lt_one (by norm_num))
    have hle : Real.exp (-τ) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have hb : (1 - Real.exp (-τ)) ^ (-s) ≤ (1 - Real.exp (-1)) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos hp1 (by linarith) (by linarith)
    have he : Real.exp (-τ) ^ (1 - s) = Real.exp (-(1 - s) * τ) := by
      rw [← Real.exp_mul]; ring_nf
    have hn : 0 ≤ Real.exp (-τ) ^ (1 - s) * (1 - Real.exp (-τ)) ^ (-s) := by
      have : 0 < 1 - Real.exp (-τ) := by linarith [Real.exp_pos (-1)]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hn, he, mul_comm]
    exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le

end PDE.Analysis
