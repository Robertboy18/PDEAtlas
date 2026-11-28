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
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import Mathlib.Topology.Separation.CompletelyRegular
public import PDE.Analysis.Complex.Exponential
public import PDE.Analysis.Complex.NormSq
public import PDE.Analysis.Complex.Numbers
public import PDE.Analysis.Lp.Functions
public import PDE.Analysis.MeasureTheory.IntervalIntegral
public import PDE.Analysis.Topology.Continuity

set_option linter.style.header false

/-!
# Fourier coefficients on the circle and the torus

The lemmas compute Fourier coefficients (of a function minus a constant, among others) and state
Parseval-type identities on an interval. The proofs use `fourierCoeffOn`, the orthonormality of the
characters and the lemmas of Mathlib on `AddCircle`.

## Main results

* `PDE.Analysis.periodic_apply_eq_of_coe_eq`: Let `f : ℝ → β` be periodic with period `1`
  (`Function.Periodic f 1`). If the real numbers `r` and `σ` have the same image in `UnitAddCircle`,
  the additive circle of period `1`, then `f r = f σ`.
* `PDE.Analysis.fourierCoeff_sub_const`: Subtracting a constant from a function on the circle
  changes only the zeroth Fourier coefficient: for `0 < T`, `f : AddCircle T → ℂ` integrable for the
  Haar measure, `c : ℂ` and `n : ℤ`,
  `fourierCoeff (fun t ↦ f t - c) n = fourierCoeff f n - (if n = 0 then c else 0)`.
* `PDE.Analysis.hasSum_conj_mul_fourierCoeff`: Parseval's identity for a pair on the circle
  `AddCircle T` (`0 < T`, Haar probability measure): for `X` in `Lp ℂ 2` and `Z : AddCircle T → ℂ`
  with `MemLp Z 2`, the family `j ↦ conj (fourierCoeff X j) * fourierCoeff Z j` over `ℤ` has sum
  `∫ t, conj (X t) * Z t ∂haarAddCircle`.
* `PDE.Analysis.hasSum_conj_mul_fourierCoeffOn`: Parseval's identity for a pair on an interval: for
  `a < b` and `f g : ℝ → ℂ` with `MemLp _ 2 (volume.restrict (Ioc a b))`, the family
  `i ↦ conj (fourierCoeffOn hab g i) * fourierCoeffOn hab f i` over `ℤ` has sum
  `(b - a)⁻¹ • ∫ x in a..b, conj (g x) * f x`.
* `PDE.Analysis.hasSum_fourierCoeff_mul_of_bounded`: The Fourier coefficients of a product on the
  circle `AddCircle T` (`0 < T`) are a convolution: if `F : AddCircle T → ℂ` is almost everywhere
  strongly measurable with `‖F t‖ ≤ C` for all `t` and `Y` is in `Lp ℂ 2` of the Haar measure, then
  for every `j : ℤ` the family `i ↦ fourierCoeff F (j - i) * fourierCoeff Y i` over `ℤ` has sum
  `fourierCoeff (fun t ↦ F t * Y t) j`.
* `PDE.Analysis.integral_exp_neg_mul_eq_fourierCoeffOn_pi`: On the interval from `-π` to `π` the
  Fourier coefficient is the classical integral: for every `h : ℝ → ℂ`, `k : ℤ` and `hab : -π < π`,
  `(1 / (2 * π)) * ∫ θ in (-π)..π, exp (-(k * θ * I)) * h θ = fourierCoeffOn hab h k`.
* `PDE.Analysis.integral_integral_re_exp_mul_re_exp`: Write `e x` for
  `Complex.exp ((x : ℂ) * Complex.I)` with `x` real. For `ξ ζ : ℤ × ℤ` and `A B : ℂ`, `∫ σ in Icc 0
  1, ∫ θ in 0..2 * π, (e (2 * π * ξ.1 * σ + ξ.2 * θ) * A).re * (e (2 * π * ζ.1 * σ + ζ.2 * θ) *
  B).re = π * ((if ξ = ζ then A * (starRingEnd ℂ) B else 0) + (if ξ = -ζ then A * B else 0)).re`.
* `PDE.Analysis.intervalIntegrable_const_mul_exp_two_pi_int`: For a complex `c` and an integer `a`,
  the function `fun τ : ℝ ↦ c * Complex.exp (((2 * π * (a : ℝ) * τ : ℝ) : ℂ) * Complex.I)` is
  interval integrable on `0..1`.

There are 10 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open MeasureTheory ComplexConjugate Set

namespace PDE.Analysis

/-- Parseval's identity for a pair on an interval: for `a < b` and `f g : ℝ → ℂ` with
`MemLp _ 2 (volume.restrict (Ioc a b))`, the family
`i ↦ conj (fourierCoeffOn hab g i) * fourierCoeffOn hab f i` over `ℤ` has sum
`(b - a)⁻¹ • ∫ x in a..b, conj (g x) * f x`. The proof lifts `f` and `g` to the circle
`AddCircle (b - a)` and expands their `L²` inner product in the Fourier Hilbert basis. -/
theorem hasSum_conj_mul_fourierCoeffOn {a b : ℝ} {f g : ℝ → ℂ} (hab : a < b)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc a b))) (hg : MemLp g 2
        (volume.restrict (Set.Ioc a b))) :
    HasSum (fun i ↦ conj (fourierCoeffOn hab g i) * fourierCoeffOn hab f i)
      ((b - a)⁻¹ • ∫ x in a..b, conj (g x) * f x) := by
  obtain ⟨T, rfl⟩ : ∃ T, b = a + T := ⟨b - a, by ring⟩
  have hT : 0 < T := by linarith
  have := Fact.mk hT
  have h1 := hf.memLp_liftIoc.haarAddCircle
  have h2 := hg.memLp_liftIoc.haarAddCircle
  have H := fourierBasis.hasSum_inner_mul_inner h2.toLp h1.toLp
  have e1 : (fun i ↦ conj (fourierCoeffOn hab g i) * fourierCoeffOn hab f i) = fun i ↦
      inner ℂ h2.toLp (fourierBasis i) * inner ℂ (fourierBasis i) h1.toLp := by
    funext i
    rw [← inner_conj_symm h2.toLp, ← HilbertBasis.repr_apply_apply, ← HilbertBasis.repr_apply_apply,
      fourierBasis_repr, fourierBasis_repr, fourierCoeff_congr_ae h1.coeFn_toLp,
      fourierCoeff_congr_ae h2.coeFn_toLp, fourierCoeff_liftIoc_eq, fourierCoeff_liftIoc_eq]
  have e2 : ((a + T - a)⁻¹ • ∫ x in a..a + T, conj (g x) * f x) = inner ℂ h2.toLp h1.toLp := by
    rw [add_sub_cancel_left, MeasureTheory.L2.inner_def,
        ← AddCircle.integral_liftIoc_eq_intervalIntegral,
      ← AddCircle.integral_haarAddCircle]
    apply integral_congr_ae
    filter_upwards [h1.coeFn_toLp, h2.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2]
    simp [AddCircle.liftIoc, mul_comm]
  rw [e1, e2]
  exact H

/-- For `0 < T` and `f` in `Lp ℂ 2` of the circle `AddCircle T` with its Haar probability measure,
the inner product of the `i`-th vector of the Fourier Hilbert basis with `f` is the `i`-th Fourier
coefficient: `inner ℂ (fourierBasis i) f = fourierCoeff f i`. -/
theorem inner_fourierBasis_eq_fourierCoeff {T : ℝ} [hT : Fact (0 < T)]
    (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) (i : ℤ) :
    inner ℂ (fourierBasis i) f = fourierCoeff f i := by
  rw [← HilbertBasis.repr_apply_apply, fourierBasis_repr]

/-- On the interval from `-π` to `π` the Fourier coefficient is the classical integral: for every
`h : ℝ → ℂ`, `k : ℤ` and `hab : -π < π`,
`(1 / (2 * π)) * ∫ θ in (-π)..π, exp (-(k * θ * I)) * h θ = fourierCoeffOn hab h k`. The proof
unfolds `fourierCoeffOn_eq_integral` and writes the character `fourier (-k)` of `AddCircle (2 * π)`
as this exponential. -/
theorem integral_exp_neg_mul_eq_fourierCoeffOn_pi (h : ℝ → ℂ) (k : ℤ) (hab : -Real.pi < Real.pi) :
    (1 / (2 * Real.pi) : ℂ) * ∫ θ in (-Real.pi)..Real.pi,
        Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) * h θ =
      fourierCoeffOn hab h k := by
  rw [fourierCoeffOn_eq_integral]
  have e2 : Real.pi - -Real.pi = 2 * Real.pi := by ring
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Complex.real_smul]
  congr 1
  · rw [e2]; push_cast; ring
  · refine intervalIntegral.integral_congr fun θ _ ↦ ?_
    simp only [smul_eq_mul]
    congr 1
    rw [fourier_coe_apply]
    congr 1
    rw [e2]
    push_cast
    field_simp

/-- For `0 < T` and an integer `n`, the integral of the character `fourier (-n)` over `AddCircle T`
with respect to the Haar probability measure is `1` if `n = 0` and `0` otherwise. This is the
orthonormality of the characters applied to `fourier n` and `fourier 0`. -/
theorem integral_fourier_neg_haarAddCircle {T : ℝ} [hT : Fact (0 < T)] (n : ℤ) :
    ∫ t, fourier (-n) t ∂(AddCircle.haarAddCircle (T := T)) = if n = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (orthonormal_fourier (T := T))) n 0
  rw [inner_haarAddCircle_eq_integral_conj_mul] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_fourierLp (T := T) 2 n, coeFn_fourierLp (T := T) 2 0] with t h1 h2
  rw [h1, h2, fourier_zero, mul_one, fourier_neg]

/-- Write `e x` for `Complex.exp ((x : ℂ) * Complex.I)` with `x` real. For `ξ ζ : ℤ × ℤ`, `A B : ℂ`
and real `σ`, the integral
`∫ θ in 0..2 * π, (e (2 * π * ξ.1 * σ + ξ.2 * θ) * A).re * (e (2 * π * ζ.1 * σ + ζ.2 * θ) *
B).re` equals `π * ((if ξ.2 = ζ.2 then A * (starRingEnd ℂ) B else 0) * e (2 * π * (ξ.1 - ζ.1) *
σ)).re + π * ((if ξ.2 = -ζ.2 then A * B else 0) * e (2 * π * (ξ.1 + ζ.1) *
σ)).re`. The proof writes the product of real parts as half the sum of the real parts of two
exponentials, with frequencies `ξ.2 - ζ.2` and `ξ.2 + ζ.2` in `θ`, and integrates each over the full
period. -/
theorem integral_re_exp_mul_re_exp (ξ ζ : ℤ × ℤ) (A B : ℂ) (σ : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (Complex.exp (((2 * Real.pi * ξ.1 * σ + ξ.2 * θ : ℝ) : ℂ) * Complex.I) * A).re *
        (Complex.exp (((2 * Real.pi * ζ.1 * σ + ζ.2 * θ : ℝ) : ℂ) * Complex.I) * B).re =
      Real.pi * ((if ξ.2 = ζ.2 then A * starRingEnd ℂ B else 0) *
          Complex.exp (((2 * Real.pi * ((ξ.1 - ζ.1 : ℤ) : ℝ) * σ : ℝ) : ℂ) * Complex.I)).re +
        Real.pi * ((if ξ.2 = -ζ.2 then A * B else 0) *
          Complex.exp (((2 * Real.pi * ((ξ.1 + ζ.1 : ℤ) : ℝ) * σ : ℝ) : ℂ) * Complex.I)).re := by
  have hpt : ∀ θ : ℝ,
      (Complex.exp (((2 * Real.pi * ξ.1 * σ + ξ.2 * θ : ℝ) : ℂ) * Complex.I) * A).re *
        (Complex.exp (((2 * Real.pi * ζ.1 * σ + ζ.2 * θ : ℝ) : ℂ) * Complex.I) * B).re =
      (A * starRingEnd ℂ B *
          Complex.exp (((2 * Real.pi * ((ξ.1 - ζ.1 : ℤ) : ℝ) * σ : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((((ξ.2 - ζ.2 : ℤ) : ℝ) * θ : ℝ) : ℂ) * Complex.I)).re / 2 +
      (A * B *
          Complex.exp (((2 * Real.pi * ((ξ.1 + ζ.1 : ℤ) : ℝ) * σ : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((((ξ.2 + ζ.2 : ℤ) : ℝ) * θ : ℝ) : ℂ) * Complex.I)).re / 2 := by
    intro θ
    rw [re_mul_re_eq, exp_mul_mul_conj_exp_mul, exp_mul_mul_exp_mul]
    have e1 : (2 * Real.pi * ξ.1 * σ + ξ.2 * θ) - (2 * Real.pi * ζ.1 * σ + ζ.2 * θ) =
        2 * Real.pi * ((ξ.1 - ζ.1 : ℤ) : ℝ) * σ + ((ξ.2 - ζ.2 : ℤ) : ℝ) * θ := by
      push_cast
      ring
    have e2 : (2 * Real.pi * ξ.1 * σ + ξ.2 * θ) + (2 * Real.pi * ζ.1 * σ + ζ.2 * θ) =
        2 * Real.pi * ((ξ.1 + ζ.1 : ℤ) : ℝ) * σ + ((ξ.2 + ζ.2 : ℤ) : ℝ) * θ := by
      push_cast
      ring
    rw [e1, e2, exp_ofReal_add_mul_I, exp_ofReal_add_mul_I, ← mul_assoc, ← mul_assoc]
  simp_rw [hpt]
  have hint : ∀ (c : ℂ) (ω : ℝ), IntervalIntegrable
      (fun θ : ℝ ↦ (c * Complex.exp (((ω * θ : ℝ) : ℂ) * Complex.I)).re / 2) volume 0
          (2 * Real.pi) :=
    fun c ω ↦ (by fun_prop : Continuous fun θ : ℝ ↦
      (c * Complex.exp (((ω * θ : ℝ) : ℂ) * Complex.I)).re / 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hint _ _) (hint _ _), intervalIntegral.integral_div,
    intervalIntegral.integral_div,
    integral_re_exp_full_period _ _ (ξ.2 - ζ.2) (by ring),
    integral_re_exp_full_period _ _ (ξ.2 + ζ.2) (by ring)]
  have c1 : (((ξ.2 - ζ.2 : ℤ) : ℝ) = 0) ↔ ξ.2 = ζ.2 := by
    rw [Int.cast_eq_zero, sub_eq_zero]
  have c2 : (((ξ.2 + ζ.2 : ℤ) : ℝ) = 0) ↔ ξ.2 = -ζ.2 := by
    rw [Int.cast_eq_zero, eq_neg_iff_add_eq_zero]
  simp only [c1, c2]
  split_ifs <;> simp <;> ring

/-- For a complex `c` and an integer `a`, the function
`fun τ : ℝ ↦ c * Complex.exp (((2 * π * (a : ℝ) * τ : ℝ) : ℂ) * Complex.I)` is interval integrable
on `0..1`. -/
theorem intervalIntegrable_const_mul_exp_two_pi_int (c : ℂ) (a : ℤ) :
    IntervalIntegrable (fun τ : ℝ ↦ c * Complex.exp (((2 * Real.pi * (a : ℝ) * τ : ℝ) : ℂ) *
        Complex.I))
      volume 0 1 :=
  (continuous_const.mul (continuous_cexp_two_pi_int_mul_I a)).intervalIntegrable _ _

/-- For an integer `b`, `∫ φ in 0..(2 * π), Complex.exp ((((b : ℝ) * φ : ℝ) : ℂ) * Complex.I)`
equals `((2 * π : ℝ) : ℂ)` if `b = 0` and `0` otherwise. This is `integral_exp_int_mul_mul_I` with
the value `2 * π` written as the cast of a real number. -/
theorem intervalIntegral_exp_int_mul_I_eq_ite (b : ℤ) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), Complex.exp ((((b : ℝ) * φ : ℝ) : ℂ) * Complex.I) =
      if b = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  simpa using integral_exp_int_mul_mul_I b

/-- Let `f : ℝ → β` be periodic with period `1` (`Function.Periodic f 1`). If the real numbers `r`
and `σ` have the same image in `UnitAddCircle`, the additive circle of period `1`, then `f r = f σ`.
-/
theorem periodic_apply_eq_of_coe_eq {β : Type*} {f : ℝ → β} (hf : Function.Periodic f 1) {r σ : ℝ}
    (h : (r : UnitAddCircle) = σ) : f r = f σ := by
  have h0 : ((r - σ : ℝ) : UnitAddCircle) = 0 := by rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff 1).1 h0
  have hr : r = σ + n • (1 : ℝ) := by rw [hn]; ring
  rw [hr]
  exact hf.zsmul n σ

/-- Parseval's identity on an interval, in extended nonnegative reals: for `a < b` and `f : ℝ → ℂ`
with `MemLp f 2 (volume.restrict (Icc a b))`,
`∑' i : ℤ, ENNReal.ofReal (‖fourierCoeffOn hab f i‖ ^ 2) = ENNReal.ofReal ((b - a)⁻¹) * ∫⁻ x in Icc
a b, ENNReal.ofReal (‖f x‖ ^ 2)`. The proof takes `hasSum_sq_fourierCoeffOn`, replaces `Ioc a
b` by `Icc a b`, and turns the Bochner integral into a lower integral. -/
theorem tsum_ofReal_sq_norm_fourierCoeffOn {a b : ℝ} (hab : a < b) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Icc a b))) :
    ∑' i : ℤ, ENNReal.ofReal (‖fourierCoeffOn hab f i‖ ^ 2) =
      ENNReal.ofReal ((b - a)⁻¹) * ∫⁻ x in Icc a b, ENNReal.ofReal (‖f x‖ ^ 2) := by
  have hres : volume.restrict (Ioc a b) = volume.restrict (Icc a b) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc
  have hf' : MemLp f 2 (volume.restrict (Ioc a b)) := by rw [hres]; exact hf
  have hs := hasSum_sq_fourierCoeffOn hab hf'
  have hint : Integrable (fun x ↦ ‖f x‖ ^ 2) (volume.restrict (Icc a b)) :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ by positivity) hs.summable, hs.tsum_eq,
    intervalIntegral.integral_of_le hab.le, hres, smul_eq_mul,
    ENNReal.ofReal_mul (inv_nonneg.2 (sub_nonneg.2 hab.le)),
    ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun x ↦ by positivity))]

/-- Subtracting a constant from a function on the circle changes only the zeroth Fourier
coefficient: for `0 < T`, `f : AddCircle T → ℂ` integrable for the Haar measure, `c : ℂ` and
`n : ℤ`, `fourierCoeff (fun t ↦ f t - c) n = fourierCoeff f n - (if n = 0 then c else 0)`. The
proof splits the integral that defines the coefficient and uses that `fourier (-n)` has integral `1`
if `n = 0` and `0` otherwise. -/
theorem fourierCoeff_sub_const {T : ℝ} [hT : Fact (0 < T)] (f : AddCircle T → ℂ)
    (hf : Integrable f AddCircle.haarAddCircle) (c : ℂ) (n : ℤ) :
    fourierCoeff (fun t ↦ f t - c) n = fourierCoeff f n - (if n = 0 then c else 0) := by
  have hi1 : Integrable (fun t ↦ fourier (-n) t • f t) AddCircle.haarAddCircle := by
    refine hf.norm.mono' ((fourier (T := T) (-n)).continuous.aestronglyMeasurable.smul hf.1)
        (ae_of_all _ fun t ↦ ?_)
    simp [Circle.norm_coe]
  have hi2 : Integrable (fun t : AddCircle T ↦ fourier (-n) t • c) AddCircle.haarAddCircle := by
    refine Integrable.of_bound ((fourier (T := T) (-n)).continuous.aestronglyMeasurable.smul
        aestronglyMeasurable_const)
      ‖c‖ (ae_of_all _ fun t ↦ ?_)
    simp [Circle.norm_coe]
  unfold fourierCoeff
  simp_rw [smul_sub]
  rw [integral_sub hi1 hi2, integral_smul_const, integral_fourier_neg_haarAddCircle]
  split_ifs <;> simp

/-- Parseval's identity for a pair on the circle `AddCircle T` (`0 < T`, Haar probability measure):
for `X` in `Lp ℂ 2` and `Z : AddCircle T → ℂ` with `MemLp Z 2`, the family
`j ↦ conj (fourierCoeff X j) * fourierCoeff Z j` over `ℤ` has sum
`∫ t, conj (X t) * Z t ∂haarAddCircle`. The proof expands the `L²` inner product of `X` and `Z` in
the Fourier Hilbert basis. -/
theorem hasSum_conj_mul_fourierCoeff {T : ℝ} [hT : Fact (0 < T)]
    (X : Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) (Z : AddCircle T → ℂ)
    (hZ : MemLp Z 2 AddCircle.haarAddCircle) :
    HasSum (fun j : ℤ ↦ conj (fourierCoeff X j) * fourierCoeff Z j)
      (∫ t, conj (X t) * Z t ∂AddCircle.haarAddCircle) := by
  have H := fourierBasis.hasSum_inner_mul_inner X hZ.toLp
  have e1 : ∀ j : ℤ, inner ℂ X (fourierBasis j) = conj (fourierCoeff X j) := by
    intro j; rw [← inner_conj_symm, inner_fourierBasis_eq_fourierCoeff]
  have e2 : ∀ j : ℤ, inner ℂ (fourierBasis j) hZ.toLp = fourierCoeff Z j := by
    intro j; rw [inner_fourierBasis_eq_fourierCoeff, fourierCoeff_congr_ae hZ.coeFn_toLp]
  have e3 : inner ℂ X hZ.toLp = ∫ t, conj (X t) * Z t ∂AddCircle.haarAddCircle := by
    rw [inner_haarAddCircle_eq_integral_conj_mul]
    refine integral_congr_ae ?_
    filter_upwards [hZ.coeFn_toLp] with t ht
    rw [ht]
  simp only [e1, e2, e3] at H
  exact H

/-- The Fourier coefficients of a product on the circle `AddCircle T` (`0 < T`) are a convolution:
if `F : AddCircle T → ℂ` is almost everywhere strongly measurable with `‖F t‖ ≤ C` for all `t` and
`Y` is in `Lp ℂ 2` of the Haar measure, then for every `j : ℤ` the family
`i ↦ fourierCoeff F (j - i) * fourierCoeff Y i` over `ℤ` has sum
`fourierCoeff (fun t ↦ F t * Y t) j`. The proof applies `HilbertBasis.hasSum_inner_mul_inner` for
the Fourier basis to the `L²` functions `t ↦ conj (F t) * fourier j t` and `Y`. -/
theorem hasSum_fourierCoeff_mul_of_bounded {T : ℝ} [hT : Fact (0 < T)] (F : AddCircle T → ℂ)
    (hF : AEStronglyMeasurable F AddCircle.haarAddCircle)
    (C : ℝ) (hC : ∀ t, ‖F t‖ ≤ C) (Y : Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) (j : ℤ) :
    HasSum (fun i : ℤ ↦ fourierCoeff F (j - i) * fourierCoeff Y i)
      (fourierCoeff (fun t ↦ F t * Y t) j) := by
  have hV : MemLp (fun t ↦ conj (F t) * fourier j t) 2 (AddCircle.haarAddCircle (T := T)) := by
    refine MemLp.of_bound (hF.star.mul (fourier j).continuous.aestronglyMeasurable) C
      (ae_of_all _ fun t ↦ ?_)
    rw [norm_mul, RCLike.norm_conj]
    have h1 : ‖fourier j t‖ = 1 := by
      rw [fourier_apply]; exact Circle.norm_coe _
    rw [h1, mul_one]
    exact hC t
  have H := fourierBasis.hasSum_inner_mul_inner hV.toLp Y
  have e1 : ∀ i : ℤ, inner ℂ hV.toLp (fourierBasis i) = fourierCoeff F (j - i) := by
    intro i
    rw [← inner_conj_symm, inner_fourierBasis_eq_fourierCoeff, fourierCoeff_congr_ae hV.coeFn_toLp,
        fourierCoeff, fourierCoeff,
      ← integral_conj]
    refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
    simp only [smul_eq_mul]
    rw [show -(j - i) = i + -j by ring, fourier_add, fourier_neg, fourier_neg]
    simp only [map_mul, RCLike.conj_conj]
    ring
  have e2 : inner ℂ hV.toLp Y = fourierCoeff (fun t ↦ F t * Y t) j := by
    rw [inner_haarAddCircle_eq_integral_conj_mul, fourierCoeff]
    refine integral_congr_ae ?_
    filter_upwards [hV.coeFn_toLp] with t ht
    rw [ht, smul_eq_mul, fourier_neg]
    simp only [map_mul, RCLike.conj_conj]
    ring
  simp only [e1, inner_fourierBasis_eq_fourierCoeff, e2] at H
  exact H

/-- Write `e x` for `Complex.exp ((x : ℂ) * Complex.I)` with `x` real. For `ξ ζ : ℤ × ℤ` and
`A B : ℂ`, `∫ σ in Icc 0 1, ∫ θ in 0..2 * π, (e (2 * π * ξ.1 * σ + ξ.2 * θ) * A).re * (e (2 * π *
ζ.1 * σ + ζ.2 * θ) * B).re = π * ((if ξ = ζ then A * (starRingEnd ℂ) B else 0) + (if ξ = -ζ then A *
B else 0)).re`. The proof evaluates the inner integral over `θ` and then integrates the remaining
exponentials in `σ` over the full period `0..1`. -/
theorem integral_integral_re_exp_mul_re_exp (ξ ζ : ℤ × ℤ) (A B : ℂ) :
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (Complex.exp (((2 * Real.pi * ξ.1 * σ + ξ.2 * θ : ℝ) : ℂ) * Complex.I) * A).re *
        (Complex.exp (((2 * Real.pi * ζ.1 * σ + ζ.2 * θ : ℝ) : ℂ) * Complex.I) * B).re =
      Real.pi * ((if ξ = ζ then A * starRingEnd ℂ B else 0) + (if ξ = -ζ then A * B else 0)).re :=
          by
  simp_rw [integral_re_exp_mul_re_exp ξ ζ A B]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have hint : ∀ (c : ℂ) (ω : ℝ), IntervalIntegrable
      (fun σ : ℝ ↦ Real.pi * (c * Complex.exp (((ω * σ : ℝ) : ℂ) * Complex.I)).re) volume 0 1 :=
    fun c ω ↦ (by fun_prop : Continuous fun σ : ℝ ↦
      Real.pi * (c * Complex.exp (((ω * σ : ℝ) : ℂ) * Complex.I)).re).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hint _ _) (hint _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_re_exp_full_period _ _ (ξ.1 - ζ.1) (by ring),
    integral_re_exp_full_period _ _ (ξ.1 + ζ.1) (by ring)]
  exact re_ite_fst_ite_snd_add_eq ξ ζ A B

/-- Parseval's identity for a finite exponential sum on the unit interval: if `f : Fin N → ℤ` is
injective on the finite set `S`, then for all `c : Fin N → ℂ`,
`∫ σ in 0..1, ‖∑ p ∈ S, exp (2 * π * f p * σ * I) * c p‖ ^ 2 = ∑ p ∈ S, ‖c p‖ ^ 2`, stated as an
equality of complex numbers with both real sides cast to `ℂ`. The proof expands the square into a
double sum and uses that `∫ σ in 0..1, exp (2 * π * n * σ * I)` is `1` for `n = 0` and `0` for other
integers `n`. -/
theorem integral_sq_norm_sum_exp_mul {N : ℕ} (f : Fin N → ℤ) (S : Finset (Fin N))
    (hf : Set.InjOn f S)
    (c : Fin N → ℂ) :
    ∫ σ in (0 : ℝ)..1,
        (((‖∑ p ∈ S, Complex.exp (2 * (Real.pi : ℂ) * (f p : ℂ) * (σ : ℂ) * Complex.I) *
            c p‖ ^ 2 : ℝ)) : ℂ) =
      (((∑ p ∈ S, ‖c p‖ ^ 2 : ℝ)) : ℂ) := by
  have hexp : ∀ σ : ℝ,
      (((‖∑ p ∈ S, Complex.exp (2 * (Real.pi : ℂ) * (f p : ℂ) * (σ : ℂ) * Complex.I) *
          c p‖ ^ 2 : ℝ)) : ℂ) =
        ∑ p ∈ S, ∑ q ∈ S, c p * (starRingEnd ℂ) (c q) *
          Complex.exp (2 * (Real.pi : ℂ) * (((f p - f q : ℤ)) : ℂ) * (σ : ℂ) * Complex.I) := by
    intro σ
    rw [sq_norm_eq_mul_conj, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun p _ ↦ Finset.sum_congr rfl (fun q _ ↦ ?_))
    exact exp_mul_mul_conj_exp_mul_eq (f p) (f q) σ (c p) (c q)
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum]
  · have hin : ∀ p ∈ S, (∫ σ in (0 : ℝ)..1, ∑ q ∈ S, c p * (starRingEnd ℂ) (c q) *
          Complex.exp (2 * (Real.pi : ℂ) * (((f p - f q : ℤ)) : ℂ) * (σ : ℂ) * Complex.I)) =
        (((‖c p‖ ^ 2 : ℝ)) : ℂ) := by
      intro p hp
      rw [intervalIntegral.integral_finsetSum]
      · simp_rw [intervalIntegral.integral_const_mul, integral_exp_two_pi_int_mul_I]
        have hiff : ∀ q ∈ S, (f p - f q = 0 ↔ p = q) := by
          intro q hq
          rw [sub_eq_zero]
          exact ⟨fun h ↦ hf hp hq h, fun h ↦ h ▸ rfl⟩
        rw [Finset.sum_congr rfl (fun q hq ↦ by rw [if_congr (hiff q hq) rfl rfl])]
        simp only [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq S p, ite_eq_left hp, sq_norm_eq_mul_conj]
      · intro q _
        exact (by fun_prop : Continuous fun σ : ℝ ↦ c p * (starRingEnd ℂ) (c q) *
          Complex.exp (2 * (Real.pi : ℂ) * (((f p - f q : ℤ)) : ℂ) * (σ : ℂ) *
              Complex.I)).intervalIntegrable _ _
    rw [Finset.sum_congr rfl hin]
    push_cast
    rfl
  · intro p _
    exact (by fun_prop : Continuous fun σ : ℝ ↦ ∑ q ∈ S, c p * (starRingEnd ℂ) (c q) *
      Complex.exp (2 * (Real.pi : ℂ) * (((f p - f q : ℤ)) : ℂ) * (σ : ℂ) *
          Complex.I)).intervalIntegrable _ _

/-- For a complex `c`, integers `m`, `l` and a real `τ`,
`∫ φ in 0..(2 * π), c * Complex.exp (((2 * π * (m : ℝ) * τ + (l : ℝ) * φ : ℝ) : ℂ) * Complex.I) =
(c * if l = 0 then (2 * π : ℂ) else 0) * Complex.exp (((2 * π * (m : ℝ) * τ : ℝ) : ℂ) *
Complex.I)`. The proof factors out the part of the exponential that does not depend on `φ` and
integrates `Complex.exp ((((l : ℝ) * φ : ℝ) : ℂ) * Complex.I)` over one period. -/
theorem intervalIntegral_const_mul_exp_add_int_mul (c : ℂ) (m l : ℤ) (τ : ℝ) :
    (∫ φ in (0 : ℝ)..(2 * Real.pi),
        c * Complex.exp (((2 * Real.pi * (m : ℝ) * τ + (l : ℝ) * φ : ℝ) : ℂ) * Complex.I)) =
      (c * if l = 0 then (2 * Real.pi : ℂ) else 0) *
        Complex.exp (((2 * Real.pi * (m : ℝ) * τ : ℝ) : ℂ) * Complex.I) := by
  have hrw : ∀ φ : ℝ,
      c * Complex.exp (((2 * Real.pi * (m : ℝ) * τ + (l : ℝ) * φ : ℝ) : ℂ) * Complex.I) =
        (c * Complex.exp (((2 * Real.pi * (m : ℝ) * τ : ℝ) : ℂ) * Complex.I)) *
          Complex.exp ((((l : ℝ) * φ : ℝ) : ℂ) * Complex.I) := by
    intro φ
    rw [mul_assoc c, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [hrw]
  rw [intervalIntegral.integral_const_mul, integral_exp_int_mul_mul_I]
  ring

/-- For a complex `c` and an integer `m`,
`∫ τ in 0..1, c * Complex.exp (((2 * π * (m : ℝ) * τ : ℝ) : ℂ) * Complex.I)` equals `c` if `m = 0`
and `0` otherwise. -/
theorem intervalIntegral_const_mul_exp_two_pi_int (c : ℂ) (m : ℤ) :
    (∫ τ in (0 : ℝ)..1, c * Complex.exp (((2 * Real.pi * (m : ℝ) * τ : ℝ) : ℂ) * Complex.I)) =
      if m = 0 then c else 0 := by
  rw [intervalIntegral.integral_const_mul, integral_exp_two_pi_mul_int_mul_mul_I]
  split_ifs <;> simp

/-- Let `t` be a finset of indices, `m`, `l`, `m'`, `l'` integer-valued and `c`, `d` complex-valued
functions of the index. Then
`∫ τ in 0..1, ∫ φ in 0..(2 * π), ∑ j ∈ t, (c j * Complex.exp (((2 * π * (m j : ℝ) * τ + (l j : ℝ) *
φ : ℝ) : ℂ) * Complex.I) + d j * Complex.exp (((2 * π * (m' j : ℝ) * τ + (l' j : ℝ) * φ : ℝ) : ℂ) *
Complex.I))` equals `∑ j ∈ t, ((if m j = 0 then c j * (if l j = 0 then (2 * π : ℂ) else 0) else 0) +
(if m' j = 0 then d j * (if l' j = 0 then (2 * π : ℂ) else 0) else
0))`. The proof exchanges the finite sum with both integrals and integrates each exponential over a
full period, first in `φ` and then in `τ`. -/
theorem intervalIntegral_integral_sum_exp_eq_sum_ite {α : Type*} (t : Finset α) (m l m' l' : α → ℤ)
    (c d : α → ℂ) :
    (∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
        ∑ j ∈ t, (c j * Complex.exp
            (((2 * Real.pi * (m j : ℝ) * τ + (l j : ℝ) * φ : ℝ) : ℂ) * Complex.I) +
          d j * Complex.exp
            (((2 * Real.pi * (m' j : ℝ) * τ + (l' j : ℝ) * φ : ℝ) : ℂ) * Complex.I))) =
      ∑ j ∈ t, ((if m j = 0 then c j * (if l j = 0 then (2 * Real.pi : ℂ) else 0) else 0) +
        (if m' j = 0 then d j * (if l' j = 0 then (2 * Real.pi : ℂ) else 0) else 0)) := by
  have hinner : ∀ τ : ℝ, (∫ φ in (0 : ℝ)..(2 * Real.pi),
        ∑ j ∈ t, (c j * Complex.exp
            (((2 * Real.pi * (m j : ℝ) * τ + (l j : ℝ) * φ : ℝ) : ℂ) * Complex.I) +
          d j * Complex.exp
            (((2 * Real.pi * (m' j : ℝ) * τ + (l' j : ℝ) * φ : ℝ) : ℂ) * Complex.I))) =
      ∑ j ∈ t, ((c j * if l j = 0 then (2 * Real.pi : ℂ) else 0) *
          Complex.exp (((2 * Real.pi * (m j : ℝ) * τ : ℝ) : ℂ) * Complex.I) +
        (d j * if l' j = 0 then (2 * Real.pi : ℂ) else 0) *
          Complex.exp (((2 * Real.pi * (m' j : ℝ) * τ : ℝ) : ℂ) * Complex.I)) := by
    intro τ
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [intervalIntegral.integral_add, intervalIntegral_const_mul_exp_add_int_mul,
          intervalIntegral_const_mul_exp_add_int_mul]
      · exact (by fun_prop : Continuous fun φ : ℝ ↦ c j * Complex.exp
          (((2 * Real.pi * (m j : ℝ) * τ + (l j : ℝ) * φ : ℝ) : ℂ) * Complex.I)).intervalIntegrable
              _ _
      · exact (by fun_prop : Continuous fun φ : ℝ ↦ d j * Complex.exp
          (((2 * Real.pi * (m' j : ℝ) * τ + (l' j : ℝ) * φ : ℝ) : ℂ) *
              Complex.I)).intervalIntegrable _ _
    · intro j _
      exact (by fun_prop : Continuous fun φ : ℝ ↦ c j * Complex.exp
          (((2 * Real.pi * (m j : ℝ) * τ + (l j : ℝ) * φ : ℝ) : ℂ) * Complex.I) +
          d j * Complex.exp
          (((2 * Real.pi * (m' j : ℝ) * τ + (l' j : ℝ) * φ : ℝ) : ℂ) *
              Complex.I)).intervalIntegrable _ _
  simp only [hinner]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [intervalIntegral.integral_add, intervalIntegral_const_mul_exp_two_pi_int,
        intervalIntegral_const_mul_exp_two_pi_int]
    · exact (by
        fun_prop : Continuous fun τ : ℝ ↦ (c j * if l j = 0 then (2 * Real.pi : ℂ) else 0) *
          Complex.exp (((2 * Real.pi * (m j : ℝ) * τ : ℝ) : ℂ) * Complex.I)).intervalIntegrable _ _
    · exact (by
        fun_prop : Continuous fun τ : ℝ ↦ (d j * if l' j = 0 then (2 * Real.pi : ℂ) else 0) *
          Complex.exp (((2 * Real.pi * (m' j : ℝ) * τ : ℝ) : ℂ) * Complex.I)).intervalIntegrable _ _
  · intro j _
    exact (by fun_prop : Continuous fun τ : ℝ ↦ (c j * if l j = 0 then (2 * Real.pi : ℂ) else 0) *
          Complex.exp (((2 * Real.pi * (m j : ℝ) * τ : ℝ) : ℂ) * Complex.I) +
        (d j * if l' j = 0 then (2 * Real.pi : ℂ) else 0) *
          Complex.exp (((2 * Real.pi * (m' j : ℝ) * τ : ℝ) : ℂ) * Complex.I)).intervalIntegrable _ _

/-- Weighted Parseval identity for a finite exponential sum, as a lower integral: if `f : Fin N → ℤ`
is injective on the finite set `S` and `0 ≤ w`, then for all `c : Fin N → ℂ`,
`∫⁻ σ in Icc 0 1, ENNReal.ofReal (w * ‖∑ p ∈ S, exp (2 * π * f p * σ * I) * c p‖ ^ 2) =
ENNReal.ofReal (w * ∑ p ∈ S, ‖c p‖ ^
2)`. The proof turns the lower integral of the continuous nonnegative integrand into a Bochner
integral and uses the same identity for the interval integral. -/
theorem lintegral_ofReal_mul_sq_norm_sum_exp {N : ℕ} (f : Fin N → ℤ) (S : Finset (Fin N))
    (hf : Set.InjOn f S)
    (c : Fin N → ℂ) (w : ℝ) (hw : 0 ≤ w) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (w *
        ‖∑ p ∈ S, Complex.exp (2 * (Real.pi : ℂ) * (f p : ℂ) * (σ : ℂ) * Complex.I) * c p‖ ^ 2) =
      ENNReal.ofReal (w * ∑ p ∈ S, ‖c p‖ ^ 2) := by
  have hcont : Continuous fun σ : ℝ ↦ w *
      ‖∑ p ∈ S, Complex.exp (2 * (Real.pi : ℂ) * (f p : ℂ) * (σ : ℂ) * Complex.I) * c p‖ ^ 2 := by
    fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)
    (Filter.Eventually.of_forall (fun σ ↦ by positivity))]
  congr 1
  rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one]
  congr 1
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  exact integral_sq_norm_sum_exp_mul f S hf c

end PDE.Analysis
