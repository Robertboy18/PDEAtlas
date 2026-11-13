/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.Core
public import PDE.Spaces.Sobolev.Extension.Representative.Basic
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Algebra.Order.Ring.Star
import PDE.Analysis.Normed.Operator.FiniteProduct
import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation
import CAS.ExactTactic
import PDE.FDeriv.PartialDeriv.Energy
import Mathlib.Analysis.InnerProductSpace.NormPow

/-!
# The Gagliardo–Nirenberg–Sobolev inequality in `W^{1,p}`

Mathlib has the Gagliardo–Nirenberg–Sobolev inequality, `eLpNorm_le_eLpNorm_fderiv_of_eq`, for `C¹`
compactly supported functions with the derivative measured as `‖fderiv u‖`. We put it into the
`ℝ^n`/`volume` conventions of this library and carry it from `C¹_c` to `W^{1,p}`.

The canonical coordinate equivalence preserves Lebesgue measure. In dimensions
`n ≥ 2`, it gives the explicit endpoint estimate `‖u‖_{n/(n-1)} ≤ Σᵢ ‖∂ᵢu‖₁` for compactly supported
`C¹` functions with any real normed target. Unlike the basis-free embedding
constant, this bound contains no chosen change of basis. Lifting a supplied
scalar endpoint bound through the norm-power and Hölder argument gives the
explicit subcritical constant `np(n-1)/(n-p)` for `1 < p < n`, with any real
inner product target. In dimension three at `p = 2` this constant is twelve.

Evans, PDE, §5.6.1, proves the inequality for `C¹_c(ℝ^n)` (Theorem 1) and passes to a bounded
`C¹` domain through the extension of §5.4 and approximation (Theorem 2).
`memLp_pStar_of_sobolevSpaceOn_of_extension` assumes `HasExtension` instead of a `C¹`
boundary, and `Bornology.IsBounded Ω` enters only for the exponents below `p*`.

## Main results

* `pStar`, `pStarPreimage`: the Sobolev conjugate `p* = np/(n-p)` and its inverse `nq/(n+q)` as
  totalized `NNReal` functions, with `1/p* = 1/p - 1/n` and `pStar (pStarPreimage q) = q`.
* `eLpNorm_le_eLpNorm_fderiv_pStar`: the Gagliardo–Nirenberg–Sobolev inequality
  `‖u‖_{p*} ≤ C ‖Du‖_p` for `u ∈ C¹_c(ℝ^n)` and `1 ≤ p < n`, from Mathlib.
* `eLpNorm_le_sum_eLpNorm_partialDeriv_of_eq`, `eLpNorm_le_sum_eLpNorm_partialDeriv_of_le`: the
  same with `‖Du‖_p` replaced by the sum of the coordinate partial derivatives, at the endpoint
  exponent and, for functions supported in a bounded set, at every exponent `q ≤ p*`.
* `memLp_pStar_of_sobolevSpace`: `W^{1,p}(ℝ^n) ⊂ L^{p*}(ℝ^n)`, by density.
* `memLp_pStar_of_sobolevSpaceOn_of_extension`, `memLp_of_le_pStar_of_sobolevSpaceOn_of_extension`:
  `W^{1,p}(Ω) ⊂ L^{p*}(Ω)` whenever `Ω` admits a `W^{1,p}` extension operator, and `⊂ L^q(Ω)` for
  all `q ≤ p*` when `Ω` is in addition bounded.

## How it works

Mathlib's inequality needs two additions. We rewrite the right-hand side as a sum of coordinate
partial derivatives (`eLpNorm_fderiv_le_sum_eLpNorm_partialDeriv`, from the elementary bound
`‖L‖ ≤ Σᵢ ‖L eᵢ‖`), since that is how weak derivatives are stored here. We then pass to
`W^{1,p}(ℝ^n)` by hand in `memLp_pStar_of_sobolevSpace`: `globalApproximation_Wkp` gives smooth
approximants, the `C¹_c` inequality bounds their `L^{p*}` norms, and Fatou's lemma places the same
base function in `L^{p*}`, which gives `MemLp` membership of the representative.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.1, Theorem 1, (10), p. 277, for `u ∈ C¹_c(ℝ^n)`, and
  Theorem 2, (15), p. 279, for a bounded `C¹` domain, proved with the extension of §5.4, Theorem 1,
  pp. 268-271, and approximation (16)-(18).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open scoped Topology


namespace Inequalities

section GNS

variable {n : ℕ}

/-!
### The Sobolev conjugate exponent `p*`

In Evans §5.6, for `1 ≤ p < n` one sets `p* := np/(n-p)` so that `1/p* = 1/p - 1/n`.
We record that algebra once, so the inverse identity need not be carried as a hypothesis.
-/

/-- Totalized Sobolev-conjugate expression `p* = np/(n-p)` (as an `NNReal`).

Analytically this is the Evans exponent under the hypotheses `0 < p < n`.  Outside that range this
definition is just Lean's total `Real.toNNReal` packaging, and the theorems below carry the needed
hypotheses explicitly. -/
noncomputable def pStar (n : ℕ) (p : NNReal) : NNReal :=
  Real.toNNReal ((p : ℝ) * (n : ℝ) / ((n : ℝ) - p))

/-- For `p < n` the totalization is inactive: `p*` is literally `np/(n-p)` as a real number. -/
theorem pStar_coe (hn : 0 < n) {p : NNReal} (hp : (p : ℝ) < (n : ℝ)) :
    ((pStar n p : NNReal) : ℝ) = (p : ℝ) * (n : ℝ) / ((n : ℝ) - p) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) - p := sub_pos.2 hp
  have hnonneg : 0 ≤ (p : ℝ) * (n : ℝ) / ((n : ℝ) - p) := by
    have hnum : 0 ≤ (p : ℝ) * (n : ℝ) := mul_nonneg p.2 hn0.le
    exact div_nonneg hnum hden.le
  simpa [pStar] using
    (Real.coe_toNNReal ((p : ℝ) * (n : ℝ) / ((n : ℝ) - p)) hnonneg)

/-- The defining relation of the Sobolev conjugate: `1/p* = 1/p - 1/n` for `0 < p < n`. -/
theorem inv_pStar_eq (hn : 0 < n) {p : NNReal} (hp0 : (0 : ℝ) < p) (hp : (p : ℝ) < (n : ℝ)) :
    (((pStar n p : NNReal) : ℝ)⁻¹) = (p : ℝ)⁻¹ - (n : ℝ)⁻¹ := by
  rw [pStar_coe hn hp]
  cas

/-- The Sobolev conjugate is at least `p` when `p < n`, since `p* = pn/(n-p)` and `n - p ≤ n`. -/
theorem le_pStar (hn : 0 < n) {p : NNReal} (hp : (p : ℝ) < (n : ℝ)) :
    p ≤ pStar n p := by
  have hden : 0 < (n : ℝ) - p := sub_pos.2 hp
  have hnp : (n : ℝ) - p ≤ (n : ℝ) := sub_le_self _ (show 0 ≤ (p : ℝ) from p.2)
  have hmul : (p : ℝ) * ((n : ℝ) - p) ≤ (p : ℝ) * (n : ℝ) :=
    mul_le_mul_of_nonneg_left hnp (show 0 ≤ (p : ℝ) from p.2)
  have hreal : (p : ℝ) ≤ (p : ℝ) * (n : ℝ) / ((n : ℝ) - p) :=
    (le_div_iff₀ hden).2 (by simpa [mul_assoc] using hmul)
  have hpStarR :
      ((pStar n p : NNReal) : ℝ) = (p : ℝ) * (n : ℝ) / ((n : ℝ) - p) :=
    pStar_coe (n := n) (p := p) hn hp
  have : (p : ℝ) ≤ ((pStar n p : NNReal) : ℝ) := by simpa [hpStarR] using hreal
  exact_mod_cast this

/-- For `1 ≤ p < n` the Sobolev conjugate is again at least `1`, so `L^{p*}` is a Banach space. -/
theorem one_le_pStar (hn : 0 < n) {p : NNReal} (hp : (1 : NNReal) ≤ p) (hp' : (p : ℝ) < (n : ℝ)) :
    (1 : NNReal) ≤ pStar n p :=
  le_trans hp (le_pStar (n := n) hn hp')

/-- Totalized inverse of the Sobolev-conjugate exponent map:
`pStarPreimage n q = nq / (n + q)`.

For positive `n` and `q`, this is the unique positive exponent `s < n`
satisfying `1 / q = 1 / s - 1 / n`. -/
noncomputable def pStarPreimage (n : ℕ) (q : NNReal) : NNReal :=
  Real.toNNReal ((n : ℝ) * (q : ℝ) / ((n : ℝ) + q))

/-- Real-valued formula for the preimage of a Sobolev-conjugate exponent. -/
theorem pStarPreimage_coe
    {n : ℕ} {q : NNReal} (hn : 0 < n) (hq : 0 < (q : ℝ)) :
    ((pStarPreimage n q : NNReal) : ℝ) =
      (n : ℝ) * (q : ℝ) / ((n : ℝ) + q) := by
  have hnonneg :
      0 ≤ (n : ℝ) * (q : ℝ) / ((n : ℝ) + q) := by
    positivity
  simpa [pStarPreimage] using
    Real.coe_toNNReal
      ((n : ℝ) * (q : ℝ) / ((n : ℝ) + q)) hnonneg

/-- The preimage of a positive Sobolev-conjugate exponent is subcritical. -/
theorem pStarPreimage_lt_dimension
    {n : ℕ} {q : NNReal} (hn : 0 < n) (hq : 0 < (q : ℝ)) :
    ((pStarPreimage n q : NNReal) : ℝ) < n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) + q := add_pos hnR hq
  rw [pStarPreimage_coe hn hq, div_lt_iff₀ hden]
  nlinarith

/-- If `2 ≤ n < q`, then the preimage of `q` under `pStar n` is at least one. -/
theorem one_le_pStarPreimage
    {n : ℕ} {q : NNReal} (hn2 : 2 ≤ n)
    (hq : (n : ℝ) < q) :
    (1 : NNReal) ≤ pStarPreimage n q := by
  have hn : 0 < n := lt_of_lt_of_le (by omega) hn2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 : 0 < (q : ℝ) := lt_trans hnR hq
  have hden : 0 < (n : ℝ) + q := add_pos hnR hq0
  apply NNReal.coe_le_coe.mp
  rw [pStarPreimage_coe hn hq0]
  rw [le_div_iff₀ hden]
  have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn1R : (1 : ℝ) ≤ n := le_trans (by norm_num) hn2R
  have hmul :
      ((n : ℝ) - 1) * (n : ℝ) ≤
        ((n : ℝ) - 1) * (q : ℝ) :=
    mul_le_mul_of_nonneg_left (le_of_lt hq) (sub_nonneg.mpr hn1R)
  have hfac : (1 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hpoly :
      (n : ℝ) ≤ ((n : ℝ) - 1) * (n : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right hfac (le_of_lt hnR)
  calc
    (1 : ℝ) * ((n : ℝ) + q) = (n : ℝ) + q := by ring
    _ ≤ ((n : ℝ) - 1) * q + q := by
      simpa [add_comm] using add_le_add_right (hpoly.trans hmul) (q : ℝ)
    _ = (n : ℝ) * q := by ring

/-- The preimage exponent satisfies the reciprocal Sobolev-conjugacy relation
`1 / s - 1 / n = 1 / q`. -/
theorem inv_pStarPreimage_sub_inv_dimension
    {n : ℕ} {q : NNReal} (hn : 0 < n) (hq : 0 < (q : ℝ)) :
    ((pStarPreimage n q : NNReal) : ℝ)⁻¹ -
        (n : ℝ)⁻¹ =
      (q : ℝ)⁻¹ := by
  rw [pStarPreimage_coe hn hq]
  cas

/-- The Sobolev-conjugate map sends its positive preimage back to the
original exponent. -/
theorem pStar_pStarPreimage
    {n : ℕ} {q : NNReal} (hn : 0 < n) (hq : 0 < (q : ℝ)) :
    pStar n (pStarPreimage n q) = q := by
  have hs0 : 0 < ((pStarPreimage n q : NNReal) : ℝ) := by
    rw [pStarPreimage_coe hn hq]
    positivity
  apply NNReal.eq
  apply inv_injective
  rw [inv_pStar_eq hn hs0 (pStarPreimage_lt_dimension hn hq)]
  exact inv_pStarPreimage_sub_inv_dimension hn hq

/-- The coordinate Gagliardo–Nirenberg–Sobolev inequality with explicit constant one.
For `q = n/(n-1)`, the integral of `‖u‖^q` is bounded by the `q`-th power of
the sum of the coordinate derivative integrals. The target need not be finite
dimensional or complete. -/
theorem lintegral_pow_le_pow_sum_lintegral_partialDeriv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {q : ℝ} (hq : Real.HolderConjugate n q) {u : ℝ^n → F}
    (hu : ContDiff ℝ 1 u) (hcompact : HasCompactSupport u) :
    ∫⁻ x, ‖u x‖ₑ ^ q ≤ (∑ i : Fin n, ∫⁻ x, ‖(∂[i] u) x‖ₑ) ^ q := by
  classical
  -- The canonical coordinates preserve volume, so no Haar scalar factor is needed.
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm
  let v : (Fin n → ℝ) → F := u ∘ e
  have hv : ContDiff ℝ 1 v := hu.comp e.contDiff
  have hvc : HasCompactSupport v := hcompact.comp_homeomorph e.toHomeomorph
  have hmp : MeasurePreserving e := PiLp.volume_preserving_toLp (Fin n)
  have hleft : (∫⁻ y, ‖v y‖ₑ ^ q) = ∫⁻ x, ‖u x‖ₑ ^ q := by
    simpa only [v, Function.comp_apply] using
      hmp.lintegral_comp (f := fun x : ℝ^n ↦ ‖u x‖ₑ ^ q)
        (hu.continuous.enorm.measurable.pow_const q)
  have hc (i : Fin n) : Continuous (∂[i] u) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hderiv (y : Fin n → ℝ) :
      fderiv ℝ v y = (fderiv ℝ u (e y)).comp e.toContinuousLinearMap :=
    (hu.differentiable one_ne_zero (e y)).hasFDerivAt.comp y e.hasFDerivAt |>.fderiv
  have hnorm (y : Fin n → ℝ) :
      ‖fderiv ℝ v y‖ₑ ≤ ∑ i : Fin n, ‖(∂[i] u) (e y)‖ₑ := by
    have h := (fderiv ℝ v y).norm_le_sum_norm_apply_pi_single
    rw [hderiv] at h
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at h
    rw [hderiv]
    simp only [enorm_eq_nnnorm, ← ENNReal.ofNNReal_finsetSum, ENNReal.coe_le_coe]
    apply NNReal.coe_le_coe.mp
    have hs : ∀ i : Fin n,
        e (Pi.single i (1 : ℝ)) = EuclideanSpace.single i 1 := fun _ ↦ rfl
    simpa only [NNReal.coe_sum, coe_nnnorm, PDE.partialDeriv, hs] using h
  calc
    ∫⁻ x, ‖u x‖ₑ ^ q = ∫⁻ y, ‖v y‖ₑ ^ q := hleft.symm
    _ ≤ (∫⁻ y, ‖fderiv ℝ v y‖ₑ) ^ q := by
      apply lintegral_pow_le_pow_lintegral_fderiv_aux _ hv hvc
      simpa only [Fintype.card_fin] using hq
    _ ≤ (∫⁻ y, ∑ i : Fin n, ‖(∂[i] u) (e y)‖ₑ) ^ q :=
      ENNReal.rpow_le_rpow (lintegral_mono hnorm) hq.symm.nonneg
    _ = (∑ i : Fin n, ∫⁻ y, ‖(∂[i] u) (e y)‖ₑ) ^ q := by
      rw [lintegral_finsetSum]
      exact fun i _ ↦ ((hc i).comp e.continuous).enorm.measurable
    _ = (∑ i : Fin n, ∫⁻ x, ‖(∂[i] u) x‖ₑ) ^ q := by
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦
        hmp.lintegral_comp (f := fun x : ℝ^n ↦ ‖(∂[i] u) x‖ₑ) (hc i).enorm.measurable

/-- At the endpoint `q = n/(n-1)`, the sum of the `L¹` coordinate derivative
norms bounds the `Lᑫ` norm with explicit constant one. No choice-dependent
embedding constant enters this estimate. -/
theorem eLpNorm_le_sum_eLpNorm_partialDeriv_one
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {q : NNReal} (hq : NNReal.HolderConjugate n q) {u : ℝ^n → F}
    (hu : ContDiff ℝ 1 u) (hcompact : HasCompactSupport u) :
    eLpNorm u q volume ≤ ∑ i : Fin n, eLpNorm (∂[i] u) 1 volume := by
  have hc (i : Fin n) : Continuous (∂[i] u) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  rw [← ENNReal.rpow_le_rpow_iff hq.coe.symm.pos,
    eLpNorm_nnreal_pow_eq_lintegral hq.symm.pos.ne' hu.continuous.aestronglyMeasurable]
  simp_rw [eLpNorm_one_eq_lintegral_enorm (hc _).aestronglyMeasurable]
  exact lintegral_pow_le_pow_sum_lintegral_partialDeriv hq.coe hu hcompact

section EndpointLifting

open Module MeasureTheory.Measure
open scoped NNReal

/-- An explicit scalar endpoint estimate lifts to every subcritical exponent greater
than one. The resulting constant is `C * p(n-1)/(n-p)` and the target may be
any real inner product space.

The norm-power and Hölder argument is adapted from Mathlib's
`eLpNorm_le_eLpNorm_fderiv_of_eq_inner`; the supplied endpoint bound replaces
its chosen-basis constant. -/
theorem eLpNorm_le_eLpNorm_fderiv_of_endpoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [IsAddHaarMeasure μ] (C : ℝ≥0)
    (hendpoint : ∀ (v : E → ℝ), ContDiff ℝ 1 v → HasCompactSupport v →
      eLpNorm v (NNReal.conjExponent (finrank ℝ E)) μ ≤
        C * eLpNorm (fderiv ℝ v) 1 μ)
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {u : E → F} (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u)
    {p p' : ℝ≥0} (hp : 1 < p) (hn : 0 < finrank ℝ E)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (finrank ℝ E : ℝ)⁻¹) :
    eLpNorm u p' μ ≤
      (C * (p * ((finrank ℝ E : ℝ) - 1) / ((finrank ℝ E : ℝ) - p)).toNNReal : ℝ≥0) *
        eLpNorm (fderiv ℝ u) p μ := by
  by_cases hp'0 : p' = 0
  · simp [hp'0, eLpNorm_exponent_zero hu.continuous.aestronglyMeasurable]
  set n := finrank ℝ E
  let n' := NNReal.conjExponent n
  have h2p : (p : ℝ) < n := by
    have : 0 < p⁻¹ - (n : ℝ)⁻¹ :=
      NNReal.coe_lt_coe.mpr (pos_iff_ne_zero.mpr (inv_ne_zero hp'0)) |>.trans_eq hp'
    rwa [NNReal.coe_inv, sub_pos,
      inv_lt_inv₀ _ (zero_lt_one.trans_le (NNReal.coe_le_coe.mpr hp.le))] at this
    exact_mod_cast hn
  have h0n : 2 ≤ n := Nat.succ_le_of_lt <| Nat.one_lt_cast.mp <|
    (show (1 : ℝ) ≤ p from hp.le).trans_lt h2p
  have hn : NNReal.HolderConjugate n n' := .conjExponent (by norm_cast)
  have h1n : 1 ≤ (n : ℝ≥0) := hn.lt.le
  have h2n : (0 : ℝ) < n - 1 := by simp_rw [sub_pos]; exact hn.coe.lt
  have hnp : (0 : ℝ) < n - p := by simp_rw [sub_pos]; exact h2p
  let q := Real.conjExponent p
  have hq : Real.HolderConjugate p q := .conjExponent hp
  have h0p : p ≠ 0 := zero_lt_one.trans hp |>.ne'
  have h1p : (p : ℝ) ≠ 1 := hq.lt.ne'
  have h3p : (p : ℝ) - 1 ≠ 0 := sub_ne_zero_of_ne h1p
  have h2q : 1 / n' - 1 / q = 1 / p' := by
    simp_rw -zeta [one_div, hp']
    rw [← hq.one_sub_inv, ← hn.coe.one_sub_inv]
    simp only [NNReal.coe_natCast, NNReal.coe_inv]
    ring
  let γ : ℝ≥0 := .mk (p * (n - 1) / (n - p)) (by positivity)
  have h0γ : (γ : ℝ) = p * (n - 1) / (n - p) := rfl
  have h1γ : 1 < (γ : ℝ) := by
    rwa [h0γ, one_lt_div hnp, mul_sub, mul_one, sub_lt_sub_iff_right, lt_mul_iff_one_lt_left]
    exact hn.coe.pos
  have h2γ : γ * n' = p' := by
    rw [← NNReal.coe_inj, ← inv_inj, hp', NNReal.coe_mul, h0γ, hn.coe.conjugate_eq]
    simp [field]
  have h3γ : (γ - 1) * q = p' := by
    rw [← inv_inj, hp', h0γ, hq.conjugate_eq]
    have : (p : ℝ) * (n - 1) - (n - p) = n * (p - 1) := by ring
    simp [field, this]
  have h4γ : (γ : ℝ) ≠ 0 := (zero_lt_one.trans h1γ).ne'
  by_cases h3u : ∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ = 0
  · rw [eLpNorm_nnreal_eq_lintegral hp'0 hu.continuous.aestronglyMeasurable, h3u,
      ENNReal.zero_rpow_of_pos] <;> positivity
  have h4u : ∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ ≠ ∞ := by
    refine lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top
      ((NNReal.coe_pos.trans pos_iff_ne_zero).mpr hp'0) ?_ |>.ne
    rw [← eLpNorm_nnreal_eq_eLpNorm' hp'0 hu.continuous.aestronglyMeasurable]
    exact hu.continuous.memLp_of_hasCompactSupport (μ := μ) h2u |>.eLpNorm_lt_top
  have h5u : (∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ) ^ (1 / q) ≠ 0 :=
    ENNReal.rpow_pos (pos_iff_ne_zero.mpr h3u) h4u |>.ne'
  have h6u : (∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ) ^ (1 / q) ≠ ∞ := by finiteness
  have h7u := hu.continuous -- for fun_prop
  -- Choose the power so that both the endpoint and Hölder exponents produce `p'`.
  let v : E → ℝ := fun x ↦ ‖u x‖ ^ (γ : ℝ)
  have hv : ContDiff ℝ 1 v := hu.norm_rpow h1γ
  have h2v : HasCompactSupport v := h2u.norm.rpow_const h4γ
  have :=
  calc (∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ) ^ (1 / (n' : ℝ)) = eLpNorm v n' μ := by
        rw [← h2γ, eLpNorm_nnreal_eq_lintegral hn.symm.pos.ne' hv.continuous.aestronglyMeasurable]
        simp (discharger := positivity) [v, Real.enorm_rpow_of_nonneg, ENNReal.rpow_mul]
    _ ≤ C * eLpNorm (fderiv ℝ v) 1 μ := hendpoint v hv h2v
    _ = C * ∫⁻ x, ‖fderiv ℝ v x‖ₑ ∂μ := by
      rw [eLpNorm_one_eq_lintegral_enorm (hv.continuous_fderiv one_ne_zero).aestronglyMeasurable]
    _ ≤ C * γ * ∫⁻ x, ‖u x‖ₑ ^ ((γ : ℝ) - 1) * ‖fderiv ℝ u x‖ₑ ∂μ := by
      rw [mul_assoc, ← lintegral_const_mul γ]
      · gcongr
        simp_rw [← mul_assoc]
        exact enorm_fderiv_norm_rpow_le (hu.differentiable one_ne_zero) h1γ
      dsimp [enorm]
      fun_prop
    _ ≤ C * γ * ((∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ) ^ (1 / q) *
        (∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ))) := by
        gcongr
        convert!
          ENNReal.lintegral_mul_le_Lp_mul_Lq μ (.symm <| .conjExponent <| show 1 < (p : ℝ) from hp)
            ?_ ?_ using 5
        · simp [γ, n, q, ← ENNReal.rpow_mul, ← h3γ]
        · borelize F
          fun_prop
        · fun_prop
    _ = C * γ * (∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) *
      (∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ) ^ (1 / q) := by ring
  -- The nonzero finite norm of `u` permits cancellation of the Hölder factor.
  calc
    eLpNorm u p' μ
      = (∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ) ^ (1 / (p' : ℝ)) :=
        eLpNorm_nnreal_eq_lintegral hp'0 hu.continuous.aestronglyMeasurable
    _ ≤ C * γ * (∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) := by
      rwa [← h2q, ENNReal.rpow_sub _ _ h3u h4u, ENNReal.div_le_iff h5u h6u]
    _ = (C * (p * ((finrank ℝ E : ℝ) - 1) /
          ((finrank ℝ E : ℝ) - p)).toNNReal : ℝ≥0) *
        eLpNorm (fderiv ℝ u) (↑p) μ := by
      have hγeq : γ = (p * ((finrank ℝ E : ℝ) - 1) /
          ((finrank ℝ E : ℝ) - p)).toNNReal := by
        apply NNReal.coe_injective
        rw [Real.coe_toNNReal _ (by
          change 0 ≤ (p : ℝ) * (n - 1) / (n - p)
          positivity)]
        exact h0γ
      rw [eLpNorm_nnreal_eq_lintegral h0p
        (hu.continuous_fderiv one_ne_zero).aestronglyMeasurable,
        ← hγeq, ENNReal.coe_mul]


/-- On Euclidean space the scalar endpoint has the explicit operator constant `n`. -/
theorem eLpNorm_le_dim_mul_eLpNorm_fderiv_one
    {n : ℕ} (hn : 2 ≤ n) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℝ^n → F} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    eLpNorm u (NNReal.conjExponent n) volume ≤
      (n : ℝ≥0∞) * eLpNorm (fderiv ℝ u) 1 volume := by
  have hq : NNReal.HolderConjugate n (NNReal.conjExponent n) :=
    .conjExponent (by exact_mod_cast (show 1 < n by omega))
  apply (eLpNorm_le_sum_eLpNorm_partialDeriv_one hq hu hc).trans
  calc
    ∑ i : Fin n, eLpNorm (∂[i] u) 1 volume ≤
        ∑ _i : Fin n, eLpNorm (fderiv ℝ u) 1 volume := by
      apply Finset.sum_le_sum
      intro i _
      apply eLpNorm_mono ((hu.continuous_fderiv one_ne_zero).clm_apply
        continuous_const).aestronglyMeasurable
      intro x
      calc
        ‖(∂[i] u) x‖ ≤ ‖fderiv ℝ u x‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
          (fderiv ℝ u x).le_opNorm _
        _ = ‖fderiv ℝ u x‖ := by simp
    _ = _ := by simp

/-- Subcritical Euclidean Sobolev embedding with the explicit constant
`np(n-1)/(n-p)`. The codomain may be any real inner product space. -/
theorem eLpNorm_le_explicit_mul_eLpNorm_fderiv_pStar
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {u : ℝ^n → F} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u)
    {p : ℝ≥0} (hp : 1 < p) (hn : 0 < n) (hpn : (p : ℝ) < n) :
    eLpNorm u (pStar n p) volume ≤
      ((n : ℝ≥0) * (p * ((n : ℝ) - 1) / ((n : ℝ) - p)).toNNReal : ℝ≥0) *
        eLpNorm (fderiv ℝ u) p volume := by
  have hn2 : 2 ≤ n := by
    have h : (1 : ℝ) < n := (show (1 : ℝ) < p from hp).trans hpn
    exact Nat.succ_le_of_lt (Nat.one_lt_cast.mp h)
  simpa only [finrank_euclideanSpace_fin, ENNReal.coe_natCast] using
    eLpNorm_le_eLpNorm_fderiv_of_endpoint (volume : Measure (ℝ^n)) (n : ℝ≥0)
      (fun v hv hvcompact ↦ by
        simpa only [finrank_euclideanSpace_fin, ENNReal.coe_natCast] using
          eLpNorm_le_dim_mul_eLpNorm_fderiv_one hn2 hv hvcompact)
      hu hc hp (by simpa only [finrank_euclideanSpace_fin] using hn)
      (by simpa only [finrank_euclideanSpace_fin, NNReal.coe_inv] using (inv_pStar_eq hn
        (show (0 : ℝ) < p from (zero_lt_one.trans hp)) hpn))


end EndpointLifting

/-- Gagliardo–Nirenberg–Sobolev inequality on `ℝ^n` with `p* = np/(n-p)`
(Evans §5.6). -/
theorem eLpNorm_le_eLpNorm_fderiv_pStar
    {u : ℝ^n → ℝ} (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u)
    {p : NNReal} (hp : (1 : NNReal) ≤ p) (hn : 0 < n)
    (hp' : (p : ℝ) < (n : ℝ)) :
    MeasureTheory.eLpNorm u (pStar n p) (MeasureTheory.volume : Measure (ℝ^n)) ≤
      MeasureTheory.SNormLESNormFDerivOfEqConst ℝ (MeasureTheory.volume : Measure (ℝ^n)) p *
        MeasureTheory.eLpNorm (fderiv ℝ u) p (MeasureTheory.volume : Measure (ℝ^n)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast zero_lt_one.trans_le hp
  have hn' : 0 < Module.finrank ℝ (ℝ^n) := by
    simpa using hn
  simpa using
    (MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq
      (μ := (MeasureTheory.volume : Measure (ℝ^n))) (u := u) hu h2u hp hn'
      (by simpa using inv_pStar_eq (n := n) (p := p) hn hp0 hp'))

end GNS

/-!
## From `C_c^1` to `W^{1,p}` (Evans §5.6)

Mathlib's Sobolev inequality is stated in terms of `fderiv`. For scalar functions on `ℝ^n`,
the operator norm of `fderiv` is bounded by a finite sum of coordinate partial derivatives,
and the global approximation theorem (§5.3.3) then extends the inequality to `W^{1,p}(ℝ^n)`.
-/

section W1p

variable {n : ℕ}

/-- For a scalar `C¹` function on `ℝ^n`, the `Lᵖ` norm of its Fréchet
derivative is bounded by the sum of the `Lᵖ` norms of its coordinate partial
derivatives. -/
theorem eLpNorm_fderiv_le_sum_eLpNorm_partialDeriv {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {u : ℝ^n → ℝ} (hu : ContDiff ℝ 1 u) :
    MeasureTheory.eLpNorm (fderiv ℝ u) p (MeasureTheory.volume : Measure (ℝ^n)) ≤
      ∑ i : Fin n, MeasureTheory.eLpNorm (fun x ↦ (∂[i] u) x) p
        (MeasureTheory.volume : Measure (ℝ^n)) := by
  have hmeas (i : Fin n) : AEStronglyMeasurable (fun x ↦ (∂[i] u) x) volume :=
    ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
  calc eLpNorm (fderiv ℝ u) p volume ≤ eLpNorm (fun x ↦ ∑ i : Fin n, ‖(∂[i] u) x‖) p volume :=
        eLpNorm_mono_ae_real (hu.continuous_fderiv one_ne_zero).aestronglyMeasurable
          (.of_forall (PDE.norm_fderiv_le_sum_norm_partialDeriv u))
    _ ≤ ∑ i : Fin n, eLpNorm (fun x ↦ ‖(∂[i] u) x‖) p volume := by
      convert eLpNorm_sum_le (μ := volume) (f := fun i x ↦ ‖(∂[i] u) x‖) (s := Finset.univ)
        (Fact.out : (1 : ℝ≥0∞) ≤ p) using 2
      ext x
      simp
    _ = _ := Finset.sum_congr rfl fun i _ ↦ eLpNorm_norm _ (hmeas i)

/-- Sobolev inequality for `C¹` compactly-supported scalar functions, with RHS written using
coordinate partial derivatives. -/
theorem eLpNorm_le_sum_eLpNorm_partialDeriv_of_eq
    {u : ℝ^n → ℝ} (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u)
    {p p' : NNReal} (hp : (1 : NNReal) ≤ p) (hn : 0 < n)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (n : ℝ)⁻¹) :
    MeasureTheory.eLpNorm u p' (MeasureTheory.volume : Measure (ℝ^n)) ≤
      (MeasureTheory.SNormLESNormFDerivOfEqConst ℝ
          (MeasureTheory.volume : Measure (ℝ^n)) (p : ℝ) : ℝ≥0∞) *
      (∑ i : Fin n,
          MeasureTheory.eLpNorm (fun x ↦ (∂[i] u) x) (p : ℝ≥0∞)
            (MeasureTheory.volume : Measure (ℝ^n))) := by
  have : Fact ((1 : ℝ≥0∞) ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
  have hSob : eLpNorm u p' volume ≤
      SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^n)) p *
        eLpNorm (fderiv ℝ u) p volume := by
    simpa using eLpNorm_le_eLpNorm_fderiv_of_eq (μ := volume) hu h2u hp (by simpa using hn)
      (by simpa using hp')
  exact hSob.trans (mul_le_mul_right (eLpNorm_fderiv_le_sum_eLpNorm_partialDeriv hu) _)

/-!
### Sobolev inequality on bounded sets (Evans §5.6, bounded-domain variant)

Evans also records the variant where `u` is supported in a bounded set `s` and one gets an
estimate in `L^q` for any `q ≤ p*`. Mathlib has this as
`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_le`, restated here with the coordinate
`partialDeriv`.
-/

/-- Sobolev inequality for `C¹` functions supported in a bounded set `s`, at every exponent `q`
with `1/q ≥ 1/p - 1/n`: Mathlib's `eLpNorm_le_eLpNorm_fderiv_of_le` with the derivative norm
expanded into coordinate partials. Boundedness of `s` is what allows exponents below `p*`. -/
theorem eLpNorm_le_sum_eLpNorm_partialDeriv_of_le
    {u : ℝ^n → ℝ} {s : Set (ℝ^n)} (hu : ContDiff ℝ 1 u) (hsupp : u.support ⊆ s)
    {p q : NNReal} (hp : (1 : NNReal) ≤ p) (hp_lt : (p : ℝ) < (n : ℝ))
    (hpq : p⁻¹ - (n : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) (hs : Bornology.IsBounded s) :
    MeasureTheory.eLpNorm u q (MeasureTheory.volume : Measure (ℝ^n)) ≤
      (MeasureTheory.eLpNormLESNormFDerivOfLeConst ℝ
          (MeasureTheory.volume : Measure (ℝ^n)) s p q : ℝ≥0∞) *
        (∑ i : Fin n,
          MeasureTheory.eLpNorm (fun x ↦ (∂[i] u) x) (p : ℝ≥0∞)
            (MeasureTheory.volume : Measure (ℝ^n))) := by
  have : Fact ((1 : ℝ≥0∞) ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
  have hSob : eLpNorm u q volume ≤
      eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure (ℝ^n)) s p q *
        eLpNorm (fderiv ℝ u) p volume := by
    simpa using eLpNorm_le_eLpNorm_fderiv_of_le (μ := volume) (F := ℝ) hu hsupp hp
      (by rwa [finrank_euclideanSpace_fin]) (by simpa using hpq) hs
  exact hSob.trans (mul_le_mul_right (eLpNorm_fderiv_le_sum_eLpNorm_partialDeriv hu) _)

/-!
### Global embedding `W^{1,p}(ℝ^n) → L^{p*}(ℝ^n)`

The `C_c^1` Sobolev inequality extends to global Sobolev functions by density, yielding
`L^{p*}` membership. This result does not bundle the inclusion as a continuous linear map.
-/

/-- Every global `W^{1,p}(ℝ^n)` function lies in `L^{p'}` when
`1/p' = 1/p - 1/n`. Smooth approximation bounds the target norms by the
convergent first-derivative norms. An almost-everywhere convergent subsequence
and Fatou's lemma then give membership of the same base function. -/
theorem memLp_pStar_of_sobolevSpace
    {p p' : NNReal} (hp : (1 : NNReal) ≤ p) (hn : 0 < n)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (n : ℝ)⁻¹)
    (u : _root_.SobolevSpace.GlobalSobolevSpace n 1 (p : ℝ≥0∞)) :
    MeasureTheory.MemLp u.toFun (p' : ℝ≥0∞) (MeasureTheory.volume : Measure (ℝ^n)) := by
  classical
  have hpE : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp
  have : Fact ((1 : ℝ≥0∞) ≤ p) := ⟨hpE⟩
  obtain ⟨f, hf, hfcs, hfbase, hfderiv⟩ :=
    SobolevSpace.Approximation.globalApproximation_Wkp (n := n)
      (μ := SobolevSpace.Approximation.standardMollifier n) (p := p) (by simp) (k := 1) u
  have hderiv (i : Fin n) : ∃ g : ℝ^n → ℝ, MemLp g p volume ∧
      Filter.Tendsto (fun m ↦ eLpNorm (fun x ↦ (∂[i] (f m)) x - g x) p volume)
        Filter.atTop (𝓝 0) := by
    obtain ⟨g, hg, _, ht⟩ := hfderiv [i] (by simp)
    exact ⟨g, hg, by simpa only [iteratedPartialDeriv] using ht⟩
  choose g hg hgt using hderiv
  have hsmall : ∀ᶠ m in Filter.atTop, ∀ i : Fin n,
      eLpNorm (fun x ↦ (∂[i] (f m)) x - g i x) p volume ≤ 1 :=
    Filter.eventually_all.2 fun i ↦
      ((hgt i).eventually (gt_mem_nhds zero_lt_one)).mono fun _ hm ↦ hm.le
  let B : ℝ≥0∞ := SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^n)) p *
    ∑ i : Fin n, (1 + eLpNorm (g i) p volume)
  have hB : B < ∞ := ENNReal.mul_lt_top (by simp)
    (ENNReal.sum_lt_top.mpr fun i _ ↦ ENNReal.add_lt_top.mpr ⟨by simp, hg i⟩)
  have hbound : ∀ᶠ m in Filter.atTop, eLpNorm (f m) (p' : ℝ≥0∞) volume ≤ B := by
    filter_upwards [hsmall] with m hm
    refine (eLpNorm_le_sum_eLpNorm_partialDeriv_of_eq
      ((hf m).of_le (by simp)) (hfcs m) hp hn hp').trans
      (mul_le_mul_right (Finset.sum_le_sum fun i _ ↦ ?_) _)
    calc
      eLpNorm (∂[i] (f m)) p volume =
          eLpNorm ((fun x ↦ (∂[i] (f m)) x - g i x) + g i) p volume := by
        congr 1
        funext x
        exact (sub_add_cancel _ _).symm
      _ ≤ _ := (eLpNorm_add_le hpE).trans (add_le_add_left (hm i) _)
  obtain ⟨φ, hφ, hφlim⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (ne_of_gt (lt_of_lt_of_le (by simp) hpE)) hfbase).exists_seq_tendsto_ae
  refine lt_of_le_of_lt ?_ hB
  exact Lp.eLpNorm_le_of_ae_tendsto (hφ.tendsto_atTop.eventually hbound)
    (fun m ↦ (hf (φ m)).continuous.aestronglyMeasurable)
    (by simpa only [domainMeasure, Measure.restrict_univ] using u.memLp.aestronglyMeasurable) hφlim

/-!
### Bounded-domain embeddings via extension (Evans §5.6 + §5.4)

Evans reduces bounded-domain Sobolev embeddings to the global embedding on `ℝ^n` using an
extension operator `E : W^{1,p}(Ω) → W^{1,p}(ℝ^n)` (Evans §5.4).
-/

/-- Bounded-domain Sobolev embedding through an extension operator: if `W^{1,p}(Ω)` admits an
extension to `W^{1,p}(ℝ^n)` agreeing with `u` a.e. on `Ω` (`HasExtension`), then every
`u ∈ W^{1,p}(Ω)` lies in `L^{p*}(Ω)` for `1 ≤ p < n`. No boundedness of `Ω` is needed for the
endpoint exponent; the boundary regularity enters only through `hE`. -/
theorem memLp_pStar_of_sobolevSpaceOn_of_extension
    {n : ℕ}
    {p : NNReal} (hp : (1 : NNReal) ≤ p) (hn : 0 < n) (hp_lt : (p : ℝ) < (n : ℝ))
    {Ω : Set (ℝ^n)}
    (hE : SobolevSpace.Extension.Representative.HasExtension n 1 (p : ℝ≥0∞) Ω) :
    ∀ u : SobolevSpaceOn n 1 (p : ℝ≥0∞) Ω,
      MeasureTheory.MemLp u.toFun (pStar n p : ℝ≥0∞) (domainMeasure n Ω) := by
  classical
  intro u
  rcases hE with ⟨extend, hExtend⟩
  have hp0 : (0 : ℝ) < p := by
    have hp0' : (0 : NNReal) < p := lt_of_lt_of_le (by norm_num) hp
    exact_mod_cast hp0'
  have hpinv : ((pStar n p : NNReal) : ℝ)⁻¹ = p⁻¹ - (n : ℝ)⁻¹ :=
    inv_pStar_eq (n := n) (p := p) hn hp0 hp_lt
  have hExt :
      MeasureTheory.MemLp (extend u).toFun (pStar n p : ℝ≥0∞)
        (MeasureTheory.volume : Measure (ℝ^n)) :=
    memLp_pStar_of_sobolevSpace
      (n := n) (p := p) (p' := pStar n p) hp hn hpinv (extend u)
  have hExtΩ :
      MeasureTheory.MemLp (extend u).toFun (pStar n p : ℝ≥0∞) (domainMeasure n Ω) := by
    simpa [domainMeasure] using (hExt.restrict Ω)
  exact (MeasureTheory.memLp_congr_ae (hExtend u)).1 hExtΩ

/-- On a bounded domain with an extension operator, the endpoint membership `u ∈ L^{p*}(Ω)`
gives `u ∈ L^q(Ω)` for every `q ≤ p*`, by finiteness of the measure. Since the conclusion is the
raw predicate `MemLp`, the statement also covers `q < 1`, outside the Banach-space range. -/
theorem memLp_of_le_pStar_of_sobolevSpaceOn_of_extension
    {n : ℕ}
    {p : NNReal} (hp : (1 : NNReal) ≤ p) (hn : 0 < n) (hp_lt : (p : ℝ) < (n : ℝ))
    {Ω : Set (ℝ^n)}
    (hE : SobolevSpace.Extension.Representative.HasExtension n 1 (p : ℝ≥0∞) Ω)
    (hΩ : Bornology.IsBounded Ω) :
    ∀ u : SobolevSpaceOn n 1 (p : ℝ≥0∞) Ω,
      ∀ {q : ℝ≥0∞}, q ≤ (pStar n p : ℝ≥0∞) →
        MeasureTheory.MemLp u.toFun q (domainMeasure n Ω) := by
  classical
  intro u q hq
  have hpStar_mem :
      MeasureTheory.MemLp u.toFun (pStar n p : ℝ≥0∞) (domainMeasure n Ω) :=
    memLp_pStar_of_sobolevSpaceOn_of_extension (n := n) (p := p) hp hn hp_lt hE u
  let : MeasureTheory.IsFiniteMeasure (domainMeasure n Ω) :=
    isFiniteMeasure_domainMeasure_of_isBounded hΩ
  exact hpStar_mem.mono_exponent hq

end W1p

end Inequalities

end SobolevSpace
