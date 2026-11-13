/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Hardy.WeightedInterval
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.L2Space
import PDE.Spaces.Sobolev.Inequalities.Hardy.Classical
import CAS.ExactTactic

import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Weighted one-dimensional Hardy inequalities

For `s > 1/2`, `0 < ε < R`, and `u ∈ C¹(ℝ)` with `u(ε) = u(R) = 0`,

`(2s - 1)² ∫ u(x)² x^{-2s} dx ≤ 4 ∫ u'(x)² x^{2-2s} dx`.

This is the power-weighted Hardy inequality in `L²`: the singular weight `x^{-2s}` on the left
is paid for by the weight `x^{2-2s}` on the right, and `(2/(2s-1))²` is the classical constant.
At `s = 1` it is the unweighted inequality of `Hardy.Classical`. The proof is the same
integration by parts, this time against `(x^{1-2s})' = (1-2s) x^{-2s}`, followed by Cauchy–Schwarz.

Iterating the one-step estimate with `s = 1, 2, …, j` controls `x^{-j} f^{(m)}` by the unweighted
derivative `f^{(m+j)}`, with the explicit constant `4^j / ∏_{l=1}^{j} (2l-1)²`. This chain is the
input for the completed half-line quotient operators of `Hardy.HalfLine`.

## Main results

* `weighted_hardy_interval_identity`, `weighted_hardy_interval` (from `Hardy.WeightedInterval`):
  identity and inequality on `[ε, R]`.
* `weighted_hardy_Ioi_of_support_subset_Ioo` (from `Hardy.WeightedInterval`): the half-line
  inequality for `C¹` functions supported in some `(ε, R)` with `ε > 0`.
* `weighted_hardy_Ioi_iteratedDeriv_of_support_subset_Ioo`: the same for the `m`-th derivative
  of a `C^{m+1}` function.
* `iterated_weighted_hardy_Ioi_nat`, `iterated_weighted_hardy_Ioi_nat_of_hasCompactSupport`:
  the `j`-fold chain, on functions with explicit support bounds and on compactly supported
  `C^{m+j}` functions with support in `(0, ∞)`.
* `tsupport_iteratedDeriv_subset`: every iterated derivative has topological support
  contained in the topological support of `f`.
* `integral_Ioi_mul_sq_le_integral_Ioi_cube_mul_deriv_sq`: the four-dimensional radial Hardy
  inequality `∫₀^∞ r u² ≤ ∫₀^∞ r³ (u')²`, with `r u²` integrable, for `C¹` functions `u` such that
  `r³u²` and `r³(u')²` are integrable on `(0, ∞)`.
* `integral_Ioi_mul_two_mul_add_mul_deriv_sq_eq_integral_Ioi_cube_mul_deriv_sq`: under the same
  hypotheses, `r (2u + ru')²` is integrable and `∫₀^∞ r (2u + ru')² = ∫₀^∞ r³ (u')²`.

## Implementation notes

The inequalities are stated multiplied out, `(2s-1)² · X ≤ 4 · Y`, rather than as
`X ≤ 4/(2s-1)² · Y`. This avoids division in the induction and keeps the product of odd squares
explicit in the final constant. The iterated half-line estimates use compactly supported
functions with the stated finite differentiability order; the extension to completed zero-trace
spaces is in `Hardy.HalfLine`.

The two radial estimates assume no boundary condition at infinity: the integrability of `r³u²`
and `r³(u')²` makes the flux `r²u²` and its derivative integrable, so the improper fundamental
theorem of calculus gives the cancellation. Their polynomial identities are discharged by the
`cas` tactic of SymLean, our verified computer algebra system.

## References

* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, 2nd ed., Cambridge Mathematical
  Library, Cambridge University Press, 1988, Chapter IX, for the power-weighted form of Hardy's
  inequality.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace


namespace Hardy

open Set MeasureTheory
open scoped ENNReal

/--
Weighted half-line Hardy for the `m`-th derivative.  This is the form used to
control a singular factor `r⁻s Dᵐf` by the next radial derivative with the
shifted weight `r¹⁻s`.
-/
theorem weighted_hardy_Ioi_iteratedDeriv_of_support_subset_Ioo
    (m : ℕ) {f : ℝ → ℝ} {ε R s : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hs : 1 / 2 < s) (hf : ContDiff ℝ (m + 1) f)
    (hsupp : Function.support (iteratedDeriv m f) ⊆ Set.Ioo ε R) :
    (2 * s - 1) ^ 2 *
        (∫ x in Set.Ioi (0 : ℝ),
          (iteratedDeriv m f x) ^ 2 * x ^ (-2 * s)) ≤
      4 * ∫ x in Set.Ioi (0 : ℝ),
        (iteratedDeriv (m + 1) f x) ^ 2 * x ^ (2 - 2 * s) := by
  have hm : ContDiff ℝ 1 (iteratedDeriv m f) :=
    (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp hf).2
  have hderivEq : deriv (iteratedDeriv m f) = iteratedDeriv (m + 1) f :=
    (iteratedDeriv_succ (n := m) (f := f)).symm
  have h := weighted_hardy_Ioi_of_support_subset_Ioo
    hε hεR hs hm hsupp
  simpa only [hderivEq] using h

/-- Every iterated one-dimensional derivative has topological support inside
the topological support of the original function. -/
theorem tsupport_iteratedDeriv_subset (m : ℕ) (f : ℝ → ℝ) :
    tsupport (iteratedDeriv m f) ⊆ tsupport f := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [iteratedDeriv_succ]
      exact tsupport_deriv_subset.trans ih

/--
The full integer weighted-Hardy chain.  Repeating the one-step estimate `j`
times controls `r⁻ʲ Dᵐf` by the unweighted derivative `Dᵐ⁺ʲf`.  The product of
odd squares is kept explicit so that later radial estimates can quote the
constant of the chain rather than an unspecified one.

Support is required for every derivative level used in the chain.  This is
the compactly supported core statement; extending it to an `H¹₀` closure is a
separate density theorem.
-/
theorem iterated_weighted_hardy_Ioi_nat
    (j m : ℕ) {f : ℝ → ℝ} {ε R : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hf : ContDiff ℝ (m + j) f)
    (hsupp : ∀ l ≤ j,
      Function.support (iteratedDeriv (m + l) f) ⊆ Set.Ioo ε R) :
    (∏ l ∈ Finset.Icc 1 j, (2 * (l : ℝ) - 1) ^ 2) *
        (∫ x in Set.Ioi (0 : ℝ),
          (iteratedDeriv m f x) ^ 2 * x ^ (-2 * (j : ℝ))) ≤
      (4 : ℝ) ^ j * ∫ x in Set.Ioi (0 : ℝ),
        (iteratedDeriv (m + j) f x) ^ 2 := by
  induction j generalizing m with
  | zero => simp
  | succ j ih =>
      have hsHalf : (1 / 2 : ℝ) < (j + 1 : ℕ) := by
        have hjReal : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show (1 : ℕ) ≤ j + 1 by omega)
        linarith
      have hfOne : ContDiff ℝ (m + 1) f := by
        have horder : m + 1 ≤ m + (j + 1) := by omega
        exact hf.of_le (by exact_mod_cast horder)
      have hsuppZero :
          Function.support (iteratedDeriv m f) ⊆ Set.Ioo ε R := by
        simpa using hsupp 0 (Nat.zero_le (j + 1))
      have hstep0 := weighted_hardy_Ioi_iteratedDeriv_of_support_subset_Ioo
        m hε hεR hsHalf hfOne hsuppZero
      have hexp :
          (2 : ℝ) - 2 * ((j + 1 : ℕ) : ℝ) = -2 * (j : ℝ) := by
        push_cast
        ring
      rw [hexp] at hstep0
      have hstep :
          (2 * ((j + 1 : ℕ) : ℝ) - 1) ^ 2 *
              (∫ x in Set.Ioi (0 : ℝ),
                (iteratedDeriv m f x) ^ 2 *
                  x ^ (-2 * ((j + 1 : ℕ) : ℝ))) ≤
            4 * ∫ x in Set.Ioi (0 : ℝ),
              (iteratedDeriv (m + 1) f x) ^ 2 * x ^ (-2 * (j : ℝ)) := by
        exact hstep0
      have hfTail : ContDiff ℝ ((m + 1) + j) f := by
        simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hf
      have hsuppTail : ∀ l ≤ j,
          Function.support (iteratedDeriv ((m + 1) + l) f) ⊆ Set.Ioo ε R := by
        intro l hl
        have h := hsupp (l + 1) (Nat.succ_le_succ hl)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      have htail := ih (m + 1) hfTail hsuppTail
      have hprodNonneg :
          0 ≤ ∏ l ∈ Finset.Icc 1 j, (2 * (l : ℝ) - 1) ^ 2 := by
        positivity
      rw [Finset.prod_Icc_succ_top (a := 1) (b := j) (by omega)]
      calc
        ((∏ l ∈ Finset.Icc 1 j, (2 * (l : ℝ) - 1) ^ 2) *
              (2 * ((j + 1 : ℕ) : ℝ) - 1) ^ 2) *
            (∫ x in Set.Ioi (0 : ℝ),
              (iteratedDeriv m f x) ^ 2 *
                x ^ (-2 * ((j + 1 : ℕ) : ℝ))) =
            (∏ l ∈ Finset.Icc 1 j, (2 * (l : ℝ) - 1) ^ 2) *
              ((2 * ((j + 1 : ℕ) : ℝ) - 1) ^ 2 *
                (∫ x in Set.Ioi (0 : ℝ),
                  (iteratedDeriv m f x) ^ 2 *
                    x ^ (-2 * ((j + 1 : ℕ) : ℝ)))) := by ring
        _ ≤ (∏ l ∈ Finset.Icc 1 j, (2 * (l : ℝ) - 1) ^ 2) *
              (4 * ∫ x in Set.Ioi (0 : ℝ),
                (iteratedDeriv (m + 1) f x) ^ 2 * x ^ (-2 * (j : ℝ))) :=
          mul_le_mul_of_nonneg_left hstep hprodNonneg
        _ = 4 * ((∏ l ∈ Finset.Icc 1 j, (2 * (l : ℝ) - 1) ^ 2) *
              (∫ x in Set.Ioi (0 : ℝ),
                (iteratedDeriv (m + 1) f x) ^ 2 * x ^ (-2 * (j : ℝ)))) := by ring
        _ ≤ 4 * ((4 : ℝ) ^ j *
              ∫ x in Set.Ioi (0 : ℝ),
                (iteratedDeriv ((m + 1) + j) f x) ^ 2) :=
          mul_le_mul_of_nonneg_left htail (by norm_num)
        _ = (4 : ℝ) ^ (j + 1) *
              ∫ x in Set.Ioi (0 : ℝ),
                (iteratedDeriv (m + (j + 1)) f x) ^ 2 := by
          rw [show (m + 1) + j = m + (j + 1) by omega]
          rw [pow_succ]
          ring

/--
Repeated weighted Hardy for `C^{m+j}` functions with compact topological
support in `(0,∞)`. Compactness places the support in one interval
`(ε,R)` with `0 < ε < R`; support monotonicity then supplies every
intermediate derivative support bound required by the chain theorem.
-/
theorem iterated_weighted_hardy_Ioi_nat_of_hasCompactSupport
    (j m : ℕ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (m + j) f) (hcompact : HasCompactSupport f)
    (hpos : tsupport f ⊆ Set.Ioi (0 : ℝ)) :
    (∏ l ∈ Finset.Icc 1 j, (2 * (l : ℝ) - 1) ^ 2) *
        (∫ x in Set.Ioi (0 : ℝ),
          (iteratedDeriv m f x) ^ 2 * x ^ (-2 * (j : ℝ))) ≤
      (4 : ℝ) ^ j * ∫ x in Set.Ioi (0 : ℝ),
        (iteratedDeriv (m + j) f x) ^ 2 := by
  obtain ⟨ε, R, hε, hεR, hsuppTop⟩ :=
    exists_Ioo_bounds_tsupport_of_subset_Ioi hcompact hpos
  have hsupp : ∀ l ≤ j,
      Function.support (iteratedDeriv (m + l) f) ⊆ Set.Ioo ε R := by
    intro l _hl
    exact (subset_tsupport _).trans
      ((tsupport_iteratedDeriv_subset (m + l) f).trans hsuppTop)
  exact iterated_weighted_hardy_Ioi_nat j m hε hεR hf hsupp

/-- A lower radial power is harmless near zero by continuity, and is bounded
by the cubic weight outside the unit interval. -/
private theorem integrableOn_lower_radial_weight
    {u w : ℝ → ℝ} (hu : Continuous u) (hw : Continuous w)
    (hwbound : ∀ r ≥ 1, 0 ≤ w r ∧ w r ≤ r ^ 3)
    (h3 : IntegrableOn (fun r ↦ r ^ 3 * u r ^ 2) (Ioi 0)) :
    IntegrableOn (fun r ↦ w r * u r ^ 2) (Ioi 0) := by
  have hlocal : IntegrableOn (fun r ↦ w r * u r ^ 2) (Ioc 0 1) :=
    (hw.mul (hu.pow 2)).integrableOn_Ioc
  have htail : IntegrableOn (fun r ↦ w r * u r ^ 2) (Ioi 1) := by
    refine (h3.mono_set (Ioi_subset_Ioi zero_le_one)).mono'
      (hw.mul (hu.pow 2)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hwbound r hr.le).1 (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hwbound r hr.le).2 (sq_nonneg _)
  simpa only [Ioc_union_Ioi_eq_Ioi zero_le_one] using hlocal.union htail

/-- The flux `r²u²` and its derivative are integrable. The improper FTC
therefore gives the cancellation without prescribing a trace at infinity. -/
private theorem radial_four_flux_identity
    {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    (h0 : IntegrableOn (fun r ↦ r ^ 3 * u r ^ 2) (Ioi 0))
    (h1 : IntegrableOn (fun r ↦ r ^ 3 * deriv u r ^ 2) (Ioi 0)) :
    IntegrableOn (fun r ↦ r * u r ^ 2) (Ioi 0) ∧
      IntegrableOn (fun r ↦ r ^ 2 * u r * deriv u r) (Ioi 0) ∧
      (∫ r in Ioi 0, r * u r ^ 2) =
        -(∫ r in Ioi 0, r ^ 2 * u r * deriv u r) := by
  have hlow : IntegrableOn (fun r ↦ r * u r ^ 2) (Ioi 0) :=
    integrableOn_lower_radial_weight hu.continuous continuous_id
      (fun r hr ↦ ⟨by linarith, by
        have hr0 : 0 ≤ r := by linarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hr) hr0,
          mul_nonneg (sub_nonneg.mpr hr) (sq_nonneg r)]⟩) h0
  have hflux : IntegrableOn (fun r ↦ r ^ 2 * u r ^ 2) (Ioi 0) :=
    integrableOn_lower_radial_weight hu.continuous (continuous_id.pow 2)
      (fun r hr ↦ ⟨sq_nonneg _, by
        nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sq_nonneg r)]⟩) h0
  have hsqrt (r : ℝ) (hr : 0 < r) : Real.sqrt r ^ 2 = r :=
    Real.sq_sqrt hr.le
  have hF : MemLp (fun r ↦ Real.sqrt r * u r) 2 (volume.restrict (Ioi 0)) := by
    refine (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.mul hu.continuous).aestronglyMeasurable).2 ?_
    refine hlow.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    change r * u r ^ 2 = (Real.sqrt r * u r) ^ 2
    simp only [mul_pow, hsqrt r hr]
  have hG : MemLp (fun r ↦ r * Real.sqrt r * deriv u r) 2
      (volume.restrict (Ioi 0)) := by
    refine (memLp_two_iff_integrable_sq
      ((continuous_id.mul Real.continuous_sqrt).mul
        (hu.continuous_deriv le_rfl)).aestronglyMeasurable).2 ?_
    refine h1.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    change r ^ 3 * deriv u r ^ 2 = (r * Real.sqrt r * deriv u r) ^ 2
    simp only [mul_pow, hsqrt r hr]
    cas
  have hcross : IntegrableOn (fun r ↦ r ^ 2 * u r * deriv u r) (Ioi 0) := by
    have hprod : Integrable
        (fun r ↦ (Real.sqrt r * u r) * (r * Real.sqrt r * deriv u r))
        (volume.restrict (Ioi 0)) :=
      memLp_one_iff_integrable.mp (hF.fun_mul hG)
    refine hprod.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    calc
      _ = r * (Real.sqrt r ^ 2) * u r * deriv u r := by cas
      _ = _ := by rw [hsqrt r hr]; cas
  have hderiv (r : ℝ) :
      HasDerivAt (fun s ↦ s ^ 2 * u s ^ 2)
        (2 * (r * u r ^ 2) + 2 * (r ^ 2 * u r * deriv u r)) r := by
    exact (((hasDerivAt_id r).pow 2).mul
      (((hu.differentiable one_ne_zero) r).hasDerivAt.pow 2)).congr_deriv (by
        change (2 * r ^ (2 - 1) * 1) * u r ^ 2 +
          r ^ 2 * (2 * u r ^ (2 - 1) * deriv u r) = _
        cas)
  have hderivInt : IntegrableOn
      (fun r ↦ 2 * (r * u r ^ 2) + 2 * (r ^ 2 * u r * deriv u r)) (Ioi 0) :=
    (hlow.const_mul 2).add (hcross.const_mul 2)
  have hlim := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (fun r _ ↦ hderiv r) hderivInt hflux
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun r (_ : r ∈ Ici (0 : ℝ)) ↦ hderiv r) hderivInt hlim
  rw [integral_add (hlow.const_mul 2) (hcross.const_mul 2),
    integral_const_mul, integral_const_mul] at hFTC
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, sub_zero] at hFTC
  exact ⟨hlow, hcross, by linarith⟩

/-- The four-dimensional radial Hardy inequality with its decay normalization.
The assumptions are the cubic-weighted `L²` moments of `u` and `u'`; no
boundary trace at infinity is required. The constant is one. -/
theorem integral_Ioi_mul_sq_le_integral_Ioi_cube_mul_deriv_sq
    {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    (h0 : IntegrableOn (fun r ↦ r ^ 3 * u r ^ 2) (Ioi 0))
    (h1 : IntegrableOn (fun r ↦ r ^ 3 * deriv u r ^ 2) (Ioi 0)) :
    IntegrableOn (fun r ↦ r * u r ^ 2) (Ioi 0) ∧
      (∫ r in Ioi 0, r * u r ^ 2) ≤
        ∫ r in Ioi 0, r ^ 3 * deriv u r ^ 2 := by
  obtain ⟨hlow, hcross, hidentity⟩ := radial_four_flux_identity hu h0 h1
  have hnonneg : 0 ≤ ∫ r in Ioi 0, r * (u r + r * deriv u r) ^ 2 := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg hr.le (sq_nonneg _)
  have hexpand :
      (∫ r in Ioi 0, r * (u r + r * deriv u r) ^ 2) =
        (∫ r in Ioi 0, r * u r ^ 2) +
          2 * (∫ r in Ioi 0, r ^ 2 * u r * deriv u r) +
          ∫ r in Ioi 0, r ^ 3 * deriv u r ^ 2 := by
    calc
      _ = ∫ r in Ioi 0,
          (r * u r ^ 2 + 2 * (r ^ 2 * u r * deriv u r)) +
            r ^ 3 * deriv u r ^ 2 := by
        apply integral_congr_ae
        exact .of_forall fun r ↦ by cas
      _ = _ := by
        have hsum : IntegrableOn
            (fun r ↦ r * u r ^ 2 + 2 * (r ^ 2 * u r * deriv u r)) (Ioi 0) :=
          hlow.add (hcross.const_mul 2)
        rw [integral_add hsum h1,
          integral_add hlow (hcross.const_mul 2), integral_const_mul]
  rw [hexpand] at hnonneg
  exact ⟨hlow, by linarith⟩

/-- The integral of `r (2u + ru')²` on the positive half-line equals its
cubic-weighted derivative integral. Integrability and cancellation of the
cross term both follow from the two cubic moments. -/
theorem integral_Ioi_mul_two_mul_add_mul_deriv_sq_eq_integral_Ioi_cube_mul_deriv_sq
    {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    (h0 : IntegrableOn (fun r ↦ r ^ 3 * u r ^ 2) (Ioi 0))
    (h1 : IntegrableOn (fun r ↦ r ^ 3 * deriv u r ^ 2) (Ioi 0)) :
    IntegrableOn (fun r ↦ r * (2 * u r + r * deriv u r) ^ 2) (Ioi 0) ∧
      (∫ r in Ioi 0, r * (2 * u r + r * deriv u r) ^ 2) =
        ∫ r in Ioi 0, r ^ 3 * deriv u r ^ 2 := by
  obtain ⟨hlow, hcross, hidentity⟩ := radial_four_flux_identity hu h0 h1
  have hpoly (r : ℝ) :
      r * (2 * u r + r * deriv u r) ^ 2 =
        (4 * (r * u r ^ 2) + 4 * (r ^ 2 * u r * deriv u r)) +
          r ^ 3 * deriv u r ^ 2 := by cas
  have hint : IntegrableOn
      (fun r ↦ r * (2 * u r + r * deriv u r) ^ 2) (Ioi 0) := by
    refine ((hlow.const_mul 4).add (hcross.const_mul 4) |>.add h1).congr ?_
    exact .of_forall fun r ↦ (hpoly r).symm
  refine ⟨hint, ?_⟩
  calc
    _ = ∫ r in Ioi 0,
        (4 * (r * u r ^ 2) + 4 * (r ^ 2 * u r * deriv u r)) +
          r ^ 3 * deriv u r ^ 2 := integral_congr_ae (.of_forall hpoly)
    _ = 4 * (∫ r in Ioi 0, r * u r ^ 2) +
        4 * (∫ r in Ioi 0, r ^ 2 * u r * deriv u r) +
          ∫ r in Ioi 0, r ^ 3 * deriv u r ^ 2 := by
      have hsum : IntegrableOn
          (fun r ↦ 4 * (r * u r ^ 2) + 4 * (r ^ 2 * u r * deriv u r)) (Ioi 0) :=
        (hlow.const_mul 4).add (hcross.const_mul 4)
      rw [integral_add hsum h1,
        integral_add (hlow.const_mul 4) (hcross.const_mul 4),
        integral_const_mul, integral_const_mul]
    _ = _ := by rw [hidentity]; cas

end Hardy

end SobolevSpace
