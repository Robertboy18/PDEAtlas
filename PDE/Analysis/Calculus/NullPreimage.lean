/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Derivatives above null target sets

The one-dimensional Luzin principle behind nonsmooth chain rules: the
derivative of a measurable real function vanishes almost everywhere where the
function takes values in a null set.

The proof applies Mathlib's differentiability partition,
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`, to the set where the function
takes values in the null set and has nonzero derivative. On each piece the function is
approximated by a nonzero linear map with an error constant below its slope, and is therefore
injective. Mathlib's one-dimensional change of variables formula,
`lintegral_image_eq_lintegral_abs_deriv_mul`, then shows that the integral of `|f'|` over each
piece is the measure of its image, which lies in the null set, so the piece is null.

## Main results

* `ae_deriv_eq_zero_on_preimage_null`: if `f : ℝ → ℝ` is measurable and `N` is a measurable
  null set, then `deriv f x = 0` for almost every `x` with `f x ∈ N`.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal NNReal

namespace PDE.Analysis.Calculus

private def derivativePartitionRadius (A : ℝ →L[ℝ] ℝ) : ℝ≥0 :=
  ⟨if A 1 = 0 then 1 else ‖A 1‖ / 2, by positivity⟩

private theorem derivativePartitionRadius_ne_zero (A : ℝ →L[ℝ] ℝ) :
    derivativePartitionRadius A ≠ 0 := by
  apply ne_of_gt
  change 0 < if A 1 = 0 then (1 : ℝ) else ‖A 1‖ / 2
  split_ifs with h
  · norm_num
  · exact half_pos (norm_pos_iff.mpr h)

private theorem derivativePartitionRadius_lt (A : ℝ →L[ℝ] ℝ)
    (hA : A 1 ≠ 0) :
    (derivativePartitionRadius A : ℝ) < ‖A 1‖ := by
  change (if A 1 = 0 then (1 : ℝ) else ‖A 1‖ / 2) < ‖A 1‖
  rw [ite_eq_right hA]
  exact half_lt_self (norm_pos_iff.mpr hA)

private theorem injOn_of_approximates_scalar
    {f : ℝ → ℝ} {A : ℝ →L[ℝ] ℝ} {s : Set ℝ} {c : ℝ≥0}
    (h : ApproximatesLinearOn f A s c) (hc : (c : ℝ) < ‖A 1‖) :
    Set.InjOn f s := by
  intro x hx y hy hxy
  have hbound := h x hx y hy
  have hmap : A (x - y) = (x - y) * A 1 := by
    rw [← smul_eq_mul, ← map_smul]
    simp
  rw [hxy, sub_self, zero_sub, norm_neg, hmap, norm_mul,
    Real.norm_eq_abs] at hbound
  by_contra hne
  have habs : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  exact (not_lt_of_ge hbound) (by
    simpa [mul_comm] using mul_lt_mul_of_pos_left hc habs)

/-- The derivative of a measurable real function vanishes almost everywhere
over the preimage of every Lebesgue-null measurable target set. -/
theorem ae_deriv_eq_zero_on_preimage_null
    {f : ℝ → ℝ} (hf : Measurable f) {N : Set ℝ}
    (hN : MeasurableSet N) (hN0 : volume N = 0) :
    ∀ᵐ x, f x ∈ N → deriv f x = 0 := by
  let s : Set ℝ := f ⁻¹' N ∩ {x | deriv f x ≠ 0}
  have hs : MeasurableSet s := by
    apply (hN.preimage hf).inter
    have hset : {x | deriv f x ≠ 0} = (deriv f ⁻¹' {0})ᶜ := by
      ext x
      simp
    rw [hset]
    exact ((measurable_deriv f) (measurableSet_singleton (0 : ℝ))).compl
  by_cases hsne : s.Nonempty
  · obtain ⟨t, A, -, htmeas, htcover, htapprox, htvalue⟩ :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt
        f s (fderiv ℝ f)
        (fun x hx ↦
          (differentiableAt_of_deriv_ne_zero hx.2).hasFDerivAt.hasFDerivWithinAt)
        derivativePartitionRadius derivativePartitionRadius_ne_zero
    have hpiece : ∀ n, volume (s ∩ t n) = 0 := by
      intro n
      rcases htvalue hsne n with ⟨y, hy, hAy⟩
      have hAone : A n 1 ≠ 0 := by
        rw [hAy, fderiv_apply_one_eq_deriv]
        exact hy.2
      have hinj : Set.InjOn f (s ∩ t n) :=
        injOn_of_approximates_scalar
          (htapprox n) (derivativePartitionRadius_lt _ hAone)
      have himage : volume (f '' (s ∩ t n)) = 0 := by
        apply le_antisymm
        · refine (measure_mono ?_).trans (le_of_eq hN0)
          exact image_subset_iff.mpr fun _ hx ↦ hx.1.1
        · exact bot_le
      have hchange :=
        lintegral_image_eq_lintegral_abs_deriv_mul
          (hs.inter (htmeas n))
          (fun x hx ↦
            (differentiableAt_of_deriv_ne_zero hx.1.2).hasDerivAt.hasDerivWithinAt)
          hinj (fun _ ↦ 1)
      have hintegral :
          ∫⁻ x in s ∩ t n, ENNReal.ofReal |deriv f x| = 0 := by
        calc
          ∫⁻ x in s ∩ t n, ENNReal.ofReal |deriv f x| =
              ∫⁻ x in s ∩ t n, ENNReal.ofReal |deriv f x| * 1 := by simp
          _ = ∫⁻ x in f '' (s ∩ t n), 1 := hchange.symm
          _ = 0 := by simp [himage]
      have hae :
          ∀ᵐ x, x ∈ s ∩ t n → ENNReal.ofReal |deriv f x| = 0 :=
        (setLIntegral_eq_zero_iff (hs.inter (htmeas n))
          ((measurable_deriv f).norm.ennreal_ofReal)).mp hintegral
      exact measure_eq_zero_iff_ae_notMem.mpr <| hae.mono fun x hx hmem ↦ by
        have hzero : deriv f x = 0 := by
          have := hx hmem
          simpa [ENNReal.ofReal_eq_zero, abs_nonpos_iff] using this
        exact hmem.1.2 hzero
    have hs0 : volume s = 0 := by
      apply le_antisymm
      · calc
          volume s ≤ volume (⋃ n, s ∩ t n) := measure_mono <| by
            rw [← inter_iUnion]
            exact subset_inter Subset.rfl htcover
          _ = 0 := measure_iUnion_null hpiece
      · exact bot_le
    exact (measure_eq_zero_iff_ae_notMem.mp hs0).mono fun x hx hfxN ↦ by
      by_contra hderiv
      exact hx ⟨hfxN, hderiv⟩
  · have hs0 : s = ∅ := not_nonempty_iff_eq_empty.mp hsne
    filter_upwards with x hfxN
    by_contra hderiv
    have : x ∈ s := ⟨hfxN, hderiv⟩
    simp [hs0] at this

end PDE.Analysis.Calculus
