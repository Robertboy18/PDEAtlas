/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Calculus of absolutely continuous paths in finite dimension

The scalar fundamental theorem of calculus applies to every coordinate of
an absolutely continuous path. A finite basis then reconstructs its actual
vector derivative almost everywhere, its integrability, and its integral.
The resulting displacement identity needs no assumptions on a particular
differential equation or variational problem.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open MeasureTheory Module Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem absolutelyContinuous_coord {ι : Type*} [Finite ι]
    (b : Basis ι ℝ E) {γ : ℝ → E} {a t : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a t) (i : ι) :
    AbsolutelyContinuousOnInterval (fun s ↦ b.repr (γ s) i) a t := by
  let := Fintype.ofFinite ι
  exact ((ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap).lipschitzWith
    |>.comp_absolutelyContinuousOnInterval hγ

private theorem deriv_eq_sum_ae {ι : Type*} [Fintype ι]
    (b : Basis ι ℝ E) {γ : ℝ → E} {a t : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a t) :
    ∀ᵐ s ∂volume, s ∈ uIcc a t →
      deriv γ s = ∑ i, deriv (fun r ↦ b.repr (γ r) i) s • b i := by
  have hc := ae_all_iff.mpr fun i ↦ (absolutelyContinuous_coord b hγ i).ae_differentiableAt
  filter_upwards [hc] with s hs hst
  have hd := HasDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) ↦
    ((hs i hst).hasDerivAt.smul_const (b i))
  have heq : (fun r ↦ ∑ i, b.repr (γ r) i • b i) = γ := by
    funext r
    exact b.sum_repr (γ r)
  rw [heq] at hd
  exact hd.deriv

variable [FiniteDimensional ℝ E]

/-- In finite dimension, an absolutely continuous path has an integrable
vector derivative. This follows from scalar coordinate integrability. -/
theorem intervalIntegrable_deriv_of_absolutelyContinuous {γ : ℝ → E} {a t : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a t) :
    IntervalIntegrable (deriv γ) volume a t := by
  let b := Module.finBasis ℝ E
  have hi : IntervalIntegrable
      (fun s ↦ ∑ i, deriv (fun r ↦ b.repr (γ r) i) s • b i) volume a t := by
    convert (IntervalIntegrable.sum Finset.univ
      (f := fun i s ↦ deriv (fun r ↦ b.repr (γ r) i) s • b i)
      fun i _ ↦ (absolutelyContinuous_coord b hγ i).intervalIntegrable_deriv.smul_continuousOn
        continuous_const.continuousOn) using 1
    ext s
    simp only [Finset.sum_apply]
  apply hi.congr_ae
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [deriv_eq_sum_ae b hγ] with s hs hst
  exact (hs (uIoc_subset_uIcc hst)).symm

/-- The vector fundamental theorem of calculus for an absolutely continuous
path in any finite-dimensional real normed space. No displacement identity
or derivative integrability is assumed. -/
theorem integral_deriv_eq_sub_of_absolutelyContinuous {γ : ℝ → E} {a t : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a t) :
    ∫ s in a..t, deriv γ s = γ t - γ a := by
  let b := Module.finBasis ℝ E
  calc
    ∫ s in a..t, deriv γ s =
        ∫ s in a..t, ∑ i, deriv (fun r ↦ b.repr (γ r) i) s • b i := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [deriv_eq_sum_ae b hγ] with s hs hst
      exact hs (uIoc_subset_uIcc hst)
    _ = ∑ i, (b.repr (γ t) i - b.repr (γ a) i) • b i := by
      rw [intervalIntegral.integral_finsetSum]
      · congr 1
        funext i
        rw [intervalIntegral.integral_smul_const,
          (absolutelyContinuous_coord b hγ i).integral_deriv_eq_sub]
      · intro i _
        exact (absolutelyContinuous_coord b hγ i).intervalIntegrable_deriv.smul_continuousOn
          continuous_const.continuousOn
    _ = γ t - γ a := by
      simp_rw [sub_smul, Finset.sum_sub_distrib]
      rw [b.sum_repr, b.sum_repr]

end PDE.Analysis

end
