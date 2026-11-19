/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.RadialCutoff

/-!
# Quantitative cutoffs on translated balls

The explicit radial bump is one on the closed ball of radius R and supported
in the closed ball of radius 2R. Translation preserves its derivative bounds, and a
cutoff centered at the origin is invariant under every coordinate reflection.
For each derivative word, one constant works for all centers and positive radii.
Thus choosing two such cutoffs at radii R and 3R supplies nested localization
with first and second derivative bounds of order R⁻¹ and R⁻².
-/

@[expose] public noncomputable section

open PDE (partialDeriv iteratedPartialDeriv)

open Set Metric TopologicalSpace
open scoped Distributions

namespace SobolevSpace.Approximation

variable {n : ℕ}

/-- Translation commutes with every iterated coordinate derivative, including
the totalized derivative of a function that need not be differentiable. -/
theorem iteratedPartialDeriv_comp_sub
    (α : List (Fin n)) (f : ℝ^n → ℝ) (a x : ℝ^n) :
    iteratedPartialDeriv α (fun y ↦ f (y - a)) x =
      iteratedPartialDeriv α f (x - a) := by
  induction α generalizing x with
  | nil => rfl
  | cons i α ih =>
    simp only [iteratedPartialDeriv, ih, partialDeriv, fderiv_comp_sub]

/-- The radial radius-`R` cutoff, translated to `a`, as a compact test function. -/
def ballCutoff (a : ℝ^n) {R : ℝ} (hR : 0 < R) :
    𝓓((⊤ : Opens (ℝ^n)), ℝ) where
  toFun x := radialCutoff R (x - a)
  contDiff' := (radialCutoff_contDiff R).comp (contDiff_id.sub contDiff_const)
  hasCompactSupport' :=
    (radialCutoff_hasCompactSupport hR).comp_homeomorph (Homeomorph.subRight a)
  tsupport_subset' := subset_univ _

attribute [inherit_doc ballCutoff] ballCutoff.eq_1

/-- The translated cutoff takes values in [0,1]. -/
theorem ballCutoff_mem_Icc (a x : ℝ^n) {R : ℝ} (hR : 0 < R) :
    ballCutoff a hR x ∈ Icc (0 : ℝ) 1 :=
  radialCutoff_mem_Icc R (x - a)

/-- The translated cutoff equals one throughout the closed inner ball. -/
theorem ballCutoff_eq_one (a : ℝ^n) {R : ℝ} (hR : 0 < R)
    {x : ℝ^n} (hx : x ∈ closedBall a R) :
    ballCutoff a hR x = 1 := by
  apply radialCutoff_eq_one hR
  simpa only [mem_closedBall, dist_eq_norm] using hx

/-- A ball cutoff centered at the origin is unchanged by any coordinate reflection. -/
theorem ballCutoff_zero_even (i : Fin n) {R : ℝ} (hR : 0 < R) :
    PDE.Common.IsEvenUnderCoordinateReflection i
      (ballCutoff (0 : ℝ^n) hR : ℝ^n → ℝ) := by
  intro x
  change radialCutoff R (PDE.Common.coordinateReflection i x - 0) =
    radialCutoff R (x - 0)
  simpa only [sub_zero] using radialCutoff_even R i x

/-- The support of the translated radius-R cutoff lies in the closed ball of
radius 2R. In particular it is compactly contained in every larger open ball. -/
theorem tsupport_ballCutoff_subset (a : ℝ^n) {R : ℝ} (hR : 0 < R) :
    tsupport (ballCutoff a hR).toFun ⊆ closedBall a (2 * R) := by
  apply closure_minimal ?_ isClosed_closedBall
  intro x hx
  have hb : x - a ∈ tsupport (radialCutoff R) :=
    subset_tsupport _ (show radialCutoff R (x - a) ≠ 0 from hx)
  simpa only [mem_closedBall, dist_eq_norm, sub_zero] using
    tsupport_radialCutoff_subset hR hb

/-- Each derivative word has a bound uniform in the center and positive
radius. The radius occurs only as R raised to minus the derivative order. -/
theorem exists_abs_iteratedPartialDeriv_ballCutoff_le (α : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ^n) (R : ℝ) (hR : 0 < R) (x : ℝ^n),
      |iteratedPartialDeriv α (ballCutoff a hR).toFun x| ≤ C * R⁻¹ ^ α.length := by
  obtain ⟨C, hC, hbound⟩ := exists_radialCutoff_derivative_bound α
  refine ⟨C, hC, ?_⟩
  intro a R hR x
  change |iteratedPartialDeriv α (fun y ↦ radialCutoff R (y - a)) x| ≤ _
  rw [iteratedPartialDeriv_comp_sub]
  exact hbound R hR (x - a)

/-- Two nested cutoffs have first derivative bounds A/R and diagonal second
derivative bounds B/R², with A and B depending only on the dimension and
the fixed bump. They equal one on balls of radii R and 3R and are supported
in the corresponding balls of radii 2R and 6R. -/
theorem exists_nested_ball_cutoffs :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (a : ℝ^n) (R : ℝ), 0 < R →
        ∃ χ η : 𝓓((⊤ : Opens (ℝ^n)), ℝ),
          tsupport χ.toFun ⊆ closedBall a (2 * R) ∧
          tsupport η.toFun ⊆ closedBall a (6 * R) ∧
          (∀ x ∈ closedBall a R, χ x = 1) ∧
          (∀ x ∈ closedBall a (3 * R), η x = 1) ∧
          (∀ x, |χ x| ≤ 1 ∧ |η x| ≤ 1) ∧
          (∀ (i : Fin n) x,
            |(∂[i] χ.toFun) x| ≤ A * R⁻¹ ∧
            |(∂[i] η.toFun) x| ≤ A * R⁻¹) ∧
          (∀ (i : Fin n) x,
            |(∂[i] (∂[i] χ.toFun)) x| ≤ B * R⁻¹ ^ 2) := by
  classical
  choose C hC hfirst using
    fun i : Fin n ↦ exists_abs_iteratedPartialDeriv_ballCutoff_le [i]
  choose D hD hsecond using
    fun i : Fin n ↦ exists_abs_iteratedPartialDeriv_ballCutoff_le [i, i]
  let A := ∑ i : Fin n, C i
  let B := ∑ i : Fin n, D i
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ ↦ hC i
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ ↦ hD i
  have hCA (i : Fin n) : C i ≤ A :=
    Finset.single_le_sum (fun j _ ↦ hC j) (Finset.mem_univ i)
  have hDB (i : Fin n) : D i ≤ B :=
    Finset.single_le_sum (fun j _ ↦ hD j) (Finset.mem_univ i)
  refine ⟨A, B, hA, hB, ?_⟩
  intro a R hR
  have h3R : 0 < 3 * R := by positivity
  refine ⟨ballCutoff a hR, ballCutoff a h3R, tsupport_ballCutoff_subset a hR, ?_,
    fun x hx ↦ ballCutoff_eq_one a hR hx,
    fun x hx ↦ ballCutoff_eq_one a h3R hx, ?_, ?_, ?_⟩
  · simpa only [← mul_assoc, show (2 : ℝ) * 3 = 6 by norm_num] using
      tsupport_ballCutoff_subset a h3R
  · intro x
    have hχ := ballCutoff_mem_Icc a x hR
    have hη := ballCutoff_mem_Icc a x h3R
    exact ⟨(abs_of_nonneg hχ.1).trans_le hχ.2, (abs_of_nonneg hη.1).trans_le hη.2⟩
  · intro i x
    have hχ : |(∂[i] (ballCutoff a hR).toFun) x| ≤ C i * R⁻¹ := by
      simpa only [iteratedPartialDeriv, List.length_cons, List.length_nil,
        Nat.zero_add, pow_one] using hfirst i a R hR x
    have hη : |(∂[i] (ballCutoff a h3R).toFun) x| ≤ C i * (3 * R)⁻¹ := by
      simpa only [iteratedPartialDeriv, List.length_cons, List.length_nil,
        Nat.zero_add, pow_one] using hfirst i a (3 * R) h3R x
    refine ⟨hχ.trans (mul_le_mul_of_nonneg_right (hCA i) (inv_nonneg.mpr hR.le)), ?_⟩
    apply hη.trans
    apply mul_le_mul (hCA i) ?_ (inv_nonneg.mpr h3R.le) hA
    exact (inv_le_inv₀ h3R hR).mpr (by linarith)
  · intro i x
    have hχ : |(∂[i] (∂[i] (ballCutoff a hR).toFun)) x| ≤
        D i * R⁻¹ ^ 2 := by
      simpa only [iteratedPartialDeriv, List.length_cons, List.length_nil,
        Nat.zero_add, Nat.reduceAdd] using hsecond i a R hR x
    exact hχ.trans (mul_le_mul_of_nonneg_right (hDB i) (sq_nonneg _))

end SobolevSpace.Approximation
