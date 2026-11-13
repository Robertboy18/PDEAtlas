/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.QuantitativeCutoff

/-!
# Positive bounded coefficient extensions on balls

A coefficient that is C1 and bounded below on a larger ball has a global
W¹,∞ extension with the same lower bound and the same value and first derivatives
on the inner ball. The extension is a compact perturbation of the constant floor.
This permits local use of Friedrichs commutators for weights that are singular
or unbounded elsewhere.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.Approximation

open GraphSpace

variable {n : ℕ}

/-- A finite or infinitely differentiable coefficient on a ball can be extended
as a compact perturbation of its lower bound, preserving that bound everywhere
and agreeing with the original coefficient on the closed inner ball. -/
theorem exists_contDiff_extension_with_floor
    {m : ℕ∞} (a : ℝ^n) {R : ℝ} (hR : 0 < R) (W : ℝ^n → ℝ) (c : ℝ)
    (hW : ContDiffOn ℝ m W (ball a (3 * R)))
    (hfloor : ∀ x ∈ ball a (3 * R), c ≤ W x) :
    ∃ g : ℝ^n → ℝ, ContDiff ℝ m g ∧
      HasCompactSupport (fun x ↦ g x - c) ∧
      (∀ x, c ≤ g x) ∧ EqOn g W (closedBall a R) := by
  let χ := ballCutoff a hR
  let f : ℝ^n → ℝ := fun x ↦ χ x * (W x - c)
  have hχ : ContDiff ℝ m χ := χ.contDiff.of_le (by simp)
  have hinside {x : ℝ^n} (hx : x ∈ tsupport χ.toFun) : x ∈ ball a (3 * R) :=
    closedBall_subset_ball (by linarith) (tsupport_ballCutoff_subset a hR hx)
  have hf : ContDiff ℝ m f := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport χ.toFun
    · exact hχ.contDiffAt.mul
        ((hW.contDiffAt (isOpen_ball.mem_nhds (hinside hx))).sub contDiffAt_const)
    · have hz : f =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
        filter_upwards [(isClosed_tsupport χ.toFun).isOpen_compl.mem_nhds hx] with y hy
        have hy0 : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
        simp only [f, hy0, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  have hfc : HasCompactSupport f := χ.hasCompactSupport.mul_right
  refine ⟨fun x ↦ c + f x, contDiff_const.add hf, ?_, ?_, ?_⟩
  · simpa only [add_sub_cancel_left] using hfc
  · intro x
    by_cases hx : x ∈ tsupport χ.toFun
    · exact le_add_of_nonneg_right
        (mul_nonneg (ballCutoff_mem_Icc a x hR).1 (sub_nonneg.mpr (hfloor x (hinside hx))))
    · have hx0 : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp only [f, hx0, zero_mul, add_zero, le_refl]
  · intro x hx
    simp only [f, χ, ballCutoff_eq_one a hR hx, one_mul, add_sub_cancel]

/-- A locally C1 coefficient admits a global W¹,∞ extension with its
original lower floor. On the inner open ball both the base row and every first
weak derivative agree almost everywhere with the original classical rows. -/
theorem exists_W1Top_extension_with_floor
    (a : ℝ^n) {R : ℝ} (hR : 0 < R) (W : ℝ^n → ℝ) (c : ℝ)
    (hW : ContDiffOn ℝ 1 W (ball a (3 * R)))
    (hfloor : ∀ x ∈ ball a (3 * R), c ≤ W x) :
    ∃ A : W^{1,∞}(ℝ^n),
      (∀ᵐ x ∂domainMeasure n univ,
        c ≤ (A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) x) ∧
      (∀ᵐ x ∂domainMeasure n univ, x ∈ ball a R →
        (A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) x = W x) ∧
      ∀ j : Fin n, ∀ᵐ x ∂domainMeasure n univ, x ∈ ball a R →
        (A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j) x = (∂[j] W) x := by
  obtain ⟨g, hg, hgc, hgf, hgeq⟩ :=
    exists_contDiff_extension_with_floor a hR W c hW hfloor
  have hsub : ContDiff ℝ 1 (fun x ↦ g x - c) := hg.sub contDiff_const
  have hbase : MemLp g ∞ (domainMeasure n univ) := by
    convert
      (memLp_top_const c (μ := domainMeasure n univ)).add
        (hsub.continuous.memLp_top_of_hasCompactSupport hgc (domainMeasure n univ)) using 1
    funext x
    dsimp only [Pi.add_apply]
    abel
  have hderiv (j : Fin n) : MemLp (∂[j] g) ∞ (domainMeasure n univ) := by
    have hc : HasCompactSupport (∂[j] (fun x ↦ g x - c)) :=
      hasCompactSupport_iteratedPartialDeriv hgc [j]
    have hm := (PDE.contDiff_partialDeriv_of_succ (m := 0) (i := j) hsub).continuous
      |>.memLp_top_of_hasCompactSupport (μ := domainMeasure n univ) hc
    have heq : ∂[j] (fun x ↦ g x - c) = ∂[j] g := by
      funext x
      rw [PDE.partialDeriv_sub (hg.differentiable (by norm_num) x) (differentiableAt_const c),
        PDE.partialDeriv_const, sub_zero]
    rwa [heq] at hm
  have hmem (α : DerivIndex n 1) :
      MemLp (iteratedPartialDeriv α.toList g) ∞ (domainMeasure n univ) := by
    rcases hword : α.toList with _ | ⟨j, rest⟩
    · exact hbase
    · have hlen := α.toList_length_le
      rw [hword] at hlen
      have hr : rest = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons] at hlen
        omega
      subst rest
      exact hderiv j
  let A := mkWkpSpaceOnOfContDiffMemLpFinite (Ω := univ) (k := 1) (p := ∞) g hg hmem
  have hA := mkWkpSpaceOnOfContDiffMemLpFinite_apply_ae
    (Ω := univ) (k := 1) (p := ∞) g hg hmem (baseIndex n 1)
  simp only [baseIndex_toList, iteratedPartialDeriv] at hA
  refine ⟨A, ?_, ?_, ?_⟩
  · filter_upwards [hA] with x hx
    exact (hgf x).trans hx.ge
  · filter_upwards [hA] with x hx
    intro hball
    exact hx.trans (hgeq (ball_subset_closedBall hball))
  · intro j
    have hdA := mkWkpSpaceOnOfContDiffMemLpFinite_apply_ae
      (Ω := univ) (k := 1) (p := ∞) g hg hmem (singleDerivIndex n j)
    simp only [singleDerivIndex_toList, iteratedPartialDeriv] at hdA
    filter_upwards [hdA] with x hx
    intro hball
    have heq : g =ᶠ[𝓝 x] W := by
      filter_upwards [isOpen_ball.mem_nhds hball] with y hy
      exact hgeq (ball_subset_closedBall hy)
    apply hx.trans
    exact congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L (EuclideanSpace.single j 1)) heq.fderiv_eq

end SobolevSpace.Approximation
