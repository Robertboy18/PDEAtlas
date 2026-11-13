/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.RegularLevel
public import PDE.FDeriv.PartialDeriv
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# A smooth nonconvex domain for constructed Green kernels

The annulus `1 < |p| < 2` is the positive set of the quartic
`-(|p|² - 1)(|p|² - 4)`. The differential of this function does not vanish on its zero
level, so the annulus has smooth graph boundary (`hasContDiffGraphBoundary_domain`). It
is bounded and not convex, and contains the poles `pole` and `otherPole`.
-/

@[expose] public noncomputable section

namespace PDE.Examples.GreenCorrectorAnnulus

open Set Metric SobolevSpace.Boundary

/-- A polynomial whose positive set is the annulus with radii one and two. -/
def defining (p : ℝ^2) : ℝ :=
  -((p 0 ^ 2 + p 1 ^ 2) - 1) * ((p 0 ^ 2 + p 1 ^ 2) - 4)

/-- The annulus, given by its strict polynomial inequality. -/
def domain : Set ℝ^2 := {p | 0 < defining p}

/-- The polynomial defining the annulus is smooth. -/
theorem contDiff_defining : ContDiff ℝ (⊤ : ℕ∞) defining := by
  unfold defining
  fun_prop

/-- The partial derivative `∂₀ defining = -2 (2|p|² - 5) p₀`. -/
theorem partialDeriv_defining_zero (p : ℝ^2) :
    (∂[0] defining) p = -2 * (2 * (p 0 ^ 2 + p 1 ^ 2) - 5) * p 0 := by
  unfold defining
  cas

/-- The partial derivative `∂₁ defining = -2 (2|p|² - 5) p₁`. -/
theorem partialDeriv_defining_one (p : ℝ^2) :
    (∂[1] defining) p = -2 * (2 * (p 0 ^ 2 + p 1 ^ 2) - 5) * p 1 := by
  unfold defining
  cas

/-- The polynomial inequality is exactly the open annulus condition. -/
theorem mem_domain_iff (p : ℝ^2) : p ∈ domain ↔ 1 < ‖p‖ ∧ ‖p‖ < 2 := by
  have hs : p 0 ^ 2 + p 1 ^ 2 = ‖p‖ ^ 2 := by
    simpa only [Fin.sum_univ_two] using (EuclideanSpace.real_norm_sq_eq p).symm
  change 0 < -((p 0 ^ 2 + p 1 ^ 2) - 1) * ((p 0 ^ 2 + p 1 ^ 2) - 4) ↔ _
  rw [hs]
  have hnorm := norm_nonneg p
  constructor
  · intro h
    constructor
    · by_contra! hle
      have hsle : ‖p‖ ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (‖p‖ ^ 2 - 1)]
    · by_contra! hle
      have hsge : 4 ≤ ‖p‖ ^ 2 := by nlinarith
      nlinarith [sq_nonneg (‖p‖ ^ 2 - 4)]
  · rintro ⟨h1, h2⟩
    have ha : 0 < ‖p‖ ^ 2 - 1 := by nlinarith
    have hb : 0 < 4 - ‖p‖ ^ 2 := by nlinarith
    nlinarith [mul_pos ha hb]

/-- The annulus is open. -/
theorem isOpen_domain : IsOpen domain :=
  isOpen_lt continuous_const contDiff_defining.continuous

/-- The annulus is bounded. -/
theorem isBounded_domain : Bornology.IsBounded domain :=
  isBounded_ball.subset (fun p hp ↦ show p ∈ ball (0 : ℝ^2) 2 from
    by simpa only [mem_ball, dist_zero_right] using ((mem_domain_iff p).mp hp).2)

/-- The defining function vanishes on the boundary of the annulus. -/
theorem defining_eq_zero_of_mem_frontier {p : ℝ^2} (hp : p ∈ frontier domain) :
    defining p = 0 :=
  (frontier_lt_subset_eq continuous_const contDiff_defining.continuous hp).symm

/-- The differential of the defining function is nonzero at every boundary point. -/
theorem fderiv_defining_ne_zero {p : ℝ^2} (hp : p ∈ frontier domain) :
    fderiv ℝ defining p ≠ 0 := by
  intro hzero
  have hd0 : (∂[0] defining) p = 0 := by
    unfold partialDeriv
    rw [hzero]
    rfl
  have hd1 : (∂[1] defining) p = 0 := by
    unfold partialDeriv
    rw [hzero]
    rfl
  rw [partialDeriv_defining_zero] at hd0
  rw [partialDeriv_defining_one] at hd1
  have hlevel := defining_eq_zero_of_mem_frontier hp
  have hs : p 0 ^ 2 + p 1 ^ 2 = 1 ∨ p 0 ^ 2 + p 1 ^ 2 = 4 := by
    have hprod : ((p 0 ^ 2 + p 1 ^ 2) - 1) * ((p 0 ^ 2 + p 1 ^ 2) - 4) = 0 := by
      simpa only [defining, neg_mul, neg_eq_zero] using hlevel
    rcases mul_eq_zero.mp hprod with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  rcases hs with hs | hs
  · rw [hs] at hd0 hd1
    have hp0 : p 0 = 0 := by linarith
    have hp1 : p 1 = 0 := by linarith
    norm_num [hp0, hp1] at hs
  · rw [hs] at hd0 hd1
    have hp0 : p 0 = 0 := by linarith
    have hp1 : p 1 = 0 := by linarith
    norm_num [hp0, hp1] at hs

/-- The annulus has smooth graph boundary, from the regular quartic level set. -/
theorem hasContDiffGraphBoundary_domain : HasContDiffGraphBoundary ⊤ domain :=
  hasContDiffGraphBoundary_of_regular_level contDiff_defining.contDiffOn isOpen_univ
    le_top (fun _ hp ↦ ⟨mem_univ _, defining_eq_zero_of_mem_frontier hp⟩)
    (fun _ hp ↦ fderiv_defining_ne_zero hp) (fun _ _ ↦ Iff.rfl)

/-- A pole displaced from the center of the missing disk. -/
def pole : ℝ^2 := EuclideanSpace.single 0 (3 / 2)

/-- The displaced pole is strictly inside the annulus. -/
theorem pole_mem : pole ∈ domain := by
  rw [mem_domain_iff]
  norm_num [pole]

/-- A second pole in a different coordinate direction. -/
def otherPole : ℝ^2 := EuclideanSpace.single 1 (3 / 2)

/-- The second pole also lies in the annulus. -/
theorem otherPole_mem : otherPole ∈ domain := by
  rw [mem_domain_iff]
  norm_num [otherPole]

/-- The annulus is not convex: opposite interior poles have the excluded origin
as their midpoint. -/
theorem not_convex_domain : ¬Convex ℝ domain := by
  intro hc
  have hneg : -pole ∈ domain := by
    rw [mem_domain_iff]
    simpa only [norm_neg] using (mem_domain_iff pole).mp pole_mem
  have hmid := hc pole_mem hneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have heq : (1 / 2 : ℝ) • pole + (1 / 2 : ℝ) • -pole = 0 := by simp
  rw [heq, mem_domain_iff] at hmid
  norm_num at hmid

end PDE.Examples.GreenCorrectorAnnulus
