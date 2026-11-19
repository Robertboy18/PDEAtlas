/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.RootFunctions
public import PDE.Analysis.Calculus.ZeroCrossing

/-!
# Roots of the azimuthal boundary function

The azimuthal Stokes modes of order `l` correspond to the positive zeros of
`boundaryFunction .azimuthal l`, which are the positive zeros of
`azimuthalBoundaryJ l α = l j_l(α) - α j_{l+1}(α) = α j_l'(α)`. We prove the two parts
of Lemma 5 of Hou, Wang and Yang that concern these roots.

* The product `α azimuthalBoundaryJ l α = α ^ 2 j_l'(α)` vanishes at the origin and has
  derivative `(l (l + 1) - α ^ 2) j_l(α)`, which is positive on `(0, √(l (l + 1)))`. Hence the
  first positive root exceeds `√(l (l + 1))` (`boundaryFunction_azimuthal_ne_zero_of_sq_le`),
  and for `l ≥ 100` there is no root in `(0, 100)`.
* At a root `α ≠ 0` the derivative satisfies
  `α (azimuthalBoundaryJ l)'(α) = (l (l + 1) - α ^ 2) j_l(α)`. Since roots lie beyond
  `√(l (l + 1))`, on an interval free of zeros of `j_l` the derivative has one sign at every
  root, so there is at most one root there (`azimuthal_root_unique`). Rolle's theorem applied
  to `j_l` gives a root between two consecutive zeros of `j_l`, so the roots interlace with
  the zeros of `j_l` (`existsUnique_azimuthal_root_of_consecutive`).

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 6.2, Lemma 5, p. 52, and
  Appendix E, proof of Lemma 5, pp. 65-67.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public section

open Set PDE.Analysis PDE.Analysis.SpecialFunctions

namespace PDE.Fluid.Stokes.Ball

/-- The derivative of `azimuthalBoundaryJ l` at a point `α ≠ 0` is
`(l ^ 2 / α - α) j_l(α) + j_{l+1}(α)`. -/
theorem hasDerivAt_azimuthalBoundaryJ {l : ℕ} {α : ℝ} (hα : α ≠ 0) :
    HasDerivAt (azimuthalBoundaryJ l)
      ((l ^ 2 / α - α) * sphericalBesselJ l α + sphericalBesselJ (l + 1) α) α := by
  have h : HasDerivAt (fun t ↦ (l : ℝ) * sphericalBesselJ l t - t * sphericalBesselJ (l + 1) t)
      _ α := ((hasDerivAt_sphericalBesselJ_of_ne_zero hα l).const_mul (l : ℝ)).sub
    ((hasDerivAt_id' α).mul (hasDerivAt_sphericalBesselJ_succ_of_ne_zero hα l))
  refine h.congr_deriv ?_
  field_simp
  ring

/-- At a zero `α ≠ 0` of `azimuthalBoundaryJ l`,
`(azimuthalBoundaryJ l)'(α) α = (l (l + 1) - α ^ 2) j_l(α)`. -/
theorem deriv_azimuthalBoundaryJ_mul_of_eq_zero {l : ℕ} {α : ℝ} (hα : α ≠ 0)
    (h : azimuthalBoundaryJ l α = 0) :
    deriv (azimuthalBoundaryJ l) α * α = (l * (l + 1) - α ^ 2) * sphericalBesselJ l α := by
  rw [(hasDerivAt_azimuthalBoundaryJ hα).deriv]
  rw [azimuthalBoundaryJ] at h
  have e : ((l : ℝ) ^ 2 / α - α) * α = l ^ 2 - α ^ 2 := by
    field_simp
  linear_combination sphericalBesselJ l α * e - h

/-- `azimuthalBoundaryJ l` is positive on `(0, √(l (l + 1))]`. -/
theorem azimuthalBoundaryJ_pos_of_sq_le {l : ℕ} {α : ℝ} (hα : 0 < α)
    (h : α ^ 2 ≤ l * (l + 1)) : 0 < azimuthalBoundaryJ l α := by
  have hF := hasDerivAt_sq_mul_deriv_sphericalBesselJ l
  have hmono : StrictMonoOn (fun y ↦ y ^ 2 * deriv (sphericalBesselJ l) y) (Icc 0 α) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 α)
      (fun t _ ↦ (hF t).continuousAt.continuousWithinAt) fun t ht ↦ ?_
    rw [interior_Icc] at ht
    rw [(hF t).deriv]
    have ht2 : t ^ 2 < α ^ 2 := by nlinarith [ht.1, ht.2]
    exact mul_pos (by linarith) (sphericalBesselJ_pos_of_sq_le ht.1 (by linarith))
  have h0 : (0 : ℝ) ^ 2 * deriv (sphericalBesselJ l) 0 <
      α ^ 2 * deriv (sphericalBesselJ l) α :=
    hmono ⟨le_rfl, hα.le⟩ ⟨hα.le, le_rfl⟩ hα
  rw [zero_pow two_ne_zero, zero_mul, sq, mul_assoc, mul_deriv_sphericalBesselJ] at h0
  exact pos_of_mul_pos_right h0 hα.le

/-- The azimuthal boundary function has no zero in `(0, √(l (l + 1))]` (Hou, Wang and Yang,
Lemma 5). -/
theorem boundaryFunction_azimuthal_ne_zero_of_sq_le {l : ℕ} {α : ℝ} (hα : 0 < α)
    (h : α ^ 2 ≤ l * (l + 1)) : boundaryFunction .azimuthal l α ≠ 0 := by
  rw [Ne, boundaryFunction_azimuthal_eq_zero_iff hα]
  exact (azimuthalBoundaryJ_pos_of_sq_le hα h).ne'

/-- For `l ≥ 100` the azimuthal boundary function has no zero in `(0, 100)`. -/
theorem boundaryFunction_azimuthal_ne_zero_of_hundred_le {l : ℕ} (hl : 100 ≤ l) {α : ℝ}
    (hα : 0 < α) (h : α < 100) : boundaryFunction .azimuthal l α ≠ 0 := by
  have hl' : (100 : ℝ) ≤ l := by exact_mod_cast hl
  exact boundaryFunction_azimuthal_ne_zero_of_sq_le hα (by nlinarith)

/-- A positive zero `α` of `azimuthalBoundaryJ l` satisfies `l (l + 1) < α ^ 2`. -/
theorem lt_sq_of_azimuthalBoundaryJ_eq_zero {l : ℕ} {α : ℝ} (hα : 0 < α)
    (h : azimuthalBoundaryJ l α = 0) : (l : ℝ) * (l + 1) < α ^ 2 := by
  by_contra hlt
  push Not at hlt
  exact (azimuthalBoundaryJ_pos_of_sq_le hα hlt).ne' h

/-- On an interval `(a, b)` with `a ≥ 0` that contains no zero of `j_l`, the azimuthal
boundary function has at most one zero (Hou, Wang and Yang, Lemma 5). -/
theorem azimuthal_root_unique {l : ℕ} {a b : ℝ} (ha : 0 ≤ a)
    (hne : ∀ x ∈ Set.Ioo a b, sphericalBesselJ l x ≠ 0) {x y : ℝ} (hx : x ∈ Set.Ioo a b)
    (hy : y ∈ Set.Ioo a b) (hfx : boundaryFunction .azimuthal l x = 0)
    (hfy : boundaryFunction .azimuthal l y = 0) : x = y := by
  have hpos : ∀ t ∈ Ioo a b, 0 < t := fun t ht ↦ ha.trans_lt ht.1
  rw [boundaryFunction_azimuthal_eq_zero_iff (hpos x hx)] at hfx
  rw [boundaryFunction_azimuthal_eq_zero_iff (hpos y hy)] at hfy
  have hd := differentiable_azimuthalBoundaryJ l
  have hc : ContinuousOn (azimuthalBoundaryJ l) (Ioo a b) := hd.continuous.continuousOn
  have hder : ∀ t ∈ Ioo a b, azimuthalBoundaryJ l t = 0 →
      deriv (azimuthalBoundaryJ l) t * t = (l * (l + 1) - t ^ 2) * sphericalBesselJ l t ∧
        (l : ℝ) * (l + 1) < t ^ 2 := fun t ht h0 ↦
    ⟨deriv_azimuthalBoundaryJ_mul_of_eq_zero (hpos t ht).ne' h0,
      lt_sq_of_azimuthalBoundaryJ_eq_zero (hpos t ht) h0⟩
  rcases sphericalBesselJ_pos_or_neg_of_forall_ne_zero hne with hj | hj
  · refine eq_of_deriv_pos_at_zeros (f := -azimuthalBoundaryJ l) ordConnected_Ioo hc.neg
      (fun t ht h0 ↦ ?_) hx hy (by simp [hfx]) (by simp [hfy])
    obtain ⟨hdt, hlt⟩ := hder t ht (neg_eq_zero.mp h0)
    refine ⟨(hd t).neg, ?_⟩
    rw [deriv.neg]
    have hjt := hj t ht
    have ht0 := hpos t ht
    nlinarith [mul_pos (sub_pos.mpr hlt) hjt]
  · refine eq_of_deriv_pos_at_zeros ordConnected_Ioo hc (fun t ht h0 ↦ ?_) hx hy hfx hfy
    obtain ⟨hdt, hlt⟩ := hder t ht h0
    refine ⟨hd t, ?_⟩
    have hjt := hj t ht
    have ht0 := hpos t ht
    nlinarith [mul_pos (sub_pos.mpr hlt) (neg_pos.mpr hjt)]

/-- Between two zeros `0 ≤ a < b` of `j_l` the azimuthal boundary function has a zero. -/
theorem exists_azimuthal_root_of_consecutive {l : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hja : sphericalBesselJ l a = 0) (hjb : sphericalBesselJ l b = 0) :
    ∃ α ∈ Set.Ioo a b, boundaryFunction .azimuthal l α = 0 := by
  obtain ⟨c, hc, hdc⟩ :=
    exists_deriv_eq_zero hab (continuous_sphericalBesselJ l).continuousOn (hja.trans hjb.symm)
  refine ⟨c, hc, ?_⟩
  rw [boundaryFunction_azimuthal_eq_zero_iff (ha.trans_lt hc.1), azimuthalBoundaryJ,
    ← mul_deriv_sphericalBesselJ, hdc, mul_zero]

/-- Between two consecutive zeros `0 ≤ a < b` of `j_l` the azimuthal boundary function has
exactly one zero (Hou, Wang and Yang, Lemma 5). -/
theorem existsUnique_azimuthal_root_of_consecutive {l : ℕ} {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hja : sphericalBesselJ l a = 0)
    (hjb : sphericalBesselJ l b = 0) (hne : ∀ x ∈ Set.Ioo a b, sphericalBesselJ l x ≠ 0) :
    ∃! α, α ∈ Set.Ioo a b ∧ boundaryFunction .azimuthal l α = 0 := by
  obtain ⟨α, hα, hfα⟩ := exists_azimuthal_root_of_consecutive ha hab hja hjb
  exact ⟨α, ⟨hα, hfα⟩, fun β hβ ↦ azimuthal_root_unique ha hne hβ.1 hα hβ.2 hfα⟩

end PDE.Fluid.Stokes.Ball
