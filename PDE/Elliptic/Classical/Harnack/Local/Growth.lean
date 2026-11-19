/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Contact.Boundary
public import PDE.Analysis.MeasureTheory.Contact.Image
public import PDE.Elliptic.Classical.Harnack.Local.Barrier
public import PDE.Elliptic.Classical.Harnack.Local.ContactJacobian
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Localized low-level measure for elliptic supersolutions

A small value anywhere in the half ball forces low-level mass in a prescribed
concentric inner ball. A normalized Gaussian barrier makes the perturbed function
negative at the reference point. Its strictly negative residual outside the inner
ball excludes contacts there. The remaining contact image gives the measure bound.

The constants are chosen before the supersolution, from radii and coefficient
bounds alone. No local PDE estimate is an input.
-/

@[expose] public section

noncomputable section

namespace EllipticHarnack

open PDE.Analysis EllipticMaximum Set Metric MeasureTheory
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- Localized contact measure: the reference point lies in the half ball while
the controlled low-level mass lies in any prescribed positive-radius inner ball. -/
theorem exists_localized_sublevel_measure_bound
    {R ρ α τ B : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hα : 0 < α) :
    ∃ M D : ℝ, 0 < M ∧ 0 < D ∧
      ∀ (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n),
        (∀ x ∈ ball (0 : ℝ^n) R, (a x).PosSemidef) →
        (∀ x ∈ ball (0 : ℝ^n) R, ∀ v : ℝ^n,
          α * ‖v‖ ^ 2 ≤ ⟪v, (a x).toEuclideanLin v⟫) →
        (∀ x ∈ ball (0 : ℝ^n) R, (a x).trace ≤ τ) →
        (∀ x ∈ ball (0 : ℝ^n) R, ‖b x‖ ≤ B) →
        ∀ u : ℝ^n → ℝ, ContinuousOn u (closedBall 0 R) →
        (∀ x ∈ ball (0 : ℝ^n) R, ContDiffAt ℝ 2 u x) →
        (∀ x ∈ closedBall (0 : ℝ^n) R, 0 ≤ u x) →
        (∀ x ∈ ball (0 : ℝ^n) R, 0 ≤ matrixOperator a b (fun _ ↦ 0) u x) →
        ∀ x₀ ∈ closedBall (0 : ℝ^n) (R / 2), u x₀ ≤ 1 →
          volume (closedBall (0 : ℝ^n) (R / 2)) ≤
            ENNReal.ofReal D * volume (ball (0 : ℝ^n) ρ ∩ {x | u x ≤ M}) := by
  -- A negative trace or drift bound cannot hold at the centre: the statement is then vacuous.
  by_cases hτB : 0 ≤ τ ∧ 0 ≤ B
  swap
  · refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro a b ha _ htrace hdrift
    exfalso
    have hp : (0 : ℝ^n) ∈ ball (0 : ℝ^n) R := mem_ball_self hR
    rcases not_and_or.mp hτB with hτ | hB
    · exact hτ ((ha _ hp).trace_nonneg.trans (htrace _ hp))
    · exact hB ((norm_nonneg _).trans (hdrift _ hp))
  obtain ⟨hτ, hB⟩ := hτB
  obtain ⟨φ, M, F, κ, hφ, hM, _, hκ, hscale, hφbound, hφlow, hφboundary, hbarrier⟩ :=
    exists_barrier_for_contact_localization (n := n) hR hρ hα hτ hB
  let D := max 1 (((τ + B * (2 * R) + κ⁻¹ * F) / α) ^ n)
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨M, D, hM, hD, ?_⟩
  intro a b ha hell htrace hdrift
  obtain ⟨hφres, hφannulus⟩ := hbarrier a b ha hell htrace hdrift
  intro u hu hreg hnonneg hsuper x₀ hx₀ hsmall
  let w := fun x ↦ u x - φ x
  have hw : ContinuousOn w (closedBall 0 R) := hu.sub hφ.continuous.continuousOn
  have hwreg : ∀ x ∈ ball (0 : ℝ^n) R, ContDiffAt ℝ 2 w x :=
    fun x hx ↦ (hreg x hx).sub hφ.contDiffAt
  have hwboundary : ∀ x ∈ sphere (0 : ℝ^n) R, 0 ≤ w x := fun x hx ↦ by
    simpa [w, hφboundary x hx] using hnonneg x (sphere_subset_closedBall hx)
  have hwsmall : w x₀ ≤ -1 := by
    dsimp only [w]
    linarith [hφlow x₀ hx₀]
  let K := closedBall (0 : ℝ^n) R ∩ {x | w x ≤ -(1 / 2)}
  let S := quadraticContactSet w κ (closedBall 0 R) K (closedBall 0 (R / 2))
  have hKinside : K ⊆ ball (0 : ℝ^n) R :=
    negative_sublevel_closedBall_subset_ball (by norm_num) hwboundary
  have hcompact : IsCompact S :=
    isCompact_quadraticContactSet (isCompact_sublevel_closedBall hw) isClosed_closedBall
      (hw.mono inter_subset_left) (fun x hx ↦
        (contDiffAt_gradient (m := 1) (hwreg x (hKinside hx))).continuousAt.continuousWithinAt)
  have hcover : closedBall (0 : ℝ^n) (R / 2) ⊆ quadraticContactMap w κ '' S :=
    closedBall_subset_image_quadraticContactMap_of_boundary_nonneg hR hκ hscale hw
      (fun x hx ↦ ((hwreg x hx).differentiableAt (by norm_num)).differentiableWithinAt)
      hwboundary hx₀ hwsmall
  have hlocal (x : ℝ^n) (hx : x ∈ S) :
      IsLocalMin (quadraticTilt w κ (quadraticContactMap w κ x)) x :=
    isLocalMin_quadraticTilt_of_mem_contactSet hx
      (closedBall_mem_nhds_of_mem (hKinside hx.1))
  have hdist (x : ℝ^n) (hx : x ∈ S) : ‖quadraticContactMap w κ x - x‖ ≤ 2 * R := by
    linarith [norm_sub_le (quadraticContactMap w κ x) x, mem_closedBall_zero_iff.1 hx.1.1,
      mem_closedBall_zero_iff.1 hx.2.1]
  have hwres (x : ℝ^n) (hx : x ∈ ball (0 : ℝ^n) R) :
      -matrixOperator a b (fun _ ↦ 0) φ x ≤ matrixOperator a b (fun _ ↦ 0) w x := by
    rw [matrixOperator_sub a b (fun _ ↦ 0) (hreg x hx) hφ.contDiffAt]
    linarith [hsuper x hx]
  have hsubset : S ⊆ ball (0 : ℝ^n) ρ ∩ {x | u x ≤ M} := fun x hx ↦ by
    have hxR := hKinside hx.1
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_zero_right]
      by_contra hnot
      have hnegative := hφannulus x hxR (le_of_not_gt hnot)
      have hp := isPositive_fderiv_quadraticContactMap (hwreg x hxR) hκ (hlocal x hx)
      have ht := trace_fderiv_quadraticContactMap_le a b (hwreg x hxR) hκ hα
        (hell x hxR) (htrace x hxR) (hdrift x hxR) (hdist x hx) (hwres x hxR)
        (hlocal x hx)
      have hnum : 0 ≤ τ + B * (2 * R) + κ⁻¹ * matrixOperator a b (fun _ ↦ 0) φ x :=
        (mul_nonneg hp.trace_nonneg hα.le).trans ((le_div_iff₀ hα).mp ht)
      have hscaled := mul_nonneg hκ.le hnum
      rw [mul_add, ← mul_assoc κ κ⁻¹, mul_inv_cancel₀ hκ.ne', one_mul] at hscaled
      linarith
    · have hwlow : u x - φ x ≤ -(1 / 2) := hx.1.2
      change u x ≤ M
      linarith [hφbound x]
  have hderiv : ∀ x ∈ S, HasFDerivWithinAt (quadraticContactMap w κ)
      (fderiv ℝ (quadraticContactMap w κ) x) S x := fun x hx ↦
    (hasFDerivAt_quadraticContactMap (hwreg x (hKinside hx.1)) κ).differentiableAt
      |>.hasFDerivAt.hasFDerivWithinAt
  have hdet : ∀ x ∈ S, |(fderiv ℝ (quadraticContactMap w κ) x).det| ≤ D := fun x hx ↦ by
    have hxR := hKinside hx.1
    exact (abs_det_fderiv_quadraticContactMap_le a b (hwreg x hxR) hκ hα
      (hell x hxR) (htrace x hxR) (hdrift x hxR) (hdist x hx)
      ((neg_le_neg (hφres x hxR)).trans (hwres x hxR)) (hlocal x hx)).trans
        (le_max_right _ _)
  apply (measure_le_mul_measure_of_subset_differentiable_image volume hcompact.measurableSet
    hderiv hcover hdet).trans
  gcongr

end EllipticHarnack
