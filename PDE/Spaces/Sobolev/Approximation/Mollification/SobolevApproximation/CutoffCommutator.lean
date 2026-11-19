/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.CutoffJets

/-!
# Differentiated cutoff terms from lower weighted data

Every nonempty derivative of the radial cutoff is supported in the expanding
annulus. Its derivative order cancels the corresponding radial power in a
polynomial weight. A weighted square-integrable lower row therefore controls
the term, whose integral tends to zero by dominated convergence.

The row is an arbitrary measurable function, not a classical derivative of a
smooth source. In particular, this estimate applies to weak-derivative
representatives without assuming the global highest-order energy.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory Set SobolevSpace
open scoped Topology

namespace SobolevSpace.Approximation

variable {n : ℕ}

/-- A nonempty cutoff derivative times a lower row tends to zero in weighted
square integral. Only the exterior radial energy of that row is assumed.
The principal undifferentiated-cutoff term is excluded by `hβ`; hence this
statement requires no highest-order source energy or smooth representative. -/
theorem radialCutoff_derivative_mul_integral_convergence
    (β : List (Fin n)) (hβ : β ≠ []) (s : ℕ)
    {C L : ℝ} (hC : 0 ≤ C) {W v : ℝ^n → ℝ} {ν : Measure (ℝ^n)}
    (hW : AEStronglyMeasurable W ν) (hW0 : ∀ᵐ x ∂ν, 0 ≤ W x)
    (hv : AEStronglyMeasurable v ν)
    (htail : ∀ᵐ x ∂ν, L ≤ ‖x‖ →
      W x ≤ C * (‖x‖ ^ 2) ^ (β.length + s))
    (henergy : Integrable ({x | L ≤ ‖x‖}.indicator
      (fun x ↦ (‖x‖ ^ 2) ^ s * v x ^ 2)) ν) :
    (∀ R : ℝ, 0 < R → L ≤ R →
      Integrable (fun x ↦ W x *
        (iteratedPartialDeriv β (radialCutoff R) x * v x) ^ 2) ν) ∧
    Tendsto (fun R : ℝ ↦ ∫ x, W x *
      (iteratedPartialDeriv β (radialCutoff R) x * v x) ^ 2 ∂ν) atTop (𝓝 0) := by
  obtain ⟨B, hB, hbound⟩ := exists_radialCutoffJetError_scaled_bound β
  have hscaled (R : ℝ) (hR : 0 < R) (x : ℝ^n) :
      (‖x‖ ^ 2) ^ β.length * (iteratedPartialDeriv β (radialCutoff R) x) ^ 2 ≤ B := by
    simpa only [radialCutoffJetError, hβ, ↓reduceIte, sub_zero] using hbound R hR x
  let H : ℝ^n → ℝ := fun x ↦ C * B *
    {x | L ≤ ‖x‖}.indicator (fun x ↦ (‖x‖ ^ 2) ^ s * v x ^ 2) x
  have hH : Integrable H ν := henergy.const_mul (C * B)
  have hH0 (x : ℝ^n) : 0 ≤ H x := by
    exact mul_nonneg (mul_nonneg hC hB)
      (indicator_nonneg (fun y _ ↦ mul_nonneg (by positivity) (sq_nonneg _)) x)
  let F (R : ℝ) : ℝ^n → ℝ := fun x ↦ W x *
    (iteratedPartialDeriv β (radialCutoff R) x * v x) ^ 2
  have hFm (R : ℝ) : AEStronglyMeasurable (F R) ν := by
    have hd := (PDE.contDiff_top_iteratedPartialDeriv (radialCutoff_contDiff R) β).continuous
    exact hW.mul ((hd.aestronglyMeasurable.mul hv).pow 2)
  have hb (R : ℝ) (hR : 0 < R) (hLR : L ≤ R) :
      ∀ᵐ x ∂ν, ‖F R x‖ ≤ H x := by
    filter_upwards [hW0, htail] with x hx htx
    change ‖W x * _ ^ 2‖ ≤ H x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx (sq_nonneg _))]
    by_cases hin : ‖x‖ < R
    · rw [radialCutoff_derivative_zero_inside β hβ hR hin, zero_mul, zero_pow
        (by decide : 2 ≠ 0), mul_zero]
      exact hH0 x
    have hex : L ≤ ‖x‖ := hLR.trans (le_of_not_gt hin)
    change _ ≤ C * B * {x | L ≤ ‖x‖}.indicator
      (fun x ↦ (‖x‖ ^ 2) ^ s * v x ^ 2) x
    rw [indicator_of_mem (show x ∈ {x | L ≤ ‖x‖} from hex)]
    calc
      _ ≤ (C * (‖x‖ ^ 2) ^ (β.length + s)) *
          (iteratedPartialDeriv β (radialCutoff R) x * v x) ^ 2 :=
        mul_le_mul_of_nonneg_right (htx hex) (sq_nonneg _)
      _ = C * ((‖x‖ ^ 2) ^ β.length *
          (iteratedPartialDeriv β (radialCutoff R) x) ^ 2) *
          ((‖x‖ ^ 2) ^ s * v x ^ 2) := by
        rw [pow_add, mul_pow]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hscaled R hR x) hC) (by positivity)
  refine ⟨fun R hR hLR ↦ hH.mono' (hFm R) (hb R hR hLR), ?_⟩
  have hb' : ∀ᶠ R : ℝ in atTop, ∀ᵐ x ∂ν, ‖F R x‖ ≤ H x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop L] with R hR hLR
    exact hb R hR hLR
  have ht : ∀ᵐ x ∂ν, Tendsto (fun R : ℝ ↦ F R x) atTop (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop ‖x‖] with R hR
    simp only [F, radialCutoff_derivative_zero_inside β hβ
      ((norm_nonneg x).trans_lt hR) hR, zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero]
  simpa only [integral_zero] using
    tendsto_integral_filter_of_dominated_convergence H
      (Eventually.of_forall hFm) hb' hH ht

end SobolevSpace.Approximation
