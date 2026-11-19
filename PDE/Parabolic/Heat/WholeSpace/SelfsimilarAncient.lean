/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarKernel
public import PDE.Analysis.Evolution.Semigroup.Duhamel.AncientStrong

/-!
# The actual projected free self-similar ancient operator

The free decay rate allows a singular exponential bound with every exponent
above `(2 - n) / 4`. Joint continuity of the actual kernel action supplies a
bounded Green operator on weighted Sobolev paths. Its values are fixed by the
actual Leray projection, and decoding gives the literal Bochner integral.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace IncompressibleFlow
open PDE.Analysis.Evolution
open scoped Sobolev Real Topology BoundedContinuousFunction

namespace HeatEquation.WholeSpace

variable {n k : ℕ}

/-- Absorb the constant term in a one-derivative smoothing bound into an
arbitrarily small positive exponential allowance. -/
theorem one_add_inv_sqrt_le_singular_exp {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) :
    1 + (Real.sqrt r)⁻¹ ≤
      (1 + (Real.sqrt (2 * δ))⁻¹) * r ^ (-(1 / 2 : ℝ)) * Real.exp (δ * r) := by
  have hsqrt := Real.sqrt_pos.2 hr
  have hg := mul_gaussian_le_inv_sqrt (c := δ) (r := Real.sqrt r) hδ
  rw [Real.sq_sqrt hr.le] at hg
  have hexp : Real.exp (-(δ * r)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hδ.le hr.le))
  have hscale : (1 + (Real.sqrt r)⁻¹) * Real.sqrt r = Real.sqrt r + 1 := by
    rw [add_mul, one_mul, inv_mul_cancel₀ hsqrt.ne']
  have hweighted : (1 + (Real.sqrt r)⁻¹) * Real.sqrt r * Real.exp (-(δ * r)) ≤
      1 + (Real.sqrt (2 * δ))⁻¹ := by
    rw [hscale, add_mul, one_mul]
    linarith
  rw [Real.rpow_neg hr.le, ← Real.sqrt_eq_rpow]
  apply (mul_le_mul_iff_of_pos_right
    (mul_pos hsqrt (Real.exp_pos (-(δ * r))))).1
  calc
    _ ≤ 1 + (Real.sqrt (2 * δ))⁻¹ := by
      simpa only [mul_assoc] using hweighted
    _ = _ := by
      rw [show ((1 + (Real.sqrt (2 * δ))⁻¹) * (Real.sqrt r)⁻¹ * Real.exp (δ * r)) *
          (Real.sqrt r * Real.exp (-(δ * r))) =
        (1 + (Real.sqrt (2 * δ))⁻¹) * ((Real.sqrt r)⁻¹ * Real.sqrt r) *
          (Real.exp (δ * r) * Real.exp (-(δ * r))) by ring]
      rw [inv_mul_cancel₀ hsqrt.ne', ← Real.exp_add, add_neg_cancel, Real.exp_zero]
      ring

/-- The singular smoothing constant retains the distance above the free decay exponent. -/
def singularSelfsimilarConstant (n k : ℕ) (ω : ℝ) : ℝ :=
  selfsimilarSmoothingConstant n k * (1 + (Real.sqrt (2 * (ω - ((2 : ℝ) - n) / 4)))⁻¹)

theorem singularSelfsimilarConstant_nonneg (n k : ℕ) (ω : ℝ) :
    0 ≤ singularSelfsimilarConstant n k ω := by
  exact mul_nonneg (selfsimilarSmoothingConstant_nonneg n k) (by positivity)

/-- The actual projected kernel has a singular bound above the free decay rate. -/
theorem norm_projectedSelfsimilarHeatGainKernel_le_singular_exp {ω r : ℝ}
    (hω : ((2 : ℝ) - n) / 4 < ω) (hr : 0 < r) :
    ‖projectedSelfsimilarHeatGainKernel n k r‖ ≤
      singularSelfsimilarConstant n k ω * r ^ (-(1 / 2 : ℝ)) * Real.exp (ω * r) := by
  have he : Real.exp (((2 : ℝ) - n) * r / 4) *
      Real.exp ((ω - ((2 : ℝ) - n) / 4) * r) = Real.exp (ω * r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ selfsimilarSmoothingConstant n k * Real.exp (((2 : ℝ) - n) * r / 4) *
        (1 + (Real.sqrt r)⁻¹) := norm_projectedSelfsimilarHeatGainKernel_le hr
    _ ≤ selfsimilarSmoothingConstant n k * Real.exp (((2 : ℝ) - n) * r / 4) *
        ((1 + (Real.sqrt (2 * (ω - ((2 : ℝ) - n) / 4)))⁻¹) *
          r ^ (-(1 / 2 : ℝ)) * Real.exp ((ω - ((2 : ℝ) - n) / 4) * r)) :=
      mul_le_mul_of_nonneg_left
        (one_add_inv_sqrt_le_singular_exp (sub_pos.mpr hω) hr)
        (mul_nonneg (selfsimilarSmoothingConstant_nonneg n k) (Real.exp_pos _).le)
    _ = _ := by
      unfold singularSelfsimilarConstant
      calc
        _ = (selfsimilarSmoothingConstant n k *
            (1 + (Real.sqrt (2 * (ω - ((2 : ℝ) - n) / 4)))⁻¹) *
            r ^ (-(1 / 2 : ℝ))) *
            (Real.exp (((2 : ℝ) - n) * r / 4) *
              Real.exp ((ω - ((2 : ℝ) - n) / 4) * r)) := by ring
        _ = _ := by rw [he]

/-- The actual free projected Green operator on exponentially weighted Sobolev paths. -/
def ancientSelfsimilarDuhamelOperator (n k : ℕ) (a η β ω : ℝ)
    (hω : ((2 : ℝ) - n) / 4 < ω) (hgap : ω < β) (hβ : 0 ≤ β) (hweight : η ≤ β) :
    (Iic a →ᵇ VectorH n k) →L[ℝ] (Iic a →ᵇ VectorH n (k + 1)) :=
  ancientDuhamelOperatorOfJoint (E := VectorH n (k + 1)) (F := VectorH n k)
    (α := 1 / 2) (ω := ω) (β := β) (η := η)
    (M := singularSelfsimilarConstant n k ω) (a := a)
    (K := projectedSelfsimilarHeatGainKernel n k) (by norm_num) hgap hweight hβ
    (singularSelfsimilarConstant_nonneg n k ω)
    (continuousOn_projectedSelfsimilarHeatGainKernel_apply (n := n) (k := k))
    (fun _ hr ↦ norm_projectedSelfsimilarHeatGainKernel_le_singular_exp (k := k) hω hr)

/-- The derived norm bound includes the exact Gamma mass and the gain in time weights. -/
theorem norm_ancientSelfsimilarDuhamelOperator_le (a η β ω : ℝ)
    (hω : ((2 : ℝ) - n) / 4 < ω) (hgap : ω < β) (hβ : 0 ≤ β) (hweight : η ≤ β) :
    ‖ancientSelfsimilarDuhamelOperator n k a η β ω hω hgap hβ hweight‖ ≤
      singularSelfsimilarConstant n k ω * smoothingMass (1 / 2) (β - ω) *
        Real.exp ((β - η) * a) :=
  norm_ancientDuhamelOperatorOfJoint_le
    (E := VectorH n (k + 1)) (F := VectorH n k) _ _ _ _ _ _ _

/-- The defining past integral is genuinely integrable for every lifted forcing. -/
theorem integrableOn_selfsimilarAncientLift {a β ω : ℝ}
    (hω : ((2 : ℝ) - n) / 4 < ω) (hgap : ω < β)
    (u : Iic a →ᵇ VectorH n k) (t : ℝ) :
    IntegrableOn
      (fun r ↦ projectedSelfsimilarHeatGainKernel n k r (ancientLift β u (t - r)))
      (Ioi 0) :=
  integrableOn_ancientLift_of_joint (E := VectorH n (k + 1)) (F := VectorH n k)
    (α := 1 / 2) (by norm_num) hgap
    (singularSelfsimilarConstant_nonneg n k ω)
    (continuousOn_projectedSelfsimilarHeatGainKernel_apply (n := n) (k := k))
    (fun _ hr ↦ norm_projectedSelfsimilarHeatGainKernel_le_singular_exp (k := k) hω hr) u t

/-- Decoding the weighted output gives the literal free projected Duhamel integral. -/
theorem ancientLift_ancientSelfsimilarDuhamelOperator (a η β ω : ℝ)
    (hω : ((2 : ℝ) - n) / 4 < ω) (hgap : ω < β) (hβ : 0 ≤ β) (hweight : η ≤ β)
    (u : Iic a →ᵇ VectorH n k) {t : ℝ} (ht : t ≤ a) :
    ancientLift η (ancientSelfsimilarDuhamelOperator n k a η β ω hω hgap hβ hweight u) t =
      ∫ r in Ioi (0 : ℝ),
        projectedSelfsimilarHeatGainKernel n k r (ancientLift β u (t - r)) := by
  change Real.exp (η * t) •
    ancientSelfsimilarDuhamelOperator n k a η β ω hω hgap hβ hweight u
      ⟨min t a, min_le_right _ _⟩ = _
  rw [ancientSelfsimilarDuhamelOperator, ancientDuhamelOperatorOfJoint_apply]
  simp only [min_eq_left ht, smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
    one_smul, ancientDuhamel]

/-- Every value of the weighted ancient output is fixed by the actual Leray projector. -/
theorem leraySobolev_ancientSelfsimilarDuhamelOperator (a η β ω : ℝ)
    (hω : ((2 : ℝ) - n) / 4 < ω) (hgap : ω < β) (hβ : 0 ≤ β) (hweight : η ≤ β)
    (u : Iic a →ᵇ VectorH n k) (t : Iic a) :
    leraySobolev n (k + 1)
        (ancientSelfsimilarDuhamelOperator n k a η β ω hω hgap hβ hweight u t) =
      ancientSelfsimilarDuhamelOperator n k a η β ω hω hgap hβ hweight u t := by
  rw [ancientSelfsimilarDuhamelOperator, ancientDuhamelOperatorOfJoint_apply, map_smul]
  congr 1
  rw [ancientDuhamel, ← (leraySobolev n (k + 1)).integral_comp_comm
    (integrableOn_selfsimilarAncientLift hω hgap u t)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun r ↦
    leraySobolev_projectedSelfsimilarHeatGainKernel r _

/-- The physical base field of every output is distributionally divergence free. -/
theorem ancientSelfsimilarDuhamelOperator_base_mem_solenoidal (a η β ω : ℝ)
    (hω : ((2 : ℝ) - n) / 4 < ω) (hgap : ω < β) (hβ : 0 ≤ β) (hweight : η ≤ β)
    (u : Iic a →ᵇ VectorH n k) (t : Iic a) :
    l2SobolevRow (baseIndex n (k + 1))
        (ancientSelfsimilarDuhamelOperator n k a η β ω hω hgap hβ hweight u t) ∈
      l2Solenoidal n := by
  have h := lerayProjection_mem n
    (l2SobolevRow (baseIndex n (k + 1))
      (ancientSelfsimilarDuhamelOperator n k a η β ω hω hgap hβ hweight u t))
  rwa [← l2SobolevRow_leraySobolev,
    leraySobolev_ancientSelfsimilarDuhamelOperator] at h

end HeatEquation.WholeSpace
