/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.CoupledEnergy
public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.WeakJet

/-!
# Coupled H² production at weak spatial regularity

The one-dimensional weak Sobolev estimate controls the vorticity, its first
derivative, and the velocity gradient. Hilbert isometry controls the two higher
velocity derivatives in L². These bounds close the coupled H² production at
weak H² regularity.

For endpoint normalization, the rate is bounded by H¹ as well. The resulting
production constant is eleven times the H¹ size. The weak transport identity
`IsClassicalRescaledSolutionOn.exists_secondDerivative_energy` identifies this production
with the time derivative of the energy.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped ENNReal Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace PDE.Analysis

/-- Weak differentiation and Hilbert isometry give the pointwise Hilbert
bound from the input H¹ size. -/
theorem IsHilbertPair.norm_le_of_weak_derivative
    {w q h d : ℝ → ℝ} (hpair : IsHilbertPair w h) (hpair₁ : IsHilbertPair q d)
    (hwq : HasWeakTimeDerivativeOn univ w q) (hh : Continuous h) (x : ℝ) :
    ‖h x‖ ≤ lpNorm w 2 volume + lpNorm q 2 volume := by
  have h := (hpair.hasWeakTimeDerivativeOn hpair₁ hwq).norm_apply_le_eLpNorm_toReal_add
    hh (by norm_num) hpair.memLp_right hpair₁.memLp_right x
  rw [hpair.eLpNorm_eq, hpair₁.eLpNorm_eq] at h
  exact h

end PDE.Analysis

namespace DeGregorio

/-- H¹ bounds the full coupled H² production for weak derivative jets.
The second vorticity derivative and third velocity derivative are only L². -/
theorem norm_integral_coupled_rescaled_weak_production_le
    {w q r h d s : ℝ → ℝ} (ρ : ℝ)
    (hw : Continuous w) (hq : Continuous q) (hh : Continuous h)
    (hwq : HasWeakTimeDerivativeOn univ w q)
    (hqr : HasWeakTimeDerivativeOn univ q r)
    (hpair : IsHilbertPair w h) (hpair₁ : IsHilbertPair q d) (hpair₂ : IsHilbertPair r s) :
    ‖∫ x,
      3 * (ρ + h x) * w x ^ 2 + (ρ + h x) * q x ^ 2 -
        (ρ + h x) * r x ^ 2 + 2 * d x * w x * q x +
        2 * s x * w x * r x + 2 * d x * q x * r x‖ ≤
      (3 * |ρ| + 8 * (lpNorm w 2 volume + lpNorm q 2 volume)) *
        ((∫ x, w x ^ 2) + (∫ x, q x ^ 2) + ∫ x, r x ^ 2) :=
  norm_integral_coupled_rescaled_jet_production_le ρ hw hq hh hpair hpair₁ hpair₂
    (hwq.norm_apply_le_eLpNorm_toReal_add hw (by norm_num)
      hpair.memLp_left hpair₁.memLp_left)
    (hqr.norm_apply_le_eLpNorm_toReal_add hq (by norm_num)
      hpair₁.memLp_left hpair₂.memLp_left)
    (hpair.norm_le_of_weak_derivative hpair₁ hwq hh)

/-- The nonconservative source in the second differentiated transport
equation is L² at weak H² regularity. The required bounded multipliers
follow from one-dimensional weak Sobolev estimates. -/
theorem memLp_secondDerivative_source_of_weak_jet
    {w q r h d s : ℝ → ℝ} (ρ : ℝ)
    (hw : Continuous w) (hq : Continuous q) (hh : Continuous h)
    (hwq : HasWeakTimeDerivativeOn univ w q)
    (hqr : HasWeakTimeDerivativeOn univ q r)
    (hpair : IsHilbertPair w h) (hpair₁ : IsHilbertPair q d) (hpair₂ : IsHilbertPair r s) :
    MemLp (fun x ↦ -(ρ + h x) * r x + s x * w x + d x * q x) 2 volume := by
  have hW := memLp_top_of_bound (μ := volume) hw.aestronglyMeasurable
    (lpNorm w 2 volume + lpNorm q 2 volume)
    (Eventually.of_forall (hwq.norm_apply_le_eLpNorm_toReal_add hw (by norm_num)
      hpair.memLp_left hpair₁.memLp_left))
  have hQ := memLp_top_of_bound (μ := volume) hq.aestronglyMeasurable
    (lpNorm q 2 volume + lpNorm r 2 volume)
    (Eventually.of_forall (hqr.norm_apply_le_eLpNorm_toReal_add hq (by norm_num)
      hpair₁.memLp_left hpair₂.memLp_left))
  have hH := memLp_top_of_bound (μ := volume) hh.aestronglyMeasurable
    (lpNorm w 2 volume + lpNorm q 2 volume)
    (Eventually.of_forall (hpair.norm_le_of_weak_derivative hpair₁ hwq hh))
  have hK : MemLp (fun x ↦ -(ρ + h x)) ∞ volume :=
    ((memLp_top_const ρ).add hH).neg
  have hI := ((hK.mul (r := 2) hpair₂.memLp_left).add
    (hW.mul (r := 2) hpair₂.memLp_right)).add (hQ.mul (r := 2) hpair₁.memLp_right)
  simpa only [Pi.add_def, Pi.mul_def, mul_comm (w _), mul_comm (q _)] using hI

/-- Endpoint normalization is bounded by the input H¹ size at weak
regularity. The proof uses the velocity's classical first derivative only. -/
theorem abs_endpoint_rate_le_of_weak_derivative
    {w q u d : ℝ → ℝ} {R : ℝ}
    (hu : ContDiff ℝ 1 u) (hpair : IsHilbertPair w (deriv u))
    (hpair₁ : IsHilbertPair q d) (hwq : HasWeakTimeDerivativeOn univ w q)
    (hzero : u 0 = 0) (hR : 0 < R) :
    |-u R / R| ≤ lpNorm w 2 volume + lpNorm q 2 volume := by
  have hbound := hpair.norm_le_of_weak_derivative hpair₁ hwq (hu.continuous_deriv le_rfl)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x (_ : x ∈ (univ : Set ℝ)) ↦ (hu.differentiable one_ne_zero) x)
    (fun x _ ↦ hbound x) convex_univ (mem_univ 0) (mem_univ R)
  have hnorm : |u R| ≤ (lpNorm w 2 volume + lpNorm q 2 volume) * R := by
    simpa only [hzero, sub_zero, Real.norm_eq_abs, abs_of_pos hR] using h
  rw [abs_div, abs_neg, abs_of_pos hR]
  exact (div_le_iff₀ hR).mpr hnorm

/-- An H² vorticity graph with a continuous representative gives the weak jet, and the
normalized H² production is bounded by `11` times the H¹ size times the H² energy. -/
theorem exists_normalized_weak_production_bound_of_h2
    (W : W^{2,2}(ℝ^1)) {w u : ℝ → ℝ} {R : ℝ}
    (hw : Continuous w)
    (hrep : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) : ℝ → ℝ)
      =ᵐ[volume] w)
    (hu : ContDiff ℝ 1 u) (hpair : IsHilbertPair w (deriv u))
    (hzero : u 0 = 0) (hR : 0 < R) :
    ∃ (r : Lp ℝ 2 (volume : Measure ℝ)) (s : ℝ → ℝ),
      HasWeakTimeDerivativeOn univ (deriv w) r ∧ IsHilbertPair r s ∧
      ‖∫ x,
        3 * (-u R / R + deriv u x) * w x ^ 2 +
          (-u R / R + deriv u x) * deriv w x ^ 2 -
          (-u R / R + deriv u x) * r x ^ 2 +
          2 * deriv (deriv u) x * w x * deriv w x +
          2 * s x * w x * r x + 2 * deriv (deriv u) x * deriv w x * r x‖ ≤
        11 * (lpNorm w 2 volume + lpNorm (deriv w) 2 volume) *
          ((∫ x, w x ^ 2) + (∫ x, deriv w x ^ 2) + ∫ x, r x ^ 2) := by
  obtain ⟨r, hw₁, hq, hwq, hqr⟩ :=
    Iteration.exists_weak_secondDerivative_of_h2 W hw hrep
  obtain ⟨hu₂, hpair₁, s, hpair₂, _⟩ :=
    Iteration.IsHilbertPair.exists_weak_velocity_jet hpair hu hq (Lp.memLp r) hwq hqr
  refine ⟨r, s, hqr, hpair₂, ?_⟩
  have hp := norm_integral_coupled_rescaled_weak_production_le (-u R / R)
    hw (hw₁.continuous_deriv le_rfl) (hu₂.continuous_deriv (by norm_num))
    hwq hqr hpair hpair₁ hpair₂
  have hρ := abs_endpoint_rate_le_of_weak_derivative hu hpair hpair₁ hwq hzero hR
  have hcoef : 3 * |-u R / R| + 8 * (lpNorm w 2 volume + lpNorm (deriv w) 2 volume) ≤
      11 * (lpNorm w 2 volume + lpNorm (deriv w) 2 volume) := by
    linarith only [hρ]
  exact hp.trans (mul_le_mul_of_nonneg_right hcoef
    (add_nonneg (add_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)
      (integral_nonneg fun _ ↦ sq_nonneg _)) (integral_nonneg fun _ ↦ sq_nonneg _)))

end DeGregorio
