/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.FactoredOperator
public import Mathlib.Analysis.InnerProductSpace.Calculus
import CAS.ExactTactic

/-!
# Radial exponential barriers for elliptic operators

For `α > 0` and `R > 0`, the function `exp (-α ‖x - z‖²) - exp (-α R²)` vanishes on the sphere of
radius `R` and is positive inside. On the annulus `R / 2 < ‖x - z‖ < R`, uniform ellipticity and
bounded principal trace, drift, and nonnegative potential make it a strict subsolution once `α` is
sufficiently large. This is the barrier `v` and the estimate (15) in step 1 of the proof of Hopf's
Lemma in Evans's §6.4.2.

## Main definitions

* `radialBarrier`: the barrier, normalized to vanish at distance `R` from `z`.

## Main results

* `factoredOperator_radialBarrier`: the residual of the barrier.
* `exists_radialBarrier_strict_subsolution`: the barrier is a strict subsolution on the annulus for
  large `α`, without coefficient continuity.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.4.2, step 1 of the proof of Hopf's Lemma, (15), p. 348.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace EllipticMaximum

open PDE.Analysis
open scoped InnerProductSpace

variable {E ι : Type*} [NormedAddCommGroup E] [Fintype ι]

/-- The radial exponential barrier, normalized to vanish at distance `R` from `z`. -/
def radialBarrier (z : E) (R α : ℝ) (x : E) : ℝ :=
  Real.exp (-α * ‖x - z‖ ^ 2) - Real.exp (-α * R ^ 2)

/-- The radial barrier is at most one for every nonnegative decay parameter. -/
theorem radialBarrier_le_one (z : E) (R : ℝ) {α : ℝ} (hα : 0 ≤ α) (x : E) :
    radialBarrier z R α x ≤ 1 := by
  have he : Real.exp (-α * ‖x - z‖ ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα) (sq_nonneg _))
  exact (sub_le_self _ (Real.exp_nonneg _)).trans he

/-- The radial barrier vanishes on the outer sphere. -/
theorem radialBarrier_eq_zero {z x : E} {R α : ℝ} (hx : ‖x - z‖ = R) :
    radialBarrier z R α x = 0 := by
  simp [radialBarrier, hx]

variable [InnerProductSpace ℝ E]

/-- The radial barrier has continuous second derivatives, including at its center. -/
theorem contDiff_radialBarrier (z : E) (R α : ℝ) :
    ContDiff ℝ 2 (radialBarrier z R α) := by
  exact (((contDiff_id.sub contDiff_const).norm_sq ℝ).const_smul (-α)).exp.sub
    contDiff_const

/-- The curvature of the Gaussian profile along an affine line. -/
theorem secondDirectionalDerivative_exp_neg_norm_sq (z : E) (α : ℝ) (x v : E) :
    secondDirectionalDerivative (fun y ↦ Real.exp (-α * ‖y - z‖ ^ 2)) x v =
      (4 * α ^ 2 * ⟪x - z, v⟫_ℝ ^ 2 - 2 * α * ‖v‖ ^ 2) *
        Real.exp (-α * ‖x - z‖ ^ 2) := by
  have hnorm (s : ℝ) :
      ‖x + s • v - z‖ ^ 2 =
        ‖x - z‖ ^ 2 + 2 * s * ⟪x - z, v⟫_ℝ + s ^ 2 * ‖v‖ ^ 2 := by
    rw [show x + s • v - z = (x - z) + s • v by abel,
      norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs]
    ring
  let F : ℝ → ℝ := fun s ↦
    Real.exp (-α * (‖x - z‖ ^ 2 + 2 * s * ⟪x - z, v⟫_ℝ + s ^ 2 * ‖v‖ ^ 2))
  have hline : (fun s : ℝ ↦ Real.exp (-α * ‖x + s • v - z‖ ^ 2)) = F := by
    funext s
    rw [hnorm]
  have hfirst (s : ℝ) :
      HasDerivAt F
        ((-α * (2 * ⟪x - z, v⟫_ℝ + 2 * s * ‖v‖ ^ 2)) * F s) s := by
    dsimp [F]
    cas
  have hsecond :
      HasDerivAt
        (fun s : ℝ ↦ (-α * (2 * ⟪x - z, v⟫_ℝ + 2 * s * ‖v‖ ^ 2)) * F s)
        ((4 * α ^ 2 * ⟪x - z, v⟫_ℝ ^ 2 - 2 * α * ‖v‖ ^ 2) *
          Real.exp (-α * ‖x - z‖ ^ 2)) 0 := by
    dsimp [F]
    cas
  simp only [secondDirectionalDerivative, hline,
    show deriv F = (fun s ↦ (-α * (2 * ⟪x - z, v⟫_ℝ + 2 * s * ‖v‖ ^ 2)) * F s)
      from funext fun s ↦ (hfirst s).deriv]
  exact hsecond.deriv

/-- The residual of the radial barrier for a factored nondivergence operator. -/
theorem factoredOperator_radialBarrier
    (σ : E → ι → E) (b : E → E) (c : E → ℝ) (z : E) (R α : ℝ) (x : E) :
    factoredOperator σ b c (radialBarrier z R α) x =
      Real.exp (-α * ‖x - z‖ ^ 2) *
        (2 * α * ∑ k, ‖σ x k‖ ^ 2 -
          4 * α ^ 2 * ∑ k, ⟪x - z, σ x k⟫_ℝ ^ 2 -
          2 * α * ⟪x - z, b x⟫_ℝ) + c x * radialBarrier z R α x := by
  have hnorm : HasFDerivAt (fun y : E ↦ ‖y - z‖ ^ 2)
      (2 • innerSL ℝ (x - z)) x := by
    simpa using ((hasFDerivAt_id x).sub_const z).norm_sq
  have hderiv : fderiv ℝ (fun y : E ↦ Real.exp (-α * ‖y - z‖ ^ 2)) x =
      Real.exp (-α * ‖x - z‖ ^ 2) • ((-α) • (2 • innerSL ℝ (x - z))) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using (hnorm.const_smul (-α)).exp.fderiv
  unfold radialBarrier
  rw [factoredOperator_sub_const]
  simp only [factoredOperator, secondDirectionalDerivative_exp_neg_norm_sq, hderiv,
    smul_apply, innerSL_apply_apply, smul_eq_mul, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- Uniform ellipticity and bounded coefficients produce a strict radial subsolution on
the annulus. Coefficient continuity is not required. -/
theorem exists_radialBarrier_strict_subsolution
    (σ : E → ι → E) (b : E → E) (c : E → ℝ) (z : E)
    {R κ A B C : ℝ} (hR : 0 < R) (hκ : 0 < κ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (helliptic : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R →
      ∀ v : E, κ * ‖v‖ ^ 2 ≤ ∑ k, ⟪v, σ x k⟫_ℝ ^ 2)
    (htrace : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → ∑ k, ‖σ x k‖ ^ 2 ≤ A)
    (hdrift : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → ‖b x‖ ≤ B)
    (hpotential : ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R → 0 ≤ c x ∧ c x ≤ C) :
    ∃ α : ℝ, 0 < α ∧
      ∀ x, R / 2 < ‖x - z‖ → ‖x - z‖ < R →
        factoredOperator σ b c (radialBarrier z R α) x < 0 := by
  let K : ℝ := 2 * A + 2 * R * B + C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let α : ℝ := 1 + (K + 1) / (κ * R ^ 2)
  have hden : 0 < κ * R ^ 2 := mul_pos hκ (sq_pos_of_pos hR)
  have hαone : 1 < α := by
    dsimp [α]
    linarith [div_pos (show 0 < K + 1 by linarith) hden]
  have hα : 0 < α := zero_lt_one.trans hαone
  have hαK : K < α * (κ * R ^ 2) := by
    have hcancel : (α - 1) * (κ * R ^ 2) = K + 1 := by
      dsimp [α]
      rw [add_sub_cancel_left, div_mul_cancel₀ _ hden.ne']
    nlinarith
  refine ⟨α, hα, ?_⟩
  intro x hxinner hxouter
  have hprincipal : κ * R ^ 2 ≤ 4 * ∑ k, ⟪x - z, σ x k⟫_ℝ ^ 2 := by
    have hradius : R ^ 2 ≤ 4 * ‖x - z‖ ^ 2 := by
      have hprod := mul_nonneg (show 0 ≤ 2 * ‖x - z‖ - R by linarith)
        (show 0 ≤ 2 * ‖x - z‖ + R by positivity)
      nlinarith
    have := mul_le_mul_of_nonneg_left hradius hκ.le
    nlinarith [helliptic x hxinner hxouter (x - z)]
  have hinner : -R * B ≤ ⟪x - z, b x⟫_ℝ := by
    have habs : |⟪x - z, b x⟫_ℝ| ≤ R * B :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul hxouter.le (hdrift x hxinner hxouter) (norm_nonneg _) hR.le)
    linarith [neg_abs_le ⟪x - z, b x⟫_ℝ]
  have hnegative :
      2 * α * ∑ k, ‖σ x k‖ ^ 2 -
          4 * α ^ 2 * ∑ k, ⟪x - z, σ x k⟫_ℝ ^ 2 -
          2 * α * ⟪x - z, b x⟫_ℝ + C < 0 := by
    have hp := mul_le_mul_of_nonneg_left hprincipal (sq_nonneg α)
    have ht := mul_le_mul_of_nonneg_left (htrace x hxinner hxouter)
      (show 0 ≤ 2 * α by positivity)
    have hb := mul_le_mul_of_nonneg_left hinner (show 0 ≤ 2 * α by positivity)
    have hstrict := mul_pos hα (sub_pos.mpr hαK)
    have hCα : C ≤ α * C := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hαone.le hC
    dsimp [K] at hstrict
    nlinarith
  obtain ⟨hc0, hcC⟩ := hpotential x hxinner hxouter
  have hpot :
      c x * radialBarrier z R α x ≤ C * Real.exp (-α * ‖x - z‖ ^ 2) := by
    calc
      c x * radialBarrier z R α x ≤ c x * Real.exp (-α * ‖x - z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (sub_le_self _ (Real.exp_nonneg _)) hc0
      _ ≤ C * Real.exp (-α * ‖x - z‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hcC (Real.exp_nonneg _)
  rw [factoredOperator_radialBarrier]
  have := mul_neg_of_pos_of_neg (Real.exp_pos (-α * ‖x - z‖ ^ 2)) hnegative
  nlinarith

end EllipticMaximum
