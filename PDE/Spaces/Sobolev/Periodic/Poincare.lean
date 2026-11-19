/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Periodic.Fourier
public import Mathlib.Analysis.Real.Pi.Bounds
public import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Poincaré inequality on the unit torus

A continuous real function `u` on the unit torus `UnitAddTorus (Fin n)` with integral zero and
continuous coordinate derivatives `g` satisfies `‖u‖_{L²} ≤ ‖g‖_{L²}` (`norm_toLp_le_gradient`),
with constant one in every dimension. The sharper constant `1 / (2π)` is not needed for the
closed-range argument of `PDE.Spaces.Sobolev.Periodic.ClosedGradient`.

By Parseval's identity (Mathlib's `hasSum_sq_mFourierCoeff`) both sides are sums of squared Fourier
coefficients, which we compare frequency by frequency (`integral_norm_sq_le_sum_derivatives`, for
complex functions). The zero coefficient of `u` vanishes. At a frequency `k ≠ 0` some `kᵢ` is a
nonzero integer, and `mFourierCoeff_coordinate_derivative` gives `ĝᵢ(k) = 2πi kᵢ û(k)`, so
`‖û(k)‖ ≤ ‖ĝᵢ(k)‖`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter UnitAddTorus
open PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology ComplexConjugate

namespace SobolevSpace.Periodic

/-- Parseval's identity for a continuous complex function `u` on the unit torus:
`Σₖ ‖û(k)‖² = ∫ ‖u‖²`. -/
theorem hasSum_sq_mFourierCoeff_continuous {n : ℕ}
    (u : C(UnitAddTorus (Fin n), ℂ)) :
    HasSum (fun k ↦ ‖mFourierCoeff u k‖ ^ 2)
      (∫ x, ‖u x‖ ^ 2 ∂cellMeasure n) := by
  have h : HasSum
      (fun k ↦ ‖mFourierCoeff (ContinuousMap.toLp 2 (cellMeasure n) ℂ u) k‖ ^ 2)
      (∫ x, ‖ContinuousMap.toLp 2 (cellMeasure n) ℂ u x‖ ^ 2 ∂cellMeasure n) :=
    hasSum_sq_mFourierCoeff (ContinuousMap.toLp 2 (cellMeasure n) ℂ u)
  have h' := h.congr_fun
    (fun k ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) (mFourierCoeff_toLp u k).symm)
  convert h' using 1
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (μ := cellMeasure n) (p := 2) (𝕜 := ℂ) u]
    with x hx
  rw [hx]

/-- If a continuous complex function `u` on the unit torus has integral zero and continuous
coordinate derivatives `g i`, then `∫ ‖u‖² ≤ Σᵢ ∫ ‖g i‖²`. -/
theorem integral_norm_sq_le_sum_derivatives {n : ℕ}
    (u : C(UnitAddTorus (Fin n), ℂ)) (g : Fin n → C(UnitAddTorus (Fin n), ℂ))
    (hd : ∀ x i t, HasDerivAt (fun s ↦ u (x + coordinateShift i s))
      (g i (x + coordinateShift i t)) t)
    (hmean : (∫ x, u x ∂cellMeasure n) = 0) :
    (∫ x, ‖u x‖ ^ 2 ∂cellMeasure n) ≤
      ∑ i, ∫ x, ‖g i x‖ ^ 2 ∂cellMeasure n := by
  classical
  have hcoeff (k : Fin n → ℤ) :
      ‖mFourierCoeff u k‖ ^ 2 ≤ ∑ i, ‖mFourierCoeff (g i) k‖ ^ 2 := by
    by_cases hk : k = 0
    · subst k
      have hz : mFourierCoeff u 0 = 0 := by
        change (∫ x, mFourier (-0) x * u x ∂cellMeasure n) = 0
        simpa [mFourier_zero] using hmean
      simp only [hz, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact Finset.sum_nonneg fun i _ ↦ sq_nonneg _
    · obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := Function.ne_iff.mp hk
      have hki : 1 ≤ |(k i : ℝ)| := by
        have hcases : k i ≤ -1 ∨ 1 ≤ k i := by omega
        rcases hcases with hneg | hpos
        · have h : (k i : ℝ) ≤ -1 := by exact_mod_cast hneg
          exact le_trans (by linarith) (neg_le_abs _)
        · have h : (1 : ℝ) ≤ k i := by exact_mod_cast hpos
          exact h.trans (le_abs_self _)
      have hc : 1 ≤ ‖(2 * Real.pi * Complex.I * k i : ℂ)‖ := by
        simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos, Complex.norm_I, mul_one, Complex.norm_intCast]
        nlinarith [Real.pi_gt_three]
      have hle : ‖mFourierCoeff u k‖ ≤ ‖mFourierCoeff (g i) k‖ := by
        rw [mFourierCoeff_coordinate_derivative u (g i) i (fun x t ↦ hd x i t), norm_mul]
        exact le_mul_of_one_le_left (norm_nonneg _) hc
      exact (pow_le_pow_left₀ (norm_nonneg _) hle 2).trans
        (Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖mFourierCoeff (g j) k‖)
          (Finset.mem_univ i))
  exact hasSum_le hcoeff (hasSum_sq_mFourierCoeff_continuous u)
    (hasSum_sum (fun i _ ↦ hasSum_sq_mFourierCoeff_continuous (g i)))

/-- If a continuous real function `u` on the unit torus has integral zero and continuous
coordinate derivatives `g`, then `‖u‖_{L²} ≤ ‖g‖_{L²}`. -/
theorem norm_toLp_le_gradient {n : ℕ}
    (u : C(UnitAddTorus (Fin n), ℝ)) (g : C(UnitAddTorus (Fin n), ℝ^n))
    (hd : ∀ x i t, HasDerivAt (fun s ↦ u (x + coordinateShift i s))
      (g (x + coordinateShift i t) i) t)
    (hmean : (∫ x, u x ∂cellMeasure n) = 0) :
    ‖ContinuousMap.toLp 2 (cellMeasure n) ℝ u‖ ≤
      ‖ContinuousMap.toLp 2 (cellMeasure n) ℝ g‖ := by
  let uc : C(UnitAddTorus (Fin n), ℂ) :=
    ⟨fun x ↦ (u x : ℂ), Complex.continuous_ofReal.comp u.continuous⟩
  let gc (i : Fin n) : C(UnitAddTorus (Fin n), ℂ) :=
    ⟨fun x ↦ (g x i : ℂ), Complex.continuous_ofReal.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp g.continuous)⟩
  have hdc : ∀ x i t, HasDerivAt (fun s ↦ uc (x + coordinateShift i s))
      (gc i (x + coordinateShift i t)) t := fun x i t ↦
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hd x i t)
  have hm : (∫ x, uc x ∂cellMeasure n) = 0 := by
    change (∫ x, (u x : ℂ) ∂cellMeasure n) = 0
    rw [integral_complex_ofReal, hmean, Complex.ofReal_zero]
  have hp := integral_norm_sq_le_sum_derivatives uc gc hdc hm
  have hnorm {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (v : C(UnitAddTorus (Fin n), E)) :
      ‖ContinuousMap.toLp 2 (cellMeasure n) ℝ v‖ ^ 2 =
        ∫ x, ‖v x‖ ^ 2 ∂cellMeasure n := by
    rw [Lp.norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (μ := cellMeasure n) (p := 2) (𝕜 := ℝ) v]
      with x hx
    rw [hx]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hnorm u, hnorm g]
  calc
    _ = ∫ x, ‖uc x‖ ^ 2 ∂cellMeasure n := by simp [uc]
    _ ≤ ∑ i, ∫ x, ‖gc i x‖ ^ 2 ∂cellMeasure n := hp
    _ = ∫ x, ‖g x‖ ^ 2 ∂cellMeasure n := by
      simp only [gc, ContinuousMap.coe_mk, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [← integral_finsetSum]
      · congr 1
        ext x
        exact (EuclideanSpace.real_norm_sq_eq (g x)).symm
      · intro i _
        exact ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp g.continuous).pow 2
          |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end SobolevSpace.Periodic
