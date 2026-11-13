/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.HilbertSemigroup
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Polynomially weighted spectral heat series

At positive time the heat multiplier absorbs every power of a nonnegative eigenvalue.
Thus every weighted series converges in Hilbert norm for arbitrary Hilbert-space data.
The closed generator identifies the derivative of each weighted trajectory with minus
the next one. No eigenvalue counting estimate is needed.

The auxiliary `spectralHeatPower` is extended by zero to nonpositive times. Only its
positive-time values represent heat evolution; initial values use `spectralHeatEvolution`.
-/

@[expose] public section

noncomputable section

namespace HeatEquation

open PDE.Analysis.Evolution Filter Set
open scoped Topology NNReal ENNReal lp

/-- A factorial bound for every polynomially weighted heat multiplier. -/
theorem pow_mul_exp_neg_mul_le (m : ℕ) {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) :
    a ^ m * Real.exp (-a * t) ≤ (m.factorial : ℝ) / t ^ m := by
  have hf : 0 < (m.factorial : ℝ) := by positivity
  have he := (div_le_iff₀ hf).1 (Real.pow_div_factorial_le_exp (a * t)
    (mul_nonneg ha ht.le) m)
  have he' := mul_le_mul_of_nonneg_right he (Real.exp_nonneg (-(a * t)))
  have hexp : Real.exp (a * t) * Real.exp (-(a * t)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [mul_pow] at he'
  apply (le_div_iff₀ (pow_pos ht m)).2
  calc
    a ^ m * Real.exp (-a * t) * t ^ m =
        (a ^ m * t ^ m) * Real.exp (-(a * t)) := by
      rw [neg_mul]
      ring
    _ ≤ Real.exp (a * t) * (m.factorial : ℝ) * Real.exp (-(a * t)) := he'
    _ = (m.factorial : ℝ) := by
      calc
        _ = (m.factorial : ℝ) * (Real.exp (a * t) * Real.exp (-(a * t))) := by ring
        _ = _ := by rw [hexp, mul_one]

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (b : HilbertBasis ι ℝ H) (lambda : ι → ℝ) (hlambda : ∀ i, 0 ≤ lambda i)

include hlambda in
/-- Positive heat damping preserves square summability after every eigenvalue power. -/
theorem memℓp_spectralHeatPower (m : ℕ) (f : H) {t : ℝ} (ht : 0 < t) :
    Memℓp (fun i ↦ lambda i ^ m * Real.exp (-lambda i * t) * b.repr f i) 2 := by
  have h := (lp.memℓp (b.repr f)).const_mul ((m.factorial : ℝ) / t ^ m)
  apply h.mono'
  intro i
  calc
    ‖lambda i ^ m * Real.exp (-lambda i * t) * b.repr f i‖ =
        (lambda i ^ m * Real.exp (-lambda i * t)) * ‖b.repr f i‖ := by
      rw [norm_mul,
        Real.norm_of_nonneg (mul_nonneg (pow_nonneg (hlambda i) _) (Real.exp_nonneg _))]
    _ ≤ ((m.factorial : ℝ) / t ^ m) * ‖b.repr f i‖ :=
      mul_le_mul_of_nonneg_right (pow_mul_exp_neg_mul_le m (hlambda i) ht) (norm_nonneg _)
    _ = ‖((m.factorial : ℝ) / t ^ m) * b.repr f i‖ := by
      rw [norm_mul, Real.norm_of_nonneg
        (div_nonneg (Nat.cast_nonneg _) (pow_nonneg ht.le m))]

/-- The Hilbert sum with the additional multiplier `lambda^m`, for positive time.
The value at nonpositive time is an auxiliary zero extension. -/
def spectralHeatPower (m : ℕ) (f : H) (t : ℝ) : H :=
  if ht : 0 < t then
    b.repr.symm ⟨fun i ↦ lambda i ^ m * Real.exp (-lambda i * t) * b.repr f i,
      memℓp_spectralHeatPower b lambda hlambda m f ht⟩
  else 0

/-- The weighted trajectory has the expected coordinates at every positive time. -/
theorem spectralHeatPower_repr (m : ℕ) (f : H) {t : ℝ} (ht : 0 < t) (i : ι) :
    b.repr (spectralHeatPower b lambda hlambda m f t) i =
      lambda i ^ m * Real.exp (-lambda i * t) * b.repr f i := by
  simp [spectralHeatPower, ht]

/-- Every polynomially weighted heat series converges in the Hilbert norm. -/
theorem hasSum_spectralHeatPower (m : ℕ) (f : H) {t : ℝ} (ht : 0 < t) :
    HasSum (fun i ↦ (lambda i ^ m * Real.exp (-lambda i * t) * b.repr f i) • b i)
      (spectralHeatPower b lambda hlambda m f t) := by
  simpa only [spectralHeatPower_repr b lambda hlambda m f ht] using
    b.hasSum_repr (spectralHeatPower b lambda hlambda m f t)

/-- The zeroth weighted trajectory is the original spectral heat evolution. -/
theorem spectralHeatPower_zero_order (f : H) {t : ℝ} (ht : 0 < t) :
    spectralHeatPower b lambda hlambda 0 f t =
      spectralHeatEvolution b lambda hlambda f ⟨t, ht.le⟩ := by
  apply b.repr.injective
  apply lp.ext
  funext i
  erw [spectralHeatPower_repr b lambda hlambda 0 f ht, spectralHeatEvolution_repr]
  change lambda i ^ 0 * Real.exp (-lambda i * t) * b.repr f i =
    Real.exp (-lambda i * t) * b.repr f i
  rw [pow_zero, one_mul]

/-- A weighted trajectory evolves by the same heat semigroup after any positive time. -/
theorem spectralHeatPower_add (m : ℕ) (f : H) {s : ℝ} (hs : 0 < s) (t : ℝ≥0) :
    spectralHeatPower b lambda hlambda m f (s + t) =
      spectralHeatSemigroup b lambda hlambda t (spectralHeatPower b lambda hlambda m f s) := by
  apply b.repr.injective
  apply lp.ext
  funext i
  erw [spectralHeatPower_repr b lambda hlambda m f (add_pos_of_pos_of_nonneg hs t.2),
    spectralHeatSemigroup_apply, spectralHeatEvolution_repr,
    spectralHeatPower_repr b lambda hlambda m f hs, mul_add, Real.exp_add]
  change lambda i ^ m * (Real.exp (-lambda i * s) * Real.exp (-lambda i * t)) * b.repr f i =
    Real.exp (-lambda i * t) * (lambda i ^ m * Real.exp (-lambda i * s) * b.repr f i)
  ring

variable [CompleteSpace H]

/-- Every positive-time weighted vector is in the generator domain; its generator is
minus the next weighted vector. -/
theorem spectralHeatSemigroup_hasGeneratorAt_power (m : ℕ) (f : H) {t : ℝ} (ht : 0 < t) :
    (spectralHeatSemigroup b lambda hlambda).HasGeneratorAt
      (spectralHeatPower b lambda hlambda m f t)
      (-spectralHeatPower b lambda hlambda (m + 1) f t) := by
  apply spectralHeatSemigroup_hasGeneratorAt_of_repr
  intro i
  rw [map_neg, lp.coeFn_neg, Pi.neg_apply, spectralHeatPower_repr b lambda hlambda m f ht,
    spectralHeatPower_repr b lambda hlambda (m + 1) f ht, pow_succ]
  ring

/-- Positive-time differentiation of a weighted heat series gives minus the next series. -/
theorem hasDerivAt_spectralHeatPower (m : ℕ) (f : H) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (spectralHeatPower b lambda hlambda m f)
      (-spectralHeatPower b lambda hlambda (m + 1) f t) t := by
  have hh : 0 < t / 2 := half_pos ht
  have hshift : 0 < t - t / 2 := by linarith
  have hg := spectralHeatSemigroup_hasGeneratorAt_power b lambda hlambda m f hh
  have hd := hg.hasDerivAt_realOrbit hshift
  have hcomp := hd.scomp t ((hasDerivAt_id t).sub_const (t / 2))
  have horbit (k : ℕ) {s : ℝ} (hs : t / 2 < s) :
      (spectralHeatSemigroup b lambda hlambda).realOrbit
        (spectralHeatPower b lambda hlambda k f (t / 2)) (s - t / 2) =
      spectralHeatPower b lambda hlambda k f s := by
    unfold StronglyContinuousSemigroup.realOrbit
    rw [← spectralHeatPower_add b lambda hlambda k f hh,
      Real.coe_toNNReal _ (sub_pos.mpr hs).le, add_sub_cancel]
  have hval :
      (spectralHeatSemigroup b lambda hlambda).realOrbit
        (-spectralHeatPower b lambda hlambda (m + 1) f (t / 2)) (t - t / 2) =
      -spectralHeatPower b lambda hlambda (m + 1) f t := by
    change (spectralHeatSemigroup b lambda hlambda (t - t / 2).toNNReal)
      (-spectralHeatPower b lambda hlambda (m + 1) f (t / 2)) = _
    rw [map_neg]
    exact congrArg Neg.neg (horbit (m + 1) (by linarith))
  simp only [one_smul, hval] at hcomp
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show t / 2 < t by linarith)] with s hs
  exact (horbit m hs).symm

/-- Every weighted heat trajectory is continuous at positive time in the Hilbert norm. -/
theorem continuousOn_spectralHeatPower (m : ℕ) (f : H) :
    ContinuousOn (spectralHeatPower b lambda hlambda m f) (Ioi 0) :=
  fun _ ht ↦ (hasDerivAt_spectralHeatPower b lambda hlambda m f ht).continuousAt.continuousWithinAt

end HeatEquation
