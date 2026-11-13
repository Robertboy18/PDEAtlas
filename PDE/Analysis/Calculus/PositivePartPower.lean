/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
import CAS.ExactTactic

/-!
# Differentiability of powers of the positive part

The positive-part cube is twice continuously differentiable, including at zero.
Its value and its first two derivatives vanish at the interface. These facts
allow polynomial cutoffs to be composed with moving squared-distance functions.
-/

@[expose] public section

namespace PDE.Analysis

open Set Filter
open scoped ContDiff Topology

/-- Powers of the positive part of degree at least two have the expected derivative
even at zero, where the derivatives from both half-lines agree. -/
theorem hasDerivAt_posPart_pow (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y⁺ ^ (n + 2))
      ((n + 2 : ℕ) * x⁺ ^ (n + 1)) x := by
  have hpower (z : ℝ) :
      HasDerivAt (fun y : ℝ ↦ y ^ (n + 2))
        ((n + 2 : ℕ) * z ^ (n + 1)) z := by
    simpa only [show n + 2 - 1 = n + 1 by omega] using hasDerivAt_pow (n + 2) z
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hzero : x⁺ = 0 := posPart_eq_zero.mpr hx.le
    simp only [hzero, pow_succ, mul_zero]
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp [posPart_eq_zero.mpr (le_of_lt hy)]
  · have hleft : HasDerivWithinAt (fun y : ℝ ↦ y⁺ ^ (n + 2)) 0 (Iic 0) 0 := by
      apply (hasDerivAt_const 0 (0 : ℝ)).hasDerivWithinAt.congr
      · intro y hy
        simp [posPart_eq_zero.mpr hy]
      · simp
    have hright : HasDerivWithinAt (fun y : ℝ ↦ y⁺ ^ (n + 2)) 0 (Ici 0) 0 := by
      have hp : HasDerivAt (fun y : ℝ ↦ y ^ (n + 2)) 0 0 := by
        simpa using hpower 0
      apply hp.hasDerivWithinAt.congr
      · intro y hy
        rw [posPart_eq_self.mpr hy]
      · simp
    simpa using hleft.union hright
  · rw [posPart_eq_self.mpr hx.le]
    apply (hpower x).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [posPart_eq_self.mpr (le_of_lt hy)]

/-- The positive-part square has a continuous first derivative. -/
theorem contDiff_one_posPart_sq : ContDiff ℝ 1 (fun x : ℝ ↦ x⁺ ^ 2) := by
  have hderiv (x : ℝ) : HasDerivAt (fun y : ℝ ↦ y⁺ ^ 2) (2 * x⁺) x := by
    simpa using hasDerivAt_posPart_pow 0 x
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x ↦ (hderiv x).differentiableAt, ?_⟩
  have heq : deriv (fun x : ℝ ↦ x⁺ ^ 2) = fun x ↦ 2 * x⁺ :=
    funext fun x ↦ (hderiv x).deriv
  rw [heq]
  exact continuous_const.mul (continuous_id.max continuous_const)

/-- The positive-part power of degree `n + 1` has `n` continuous derivatives
across zero. The derivative formula reduces the regularity order inductively. -/
theorem contDiff_posPart_pow_succ (n : ℕ) :
    ContDiff ℝ (n : ℕ∞ω) (fun x : ℝ ↦ x⁺ ^ (n + 1)) := by
  induction n with
  | zero =>
      simpa only [Nat.cast_zero, Nat.zero_add, pow_one] using
        contDiff_zero.mpr continuous_posPart
  | succ n hn =>
      have hderiv (x : ℝ) : HasDerivAt (fun y : ℝ ↦ y⁺ ^ (n + 1 + 1))
          ((n + 2 : ℕ) * x⁺ ^ (n + 1)) x := by
        simpa only [Nat.add_assoc] using hasDerivAt_posPart_pow n x
      rw [show (↑(n + 1) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
        contDiff_succ_iff_deriv]
      refine ⟨fun x ↦ (hderiv x).differentiableAt, by simp, ?_⟩
      have heq : deriv (fun y : ℝ ↦ y⁺ ^ (n + 1 + 1)) =
          fun x : ℝ ↦ (n + 2 : ℕ) * x⁺ ^ (n + 1) :=
        funext fun x ↦ (hderiv x).deriv
      rw [heq]
      exact contDiff_const.mul hn

/-- The positive-part cube has two continuous derivatives across its interface. -/
theorem contDiff_two_posPart_cube : ContDiff ℝ 2 (fun x : ℝ ↦ x⁺ ^ 3) := by
  have hderiv (x : ℝ) : HasDerivAt (fun y : ℝ ↦ y⁺ ^ 3) (3 * x⁺ ^ 2) x := by
    simpa using hasDerivAt_posPart_pow 1 x
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x ↦ (hderiv x).differentiableAt, by simp, ?_⟩
  have heq : deriv (fun x : ℝ ↦ x⁺ ^ 3) = fun x ↦ 3 * x⁺ ^ 2 :=
    funext fun x ↦ (hderiv x).deriv
  rw [heq]
  exact contDiff_const.mul contDiff_one_posPart_sq

/-- The derivative of `y ↦ (y⁺)³` is `3 (x⁺)²` at every `x`, including `x = 0`. -/
theorem deriv_posPart_cube (x : ℝ) :
    deriv (fun y : ℝ ↦ y⁺ ^ 3) x = 3 * x⁺ ^ 2 := by
  simpa using (hasDerivAt_posPart_pow 1 x).deriv

/-- The second derivative of the positive-part cube vanishes continuously at zero. -/
theorem deriv_deriv_posPart_cube (x : ℝ) :
    deriv (deriv (fun y : ℝ ↦ y⁺ ^ 3)) x = 6 * x⁺ := by
  have heq : deriv (fun y : ℝ ↦ y⁺ ^ 3) = fun y ↦ 3 * y⁺ ^ 2 :=
    funext deriv_posPart_cube
  rw [heq]
  have hderiv := (hasDerivAt_posPart_pow 0 x).const_mul 3
  have hscalar (q : ℝ) : (3 : ℝ) * (2 * q) = 6 * q := by cas
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, pow_one, hscalar] using hderiv.deriv

end PDE.Analysis
