/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.SphericalBessel.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Bounds for spherical Bessel functions

The energy `E x = g_l x ^ 2 + x ^ 2 g_{l+1} x ^ 2` of the reduced function satisfies
`E' x = -4 (l + 1) x g_{l+1} x ^ 2`, so it decreases on `[0, ∞)` from its value
`(1 / (2l + 1)‼) ^ 2` at the origin. Hence `|j_l x| ≤ |x| ^ l / (2l + 1)‼`.

The partial sums `S_N = ∑_{l ≤ N} (2l + 1) j_l ^ 2` have derivative `-2 (N + 1) j_N j_{N+1}`
and value `1` at the origin. The bound `|j_l x| ≤ |x| ^ l / (2l + 1)‼` makes this derivative small
on a fixed interval as `N` grows, so `(2l + 1) j_l x ^ 2 ≤ 1` for every `l` and `x`. Since
`(2l + 3) j_{l+1}' = (l + 1) j_l - (l + 2) j_{l+2}` has coefficients of total mass one, every
derivative of every `j_l` is bounded by one as well.

## Main results

* `abs_reducedSphericalBesselJ_le`: `|g_l x| ≤ 1 / (2l + 1)‼`.
* `abs_sphericalBesselJ_le_pow`: `|j_l x| ≤ x ^ l / (2l + 1)‼` for `0 ≤ x`.
* `two_mul_add_one_mul_sq_sphericalBesselJ_le`: `(2l + 1) j_l x ^ 2 ≤ 1`.
* `abs_iteratedDeriv_sphericalBesselJ_le`: `|j_l^{(k)} x| ≤ 1`.
* `abs_sphericalBesselJ_sub_le`: `j_l` is `1`-Lipschitz.
* `abs_iteratedDeriv_sphericalBesselJ_comp_mul_le`: `|(d/dr)^k j_l (a r)| ≤ |a| ^ k`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.SpecialFunctions

open Nat Filter Set
open scoped Topology ContDiff

/-- The energy of the reduced function has derivative `-4 (l + 1) x g_{l+1} x ^ 2`. -/
theorem hasDerivAt_reducedSphericalBesselJ_energy (l : ℕ) (x : ℝ) :
    HasDerivAt (fun y ↦ reducedSphericalBesselJ l y ^ 2 +
        y ^ 2 * reducedSphericalBesselJ (l + 1) y ^ 2)
      (-(4 * ((l : ℝ) + 1)) * x * reducedSphericalBesselJ (l + 1) x ^ 2) x := by
  have h₁ := (hasDerivAt_reducedSphericalBesselJ l x).pow 2
  have h₂ := (hasDerivAt_pow 2 x).mul ((hasDerivAt_reducedSphericalBesselJ (l + 1) x).pow 2)
  refine (h₁.add h₂).congr_deriv ?_
  rw [Pi.pow_apply, reducedSphericalBesselJ_eq_sub l x]
  push_cast
  ring

/-- The energy of the reduced function is at most its value at the origin. -/
theorem reducedSphericalBesselJ_energy_le (l : ℕ) (x : ℝ) :
    reducedSphericalBesselJ l x ^ 2 + x ^ 2 * reducedSphericalBesselJ (l + 1) x ^ 2 ≤
      (1 / ((2 * l + 1)‼ : ℝ)) ^ 2 := by
  wlog hx : 0 ≤ x generalizing x
  · simpa only [reducedSphericalBesselJ_neg, neg_sq] using this (-x) (by linarith)
  set E : ℝ → ℝ := fun y ↦ reducedSphericalBesselJ l y ^ 2 +
    y ^ 2 * reducedSphericalBesselJ (l + 1) y ^ 2 with hE
  have hderiv (y : ℝ) := hasDerivAt_reducedSphericalBesselJ_energy l y
  have hanti : AntitoneOn E (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun y _ ↦ (hderiv y).continuousAt.continuousWithinAt)
      (fun y _ ↦ (hderiv y).differentiableAt.differentiableWithinAt) fun y hy ↦ ?_
    rw [interior_Ici, mem_Ioi] at hy
    rw [(hderiv y).deriv]
    have : 0 ≤ (4 * ((l : ℝ) + 1)) * y * reducedSphericalBesselJ (l + 1) y ^ 2 := by
      positivity
    linarith
  have h := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
  simpa only [hE, reducedSphericalBesselJ_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_mul, add_zero] using h

/-- `|g_l x| ≤ 1 / (2l + 1)‼`. -/
theorem abs_reducedSphericalBesselJ_le (l : ℕ) (x : ℝ) :
    |reducedSphericalBesselJ l x| ≤ 1 / ((2 * l + 1)‼ : ℝ) := by
  have h := reducedSphericalBesselJ_energy_le l x
  have hpos : (0 : ℝ) < ((2 * l + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
  apply abs_le_of_sq_le_sq _ (by positivity)
  nlinarith [sq_nonneg x, sq_nonneg (reducedSphericalBesselJ (l + 1) x)]

/-- `|j_l x| ≤ |x| ^ l / (2l + 1)‼` at every real point. -/
theorem abs_sphericalBesselJ_le_abs_pow (l : ℕ) (x : ℝ) :
    |sphericalBesselJ l x| ≤ |x| ^ l / (2 * l + 1)‼ := by
  rw [sphericalBesselJ_eq_pow_mul, abs_mul, abs_pow, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (abs_reducedSphericalBesselJ_le l x) (by positivity)

/-- `|j_l x| ≤ x ^ l / (2l + 1)‼` for `0 ≤ x`. -/
theorem abs_sphericalBesselJ_le_pow {l : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    |sphericalBesselJ l x| ≤ x ^ l / (2 * l + 1)‼ := by
  simpa only [abs_of_nonneg hx] using abs_sphericalBesselJ_le_abs_pow l x

/-- The partial sums `∑_{l ≤ N} (2l + 1) j_l ^ 2` have derivative `-2 (N + 1) j_N j_{N+1}`. -/
theorem hasDerivAt_sum_sq_sphericalBesselJ (N : ℕ) (x : ℝ) :
    HasDerivAt (fun y ↦ ∑ l ∈ Finset.range (N + 1), (2 * (l : ℝ) + 1) * sphericalBesselJ l y ^ 2)
      (-(2 * ((N : ℝ) + 1)) * sphericalBesselJ N x * sphericalBesselJ (N + 1) x) x := by
  induction N with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, CharP.cast_eq_zero, mul_zero,
      one_mul]
    refine ((hasDerivAt_sphericalBesselJ_zero x).pow 2).congr_deriv ?_
    push_cast
    ring
  | succ N ih =>
    simp only [Finset.sum_range_succ _ (N + 1)]
    refine (ih.add (((hasDerivAt_sphericalBesselJ_succ N x).pow 2).const_mul
      (2 * ((N + 1 : ℕ) : ℝ) + 1))).congr_deriv ?_
    push_cast
    field_simp
    ring

/-- The partial sums `∑_{l ≤ N} (2l + 1) j_l ^ 2` take the value one at the origin. -/
theorem sum_sq_sphericalBesselJ_zero (N : ℕ) :
    ∑ l ∈ Finset.range (N + 1), (2 * (l : ℝ) + 1) * sphericalBesselJ l 0 ^ 2 = 1 := by
  rw [Finset.sum_range_succ']
  simp [sphericalBesselJ_succ_zero, sphericalBesselJ_zero_zero]

/-- `(N + 1)! ≤ (2N + 1)‼`. -/
private theorem factorial_succ_le_doubleFactorial (N : ℕ) : (N + 1)! ≤ (2 * N + 1)‼ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.factorial_succ, show 2 * (N + 1) + 1 = 2 * N + 1 + 2 by ring,
      Nat.doubleFactorial_add_two]
    exact Nat.mul_le_mul (by omega) ih

/-- The partial sums stay within `(x ^ 2) ^ (N + 1) / (N + 1)!` of one. -/
theorem abs_sum_sq_sphericalBesselJ_sub_one_le (N : ℕ) (x : ℝ) :
    |∑ l ∈ Finset.range (N + 1), (2 * (l : ℝ) + 1) * sphericalBesselJ l x ^ 2 - 1| ≤
      (x ^ 2) ^ (N + 1) / (N + 1)! := by
  set S : ℝ → ℝ := fun y ↦
    ∑ l ∈ Finset.range (N + 1), (2 * (l : ℝ) + 1) * sphericalBesselJ l y ^ 2 with hS
  have hfac : (0 : ℝ) < ((N + 1)! : ℕ) := by exact_mod_cast Nat.factorial_pos _
  have hd₁ : ((N + 1)! : ℝ) ≤ ((2 * N + 1)‼ : ℕ) := by
    exact_mod_cast factorial_succ_le_doubleFactorial N
  have hd₂ : 2 * ((N : ℝ) + 1) * ((2 * N + 1)‼ : ℕ) ≤ ((2 * (N + 1) + 1)‼ : ℕ) := by
    rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 2 by ring, Nat.doubleFactorial_add_two]
    push_cast
    nlinarith [(by exact_mod_cast Nat.doubleFactorial_pos (2 * N + 1) :
      (0 : ℝ) < ((2 * N + 1)‼ : ℕ))]
  set C : ℝ := 2 * ((N : ℝ) + 1) * (|x| ^ N / (2 * N + 1)‼) *
    (|x| ^ (N + 1) / (2 * (N + 1) + 1)‼) with hC
  have hbound : ∀ y ∈ Icc (-|x|) |x|, ‖deriv S y‖ ≤ C := by
    intro y hy
    have hy' : |y| ≤ |x| := abs_le.mpr hy
    rw [(hasDerivAt_sum_sq_sphericalBesselJ N y).deriv, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * ((N : ℝ) + 1))]
    have h₁ := (abs_sphericalBesselJ_le_abs_pow N y).trans
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg y) hy' N) (by positivity))
    have h₂ := (abs_sphericalBesselJ_le_abs_pow (N + 1) y).trans
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg y) hy' (N + 1)) (by positivity))
    rw [hC]
    gcongr
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun y _ ↦ (hasDerivAt_sum_sq_sphericalBesselJ N y).differentiableAt) hbound
    (convex_Icc (-|x|) |x|) (x := 0) (y := x)
    ⟨by linarith [abs_nonneg x], abs_nonneg x⟩ ⟨neg_abs_le x, le_abs_self x⟩
  rw [sum_sq_sphericalBesselJ_zero N, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  refine hmvt.trans ?_
  have hpow : (x ^ 2) ^ (N + 1) = |x| ^ N * |x| ^ (N + 1) * |x| := by
    rw [← sq_abs, ← pow_mul]
    ring
  have hdf₁ : (0 : ℝ) < ((2 * N + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have hdf₂ : (0 : ℝ) < ((2 * (N + 1) + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
  rw [hC, hpow]
  have hxN : 0 ≤ |x| ^ N * |x| ^ (N + 1) * |x| := by positivity
  have key : 2 * ((N : ℝ) + 1) * ((N + 1)! : ℕ) ≤
      ((2 * N + 1)‼ : ℕ) * ((2 * (N + 1) + 1)‼ : ℕ) := by
    have h1 : (1 : ℝ) ≤ ((2 * N + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
    calc 2 * ((N : ℝ) + 1) * ((N + 1)! : ℕ) ≤ 2 * ((N : ℝ) + 1) * ((2 * N + 1)‼ : ℕ) := by
          gcongr
      _ ≤ ((2 * (N + 1) + 1)‼ : ℕ) := hd₂
      _ ≤ ((2 * N + 1)‼ : ℕ) * ((2 * (N + 1) + 1)‼ : ℕ) := le_mul_of_one_le_left hdf₂.le h1
  have heq : 2 * ((N : ℝ) + 1) * (|x| ^ N / ((2 * N + 1)‼ : ℕ)) *
      (|x| ^ (N + 1) / ((2 * (N + 1) + 1)‼ : ℕ)) * |x| =
      (|x| ^ N * |x| ^ (N + 1) * |x|) * (2 * ((N : ℝ) + 1)) /
        (((2 * N + 1)‼ : ℕ) * ((2 * (N + 1) + 1)‼ : ℕ)) := by
    field_simp
  rw [heq, div_le_div_iff₀ (by positivity) hfac, mul_assoc]
  exact mul_le_mul_of_nonneg_left key hxN

/-- `(2l + 1) j_l x ^ 2 ≤ 1` at every real point. -/
theorem two_mul_add_one_mul_sq_sphericalBesselJ_le (l : ℕ) (x : ℝ) :
    (2 * (l : ℝ) + 1) * sphericalBesselJ l x ^ 2 ≤ 1 := by
  have hlim : Tendsto (fun N : ℕ ↦ 1 + (x ^ 2) ^ (N + l + 1) / (N + l + 1)!) atTop (𝓝 1) := by
    have h := (FloorSemiring.tendsto_pow_div_factorial_atTop (x ^ 2)).comp
      (tendsto_add_atTop_nat (l + 1))
    simpa only [Function.comp_def, add_assoc, add_zero] using h.const_add 1
  refine le_of_tendsto_of_tendsto' tendsto_const_nhds hlim fun N ↦ ?_
  have hsum := abs_sum_sq_sphericalBesselJ_sub_one_le (N + l) x
  have hle : (2 * (l : ℝ) + 1) * sphericalBesselJ l x ^ 2 ≤
      ∑ k ∈ Finset.range (N + l + 1), (2 * (k : ℝ) + 1) * sphericalBesselJ k x ^ 2 := by
    apply Finset.single_le_sum (f := fun k : ℕ ↦ (2 * (k : ℝ) + 1) * sphericalBesselJ k x ^ 2)
      (fun k _ ↦ by positivity)
    simp only [Finset.mem_range]
    omega
  linarith [(abs_le.mp hsum).2]

/-- `|j_l x| ≤ 1` at every real point. -/
theorem abs_sphericalBesselJ_le_one (l : ℕ) (x : ℝ) : |sphericalBesselJ l x| ≤ 1 := by
  have h := two_mul_add_one_mul_sq_sphericalBesselJ_le l x
  apply abs_le_of_sq_le_sq _ zero_le_one
  nlinarith [sq_nonneg (sphericalBesselJ l x), (Nat.cast_nonneg l : (0 : ℝ) ≤ l)]

/-- The derivative of `j_{l+1}` as a combination of `j_l` and `j_{l+2}`. -/
theorem deriv_sphericalBesselJ_succ_eq_mul (l : ℕ) :
    deriv (sphericalBesselJ (l + 1)) = fun y ↦
      (l + 1 : ℝ) / (2 * l + 3) * sphericalBesselJ l y -
        (l + 2 : ℝ) / (2 * l + 3) * sphericalBesselJ (l + 2) y := by
  rw [deriv_sphericalBesselJ_succ]
  funext x
  ring

/-- Every derivative of every spherical Bessel function is bounded by one. -/
theorem abs_iteratedDeriv_sphericalBesselJ_le (l k : ℕ) (x : ℝ) :
    |iteratedDeriv k (sphericalBesselJ l) x| ≤ 1 := by
  induction k generalizing l x with
  | zero => simpa only [iteratedDeriv_zero] using abs_sphericalBesselJ_le_one l x
  | succ k ih =>
    rw [iteratedDeriv_succ']
    rcases l with _ | l
    · rw [deriv_sphericalBesselJ_zero, iteratedDeriv_fun_neg, abs_neg]
      exact ih 1 x
    · have hc (m : ℕ) : ContDiffAt ℝ k (sphericalBesselJ m) x :=
        (contDiff_sphericalBesselJ m).contDiffAt
      rw [deriv_sphericalBesselJ_succ_eq_mul, iteratedDeriv_fun_sub
        (contDiffAt_const.mul (hc l)) (contDiffAt_const.mul (hc (l + 2))),
        iteratedDeriv_const_mul _ (hc l), iteratedDeriv_const_mul _ (hc (l + 2))]
      have ha : (0 : ℝ) ≤ (l + 1 : ℝ) / (2 * l + 3) := by positivity
      have hb : (0 : ℝ) ≤ (l + 2 : ℝ) / (2 * l + 3) := by positivity
      have hab : (l + 1 : ℝ) / (2 * l + 3) + (l + 2 : ℝ) / (2 * l + 3) = 1 := by
        field_simp
        ring
      calc |(l + 1 : ℝ) / (2 * l + 3) * iteratedDeriv k (sphericalBesselJ l) x -
            (l + 2 : ℝ) / (2 * l + 3) * iteratedDeriv k (sphericalBesselJ (l + 2)) x|
          ≤ (l + 1 : ℝ) / (2 * l + 3) * |iteratedDeriv k (sphericalBesselJ l) x| +
            (l + 2 : ℝ) / (2 * l + 3) * |iteratedDeriv k (sphericalBesselJ (l + 2)) x| := by
            refine (abs_sub _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ (l + 1 : ℝ) / (2 * l + 3) * 1 + (l + 2 : ℝ) / (2 * l + 3) * 1 := by
            gcongr
            · exact ih l x
            · exact ih (l + 2) x
        _ = 1 := by rw [mul_one, mul_one, hab]

/-- `j_l` is `1`-Lipschitz. -/
theorem abs_sphericalBesselJ_sub_le (l : ℕ) (x y : ℝ) :
    |sphericalBesselJ l x - sphericalBesselJ l y| ≤ |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := sphericalBesselJ l) (s := univ)
    (C := 1) (fun z _ ↦ differentiable_sphericalBesselJ l z) (fun z _ ↦ by
      simpa only [iteratedDeriv_one, Real.norm_eq_abs] using
        abs_iteratedDeriv_sphericalBesselJ_le l 1 z) convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs, one_mul] using h

/-- The derivatives of `r ↦ j_l (a r)` satisfy `|(d/dr)^k j_l (a r)| ≤ |a| ^ k`. -/
theorem abs_iteratedDeriv_sphericalBesselJ_comp_mul_le (l k : ℕ) (a x : ℝ) :
    |iteratedDeriv k (fun r ↦ sphericalBesselJ l (a * r)) x| ≤ |a| ^ k := by
  rw [iteratedDeriv_comp_const_mul (contDiff_sphericalBesselJ l) a,
    abs_mul, abs_pow]
  exact mul_le_of_le_one_right (by positivity) (abs_iteratedDeriv_sphericalBesselJ_le l k _)

end PDE.Analysis.SpecialFunctions
