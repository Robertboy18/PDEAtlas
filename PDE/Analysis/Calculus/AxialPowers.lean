/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.HomogeneousDerivative
public import PDE.Analysis.Asymptotics.PowerSums
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Sums of axial-radial powers along rays

An axial-radial power is `|x_j|^a |x|^b` on `ℝⁿ`; it is homogeneous of degree `a + b` and smooth
where `x_j ≠ 0`. A weight `w = ∑ c_k |x_j|^{a_k} |x|^{b_k}` with nonnegative coefficients is,
along a ray `s v` with `v_j ≠ 0`, a sum of powers of `s`, and so are its radial derivative
`Dw(s v)(s v)` (Euler's identity) and a bound of `‖Dw(s v)‖` (the scaling of derivatives of
homogeneous functions). The limits below assume a unique largest degree `d_{k₀}` with
`c_{k₀} > 0`.

## Main definitions

* `axialPower`: the axial-radial power `|x_j|^a |x|^b`.
* `axialPowerSum`: a sum `∑ c_k |x_j|^{a_k} |x|^{b_k}` of axial-radial powers.

## Main results

* `fderiv_axialPower_apply_self`: Euler's identity `D T(v) v = (a + b) T(v)`.
* `fderiv_axialPowerSum_smul_apply_smul`:
  `D w(s v)(s v) = ∑ c_k (a_k + b_k) T_k(v) s^{a_k + b_k}`.
* `tendsto_fderiv_axialPowerSum_apply_div`: `Dw(x) x / w(x) → d_{k₀}` along the ray.
* `tendsto_norm_fderiv_axialPowerSum_mul_rpow_div`: `‖Dw(s v)‖ s^{1+β} / w(s v) → 0` for `β < 0`,
  so `|Dw(x)| = O(w(x)/|x|)`.
* `eventually_axialPowerSum_le_mul`: a sum of powers of lower degrees is eventually below `μ w`
  for every `μ > 0`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Filter Topology

variable {n : ℕ}

/-- The axial-radial power `|x_j|^a |x|^b`, homogeneous of degree `a + b`. -/
def axialPower (j : Fin n) (a b : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  |x j| ^ a * ‖x‖ ^ b

/-- A sum `∑ c_k |x_j|^{a_k} |x|^{b_k}` of axial-radial powers. -/
def axialPowerSum {ι : Type*} [Fintype ι] (j : Fin n) (c a b : ι → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ k, c k * axialPower j (a k) (b k) x

variable (j : Fin n)

/-- `|(s x)_j|^a |s x|^b = s^{a+b} |x_j|^a |x|^b` for `s > 0`. -/
theorem axialPower_smul (a b : ℝ) {s : ℝ} (hs : 0 < s) (x : EuclideanSpace ℝ (Fin n)) :
    axialPower j a b (s • x) = s ^ (a + b) • axialPower j a b x := by
  simp only [axialPower, PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hs, norm_smul,
    Real.norm_eq_abs]
  rw [Real.mul_rpow hs.le (abs_nonneg _), Real.mul_rpow hs.le (norm_nonneg _),
    Real.rpow_add hs]
  ring

/-- An axial-radial power is differentiable where `x_j ≠ 0`. -/
theorem differentiableAt_axialPower (a b : ℝ) {x : EuclideanSpace ℝ (Fin n)} (h0 : x j ≠ 0) :
    DifferentiableAt ℝ (axialPower j a b) x := by
  have hx : x ≠ 0 := fun h ↦ h0 (by simp [h])
  have h1 : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦ |y j|) x := by
    have hp : ContDiffAt ℝ 1 (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) x :=
      (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).contDiff.contDiffAt
    have h := ((contDiffAt_abs (n := 1) h0).comp x hp).differentiableAt (by norm_num)
    exact h
  have h2 : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y‖) x :=
    (contDiffAt_norm ℝ (n := 1) hx).differentiableAt (by norm_num)
  exact (h1.rpow_const (Or.inl (abs_pos.2 h0).ne')).mul
    (h2.rpow_const (Or.inl (norm_ne_zero_iff.2 hx)))

/-- An axial-radial power is positive where `x_j ≠ 0`. -/
theorem axialPower_pos (a b : ℝ) {x : EuclideanSpace ℝ (Fin n)} (h0 : x j ≠ 0) :
    0 < axialPower j a b x := by
  have hx : x ≠ 0 := fun h ↦ h0 (by simp [h])
  exact mul_pos (Real.rpow_pos_of_pos (abs_pos.2 h0) _)
    (Real.rpow_pos_of_pos (norm_pos_iff.2 hx) _)

/-- Along a ray, the derivative of an axial-radial power scales:
`D T(s v) = s^{a+b-1} D T(v)`. -/
theorem fderiv_axialPower_smul (a b : ℝ) {v : EuclideanSpace ℝ (Fin n)} (h0 : v j ≠ 0) {s : ℝ}
    (hs : 0 < s) :
    fderiv ℝ (axialPower j a b) (s • v) = s ^ (a + b - 1) • fderiv ℝ (axialPower j a b) v :=
  (hasFDerivAt_smul_of_homogeneous (fun _ hs y ↦ axialPower_smul j a b hs y)
    (differentiableAt_axialPower j a b h0).hasFDerivAt hs).fderiv

/-- Euler's identity for an axial-radial power: `D T(v) v = (a + b) T(v)`. -/
theorem fderiv_axialPower_apply_self (a b : ℝ) {v : EuclideanSpace ℝ (Fin n)} (h0 : v j ≠ 0) :
    fderiv ℝ (axialPower j a b) v v = (a + b) * axialPower j a b v := by
  have h := apply_self_of_hasFDerivAt_of_homogeneous (fun _ hs y ↦ axialPower_smul j a b hs y)
    (differentiableAt_axialPower j a b h0).hasFDerivAt
  simpa [smul_eq_mul] using h

section Sum

variable {ι : Type*} [Fintype ι] (c a b : ι → ℝ)

/-- Along a ray, a sum of axial-radial powers is a sum of powers of the distance. -/
theorem axialPowerSum_smul {s : ℝ} (hs : 0 < s) (v : EuclideanSpace ℝ (Fin n)) :
    axialPowerSum j c a b (s • v) =
      ∑ k, (c k * axialPower j (a k) (b k) v) * s ^ (a k + b k) := by
  simp only [axialPowerSum, axialPower_smul _ _ _ hs, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- The derivative of a sum of axial-radial powers. -/
theorem hasFDerivAt_axialPowerSum {x : EuclideanSpace ℝ (Fin n)} (h0 : x j ≠ 0) :
    HasFDerivAt (axialPowerSum j c a b)
      (∑ k, c k • fderiv ℝ (axialPower j (a k) (b k)) x) x :=
  HasFDerivAt.fun_sum (u := Finset.univ) (A := fun k y ↦ c k * axialPower j (a k) (b k) y)
    fun k _ ↦ ((differentiableAt_axialPower j (a k) (b k) h0).hasFDerivAt).const_mul (c k)

/-- Along a ray, the radial derivative of a sum of axial-radial powers is a sum of powers:
`D w(s v)(s v) = ∑ c_k (a_k + b_k) T_k(v) s^{a_k + b_k}`. -/
theorem fderiv_axialPowerSum_smul_apply_smul {v : EuclideanSpace ℝ (Fin n)} (h0 : v j ≠ 0)
    {s : ℝ} (hs : 0 < s) :
    fderiv ℝ (axialPowerSum j c a b) (s • v) (s • v) =
      ∑ k, (c k * (a k + b k) * axialPower j (a k) (b k) v) * s ^ (a k + b k) := by
  have h0' : (s • v) j ≠ 0 := by simpa [hs.ne'] using h0
  rw [(hasFDerivAt_axialPowerSum j c a b h0').fderiv]
  simp only [sum_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [fderiv_axialPower_smul _ _ _ h0 hs]
  simp only [smul_apply, map_smul, smul_eq_mul]
  rw [fderiv_axialPower_apply_self _ _ _ h0,
    show s ^ (a k + b k) = s ^ (a k + b k - 1) * s by
      rw [← Real.rpow_add_one hs.ne', sub_add_cancel]]
  ring

/-- Along a ray, the norm of the derivative of a sum of axial-radial powers is at most a sum of
powers: `‖D w(s v)‖ ≤ ∑ |c_k| ‖D T_k(v)‖ s^{a_k + b_k - 1}`. -/
theorem norm_fderiv_axialPowerSum_smul_le {v : EuclideanSpace ℝ (Fin n)} (h0 : v j ≠ 0) {s : ℝ}
    (hs : 0 < s) :
    ‖fderiv ℝ (axialPowerSum j c a b) (s • v)‖ ≤
      ∑ k, (|c k| * ‖fderiv ℝ (axialPower j (a k) (b k)) v‖) * s ^ (a k + b k - 1) := by
  have h0' : (s • v) j ≠ 0 := by simpa [hs.ne'] using h0
  rw [(hasFDerivAt_axialPowerSum j c a b h0').fderiv]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ ↦ ?_))
  rw [fderiv_axialPower_smul _ _ _ h0 hs, smul_smul, norm_smul, Real.norm_eq_abs,
    abs_mul, abs_of_pos (Real.rpow_pos_of_pos hs _)]
  ring

/-! ### Asymptotics along a ray -/

variable {c a b} {k₀ : ι} {v : EuclideanSpace ℝ (Fin n)}

/-- A sum of axial-radial powers with nonnegative coefficients, one of them positive, is positive
where `x_j ≠ 0`. -/
theorem axialPowerSum_pos (hc : ∀ k, 0 ≤ c k) (hk₀ : 0 < c k₀) {x : EuclideanSpace ℝ (Fin n)}
    (h0 : x j ≠ 0) : 0 < axialPowerSum j c a b x :=
  Finset.sum_pos' (fun k _ ↦ mul_nonneg (hc k) (axialPower_pos j _ _ h0).le)
    ⟨k₀, Finset.mem_univ _, mul_pos hk₀ (axialPower_pos j _ _ h0)⟩

/-- **The radial log-derivative tends to the largest degree**: if `c_{k₀} > 0` and every other
term has a lower degree, then `D w(s v)(s v) / w(s v) → a_{k₀} + b_{k₀}`. -/
theorem tendsto_fderiv_axialPowerSum_apply_div (hk₀ : 0 < c k₀)
    (hd : ∀ k, k ≠ k₀ → a k + b k < a k₀ + b k₀) (h0 : v j ≠ 0) :
    Tendsto (fun s : ℝ ↦ fderiv ℝ (axialPowerSum j c a b) (s • v) (s • v) /
      axialPowerSum j c a b (s • v)) atTop (𝓝 (a k₀ + b k₀)) := by
  have hA : 0 < c k₀ * axialPower j (a k₀) (b k₀) v := mul_pos hk₀ (axialPower_pos j _ _ h0)
  have h := tendsto_sum_mul_rpow_div_sum_mul_rpow
    (A := fun k ↦ c k * axialPower j (a k) (b k) v)
    (B := fun k ↦ c k * (a k + b k) * axialPower j (a k) (b k) v)
    (d := fun k ↦ a k + b k) hA hd
  have hlim : c k₀ * (a k₀ + b k₀) * axialPower j (a k₀) (b k₀) v /
      (c k₀ * axialPower j (a k₀) (b k₀) v) = a k₀ + b k₀ := by
    rw [show c k₀ * (a k₀ + b k₀) * axialPower j (a k₀) (b k₀) v =
        (a k₀ + b k₀) * (c k₀ * axialPower j (a k₀) (b k₀) v) by ring,
      mul_div_assoc, div_self hA.ne', mul_one]
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  rw [fderiv_axialPowerSum_smul_apply_smul j c a b h0 hs, axialPowerSum_smul j c a b hs]

/-- **The gradient is of order `w/|x|`**: with nonnegative coefficients, `c_{k₀} > 0`, a unique
largest degree and `β < 0`, `‖D w(s v)‖ s^{1+β} / w(s v) → 0`. -/
theorem tendsto_norm_fderiv_axialPowerSum_mul_rpow_div (hc : ∀ k, 0 ≤ c k) (hk₀ : 0 < c k₀)
    (hd : ∀ k, k ≠ k₀ → a k + b k < a k₀ + b k₀) (h0 : v j ≠ 0) {β : ℝ} (hβ : β < 0) :
    Tendsto (fun s : ℝ ↦ ‖fderiv ℝ (axialPowerSum j c a b) (s • v)‖ * s ^ (1 + β) /
      axialPowerSum j c a b (s • v)) atTop (𝓝 0) := by
  have hA : 0 < c k₀ * axialPower j (a k₀) (b k₀) v := mul_pos hk₀ (axialPower_pos j _ _ h0)
  have h := tendsto_sum_mul_rpow_div_sum_mul_rpow_zero
    (A := fun k ↦ c k * axialPower j (a k) (b k) v)
    (B := fun k ↦ |c k| * ‖fderiv ℝ (axialPower j (a k) (b k)) v‖)
    (d := fun k ↦ a k + b k) (d' := fun k ↦ a k + b k + β) hA hd
    (fun k ↦ by
      rcases eq_or_ne k k₀ with rfl | hk
      · linarith
      · linarith [hd k hk])
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with s hs
    have hw := axialPowerSum_pos j hc hk₀ (a := a) (b := b) (x := s • v)
      (by simpa [hs.ne'] using h0)
    positivity
  · filter_upwards [eventually_gt_atTop 0] with s hs
    have hw := axialPowerSum_pos j hc hk₀ (a := a) (b := b) (x := s • v)
      (by simpa [hs.ne'] using h0)
    rw [axialPowerSum_smul j c a b hs] at hw ⊢
    refine div_le_div_of_nonneg_right ?_ hw.le
    calc ‖fderiv ℝ (axialPowerSum j c a b) (s • v)‖ * s ^ (1 + β)
        ≤ (∑ k, (|c k| * ‖fderiv ℝ (axialPower j (a k) (b k)) v‖) *
            s ^ (a k + b k - 1)) * s ^ (1 + β) :=
          mul_le_mul_of_nonneg_right (norm_fderiv_axialPowerSum_smul_le j c a b h0 hs)
            (Real.rpow_nonneg hs.le _)
      _ = _ := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [mul_assoc, ← Real.rpow_add hs]
          ring_nf

/-- **Lower degrees are negligible**: if every term of `w' = ∑ c'_k |x_j|^{a'_k} |x|^{b'_k}` has a
degree below the largest degree of `w` (with `c_{k₀} > 0`, nonnegative coefficients), then
eventually `w'(s v) ≤ μ w(s v)` for every `μ > 0`. -/
theorem eventually_axialPowerSum_le_mul {κ : Type*} [Fintype κ] {c' a' b' : κ → ℝ}
    (hc : ∀ k, 0 ≤ c k) (hk₀ : 0 < c k₀) (hd : ∀ k, k ≠ k₀ → a k + b k < a k₀ + b k₀)
    (hd' : ∀ k, a' k + b' k < a k₀ + b k₀) (h0 : v j ≠ 0) {μ : ℝ} (hμ : 0 < μ) :
    ∀ᶠ s : ℝ in atTop, axialPowerSum j c' a' b' (s • v) ≤ μ * axialPowerSum j c a b (s • v) := by
  have hA : 0 < c k₀ * axialPower j (a k₀) (b k₀) v := mul_pos hk₀ (axialPower_pos j _ _ h0)
  have h := tendsto_sum_mul_rpow_div_sum_mul_rpow_zero
    (A := fun k ↦ c k * axialPower j (a k) (b k) v)
    (B := fun k ↦ c' k * axialPower j (a' k) (b' k) v)
    (d := fun k ↦ a k + b k) (d' := fun k ↦ a' k + b' k) hA hd hd'
  filter_upwards [h.eventually (ge_mem_nhds hμ), eventually_gt_atTop 0] with s hle hs
  have hw := axialPowerSum_pos j hc hk₀ (a := a) (b := b) (x := s • v)
    (by simpa [hs.ne'] using h0)
  rw [← axialPowerSum_smul j c' a' b' hs, ← axialPowerSum_smul j c a b hs,
    div_le_iff₀ hw] at hle
  exact hle

end Sum

end PDE.Analysis
