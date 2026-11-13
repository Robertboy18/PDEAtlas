/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.TensorSplineNodes.Field

/-!
# Derivatives of weighted multilevel tensor fields

Two products of an unweighted multilevel tensor field `F = field n L lv 1` with a function of one
variable occur in the profile representation of Chen and Hou: the temperature is `x F(x, y)` (Part
II, (C.8), the quotient field times `x`) and the numerical stream is `ρ_p(y) F(x, y)` with the
normal weight `ρ_p` (Part II, (C.9a) and (C.10)). Their mixed derivatives follow from the tensor
form and the Leibniz rule, for orders `k, l ≤ n`, at every point of the plane.

## Main results

* `mixedDeriv_mul_field`: `∂ₓᵏ ∂ᵧˡ (x F) = x ∂ₓᵏ ∂ᵧˡ F + k ∂ₓᵏ⁻¹ ∂ᵧˡ F`.
* `mixedDeriv_field_weight`: `∂ₓᵏ ∂ᵧˡ (w(y) F) = ∑_{m ≤ l} (l choose m) w⁽ᵐ⁾(y) ∂ₓᵏ ∂ᵧˡ⁻ᵐ F`.
* `iteratedDeriv_id_mul`: the `k`-th derivative of `x f(x)` is `x f⁽ᵏ⁾(x) + k f⁽ᵏ⁻¹⁾(x)`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, (C.8)-(C.10).
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace CAS.Numerics.TensorSpline

open Finset

/-- The `k`-th derivative of `x f(x)` is `x f⁽ᵏ⁾(x) + k f⁽ᵏ⁻¹⁾(x)`. -/
theorem iteratedDeriv_id_mul {f : ℝ → ℝ} {k : ℕ} (hf : ContDiff ℝ k f) (x : ℝ) :
    iteratedDeriv k (fun x ↦ x * f x) x =
      x * iteratedDeriv k f x + k * iteratedDeriv (k - 1) f x := by
  have hid : ContDiffAt ℝ k (fun x : ℝ ↦ x) x := contDiffAt_id
  rw [iteratedDeriv_fun_mul hid hf.contDiffAt]
  rcases k with _ | k
  · simp
  rw [sum_range_succ', sum_range_succ']
  have hz : ∀ i ∈ range k, ((k + 1).choose (i + 1 + 1) : ℝ) *
      iteratedDeriv (i + 1 + 1) (fun x : ℝ ↦ x) x * iteratedDeriv (k + 1 - (i + 1 + 1)) f x = 0 :=
    fun i _ ↦ by simp [iteratedDeriv_fun_id]
  rw [sum_eq_zero hz]
  simp [iteratedDeriv_fun_id]
  ring

/-- **The `x`-weighted field.** -/
theorem mixedDeriv_mul_field (n L : ℕ) (lv : ℕ → Level) {k l : ℕ} (hk : k ≤ n) (hl : l ≤ n)
    (x y : ℝ) :
    mixedDeriv k l (fun x y ↦ x * field n L lv (fun _ ↦ 1) x y) x y =
      x * mixedDeriv k l (field n L lv (fun _ ↦ 1)) x y +
        k * mixedDeriv (k - 1) l (field n L lv (fun _ ↦ 1)) x y := by
  have hX : ∀ m i, ContDiff ℝ n (mode n (lv m).xKnots ((lv m).xModes i)) := fun _ _ ↦
    contDiff_mode n _ _
  have hY : ∀ m j, ContDiff ℝ l (fun y ↦ (fun _ : ℝ ↦ (1 : ℝ)) y *
      mode n (lv m).yKnots ((lv m).yModes j) y) := fun _ _ ↦
    contDiff_const.mul ((contDiff_mode n _ _).of_le (by exact_mod_cast hl))
  have h₁ := mixedDeriv_tensor (L := L) (I := fun m ↦ (lv m).rows) (J := fun m ↦ (lv m).cols)
    (fun m i j ↦ ((lv m).coeff i j : ℝ))
    (fun m i x ↦ x * mode n (lv m).xKnots ((lv m).xModes i) x)
    (fun m j y ↦ (fun _ : ℝ ↦ (1 : ℝ)) y * mode n (lv m).yKnots ((lv m).yModes j) y)
    (k := k) (l := l) (fun m i ↦ contDiff_id.mul ((hX m i).of_le (by exact_mod_cast hk))) hY x y
  have h₂ := mixedDeriv_tensor (L := L) (I := fun m ↦ (lv m).rows) (J := fun m ↦ (lv m).cols)
    (fun m i j ↦ ((lv m).coeff i j : ℝ))
    (fun m i x ↦ mode n (lv m).xKnots ((lv m).xModes i) x)
    (fun m j y ↦ (fun _ : ℝ ↦ (1 : ℝ)) y * mode n (lv m).yKnots ((lv m).yModes j) y)
    (k := k) (l := l) (fun m i ↦ (hX m i).of_le (by exact_mod_cast hk)) hY x y
  have h₃ := mixedDeriv_tensor (L := L) (I := fun m ↦ (lv m).rows) (J := fun m ↦ (lv m).cols)
    (fun m i j ↦ ((lv m).coeff i j : ℝ))
    (fun m i x ↦ mode n (lv m).xKnots ((lv m).xModes i) x)
    (fun m j y ↦ (fun _ : ℝ ↦ (1 : ℝ)) y * mode n (lv m).yKnots ((lv m).yModes j) y)
    (k := k - 1) (l := l) (fun m i ↦ (hX m i).of_le (by exact_mod_cast (by omega : k - 1 ≤ n)))
    hY x y
  have hF : (fun x y ↦ x * field n L lv (fun _ ↦ 1) x y) = fun x y ↦
      ∑ m ∈ range L, ∑ i ∈ range (lv m).rows, ∑ j ∈ range (lv m).cols,
        ((lv m).coeff i j : ℝ) * (x * mode n (lv m).xKnots ((lv m).xModes i) x) *
          ((fun _ : ℝ ↦ (1 : ℝ)) y * mode n (lv m).yKnots ((lv m).yModes j) y) := by
    funext x y
    unfold field
    rw [mul_sum]
    refine sum_congr rfl fun m _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    ring
  rw [hF, h₁]
  unfold field
  rw [h₂, h₃, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun m _ ↦ ?_
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [iteratedDeriv_id_mul ((hX m i).of_le (by exact_mod_cast hk))]
  ring

/-- **The `y`-weighted field.** -/
theorem mixedDeriv_field_weight (n L : ℕ) (lv : ℕ → Level) {w : ℝ → ℝ} (hw : ContDiff ℝ n w)
    {k l : ℕ} (hk : k ≤ n) (hl : l ≤ n) (x y : ℝ) :
    mixedDeriv k l (field n L lv w) x y =
      ∑ m ∈ range (l + 1), (l.choose m : ℝ) * iteratedDeriv m w y *
        mixedDeriv k (l - m) (field n L lv (fun _ ↦ 1)) x y := by
  have hX : ∀ m i, ContDiff ℝ k (mode n (lv m).xKnots ((lv m).xModes i)) := fun _ _ ↦
    (contDiff_mode n _ _).of_le (by exact_mod_cast hk)
  have hYn : ∀ m j, ContDiff ℝ n (mode n (lv m).yKnots ((lv m).yModes j)) := fun _ _ ↦
    contDiff_mode n _ _
  have h₁ := mixedDeriv_tensor (L := L) (I := fun m ↦ (lv m).rows) (J := fun m ↦ (lv m).cols)
    (fun m i j ↦ ((lv m).coeff i j : ℝ))
    (fun m i x ↦ mode n (lv m).xKnots ((lv m).xModes i) x)
    (fun m j y ↦ w y * mode n (lv m).yKnots ((lv m).yModes j) y)
    (k := k) (l := l) hX (fun m j ↦ (hw.mul (hYn m j)).of_le (by exact_mod_cast hl)) x y
  have hL : mixedDeriv k l (field n L lv w) x y =
      ∑ m ∈ range L, ∑ i ∈ range (lv m).rows, ∑ j ∈ range (lv m).cols,
        ((lv m).coeff i j : ℝ) * iteratedDeriv k (mode n (lv m).xKnots ((lv m).xModes i)) x *
          iteratedDeriv l (fun y ↦ w y * mode n (lv m).yKnots ((lv m).yModes j) y) y := by
    unfold field; exact h₁
  have hR : ∀ t ≤ l, mixedDeriv k t (field n L lv (fun _ ↦ 1)) x y =
      ∑ m ∈ range L, ∑ i ∈ range (lv m).rows, ∑ j ∈ range (lv m).cols,
        ((lv m).coeff i j : ℝ) * iteratedDeriv k (mode n (lv m).xKnots ((lv m).xModes i)) x *
          iteratedDeriv t (mode n (lv m).yKnots ((lv m).yModes j)) y := fun t ht ↦ by
    unfold field
    rw [mixedDeriv_tensor (L := L) (I := fun m ↦ (lv m).rows) (J := fun m ↦ (lv m).cols)
      (fun m i j ↦ ((lv m).coeff i j : ℝ))
      (fun m i x ↦ mode n (lv m).xKnots ((lv m).xModes i) x)
      (fun m j y ↦ (fun _ : ℝ ↦ (1 : ℝ)) y * mode n (lv m).yKnots ((lv m).yModes j) y)
      (k := k) (l := t) hX
      (fun m j ↦ contDiff_const.mul ((hYn m j).of_le (by exact_mod_cast (by omega : t ≤ n)))) x y]
    simp only [one_mul]
  rw [hL]
  have hRHS : ∑ t ∈ range (l + 1), (l.choose t : ℝ) * iteratedDeriv t w y *
        mixedDeriv k (l - t) (field n L lv (fun _ ↦ 1)) x y =
      ∑ t ∈ range (l + 1), (l.choose t : ℝ) * iteratedDeriv t w y *
        ∑ m ∈ range L, ∑ i ∈ range (lv m).rows, ∑ j ∈ range (lv m).cols,
          ((lv m).coeff i j : ℝ) * iteratedDeriv k (mode n (lv m).xKnots ((lv m).xModes i)) x *
            iteratedDeriv (l - t) (mode n (lv m).yKnots ((lv m).yModes j)) y :=
    sum_congr rfl fun t ht ↦ by rw [hR (l - t) (by simp at ht; omega)]
  rw [hRHS]
  simp_rw [mul_sum]
  conv_rhs =>
    rw [sum_comm]
    arg 2; ext m
    rw [sum_comm]
    arg 2; ext i
    rw [sum_comm]
  refine sum_congr rfl fun m _ ↦ sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  rw [iteratedDeriv_fun_mul ((hw.of_le (by exact_mod_cast hl)).contDiffAt)
    (((hYn m j).of_le (by exact_mod_cast hl)).contDiffAt), mul_sum]
  refine sum_congr rfl fun t _ ↦ ?_
  ring

end CAS.Numerics.TensorSpline
