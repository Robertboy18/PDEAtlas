/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Difference quotients from piecewise slope bounds

Chen and Hou, Part II, App E.2. Let `y₀ < y₁ < ⋯` be a mesh and `p` a function whose increments on
the piece `[yᵢ, yᵢ₊₁]` are at most `Cᵢ` times the step: `p v - p u ≤ Cᵢ (v - u)` for
`yᵢ ≤ u ≤ v ≤ yᵢ₊₁` (for instance `p' ≤ Cᵢ` there, `sub_le_of_deriv_le`). For `a ∈ [y_k, y_{k+1}]`
and `b ∈ [y_l, y_{l+1}]` with `l ≥ k + 2`, let
`M_{kl} = (∑_{k < m < l} C_m (y_{m+1} - y_m)) / (y_l - y_{k+1})` (`meanSlope`, (E.2)). Then
`(p b - p a) / (b - a) ≤ (C_k - M_{kl})₊ (y_{k+1} - y_k) / (y_l - y_k) +
(C_l - M_{kl})₊ (y_{l+1} - y_l) / (y_{l+1} - y_{k+1}) + M_{kl}` (`slope_le_slopeBound`, (E.3));
for `k ≤ l ≤ k + 1` the increment is at most `max(C_k, C_l) (b - a)`
(`sub_le_max_mul_of_adjacent`). The lower bound with `min` and the two-sided bound follow by
applying these to `-p` (`neg_slopeBound_neg_le_slope`, `abs_slope_le_slopeBound`). On a uniform
mesh the weights are `1 / (l - k)` and `M_{kl}` is the mean of the interior `C_m`
(`slopeBound_uniform`). With `Cᵢ = L` on every piece the increments glue to a global Lipschitz
bound on `[y₀, y_m]` (`abs_sub_le_of_mesh`), which turns piecewise derivative bounds of a
`C^{k,1}` function across knots into the Lipschitz hypothesis of the interpolation remainders.

The mesh only needs to increase, and the increment bounds only need to hold, on the pieces between
`k` and `l`. The bounds `Cᵢ` may have any sign in the one-sided statements.

## Main definitions

* `meanSlope`: the mean slope `M_{kl}` over the pieces strictly between `k` and `l` (E.2).
* `slopeBound`: the right side of (E.3).

## Main results

* `slope_le_slopeBound`: for `l ≥ k + 2`, `a ∈ [y_k, y_{k+1}]` and `b ∈ [y_l, y_{l+1}]`,
  `(p b - p a) / (b - a) ≤ slopeBound y C k l` (E.3).
* `sub_le_max_mul_of_adjacent`: for `k ≤ l ≤ k + 1`, `p b - p a ≤ max(C_k, C_l) (b - a)`.
* `neg_slopeBound_neg_le_slope`: lower increment bounds give
  `-slopeBound y (-C) k l ≤ (p b - p a) / (b - a)`.
* `abs_slope_le_slopeBound`: two-sided increment bounds bound the absolute difference quotient by
  `slopeBound y C k l`.
* `slopeBound_uniform`: on the mesh `y i = y₀ + i h`, the bound (E.3) is
  `((C_k - M)₊ + (C_l - M)₊) / (l - k) + M` with `M` the mean of `C_m`, `k < m < l`.
* `sub_le_of_deriv_le`: if `p' ≤ C` on `(u, v)` and `p` is continuous on `[u, v]`, then
  `p v - p u ≤ C (v - u)`.
* `abs_sub_le_of_mesh`: if `|p v - p u| ≤ L (v - u)` on every piece of the mesh
  `y₀ < y₁ < ⋯ < y_m`, then `p` is `L`-Lipschitz on `[y₀, y_m]`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Appendix E.2, (E.2)
  and (E.3). <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace PDE.Analysis.Approximation

open Set Finset

/-- The mean slope `M_{kl}` over the pieces strictly between `k` and `l` (Part II (E.2)). -/
noncomputable def meanSlope (y C : ℕ → ℝ) (k l : ℕ) : ℝ :=
  (∑ m ∈ Ico (k + 1) l, C m * (y (m + 1) - y m)) / (y l - y (k + 1))

/-- The right side of Part II (E.3). -/
noncomputable def slopeBound (y C : ℕ → ℝ) (k l : ℕ) : ℝ :=
  max (C k - meanSlope y C k l) 0 * ((y (k + 1) - y k) / (y l - y k)) +
    max (C l - meanSlope y C k l) 0 * ((y (l + 1) - y l) / (y (l + 1) - y (k + 1))) +
    meanSlope y C k l

/-- Steps of a mesh between `k` and `l + 1` give strict order between its points. -/
theorem mesh_lt_of_steps {y : ℕ → ℝ} {k l : ℕ} (hy : ∀ i, k ≤ i → i ≤ l → y i < y (i + 1))
    {i j : ℕ} (hki : k ≤ i) (hij : i < j) (hjl : j ≤ l + 1) : y i < y j := by
  induction j, hij using Nat.le_induction with
  | base => exact hy i hki (by omega)
  | succ j hj ih => exact (ih (by omega)).trans (hy j (by omega) (by omega))

/-- Steps of a mesh between `k` and `l + 1` give `y i ≤ y j` for `k ≤ i ≤ j ≤ l + 1`. -/
theorem mesh_le_of_steps {y : ℕ → ℝ} {k l : ℕ} (hy : ∀ i, k ≤ i → i ≤ l → y i < y (i + 1))
    {i j : ℕ} (hki : k ≤ i) (hij : i ≤ j) (hjl : j ≤ l + 1) : y i ≤ y j := by
  rcases hij.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (mesh_lt_of_steps hy hki hlt hjl).le

/-- Increment bounds on the pieces between `a ∈ [y_k, y_{k+1}]` and `b ∈ [y_l, y_{l+1}]`, `k < l`:
`p b - p a ≤ C_k (y_{k+1} - a) + ∑_{k < m < l} C_m (y_{m+1} - y_m) + C_l (b - y_l)`. -/
theorem sub_le_of_piecewise_increment {y C : ℕ → ℝ} {p : ℝ → ℝ} {k l : ℕ}
    (hy : ∀ i, k ≤ i → i ≤ l → y i < y (i + 1))
    (hinc : ∀ i, k ≤ i → i ≤ l → ∀ u v, y i ≤ u → u ≤ v → v ≤ y (i + 1) →
      p v - p u ≤ C i * (v - u))
    (hkl : k < l) {a b : ℝ} (ha : a ∈ Icc (y k) (y (k + 1)))
    (hb : b ∈ Icc (y l) (y (l + 1))) :
    p b - p a ≤ C k * (y (k + 1) - a) + ∑ m ∈ Ico (k + 1) l, C m * (y (m + 1) - y m) +
      C l * (b - y l) := by
  have hmid : p (y l) - p (y (k + 1)) ≤ ∑ m ∈ Ico (k + 1) l, C m * (y (m + 1) - y m) := by
    rw [← sum_Ico_sub (fun i ↦ p (y i)) (by omega : k + 1 ≤ l)]
    refine sum_le_sum fun m hm ↦ ?_
    have hm' := Finset.mem_Ico.mp hm
    exact hinc m (by omega) (by omega) _ _ le_rfl (hy m (by omega) (by omega)).le le_rfl
  have h1 := hinc k le_rfl hkl.le a (y (k + 1)) ha.1 ha.2 le_rfl
  have h2 := hinc l hkl.le le_rfl (y l) b le_rfl hb.1 hb.2
  linarith

/-- **Part II (E.3).** For `l ≥ k + 2`, `a ∈ [y_k, y_{k+1}]`, `b ∈ [y_l, y_{l+1}]`, the difference
quotient of `p` is at most `slopeBound y C k l`. -/
theorem slope_le_slopeBound {y C : ℕ → ℝ} {p : ℝ → ℝ} {k l : ℕ}
    (hy : ∀ i, k ≤ i → i ≤ l → y i < y (i + 1))
    (hinc : ∀ i, k ≤ i → i ≤ l → ∀ u v, y i ≤ u → u ≤ v → v ≤ y (i + 1) →
      p v - p u ≤ C i * (v - u))
    (hkl : k + 2 ≤ l) {a b : ℝ} (ha : a ∈ Icc (y k) (y (k + 1)))
    (hb : b ∈ Icc (y l) (y (l + 1))) :
    (p b - p a) / (b - a) ≤ slopeBound y C k l := by
  have hk1l : y (k + 1) < y l := mesh_lt_of_steps hy (by omega) (by omega) (by omega)
  have hkk1 : y k < y (k + 1) := hy k le_rfl (by omega)
  have hll1 : y l < y (l + 1) := hy l (by omega) le_rfl
  have hab : 0 < b - a := by linarith [ha.2, hb.1]
  set M := meanSlope y C k l with hM
  set A := y (k + 1) - a
  set B := b - y l
  set D := y l - y (k + 1)
  have hA : 0 ≤ A := by linarith [ha.2]
  have hB : 0 ≤ B := by linarith [hb.1]
  have hD : 0 < D := by linarith
  have hsum : ∑ m ∈ Ico (k + 1) l, C m * (y (m + 1) - y m) = M * D := by
    simp only [M, meanSlope, D]
    field_simp
  have hinc' := sub_le_of_piecewise_increment hy hinc (by omega : k < l) ha hb
  rw [hsum] at hinc'
  -- `p b - p a ≤ (C_k - M) A + (C_l - M) B + M (b - a)`
  have hba : b - a = A + D + B := by simp only [A, B, D]; ring
  have hkey : p b - p a ≤ (C k - M) * A + (C l - M) * B + M * (b - a) := by
    rw [hba]
    nlinarith
  -- the two weights
  have hwA : A / (b - a) ≤ (y (k + 1) - y k) / (y l - y k) := by
    rw [div_le_div_iff₀ hab (by linarith)]
    nlinarith [ha.1, ha.2, hb.1]
  have hwB : B / (b - a) ≤ (y (l + 1) - y l) / (y (l + 1) - y (k + 1)) := by
    rw [div_le_div_iff₀ hab (by linarith)]
    nlinarith [ha.1, ha.2, hb.1, hb.2]
  have hq : (p b - p a) / (b - a) ≤ (C k - M) * (A / (b - a)) + (C l - M) * (B / (b - a)) + M := by
    rw [div_le_iff₀ hab]
    have : ((C k - M) * (A / (b - a)) + (C l - M) * (B / (b - a)) + M) * (b - a) =
        (C k - M) * A + (C l - M) * B + M * (b - a) := by
      field_simp
    linarith
  refine hq.trans ?_
  have hA' : 0 ≤ A / (b - a) := div_nonneg hA hab.le
  have hB' : 0 ≤ B / (b - a) := div_nonneg hB hab.le
  have t1 : (C k - M) * (A / (b - a)) ≤ max (C k - M) 0 * ((y (k + 1) - y k) / (y l - y k)) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hA').trans
      (mul_le_mul_of_nonneg_left hwA (le_max_right _ _))
  have t2 : (C l - M) * (B / (b - a)) ≤
      max (C l - M) 0 * ((y (l + 1) - y l) / (y (l + 1) - y (k + 1))) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hB').trans
      (mul_le_mul_of_nonneg_left hwB (le_max_right _ _))
  simp only [slopeBound, ← hM]
  linarith

/-- **Part II, App E.2, adjacent pieces.** For `k ≤ l ≤ k + 1` the increment is at most
`max(C_k, C_l) (b - a)`. -/
theorem sub_le_max_mul_of_adjacent {y C : ℕ → ℝ} {p : ℝ → ℝ} {k l : ℕ}
    (hy : ∀ i, k ≤ i → i ≤ l → y i < y (i + 1))
    (hinc : ∀ i, k ≤ i → i ≤ l → ∀ u v, y i ≤ u → u ≤ v → v ≤ y (i + 1) →
      p v - p u ≤ C i * (v - u))
    (hkl : k ≤ l) (hlk : l ≤ k + 1) {a b : ℝ} (ha : a ∈ Icc (y k) (y (k + 1)))
    (hb : b ∈ Icc (y l) (y (l + 1))) (hab : a ≤ b) : p b - p a ≤ max (C k) (C l) * (b - a) := by
  rcases Nat.eq_or_lt_of_le hkl with rfl | hlt
  · have := hinc k le_rfl le_rfl a b ha.1 hab hb.2
    calc p b - p a ≤ C k * (b - a) := this
      _ ≤ max (C k) (C k) * (b - a) := by rw [max_self]
  · have hl : l = k + 1 := by omega
    subst hl
    have h := sub_le_of_piecewise_increment hy hinc hlt ha hb
    rw [Ico_self, sum_empty, add_zero] at h
    have hA : 0 ≤ y (k + 1) - a := by linarith [ha.2]
    have hB : 0 ≤ b - y (k + 1) := by linarith [hb.1]
    have e1 := mul_le_mul_of_nonneg_right (le_max_left (C k) (C (k + 1))) hA
    have e2 := mul_le_mul_of_nonneg_right (le_max_right (C k) (C (k + 1))) hB
    nlinarith

/-- **Part II, App E.2, lower bound.** With lower increment bounds `p v - p u ≥ Cᵢ (v - u)`,
`(p b - p a) / (b - a) ≥ min(C_k - M_{kl}, 0) w_k + min(C_l - M_{kl}, 0) w_l + M_{kl}`, written as
`-slopeBound y (-C) k l ≤ (p b - p a) / (b - a)`. -/
theorem neg_slopeBound_neg_le_slope {y C : ℕ → ℝ} {p : ℝ → ℝ} {k l : ℕ}
    (hy : ∀ i, k ≤ i → i ≤ l → y i < y (i + 1))
    (hinc : ∀ i, k ≤ i → i ≤ l → ∀ u v, y i ≤ u → u ≤ v → v ≤ y (i + 1) →
      C i * (v - u) ≤ p v - p u)
    (hkl : k + 2 ≤ l) {a b : ℝ} (ha : a ∈ Icc (y k) (y (k + 1)))
    (hb : b ∈ Icc (y l) (y (l + 1))) :
    -slopeBound y (fun i ↦ -C i) k l ≤ (p b - p a) / (b - a) := by
  have h := slope_le_slopeBound (p := fun x ↦ -p x) (C := fun i ↦ -C i) hy
    (fun i hi hi' u v hu huv hv ↦ by have := hinc i hi hi' u v hu huv hv; linarith) hkl ha hb
  have heq : (-p b - -p a) / (b - a) = -((p b - p a) / (b - a)) := by ring
  rw [heq] at h
  linarith

/-- **Part II, App E.2, two-sided.** With `|p v - p u| ≤ Cᵢ (v - u)` on each piece, the absolute
difference quotient is at most `slopeBound y C k l`. -/
theorem abs_slope_le_slopeBound {y C : ℕ → ℝ} {p : ℝ → ℝ} {k l : ℕ}
    (hy : ∀ i, k ≤ i → i ≤ l → y i < y (i + 1))
    (hinc : ∀ i, k ≤ i → i ≤ l → ∀ u v, y i ≤ u → u ≤ v → v ≤ y (i + 1) →
      |p v - p u| ≤ C i * (v - u))
    (hkl : k + 2 ≤ l) {a b : ℝ} (ha : a ∈ Icc (y k) (y (k + 1)))
    (hb : b ∈ Icc (y l) (y (l + 1))) :
    |(p b - p a) / (b - a)| ≤ slopeBound y C k l := by
  have h₁ := slope_le_slopeBound hy (fun i hi hi' u v hu huv hv ↦ (le_abs_self _).trans
    (hinc i hi hi' u v hu huv hv)) hkl ha hb
  have h₂ := slope_le_slopeBound (p := fun x ↦ -p x) hy (fun i hi hi' u v hu huv hv ↦ by
    have := hinc i hi hi' u v hu huv hv
    rw [show -p v - -p u = -(p v - p u) by ring]
    exact (neg_le_abs _).trans this) hkl ha hb
  have heq : (-p b - -p a) / (b - a) = -((p b - p a) / (b - a)) := by ring
  rw [heq] at h₂
  exact abs_le.mpr ⟨by linarith, h₁⟩

/-- **Part II, App E.2, uniform mesh.** For `y i = y₀ + i h`, `h > 0`, the bound (E.3) is
`((C_k - M)₊ + (C_l - M)₊) / (l - k) + M` with `M` the mean of `C_m`, `k < m < l`. -/
theorem slopeBound_uniform {C : ℕ → ℝ} {y₀ h : ℝ} (hh : 0 < h) {k l : ℕ} (hkl : k + 2 ≤ l) :
    slopeBound (fun i ↦ y₀ + i * h) C k l =
      (max (C k - (∑ m ∈ Ico (k + 1) l, C m) / ((l : ℝ) - k - 1)) 0 +
        max (C l - (∑ m ∈ Ico (k + 1) l, C m) / ((l : ℝ) - k - 1)) 0) / ((l : ℝ) - k) +
      (∑ m ∈ Ico (k + 1) l, C m) / ((l : ℝ) - k - 1) := by
  have hlk : (k : ℝ) + 2 ≤ l := by exact_mod_cast hkl
  have hM : meanSlope (fun i ↦ y₀ + i * h) C k l =
      (∑ m ∈ Ico (k + 1) l, C m) / ((l : ℝ) - k - 1) := by
    simp only [meanSlope, Nat.cast_add, Nat.cast_one]
    have hstep : ∀ m ∈ Finset.Ico (k + 1) l, C m * (y₀ + ((m : ℝ) + 1) * h - (y₀ + m * h)) =
        C m * h := fun m _ ↦ by ring
    rw [sum_congr rfl hstep, ← Finset.sum_mul]
    have hne : (l : ℝ) - k - 1 ≠ 0 := by linarith
    have hne' : y₀ + l * h - (y₀ + ((k : ℝ) + 1) * h) = ((l : ℝ) - k - 1) * h := by ring
    rw [hne', mul_div_mul_right _ _ hh.ne']
  simp only [slopeBound, hM, Nat.cast_add, Nat.cast_one]
  have hne : (l : ℝ) - k ≠ 0 := by linarith
  have w1 : (y₀ + ((k : ℝ) + 1) * h - (y₀ + k * h)) / (y₀ + l * h - (y₀ + k * h)) =
      1 / ((l : ℝ) - k) := by
    rw [show y₀ + ((k : ℝ) + 1) * h - (y₀ + k * h) = 1 * h by ring,
      show y₀ + l * h - (y₀ + k * h) = ((l : ℝ) - k) * h by ring, mul_div_mul_right _ _ hh.ne']
  have w2 : (y₀ + ((l : ℝ) + 1) * h - (y₀ + l * h)) / (y₀ + ((l : ℝ) + 1) * h -
      (y₀ + ((k : ℝ) + 1) * h)) = 1 / ((l : ℝ) - k) := by
    rw [show y₀ + ((l : ℝ) + 1) * h - (y₀ + l * h) = 1 * h by ring,
      show y₀ + ((l : ℝ) + 1) * h - (y₀ + ((k : ℝ) + 1) * h) = ((l : ℝ) - k) * h by ring,
      mul_div_mul_right _ _ hh.ne']
  rw [w1, w2]
  ring

/-- One-sided increments from a one-sided derivative bound: if `p` is continuous on `[u, v]` and
`p' ≤ C` on `(u, v)`, then `p v - p u ≤ C (v - u)`. -/
theorem sub_le_of_deriv_le {p p' : ℝ → ℝ} {u v C : ℝ} (huv : u ≤ v)
    (hcont : ContinuousOn p (Icc u v)) (hderiv : ∀ z ∈ Ioo u v, HasDerivAt p (p' z) z)
    (hbound : ∀ z ∈ Ioo u v, p' z ≤ C) : p v - p u ≤ C * (v - u) := by
  rcases huv.eq_or_lt with rfl | hlt
  · simp
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope p p' hlt hcont hderiv
  have hpos : 0 < v - u := sub_pos.mpr hlt
  have heq : p v - p u = p' c * (v - u) := by
    rw [hslope]
    field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_right (hbound c hc) hpos.le

/-! ### Gluing Lipschitz bounds across a mesh -/

/-- Every point of `[y₀, y_m]` lies in one of the pieces `[yᵢ, yᵢ₊₁]`, `i < m`. -/
theorem exists_mem_mesh_piece {y : ℕ → ℝ} {m : ℕ} (hm : 0 < m) {u : ℝ}
    (hu : u ∈ Icc (y 0) (y m)) : ∃ i < m, u ∈ Icc (y i) (y (i + 1)) := by
  classical
  have hP : ∃ i, u ≤ y (i + 1) := ⟨m - 1, by rw [Nat.sub_add_cancel hm]; exact hu.2⟩
  set i₀ := Nat.find hP
  have hi₀ : u ≤ y (i₀ + 1) := Nat.find_spec hP
  have hlt : i₀ < m := by
    have := Nat.find_min' hP (show u ≤ y (m - 1 + 1) by rw [Nat.sub_add_cancel hm]; exact hu.2)
    omega
  refine ⟨i₀, hlt, ?_, hi₀⟩
  rcases Nat.eq_zero_or_pos i₀ with h0 | hpos
  · rw [h0]
    exact hu.1
  · have hmin := Nat.find_min hP (show i₀ - 1 < i₀ by omega)
    rw [Nat.sub_add_cancel hpos] at hmin
    exact (not_le.mp hmin).le

/-- **Lipschitz bounds glue across a mesh.** If `|p v - p u| ≤ L (v - u)` on every piece of the
mesh `y₀ < y₁ < ⋯ < y_m`, then `p` is `L`-Lipschitz on `[y₀, y_m]`. With `p = f⁽ⁿ⁾` for a piecewise
smooth `f` whose `(n + 1)`-st derivatives on the pieces are bounded by `L`, this gives the Lipschitz
top derivative of the interpolation remainders across knots. -/
theorem abs_sub_le_of_mesh {y : ℕ → ℝ} {p : ℝ → ℝ} {m : ℕ} {L : ℝ} (hm : 0 < m)
    (hy : ∀ i, i < m → y i < y (i + 1))
    (hinc : ∀ i < m, ∀ u v, y i ≤ u → u ≤ v → v ≤ y (i + 1) → |p v - p u| ≤ L * (v - u)) :
    ∀ u ∈ Icc (y 0) (y m), ∀ v ∈ Icc (y 0) (y m), |p u - p v| ≤ L * |u - v| := by
  -- the ordered case
  have key : ∀ u ∈ Icc (y 0) (y m), ∀ v ∈ Icc (y 0) (y m), u ≤ v → |p v - p u| ≤ L * (v - u) := by
    intro u hu v hv huv
    obtain ⟨k, hk, hku⟩ := exists_mem_mesh_piece hm hu
    obtain ⟨l, hl, hlv⟩ := exists_mem_mesh_piece hm hv
    have hy' : ∀ i, k ≤ i → i ≤ l → y i < y (i + 1) := fun i _ hi ↦ hy i (by omega)
    rcases lt_trichotomy k l with hkl | rfl | hkl
    · have h₁ := sub_le_of_piecewise_increment (C := fun _ ↦ L) hy'
        (fun i _ hi u v h1 h2 h3 ↦ (le_abs_self _).trans (hinc i (by omega) u v h1 h2 h3))
        hkl hku hlv
      have h₂ := sub_le_of_piecewise_increment (C := fun _ ↦ L) (p := fun x ↦ -p x) hy'
        (fun i _ hi u v h1 h2 h3 ↦ by
          have := hinc i (by omega) u v h1 h2 h3
          rw [show -p v - -p u = -(p v - p u) by ring]
          exact (neg_le_abs _).trans this) hkl hku hlv
      have htel : ∑ i ∈ Finset.Ico (k + 1) l, L * (y (i + 1) - y i) = L * (y l - y (k + 1)) := by
        rw [← Finset.mul_sum, sum_Ico_sub y (by omega)]
      rw [htel] at h₁ h₂
      rw [abs_le]
      constructor <;> linarith
    · exact hinc k hk u v hku.1 huv hlv.2
    · -- the pieces are in the wrong order only when `u = v` is a common knot
      have h1 : y l ≤ y (k + 1) := by
        have : ∀ i j, i ≤ j → j ≤ m → y i ≤ y j := fun i j hij hjm ↦
          mesh_le_of_steps (k := 0) (l := m - 1) (fun i' _ hi' ↦ hy i' (by omega)) (by omega)
            hij (by omega)
        exact this _ _ (by omega) (by omega)
      have h2 : y (l + 1) ≤ y k := by
        have : ∀ i j, i ≤ j → j ≤ m → y i ≤ y j := fun i j hij hjm ↦
          mesh_le_of_steps (k := 0) (l := m - 1) (fun i' _ hi' ↦ hy i' (by omega)) (by omega)
            hij (by omega)
        exact this _ _ (by omega) (by omega)
      have huv' : u = v := le_antisymm huv (by linarith [hlv.2, hku.1])
      subst huv'
      simp
  intro u hu v hv
  rcases le_total u v with h | h
  · rw [abs_sub_comm, abs_sub_comm u v, abs_of_nonneg (sub_nonneg.mpr h)]
    exact key u hu v hv h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact key v hv u hu h

end PDE.Analysis.Approximation
