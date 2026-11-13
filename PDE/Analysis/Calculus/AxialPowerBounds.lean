/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.AxialPowers
public import PDE.FDeriv.PartialDeriv
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Pointwise bounds for sums of axial-radial powers

For a weight `w = ∑ c_k |x_j|^{a_k} |x|^{b_k}` with nonnegative coefficients (`axialPowerSum`), the
bounds below hold at every point with `x_j ≠ 0`. The radial log-derivative `x·∇w/w` is an average
of the degrees `a_k + b_k`, so it is bounded by the largest one at every point; along a fixed ray
with `x_j ≠ 0` it tends to that degree (`tendsto_fderiv_axialPowerSum_apply_div`), but not
uniformly near the axis `x_j = 0`, where terms of a more negative axial order can dominate. In the
far region `|x| ≥ R` a comparison of single terms bounds a ratio of two weights by a sum of powers
of `R`.

These are the asymptotics of the weights in Chen and Hou, Supplement I, Section 8.3.1,
(8.28)-(8.31), and the damping bound (8.57).

## Main results

* `fderiv_axialPowerSum_apply_self`: Euler's identity `D w(x) x = ∑ c_k (a_k + b_k) T_k(x)`.
* `fderiv_axialPowerSum_apply_self_le`: `x·∇w ≤ d w` when every degree `a_k + b_k` of a nonzero
  term is at most `d`.
* `mul_partialDeriv_axialPower`:
  `x_i ∂_i(|x_j|^a |x|^b) = (a [i = j] + b x_i²/|x|²) |x_j|^a |x|^b`.
* `abs_mul_partialDeriv_axialPowerSum_le`: `|x_i ∂_i w| ≤ M w` when `|a_k| [i = j] + |b_k| ≤ M`
  for every `k`.
* `norm_mul_abs_partialDeriv_axialPowerSum_le`: for `i ≠ j`, `|x| |∂_i w| ≤ M w` when
  `|b_k| ≤ M` for every `k`.
* `axialPower_le_rpow_mul_axialPower`: for `|x| ≥ R`, `c ≤ a` and `a + b ≤ c + e`,
  `|x_j|^a |x|^b ≤ R^{(a+b)-(c+e)} |x_j|^c |x|^e`.
* `axialPowerSum_le_mul_axialPowerSum`: the termwise comparison of two weights in the far region.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Supplementary material I (in the
  same PDF), Section 8.3.1, (8.28)-(8.31), and Section 8.6, (8.57a)-(8.57b).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Real

variable {n : ℕ} (j : Fin n)

/-! ### Euler's identity at a point -/

section Euler

variable {ι : Type*} [Fintype ι] (c a b : ι → ℝ)

/-- **Euler's identity** for a sum of axial-radial powers at a point with `x_j ≠ 0`:
`D w(x) x = ∑ c_k (a_k + b_k) |x_j|^{a_k} |x|^{b_k}`. -/
theorem fderiv_axialPowerSum_apply_self {x : EuclideanSpace ℝ (Fin n)} (h0 : x j ≠ 0) :
    fderiv ℝ (axialPowerSum j c a b) x x =
      ∑ k, c k * (a k + b k) * axialPower j (a k) (b k) x := by
  rw [(hasFDerivAt_axialPowerSum j c a b h0).fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul,
    fderiv_axialPower_apply_self j _ _ h0]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

variable {c a b}

/-- **The radial derivative is at most the largest degree**: with nonnegative coefficients and
every degree `a_k + b_k ≤ d` of a term with `c_k ≠ 0`, `D w(x) x ≤ d w(x)` at every point with
`x_j ≠ 0`. -/
theorem fderiv_axialPowerSum_apply_self_le (hc : ∀ k, 0 ≤ c k) {d : ℝ}
    (hd : ∀ k, c k ≠ 0 → a k + b k ≤ d) {x : EuclideanSpace ℝ (Fin n)} (h0 : x j ≠ 0) :
    fderiv ℝ (axialPowerSum j c a b) x x ≤ d * axialPowerSum j c a b x := by
  rw [fderiv_axialPowerSum_apply_self j c a b h0, axialPowerSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  rcases eq_or_ne (c k) 0 with hk | hk
  · simp [hk]
  have hT := (axialPower_pos j (a k) (b k) h0).le
  have := mul_le_mul_of_nonneg_right (hd k hk) (mul_nonneg (hc k) hT)
  nlinarith

/-- **The radial derivative is at least the smallest degree**: with nonnegative coefficients and
every degree `a_k + b_k ≥ d` of a term with `c_k ≠ 0`, `d w(x) ≤ D w(x) x`. -/
theorem le_fderiv_axialPowerSum_apply_self (hc : ∀ k, 0 ≤ c k) {d : ℝ}
    (hd : ∀ k, c k ≠ 0 → d ≤ a k + b k) {x : EuclideanSpace ℝ (Fin n)} (h0 : x j ≠ 0) :
    d * axialPowerSum j c a b x ≤ fderiv ℝ (axialPowerSum j c a b) x x := by
  rw [fderiv_axialPowerSum_apply_self j c a b h0, axialPowerSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  rcases eq_or_ne (c k) 0 with hk | hk
  · simp [hk]
  have hT := (axialPower_pos j (a k) (b k) h0).le
  have := mul_le_mul_of_nonneg_right (hd k hk) (mul_nonneg (hc k) hT)
  nlinarith

end Euler

/-! ### Coordinate derivatives -/

section Coordinate

/-- The derivative of `|y_j|` at a point with `x_j ≠ 0`. -/
private theorem hasFDerivAt_abs_apply {x : EuclideanSpace ℝ (Fin n)} (h0 : x j ≠ 0) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) ↦ |y j|)
      ((SignType.sign (x j) : ℝ) • (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
      x := by
  have h := (hasDerivAt_abs h0).comp_hasFDerivAt x
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).hasFDerivAt
  simpa [Function.comp_def] using h

/-- The coordinate derivative of `|y|^b`: `∂_i |x|^b = b x_i |x|^b / |x|²` for `x ≠ 0`. -/
private theorem fderiv_norm_rpow_single (i : Fin n) (b : ℝ) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ≠ 0) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y‖ ^ b)
      ((b / 2 * (‖x‖ ^ 2) ^ (b / 2 - 1)) • (2 • innerSL ℝ x)) x ∧
    ((b / 2 * (‖x‖ ^ 2) ^ (b / 2 - 1)) • (2 • innerSL ℝ x)) (EuclideanSpace.single i 1) =
      b * x i * ‖x‖ ^ b / ‖x‖ ^ 2 := by
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hn2 : ‖x‖ ^ 2 ≠ 0 := by positivity
  refine ⟨?_, ?_⟩
  · have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).rpow_const (p := b / 2) (Or.inl hn2)
    have he : (fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y‖ ^ b) =
        fun y ↦ (‖y‖ ^ 2) ^ (b / 2) := funext fun y ↦ by
      rw [Real.rpow_div_two_eq_sqrt b (sq_nonneg _), Real.sqrt_sq (norm_nonneg y)]
    rw [he]
    exact h
  · simp only [smul_apply, innerSL_apply_apply, smul_eq_mul,
      EuclideanSpace.inner_single_right, one_mul, nsmul_eq_mul, Nat.cast_ofNat, conj_trivial]
    have hpow : (‖x‖ ^ 2) ^ (b / 2 - 1) = ‖x‖ ^ b / ‖x‖ ^ 2 := by
      rw [Real.rpow_sub (by positivity), Real.rpow_one, Real.rpow_div_two_eq_sqrt b (sq_nonneg _),
        Real.sqrt_sq (norm_nonneg x)]
    rw [hpow]
    field_simp

/-- The coordinate derivative of `|y_j|^a` at a point with `x_j ≠ 0`. -/
private theorem fderiv_abs_rpow_single (i : Fin n) (a : ℝ) {x : EuclideanSpace ℝ (Fin n)}
    (h0 : x j ≠ 0) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) ↦ |y j| ^ a)
      ((a * |x j| ^ (a - 1)) • ((SignType.sign (x j) : ℝ) •
        (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))) x ∧
    x i * ((a * |x j| ^ (a - 1)) • ((SignType.sign (x j) : ℝ) •
        (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))) (EuclideanSpace.single i 1) =
      (if i = j then a else 0) * |x j| ^ a := by
  have hxj : 0 < |x j| := abs_pos.2 h0
  refine ⟨(hasFDerivAt_abs_apply j h0).rpow_const (Or.inl hxj.ne'), ?_⟩
  have hp : (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (EuclideanSpace.single i 1) = if j = i then 1 else 0 := by
    simp [PiLp.single_apply]
  simp only [smul_apply, smul_eq_mul, hp]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte, mul_one]
    have hsx : (SignType.sign (x i) : ℝ) * x i = |x i| := by
      rcases lt_or_gt_of_ne h0 with hn | hp
      · rw [sign_neg hn, abs_of_neg hn]; simp
      · rw [sign_pos hp, abs_of_pos hp]; simp
    have hr : |x i| ^ (a - 1) * |x i| = |x i| ^ a := by
      rw [← Real.rpow_add_one hxj.ne', sub_add_cancel]
    calc x i * (a * |x i| ^ (a - 1) * (SignType.sign (x i) : ℝ))
        = a * (|x i| ^ (a - 1) * ((SignType.sign (x i) : ℝ) * x i)) := by ring
      _ = a * |x i| ^ a := by rw [hsx, hr]
  · simp [Ne.symm hij, hij]

/-- **Coordinate derivative of an axial-radial power**: at a point with `x_j ≠ 0`,
`∂_i(|x_j|^a |x|^b) = (a [i = j] / x_j + b x_i/|x|²) |x_j|^a |x|^b`. -/
theorem partialDeriv_axialPower (i : Fin n) (a b : ℝ) {x : EuclideanSpace ℝ (Fin n)}
    (h0 : x j ≠ 0) :
    (∂[i] (axialPower j a b)) x =
      ((if i = j then a / x j else 0) + b * x i / ‖x‖ ^ 2) * axialPower j a b x := by
  have hx : x ≠ 0 := fun h ↦ h0 (by simp [h])
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  obtain ⟨hN, hNi⟩ := fderiv_norm_rpow_single i b hx
  obtain ⟨hA, hAi⟩ := fderiv_abs_rpow_single j i a h0
  have hT := hA.fun_mul hN
  set L₁ := (b / 2 * (‖x‖ ^ 2) ^ (b / 2 - 1)) • (2 • innerSL ℝ x)
  set L₂ := (a * |x j| ^ (a - 1)) • ((SignType.sign (x j) : ℝ) •
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
  change fderiv ℝ (fun y ↦ |y j| ^ a * ‖y‖ ^ b) x (EuclideanSpace.single i 1) = _
  have hsplit : fderiv ℝ (fun y ↦ |y j| ^ a * ‖y‖ ^ b) x (EuclideanSpace.single i 1) =
      |x j| ^ a * L₁ (EuclideanSpace.single i 1) + ‖x‖ ^ b * L₂ (EuclideanSpace.single i 1) := by
    rw [hT.fderiv]
    rfl
  have hL₂ : L₂ (EuclideanSpace.single i 1) = (if i = j then a / x j else 0) * |x j| ^ a := by
    by_cases hij : i = j
    · subst hij
      have := hAi
      simp only [↓reduceIte] at this ⊢
      field_simp
      linarith
    · simp only [hij, ↓reduceIte, zero_mul, L₂, smul_apply, smul_eq_mul]
      simp [Ne.symm hij]
  rw [hsplit, hNi, hL₂, axialPower]
  ring

/-- **Coordinate log-derivative of an axial-radial power**: at a point with `x_j ≠ 0`,
`x_i ∂_i(|x_j|^a |x|^b) = (a [i = j] + b x_i²/|x|²) |x_j|^a |x|^b`. -/
theorem mul_partialDeriv_axialPower (i : Fin n) (a b : ℝ) {x : EuclideanSpace ℝ (Fin n)}
    (h0 : x j ≠ 0) :
    x i * (∂[i] (axialPower j a b)) x =
      ((if i = j then a else 0) + b * (x i ^ 2 / ‖x‖ ^ 2)) * axialPower j a b x := by
  rw [partialDeriv_axialPower j i a b h0]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    field_simp
  · simp only [hij, ↓reduceIte, zero_add]
    ring

variable {ι : Type*} [Fintype ι] {c a b : ι → ℝ}

/-- **Coordinate log-derivatives of a weight are bounded**: with nonnegative coefficients and
`|a_k| [i = j] + |b_k| ≤ M` for every `k` with `c_k ≠ 0`, `|x_i ∂_i w(x)| ≤ M w(x)` at every
point with `x_j ≠ 0`. -/
theorem abs_mul_partialDeriv_axialPowerSum_le (i : Fin n) (hc : ∀ k, 0 ≤ c k) {M : ℝ}
    (hM : ∀ k, c k ≠ 0 → |if i = j then a k else 0| + |b k| ≤ M) {x : EuclideanSpace ℝ (Fin n)}
    (h0 : x j ≠ 0) :
    |x i * (∂[i] (axialPowerSum j c a b)) x| ≤ M * axialPowerSum j c a b x := by
  have hx : x ≠ 0 := fun h ↦ h0 (by simp [h])
  have hD : (∂[i] (axialPowerSum j c a b)) x = ∑ k, c k * (∂[i] (axialPower j (a k) (b k))) x := by
    change fderiv ℝ (axialPowerSum j c a b) x (EuclideanSpace.single i 1) = _
    rw [(hasFDerivAt_axialPowerSum j c a b h0).fderiv]
    simp only [sum_apply, smul_apply, smul_eq_mul]
    rfl
  have hs : 0 ≤ x i ^ 2 / ‖x‖ ^ 2 := by positivity
  have hs1 : x i ^ 2 / ‖x‖ ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    have := EuclideanSpace.norm_sq_eq x
    rw [this]
    exact Finset.single_le_sum (f := fun k ↦ ‖x k‖ ^ 2) (fun k _ ↦ by positivity)
      (Finset.mem_univ i) |>.trans_eq' (by simp [sq_abs])
  rw [hD, Finset.mul_sum, axialPowerSum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
  rcases eq_or_ne (c k) 0 with hk | hk
  · simp [hk]
  rw [mul_left_comm, mul_partialDeriv_axialPower j i _ _ h0]
  have hT := (axialPower_pos j (a k) (b k) h0).le
  rw [abs_mul, abs_mul, abs_of_nonneg hT, abs_of_nonneg (hc k)]
  have hcoef : |(if i = j then a k else 0) + b k * (x i ^ 2 / ‖x‖ ^ 2)| ≤ M := by
    refine (abs_add_le _ _).trans ((add_le_add le_rfl ?_).trans (hM k hk))
    rw [abs_mul, abs_of_nonneg hs]
    exact mul_le_of_le_one_right (abs_nonneg _) hs1
  nlinarith [mul_le_mul_of_nonneg_right hcoef (mul_nonneg (hc k) hT)]

/-- **Off-axis coordinate derivatives of a weight**: for `i ≠ j`, with nonnegative coefficients
and `|b_k| ≤ M` for every `k` with `c_k ≠ 0`, `|x| |∂_i w(x)| ≤ M w(x)` at every point with
`x_j ≠ 0`. -/
theorem norm_mul_abs_partialDeriv_axialPowerSum_le {i : Fin n} (hij : i ≠ j) (hc : ∀ k, 0 ≤ c k)
    {M : ℝ} (hM : ∀ k, c k ≠ 0 → |b k| ≤ M) {x : EuclideanSpace ℝ (Fin n)} (h0 : x j ≠ 0) :
    ‖x‖ * |(∂[i] (axialPowerSum j c a b)) x| ≤ M * axialPowerSum j c a b x := by
  have hx : x ≠ 0 := fun h ↦ h0 (by simp [h])
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hxi : |x i| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  have hD : (∂[i] (axialPowerSum j c a b)) x = ∑ k, c k * (∂[i] (axialPower j (a k) (b k))) x := by
    change fderiv ℝ (axialPowerSum j c a b) x (EuclideanSpace.single i 1) = _
    rw [(hasFDerivAt_axialPowerSum j c a b h0).fderiv]
    simp only [sum_apply, smul_apply, smul_eq_mul]
    rfl
  rw [hD, axialPowerSum, Finset.mul_sum]
  refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hn.le).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  rcases eq_or_ne (c k) 0 with hk | hk
  · simp [hk]
  rw [partialDeriv_axialPower j i _ _ h0]
  simp only [hij, ↓reduceIte, zero_add]
  have hT := (axialPower_pos j (a k) (b k) h0).le
  rw [abs_mul, abs_mul, abs_of_nonneg hT, abs_of_nonneg (hc k), abs_div, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < ‖x‖ ^ 2)]
  have hb := hM k hk
  have hq : ‖x‖ * (|b k| * |x i| / ‖x‖ ^ 2) ≤ |b k| := by
    rw [show ‖x‖ * (|b k| * |x i| / ‖x‖ ^ 2) = |b k| * (|x i| / ‖x‖) by field_simp]
    exact mul_le_of_le_one_right (abs_nonneg _) ((div_le_one hn).2 hxi)
  calc ‖x‖ * (c k * (|b k| * |x i| / ‖x‖ ^ 2 * axialPower j (a k) (b k) x))
      = c k * axialPower j (a k) (b k) x * (‖x‖ * (|b k| * |x i| / ‖x‖ ^ 2)) := by ring
    _ ≤ c k * axialPower j (a k) (b k) x * M :=
        mul_le_mul_of_nonneg_left (hq.trans hb) (mul_nonneg (hc k) hT)
    _ = M * (c k * axialPower j (a k) (b k) x) := by ring

end Coordinate

/-! ### The far region -/

section Far

/-- **A term of higher axial order and lower degree is smaller in the far region**: for
`0 < R ≤ |x|`, `x_j ≠ 0`, `c ≤ a` and `a + b ≤ c + e`,
`|x_j|^a |x|^b ≤ R^{(a+b)-(c+e)} |x_j|^c |x|^e`, since `|x_j| ≤ |x|`. -/
theorem axialPower_le_rpow_mul_axialPower {R : ℝ} (hR : 0 < R) {x : EuclideanSpace ℝ (Fin n)}
    (hx : R ≤ ‖x‖) (h0 : x j ≠ 0) {a b c e : ℝ} (hac : c ≤ a) (hd : a + b ≤ c + e) :
    axialPower j a b x ≤ R ^ (a + b - (c + e)) * axialPower j c e x := by
  have hxj : 0 < |x j| := abs_pos.2 h0
  have hn : 0 < ‖x‖ := hR.trans_le hx
  have hjx : |x j| ≤ ‖x‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x j
  unfold axialPower
  have h1 : |x j| ^ a = |x j| ^ c * |x j| ^ (a - c) := by
    rw [← Real.rpow_add hxj]; ring_nf
  have h2 : |x j| ^ (a - c) ≤ ‖x‖ ^ (a - c) :=
    Real.rpow_le_rpow hxj.le hjx (by linarith)
  have h3 : ‖x‖ ^ (a - c) * ‖x‖ ^ b = ‖x‖ ^ (a + b - (c + e)) * ‖x‖ ^ e := by
    rw [← Real.rpow_add hn, ← Real.rpow_add hn]; ring_nf
  have h4 : ‖x‖ ^ (a + b - (c + e)) ≤ R ^ (a + b - (c + e)) :=
    Real.rpow_le_rpow_of_nonpos hR hx (by linarith)
  have hc0 : 0 ≤ |x j| ^ c := Real.rpow_nonneg (abs_nonneg _) _
  have he0 : 0 ≤ ‖x‖ ^ e := Real.rpow_nonneg (norm_nonneg _) _
  have hb0 : 0 ≤ ‖x‖ ^ b := Real.rpow_nonneg (norm_nonneg _) _
  calc |x j| ^ a * ‖x‖ ^ b = |x j| ^ c * (|x j| ^ (a - c) * ‖x‖ ^ b) := by rw [h1]; ring
    _ ≤ |x j| ^ c * (‖x‖ ^ (a - c) * ‖x‖ ^ b) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hb0) hc0
    _ = |x j| ^ c * (‖x‖ ^ (a + b - (c + e)) * ‖x‖ ^ e) := by rw [h3]
    _ ≤ |x j| ^ c * (R ^ (a + b - (c + e)) * ‖x‖ ^ e) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 he0) hc0
    _ = R ^ (a + b - (c + e)) * (|x j| ^ c * ‖x‖ ^ e) := by ring

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {c a b : ι → ℝ} {c' a' b' : κ → ℝ}

/-- **Termwise comparison of two weights in the far region**: if each term `k` of
`w = ∑ c_k |x_j|^{a_k} |x|^{b_k}` is matched with a term `σ k` of
`w' = ∑ c'_l |x_j|^{a'_l} |x|^{b'_l}` of lower axial order and higher degree, with `c'_{σ k} > 0`
(for the terms with `c_k ≠ 0`), then on `|x| ≥ R > 0`,
`w(x) ≤ (∑_k (c_k / c'_{σ k}) R^{(a_k + b_k) - (a'_{σ k} + b'_{σ k})}) w'(x)`. -/
theorem axialPowerSum_le_mul_axialPowerSum (σ : ι → κ) (hc : ∀ k, 0 ≤ c k)
    (hc' : ∀ l, 0 ≤ c' l) (hσ : ∀ k, c k ≠ 0 → 0 < c' (σ k))
    (ha : ∀ k, c k ≠ 0 → a' (σ k) ≤ a k)
    (hd : ∀ k, c k ≠ 0 → a k + b k ≤ a' (σ k) + b' (σ k)) {R : ℝ} (hR : 0 < R)
    {x : EuclideanSpace ℝ (Fin n)} (hx : R ≤ ‖x‖) (h0 : x j ≠ 0) :
    axialPowerSum j c a b x ≤
      (∑ k, c k / c' (σ k) * R ^ (a k + b k - (a' (σ k) + b' (σ k)))) *
        axialPowerSum j c' a' b' x := by
  rw [axialPowerSum, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  rcases eq_or_ne (c k) 0 with hk | hk
  · simp [hk]
  replace hσ := hσ k hk
  replace ha := ha k hk
  replace hd := hd k hk
  have hterm : c' (σ k) * axialPower j (a' (σ k)) (b' (σ k)) x ≤ axialPowerSum j c' a' b' x :=
    Finset.single_le_sum (f := fun l ↦ c' l * axialPower j (a' l) (b' l) x)
      (fun l _ ↦ mul_nonneg (hc' l) (axialPower_pos j _ _ h0).le) (Finset.mem_univ (σ k))
  have hT := axialPower_le_rpow_mul_axialPower j hR hx h0 ha hd
  have hRp : 0 ≤ R ^ (a k + b k - (a' (σ k) + b' (σ k))) := Real.rpow_nonneg hR.le _
  have hq : 0 ≤ c k / c' (σ k) := div_nonneg (hc k) hσ.le
  calc c k * axialPower j (a k) (b k) x
      ≤ c k * (R ^ (a k + b k - (a' (σ k) + b' (σ k))) *
          axialPower j (a' (σ k)) (b' (σ k)) x) := mul_le_mul_of_nonneg_left hT (hc k)
    _ = c k / c' (σ k) * R ^ (a k + b k - (a' (σ k) + b' (σ k))) *
          (c' (σ k) * axialPower j (a' (σ k)) (b' (σ k)) x) := by
        field_simp [hσ.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hterm (mul_nonneg hq hRp)

variable (c a b) in
/-- **Two weights with the same terms**: if `c_k ≤ λ c'_k` for every `k`, then `w ≤ λ w'` at
every point with `x_j ≠ 0`. -/
theorem axialPowerSum_le_mul_of_le {c'' : ι → ℝ} {μ : ℝ} (h : ∀ k, c k ≤ μ * c'' k)
    {x : EuclideanSpace ℝ (Fin n)} (h0 : x j ≠ 0) :
    axialPowerSum j c a b x ≤ μ * axialPowerSum j c'' a b x := by
  rw [axialPowerSum, axialPowerSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  have hT := (axialPower_pos j (a k) (b k) h0).le
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (h k) hT

end Far

/-- Powers of a large radius by a power of two: if `2^m ≤ R`, `e ≤ 0` and `m e ≤ -k`, then
`R^e ≤ 2^{-k}`. -/
theorem rpow_le_inv_two_pow {R e : ℝ} {m k : ℕ} (hR : 2 ^ m ≤ R) (he : e ≤ 0)
    (hk : (m : ℝ) * e ≤ -k) : R ^ e ≤ ((2 : ℝ) ^ k)⁻¹ := by
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  calc R ^ e ≤ ((2 : ℝ) ^ m) ^ e := Real.rpow_le_rpow_of_nonpos h2 hR he
    _ = (2 : ℝ) ^ ((m : ℝ) * e) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    _ ≤ (2 : ℝ) ^ (-(k : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hk
    _ = ((2 : ℝ) ^ k)⁻¹ := by rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]

end PDE.Analysis
