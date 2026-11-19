/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SmoothTransitionGlobalBounds
public import CAS.Polynomial.NestedCoefficientList

/-!
# Every derivative of the exponential transition

Write `σ = Real.smoothTransition`, which on `(0, 1)` is the exponential cutoff
`χ_e(t) = (1 + exp (1 / t + 1 / (t - 1)))⁻¹` of Chen and Hou, (D.1), and
`w(t) = t (1 - t)`, `q(t) = t ^ 2 + (1 - t) ^ 2`, so that `σ' = σ (1 - σ) q / w ^ 2`. On `(0, 1)`
every derivative of positive order is

`σ^(k+1)(t) = σ(t) (1 - σ(t)) H_k(σ(t), t) / w(t) ^ (2k + 2)`,

where `H_k` is a polynomial in `σ` and `t` with rational coefficients, a list of coefficient
lists computed by the recursion

`H_0 = q`, `H_{k+1} = q ((1 - 2σ) H_k + (σ - σ²) ∂_σ H_k) + w² ∂_t H_k - 2 (k + 1) w w' H_k`.

The formula is proved from the first derivative and the chain rule; no symbolic output enters it.
Chen and Hou write `χ_e = f(e ^ p)` with `f(s) = 1 / (1 + s)` and `p(t) = 1 / t + 1 / (t - 1)`,
and expand `χ_e^(k)` through the derivatives of `p`; our form keeps the two flat factors `σ` and
`1 - σ` explicit.

Near the flat endpoints, `σ ≤ e ^ (2 - 1 / t)` and `w ≥ t / 2` on `(0, 1/2]`, and
`e ^ (-1/t) t ^ (-m)` increases on `(0, 1/m]`, so for `t ≤ δ` with `(2k + 2) δ ≤ 1`,
`|σ^(k+1)(t)| ≤ ‖H_k‖₁ e ^ (2 - 1/δ) (2/δ) ^ (2k + 2)` with `‖H_k‖₁` the sum of the absolute
values of the coefficients, and the same bound holds for `t ≥ 1 - δ` by the reflection
`σ (1 - t) = 1 - σ t`.

## Main definitions

* `transitionNumerator`: the polynomials `H_k(σ, t)`, as lists over powers of `σ` of coefficient
  lists in `t`.

## Main results

* `iteratedDeriv_succ_smoothTransition`: the formula for `σ^(k+1)` on `(0, 1)`.
* `smoothTransition_le_exp`: `σ(t) ≤ e ^ (2 - 1 / t)` on `(0, 1/2]`.
* `iteratedDeriv_succ_smoothTransition_of_nonpos`: the derivatives of positive order vanish for
  `t ≤ 0`.
* `iteratedDeriv_succ_smoothTransition_of_one_le`: the derivatives of positive order vanish for
  `t ≥ 1`.
* `abs_iteratedDeriv_succ_smoothTransition_le_of_le`: the flat-end bound for `t ≤ δ`.
* `abs_iteratedDeriv_succ_smoothTransition_le_of_one_sub_le`: the flat-end bound for
  `t ≥ 1 - δ`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Appendix D.1.1, (D.1).
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open CAS.Polynomial
open scoped Topology

/-- `q(t) = t ^ 2 + (1 - t) ^ 2 = 1 - 2t + 2t ^ 2`. -/
def transitionRateNumerator : List ℚ := [1, -2, 2]

/-- `w(t) ^ 2 = (t (1 - t)) ^ 2 = t ^ 2 - 2t ^ 3 + t ^ 4`. -/
def transitionWidthSq : List ℚ := [0, 0, 1, -2, 1]

/-- `w(t) w'(t) = t (1 - t) (1 - 2t) = t - 3t ^ 2 + 2t ^ 3`. -/
def transitionWidthDeriv : List ℚ := [0, 1, -3, 2]

/-- The polynomials `H_k(σ, t)` of `σ^(k+1) = σ (1 - σ) H_k / w ^ (2k + 2)`, as lists over powers
of `σ` of coefficient lists in `t`. -/
def transitionNumerator : ℕ → List (List ℚ)
  | 0 => [transitionRateNumerator]
  | k + 1 => nestedTrim <|
    nestedAdd
      (nestedMulInner transitionRateNumerator
        (nestedAdd
          (nestedAdd (transitionNumerator k)
            (nestedScale (-2) (nestedShift (transitionNumerator k))))
          (nestedAdd (nestedShift (nestedDerivOuter (transitionNumerator k)))
            (nestedScale (-1) (nestedShift (nestedShift
              (nestedDerivOuter (transitionNumerator k))))))))
      (nestedAdd (nestedMulInner transitionWidthSq (nestedDerivInner (transitionNumerator k)))
        (nestedMulInner (coeffScale (-(2 * (k + 1) : ℚ)) transitionWidthDeriv)
          (transitionNumerator k)))

/-- The coefficient list `transitionRateNumerator` evaluates to `q(t) = t ^ 2 + (1 - t) ^ 2`. -/
theorem coeffEval_transitionRateNumerator (t : ℝ) :
    coeffEval transitionRateNumerator t = t ^ 2 + (1 - t) ^ 2 := by
  simp [transitionRateNumerator]; ring

/-- The coefficient list `transitionWidthSq` evaluates to `w(t) ^ 2 = (t (1 - t)) ^ 2`. -/
theorem coeffEval_transitionWidthSq (t : ℝ) :
    coeffEval transitionWidthSq t = (t * (1 - t)) ^ 2 := by
  simp [transitionWidthSq]; ring

/-- The coefficient list `transitionWidthDeriv` evaluates to `w(t) w'(t) = t (1 - t) (1 - 2t)`. -/
theorem coeffEval_transitionWidthDeriv (t : ℝ) :
    coeffEval transitionWidthDeriv t = t * (1 - t) * (1 - 2 * t) := by
  simp [transitionWidthDeriv]; ring

/-- The value of `H_{k+1}` in terms of `H_k` and its partial derivatives. -/
theorem nestedEval_transitionNumerator_succ (k : ℕ) (σ t : ℝ) :
    nestedEval (transitionNumerator (k + 1)) σ t =
      (t ^ 2 + (1 - t) ^ 2) * ((1 - 2 * σ) * nestedEval (transitionNumerator k) σ t +
          (σ - σ ^ 2) * nestedEval (nestedDerivOuter (transitionNumerator k)) σ t) +
        (t * (1 - t)) ^ 2 * nestedEval (nestedDerivInner (transitionNumerator k)) σ t -
        2 * (k + 1) * (t * (1 - t) * (1 - 2 * t)) * nestedEval (transitionNumerator k) σ t := by
  simp only [transitionNumerator, nestedEval_nestedTrim, nestedEval_nestedAdd,
    nestedEval_nestedMulInner,
    nestedEval_nestedScale, nestedEval_nestedShift, coeffEval_coeffScale,
    coeffEval_transitionRateNumerator, coeffEval_transitionWidthSq,
    coeffEval_transitionWidthDeriv]
  push_cast
  ring

/-- The rate of the first derivative over the open interval. -/
theorem smoothTransitionRate_eq {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    smoothTransitionRate t = (t ^ 2 + (1 - t) ^ 2) / (t * (1 - t)) ^ 2 := by
  have h1 : 1 - t ≠ 0 := (sub_pos.mpr ht₁).ne'
  unfold smoothTransitionRate
  field_simp
  ring

/-- `n w ^ (n - 1) = n w ^ n / w` for `w ≠ 0`, including `n = 0`. -/
theorem natCast_mul_pow_pred {w : ℝ} (hw : w ≠ 0) (n : ℕ) :
    (n : ℝ) * w ^ (n - 1) = n * w ^ n / w := by
  cases n with
  | zero => simp
  | succ n => rw [Nat.add_sub_cancel, pow_succ]; field_simp

/-- The derivatives of positive order vanish on the nonpositive half-line. -/
theorem iteratedDeriv_succ_smoothTransition_of_nonpos (k : ℕ) {t : ℝ} (ht : t ≤ 0) :
    iteratedDeriv (k + 1) Real.smoothTransition t = 0 := by
  rcases lt_or_eq_of_le ht with ht | rfl
  · have heq : Set.EqOn Real.smoothTransition (fun _ ↦ (0 : ℝ)) (Set.Iio 0) :=
      fun _ hs ↦ Real.smoothTransition.zero_of_nonpos (le_of_lt hs)
    rw [heq.iteratedDeriv_of_isOpen isOpen_Iio (k + 1) ht]
    simp
  · exact iteratedDeriv_smoothTransition_zero (k + 1)

/-- The reflection `σ (1 - t) = 1 - σ t` preserves the size of every derivative of positive
order. -/
theorem abs_iteratedDeriv_succ_smoothTransition_one_sub (k : ℕ) (t : ℝ) :
    |iteratedDeriv (k + 1) Real.smoothTransition (1 - t)| =
      |iteratedDeriv (k + 1) Real.smoothTransition t| := by
  have hrefl : (fun s ↦ Real.smoothTransition (1 - s)) =
      fun s ↦ 1 - Real.smoothTransition s := funext smoothTransition_one_sub
  have h1 : iteratedDeriv (k + 1) (fun s ↦ Real.smoothTransition (1 - s)) t =
      (-1) ^ (k + 1) * iteratedDeriv (k + 1) Real.smoothTransition (1 - t) := by
    have hneg := iteratedDeriv_comp_neg (k + 1) (fun z ↦ Real.smoothTransition (1 + z)) t
    have hshift := iteratedDeriv_comp_const_add (k + 1) Real.smoothTransition 1
    simp only [smul_eq_mul] at hneg
    rw [hshift] at hneg
    simpa [sub_eq_add_neg] using hneg
  have h2 : iteratedDeriv (k + 1) (fun s ↦ 1 - Real.smoothTransition s) t =
      -iteratedDeriv (k + 1) Real.smoothTransition t := by
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    have hd : deriv (fun s ↦ 1 - Real.smoothTransition s) = fun s ↦
        -deriv Real.smoothTransition s := by
      funext s; exact deriv_const_sub 1
    rw [hd, iteratedDeriv_fun_neg]
  rw [hrefl, h2] at h1
  have := congrArg abs h1
  rw [abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at this
  exact this.symm

/-- The derivatives of positive order vanish from `1` on. -/
theorem iteratedDeriv_succ_smoothTransition_of_one_le (k : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    iteratedDeriv (k + 1) Real.smoothTransition t = 0 := by
  have h := abs_iteratedDeriv_succ_smoothTransition_one_sub k t
  rw [iteratedDeriv_succ_smoothTransition_of_nonpos k (by linarith), abs_zero] at h
  exact abs_eq_zero.mp h.symm

/-- Every derivative of positive order of the transition. The formula is the one on `(0, 1)`;
outside, both sides vanish, through the factor `σ` or `1 - σ`. -/
theorem iteratedDeriv_succ_smoothTransition (k : ℕ) {t : ℝ} :
    iteratedDeriv (k + 1) Real.smoothTransition t =
      Real.smoothTransition t * (1 - Real.smoothTransition t) *
        nestedEval (transitionNumerator k) (Real.smoothTransition t) t /
          (t * (1 - t)) ^ (2 * k + 2) := by
  rcases le_or_gt t 0 with ht | ht
  · rw [iteratedDeriv_succ_smoothTransition_of_nonpos k ht,
      Real.smoothTransition.zero_of_nonpos ht]
    simp
  rcases le_or_gt 1 t with ht₁ | ht₁
  · rw [iteratedDeriv_succ_smoothTransition_of_one_le k ht₁,
      Real.smoothTransition.one_of_one_le ht₁]
    simp
  have hgap : 0 < 1 - t := sub_pos.mpr ht₁
  induction k generalizing t with
  | zero =>
    rw [iteratedDeriv_one, deriv_smoothTransition ht ht₁, smoothTransitionRate_eq ht ht₁]
    simp only [transitionNumerator, nestedEval_cons, nestedEval_nil, mul_zero, add_zero,
      coeffEval_transitionRateNumerator]
    ring
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv (k + 1) Real.smoothTransition =ᶠ[𝓝 t] fun s ↦
        Real.smoothTransition s * (1 - Real.smoothTransition s) *
          nestedEval (transitionNumerator k) (Real.smoothTransition s) s /
            (s * (1 - s)) ^ (2 * k + 2) := by
      filter_upwards [eventually_gt_nhds ht, eventually_lt_nhds ht₁] with s hs hs₁
      exact ih hs hs₁ (sub_pos.mpr hs₁)
    rw [heq.deriv_eq]
    have hσ := hasDerivAt_smoothTransition ht ht₁
    have hH := hasDerivAt_nestedEval (transitionNumerator k) hσ (hasDerivAt_id t)
    have hw := ((hasDerivAt_id t).mul ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))).pow
      (2 * k + 2)
    have hwne : (t * (1 - t)) ^ (2 * k + 2) ≠ 0 := pow_ne_zero _ (by positivity)
    have hd := ((hσ.mul ((hasDerivAt_const t (1 : ℝ)).sub hσ)).mul hH).div hw hwne
    have hd' : HasDerivAt (fun s ↦ Real.smoothTransition s * (1 - Real.smoothTransition s) *
        nestedEval (transitionNumerator k) (Real.smoothTransition s) s /
          (s * (1 - s)) ^ (2 * k + 2)) _ t := hd
    rw [hd'.deriv]
    simp only [id, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
    rw [nestedEval_transitionNumerator_succ, smoothTransitionRate_eq ht ht₁,
      natCast_mul_pow_pred (by positivity : t * (1 - t) ≠ 0)]
    have hpow : (t * (1 - t)) ^ (2 * (k + 1) + 2) =
        (t * (1 - t)) ^ (2 * k + 2) * (t * (1 - t)) ^ 2 := by
      rw [← pow_add]; ring_nf
    rw [hpow]
    field_simp
    push_cast
    ring

/-! ### The flat endpoints -/

/-- On `(0, 1/2]` the transition is at most `e ^ (2 - 1 / t)`. -/
theorem smoothTransition_le_exp {t : ℝ} (ht : 0 < t) (ht₂ : t ≤ 1 / 2) :
    Real.smoothTransition t ≤ Real.exp (2 - 1 / t) := by
  have ht₁ : t < 1 := by linarith
  have hgap : 0 < 1 - t := by linarith
  rw [smoothTransition_eq_inv_one_add_exp ht ht₁]
  have h1 : (1 + Real.exp (1 / t - 1 / (1 - t)))⁻¹ ≤ Real.exp (-(1 / t - 1 / (1 - t))) := by
    rw [Real.exp_neg]
    exact inv_anti₀ (Real.exp_pos _) (by linarith)
  have h2 : -(1 / t - 1 / (1 - t)) ≤ 2 - 1 / t := by
    have : 1 / (1 - t) ≤ 2 := by rw [div_le_iff₀ hgap]; linarith
    linarith
  exact h1.trans (Real.exp_le_exp.mpr h2)

/-- `e ^ (-1/t) / t ^ m` increases on `(0, 1/m]`. -/
theorem exp_neg_inv_div_pow_le {m : ℕ} {t δ : ℝ} (ht : 0 < t) (htδ : t ≤ δ)
    (hδ : m * δ ≤ 1) : Real.exp (-(1 / t)) / t ^ m ≤ Real.exp (-(1 / δ)) / δ ^ m := by
  have hδpos : 0 < δ := ht.trans_le htδ
  set u := δ / t with hu
  have hu1 : 1 ≤ u := by rw [hu, le_div_iff₀ ht]; linarith
  have hδu : δ = u * t := by rw [hu]; field_simp
  have key : u ^ m ≤ Real.exp (m * (u - 1)) := by
    calc u ^ m ≤ Real.exp (u - 1) ^ m :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (u - 1)]) m
      _ = Real.exp (m * (u - 1)) := by rw [← Real.exp_nat_mul]
  have hexp : (m : ℝ) * (u - 1) ≤ 1 / t - 1 / δ := by
    have h1 : 1 / t - 1 / δ = (u - 1) / δ := by rw [hδu]; field_simp
    rw [h1, le_div_iff₀ hδpos]
    nlinarith
  rw [div_le_div_iff₀ (pow_pos ht m) (pow_pos hδpos m)]
  calc Real.exp (-(1 / t)) * δ ^ m = Real.exp (-(1 / t)) * u ^ m * t ^ m := by
        rw [hδu, mul_pow]; ring
    _ ≤ Real.exp (-(1 / t)) * Real.exp (1 / t - 1 / δ) * t ^ m := by
        gcongr
        exact key.trans (Real.exp_le_exp.mpr hexp)
    _ = Real.exp (-(1 / δ)) * t ^ m := by rw [← Real.exp_add]; ring_nf

/-- The flat-end bound on `(0, δ]` for `(2k + 2) δ ≤ 1`. -/
theorem abs_iteratedDeriv_succ_smoothTransition_le_of_pos {k : ℕ} {t δ : ℝ} (ht : 0 < t)
    (htδ : t ≤ δ) (hδ : (2 * k + 2) * δ ≤ 1) :
    |iteratedDeriv (k + 1) Real.smoothTransition t| ≤
      nestedNorm (transitionNumerator k) * (Real.exp (2 - 1 / δ) * (2 / δ) ^ (2 * k + 2)) := by
  have hδpos : 0 < δ := ht.trans_le htδ
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have ht₂ : t ≤ 1 / 2 := by nlinarith
  have ht₁ : t < 1 := by linarith
  have hgap : 0 < 1 - t := by linarith
  set σ := Real.smoothTransition t
  have hσ0 : 0 ≤ σ := Real.smoothTransition.nonneg t
  have hσ1 : σ ≤ 1 := Real.smoothTransition.le_one t
  have hw : 0 < t * (1 - t) := by positivity
  set m := 2 * k + 2
  have hH : |nestedEval (transitionNumerator k) σ t| ≤ nestedNorm (transitionNumerator k) :=
    abs_nestedEval_le_nestedNorm _ (by rw [abs_of_nonneg hσ0]; exact hσ1)
      (by rw [abs_of_pos ht]; exact ht₁.le)
  have hN : (0 : ℝ) ≤ nestedNorm (transitionNumerator k) := by
    exact_mod_cast nestedNorm_nonneg _
  rw [iteratedDeriv_succ_smoothTransition k, abs_div, abs_mul, abs_mul,
    abs_of_nonneg hσ0, abs_of_nonneg (sub_nonneg.mpr hσ1), abs_of_pos (pow_pos hw m)]
  have hwm : (t / 2) ^ m ≤ (t * (1 - t)) ^ m :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) m
  have hmono := exp_neg_inv_div_pow_le (m := m) ht htδ (by push_cast [m]; linarith)
  calc σ * (1 - σ) * |nestedEval (transitionNumerator k) σ t| / (t * (1 - t)) ^ m
      ≤ Real.exp (2 - 1 / t) * 1 * nestedNorm (transitionNumerator k) / (t / 2) ^ m := by
        gcongr
        · exact smoothTransition_le_exp ht ht₂
        · linarith
    _ = nestedNorm (transitionNumerator k) * (Real.exp 2 * 2 ^ m) *
          (Real.exp (-(1 / t)) / t ^ m) := by
        rw [sub_eq_add_neg, Real.exp_add, div_pow]; field_simp
    _ ≤ nestedNorm (transitionNumerator k) * (Real.exp 2 * 2 ^ m) *
          (Real.exp (-(1 / δ)) / δ ^ m) := by gcongr
    _ = nestedNorm (transitionNumerator k) * (Real.exp (2 - 1 / δ) * (2 / δ) ^ m) := by
        rw [sub_eq_add_neg, Real.exp_add, div_pow]; field_simp

/-- The flat-end bound near `0`: for `t ≤ δ` with `0 < δ` and `(2k + 2) δ ≤ 1`. -/
theorem abs_iteratedDeriv_succ_smoothTransition_le_of_le {k : ℕ} {t δ : ℝ} (hδpos : 0 < δ)
    (htδ : t ≤ δ) (hδ : (2 * k + 2) * δ ≤ 1) :
    |iteratedDeriv (k + 1) Real.smoothTransition t| ≤
      nestedNorm (transitionNumerator k) * (Real.exp (2 - 1 / δ) * (2 / δ) ^ (2 * k + 2)) := by
  rcases le_or_gt t 0 with ht | ht
  · rw [iteratedDeriv_succ_smoothTransition_of_nonpos k ht, abs_zero]
    have hN : (0 : ℝ) ≤ nestedNorm (transitionNumerator k) := by
      exact_mod_cast nestedNorm_nonneg _
    positivity
  · exact abs_iteratedDeriv_succ_smoothTransition_le_of_pos ht htδ hδ

/-- The flat-end bound near `1`: for `1 - δ ≤ t`. -/
theorem abs_iteratedDeriv_succ_smoothTransition_le_of_one_sub_le {k : ℕ} {t δ : ℝ}
    (hδpos : 0 < δ) (htδ : 1 - δ ≤ t) (hδ : (2 * k + 2) * δ ≤ 1) :
    |iteratedDeriv (k + 1) Real.smoothTransition t| ≤
      nestedNorm (transitionNumerator k) * (Real.exp (2 - 1 / δ) * (2 / δ) ^ (2 * k + 2)) := by
  rw [← abs_iteratedDeriv_succ_smoothTransition_one_sub k t]
  exact abs_iteratedDeriv_succ_smoothTransition_le_of_le hδpos (by linarith) hδ

end PDE.Analysis
