/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.RootFunctions
public import PDE.Analysis.Calculus.ZeroCrossing
public import PDE.Analysis.SpecialFunctions.SphericalBessel.Series
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Roots of the meridional boundary function

Write `f = meridionalBoundaryJ l = A j_l + B j_{l+1}` with `A(α) = ((l - 1)(2l + 1) - α²) α`,
`B(α) = α² - γ²` and `γ² = l (l - 1)(l + 2)`. For `α > 0` the meridional boundary function vanishes
exactly where `f` does, and its zeros `α > 0` are the meridional roots of degree `l`. For `l ≥ 2`
the cubic `Q_l` of Hou, Wang and Yang (Lemma 5) has a single root `s_l`, with `0 < s_l < l (l + 1)`,
and every meridional root satisfies `α² > s_l`; for `l = 1` every meridional root satisfies
`α² ≥ 8`. Between consecutive points of `{0}`, the zeros of `j_l` and `γ` there is exactly one
meridional root (`existsUnique_meridional_root_of_consecutive`).

## Main results

* `deriv_meridionalBoundaryJ_mul_eq`: `f'(α) (α² - γ²) = j_l(α) Q_l(α²) + D(α) f(α)` for
  `α ≠ 0`.
* `meridionalRootPolynomial_strictMono`, `exists_meridionalRootPolynomial_eq_zero`: the cubic
  for `l ≥ 2`; `meridionalRootPolynomial_neg_of_le`: `s_l > 10⁴` for `l ≥ 100`.
* `meridionalBoundaryJ_pos_of_rootPolynomial_neg`: every meridional root `α > 0` of degree
  `l ≥ 2` satisfies `α² ≥ s_l`, and `meridionalBoundaryJ_ne_zero_of_rootPolynomial_eq_zero`:
  `α² ≠ s_l`.
* `boundaryFunction_meridional_ne_zero_of_hundred_le`: no meridional root in `(0, 100)` for
  `l ≥ 100`.
* `meridional_root_unique`: at most one meridional root on an interval free of the zeros of
  `j_l` and of `α² - γ²`.
* `existsUnique_meridional_root_of_consecutive`: exactly one meridional root between consecutive
  points of `{0}`, the zeros of `j_l` and `γ`.

## How it works

We follow the proof of Lemma 5 in Appendix E of Hou, Wang and Yang, written for `f`, which has no
poles, instead of their function `F_l(k)`, so that the breakpoints carry signs instead of infinite
limits. Away from the origin the derivative formulas for `j_l` and `j_{l+1}` give
`f'(α) B(α) = j_l(α) Q_l(α²) + D(α) f(α)` (`deriv_meridionalBoundaryJ_mul_eq`), so at a zero of `f`
the sign of `f'(α) B(α)` is the sign of `j_l(α) Q_l(α²)`. For `l ≥ 2` the cubic is strictly
increasing, negative at `0` and positive at `l (l + 1)` and at `γ²`; on `(0, √s_l)` the function
`j_l` is positive and `B` negative, so the boundary function, positive at the origin, crosses zero
only upwards and stays positive (`boundaryFunction_meridional_pos_of_rootPolynomial_neg`, by
`PDE.Analysis.pos_of_le_of_deriv_pos_at_zeros`). Lemma 5 assumes that `√s_l` is not a root, and we
prove it: a zero there would have zero derivative and negative second derivative
(`meridionalBoundaryJ_ne_zero_of_rootPolynomial_eq_zero`), while for `l = 1` the alternating series
for `g_1` and `g_2` give `f < 0` on `0 < α² < 8` (`meridionalBoundaryJ_one_neg_of_sq_lt`). Between
consecutive breakpoints `j_l B` keeps its sign and every zero has `Q_l(α²) > 0`, so all zeros cross
in the same direction and there is at most one (`meridional_root_unique`). At a zero `z` of `j_l` we
have `f(z) = B(z) j_{l+1}(z)` with `j_{l+1}(z) = -j_l'(z)`, and `f(γ) = -(l - 1)² (l + 1) γ j_l(γ)`,
so `j_l B f` is negative just right of the left end and positive just left of the right end, also
where a zero of `j_l` meets `γ`, a case Lemma 5 excludes; the intermediate value theorem gives the
root (`exists_meridional_root_of_consecutive`). ## References * T. Hou, Y. Wang, and C. Yang,
"Nonuniqueness of Leray–Hopf solutions to the unforced incompressible 3D Navier–Stokes Equation",
arXiv:2509.25116v2, Section 6.2, Lemma 5, p. 52, and Appendix E, proof of Lemma 5, pp. 65-67.
<https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open PDE.Analysis.SpecialFunctions
open scoped Nat

namespace PDE.Fluid.Stokes.Ball

/-- The coefficient `D(α) = -A(α) + 2α - (l + 2)(α² - γ²) / α` of `j_{l+1}` in the derivative
of `meridionalBoundaryJ l` away from the origin. -/
def meridionalBoundaryCoefficient (l : ℕ) (α : ℝ) : ℝ :=
  -(((l : ℝ) - 1) * (2 * l + 1) - α ^ 2) * α + 2 * α -
    (α ^ 2 - l * (l - 1) * (l + 2)) * (l + 2) / α

/-- The derivative of `meridionalBoundaryJ l` in terms of `j_l`, `j_{l+1}` and their
derivatives. -/
theorem hasDerivAt_meridionalBoundaryJ (l : ℕ) (x : ℝ) :
    HasDerivAt (meridionalBoundaryJ l)
      ((((l : ℝ) - 1) * (2 * l + 1) - 3 * x ^ 2) * sphericalBesselJ l x +
        (((l : ℝ) - 1) * (2 * l + 1) - x ^ 2) * x * deriv (sphericalBesselJ l) x +
        2 * x * sphericalBesselJ (l + 1) x +
        (x ^ 2 - l * (l - 1) * (l + 2)) * deriv (sphericalBesselJ (l + 1)) x) x := by
  have hj := (differentiable_sphericalBesselJ l x).hasDerivAt
  have hk := (differentiable_sphericalBesselJ (l + 1) x).hasDerivAt
  have hA : HasDerivAt (fun y : ℝ ↦ (((l : ℝ) - 1) * (2 * l + 1) - y ^ 2) * y)
      (((l : ℝ) - 1) * (2 * l + 1) - 3 * x ^ 2) x := by
    refine (((hasDerivAt_const x (((l : ℝ) - 1) * (2 * l + 1))).fun_sub
      (hasDerivAt_pow 2 x)).fun_mul (hasDerivAt_id' x)).congr_deriv ?_
    norm_num
    ring
  have hB : HasDerivAt (fun y : ℝ ↦ y ^ 2 - l * (l - 1) * (l + 2)) (2 * x) x := by
    refine ((hasDerivAt_pow 2 x).sub_const ((l : ℝ) * (l - 1) * (l + 2))).congr_deriv ?_
    norm_num
  refine ((hA.fun_mul hj).fun_add (hB.fun_mul hk)).congr_deriv ?_
  ring

/-- For `α ≠ 0`, `f'(α) (α² - γ²) = j_l(α) Q_l(α²) + D(α) f(α)`, where
`f = meridionalBoundaryJ l` and `D = meridionalBoundaryCoefficient l`. -/
theorem deriv_meridionalBoundaryJ_mul_eq {l : ℕ} {α : ℝ} (hα : α ≠ 0) :
    deriv (meridionalBoundaryJ l) α * (α ^ 2 - l * (l - 1) * (l + 2)) =
      sphericalBesselJ l α * meridionalRootPolynomial l (α ^ 2) +
        meridionalBoundaryCoefficient l α * meridionalBoundaryJ l α := by
  rw [(hasDerivAt_meridionalBoundaryJ l α).deriv,
    (hasDerivAt_sphericalBesselJ_of_ne_zero hα l).deriv,
    (hasDerivAt_sphericalBesselJ_succ_of_ne_zero hα l).deriv]
  unfold meridionalRootPolynomial meridionalBoundaryCoefficient meridionalBoundaryJ
  field_simp
  ring

/-- At a zero `α ≠ 0` of `f = meridionalBoundaryJ l`, `f'(α) (α² - γ²) = j_l(α) Q_l(α²)`. -/
theorem deriv_meridionalBoundaryJ_mul_of_eq_zero {l : ℕ} {α : ℝ} (hα : α ≠ 0)
    (h : meridionalBoundaryJ l α = 0) :
    deriv (meridionalBoundaryJ l) α * (α ^ 2 - l * (l - 1) * (l + 2)) =
      sphericalBesselJ l α * meridionalRootPolynomial l (α ^ 2) := by
  rw [deriv_meridionalBoundaryJ_mul_eq hα, h, mul_zero, add_zero]

/-! ### The cubic `Q_l` -/

/-- `Q_l` is continuous. -/
theorem continuous_meridionalRootPolynomial (l : ℕ) :
    Continuous (meridionalRootPolynomial l) := by
  unfold meridionalRootPolynomial
  fun_prop

/-- The derivative of `Q_l` is `3 s² - 8 l² s + l (l - 1)(6l² + 11l + 7)`. -/
theorem hasDerivAt_meridionalRootPolynomial (l : ℕ) (s : ℝ) :
    HasDerivAt (meridionalRootPolynomial l)
      (3 * s ^ 2 - 8 * (l : ℝ) ^ 2 * s + l * (l - 1) * (6 * l ^ 2 + 11 * l + 7)) s := by
  have h := (((hasDerivAt_pow 3 s).fun_sub ((hasDerivAt_pow 2 s).const_mul
    (4 * (l : ℝ) ^ 2))).fun_add ((hasDerivAt_id' s).const_mul
      ((l : ℝ) * (l - 1) * (6 * l ^ 2 + 11 * l + 7)))).sub_const
    (3 * l * ((l : ℝ) - 1) ^ 2 * (l + 1) ^ 2 * (l + 2))
  refine h.congr_deriv ?_
  norm_num
  ring

/-- For `l ≥ 2` the derivative of `Q_l` is positive: its discriminant
`-4 l (2l³ + 15l² - 12l - 21)` is negative. -/
theorem meridionalRootPolynomial_deriv_pos {l : ℕ} (hl : 2 ≤ l) (s : ℝ) :
    0 < 3 * s ^ 2 - 8 * (l : ℝ) ^ 2 * s + l * (l - 1) * (6 * l ^ 2 + 11 * l + 7) := by
  have hL : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have h₁ : 0 < (l : ℝ) * (2 * l ^ 3 + 15 * l ^ 2 - 12 * l - 21) := by
    apply mul_pos (by linarith)
    nlinarith
  nlinarith [sq_nonneg (s - 4 * (l : ℝ) ^ 2 / 3)]

/-- For `l ≥ 2` the cubic `Q_l` is strictly increasing. -/
theorem meridionalRootPolynomial_strictMono {l : ℕ} (hl : 2 ≤ l) :
    StrictMono (meridionalRootPolynomial l) := by
  intro s t hst
  have hL : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have h₁ : 0 < (l : ℝ) * (2 * l ^ 3 + 15 * l ^ 2 - 12 * l - 21) := by
    apply mul_pos (by linarith)
    nlinarith
  have hq : 0 < t ^ 2 + t * s + s ^ 2 - 4 * (l : ℝ) ^ 2 * (t + s) +
      l * (l - 1) * (6 * l ^ 2 + 11 * l + 7) := by
    nlinarith [sq_nonneg (t + s - 8 * (l : ℝ) ^ 2 / 3), sq_nonneg (t - s)]
  have hsub : meridionalRootPolynomial l t - meridionalRootPolynomial l s =
      (t - s) * (t ^ 2 + t * s + s ^ 2 - 4 * (l : ℝ) ^ 2 * (t + s) +
        l * (l - 1) * (6 * l ^ 2 + 11 * l + 7)) := by
    unfold meridionalRootPolynomial
    ring
  have := mul_pos (sub_pos.mpr hst) hq
  linarith

/-- `Q_l(l (l + 1)) = 2 l (l + 1)(3l² - 2l - 3)` is positive for `l ≥ 2`. -/
theorem meridionalRootPolynomial_mul_succ_pos {l : ℕ} (hl : 2 ≤ l) :
    0 < meridionalRootPolynomial l (l * (l + 1)) := by
  have hL : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have h : meridionalRootPolynomial l (l * (l + 1)) =
      2 * l * (l + 1) * (3 * (l : ℝ) ^ 2 - 2 * l - 3) := by
    unfold meridionalRootPolynomial
    ring
  rw [h]
  apply mul_pos (by positivity)
  nlinarith

/-- `Q_l(γ²) = l (l - 1)³ (l + 1)(l + 2)(l³ - l² - l + 3)` is positive for `l ≥ 2`, where
`γ² = l (l - 1)(l + 2)`. -/
theorem meridionalRootPolynomial_gamma_pos {l : ℕ} (hl : 2 ≤ l) :
    0 < meridionalRootPolynomial l (l * (l - 1) * (l + 2)) := by
  have hL : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have h : meridionalRootPolynomial l (l * (l - 1) * (l + 2)) =
      l * ((l : ℝ) - 1) ^ 3 * (l + 1) * (l + 2) * ((l : ℝ) ^ 3 - l ^ 2 - l + 3) := by
    unfold meridionalRootPolynomial
    ring
  have h₁ : 0 < (l : ℝ) - 1 := by linarith
  rw [h]
  apply mul_pos (by positivity)
  nlinarith

/-- `Q_l(0) = -3 l (l - 1)² (l + 1)² (l + 2)` is negative for `l ≥ 2`. -/
theorem meridionalRootPolynomial_zero_neg {l : ℕ} (hl : 2 ≤ l) :
    meridionalRootPolynomial l 0 < 0 := by
  have hL : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have h₁ : 0 < (l : ℝ) - 1 := by linarith
  have h : meridionalRootPolynomial l 0 =
      -(3 * l * ((l : ℝ) - 1) ^ 2 * (l + 1) ^ 2 * (l + 2)) := by
    unfold meridionalRootPolynomial
    ring
  rw [h, neg_lt_zero]
  positivity

/-- For `l ≥ 2` the cubic `Q_l` has a root `s` with `0 < s < l (l + 1)`. -/
theorem exists_meridionalRootPolynomial_eq_zero {l : ℕ} (hl : 2 ≤ l) :
    ∃ s : ℝ, 0 < s ∧ s < l * (l + 1) ∧ meridionalRootPolynomial l s = 0 := by
  have hpos : (0 : ℝ) ≤ l * (l + 1) := by positivity
  obtain ⟨s, hs, hQ⟩ := intermediate_value_Ioo hpos
    (continuous_meridionalRootPolynomial l).continuousOn
    ⟨meridionalRootPolynomial_zero_neg hl, meridionalRootPolynomial_mul_succ_pos hl⟩
  exact ⟨s, hs.1, hs.2, hQ⟩

/-- For `l = 1` the cubic is `Q_1(s) = s² (s - 4)`. -/
theorem meridionalRootPolynomial_one (s : ℝ) :
    meridionalRootPolynomial 1 s = s ^ 2 * (s - 4) := by
  unfold meridionalRootPolynomial
  push_cast
  ring

/-- For `l ≥ 1`, once `Q_l` is positive at some `s` it stays positive to the right. -/
theorem meridionalRootPolynomial_pos_of_le {l : ℕ} (hl : 1 ≤ l) {s t : ℝ} (hst : s ≤ t)
    (h : 0 < meridionalRootPolynomial l s) : 0 < meridionalRootPolynomial l t := by
  rcases hl.eq_or_lt with rfl | hl
  · rw [meridionalRootPolynomial_one] at h ⊢
    have hs4 : 4 < s := by
      by_contra hs4
      push Not at hs4
      nlinarith [sq_nonneg s]
    have ht : 0 < t := by linarith
    have := sq_pos_of_pos ht
    nlinarith
  · exact h.trans_le ((meridionalRootPolynomial_strictMono hl).monotone hst)

/-- For `l ≥ 100`, `Q_l(s) < 0` whenever `s ≤ 10⁴`: the root `s_l` of `Q_l` exceeds `10⁴`. -/
theorem meridionalRootPolynomial_neg_of_le {l : ℕ} (hl : 100 ≤ l) {s : ℝ} (hs : s ≤ 10 ^ 4) :
    meridionalRootPolynomial l s < 0 := by
  refine ((meridionalRootPolynomial_strictMono (by omega)).monotone hs).trans_lt ?_
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hl
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h : meridionalRootPolynomial (100 + m) (10 ^ 4) =
      -(3 * (m : ℝ) ^ 6 + 1806 * m ^ 5 + 392994 * m ^ 4 + 36547588 * m ^ 3 +
        1344676403 * m ^ 2 + 21483710606 * m + 9795030600) := by
    unfold meridionalRootPolynomial
    push_cast
    ring
  rw [h, neg_lt_zero]
  positivity

/-! ### The lower bound `α ≥ √s_l` -/

/-- The meridional boundary function is differentiable. -/
theorem differentiable_boundaryFunction_meridional (l : ℕ) :
    Differentiable ℝ (boundaryFunction .meridional l) := by
  have h : boundaryFunction .meridional l = fun α ↦
      (((l : ℝ) - 1) * (2 * l + 1) - α ^ 2) * reducedSphericalBesselJ l α +
        (α ^ 2 - l * (l - 1) * (l + 2)) * reducedSphericalBesselJ (l + 1) α :=
    funext fun _ ↦ rfl
  have h₁ := differentiable_reducedSphericalBesselJ l
  have h₂ := differentiable_reducedSphericalBesselJ (l + 1)
  rw [h]
  fun_prop

/-- At a zero of the meridional boundary function, the derivative of
`meridionalBoundaryJ l = α^{l+1} boundaryFunction .meridional l` is `α^{l+1}` times its
derivative. -/
theorem deriv_meridionalBoundaryJ_of_boundaryFunction_eq_zero {l : ℕ} {α : ℝ}
    (h : boundaryFunction .meridional l α = 0) :
    deriv (meridionalBoundaryJ l) α =
      α ^ (l + 1) * deriv (boundaryFunction .meridional l) α := by
  have hF := (differentiable_boundaryFunction_meridional l α).hasDerivAt
  have heq : meridionalBoundaryJ l = fun y ↦ y ^ (l + 1) * boundaryFunction .meridional l y :=
    funext fun y ↦ (pow_mul_boundaryFunction_meridional_eq l y).symm
  rw [heq, ((hasDerivAt_pow (l + 1) α).fun_mul hF).deriv, h]
  ring

/-- At the origin the meridional boundary function of degree `l ≥ 2` is
`3 (l - 1)(l + 1)² / (2l + 3)‼ > 0`. -/
theorem boundaryFunction_meridional_zero_pos {l : ℕ} (hl : 2 ≤ l) :
    0 < boundaryFunction .meridional l 0 := by
  have hL : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hd : (0 : ℝ) < ((2 * l + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have hdf : (2 * (l + 1) + 1)‼ = (2 * l + 3) * (2 * l + 1)‼ := by
    rw [show 2 * (l + 1) + 1 = 2 * l + 1 + 2 by ring, Nat.doubleFactorial_add_two]
  simp only [boundaryFunction, reducedSphericalBesselJ_zero, hdf]
  push_cast
  have h : (((l : ℝ) - 1) * (2 * l + 1) - 0 ^ 2) * (1 / ((2 * l + 1)‼ : ℕ)) +
      (0 ^ 2 - l * (l - 1) * (l + 2)) * (1 / ((2 * l + 3) * ((2 * l + 1)‼ : ℕ))) =
      3 * ((l : ℝ) - 1) * (l + 1) ^ 2 / ((2 * l + 3) * ((2 * l + 1)‼ : ℕ)) := by
    field_simp
    ring
  rw [h]
  apply div_pos _ (by positivity)
  have : (0 : ℝ) < l - 1 := by linarith
  positivity

/-- **Lower bound for the meridional roots.** For `l ≥ 2` the meridional boundary function is
positive at every `α ≥ 0` with `Q_l(α²) < 0`. -/
theorem boundaryFunction_meridional_pos_of_rootPolynomial_neg {l : ℕ} (hl : 2 ≤ l) {α : ℝ}
    (hα : 0 ≤ α) (h : meridionalRootPolynomial l (α ^ 2) < 0) :
    0 < boundaryFunction .meridional l α := by
  have hmono := meridionalRootPolynomial_strictMono hl
  set S : Set ℝ := {t | 0 ≤ t ∧ meridionalRootPolynomial l (t ^ 2) < 0} with hSdef
  have hS : S.OrdConnected := ⟨fun a ha b hb x hx ↦ ⟨ha.1.trans hx.1,
    (hmono.monotone (pow_le_pow_left₀ (ha.1.trans hx.1) hx.2 2)).trans_lt hb.2⟩⟩
  have hc : ContinuousOn (boundaryFunction .meridional l) S :=
    (differentiable_boundaryFunction_meridional l).continuous.continuousOn
  have hd : ∀ x ∈ S, boundaryFunction .meridional l x = 0 →
      DifferentiableAt ℝ (boundaryFunction .meridional l) x ∧
        0 < deriv (boundaryFunction .meridional l) x := by
    intro x hx hFx
    refine ⟨differentiable_boundaryFunction_meridional l x, ?_⟩
    have hx0 : 0 < x :=
      hx.1.lt_of_ne fun h0 ↦ (boundaryFunction_meridional_zero_pos hl).ne' (h0 ▸ hFx)
    have hf : meridionalBoundaryJ l x = 0 := by
      rw [← pow_mul_boundaryFunction_meridional_eq, hFx, mul_zero]
    have hder := deriv_meridionalBoundaryJ_mul_of_eq_zero hx0.ne' hf
    rw [deriv_meridionalBoundaryJ_of_boundaryFunction_eq_zero hFx] at hder
    have hlt₁ : x ^ 2 < l * (l + 1) :=
      hmono.lt_iff_lt.mp (hx.2.trans (meridionalRootPolynomial_mul_succ_pos hl))
    have hlt₂ : x ^ 2 < l * (l - 1) * (l + 2) :=
      hmono.lt_iff_lt.mp (hx.2.trans (meridionalRootPolynomial_gamma_pos hl))
    have hj := sphericalBesselJ_pos_of_sq_le hx0 hlt₁.le
    have hjQ := mul_neg_of_pos_of_neg hj hx.2
    have hP : 0 < x ^ (l + 1) * deriv (boundaryFunction .meridional l) x := by
      nlinarith
    exact pos_of_mul_pos_right hP (pow_pos hx0 _).le
  have h0 : (0 : ℝ) ∈ S := ⟨le_rfl, by simpa using meridionalRootPolynomial_zero_neg hl⟩
  exact PDE.Analysis.pos_of_le_of_deriv_pos_at_zeros hS hc hd h0 ⟨hα, h⟩ hα
    (boundaryFunction_meridional_zero_pos hl)

/-- For `l ≥ 2`, `meridionalBoundaryJ l α > 0` at every `α > 0` with `Q_l(α²) < 0`. -/
theorem meridionalBoundaryJ_pos_of_rootPolynomial_neg {l : ℕ} (hl : 2 ≤ l) {α : ℝ}
    (hα : 0 < α) (h : meridionalRootPolynomial l (α ^ 2) < 0) : 0 < meridionalBoundaryJ l α := by
  rw [← pow_mul_boundaryFunction_meridional_eq]
  exact mul_pos (pow_pos hα _)
    (boundaryFunction_meridional_pos_of_rootPolynomial_neg hl hα.le h)

/-- For `l = 1`, `meridionalBoundaryJ 1 α = α⁴ (g_2(α) - g_1(α))`. -/
theorem meridionalBoundaryJ_one_eq (α : ℝ) :
    meridionalBoundaryJ 1 α =
      α ^ 4 * (reducedSphericalBesselJ 2 α - reducedSphericalBesselJ 1 α) := by
  simp only [meridionalBoundaryJ, sphericalBesselJ_eq_pow_mul]
  push_cast
  ring

/-- For `l = 1`, `meridionalBoundaryJ 1 α < 0` for `0 < α² < 8`: the alternating series give
`g_2 ≤ 1/15` and `g_1 ≥ 1/3 - α²/30`. -/
theorem meridionalBoundaryJ_one_neg_of_sq_lt {α : ℝ} (hα : α ≠ 0) (h : α ^ 2 < 8) :
    meridionalBoundaryJ 1 α < 0 := by
  have h₂ := (reducedSphericalBesselJ_sub_sum_mem (l := 2) (K := 0) (x := α)
    (by norm_num; linarith)).2
  have h₁ := (reducedSphericalBesselJ_sub_sum_mem (l := 1) (K := 1) (x := α)
    (by norm_num; linarith)).2
  norm_num [sphericalBesselTermAbs, sphericalBesselTerm, Nat.doubleFactorial] at h₁ h₂
  rw [meridionalBoundaryJ_one_eq]
  have hα4 : 0 < α ^ 4 := by positivity
  apply mul_neg_of_pos_of_neg hα4
  nlinarith

/-- For `l = 1`, `meridionalBoundaryJ 1 α < 0` for `0 < α < 2`, which is where `Q_1(α²) < 0`. -/
theorem meridionalBoundaryJ_one_neg {α : ℝ} (hα : 0 < α) (h : α < 2) :
    meridionalBoundaryJ 1 α < 0 :=
  meridionalBoundaryJ_one_neg_of_sq_lt hα.ne' (by nlinarith)

/-- For `l ≥ 1` the meridional boundary function has no zero `α > 0` with `Q_l(α²) < 0`. -/
theorem boundaryFunction_meridional_ne_zero_of_rootPolynomial_neg {l : ℕ} (hl : 1 ≤ l) {α : ℝ}
    (hα : 0 < α) (h : meridionalRootPolynomial l (α ^ 2) < 0) :
    boundaryFunction .meridional l α ≠ 0 := by
  rcases hl.eq_or_lt with rfl | hl
  · rw [meridionalRootPolynomial_one] at h
    rw [ne_eq, boundaryFunction_meridional_eq_zero_iff hα]
    refine (meridionalBoundaryJ_one_neg_of_sq_lt hα.ne' ?_).ne
    have : 0 < (α ^ 2) ^ 2 := by positivity
    nlinarith
  · exact (boundaryFunction_meridional_pos_of_rootPolynomial_neg hl hα.le h).ne'

/-- For `l ≥ 100` the meridional boundary function has no zero in `(0, 100)`. -/
theorem boundaryFunction_meridional_ne_zero_of_hundred_le {l : ℕ} (hl : 100 ≤ l) {α : ℝ}
    (hα : 0 < α) (h : α < 100) : boundaryFunction .meridional l α ≠ 0 :=
  boundaryFunction_meridional_ne_zero_of_rootPolynomial_neg (by omega) hα
    (meridionalRootPolynomial_neg_of_le hl (by nlinarith))

/-! ### No zero at the root of `Q_l` -/

/-- `meridionalBoundaryJ l` is smooth. -/
theorem contDiff_meridionalBoundaryJ (l : ℕ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (meridionalBoundaryJ l) := by
  unfold meridionalBoundaryJ
  have h₁ := contDiff_sphericalBesselJ l (n := n)
  have h₂ := contDiff_sphericalBesselJ (l + 1) (n := n)
  fun_prop

/-- For `l ≥ 2`, `meridionalBoundaryJ l` does not vanish at `α = √s_l > 0`, the root of `Q_l`.
At such a zero the derivative would vanish and the second derivative would be negative, so the
function would be negative just to the left of `α`, where it is positive. -/
theorem meridionalBoundaryJ_ne_zero_of_rootPolynomial_eq_zero {l : ℕ} (hl : 2 ≤ l) {α : ℝ}
    (hα : 0 < α) (h : meridionalRootPolynomial l (α ^ 2) = 0) : meridionalBoundaryJ l α ≠ 0 := by
  intro hf
  have hmono := meridionalRootPolynomial_strictMono hl
  have hlt₁ : α ^ 2 < l * (l + 1) :=
    hmono.lt_iff_lt.mp (h ▸ meridionalRootPolynomial_mul_succ_pos hl)
  have hlt₂ : α ^ 2 < l * (l - 1) * (l + 2) :=
    hmono.lt_iff_lt.mp (h ▸ meridionalRootPolynomial_gamma_pos hl)
  have hj := sphericalBesselJ_pos_of_sq_le hα hlt₁.le
  have hB : α ^ 2 - l * (l - 1) * (l + 2) < 0 := sub_neg.mpr hlt₂
  have hf' : deriv (meridionalBoundaryJ l) α = 0 := by
    have hder := deriv_meridionalBoundaryJ_mul_of_eq_zero hα.ne' hf
    rw [h, mul_zero] at hder
    exact (mul_eq_zero.mp hder).resolve_right hB.ne
  have hdd : Differentiable ℝ (deriv (meridionalBoundaryJ l)) := by
    simpa only [iteratedDeriv_one] using
      (contDiff_meridionalBoundaryJ l (n := 2)).differentiable_iteratedDeriv 1 (by norm_num)
  set f₂ := deriv (deriv (meridionalBoundaryJ l)) α with hf₂
  have heq : (fun y ↦ deriv (meridionalBoundaryJ l) y * (y ^ 2 - l * (l - 1) * (l + 2)) -
      meridionalBoundaryCoefficient l y * meridionalBoundaryJ l y) =ᶠ[nhds α]
      fun y ↦ sphericalBesselJ l y * meridionalRootPolynomial l (y ^ 2) := by
    filter_upwards [isOpen_ne.mem_nhds hα.ne'] with y hy
    rw [deriv_meridionalBoundaryJ_mul_eq hy]
    ring
  have hD : DifferentiableAt ℝ (meridionalBoundaryCoefficient l) α := by
    unfold meridionalBoundaryCoefficient
    fun_prop (disch := exact hα.ne')
  have hL : HasDerivAt (fun y ↦ deriv (meridionalBoundaryJ l) y *
      (y ^ 2 - l * (l - 1) * (l + 2)) -
      meridionalBoundaryCoefficient l y * meridionalBoundaryJ l y)
      (f₂ * (α ^ 2 - l * (l - 1) * (l + 2))) α := by
    have h₁ := ((hdd α).hasDerivAt.fun_mul
      ((hasDerivAt_pow 2 α).sub_const ((l : ℝ) * (l - 1) * (l + 2)))).fun_sub
      (hD.hasDerivAt.fun_mul (differentiable_meridionalBoundaryJ l α).hasDerivAt)
    refine h₁.congr_deriv ?_
    rw [hf', hf, ← hf₂]
    ring
  have hR : HasDerivAt (fun y ↦ sphericalBesselJ l y * meridionalRootPolynomial l (y ^ 2))
      (sphericalBesselJ l α * ((3 * (α ^ 2) ^ 2 - 8 * (l : ℝ) ^ 2 * α ^ 2 +
        l * (l - 1) * (6 * l ^ 2 + 11 * l + 7)) * (2 * α))) α := by
    have h₁ := (differentiable_sphericalBesselJ l α).hasDerivAt.fun_mul
      ((hasDerivAt_meridionalRootPolynomial l (α ^ 2)).comp α (hasDerivAt_pow 2 α))
    refine h₁.congr_deriv ?_
    rw [Function.comp_apply, h]
    norm_num
  have key := heq.deriv_eq
  rw [hL.deriv, hR.deriv] at key
  have hQ' := meridionalRootPolynomial_deriv_pos hl (α ^ 2)
  have hneg : f₂ < 0 := neg_of_mul_pos_left (by rw [key]; positivity) hB.le
  have hev : ∀ᶠ t in nhdsWithin α (Set.Iio α), 0 < deriv (meridionalBoundaryJ l) t := by
    have hneg' : DifferentiableAt ℝ (fun y ↦ -deriv (meridionalBoundaryJ l) y) α := (hdd α).neg
    filter_upwards [PDE.Analysis.eventually_neg_left_of_deriv_pos hneg' (by rw [hf', neg_zero])
      (by rw [deriv.fun_neg, ← hf₂]; linarith)] with t ht
    linarith
  obtain ⟨a, ha, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hev
  set t := max a (α / 2) with ht
  have ht₀ : 0 < t := lt_max_of_lt_right (by linarith)
  have htα : t < α := max_lt ha (by linarith)
  have hstrict : StrictMonoOn (meridionalBoundaryJ l) (Set.Icc t α) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc t α)
      (differentiable_meridionalBoundaryJ l).continuous.continuousOn fun y hy ↦ ?_
    rw [interior_Icc] at hy
    exact hsub ⟨(le_max_left a _).trans_lt hy.1, hy.2⟩
  have hft := hf ▸ hstrict ⟨le_rfl, htα.le⟩ ⟨htα.le, le_rfl⟩ htα
  have hQt : meridionalRootPolynomial l (t ^ 2) < 0 :=
    h ▸ hmono (pow_lt_pow_left₀ htα ht₀.le two_ne_zero)
  exact (meridionalBoundaryJ_pos_of_rootPolynomial_neg hl ht₀ hQt).not_gt hft

/-- For `l ≥ 1` the meridional boundary function has no zero `α > 0` with `Q_l(α²) ≤ 0`. -/
theorem boundaryFunction_meridional_ne_zero_of_rootPolynomial_nonpos {l : ℕ} (hl : 1 ≤ l)
    {α : ℝ} (hα : 0 < α) (h : meridionalRootPolynomial l (α ^ 2) ≤ 0) :
    boundaryFunction .meridional l α ≠ 0 := by
  rcases h.lt_or_eq with h | h
  · exact boundaryFunction_meridional_ne_zero_of_rootPolynomial_neg hl hα h
  rw [ne_eq, boundaryFunction_meridional_eq_zero_iff hα]
  rcases hl.eq_or_lt with rfl | hl
  · rw [meridionalRootPolynomial_one] at h
    have hα4 : α ^ 2 = 4 := by linarith [(mul_eq_zero.mp h).resolve_left (by positivity)]
    exact (meridionalBoundaryJ_one_neg_of_sq_lt hα.ne' (by linarith)).ne
  · exact meridionalBoundaryJ_ne_zero_of_rootPolynomial_eq_zero hl hα h

/-! ### Uniqueness between consecutive zeros of `j_l (α² - γ²)` -/

/-- **Uniqueness of the meridional root.** On an interval `(a, b)` with `0 ≤ a` on which neither
`j_l` nor `α² - γ²` vanishes, the meridional boundary function of degree `l ≥ 1` has at most
one zero. -/
theorem meridional_root_unique {l : ℕ} (hl : 1 ≤ l) {a b : ℝ} (ha : 0 ≤ a)
    (hne : ∀ x ∈ Set.Ioo a b, sphericalBesselJ l x ≠ 0)
    (hγ : ∀ x ∈ Set.Ioo a b, x ^ 2 ≠ l * (l - 1) * (l + 2)) {x y : ℝ}
    (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b)
    (hfx : boundaryFunction .meridional l x = 0) (hfy : boundaryFunction .meridional l y = 0) :
    x = y := by
  have hQpos : ∀ t ∈ Set.Ioo a b, boundaryFunction .meridional l t = 0 →
      0 < meridionalRootPolynomial l (t ^ 2) := fun t ht hFt ↦ lt_of_not_ge fun hle ↦
    boundaryFunction_meridional_ne_zero_of_rootPolynomial_nonpos hl (ha.trans_lt ht.1) hle hFt
  set P : ℝ → ℝ := fun t ↦ sphericalBesselJ l t * (t ^ 2 - l * (l - 1) * (l + 2)) with hPdef
  have hPc : ContinuousOn P (Set.Ioo a b) := by
    have := continuous_sphericalBesselJ l
    exact Continuous.continuousOn (by fun_prop)
  have hP0 : ∀ t ∈ Set.Ioo a b, P t ≠ 0 := fun t ht ↦
    mul_ne_zero (hne t ht) (sub_ne_zero.mpr (hγ t ht))
  set S : Set ℝ := {t | t ∈ Set.Ioo a b ∧ 0 < meridionalRootPolynomial l (t ^ 2)} with hSdef
  have hS : S.OrdConnected := ⟨fun u hu v hv w hw ↦
    ⟨⟨hu.1.1.trans_le hw.1, hw.2.trans_lt hv.1.2⟩, meridionalRootPolynomial_pos_of_le hl
      (pow_le_pow_left₀ (ha.trans hu.1.1.le) hw.1 2) hu.2⟩⟩
  set g : ℝ → ℝ := fun t ↦ P x * boundaryFunction .meridional l t with hg
  have hgc : ContinuousOn g S :=
    ((differentiable_boundaryFunction_meridional l).continuous.const_smul (P x)).continuousOn
  have hd : ∀ t ∈ S, g t = 0 → DifferentiableAt ℝ g t ∧ 0 < deriv g t := by
    intro t ht hgt
    have hFt : boundaryFunction .meridional l t = 0 :=
      (mul_eq_zero.mp hgt).resolve_left (hP0 x hx)
    have hFd := differentiable_boundaryFunction_meridional l t
    refine ⟨hFd.const_mul _, ?_⟩
    rw [hg, deriv_const_mul _ hFd]
    have ht₀ : 0 < t := ha.trans_lt ht.1.1
    have hf : meridionalBoundaryJ l t = 0 := by
      rw [← pow_mul_boundaryFunction_meridional_eq, hFt, mul_zero]
    have hder := deriv_meridionalBoundaryJ_mul_of_eq_zero ht₀.ne' hf
    rw [deriv_meridionalBoundaryJ_of_boundaryFunction_eq_zero hFt] at hder
    have hPt := PDE.Analysis.sign_eq_of_forall_ne_zero Set.ordConnected_Ioo hPc hP0 hx ht.1
    have hcj : P x * sphericalBesselJ l t ≠ 0 := mul_ne_zero (hP0 x hx) (hne t ht.1)
    have hPeq : P t = sphericalBesselJ l t * (t ^ 2 - l * (l - 1) * (l + 2)) := rfl
    have hpos : 0 < (P x * deriv (boundaryFunction .meridional l) t * t ^ (l + 1)) *
        (P x * P t) := by
      rw [show (P x * deriv (boundaryFunction .meridional l) t * t ^ (l + 1)) * (P x * P t) =
          (P x * sphericalBesselJ l t) ^ 2 * meridionalRootPolynomial l (t ^ 2) by
        linear_combination P x ^ 2 * sphericalBesselJ l t * hder +
          P x * deriv (boundaryFunction .meridional l) t * t ^ (l + 1) * P x * hPeq]
      exact mul_pos (sq_pos_iff.mpr hcj) ht.2
    have h₁ := (pos_iff_pos_of_mul_pos hpos).mpr hPt
    exact pos_of_mul_pos_left h₁ (pow_pos ht₀ _).le
  exact PDE.Analysis.eq_of_deriv_pos_at_zeros hS hgc hd ⟨hx, hQpos x hx hfx⟩
    ⟨hy, hQpos y hy hfy⟩ (by simp only [hg, hfx, mul_zero]) (by simp only [hg, hfy, mul_zero])

/-! ### Existence between consecutive zeros of `j_l (α² - γ²)` -/

/-- At a zero `z` of `j_l`, `meridionalBoundaryJ l z = (z² - γ²) j_{l+1}(z)`. -/
theorem meridionalBoundaryJ_of_sphericalBesselJ_eq_zero {l : ℕ} {z : ℝ}
    (h : sphericalBesselJ l z = 0) :
    meridionalBoundaryJ l z =
      (z ^ 2 - l * (l - 1) * (l + 2)) * sphericalBesselJ (l + 1) z := by
  rw [meridionalBoundaryJ, h, mul_zero, zero_add]

/-- At `z² = γ²`, `meridionalBoundaryJ l z = -(l - 1)² (l + 1) z j_l(z)`. -/
theorem meridionalBoundaryJ_of_sq_eq {l : ℕ} {z : ℝ} (h : z ^ 2 = l * (l - 1) * (l + 2)) :
    meridionalBoundaryJ l z = -(((l : ℝ) - 1) ^ 2 * (l + 1)) * z * sphericalBesselJ l z := by
  rw [meridionalBoundaryJ, h]
  ring

/-- At a common zero `z ≠ 0` of `j_l` and `α² - γ²`, the derivative of `meridionalBoundaryJ l`
is `z (l³ - l² - l + 3) j_{l+1}(z)`. -/
theorem deriv_meridionalBoundaryJ_of_eq_zero_of_sq_eq {l : ℕ} {z : ℝ} (hz : z ≠ 0)
    (hj : sphericalBesselJ l z = 0) (h : z ^ 2 = l * (l - 1) * (l + 2)) :
    deriv (meridionalBoundaryJ l) z =
      z * ((l : ℝ) ^ 3 - l ^ 2 - l + 3) * sphericalBesselJ (l + 1) z := by
  rw [(hasDerivAt_meridionalBoundaryJ l z).deriv, deriv_sphericalBesselJ_of_eq_zero hz hj, hj, h]
  ring

/-- If `j_l` vanishes at `a ≠ 0` and `u j_l > 0` on `(a, b)`, then `u j_{l+1}(a) < 0`. -/
theorem mul_sphericalBesselJ_succ_neg_of_left {l : ℕ} {a b u : ℝ} (ha : a ≠ 0) (hab : a < b)
    (hj : sphericalBesselJ l a = 0) (hu : ∀ x ∈ Set.Ioo a b, 0 < u * sphericalBesselJ l x) :
    u * sphericalBesselJ (l + 1) a < 0 := by
  have hk := sphericalBesselJ_succ_ne_zero_of_eq_zero ha hj
  have hu0 : u ≠ 0 := left_ne_zero_of_mul (hu ((a + b) / 2) ⟨by linarith, by linarith⟩).ne'
  by_contra hle
  push Not at hle
  have hpos : 0 < u * sphericalBesselJ (l + 1) a :=
    lt_of_le_of_ne hle (mul_ne_zero hu0 hk).symm
  have hd : HasDerivAt (fun x ↦ -(u * sphericalBesselJ l x))
      (u * sphericalBesselJ (l + 1) a) a := by
    have h₁ := ((differentiable_sphericalBesselJ l a).hasDerivAt.const_mul u).fun_neg
    rw [deriv_sphericalBesselJ_of_eq_zero ha hj] at h₁
    refine h₁.congr_deriv ?_
    ring
  have hev := PDE.Analysis.eventually_pos_right_of_deriv_pos hd.differentiableAt
    (by simp only [hj, mul_zero, neg_zero]) (by rw [hd.deriv]; exact hpos)
  obtain ⟨x, hx, hxb, hax⟩ := (hev.and ((Filter.eventually_of_mem (Ioo_mem_nhdsGT hab)
    fun t ht ↦ ht.2).and self_mem_nhdsWithin)).exists
  have := hu x ⟨hax, hxb⟩
  linarith

/-- If `j_l` vanishes at `b ≠ 0` and `u j_l > 0` on `(a, b)`, then `u j_{l+1}(b) > 0`. -/
theorem mul_sphericalBesselJ_succ_pos_of_right {l : ℕ} {a b u : ℝ} (hb : b ≠ 0) (hab : a < b)
    (hj : sphericalBesselJ l b = 0) (hu : ∀ x ∈ Set.Ioo a b, 0 < u * sphericalBesselJ l x) :
    0 < u * sphericalBesselJ (l + 1) b := by
  have hk := sphericalBesselJ_succ_ne_zero_of_eq_zero hb hj
  have hu0 : u ≠ 0 := left_ne_zero_of_mul (hu ((a + b) / 2) ⟨by linarith, by linarith⟩).ne'
  by_contra hle
  push Not at hle
  have hneg : u * sphericalBesselJ (l + 1) b < 0 := lt_of_le_of_ne hle (mul_ne_zero hu0 hk)
  have hd : HasDerivAt (fun x ↦ u * sphericalBesselJ l x)
      (-(u * sphericalBesselJ (l + 1) b)) b := by
    have h₁ := (differentiable_sphericalBesselJ l b).hasDerivAt.const_mul u
    rw [deriv_sphericalBesselJ_of_eq_zero hb hj] at h₁
    refine h₁.congr_deriv ?_
    ring
  have hev := PDE.Analysis.eventually_neg_left_of_deriv_pos hd.differentiableAt
    (by simp only [hj, mul_zero]) (by rw [hd.deriv]; linarith)
  obtain ⟨x, hx, hax, hxb⟩ := (hev.and ((Filter.eventually_of_mem (Ioo_mem_nhdsLT hab)
    fun t ht ↦ ht.1).and self_mem_nhdsWithin)).exists
  have := hu x ⟨hax, hxb⟩
  linarith

/-- **Existence of the meridional root.** Let `0 ≤ a < b`, where `a` is `0`, a zero of `j_l` or
a point with `a² = γ²`, and `b` is a zero of `j_l` or a point with `b² = γ²`. If neither `j_l`
nor `α² - γ²` vanishes on `(a, b)`, the meridional boundary function of degree `l ≥ 1` has a
zero in `(a, b)`. -/
theorem exists_meridional_root_of_consecutive {l : ℕ} (hl : 1 ≤ l) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hA : a = 0 ∨ sphericalBesselJ l a = 0 ∨ a ^ 2 = l * (l - 1) * (l + 2))
    (hB : sphericalBesselJ l b = 0 ∨ b ^ 2 = l * (l - 1) * (l + 2))
    (hne : ∀ x ∈ Set.Ioo a b, sphericalBesselJ l x ≠ 0)
    (hγ : ∀ x ∈ Set.Ioo a b, x ^ 2 ≠ l * (l - 1) * (l + 2)) :
    ∃ α ∈ Set.Ioo a b, boundaryFunction .meridional l α = 0 := by
  have hfc : Continuous (meridionalBoundaryJ l) := (differentiable_meridionalBoundaryJ l).continuous
  have hBc : Continuous fun x : ℝ ↦ x ^ 2 - l * (l - 1) * (l + 2) := by fun_prop
  have hm₀ : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
  set m₀ := (a + b) / 2 with hm₀def
  set u := sphericalBesselJ l m₀ with hudef
  set v := m₀ ^ 2 - l * (l - 1) * (l + 2) with hvdef
  have hu : ∀ x ∈ Set.Ioo a b, 0 < u * sphericalBesselJ l x := fun x hx ↦
    PDE.Analysis.sign_eq_of_forall_ne_zero Set.ordConnected_Ioo
      (continuous_sphericalBesselJ l).continuousOn hne hm₀ hx
  have hB0 : ∀ x ∈ Set.Ioo a b, x ^ 2 - l * (l - 1) * (l + 2) ≠ 0 := fun x hx ↦
    sub_ne_zero.mpr (hγ x hx)
  have hv : ∀ x ∈ Set.Ioo a b, 0 < v * (x ^ 2 - l * (l - 1) * (l + 2)) := fun x hx ↦
    PDE.Analysis.sign_eq_of_forall_ne_zero Set.ordConnected_Ioo hBc.continuousOn hB0 hm₀ hx
  -- signs at the ends from continuity
  have hIco : ∀ g : ℝ → ℝ, Continuous g → (∀ x ∈ Set.Ioo a b, g x ≠ 0) → g a ≠ 0 →
      0 < g m₀ * g a := fun g hg h₁ h₂ ↦
    PDE.Analysis.sign_eq_of_forall_ne_zero Set.ordConnected_Ico hg.continuousOn
      (fun x hx ↦ hx.1.eq_or_lt.elim (fun h ↦ h ▸ h₂) fun h ↦ h₁ x ⟨h, hx.2⟩)
      ⟨hm₀.1.le, hm₀.2⟩ ⟨le_rfl, hab⟩
  have hIoc : ∀ g : ℝ → ℝ, Continuous g → (∀ x ∈ Set.Ioo a b, g x ≠ 0) → g b ≠ 0 →
      0 < g m₀ * g b := fun g hg h₁ h₂ ↦
    PDE.Analysis.sign_eq_of_forall_ne_zero Set.ordConnected_Ioc hg.continuousOn
      (fun x hx ↦ hx.2.eq_or_lt.elim (fun h ↦ h ▸ h₂) fun h ↦ h₁ x ⟨hx.1, h⟩)
      ⟨hm₀.1, hm₀.2.le⟩ ⟨hab, le_rfl⟩
  have hb0 : 0 < b := ha.trans_lt hab
  have huvc : Continuous fun x ↦ u * v * meridionalBoundaryJ l x := continuous_const.mul hfc
  have hm0 : 0 < m₀ := ha.trans_lt hm₀.1
  have hl2 : ∀ z : ℝ, z ≠ 0 → z ^ 2 = l * (l - 1) * (l + 2) → (2 : ℝ) ≤ l := by
    intro z hz h
    rcases hl.eq_or_lt with rfl | hl1
    · norm_num at h
      exact absurd h hz
    · exact_mod_cast hl1
  -- the sign just to the right of `a`
  have hleft : ∀ᶠ x in nhdsWithin a (Set.Ioi a), u * v * meridionalBoundaryJ l x < 0 := by
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · set x₁ := min (b / 2) 1 with hx₁def
      have hx₁0 : 0 < x₁ := lt_min (by linarith) one_pos
      have hx₁1 : x₁ ≤ 1 := min_le_right _ _
      have hx₁ : x₁ ∈ Set.Ioo a b :=
        ⟨ha0 ▸ hx₁0, (min_le_left _ _).trans_lt (by linarith)⟩
      have hL : (1 : ℝ) ≤ l := by exact_mod_cast hl
      have hj₁ : 0 < sphericalBesselJ l x₁ :=
        sphericalBesselJ_pos_of_sq_le hx₁0 (by nlinarith)
      have hupos : 0 < u := pos_of_mul_pos_left (hu x₁ hx₁) hj₁.le
      rw [← ha0]
      rcases hl.eq_or_lt with rfl | hl1
      · have hvpos : 0 < v := pos_of_mul_pos_left (hv x₁ hx₁) (by norm_num; positivity)
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 by norm_num)] with x hx
        exact mul_neg_of_pos_of_neg (mul_pos hupos hvpos) (meridionalBoundaryJ_one_neg hx.1 hx.2)
      · have hL2 : (2 : ℝ) ≤ l := by exact_mod_cast hl1
        have hvneg : v < 0 := by
          have : (8 : ℝ) ≤ l * (l - 1) * (l + 2) := by
            calc (8 : ℝ) = 2 * 1 * 4 := by norm_num
              _ ≤ l * (l - 1) * (l + 2) := by gcongr <;> linarith
          exact neg_of_mul_pos_left (hv x₁ hx₁) (by nlinarith)
        have hF := ((differentiable_boundaryFunction_meridional l).continuous.tendsto 0).eventually
          (lt_mem_nhds (boundaryFunction_meridional_zero_pos hl1))
        filter_upwards [hF.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hFx hx0
        rw [← pow_mul_boundaryFunction_meridional_eq]
        exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hupos hvneg)
          (mul_pos (pow_pos hx0 _) hFx)
    · by_cases hja : sphericalBesselJ l a = 0
      · have huk := mul_sphericalBesselJ_succ_neg_of_left ha0.ne' hab hja hu
        by_cases hγa : a ^ 2 = l * (l - 1) * (l + 2)
        · have hL2 := hl2 a ha0.ne' hγa
          have hvpos : 0 < v := by
            rw [hvdef, ← hγa]
            nlinarith [hm₀.1]
          have hfa : meridionalBoundaryJ l a = 0 := by
            rw [meridionalBoundaryJ_of_sphericalBesselJ_eq_zero hja, hγa, sub_self, zero_mul]
          have hK : (0 : ℝ) < (l : ℝ) ^ 3 - l ^ 2 - l + 3 := by nlinarith
          have hcd : u * v * deriv (meridionalBoundaryJ l) a < 0 := by
            rw [deriv_meridionalBoundaryJ_of_eq_zero_of_sq_eq ha0.ne' hja hγa]
            linarith [mul_neg_of_pos_of_neg
              (by positivity : 0 < v * a * ((l : ℝ) ^ 3 - l ^ 2 - l + 3)) huk]
          have hg : HasDerivAt (fun x ↦ -(u * v * meridionalBoundaryJ l x))
              (-(u * v * deriv (meridionalBoundaryJ l) a)) a :=
            ((differentiable_meridionalBoundaryJ l a).hasDerivAt.const_mul (u * v)).fun_neg
          have hev := PDE.Analysis.eventually_pos_right_of_deriv_pos hg.differentiableAt
            (by simp only [hfa, mul_zero, neg_zero]) (by rw [hg.deriv]; linarith)
          filter_upwards [hev] with x hx
          linarith
        · have hBa := hIco (fun x ↦ x ^ 2 - l * (l - 1) * (l + 2)) hBc hB0 (sub_ne_zero.mpr hγa)
          have h₁ : u * v * meridionalBoundaryJ l a < 0 := by
            rw [meridionalBoundaryJ_of_sphericalBesselJ_eq_zero hja]
            linarith [mul_neg_of_pos_of_neg hBa huk]
          exact ((huvc.tendsto a).eventually (gt_mem_nhds h₁)).filter_mono nhdsWithin_le_nhds
      · have hγa : a ^ 2 = l * (l - 1) * (l + 2) := (hA.resolve_left ha0.ne').resolve_left hja
        have hL2 := hl2 a ha0.ne' hγa
        have hja' := hIco (sphericalBesselJ l) (continuous_sphericalBesselJ l) hne hja
        have hvpos : 0 < v := by
          rw [hvdef, ← hγa]
          nlinarith [hm₀.1]
        have h₁ : u * v * meridionalBoundaryJ l a < 0 := by
          rw [meridionalBoundaryJ_of_sq_eq hγa]
          have : (0 : ℝ) < l - 1 := by linarith
          linarith [mul_pos (by positivity : 0 < v * (((l : ℝ) - 1) ^ 2 * (l + 1)) * a) hja']
        exact ((huvc.tendsto a).eventually (gt_mem_nhds h₁)).filter_mono nhdsWithin_le_nhds
  -- the sign just to the left of `b`
  have hright : ∀ᶠ x in nhdsWithin b (Set.Iio b), 0 < u * v * meridionalBoundaryJ l x := by
    have hvneg_of : b ^ 2 = l * (l - 1) * (l + 2) → v < 0 := fun hγb ↦ by
      rw [hvdef, ← hγb]
      nlinarith [hm₀.2]
    by_cases hjb : sphericalBesselJ l b = 0
    · have huk := mul_sphericalBesselJ_succ_pos_of_right hb0.ne' hab hjb hu
      by_cases hγb : b ^ 2 = l * (l - 1) * (l + 2)
      · have hL2 := hl2 b hb0.ne' hγb
        have hvneg := hvneg_of hγb
        have hfb : meridionalBoundaryJ l b = 0 := by
          rw [meridionalBoundaryJ_of_sphericalBesselJ_eq_zero hjb, hγb, sub_self, zero_mul]
        have hK : (0 : ℝ) < (l : ℝ) ^ 3 - l ^ 2 - l + 3 := by nlinarith
        have hcd : u * v * deriv (meridionalBoundaryJ l) b < 0 := by
          rw [deriv_meridionalBoundaryJ_of_eq_zero_of_sq_eq hb0.ne' hjb hγb]
          linarith [mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hvneg
            (by positivity : 0 < b * ((l : ℝ) ^ 3 - l ^ 2 - l + 3))) huk]
        have hg : HasDerivAt (fun x ↦ -(u * v * meridionalBoundaryJ l x))
            (-(u * v * deriv (meridionalBoundaryJ l) b)) b :=
          ((differentiable_meridionalBoundaryJ l b).hasDerivAt.const_mul (u * v)).fun_neg
        have hev := PDE.Analysis.eventually_neg_left_of_deriv_pos hg.differentiableAt
          (by simp only [hfb, mul_zero, neg_zero]) (by rw [hg.deriv]; linarith)
        filter_upwards [hev] with x hx
        linarith
      · have hBb := hIoc (fun x ↦ x ^ 2 - l * (l - 1) * (l + 2)) hBc hB0 (sub_ne_zero.mpr hγb)
        have h₁ : 0 < u * v * meridionalBoundaryJ l b := by
          rw [meridionalBoundaryJ_of_sphericalBesselJ_eq_zero hjb]
          linarith [mul_pos hBb huk]
        exact ((huvc.tendsto b).eventually (lt_mem_nhds h₁)).filter_mono nhdsWithin_le_nhds
    · have hγb : b ^ 2 = l * (l - 1) * (l + 2) := hB.resolve_left hjb
      have hL2 := hl2 b hb0.ne' hγb
      have hvneg := hvneg_of hγb
      have hjb' := hIoc (sphericalBesselJ l) (continuous_sphericalBesselJ l) hne hjb
      have h₁ : 0 < u * v * meridionalBoundaryJ l b := by
        rw [meridionalBoundaryJ_of_sq_eq hγb]
        have : (0 : ℝ) < l - 1 := by linarith
        have : 0 < -v := neg_pos.mpr hvneg
        linarith [mul_pos (by positivity : 0 < -v * (((l : ℝ) - 1) ^ 2 * (l + 1)) * b) hjb']
      exact ((huvc.tendsto b).eventually (lt_mem_nhds h₁)).filter_mono nhdsWithin_le_nhds
  -- the intermediate value theorem
  obtain ⟨p, hp, hpb, hpa⟩ := (hleft.and ((Filter.eventually_of_mem (Ioo_mem_nhdsGT hab)
    fun t ht ↦ ht.2).and self_mem_nhdsWithin)).exists
  obtain ⟨q, hq, hpq, hqb⟩ := (hright.and ((Filter.eventually_of_mem (Ioo_mem_nhdsLT hpb)
    fun t ht ↦ ht.1).and self_mem_nhdsWithin)).exists
  obtain ⟨α, hα, hfα⟩ := intermediate_value_Ioo hpq.le huvc.continuousOn ⟨hp, hq⟩
  have hf0 : meridionalBoundaryJ l α = 0 :=
    (mul_eq_zero.mp hfα).resolve_left (left_ne_zero_of_mul hp.ne)
  have hαab : α ∈ Set.Ioo a b := ⟨(Set.mem_Ioi.mp hpa).trans hα.1, hα.2.trans hqb⟩
  exact ⟨α, hαab, (boundaryFunction_meridional_eq_zero_iff (ha.trans_lt hαab.1)).mpr hf0⟩

/-- **The meridional root between consecutive breakpoints.** Let `0 ≤ a < b`, where `a` is `0`,
a zero of `j_l` or a point with `a² = γ²`, and `b` is a zero of `j_l` or a point with `b² = γ²`.
If neither `j_l` nor `α² - γ²` vanishes on `(a, b)`, the meridional boundary function of degree
`l ≥ 1` has exactly one zero in `(a, b)`. -/
theorem existsUnique_meridional_root_of_consecutive {l : ℕ} (hl : 1 ≤ l) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hA : a = 0 ∨ sphericalBesselJ l a = 0 ∨ a ^ 2 = l * (l - 1) * (l + 2))
    (hB : sphericalBesselJ l b = 0 ∨ b ^ 2 = l * (l - 1) * (l + 2))
    (hne : ∀ x ∈ Set.Ioo a b, sphericalBesselJ l x ≠ 0)
    (hγ : ∀ x ∈ Set.Ioo a b, x ^ 2 ≠ l * (l - 1) * (l + 2)) :
    ∃! α, α ∈ Set.Ioo a b ∧ boundaryFunction .meridional l α = 0 := by
  obtain ⟨α, hα, hfα⟩ := exists_meridional_root_of_consecutive hl ha hab hA hB hne hγ
  exact ⟨α, ⟨hα, hfα⟩, fun y hy ↦ meridional_root_unique hl ha hne hγ hy.1 hα hy.2 hfα⟩

end PDE.Fluid.Stokes.Ball
