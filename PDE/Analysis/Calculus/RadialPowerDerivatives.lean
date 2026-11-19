/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Polynomial.NestedCoefficientList
public import PDE.Symbolic.Calculus.ClassicalPDE
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Partial derivatives of power weights in the plane

A power term is `c |x| ^ b (x ^ 2 + y ^ 2) ^ s` with rational `c`, `b`, `s`; a power weight is a
finite sum of such terms. With `S = x ^ 2 + y ^ 2`,

`∂_x ^ i ∂_y ^ j (c x ^ b S ^ s) = N_{ij}(x, y) x ^ (b - i) S ^ (s - i - j)` on `x > 0`,

where `N_{ij}` is a polynomial in `x` and `y` computed by
`N_{i,j+1} = S ∂_y N_{ij} + 2 h y N_{ij}` and
`N_{i+1,j} = x S ∂_x N_{ij} + (b - i) S N_{ij} + 2 h x ^ 2 N_{ij}`, `h = s - i - j`. For terms
with `b = 0` the factor `x ^ (b - i)` is absorbed: `N_{i+1,j} = S ∂_x N_{ij} + 2 h x N_{ij}`, and
the formula holds wherever `S > 0`, including the axis `x = 0`. The derivatives are taken first
in `y` at fixed `x`, then in `x`.

The radial formulas of Chen and Hou for `i + j ≤ 4` are the cases `s = a / 2` of these
numerators. Every derivative is proved from the one-step rules, never taken from symbolic output.

## Main definitions

* `PowerTerm`: the term `c |x| ^ b (x ^ 2 + y ^ 2) ^ s`.
* `powerWeight`: a finite sum of power terms.
* `PowerTerm.numerator`: the numerators `N_{ij}` of a power term on `x > 0`.
* `powerWeightDeriv`: the closed form of `∂_x ^ i ∂_y ^ j` of a weight on `x > 0`.
* `radialWeightDeriv`: the closed form of `∂_x ^ i ∂_y ^ j` of a radial weight where `S > 0`.

## Main results

* `hasDerivAt_radial_y`: the `y`-derivative of `N S ^ h` is the `y`-step times `S ^ (h - 1)`.
* `hasDerivAt_axial_x`: the `x`-derivative of `N x ^ c S ^ h` on `x > 0` is the axial `x`-step
  times `x ^ (c - 1) S ^ (h - 1)`.
* `iteratedDeriv_powerWeight`: every mixed partial derivative `∂_x ^ i ∂_y ^ j` of a power weight
  on `x > 0` is its closed form.
* `iteratedDeriv_radialWeight`: every mixed partial derivative of a radial weight where `S > 0`,
  including the axis `x = 0`, is its closed form.
* `powerWeightDeriv_eq_closed`: the closed form of a power weight is the sum of its closed-form
  terms.
* `radialWeightDeriv_eq_closed`: the closed form of a radial weight is the sum of its closed-form
  terms.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Appendix A.2.1, the
  derivatives of `r ^ a` for `i + j ≤ 4`. <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open CAS.Polynomial
open CAS.ClassicalPDE (hasDerivAt_list_sum)
open scoped Topology

/-! ### Iterated derivatives from one-step rules -/

/-- If `G (k + 1)` is the derivative of `G k` on an open set where `f = G 0`, then
`iteratedDeriv k f = G k` there. -/
theorem iteratedDeriv_eqOn_of_hasDerivAt {f : ℝ → ℝ} {G : ℕ → ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (h0 : Set.EqOn f (G 0) U)
    (hG : ∀ k, ∀ y ∈ U, HasDerivAt (G k) (G (k + 1) y) y) (k : ℕ) :
    Set.EqOn (iteratedDeriv k f) (G k) U := by
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    intro y hy
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv k f =ᶠ[𝓝 y] G k := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact ih hz
    rw [heq.deriv_eq, (hG k y hy).deriv]

/-! ### Nested-list steps -/

/-- The product by `x ^ 2 + y ^ 2`. -/
def nestedMulRadius (N : List (List ℚ)) : List (List ℚ) :=
  nestedAdd (nestedShift (nestedShift N)) (nestedMulInner [0, 0, 1] N)

/-- `nestedMulRadius N` evaluates to `(x² + y²) N(x, y)`. -/
theorem nestedEval_nestedMulRadius (N : List (List ℚ)) (x y : ℝ) :
    nestedEval (nestedMulRadius N) x y = (x ^ 2 + y ^ 2) * nestedEval N x y := by
  simp only [nestedMulRadius, nestedEval_nestedAdd, nestedEval_nestedShift,
    nestedEval_nestedMulInner]
  simp; ring

/-- The `y`-step `S ∂_y N + 2 h y N`. -/
def radialStepY (h : ℚ) (N : List (List ℚ)) : List (List ℚ) :=
  nestedTrim (nestedAdd (nestedMulRadius (nestedDerivInner N))
    (nestedScale (2 * h) (nestedMulInner [0, 1] N)))

/-- The radial `x`-step `S ∂_x N + 2 h x N`. -/
def radialStepX (h : ℚ) (N : List (List ℚ)) : List (List ℚ) :=
  nestedTrim (nestedAdd (nestedMulRadius (nestedDerivOuter N))
    (nestedScale (2 * h) (nestedShift N)))

/-- The axial `x`-step `x S ∂_x N + c S N + 2 h x ^ 2 N`. -/
def axialStepX (c h : ℚ) (N : List (List ℚ)) : List (List ℚ) :=
  nestedTrim (nestedAdd (nestedShift (nestedMulRadius (nestedDerivOuter N)))
    (nestedAdd (nestedScale c (nestedMulRadius N))
      (nestedScale (2 * h) (nestedShift (nestedShift N)))))

/-- The `y`-step evaluates to `(x² + y²) ∂_y N + 2 h y N`. -/
theorem nestedEval_radialStepY (h : ℚ) (N : List (List ℚ)) (x y : ℝ) :
    nestedEval (radialStepY h N) x y = (x ^ 2 + y ^ 2) * nestedEval (nestedDerivInner N) x y +
      2 * h * y * nestedEval N x y := by
  simp only [radialStepY, nestedEval_nestedTrim, nestedEval_nestedAdd, nestedEval_nestedMulRadius,
    nestedEval_nestedScale, nestedEval_nestedMulInner]
  simp; ring

/-- The radial `x`-step evaluates to `(x² + y²) ∂_x N + 2 h x N`. -/
theorem nestedEval_radialStepX (h : ℚ) (N : List (List ℚ)) (x y : ℝ) :
    nestedEval (radialStepX h N) x y = (x ^ 2 + y ^ 2) * nestedEval (nestedDerivOuter N) x y +
      2 * h * x * nestedEval N x y := by
  simp only [radialStepX, nestedEval_nestedTrim, nestedEval_nestedAdd, nestedEval_nestedMulRadius,
    nestedEval_nestedScale, nestedEval_nestedShift]
  push_cast; ring

/-- The axial `x`-step evaluates to `x (x² + y²) ∂_x N + c (x² + y²) N + 2 h x² N`. -/
theorem nestedEval_axialStepX (c h : ℚ) (N : List (List ℚ)) (x y : ℝ) :
    nestedEval (axialStepX c h N) x y =
      x * (x ^ 2 + y ^ 2) * nestedEval (nestedDerivOuter N) x y +
        c * (x ^ 2 + y ^ 2) * nestedEval N x y + 2 * h * x ^ 2 * nestedEval N x y := by
  simp only [axialStepX, nestedEval_nestedTrim, nestedEval_nestedAdd, nestedEval_nestedMulRadius,
    nestedEval_nestedScale, nestedEval_nestedShift]
  push_cast; ring

/-! ### One step of the derivative -/

/-- Where `x² + y² > 0`, the `y`-derivative of `N(x, y) (x² + y²) ^ h` is
`radialStepY h N (x, y) (x² + y²) ^ (h - 1)`. -/
theorem hasDerivAt_radial_y (N : List (List ℚ)) (h : ℚ) {x y : ℝ} (hS : 0 < x ^ 2 + y ^ 2) :
    HasDerivAt (fun v ↦ nestedEval N x v * (x ^ 2 + v ^ 2) ^ (h : ℝ))
      (nestedEval (radialStepY h N) x y * (x ^ 2 + y ^ 2) ^ ((h : ℝ) - 1)) y := by
  have hN := hasDerivAt_nestedEval_inner N x y
  have hR := ((hasDerivAt_pow 2 y).const_add (x ^ 2)).rpow_const (p := (h : ℝ)) (Or.inl hS.ne')
  refine (hN.mul hR).congr_deriv ?_
  rw [nestedEval_radialStepY, Real.rpow_sub_one hS.ne']
  field_simp
  ring

/-- Where `x² + y² > 0`, the `x`-derivative of `N(x, y) (x² + y²) ^ h` is
`radialStepX h N (x, y) (x² + y²) ^ (h - 1)`. -/
theorem hasDerivAt_radial_x (N : List (List ℚ)) (h : ℚ) {x y : ℝ} (hS : 0 < x ^ 2 + y ^ 2) :
    HasDerivAt (fun u ↦ nestedEval N u y * (u ^ 2 + y ^ 2) ^ (h : ℝ))
      (nestedEval (radialStepX h N) x y * (x ^ 2 + y ^ 2) ^ ((h : ℝ) - 1)) x := by
  have hN := hasDerivAt_nestedEval_outer N x y
  have hR := ((hasDerivAt_pow 2 x).add_const (y ^ 2)).rpow_const (p := (h : ℝ)) (Or.inl hS.ne')
  refine (hN.mul hR).congr_deriv ?_
  rw [nestedEval_radialStepX, Real.rpow_sub_one hS.ne']
  field_simp
  ring

/-- On `x > 0`, the `x`-derivative of `N(x, y) x ^ c (x² + y²) ^ h` is
`axialStepX c h N (x, y) x ^ (c - 1) (x² + y²) ^ (h - 1)`. -/
theorem hasDerivAt_axial_x (N : List (List ℚ)) (c h : ℚ) {x y : ℝ} (hx : 0 < x) :
    HasDerivAt (fun u ↦ nestedEval N u y * u ^ (c : ℝ) * (u ^ 2 + y ^ 2) ^ (h : ℝ))
      (nestedEval (axialStepX c h N) x y * x ^ ((c : ℝ) - 1) *
        (x ^ 2 + y ^ 2) ^ ((h : ℝ) - 1)) x := by
  have hS : 0 < x ^ 2 + y ^ 2 := by positivity
  have hN := hasDerivAt_nestedEval_outer N x y
  have hX := Real.hasDerivAt_rpow_const (x := x) (p := (c : ℝ)) (Or.inl hx.ne')
  have hR := ((hasDerivAt_pow 2 x).add_const (y ^ 2)).rpow_const (p := (h : ℝ)) (Or.inl hS.ne')
  refine ((hN.mul hX).mul hR).congr_deriv ?_
  rw [nestedEval_axialStepX, Real.rpow_sub_one hS.ne', Real.rpow_sub_one hx.ne']
  simp only [Pi.mul_apply]
  field_simp
  ring

/-! ### Power weights -/

/-- The term `coeff |x| ^ axial (x ^ 2 + y ^ 2) ^ radial`. -/
structure PowerTerm where
  /-- The coefficient. -/
  coeff : ℚ
  /-- The exponent of `x`. -/
  axial : ℚ
  /-- The exponent of `x ^ 2 + y ^ 2`, half the exponent of `|(x, y)|`. -/
  radial : ℚ

/-- The value of a power term. -/
def PowerTerm.eval (t : PowerTerm) (x y : ℝ) : ℝ :=
  t.coeff * |x| ^ (t.axial : ℝ) * (x ^ 2 + y ^ 2) ^ (t.radial : ℝ)

/-- The finite sum of power terms. -/
def powerWeight (ts : List PowerTerm) (x y : ℝ) : ℝ := (ts.map fun t ↦ t.eval x y).sum

/-- The numerators of `∂_y ^ j (coeff S ^ radial) = N S ^ (radial - j)`. -/
def PowerTerm.numeratorY (t : PowerTerm) : ℕ → List (List ℚ)
  | 0 => [[t.coeff]]
  | j + 1 => radialStepY (t.radial - j) (t.numeratorY j)

/-- The numerators of `∂_x ^ i ∂_y ^ j (coeff x ^ axial S ^ radial)` on `x > 0`. -/
def PowerTerm.numerator (t : PowerTerm) (j : ℕ) : ℕ → List (List ℚ)
  | 0 => t.numeratorY j
  | i + 1 => axialStepX (t.axial - i) (t.radial - j - i) (t.numerator j i)

/-- The numerators of `∂_x ^ i ∂_y ^ j (coeff S ^ radial)`, ignoring `axial`. -/
def PowerTerm.radialNumerator (t : PowerTerm) (j : ℕ) : ℕ → List (List ℚ)
  | 0 => t.numeratorY j
  | i + 1 => radialStepX (t.radial - j - i) (t.radialNumerator j i)

/-- The closed form of `∂_y ^ j` of a weight at fixed `x`. -/
def powerWeightDerivY (ts : List PowerTerm) (j : ℕ) (x y : ℝ) : ℝ :=
  (ts.map fun t ↦ nestedEval (t.numeratorY j) x y * x ^ (t.axial : ℝ) *
    (x ^ 2 + y ^ 2) ^ ((t.radial : ℝ) - j)).sum

/-- The closed form of `∂_x ^ i ∂_y ^ j` of a weight on `x > 0`. -/
def powerWeightDeriv (ts : List PowerTerm) (i j : ℕ) (x y : ℝ) : ℝ :=
  (ts.map fun t ↦ nestedEval (t.numerator j i) x y * x ^ ((t.axial : ℝ) - i) *
    (x ^ 2 + y ^ 2) ^ ((t.radial : ℝ) - j - i)).sum

/-- The closed form of `∂_x ^ i ∂_y ^ j` of a radial weight where `x ^ 2 + y ^ 2 > 0`. -/
def radialWeightDeriv (ts : List PowerTerm) (i j : ℕ) (x y : ℝ) : ℝ :=
  (ts.map fun t ↦ nestedEval (t.radialNumerator j i) x y *
    (x ^ 2 + y ^ 2) ^ ((t.radial : ℝ) - j - i)).sum

/-- On `x > 0` a power weight equals its closed form of order zero, `powerWeightDerivY ts 0`. -/
theorem powerWeight_eq_derivY_zero (ts : List PowerTerm) {x : ℝ} (hx : 0 < x) (y : ℝ) :
    powerWeight ts x y = powerWeightDerivY ts 0 x y := by
  unfold powerWeight powerWeightDerivY
  congr 1
  refine List.map_congr_left fun t _ ↦ ?_
  simp [PowerTerm.numeratorY, PowerTerm.eval, abs_of_pos hx]

/-- The `y`-derivatives of a weight at fixed `x > 0`. -/
theorem iteratedDeriv_powerWeight_y (ts : List PowerTerm) (j : ℕ) {x y : ℝ} (hx : 0 < x) :
    iteratedDeriv j (fun v ↦ powerWeight ts x v) y = powerWeightDerivY ts j x y := by
  refine iteratedDeriv_eqOn_of_hasDerivAt (G := fun k v ↦ powerWeightDerivY ts k x v)
    (U := Set.univ) isOpen_univ (fun v _ ↦ powerWeight_eq_derivY_zero ts hx v) ?_ j
    (Set.mem_univ y)
  intro k v _
  have hS : 0 < x ^ 2 + v ^ 2 := by positivity
  unfold powerWeightDerivY
  refine hasDerivAt_list_sum ts (f := fun t v ↦ nestedEval (t.numeratorY k) x v *
    x ^ (t.axial : ℝ) * (x ^ 2 + v ^ 2) ^ ((t.radial : ℝ) - k))
    (f' := fun t ↦ nestedEval (t.numeratorY (k + 1)) x v *
    x ^ (t.axial : ℝ) * (x ^ 2 + v ^ 2) ^ ((t.radial : ℝ) - (k + 1 : ℕ))) _ fun t _ ↦ ?_
  have h := hasDerivAt_radial_y (t.numeratorY k) (t.radial - k) hS
  have h2 := h.mul_const (x ^ (t.axial : ℝ))
  refine (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w ↦ ?_)).congr_deriv ?_
  · simp only; push_cast; ring_nf
  · simp only [PowerTerm.numeratorY]; push_cast; ring_nf

/-- Every mixed partial derivative `∂_x ^ i ∂_y ^ j` of a power weight on `x > 0`. -/
theorem iteratedDeriv_powerWeight (ts : List PowerTerm) (i j : ℕ) {x y : ℝ} (hx : 0 < x) :
    iteratedDeriv i (fun u ↦ iteratedDeriv j (fun v ↦ powerWeight ts u v) y) x =
      powerWeightDeriv ts i j x y := by
  refine iteratedDeriv_eqOn_of_hasDerivAt (G := fun k u ↦ powerWeightDeriv ts k j u y)
    (U := Set.Ioi 0) isOpen_Ioi (fun u hu ↦ ?_) ?_ i hx
  · rw [iteratedDeriv_powerWeight_y ts j hu]
    unfold powerWeightDerivY powerWeightDeriv
    congr 1
    refine List.map_congr_left fun t _ ↦ ?_
    simp [PowerTerm.numerator]
  · intro k u hu
    unfold powerWeightDeriv
    refine hasDerivAt_list_sum ts (f := fun t u ↦ nestedEval (t.numerator j k) u y *
      u ^ ((t.axial : ℝ) - k) * (u ^ 2 + y ^ 2) ^ ((t.radial : ℝ) - j - k))
      (f' := fun t ↦ nestedEval (t.numerator j (k + 1)) u y *
      u ^ ((t.axial : ℝ) - (k + 1 : ℕ)) * (u ^ 2 + y ^ 2) ^ ((t.radial : ℝ) - j - (k + 1 : ℕ)))
      _ fun t _ ↦ ?_
    have h := hasDerivAt_axial_x (t.numerator j k) (t.axial - k) (t.radial - j - k)
      (y := y) hu
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w ↦ ?_)).congr_deriv ?_
    · simp only; push_cast; ring_nf
    · simp only [PowerTerm.numerator]; push_cast; ring_nf

/-- Every mixed partial derivative of a radial weight (all `axial` exponents zero) where
`x ^ 2 + y ^ 2 > 0`, including the axis `x = 0`. -/
theorem iteratedDeriv_radialWeight (ts : List PowerTerm) (hts : ∀ t ∈ ts, t.axial = 0)
    (i j : ℕ) {x y : ℝ} (hS : 0 < x ^ 2 + y ^ 2) :
    iteratedDeriv i (fun u ↦ iteratedDeriv j (fun v ↦ powerWeight ts u v) y) x =
      radialWeightDeriv ts i j x y := by
  have hrad : ∀ u v, powerWeight ts u v = (ts.map fun t ↦ nestedEval (t.numeratorY 0) u v *
      (u ^ 2 + v ^ 2) ^ ((t.radial : ℝ) - (0 : ℕ))).sum := by
    intro u v
    unfold powerWeight
    congr 1
    refine List.map_congr_left fun t ht ↦ ?_
    simp [PowerTerm.numeratorY, PowerTerm.eval, hts t ht]
  have hy : ∀ u, 0 < u ^ 2 + y ^ 2 → iteratedDeriv j (fun v ↦ powerWeight ts u v) y =
      (ts.map fun t ↦ nestedEval (t.numeratorY j) u y *
        (u ^ 2 + y ^ 2) ^ ((t.radial : ℝ) - j)).sum := by
    intro u hu
    have hU : IsOpen {v : ℝ | 0 < u ^ 2 + v ^ 2} :=
      isOpen_lt continuous_const (continuous_const.add (continuous_id.pow 2))
    refine iteratedDeriv_eqOn_of_hasDerivAt (G := fun k v ↦ (ts.map fun t ↦
      nestedEval (t.numeratorY k) u v * (u ^ 2 + v ^ 2) ^ ((t.radial : ℝ) - k)).sum) hU
      (fun v _ ↦ hrad u v) ?_ j hu
    intro k v hv
    refine hasDerivAt_list_sum ts (f := fun t v ↦ nestedEval (t.numeratorY k) u v *
      (u ^ 2 + v ^ 2) ^ ((t.radial : ℝ) - k))
      (f' := fun t ↦ nestedEval (t.numeratorY (k + 1)) u v *
      (u ^ 2 + v ^ 2) ^ ((t.radial : ℝ) - (k + 1 : ℕ))) _ fun t _ ↦ ?_
    have h := hasDerivAt_radial_y (t.numeratorY k) (t.radial - k) hv
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w ↦ ?_)).congr_deriv ?_
    · simp only; push_cast; ring_nf
    · simp only [PowerTerm.numeratorY]; push_cast; ring_nf
  have hU : IsOpen {u : ℝ | 0 < u ^ 2 + y ^ 2} :=
    isOpen_lt continuous_const ((continuous_id.pow 2).add continuous_const)
  refine iteratedDeriv_eqOn_of_hasDerivAt (G := fun k u ↦ radialWeightDeriv ts k j u y) hU
    (fun u hu ↦ ?_) ?_ i hS
  · rw [hy u hu]
    unfold radialWeightDeriv
    congr 1
    refine List.map_congr_left fun t _ ↦ ?_
    simp [PowerTerm.radialNumerator]
  · intro k u hu
    unfold radialWeightDeriv
    refine hasDerivAt_list_sum ts (f := fun t u ↦ nestedEval (t.radialNumerator j k) u y *
      (u ^ 2 + y ^ 2) ^ ((t.radial : ℝ) - j - k))
      (f' := fun t ↦ nestedEval (t.radialNumerator j (k + 1)) u y *
      (u ^ 2 + y ^ 2) ^ ((t.radial : ℝ) - j - (k + 1 : ℕ))) _ fun t _ ↦ ?_
    have h := hasDerivAt_radial_x (t.radialNumerator j k) (t.radial - j - k) hu
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w ↦ ?_)).congr_deriv ?_
    · simp only; push_cast; ring_nf
    · simp only [PowerTerm.radialNumerator]; push_cast; ring_nf

/-! ### Closed-form terms -/

/-- A closed-form term `N(x, y) x ^ axial (x ^ 2 + y ^ 2) ^ radial`. -/
structure ClosedTerm where
  /-- The polynomial numerator, outer variable `x`, inner variable `y`. -/
  numerator : List (List ℚ)
  /-- The exponent of `x`. -/
  axial : ℚ
  /-- The exponent of `x ^ 2 + y ^ 2`. -/
  radial : ℚ

/-- The value of a closed-form term. -/
def ClosedTerm.eval (c : ClosedTerm) (x y : ℝ) : ℝ :=
  nestedEval c.numerator x y * x ^ (c.axial : ℝ) * (x ^ 2 + y ^ 2) ^ (c.radial : ℝ)

/-- The closed-form terms of `∂_x ^ i ∂_y ^ j` of a power weight on `x > 0`. -/
def powerWeightClosed (ts : List PowerTerm) (i j : ℕ) : List ClosedTerm :=
  ts.map fun t ↦ ⟨t.numerator j i, t.axial - i, t.radial - j - i⟩

/-- The closed-form terms of `∂_x ^ i ∂_y ^ j` of a radial weight, with `axial = 0`. -/
def radialWeightClosed (ts : List PowerTerm) (i j : ℕ) : List ClosedTerm :=
  ts.map fun t ↦ ⟨t.radialNumerator j i, 0, t.radial - j - i⟩

/-- The closed form of `∂_x ^ i ∂_y ^ j` of a power weight is the sum of the values of the terms
`powerWeightClosed ts i j`. -/
theorem powerWeightDeriv_eq_closed (ts : List PowerTerm) (i j : ℕ) (x y : ℝ) :
    powerWeightDeriv ts i j x y = ((powerWeightClosed ts i j).map fun c ↦ c.eval x y).sum := by
  unfold powerWeightDeriv powerWeightClosed
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun t _ ↦ ?_
  simp only [Function.comp, ClosedTerm.eval]
  push_cast; ring_nf

/-- The closed form of `∂_x ^ i ∂_y ^ j` of a radial weight is the sum of the values of the terms
`radialWeightClosed ts i j`. -/
theorem radialWeightDeriv_eq_closed (ts : List PowerTerm) (i j : ℕ) (x y : ℝ) :
    radialWeightDeriv ts i j x y = ((radialWeightClosed ts i j).map fun c ↦ c.eval x y).sum := by
  unfold radialWeightDeriv radialWeightClosed
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun t _ ↦ ?_
  simp only [Function.comp, ClosedTerm.eval, Rat.cast_zero, Real.rpow_zero, mul_one]
  push_cast; ring_nf

end PDE.Analysis
