/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Euclidean PDE calculus

Calculus rules for the coordinate operators this library uses on functions of `ℝ^n`: the
coordinate derivative `partialDeriv i`, Mathlib's `gradient`, the advective derivative, and the
iterated-coordinate `laplacian f x = ∑ᵢ ∂ᵢ∂ᵢ f x`. All of them are built from Mathlib's total
`fderiv`, so regularity appears as explicit hypotheses.
`laplacian_const_smul`, `laplacian_neg`, and `advectiveDerivative_smul_advecting` hold for every
`f`, because `fderiv` commutes with scalars even where it is zero by convention. `laplacian_add`
needs `ContDiffAt ℝ 2` at the point, and `partialDeriv_partialDeriv_comp_at` needs a `C²` germ
of both `u` and the chart `Φ`. Mathlib has `fderiv_comp` but no coordinate form of the
second-order chain rule. That rule, with its Hessian and chart-curvature terms written out,
transforms an operator in nondivergence form under a change of coordinates, such as the one
that flattens the boundary in Evans, §6.3.2, proof of Theorem 4, step 6. Evans transforms the
divergence form there ((63)-(64)), for which the first-order rule suffices.

## Main results

* `norm_fderiv_sq_eq_sum_partialDeriv_sq`: `‖Df(x)‖² = ∑ᵢ (∂ᵢ f(x))²` for a scalar `f`
  differentiable at `x`.
* `partialDeriv_comp_real`, `partialDeriv_inv`, `partialDeriv_div`,
  `ContinuousLinearMap.partialDeriv_comp`: the scalar chain rule, the reciprocal and quotient
  rules, and commutation with continuous linear maps.
* `advectiveDerivative_eq_sum_mul_partialDeriv`, `partialDeriv_advectiveDerivative`,
  `secondPartialDeriv_advectiveDerivative`: coordinate formulas and product rules for the
  advective derivative `(b · ∇) f`.
* `partialDeriv_comp`, `partialDeriv_partialDeriv_comp_at`: first- and second-order chain rules
  for a scalar function pulled back by a Euclidean map. The second-order rule transforms
  nondivergence-form operators under a change of coordinates.
* `partialDeriv_congr_nhds`, `partialDeriv_eq_on_closure_of_eqOn_open`,
  `contDiffAt_partialDeriv`: germ dependence and regularity of coordinate derivatives.
* `laplacian_add`, `laplacian_sub`, `laplacian_const_smul`, `laplacian_neg`,
  `laplacian_comp_add_left`: linearity and translation invariance of the Laplacian.
* `laplacian_coordinate_mul`: `Δ(xₖ f) = xₖ Δf + 2 ∂ₖ f`.
* `laplacian_coordinate_sq_sub`: `Δ((xₖ - c)²) = 2`, the strictly subharmonic perturbation
  used in the weak maximum principle.

## Implementation notes

Only rules without regularity hypotheses are `@[simp]`: derivatives of constants and coordinate
functions, negation, and constant multiples (`partialDeriv_const`, `partialDeriv_coord`,
`partialDeriv_neg`, `partialDeriv_const_smul`, `laplacian_const`). Product, chain, and
commutation rules need regularity, and expanding every operator by default would enlarge most
expressions, so proofs pass the rules they need to `simp` or `grind` explicitly.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, proof of Theorem 4,
  steps 6-8, (57)-(64), pp. 337-338.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

variable {n m : ℕ}

open PDE
open scoped Gradient InnerProductSpace RealInnerProductSpace

namespace PDE

/-- The Euclidean Laplacian of a constant function is zero. -/
@[simp]
theorem laplacian_const (c : ℝ) (x : ℝ^n) :
    laplacian (n := n) (fun _ : ℝ^n ↦ c) x = 0 := by
  have hf : ContDiffAt ℝ 2 (fun _ : ℝ^n ↦ c) x := contDiffAt_const
  rw [hf.coordinate_laplacian_eq_laplacian]
  exact congrFun (InnerProductSpace.laplacian_const (E := ℝ^n) (c := c)) x

/-- The squared norm of the Fréchet derivative of a scalar function is the sum of the squared
coordinate partial derivatives (the Euclidean gradient norm). -/
theorem norm_fderiv_sq_eq_sum_partialDeriv_sq
    {f : ℝ^n → ℝ} {x : ℝ^n}
    (hf : DifferentiableAt ℝ f x) :
    ‖fderiv ℝ f x‖ ^ 2 = ∑ i : Fin n, (∂[i] f) x ^ 2 := by
  have hnorm :
      ‖∇ f x‖ = ‖fderiv ℝ f x‖ := by
    rw [hf.hasGradientAt.hasFDerivAt.fderiv]
    exact ((InnerProductSpace.toDual ℝ (ℝ^n)).norm_map (∇ f x)).symm
  rw [← hnorm, EuclideanSpace.real_norm_sq_eq]
  simp

/-- Coordinate formula for scalar advection.

This identity is algebraic in the Fréchet derivative, so it needs no
differentiability hypothesis. -/
theorem advectiveDerivative_eq_sum_mul_partialDeriv
    (u : ℝ^n → ℝ^n) (f : ℝ^n → ℝ) (x : ℝ^n) :
    advectiveDerivative u f x =
      ∑ i : Fin n, u x i * (∂[i] f) x := by
  calc
    advectiveDerivative u f x =
        ∑ i : Fin n, (∂[i] f) x * u x i := by
      exact fderiv_apply_eq_sum_partialDeriv_mul f x (u x)
    _ = ∑ i : Fin n, u x i * (∂[i] f) x := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _

/-- Coordinate partial derivatives depend only on the germ of the function at the point. -/
theorem partialDeriv_congr_nhds (i : Fin n)
    {f g : ℝ^n → ℝ} {x : ℝ^n}
    (h : f =ᶠ[nhds x] g) :
    (∂[i] f) x =
      (∂[i] g) x := by
  exact partialDeriv_eq_of_fderiv_eq (h.fderiv_eq (𝕜 := ℝ)) i

/-- Taking one Euclidean coordinate derivative lowers finite local regularity by one order. -/
theorem contDiffAt_partialDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^n → E} {x : ℝ^n}
    (m : ℕ) (hf : ContDiffAt ℝ (m + 1) f x) (i : Fin n) :
    ContDiffAt ℝ m (fun y ↦ (∂[i] f) y) x :=
  hf.partialDeriv i le_rfl

/-- Coordinate product rule for one derivative of scalar advection. -/
theorem partialDeriv_advectiveDerivative
    (i : Fin n) (u : ℝ^n → ℝ^n) (f : ℝ^n → ℝ) (x : ℝ^n)
    (hu : ContDiffAt ℝ 1 u x) (hf : ContDiffAt ℝ 2 f x) :
    (∂[i] (fun y ↦ advectiveDerivative u f y)) x =
      ∑ j : Fin n,
        ((∂[i] (fun y ↦ u y j)) x * (∂[j] f) x +
          u x j * (∂[i] (fun y ↦ (∂[j] f) y)) x) := by
  have huComponent (j : Fin n) : ContDiffAt ℝ 1 (fun y ↦ u y j) x :=
    by
      simpa [Function.comp_def] using
        (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) j).contDiff.contDiffAt.comp x hu
  have hfPartial (j : Fin n) :
      ContDiffAt ℝ 1 (fun y ↦ (∂[j] f) y) x :=
    contDiffAt_partialDeriv 1 hf j
  have hadvection :
      (fun y ↦ advectiveDerivative u f y) =
        fun y ↦ ∑ j : Fin n, u y j * (∂[j] f) y := by
    funext y
    exact advectiveDerivative_eq_sum_mul_partialDeriv u f y
  rw [hadvection]
  have hsum :
      (∂[i] (fun y ↦ ∑ j : Fin n, u y j * (∂[j] f) y)) x =
        ∑ j : Fin n,
          (∂[i] (fun y ↦ u y j * (∂[j] f) y)) x := by
    unfold partialDeriv
    rw [fderiv_fun_sum]
    · simp
    · intro j _hj
      exact ((huComponent j).mul (hfPartial j)).differentiableAt (by norm_num)
  rw [hsum]
  apply Finset.sum_congr rfl
  intro j _hj
  exact partialDeriv_mul
    ((huComponent j).differentiableAt (by norm_num))
    ((hfPartial j).differentiableAt (by norm_num))

/-- Coordinate product rule for two derivatives of scalar advection. -/
theorem secondPartialDeriv_advectiveDerivative
    (i k : Fin n) (u : ℝ^n → ℝ^n) (f : ℝ^n → ℝ) (x : ℝ^n)
    (hu : ContDiffAt ℝ 2 u x) (hf : ContDiffAt ℝ 3 f x) :
    (∂[i] (fun y ↦ (∂[k] (fun z ↦ advectiveDerivative u f z)) y)) x =
      ∑ j : Fin n,
        ((∂[i] (fun y ↦ (∂[k] (fun z ↦ u z j)) y)) x *
            (∂[j] f) x +
          (∂[k] (fun y ↦ u y j)) x *
            (∂[i] (fun y ↦ (∂[j] f) y)) x +
          ((∂[i] (fun y ↦ u y j)) x *
              (∂[k] (fun y ↦ (∂[j] f) y)) x +
            u x j *
              (∂[i] (fun y ↦ (∂[k] (fun z ↦ (∂[j] f) z)) y)) x)) := by
  have huComponent (j : Fin n) : ContDiffAt ℝ 2 (fun y ↦ u y j) x :=
    by
      simpa [Function.comp_def] using
        (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) j).contDiff.contDiffAt.comp x hu
  have huPartial (j : Fin n) :
      ContDiffAt ℝ 1 (fun y ↦ (∂[k] (fun z ↦ u z j)) y) x :=
    contDiffAt_partialDeriv 1 (huComponent j) k
  have hfPartialTwo (j : Fin n) :
      ContDiffAt ℝ 2 (fun y ↦ (∂[j] f) y) x :=
    contDiffAt_partialDeriv 2 hf j
  have hfPartialOne (j : Fin n) :
      ContDiffAt ℝ 1 (fun y ↦ (∂[j] f) y) x :=
    (hfPartialTwo j).of_le (by norm_num)
  have hfPartialPartial (j : Fin n) :
      ContDiffAt ℝ 1
        (fun y ↦ (∂[k] (fun z ↦ (∂[j] f) z)) y) x :=
    contDiffAt_partialDeriv 1 (hfPartialTwo j) k
  have hfirst :
      (fun y ↦ (∂[k] (fun z ↦ advectiveDerivative u f z)) y) =ᶠ[nhds x]
        fun y ↦ ∑ j : Fin n,
          ((∂[k] (fun z ↦ u z j)) y * (∂[j] f) y +
            u y j *
              (∂[k] (fun z ↦ (∂[j] f) z)) y) := by
    filter_upwards [hu.eventually (by norm_num), hf.eventually (by norm_num)] with y huy hfy
    exact partialDeriv_advectiveDerivative k u f y
      (huy.of_le (by norm_num)) (hfy.of_le (by norm_num))
  rw [partialDeriv_congr_nhds i hfirst]
  have hsum :
      (∂[i] (fun y ↦ ∑ j : Fin n,
            ((∂[k] (fun z ↦ u z j)) y * (∂[j] f) y +
              u y j *
                (∂[k] (fun z ↦ (∂[j] f) z)) y))) x =
        ∑ j : Fin n,
          (∂[i] (fun y ↦
              (∂[k] (fun z ↦ u z j)) y * (∂[j] f) y +
                u y j *
                  (∂[k] (fun z ↦ (∂[j] f) z)) y)) x := by
    unfold partialDeriv
    rw [fderiv_fun_sum]
    · simp
    · intro j _hj
      exact (((huPartial j).mul (hfPartialOne j)).add
        ((huComponent j).of_le (by norm_num) |>.mul
          (hfPartialPartial j))).differentiableAt (by norm_num)
  rw [hsum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [partialDeriv_add
    (((huPartial j).mul (hfPartialOne j)).differentiableAt (by norm_num))
    (((huComponent j).of_le (by norm_num) |>.mul
      (hfPartialPartial j)).differentiableAt (by norm_num))]
  rw [partialDeriv_mul
    ((huPartial j).differentiableAt (by norm_num))
    ((hfPartialOne j).differentiableAt (by norm_num))]
  rw [partialDeriv_mul
    ((huComponent j).differentiableAt (by norm_num))
    ((hfPartialPartial j).differentiableAt (by norm_num))]

/-- The advective derivative is additive in the advecting velocity field. -/
theorem advectiveDerivative_add_advecting
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v : ℝ^n → ℝ^n) (f : ℝ^n → E) (x : ℝ^n) :
    advectiveDerivative (fun y ↦ u y + v y) f x =
      advectiveDerivative u f x + advectiveDerivative v f x := by
  unfold advectiveDerivative
  rw [map_add]

/-- Scaling the advecting velocity scales the advective derivative. -/
theorem advectiveDerivative_smul_advecting
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (u : ℝ^n → ℝ^n) (f : ℝ^n → E) (x : ℝ^n) :
    advectiveDerivative (fun y ↦ a • u y) f x =
      a • advectiveDerivative u f x := by
  unfold advectiveDerivative
  rw [map_smul]

/-- Coordinate chain rule for a real-valued function composed with a scalar Euclidean map. -/
theorem partialDeriv_comp_real
    (i : Fin n) {g : ℝ → ℝ} {u : ℝ^n → ℝ} {x : ℝ^n}
    (hg : DifferentiableAt ℝ g (u x)) (hu : DifferentiableAt ℝ u x) :
    (∂[i] (fun y ↦ g (u y))) x =
      (∂[i] u) x * deriv g (u x) := by
  change (∂[i] (g ∘ u)) x = _
  unfold partialDeriv
  rw [fderiv_comp x hg hu, ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv]
  simp [smul_eq_mul, mul_comm]

/-- A continuous linear map commutes with coordinate differentiation. -/
theorem _root_.ContinuousLinearMap.partialDeriv_comp
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (i : Fin n) {u : ℝ^n → E} {x : ℝ^n}
    (hu : DifferentiableAt ℝ u x) :
    (∂[i] (L ∘ u)) x = L ((∂[i] u) x) := by
  unfold partialDeriv
  rw [fderiv_comp x L.differentiableAt hu, L.fderiv]
  rfl

/-- Continuous linear maps commute with two coordinate derivatives
under local C² regularity. -/
theorem _root_.ContinuousLinearMap.secondPartialDeriv_comp
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (i j : Fin n) {u : ℝ^n → E} {x : ℝ^n}
    (hu : ContDiffAt ℝ 2 u x) :
    (∂[j] (∂[i] (L ∘ u))) x =
      L ((∂[j] (∂[i] u)) x) := by
  have heq : (∂[i] (L ∘ u)) =ᶠ[nhds x] L ∘ (∂[i] u) := by
    filter_upwards [hu.eventually (by norm_num)] with y hy
    exact L.partialDeriv_comp i (hy.differentiableAt (by norm_num))
  have hd := (contDiffAt_partialDeriv 1 hu i).differentiableAt (by norm_num)
  calc
    _ = (∂[j] (L ∘ (∂[i] u))) x :=
      partialDeriv_eq_of_fderiv_eq (heq.fderiv_eq (𝕜 := ℝ)) j
    _ = _ := L.partialDeriv_comp j hd

/-- Pulling a differentiable curve back by one coordinate gives its ordinary
derivative in that direction and zero in all other directions. -/
theorem partialDeriv_comp_coord
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i j : Fin n) {g : ℝ → E} {x : ℝ^n} (hg : DifferentiableAt ℝ g (x j)) :
    (∂[i] (fun y : ℝ^n ↦ g (y j))) x =
      (if i = j then 1 else 0 : ℝ) • deriv g (x j) := by
  unfold partialDeriv
  have hj : DifferentiableAt ℝ (fun y : ℝ^n ↦ y j) x :=
    (EuclideanSpace.proj j : ℝ^n →L[ℝ] ℝ).differentiableAt
  change fderiv ℝ (g ∘ fun y : ℝ^n ↦ y j) x (EuclideanSpace.single i 1) = _
  rw [fderiv_comp x hg hj,
    ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv]
  change (∂[i] (fun y : ℝ^n ↦ y j)) x • deriv g (x j) = _
  rw [partialDeriv_coord]

/-- First-order coordinate chain rule for a scalar function pulled back by a
Euclidean map. The formula is stated pointwise under local differentiability
assumptions. -/
theorem partialDeriv_comp
    (i : Fin n) (u : ℝ^n → ℝ)
    (Φ : ℝ^n → ℝ^n)
    (x : ℝ^n)
    (hu : DifferentiableAt ℝ u (Φ x)) (hΦ : DifferentiableAt ℝ Φ x) :
    (∂[i] (fun y ↦ u (Φ y))) x =
      ∑ j : Fin n,
        (∂[j] u) (Φ x) *
          (∂[i] (fun y ↦ Φ y j)) x := by
  have hcomp := fderiv_comp x hu hΦ
  have happ := congrArg
    (fun L : ℝ^n →L[ℝ] ℝ ↦
      L (EuclideanSpace.single i (1 : ℝ))) hcomp
  change (∂[i] (fun y ↦ u (Φ y))) x =
    (fderiv ℝ u (Φ x))
      ((fderiv ℝ Φ x) (EuclideanSpace.single i (1 : ℝ))) at happ
  rw [fderiv_apply_eq_sum_partialDeriv_mul] at happ
  apply happ.trans
  apply Finset.sum_congr rfl
  intro j _hj
  congr 1
  exact partialDeriv_apply i j hΦ

/-- Second-order coordinate chain rule for a scalar function pulled back by a
`C²` Euclidean map. The first double sum is the Hessian of `u` contracted
against two chart derivatives; the second sum is the correction involving
the first derivatives of `u` and second derivatives of the chart. It transforms a
second-order operator in nondivergence form under a change of coordinates, for example one
that flattens a smooth boundary. -/
theorem partialDeriv_partialDeriv_comp_at
    (i k : Fin n) (u : ℝ^n → ℝ)
    (Φ : ℝ^n → ℝ^n)
    (x : ℝ^n)
    (hu : ContDiffAt ℝ 2 u (Φ x)) (hΦ : ContDiffAt ℝ 2 Φ x) :
    (∂[i] (fun y ↦ (∂[k] (fun z ↦ u (Φ z))) y)) x =
      (∑ j : Fin n, ∑ l : Fin n,
        (∂[l] (fun z ↦ (∂[j] u) z)) (Φ x) *
          (∂[i] (fun y ↦ Φ y l)) x *
          (∂[k] (fun y ↦ Φ y j)) x) +
      ∑ j : Fin n,
        (∂[j] u) (Φ x) *
          (∂[i] (fun y ↦ (∂[k] (fun z ↦ Φ z j)) y)) x := by
  let A : Fin n → ℝ^n → ℝ := fun j y ↦
    (∂[j] u) (Φ y)
  let B : Fin n → ℝ^n → ℝ := fun j y ↦
    (∂[k] (fun z ↦ Φ z j)) y
  have huD (j : Fin n) :
      ContDiffAt ℝ 1 (fun z ↦ (∂[j] u) z) (Φ x) := by
    have hfd : ContDiffAt ℝ 1 (fderiv ℝ u) (Φ x) :=
      hu.fderiv_right (by norm_num)
    simpa [partialDeriv] using hfd.clm_apply
      (contDiffAt_const : ContDiffAt ℝ 1
        (fun _ : ℝ^n ↦ EuclideanSpace.single j (1 : ℝ)) (Φ x))
  have hΦcoord (j : Fin n) : ContDiffAt ℝ 2 (fun y ↦ Φ y j) x := by
    simpa [Function.comp_def] using
      (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) j).contDiff.contDiffAt.comp x hΦ
  have hΦD (j : Fin n) : ContDiffAt ℝ 1 (B j) x := by
    have hfd : ContDiffAt ℝ 1 (fderiv ℝ (fun z ↦ Φ z j)) x :=
      (hΦcoord j).fderiv_right (by norm_num)
    simpa [B, partialDeriv] using hfd.clm_apply
      (contDiffAt_const : ContDiffAt ℝ 1
        (fun _ : ℝ^n ↦ EuclideanSpace.single k (1 : ℝ)) x)
  have hA (j : Fin n) : ContDiffAt ℝ 1 (A j) x :=
    (huD j).comp x (hΦ.of_le (by norm_num))
  have huNear : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 u (Φ y) :=
    hΦ.continuousAt.eventually (hu.eventually (by norm_num))
  have hΦNear : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 Φ y :=
    hΦ.eventually (by norm_num)
  have hfirst :
      (fun y ↦ (∂[k] (fun z ↦ u (Φ z))) y) =ᶠ[nhds x]
        fun y ↦ ∑ j : Fin n, A j y * B j y := by
    filter_upwards [huNear, hΦNear] with y huy hΦy
    simpa [A, B] using partialDeriv_comp (n := n) k u Φ y
      (huy.differentiableAt (by norm_num))
      (hΦy.differentiableAt (by norm_num))
  have hfirstDeriv :
      (∂[i] (fun y ↦ (∂[k] (fun z ↦ u (Φ z))) y)) x =
        (∂[i] (fun y ↦ ∑ j : Fin n, A j y * B j y)) x :=
    partialDeriv_eq_of_fderiv_eq (hfirst.fderiv_eq (𝕜 := ℝ)) i
  rw [hfirstDeriv]
  have hsum :
      (∂[i] (fun y ↦ ∑ j : Fin n, A j y * B j y)) x =
        ∑ j : Fin n, (∂[i] (fun y ↦ A j y * B j y)) x := by
    unfold partialDeriv
    rw [fderiv_fun_sum]
    · simp
    · intro j _hj
      exact ((hA j).mul (hΦD j)).differentiableAt (by norm_num)
  rw [hsum]
  have hDA (j : Fin n) :
      (∂[i] (A j)) x =
        ∑ l : Fin n,
          (∂[l] (fun z ↦ (∂[j] u) z)) (Φ x) *
            (∂[i] (fun y ↦ Φ y l)) x := by
    simpa [A] using partialDeriv_comp (n := n) i
      (fun z ↦ (∂[j] u) z) Φ x
      ((huD j).differentiableAt (by norm_num))
      (hΦ.differentiableAt (by norm_num))
  calc
    (∑ j : Fin n, (∂[i] (fun y ↦ A j y * B j y)) x) =
        ∑ j : Fin n,
          ((∂[i] (A j)) x * B j x +
            A j x * (∂[i] (B j)) x) := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact partialDeriv_mul (n := n) (i := i) (f := A j) (g := B j) (x := x)
        ((hA j).differentiableAt (by norm_num))
        ((hΦD j).differentiableAt (by norm_num))
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp_rw [hDA]
      simp only [A, B, Finset.sum_mul]

/-- Global `C²` specialization of `partialDeriv_partialDeriv_comp_at`. -/
theorem partialDeriv_partialDeriv_comp
    (i k : Fin n) (u : ℝ^n → ℝ)
    (Φ : ℝ^n → ℝ^n)
    (x : ℝ^n)
    (hu : ContDiff ℝ 2 u) (hΦ : ContDiff ℝ 2 Φ) :
    (∂[i] (fun y ↦ (∂[k] (fun z ↦ u (Φ z))) y)) x =
      (∑ j : Fin n, ∑ l : Fin n,
        (∂[l] (fun z ↦ (∂[j] u) z)) (Φ x) *
          (∂[i] (fun y ↦ Φ y l)) x *
          (∂[k] (fun y ↦ Φ y j)) x) +
      ∑ j : Fin n,
        (∂[j] u) (Φ x) *
          (∂[i] (fun y ↦ (∂[k] (fun z ↦ Φ z j)) y)) x :=
  partialDeriv_partialDeriv_comp_at i k u Φ x hu.contDiffAt hΦ.contDiffAt

/-- Coordinate reciprocal rule at a point where the denominator is nonzero. -/
theorem partialDeriv_inv (i : Fin n)
    (f : ℝ^n → ℝ) (x : ℝ^n)
    (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    (∂[i] (fun y ↦ (f y)⁻¹)) x =
      -(∂[i] f) x / (f x) ^ 2 := by
  have hcomp := (hasFDerivAt_inv (𝕜 := ℝ) hx).comp x hf.hasFDerivAt
  have happ := congrArg
    (fun L : ℝ^n →L[ℝ] ℝ ↦
      L (EuclideanSpace.single i (1 : ℝ))) hcomp.fderiv
  change (fderiv ℝ (fun y ↦ (f y)⁻¹) x)
      (EuclideanSpace.single i (1 : ℝ)) =
    _ at happ
  simpa [partialDeriv, partialDeriv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm] using happ

/-- Coordinate quotient rule at a point where the denominator is nonzero. -/
theorem partialDeriv_div (i : Fin n)
    (f g : ℝ^n → ℝ) (x : ℝ^n)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (hx : g x ≠ 0) :
    (∂[i] (fun y ↦ f y / g y)) x =
      ((∂[i] f) x * g x -
        f x * (∂[i] g) x) / (g x) ^ 2 := by
  have hinv : DifferentiableAt ℝ (fun y ↦ (g y)⁻¹) x := hg.inv hx
  have hmul := fderiv_fun_mul hf hinv
  have happ := congrArg
    (fun L : ℝ^n →L[ℝ] ℝ ↦
      L (EuclideanSpace.single i (1 : ℝ))) hmul
  have hprod :
      (∂[i] (fun y ↦ f y / g y)) x =
        f x * (∂[i] (fun y ↦ (g y)⁻¹)) x +
          (g x)⁻¹ * (∂[i] f) x := by
    simpa [div_eq_mul_inv, partialDeriv,
      add_apply, smul_apply, smul_eq_mul] using happ
  rw [hprod, partialDeriv_inv i g x hg hx]
  field_simp
  ring

/-- Coordinate differentiation preserves equality of germs, including for vector-valued maps. -/
theorem _root_.Filter.EventuallyEq.partialDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ^n → E} {x : ℝ^n} (h : f =ᶠ[nhds x] g) (i : Fin n) :
    (∂[i] f) =ᶠ[nhds x] (∂[i] g) := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  exact congrArg (fun L : ℝ^n →L[ℝ] E ↦ L (EuclideanSpace.single i 1)) hy

/-- If two globally `C¹` scalar functions agree on an open set, their
coordinate derivatives agree on its closure. -/
theorem partialDeriv_eq_on_closure_of_eqOn_open
    (i : Fin n) {f g : ℝ^n → ℝ} {s : Set (ℝ^n)}
    (hs : IsOpen s) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfg : Set.EqOn f g s) :
    Set.EqOn (fun x ↦ (∂[i] f) x)
      (fun x ↦ (∂[i] g) x) (closure s) := by
  have hderiv : Set.EqOn (fun x ↦ (∂[i] f) x)
      (fun x ↦ (∂[i] g) x) s := by
    intro x hx
    apply partialDeriv_congr_nhds i
    filter_upwards [hs.mem_nhds hx] with y hy
    exact hfg hy
  exact hderiv.closure
    (contDiff_partialDeriv_of_succ (m := 0) hf).continuous
    (contDiff_partialDeriv_of_succ (m := 0) hg).continuous

/-- If two globally `C²` scalar functions agree on an open set, their mixed
second coordinate derivatives agree on its closure. -/
theorem secondPartialDeriv_eq_on_closure_of_eqOn_open
    (i j : Fin n) {f g : ℝ^n → ℝ} {s : Set (ℝ^n)}
    (hs : IsOpen s) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfg : Set.EqOn f g s) :
    Set.EqOn
      (fun x ↦ (∂[i] (fun y ↦ (∂[j] f) y)) x)
      (fun x ↦ (∂[i] (fun y ↦ (∂[j] g) y)) x)
      (closure s) := by
  have hfirst := partialDeriv_eq_on_closure_of_eqOn_open j hs
    (hf.of_le (by norm_num)) (hg.of_le (by norm_num)) hfg
  apply partialDeriv_eq_on_closure_of_eqOn_open i hs
    (contDiff_partialDeriv_of_succ (m := 1) hf)
    (contDiff_partialDeriv_of_succ (m := 1) hg)
  exact hfirst.mono subset_closure

/-- The repeated second partial `∂ᵢ∂ᵢ f` at `x` depends only on the germ of `f` at `x`:
if two maps into a real normed space agree near `x`, then their second partials in
coordinate `i` agree at `x`. -/
theorem partialDeriv_second_congr_nhds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin n) {f g : ℝ^n → E} {x : ℝ^n}
    (h : f =ᶠ[nhds x] g) :
    (∂[i] (fun y ↦ (∂[i] f) y)) x =
      (∂[i] (fun y ↦ (∂[i] g) y)) x := by
  have h1 : (fun y ↦ (∂[i] f) y) =ᶠ[nhds x] fun y ↦ (∂[i] g) y := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    simp only [partialDeriv, hy]
  exact congrArg (fun L : ℝ^n →L[ℝ] E ↦ L (EuclideanSpace.single i 1)) h1.fderiv_eq

/-- Divergence respects subtraction when both vector fields are differentiable
coordinatewise at the point. -/
theorem divergence_sub
    {F G : ℝ^n → ℝ^n} {x : ℝ^n}
    (hF : ∀ i, DifferentiableAt ℝ (fun y ↦ F y i) x)
    (hG : ∀ i, DifferentiableAt ℝ (fun y ↦ G y i) x) :
    ∇· (fun y ↦ F y - G y) x = ∇· F x - ∇· G x := by
  unfold divergence
  calc
    (∑ i, (∂[i] (fun y ↦ (F y - G y) i)) x) =
        ∑ i, ((∂[i] (fun y ↦ F y i)) x -
          (∂[i] (fun y ↦ G y i)) x) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simpa using partialDeriv_sub (hF i) (hG i)
    _ = _ := by
      rw [Finset.sum_sub_distrib]

/-- Divergence respects addition when both vector fields are differentiable
coordinatewise at the point. -/
theorem divergence_add
    {F G : ℝ^n → ℝ^n} {x : ℝ^n}
    (hF : ∀ i, DifferentiableAt ℝ (fun y ↦ F y i) x)
    (hG : ∀ i, DifferentiableAt ℝ (fun y ↦ G y i) x) :
    ∇· (fun y ↦ F y + G y) x = ∇· F x + ∇· G x := by
  unfold divergence
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  simpa using partialDeriv_add (hF i) (hG i)

/-- Divergence respects addition of vector fields differentiable at the point. -/
theorem divergence_add_of_differentiableAt
    {F G : ℝ^n → ℝ^n} {x : ℝ^n}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    ∇· (fun y ↦ F y + G y) x = ∇· F x + ∇· G x :=
  divergence_add (fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp x hF)
    (fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp x hG)

/-- Divergence commutes with multiplication by a constant. -/
theorem divergence_const_smul (c : ℝ) (F : ℝ^n → ℝ^n) (x : ℝ^n) :
    ∇· (fun y ↦ c • F y) x = c * ∇· F x := by
  unfold divergence
  have hcoord (i : Fin n) :
      (∂[i] (fun y ↦ (c • F y) i)) x = c * (∂[i] (fun y ↦ F y i)) x := by
    change (∂[i] (fun y ↦ c • F y i)) x = _
    rw [partialDeriv_const_smul, smul_eq_mul]
  simp only [hcoord, Finset.mul_sum]

/-- The Euclidean coordinate Laplacian is additive under local `C²` hypotheses. -/
theorem laplacian_add
    (f g : ℝ^n → ℝ) (x : ℝ^n)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    laplacian (n := n) (fun y ↦ f y + g y) x =
      laplacian (n := n) f x + laplacian (n := n) g x := by
  rw [(hf.add hg).coordinate_laplacian_eq_laplacian,
    hf.coordinate_laplacian_eq_laplacian,
    hg.coordinate_laplacian_eq_laplacian]
  exact hf.laplacian_add hg

/-- Product rule for a coordinate function under the local differentiability
hypotheses used by the coordinate Laplacian:

`Δ(xₖ f) = xₖ Δf + 2 ∂ₖf`. -/
theorem laplacian_coordinate_mul_of_eventually_differentiableAt
    (k : Fin n) (f : ℝ^n → ℝ) (x : ℝ^n)
    (hf : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y)
    (hpartial :
      ∀ i : Fin n,
        DifferentiableAt ℝ
          (fun y ↦ (∂[i] f) y) x) :
    laplacian (n := n) (fun y ↦ y k * f y) x =
      x k * laplacian (n := n) f x +
        2 * (∂[k] f) x := by
  classical
  have hfirst (i : Fin n) :
      (fun y ↦
        (∂[i] (fun z ↦ z k * f z)) y) =ᶠ[nhds x]
        fun y ↦
          (if i = k then 1 else 0) * f y +
            y k * (∂[i] f) y := by
    filter_upwards [hf] with y hfy
    have hcoord :
        DifferentiableAt ℝ (fun z : ℝ^n ↦ z k) y := by
      simpa only [EuclideanSpace.coe_proj] using
        (EuclideanSpace.proj k : ℝ^n →L[ℝ] ℝ).differentiableAt
    rw [partialDeriv_mul hcoord hfy, partialDeriv_coord]
  have hsecond (i : Fin n) :
      (∂[i] (fun y ↦
            (∂[i] (fun z ↦ z k * f z)) y)) x =
        x k *
            (∂[i] (fun y ↦ (∂[i] f) y)) x +
          2 * (if i = k then 1 else 0) *
            (∂[i] f) x := by
    rw [partialDeriv_congr_nhds i (hfirst i)]
    have hconst_mul :
        DifferentiableAt ℝ
          (fun y ↦ (if i = k then 1 else 0) * f y) x :=
      hf.self_of_nhds.const_mul _
    have hcoord :
        DifferentiableAt ℝ (fun y : ℝ^n ↦ y k) x := by
      simpa only [EuclideanSpace.coe_proj] using
        (EuclideanSpace.proj k : ℝ^n →L[ℝ] ℝ).differentiableAt
    have hadd :=
      partialDeriv_add (n := n) (i := i)
        (f := fun y ↦ (if i = k then 1 else 0) * f y)
        (g := fun y ↦ y k * (∂[i] f) y)
        hconst_mul (hcoord.mul (hpartial i))
    rw [hadd]
    rw [show
        (∂[i] (fun y ↦ (if i = k then 1 else 0) * f y)) x =
          (if i = k then 1 else 0) *
            (∂[i] f) x by
      simpa [smul_eq_mul] using
        (partialDeriv_const_smul
          (n := n) (E := ℝ) (if i = k then 1 else 0)
          (i := i) (f := f) (x := x))]
    rw [partialDeriv_mul hcoord (hpartial i), partialDeriv_coord]
    ring
  unfold laplacian
  calc
    (∑ i : Fin n,
        (∂[i] (fun y ↦
            (∂[i] (fun z ↦ z k * f z)) y)) x) =
        ∑ i : Fin n,
          (x k *
              (∂[i] (fun y ↦ (∂[i] f) y)) x +
            2 * (if i = k then 1 else 0) *
              (∂[i] f) x) :=
      Finset.sum_congr rfl fun i _ ↦ hsecond i
    _ = x k *
          (∑ i : Fin n,
            (∂[i] (fun y ↦ (∂[i] f) y)) x) +
        2 * (∂[k] f) x := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp

/-- Product rule for a coordinate function and a scalar `C²` function:

`Δ(xₖ f) = xₖ Δf + 2 ∂ₖf`. -/
theorem laplacian_coordinate_mul
    (k : Fin n) (f : ℝ^n → ℝ) (x : ℝ^n)
    (hf : ContDiffAt ℝ 2 f x) :
    laplacian (n := n) (fun y ↦ y k * f y) x =
      x k * laplacian (n := n) f x +
        2 * (∂[k] f) x := by
  apply laplacian_coordinate_mul_of_eventually_differentiableAt
  · filter_upwards [hf.eventually (by norm_num)] with y hfy
    exact hfy.differentiableAt (by norm_num)
  · intro i
    exact
      (contDiffAt_partialDeriv 1 hf i).differentiableAt
        (by norm_num)

/-- The coordinate Laplacian of a squared affine coordinate is `2`.

It is the strictly subharmonic perturbation used in the weak maximum principle, with no
dimension-dependent normalization. -/
theorem laplacian_coordinate_sq_sub
    (k : Fin n) (c : ℝ) (x : ℝ^n) :
    laplacian (n := n) (fun y ↦ (y k - c) ^ 2) x = 2 := by
  classical
  let q : ℝ^n → ℝ := fun y ↦ (y k - c) ^ 2
  have hfirst (i : Fin n) (y : ℝ^n) :
      (∂[i] q) y =
        if i = k then 2 * (y k - c) else 0 := by
    have hcoord : DifferentiableAt ℝ (fun z : ℝ^n ↦ z k) y := by
      simpa only [EuclideanSpace.coe_proj] using
        (EuclideanSpace.proj k : ℝ^n →L[ℝ] ℝ).differentiableAt
    have hconst : DifferentiableAt ℝ (fun _ : ℝ^n ↦ c) y := by
      fun_prop
    have hsub := partialDeriv_sub (n := n) (i := i)
      (f := fun z : ℝ^n ↦ z k) (g := fun _ ↦ c) (x := y) hcoord hconst
    have hsub' :
        (∂[i] (fun z : ℝ^n ↦ z k - c)) y =
          (∂[i] (fun z : ℝ^n ↦ z k)) y -
            (∂[i] (fun _ : ℝ^n ↦ c)) y := by
      simpa using hsub
    have hmul := partialDeriv_mul (n := n) (i := i)
      (f := fun z : ℝ^n ↦ z k - c)
      (g := fun z : ℝ^n ↦ z k - c) (x := y)
      (hcoord.sub hconst) (hcoord.sub hconst)
    simp only [q, pow_two] at hmul ⊢
    rw [hmul, hsub']
    simp [partialDeriv_coord, partialDeriv_const]
    split <;> ring
  have hsecond (i : Fin n) :
      (∂[i] (fun y ↦ (∂[i] q) y)) x =
        if i = k then 2 else 0 := by
    have hfun :
        (fun y ↦ (∂[i] q) y) =
          fun y ↦ if i = k then 2 * (y k - c) else 0 := by
      funext y
      exact hfirst i y
    rw [hfun]
    by_cases hik : i = k
    · subst i
      simp only [ite_eq_left]
      have hscale :
          (∂[k] (fun y : ℝ^n ↦ 2 * (y k - c))) x =
            2 * (∂[k] (fun y : ℝ^n ↦ y k - c)) x := by
        have hsmul :
            (fun y : ℝ^n ↦ 2 * (y k - c)) =
              (2 : ℝ) • (fun y : ℝ^n ↦ y k - c) := by
          funext y
          simp [smul_eq_mul]
        rw [hsmul]
        change
          (fderiv ℝ ((2 : ℝ) • (fun y : ℝ^n ↦ y k - c)) x)
              (EuclideanSpace.single k (1 : ℝ)) =
            2 * (fderiv ℝ (fun y : ℝ^n ↦ y k - c) x)
              (EuclideanSpace.single k (1 : ℝ))
        rw [congrFun (fderiv_const_smul_field (2 : ℝ)) x]
        simp [smul_eq_mul]
      rw [hscale]
      have hsub := partialDeriv_sub (n := n) (i := k)
        (f := fun y : ℝ^n ↦ y k) (g := fun _ ↦ c) (x := x)
        (by
          simpa only [EuclideanSpace.coe_proj] using
            (EuclideanSpace.proj k : ℝ^n →L[ℝ] ℝ).differentiableAt)
        (by fun_prop)
      simpa [partialDeriv_coord, partialDeriv_const] using hsub
    · simp [hik, partialDeriv_const]
  unfold laplacian
  change (∑ i : Fin n,
    (∂[i] (fun y ↦ (∂[i] q) y)) x) = 2
  simp [hsecond]

/-- The Euclidean Laplacian is invariant under translations of the input. -/
theorem laplacian_comp_add_left
    (f : ℝ^n → ℝ) (c x : ℝ^n)
    (hf : ContDiffAt ℝ 2 f (c + x)) :
    laplacian (n := n) (fun y ↦ f (c + y)) x =
      laplacian (n := n) f (c + x) := by
  classical
  have hshift : ContDiffAt ℝ 2 (fun y ↦ f (c + y)) x := by
    have haffine : ContDiffAt ℝ 2 (fun y : ℝ^n ↦ c + y) x := by
      fun_prop
    simpa [Function.comp_def] using hf.comp x haffine
  unfold laplacian
  refine Finset.sum_congr rfl ?_
  intro i _hi
  change
    ((fun g y ↦ (∂[i] g) y)^[2] (fun y ↦ f (c + y))) x =
      ((fun g y ↦ (∂[i] g) y)^[2] f) (c + x)
  rw [iterate_partialDeriv_eq_iteratedFDeriv_single i 2 hshift,
    iterate_partialDeriv_eq_iteratedFDeriv_single i 2 hf,
    iteratedFDeriv_comp_add_left]

/-- The Euclidean Laplacian is invariant under subtracting a fixed vector
from the input. -/
theorem laplacian_comp_sub_right
    (f : ℝ^n → ℝ) (a x : ℝ^n)
    (hf : ContDiffAt ℝ 2 f (x - a)) :
    laplacian (n := n) (fun y ↦ f (y - a)) x =
      laplacian (n := n) f (x - a) := by
  classical
  have hshift : ContDiffAt ℝ 2 (fun y ↦ f (y - a)) x := by
    have haffine : ContDiffAt ℝ 2 (fun y : ℝ^n ↦ y - a) x := by
      fun_prop
    simpa [Function.comp_def] using hf.comp x haffine
  unfold laplacian
  refine Finset.sum_congr rfl ?_
  intro i _hi
  change
    ((fun g y ↦ (∂[i] g) y)^[2]
        (fun y ↦ f (y - a))) x =
      ((fun g y ↦ (∂[i] g) y)^[2] f) (x - a)
  rw [iterate_partialDeriv_eq_iteratedFDeriv_single i 2 hshift,
    iterate_partialDeriv_eq_iteratedFDeriv_single i 2 hf,
    iteratedFDeriv_comp_sub]

/-- The Euclidean Laplacian commutes with multiplication by a scalar constant.

No regularity hypothesis is needed: Mathlib's total Fréchet derivative commutes with scalar
multiplication even where it is defined to be zero. -/
theorem laplacian_const_smul (c : ℝ)
    (f : ℝ^n → ℝ) (x : ℝ^n) :
    laplacian (n := n) (fun y ↦ c * f y) x =
      c * laplacian (n := n) f x := by
  have hfirst (i : Fin n) :
      (fun y ↦ (∂[i] (fun z ↦ c * f z)) y) =
        fun y ↦ c * (∂[i] f) y := by
    funext y
    simpa [smul_eq_mul] using
      (partialDeriv_const_smul (n := n) (E := ℝ) c
        (i := i) (f := f) (x := y))
  unfold laplacian
  simp_rw [hfirst]
  simp_rw [show ∀ i : Fin n,
      (∂[i] (fun y ↦ c * (∂[i] f) y)) x =
        c * (∂[i] (fun y ↦ (∂[i] f) y)) x by
    intro i
    simpa [smul_eq_mul] using
      (partialDeriv_const_smul (n := n) (E := ℝ) c
        (i := i) (f := fun y ↦ (∂[i] f) y) (x := x))]
  rw [Finset.mul_sum]

/-- The Euclidean gradient commutes with negation. -/
theorem gradient_neg (f : ℝ^n → ℝ)
    (x : ℝ^n) :
    ∇ (-f) x = -∇ f x := by
  ext i
  change ∇ (-f) x i = -∇ f x i
  simp only [gradient_apply_eq_partialDeriv, partialDeriv_neg]

/-- The Euclidean Laplacian commutes with negation. -/
theorem laplacian_neg (f : ℝ^n → ℝ)
    (x : ℝ^n) :
    laplacian (n := n) (-f) x = -laplacian (n := n) f x := by
  have hneg (i : Fin n) :
      (fun y ↦ (∂[i] (-f)) y) =
        -(fun y ↦ (∂[i] f) y) := by
    funext y
    exact partialDeriv_neg (n := n) (i := i) (f := f) (x := y)
  unfold laplacian
  simp_rw [hneg, partialDeriv_neg]
  simpa only using
    (Finset.sum_neg_distrib (s := Finset.univ)
      (fun i : Fin n ↦
        (∂[i] (fun y ↦ (∂[i] f) y)) x))

/-- The Euclidean coordinate Laplacian respects subtraction under local `C²` hypotheses. -/
theorem laplacian_sub
    (f g : ℝ^n → ℝ) (x : ℝ^n)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    laplacian (n := n) (fun y ↦ f y - g y) x =
      laplacian (n := n) f x - laplacian (n := n) g x := by
  rw [(hf.sub hg).coordinate_laplacian_eq_laplacian,
    hf.coordinate_laplacian_eq_laplacian,
    hg.coordinate_laplacian_eq_laplacian]
  exact hf.laplacian_sub hg

end PDE
