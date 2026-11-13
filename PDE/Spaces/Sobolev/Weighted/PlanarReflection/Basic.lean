/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.OddSecondOrder
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Planar reflection and coordinate derivatives

For `f : ℝ → ℝ → ℝ` in the coordinates `(r, z)` we define the even reflection
`evenReflection2D f r z = f |r| z`, the odd reflection `oddReflection2D f`, equal to `-f (-r) z` for
`r < 0` and to `f r z` otherwise, and the mixed derivative
`mixedIteratedDeriv2D q ell f = ∂_r^q ∂_z^ell f`. Off the axis `r = 0` we compute the mixed
derivatives of both reflections, and almost everywhere we identify those of the even reflection with
a reflection of `∂_r^q ∂_z^ell f`. At the axis we state the trace conditions explicitly: a vanishing
radial derivative for the even reflection and a vanishing value for the odd one. Under them the
reflections of a `C¹` function on `ℝ²` are differentiable, and we compute their Fréchet and partial
derivatives. The coordinate swap `radialCoordinateSwap2D` moves the half-plane `r > 0` to
`SobolevSpace.HalfSpace.upper 2`.

## Main results

* `mixedIteratedDeriv2D_evenReflection_pos`, `mixedIteratedDeriv2D_evenReflection_neg`,
  `mixedIteratedDeriv2D_oddReflection_pos`, `mixedIteratedDeriv2D_oddReflection_neg`: for `r < 0`
  the mixed derivatives of the even and odd reflections at `(r, z)` are `(-1)^q` and `(-1)^(q + 1)`
  times `∂_r^q ∂_z^ell f (-r) z`, and for `r > 0` they are those of `f`.
* `mixedIteratedDeriv2D_evenReflection_ae_eq_parity`: almost everywhere, `∂_r^q ∂_z^ell` of the even
  reflection is the even reflection of `∂_r^q ∂_z^ell f` for even `q` and its odd reflection for odd
  `q`, for every `f`.
* `deriv_evenReflection2D_eq_oddReflection2D`, `deriv_oddReflection2D_eq_evenReflection2D`: the
  radial derivative of a reflection is the reflection of the opposite parity of the radial
  derivative, everywhere, under the trace condition at the axis.
* `differentiable_evenRadialReflection`, `fderiv_evenRadialReflection_apply`,
  `differentiable_oddRadialReflection`, `fderiv_oddRadialReflection_apply`: the reflections of a
  `C¹` function on `ℝ²` that satisfies the trace condition are differentiable, with explicit Fréchet
  derivatives.
* `radialOpenHalfPlane_eq_preimage_upper`, `radialCoordinateSwap2D_reflect`,
  `iteratedPartialDeriv_orderTwo_comp_radialCoordinateSwap2D`: the coordinate swap maps the
  half-plane `r > 0` to the upper half-plane, conjugates the radial sign flip to the reflection
  `SobolevSpace.HalfSpace.reflect 2`, and permutes the partial derivatives through order two.

## How it works

On each side of the axis a reflection agrees near every point with `f` or with `± f (-r) z`, so
Mathlib's `Filter.EventuallyEq.iteratedDeriv_eq` and `iteratedDeriv_comp_neg` give its mixed
derivatives. This is the formula (253) in the proof of Proposition 8 of Duruisseaux, Ganeshram,
George and Anandkumar, with `p = 0` for the even and `p = 1` for the odd reflection. The axis is a
coordinate hyperplane, hence a null set
(`SobolevSpace.HalfSpace.volume_coordinateHyperplane_eq_zero`), which gives the almost-everywhere
statements with no condition on `f`. At the axis we glue the one-sided derivatives on `Iic 0` and
`Ici 0`; they match, as in (254), under the first-order cases of the trace conditions (249) of that
proposition. For the Fréchet derivative at an axis point `x`, the map `R y = (|y 0|, y 1)` satisfies
`‖R y - x‖ = ‖y - x‖`, and `L (R y - x) = L (y - x)` when `L` vanishes on the radial direction, so
the derivative `L` of `F` at `x` is also the derivative of `F ∘ R`; off the axis we compose with
`radialSignFlip2D`.

## References

* V. Duruisseaux, A. Ganeshram, R. J. George and A. Anandkumar, "Stability Framework for the
  Singularity of the Euler Equations on ℝ³", arXiv:2609.10860v2, Appendix B.4, Proposition 8,
  (248)-(249) and (253)-(254), p. 51, for the even and odd reflections, the trace conditions on the
  axis and the derivatives of the reflections off the axis.
  <https://arxiv.org/abs/2609.10860v2>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

open MeasureTheory Filter LineDeriv
open scoped ENNReal RealInnerProductSpace Topology
open SobolevSpace.GraphSpace.HigherOrderReflection

namespace SobolevSpace.Weighted

/-- The even reflection `evenReflection2D f r z = f |r| z` of `f` across the axis `r = 0`. -/
def evenReflection2D (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun r z ↦ f |r| z

/-- The radial sign flip `(r, z) ↦ (-r, z)` as a continuous linear map of `ℝ²`. -/
noncomputable def radialSignFlip2D : (ℝ^2) →L[ℝ] (ℝ^2) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y ↦ EuclideanSpace.single 0 (-y 0) +
        EuclideanSpace.single 1 (y 1)
      map_add' := by
        intro x y
        ext i
        fin_cases i
        · simp [add_comm]
        · simp
      map_smul' := by
        intro c x
        ext i
        fin_cases i <;> simp }

/-- Pointwise formula for the radial sign flip `(r, z) ↦ (-r, z)`. -/
@[simp] theorem radialSignFlip2D_apply (y : (ℝ^2)) :
    radialSignFlip2D y = EuclideanSpace.single 0 (-y 0) +
      EuclideanSpace.single 1 (y 1) := rfl

/-- The linear isometry `(r, z) ↦ (z, r)` of `ℝ²`. It maps the half-plane `{y | 0 < y 0}` onto
`SobolevSpace.HalfSpace.upper 2`, where the last coordinate is positive. -/
noncomputable def radialCoordinateSwap2D : (ℝ^2) ≃ₗᵢ[ℝ] (ℝ^2) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 1)

/-- The first coordinate of the swapped point is the original second coordinate. -/
@[simp] theorem radialCoordinateSwap2D_apply_zero (y : (ℝ^2)) :
    radialCoordinateSwap2D y 0 = y 1 := by
  simp [radialCoordinateSwap2D, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft']

/-- The second coordinate of the swapped point is the original first coordinate. -/
@[simp] theorem radialCoordinateSwap2D_apply_one (y : (ℝ^2)) :
    radialCoordinateSwap2D y 1 = y 0 := by
  simp [radialCoordinateSwap2D, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft']

/-- Swapping the two coordinates twice is the identity. -/
@[simp] theorem radialCoordinateSwap2D_involutive (y : (ℝ^2)) :
    radialCoordinateSwap2D (radialCoordinateSwap2D y) = y := by
  ext i
  fin_cases i <;> simp

/-- `{y | 0 < y 0}` is the preimage of `SobolevSpace.HalfSpace.upper 2` under the coordinate swap.
-/
theorem radialOpenHalfPlane_eq_preimage_upper :
    {y : (ℝ^2) | 0 < y 0} =
      radialCoordinateSwap2D ⁻¹' SobolevSpace.HalfSpace.upper 2 := by
  ext y
  simp [SobolevSpace.HalfSpace.upper, PDE.Common.lastIndex]

/-- The coordinate swap is a linear isometry of the plane, so it preserves
Lebesgue measure. -/
theorem radialCoordinateSwap2D_measurePreserving :
    MeasureTheory.MeasurePreserving (radialCoordinateSwap2D : (ℝ^2) → (ℝ^2))
      volume volume :=
  radialCoordinateSwap2D.measurePreserving

/-- `L^p` membership is unchanged by swapping the radial and axial
coordinates. -/
theorem memLp_comp_radialCoordinateSwap2D_iff
    (f : (ℝ^2) → ℝ) (p : ℝ≥0∞) :
    MemLp (f ∘ radialCoordinateSwap2D) p volume ↔ MemLp f p volume := by
  constructor
  · intro h
    have h' := h.comp_measurePreserving radialCoordinateSwap2D_measurePreserving
    simpa [Function.comp_def] using h'
  · intro h
    exact h.comp_measurePreserving radialCoordinateSwap2D_measurePreserving

/-- Whole-plane integrals are unchanged by the coordinate swap. -/
theorem integral_comp_radialCoordinateSwap2D (g : (ℝ^2) → ℝ) :
    (∫ y : (ℝ^2), g (radialCoordinateSwap2D y)) = ∫ y : (ℝ^2), g y := by
  exact radialCoordinateSwap2D_measurePreserving.integral_comp
    radialCoordinateSwap2D.toHomeomorph.measurableEmbedding g

/-- If `F` is differentiable, then `(∂[0] (F ∘ S)) y = (∂[1] F) (S y)` for the coordinate swap
`S = radialCoordinateSwap2D`. -/
theorem partialDeriv_comp_radialCoordinateSwap2D_zero
    (F : (ℝ^2) → ℝ) (hF : Differentiable ℝ F) (y : (ℝ^2)) :
    (∂[0] (F ∘ radialCoordinateSwap2D)) y =
      (∂[1] F) (radialCoordinateSwap2D y) := by
  have hcomp := fderiv_comp y (hF (radialCoordinateSwap2D y))
    radialCoordinateSwap2D.differentiableAt
  have hswap : fderiv ℝ (radialCoordinateSwap2D : (ℝ^2) → (ℝ^2)) y =
      (radialCoordinateSwap2D.toContinuousLinearEquiv : (ℝ^2) →L[ℝ] (ℝ^2)) := by
    simpa using radialCoordinateSwap2D.toContinuousLinearEquiv.fderiv
  unfold partialDeriv
  rw [hcomp, hswap]
  change
    (fderiv ℝ F (radialCoordinateSwap2D y))
        (radialCoordinateSwap2D (EuclideanSpace.single 0 (1 : ℝ))) =
      (fderiv ℝ F (radialCoordinateSwap2D y)) (EuclideanSpace.single 1 (1 : ℝ))
  congr 1
  ext j
  fin_cases j <;> simp

/-- If `F` is differentiable, then `(∂[1] (F ∘ S)) y = (∂[0] F) (S y)` for the coordinate swap
`S = radialCoordinateSwap2D`. -/
theorem partialDeriv_comp_radialCoordinateSwap2D_one
    (F : (ℝ^2) → ℝ) (hF : Differentiable ℝ F) (y : (ℝ^2)) :
    (∂[1] (F ∘ radialCoordinateSwap2D)) y =
      (∂[0] F) (radialCoordinateSwap2D y) := by
  have hcomp := fderiv_comp y (hF (radialCoordinateSwap2D y))
    radialCoordinateSwap2D.differentiableAt
  have hswap : fderiv ℝ (radialCoordinateSwap2D : (ℝ^2) → (ℝ^2)) y =
      (radialCoordinateSwap2D.toContinuousLinearEquiv : (ℝ^2) →L[ℝ] (ℝ^2)) := by
    simpa using radialCoordinateSwap2D.toContinuousLinearEquiv.fderiv
  unfold partialDeriv
  rw [hcomp, hswap]
  change
    (fderiv ℝ F (radialCoordinateSwap2D y))
        (radialCoordinateSwap2D (EuclideanSpace.single 1 (1 : ℝ))) =
      (fderiv ℝ F (radialCoordinateSwap2D y)) (EuclideanSpace.single 0 (1 : ℝ))
  congr 1
  ext j
  fin_cases j <;> simp

/-- If `A` is `C²` on `ℝ²` and `S = A ∘ radialCoordinateSwap2D`, then at every `y` the iterated
partial derivatives of `S` along `[]`, `[0]`, `[1]`, `[0, 0]`, `[0, 1]` and `[1, 1]` are those of
`A` along `[]`, `[1]`, `[0]`, `[1, 1]`, `[0, 1]` and `[0, 0]` at `radialCoordinateSwap2D y`. -/
theorem iteratedPartialDeriv_orderTwo_comp_radialCoordinateSwap2D
    (A : (ℝ^2) → ℝ) (hA : ContDiff ℝ 2 A) :
    let S := A ∘ radialCoordinateSwap2D
    ∀ y : (ℝ^2),
      iteratedPartialDeriv (n := 2) [] S y = A (radialCoordinateSwap2D y) ∧
      iteratedPartialDeriv (n := 2) [0] S y =
        iteratedPartialDeriv (n := 2) [1] A (radialCoordinateSwap2D y) ∧
      iteratedPartialDeriv (n := 2) [1] S y =
        iteratedPartialDeriv (n := 2) [0] A (radialCoordinateSwap2D y) ∧
      iteratedPartialDeriv (n := 2) [0, 0] S y =
        iteratedPartialDeriv (n := 2) [1, 1] A (radialCoordinateSwap2D y) ∧
      iteratedPartialDeriv (n := 2) [0, 1] S y =
        iteratedPartialDeriv (n := 2) [0, 1] A (radialCoordinateSwap2D y) ∧
      iteratedPartialDeriv (n := 2) [1, 1] S y =
        iteratedPartialDeriv (n := 2) [0, 0] A (radialCoordinateSwap2D y) := by
  dsimp only
  let S := A ∘ radialCoordinateSwap2D
  have hS : ContDiff ℝ 2 S := hA.comp radialCoordinateSwap2D.contDiff
  have hS0 : (fun y ↦ (∂[0] S) y) =
      (fun y ↦ (∂[1] A) (radialCoordinateSwap2D y)) := by
    funext y
    exact partialDeriv_comp_radialCoordinateSwap2D_zero A
      (hA.differentiable (by norm_num)) y
  have hS1 : (fun y ↦ (∂[1] S) y) =
      (fun y ↦ (∂[0] A) (radialCoordinateSwap2D y)) := by
    funext y
    exact partialDeriv_comp_radialCoordinateSwap2D_one A
      (hA.differentiable (by norm_num)) y
  have hA0 : Differentiable ℝ (fun y ↦ (∂[0] A) y) :=
    (PDE.contDiff_partialDeriv_of_succ
      (n := 2) (m := 1) (i := 0) hA).differentiable (by norm_num)
  have hA1 : Differentiable ℝ (fun y ↦ (∂[1] A) y) :=
    (PDE.contDiff_partialDeriv_of_succ
      (n := 2) (m := 1) (i := 1) hA).differentiable (by norm_num)
  intro y
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · change (∂[0] S) y =
      (∂[1] A) (radialCoordinateSwap2D y)
    exact congrFun hS0 y
  · change (∂[1] S) y =
      (∂[0] A) (radialCoordinateSwap2D y)
    exact congrFun hS1 y
  · simp only [iteratedPartialDeriv]
    rw [hS0]
    exact partialDeriv_comp_radialCoordinateSwap2D_zero
      (fun y ↦ (∂[1] A) y) hA1 y
  · have hswap : (fun y ↦ iteratedPartialDeriv (n := 2) [0, 1] S y) =
        fun y ↦ iteratedPartialDeriv (n := 2) [1, 0] S y := by
      exact SobolevSpace.iteratedPartialDeriv_congr_perm_of_contDiff
        hS (List.Perm.swap (0 : Fin 2) 1 []).symm
    rw [congrFun hswap y]
    simp only [iteratedPartialDeriv]
    rw [hS0]
    exact partialDeriv_comp_radialCoordinateSwap2D_one
      (fun y ↦ (∂[1] A) y) hA1 y
  · simp only [iteratedPartialDeriv]
    rw [hS1]
    exact partialDeriv_comp_radialCoordinateSwap2D_one
      (fun y ↦ (∂[0] A) y) hA0 y

/-- With `S = radialCoordinateSwap2D`,
`S (radialSignFlip2D y) = SobolevSpace.HalfSpace.reflect 2 (S y)`: the coordinate swap conjugates
the radial sign flip to the reflection in the last coordinate. -/
theorem radialCoordinateSwap2D_signFlip (y : (ℝ^2)) :
    radialCoordinateSwap2D (radialSignFlip2D y) =
      SobolevSpace.HalfSpace.reflect 2 (radialCoordinateSwap2D y) := by
  ext i
  fin_cases i <;>
    simp [SobolevSpace.HalfSpace.reflect, PDE.Common.lastIndex]

/-- The half-space reflection in the last coordinate is conjugate, by the
coordinate swap, to the radial sign flip: the `simp` direction of
`radialCoordinateSwap2D_signFlip`. -/
@[simp] theorem radialCoordinateSwap2D_reflect (y : (ℝ^2)) :
    radialCoordinateSwap2D (SobolevSpace.HalfSpace.reflect 2 y) =
      radialSignFlip2D (radialCoordinateSwap2D y) := by
  ext i
  fin_cases i <;>
    simp [SobolevSpace.HalfSpace.reflect, PDE.Common.lastIndex, radialSignFlip2D]

/-- The odd reflection of `f` across the axis `r = 0`: `-f (-r) z` for `r < 0` and `f r z`
otherwise. -/
def oddReflection2D (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun r z ↦ if r < 0 then -f (-r) z else f r z

/-- The mixed derivative `∂_r^q ∂_z^ell f`, that is
`iteratedDeriv q (fun ρ ↦ iteratedDeriv ell (f ρ) z) r` at `(r, z)`. -/
def mixedIteratedDeriv2D (q ell : ℕ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun r z ↦ iteratedDeriv q (fun rho ↦ iteratedDeriv ell (f rho) z) r

/-- If `r ↦ f r z` has derivative `0` at `r = 0`, then `r ↦ evenReflection2D f r z` has derivative
`0` at `r = 0`. -/
theorem hasDerivAt_evenReflection2D_axis
    (f : ℝ → ℝ → ℝ) (z : ℝ)
    (hf : HasDerivAt (fun r ↦ f r z) 0 0) :
    HasDerivAt (fun r ↦ evenReflection2D f r z) 0 0 := by
  have hright :
      HasDerivWithinAt (fun r ↦ evenReflection2D f r z) 0 (Set.Ici 0) 0 := by
    refine hf.hasDerivWithinAt.congr ?_ ?_
    · intro r hr
      change 0 ≤ r at hr
      simp [evenReflection2D, abs_of_nonneg hr]
    · simp [evenReflection2D]
  have hleftBase : HasDerivAt (fun r ↦ f (-r) z) 0 0 := by
    have hfnegzero : HasDerivAt (fun r ↦ f r z) 0 (-(0 : ℝ)) := by
      simpa using hf
    change HasDerivAt ((fun r : ℝ ↦ f r z) ∘ Neg.neg) 0 0
    simpa only [zero_mul] using
      hfnegzero.comp 0 (hasDerivAt_neg (0 : ℝ))
  have hleft :
      HasDerivWithinAt (fun r ↦ evenReflection2D f r z) 0 (Set.Iic 0) 0 := by
    refine hleftBase.hasDerivWithinAt.congr ?_ ?_
    · intro r hr
      change r ≤ 0 at hr
      simp [evenReflection2D, abs_of_nonpos hr]
    · simp [evenReflection2D]
  simpa only [Set.Iic_union_Ici, hasDerivWithinAt_univ] using hleft.union hright

/-- If `f 0 z = 0` and `r ↦ f r z` has derivative `f'` at `r = 0`, then `r ↦ oddReflection2D f r z`
has derivative `f'` at `r = 0`. -/
theorem hasDerivAt_oddReflection2D_axis
    (f : ℝ → ℝ → ℝ) (z f' : ℝ)
    (htrace : f 0 z = 0)
    (hf : HasDerivAt (fun r ↦ f r z) f' 0) :
    HasDerivAt (fun r ↦ oddReflection2D f r z) f' 0 := by
  have hright :
      HasDerivWithinAt (fun r ↦ oddReflection2D f r z) f' (Set.Ici 0) 0 := by
    refine hf.hasDerivWithinAt.congr ?_ ?_
    · intro r hr
      change 0 ≤ r at hr
      simp [oddReflection2D, not_lt.mpr hr]
    · simp [oddReflection2D]
  have hleftBase : HasDerivAt (fun r ↦ -f (-r) z) f' 0 := by
    have hfnegzero : HasDerivAt (fun r ↦ f r z) f' (-(0 : ℝ)) := by
      simpa using hf
    change HasDerivAt (-((fun r : ℝ ↦ f r z) ∘ Neg.neg)) f' 0
    simpa using (hfnegzero.comp 0 (hasDerivAt_neg (0 : ℝ))).neg
  have hleft :
      HasDerivWithinAt (fun r ↦ oddReflection2D f r z) f' (Set.Iic 0) 0 := by
    refine hleftBase.hasDerivWithinAt.congr ?_ ?_
    · intro r hr
      change r ≤ 0 at hr
      rcases hr.eq_or_lt with rfl | hr
      · simp [oddReflection2D, htrace]
      · simp [oddReflection2D, hr]
    · simp [oddReflection2D, htrace]
  simpa only [Set.Iic_union_Ici, hasDerivWithinAt_univ] using hleft.union hright

/-- For `r > 0`,
`mixedIteratedDeriv2D q ell (evenReflection2D f) r z = mixedIteratedDeriv2D q ell f r z`. -/
theorem mixedIteratedDeriv2D_evenReflection_pos
    (q ell : ℕ) (f : ℝ → ℝ → ℝ) {r z : ℝ} (hr : 0 < r) :
    mixedIteratedDeriv2D q ell (evenReflection2D f) r z =
      mixedIteratedDeriv2D q ell f r z := by
  apply Filter.EventuallyEq.iteratedDeriv_eq q
  filter_upwards [Ioi_mem_nhds hr] with rho hrho
  change 0 < rho at hrho
  have hfun : evenReflection2D f rho = f rho := by
    funext zeta
    simp [evenReflection2D, abs_of_pos hrho]
  rw [hfun]

/-- For `r < 0`, with `D = mixedIteratedDeriv2D q ell`,
`D (evenReflection2D f) r z = (-1) ^ q * D f (-r) z`. -/
theorem mixedIteratedDeriv2D_evenReflection_neg
    (q ell : ℕ) (f : ℝ → ℝ → ℝ) {r z : ℝ} (hr : r < 0) :
    mixedIteratedDeriv2D q ell (evenReflection2D f) r z =
      (-1 : ℝ) ^ q * mixedIteratedDeriv2D q ell f (-r) z := by
  calc
    mixedIteratedDeriv2D q ell (evenReflection2D f) r z =
        iteratedDeriv q (fun rho ↦ iteratedDeriv ell (f (-rho)) z) r := by
      apply Filter.EventuallyEq.iteratedDeriv_eq q
      filter_upwards [Iio_mem_nhds hr] with rho hrho
      change rho < 0 at hrho
      have hfun : evenReflection2D f rho = f (-rho) := by
        funext zeta
        simp [evenReflection2D, abs_of_neg hrho]
      rw [hfun]
    _ = (-1 : ℝ) ^ q * mixedIteratedDeriv2D q ell f (-r) z := by
      simpa [mixedIteratedDeriv2D] using
        (iteratedDeriv_comp_neg q (fun rho ↦ iteratedDeriv ell (f rho) z) r)

/-- The radial symmetry axis has zero two-dimensional Lebesgue measure: it is
the coordinate hyperplane `PDE.Common.coordinateHyperplane 0`, which is null by
`SobolevSpace.HalfSpace.volume_coordinateHyperplane_eq_zero`.
-/
theorem volume_radialAxis_eq_zero :
    (volume : Measure (ℝ^2)) {y : (ℝ^2) | y 0 = 0} = 0 :=
  SobolevSpace.HalfSpace.volume_coordinateHyperplane_eq_zero (0 : Fin 2)

/-- For every `f`, almost everywhere on `ℝ²`, `mixedIteratedDeriv2D q ell (evenReflection2D f)`
equals `evenReflection2D (mixedIteratedDeriv2D q ell f)` if `q` is even and
`oddReflection2D (mixedIteratedDeriv2D q ell f)` if `q` is odd. -/
theorem mixedIteratedDeriv2D_evenReflection_ae_eq_parity
    (q ell : ℕ) (f : ℝ → ℝ → ℝ) :
    (fun y : (ℝ^2) ↦ mixedIteratedDeriv2D q ell (evenReflection2D f)
      (y 0) (y 1)) =ᵐ[volume]
      if Even q then
        fun y ↦ evenReflection2D (mixedIteratedDeriv2D q ell f) (y 0) (y 1)
      else
        fun y ↦ oddReflection2D (mixedIteratedDeriv2D q ell f) (y 0) (y 1) := by
  have haxis : ∀ᵐ y ∂(volume : Measure (ℝ^2)), y 0 ≠ 0 := by
    rw [ae_iff]
    simpa only [Set.mem_ofPred_eq, not_not] using volume_radialAxis_eq_zero
  filter_upwards [haxis] with y hy
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · rw [mixedIteratedDeriv2D_evenReflection_neg q ell f hneg]
    by_cases heven : Even q
    · rcases heven with ⟨t, rfl⟩
      simp [evenReflection2D, abs_of_neg hneg]
    · have hodd : Odd q := Nat.not_even_iff_odd.mp heven
      rcases hodd with ⟨t, rfl⟩
      simp [oddReflection2D, hneg, pow_add, pow_mul]
  · rw [mixedIteratedDeriv2D_evenReflection_pos q ell f hpos]
    by_cases heven : Even q
    · simp [heven, evenReflection2D, abs_of_pos hpos]
    · simp [heven, oddReflection2D, not_lt.mpr hpos.le]

/-- For `r > 0`,
`mixedIteratedDeriv2D q ell (oddReflection2D f) r z = mixedIteratedDeriv2D q ell f r z`. -/
theorem mixedIteratedDeriv2D_oddReflection_pos
    (q ell : ℕ) (f : ℝ → ℝ → ℝ) {r z : ℝ} (hr : 0 < r) :
    mixedIteratedDeriv2D q ell (oddReflection2D f) r z =
      mixedIteratedDeriv2D q ell f r z := by
  apply Filter.EventuallyEq.iteratedDeriv_eq q
  filter_upwards [Ioi_mem_nhds hr] with rho hrho
  change 0 < rho at hrho
  have hfun : oddReflection2D f rho = f rho := by
    funext zeta
    simp [oddReflection2D, not_lt.mpr hrho.le]
  rw [hfun]

/-- For `r < 0`, with `D = mixedIteratedDeriv2D q ell`,
`D (oddReflection2D f) r z = (-1) ^ (q + 1) * D f (-r) z`. -/
theorem mixedIteratedDeriv2D_oddReflection_neg
    (q ell : ℕ) (f : ℝ → ℝ → ℝ) {r z : ℝ} (hr : r < 0) :
    mixedIteratedDeriv2D q ell (oddReflection2D f) r z =
      (-1 : ℝ) ^ (q + 1) * mixedIteratedDeriv2D q ell f (-r) z := by
  calc
    mixedIteratedDeriv2D q ell (oddReflection2D f) r z =
        iteratedDeriv q (fun rho ↦ -iteratedDeriv ell (f (-rho)) z) r := by
      apply Filter.EventuallyEq.iteratedDeriv_eq q
      filter_upwards [Iio_mem_nhds hr] with rho hrho
      change rho < 0 at hrho
      have hfun : oddReflection2D f rho = -(f (-rho)) := by
        funext zeta
        simp [oddReflection2D, hrho]
      rw [hfun, iteratedDeriv_neg]
    _ = iteratedDeriv q
          (-(fun rho ↦ iteratedDeriv ell (f (-rho)) z)) r := by rfl
    _ = -iteratedDeriv q (fun rho ↦ iteratedDeriv ell (f (-rho)) z) r :=
      iteratedDeriv_neg q (fun rho ↦ iteratedDeriv ell (f (-rho)) z) r
    _ = (-1 : ℝ) ^ (q + 1) * mixedIteratedDeriv2D q ell f (-r) z := by
      have hcomp :
          iteratedDeriv q (fun rho ↦ iteratedDeriv ell (f (-rho)) z) r =
            (-1 : ℝ) ^ q * mixedIteratedDeriv2D q ell f (-r) z := by
        simpa [mixedIteratedDeriv2D] using
          (iteratedDeriv_comp_neg q (fun rho ↦ iteratedDeriv ell (f rho) z) r)
      rw [hcomp, pow_succ]
      ring

/-- If `r ↦ f r z` has derivative `df r z` at every `r`, for every `z`, and `df 0 z = 0` for all
`z`, then the radial derivative `(r, z) ↦ deriv (fun ρ ↦ evenReflection2D f ρ z) r` is
`oddReflection2D df`. -/
theorem deriv_evenReflection2D_eq_oddReflection2D
    (f df : ℝ → ℝ → ℝ)
    (hderiv : ∀ r z, HasDerivAt (fun rho ↦ f rho z) (df r z) r)
    (htrace : ∀ z, df 0 z = 0) :
    (fun r z ↦ deriv (fun rho ↦ evenReflection2D f rho z) r) =
      oddReflection2D df := by
  funext r z
  by_cases hr0 : r = 0
  · subst r
    have haxis : HasDerivAt (fun rho ↦ evenReflection2D f rho z) 0 0 :=
      hasDerivAt_evenReflection2D_axis f z (by simpa [htrace z] using hderiv 0 z)
    rw [haxis.deriv]
    simp [oddReflection2D, htrace]
  · rcases lt_or_gt_of_ne hr0 with hr | hr
    · have hoff := mixedIteratedDeriv2D_evenReflection_neg 1 0 f (z := z) hr
      simpa [mixedIteratedDeriv2D, iteratedDeriv_succ, oddReflection2D, hr,
        (hderiv (-r) z).deriv] using hoff
    · have hoff := mixedIteratedDeriv2D_evenReflection_pos 1 0 f (z := z) hr
      simpa [mixedIteratedDeriv2D, iteratedDeriv_succ, oddReflection2D,
        not_lt.mpr hr.le, (hderiv r z).deriv] using hoff

/-- If `r ↦ f r z` has derivative `df r z` at every `r`, for every `z`, and `f 0 z = 0` for all `z`,
then the radial derivative `(r, z) ↦ deriv (fun ρ ↦ oddReflection2D f ρ z) r` is
`evenReflection2D df`. -/
theorem deriv_oddReflection2D_eq_evenReflection2D
    (f df : ℝ → ℝ → ℝ)
    (hderiv : ∀ r z, HasDerivAt (fun rho ↦ f rho z) (df r z) r)
    (htrace : ∀ z, f 0 z = 0) :
    (fun r z ↦ deriv (fun rho ↦ oddReflection2D f rho z) r) =
      evenReflection2D df := by
  funext r z
  by_cases hr0 : r = 0
  · subst r
    have haxis : HasDerivAt (fun rho ↦ oddReflection2D f rho z) (df 0 z) 0 :=
      hasDerivAt_oddReflection2D_axis f z (df 0 z) (htrace z) (hderiv 0 z)
    rw [haxis.deriv]
    simp [evenReflection2D]
  · rcases lt_or_gt_of_ne hr0 with hr | hr
    · have hoff := mixedIteratedDeriv2D_oddReflection_neg 1 0 f (z := z) hr
      simpa [mixedIteratedDeriv2D, iteratedDeriv_succ, evenReflection2D,
        abs_of_neg hr, (hderiv (-r) z).deriv] using hoff
    · have hoff := mixedIteratedDeriv2D_oddReflection_pos 1 0 f (z := z) hr
      simpa [mixedIteratedDeriv2D, iteratedDeriv_succ, evenReflection2D,
        abs_of_pos hr, (hderiv r z).deriv] using hoff

/-- The map `y ↦ EuclideanSpace.single 0 |y 0| + EuclideanSpace.single 1 (y 1)` of `ℝ²` is
continuous. -/
theorem continuous_evenRadialReflectionPoint :
    Continuous (fun y : (ℝ^2) ↦ EuclideanSpace.single (0 : Fin 2) |y 0| +
      EuclideanSpace.single (1 : Fin 2) (y 1)) := by
  rw [← (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 2 ↦ ℝ)).comp_continuous_iff]
  apply continuous_pi
  intro i
  fin_cases i
  · simpa [Function.comp_def] using
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.abs
  · simpa [Function.comp_def] using
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 1).continuous

/-- If `A` is continuous on `ℝ²` and vanishes on the axis `y 0 = 0`, then its odd reflection,
`-A (radialSignFlip2D y)` for `y 0 < 0` and `A y` otherwise, is continuous. -/
theorem continuous_oddRadialReflectionPoint
    (A : (ℝ^2) → ℝ) (hA : Continuous A)
    (haxis : ∀ z : ℝ, A (EuclideanSpace.single (1 : Fin 2) z) = 0) :
    Continuous (fun y : (ℝ^2) ↦ if y 0 < 0 then
      -A (radialSignFlip2D y) else A y) := by
  let O : (ℝ^2) → ℝ := fun y ↦ if y 0 < 0 then
    -A (radialSignFlip2D y) else A y
  let R : (ℝ^2) → (ℝ^2) := fun y ↦ EuclideanSpace.single (0 : Fin 2) |y 0| +
    EuclideanSpace.single (1 : Fin 2) (y 1)
  have hRcont : Continuous R := by
    simpa [R] using continuous_evenRadialReflectionPoint
  change Continuous O
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x 0 = 0
  · have hxaxis : EuclideanSpace.single (1 : Fin 2) (x 1) = x := by
      ext i
      fin_cases i <;> simp [hx]
    have hOx : O x = 0 := by
      simp only [O, hx, lt_self_iff_false, ite_false]
      rw [← hxaxis]
      exact haxis (x 1)
    have hRx : R x = x := by
      ext i
      fin_cases i <;> simp [R, hx]
    have hAR : Tendsto (fun y ↦ A (R y)) (nhds x) (nhds 0) := by
      have hcompAt : ContinuousAt (fun y ↦ A (R y)) x := by
        simpa [Function.comp_def] using
          (hA.continuousAt.comp
            (show ContinuousAt R x from hRcont.continuousAt))
      have hAx : A x = 0 := by
        rw [← hxaxis]
        exact haxis (x 1)
      change Tendsto (fun y ↦ A (R y)) (nhds x) (nhds (A (R x))) at hcompAt
      rw [hRx, hAx] at hcompAt
      exact hcompAt
    change Tendsto O (nhds x) (nhds (O x))
    rw [hOx]
    rw [Metric.tendsto_nhds] at hAR ⊢
    intro ε hε
    filter_upwards [hAR ε hε] with y hy
    have hdist : dist (O y) 0 = dist (A (R y)) 0 := by
      by_cases hyr : y 0 < 0
      · have hRy : R y = radialSignFlip2D y := by
          ext i
          fin_cases i <;> simp [R, abs_of_neg hyr]
        simp [O, hyr, hRy]
      · have hyr0 : 0 ≤ y 0 := le_of_not_gt hyr
        have hRy : R y = y := by
          ext i
          fin_cases i <;> simp [R, abs_of_nonneg hyr0]
        simp [O, hyr, hRy]
    rw [hdist]
    exact hy
  · rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · have hnegNhd : {y : (ℝ^2) | y 0 < 0} ∈ nhds x :=
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.continuousAt
          (Iio_mem_nhds hxneg)
      have heq : O =ᶠ[nhds x] fun y ↦ -A (radialSignFlip2D y) := by
        filter_upwards [hnegNhd] with y hy
        simp [O, hy]
      exact (hA.comp radialSignFlip2D.continuous).neg.continuousAt
        |>.congr_of_eventuallyEq heq
    · have hposNhd : {y : (ℝ^2) | 0 < y 0} ∈ nhds x :=
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.continuousAt
          (Ioi_mem_nhds hxpos)
      have heq : O =ᶠ[nhds x] A := by
        filter_upwards [hposNhd] with y hy
        simp [O, not_lt.mpr hy.le]
      exact hA.continuousAt.congr_of_eventuallyEq heq

/-- Let `x 0 = 0`, and let `F` have derivative `L` at `x` with `L (EuclideanSpace.single 0 1) = 0`.
Then `y ↦ F (EuclideanSpace.single 0 |y 0| + EuclideanSpace.single 1 (y 1))` has derivative `L` at
`x`. -/
theorem hasFDerivAt_evenRadialReflection_axis
    (F : (ℝ^2) → ℝ) (L : (ℝ^2) →L[ℝ] ℝ) (x : (ℝ^2))
    (hx : x 0 = 0) (hF : HasFDerivAt F L x)
    (hLrad : L (EuclideanSpace.single (0 : Fin 2) 1) = 0) :
    HasFDerivAt
      (fun y : (ℝ^2) ↦ F (EuclideanSpace.single 0 |y 0| +
        EuclideanSpace.single 1 (y 1))) L x := by
  let R : (ℝ^2) → (ℝ^2) := fun y ↦ EuclideanSpace.single 0 |y 0| +
    EuclideanSpace.single 1 (y 1)
  have hRcont : Continuous R := by
    simpa [R] using continuous_evenRadialReflectionPoint
  have hRx : R x = x := by
    ext i
    fin_cases i <;> simp [R, hx]
  have hnorm (y : (ℝ^2)) : ‖R y - x‖ = ‖y - x‖ := by
    have hsquare : ‖R y - x‖ ^ 2 = ‖y - x‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      simp [Fin.sum_univ_two, R, hx, sq_abs]
    nlinarith [norm_nonneg (R y - x), norm_nonneg (y - x)]
  have hdecomp (v : (ℝ^2)) : v =
      v 0 • EuclideanSpace.single (0 : Fin 2) 1 +
        v 1 • EuclideanSpace.single (1 : Fin 2) 1 := by
    ext i
    fin_cases i <;> simp
  have hLeq (y : (ℝ^2)) : L (R y - x) = L (y - x) := by
    rw [hdecomp (R y - x), hdecomp (y - x)]
    simp [map_add, hLrad, R, hx]
  rw [hasFDerivAt_iff_tendsto] at hF ⊢
  have hcomp := hF.comp (by simpa [hRx] using hRcont.tendsto x)
  convert hcomp using 1
  funext y
  change ‖y - x‖⁻¹ * ‖F (R y) - F (R x) - L (y - x)‖ =
    ‖R y - x‖⁻¹ * ‖F (R y) - F x - L (R y - x)‖
  rw [hRx, hnorm y, hLeq y]

/-- Let `x 0 = 0` and `A x = 0`, and let `A` have derivative `L` at `x` with
`L (EuclideanSpace.single 1 1) = 0`. Then the odd reflection of `A`, `-A (radialSignFlip2D y)` for
`y 0 < 0` and `A y` otherwise, has derivative `L` at `x`. -/
theorem hasFDerivAt_oddRadialReflection_axis
    (A : (ℝ^2) → ℝ) (L : (ℝ^2) →L[ℝ] ℝ) (x : (ℝ^2))
    (hx : x 0 = 0) (hAx : A x = 0) (hA : HasFDerivAt A L x)
    (hLax : L (EuclideanSpace.single (1 : Fin 2) 1) = 0) :
    HasFDerivAt
      (fun y : (ℝ^2) ↦ if y 0 < 0 then -A (radialSignFlip2D y) else A y) L x := by
  let R : (ℝ^2) → (ℝ^2) := fun y ↦ EuclideanSpace.single (0 : Fin 2) |y 0| +
    EuclideanSpace.single (1 : Fin 2) (y 1)
  have hRcont : Continuous R := by
    simpa [R] using continuous_evenRadialReflectionPoint
  have hRx : R x = x := by
    ext i
    fin_cases i <;> simp [R, hx]
  have hnorm (y : (ℝ^2)) : ‖R y - x‖ = ‖y - x‖ := by
    have hsquare : ‖R y - x‖ ^ 2 = ‖y - x‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      simp [Fin.sum_univ_two, R, hx, sq_abs]
    nlinarith [norm_nonneg (R y - x), norm_nonneg (y - x)]
  have hdecomp (v : (ℝ^2)) : v =
      v 0 • EuclideanSpace.single (0 : Fin 2) 1 +
        v 1 • EuclideanSpace.single (1 : Fin 2) 1 := by
    ext i
    fin_cases i <;> simp
  have hLneg (y : (ℝ^2)) (hy : y 0 < 0) :
      L (R y - x) = -L (y - x) := by
    rw [hdecomp (R y - x), hdecomp (y - x)]
    simp [map_add, hLax, R, hx, abs_of_neg hy]
  rw [hasFDerivAt_iff_tendsto] at hA ⊢
  have hcomp := hA.comp (by simpa [hRx] using hRcont.tendsto x)
  convert hcomp using 1
  funext y
  change ‖y - x‖⁻¹ * ‖(if y 0 < 0 then -A (radialSignFlip2D y) else A y) -
      (if x 0 < 0 then -A (radialSignFlip2D x) else A x) - L (y - x)‖ =
    ‖R y - x‖⁻¹ * ‖A (R y) - A x - L (R y - x)‖
  rw [hnorm]
  by_cases hy : y 0 < 0
  · have hRy : R y = radialSignFlip2D y := by
      ext i
      fin_cases i <;> simp [R, radialSignFlip2D, abs_of_neg hy]
    rw [ite_eq_left hy, ite_eq_right (by simp [hx]), hAx, hLneg y hy, hRy]
    simp only [sub_zero, sub_neg_eq_add]
    rw [show -A (radialSignFlip2D y) - L (y - x) =
        -(A (radialSignFlip2D y) + L (y - x)) by ring, norm_neg]
  · have hRy : R y = y := by
      ext i
      fin_cases i <;> simp [R, abs_of_nonneg (le_of_not_gt hy)]
    rw [ite_eq_right hy, ite_eq_right (by simp [hx]), hAx, hRy]

/-- If `F` is `C¹` on `ℝ²` and `∂[0] F` vanishes on the axis `y 0 = 0`, then
`y ↦ F (EuclideanSpace.single 0 |y 0| + EuclideanSpace.single 1 (y 1))` is differentiable. -/
theorem differentiable_evenRadialReflection
    (F : (ℝ^2) → ℝ) (hF : ContDiff ℝ 1 F)
    (htrace : ∀ z : ℝ,
      (∂[0] F)
        (EuclideanSpace.single (1 : Fin 2) z) = 0) :
    Differentiable ℝ (fun y : (ℝ^2) ↦
      F (EuclideanSpace.single 0 |y 0| + EuclideanSpace.single 1 (y 1))) := by
  let R : (ℝ^2) → (ℝ^2) := fun y ↦ EuclideanSpace.single 0 |y 0| +
    EuclideanSpace.single 1 (y 1)
  have hFdiff : Differentiable ℝ F := hF.differentiable (by norm_num)
  intro x
  by_cases hx : x 0 = 0
  · have hxaxis : EuclideanSpace.single (1 : Fin 2) (x 1) = x := by
      ext i
      fin_cases i <;> simp [hx]
    have hrad : (fderiv ℝ F x)
        (EuclideanSpace.single (0 : Fin 2) 1) = 0 := by
      change (∂[0] F) x = 0
      rw [← hxaxis]
      exact htrace (x 1)
    exact (hasFDerivAt_evenRadialReflection_axis F (fderiv ℝ F x) x hx
      hFdiff.differentiableAt.hasFDerivAt hrad).differentiableAt
  · rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · have hcomp : DifferentiableAt ℝ
          (fun y : (ℝ^2) ↦ F (radialSignFlip2D y)) x :=
        (hFdiff (radialSignFlip2D x)).comp x radialSignFlip2D.differentiableAt
      have hnegNhd : {y : (ℝ^2) | y 0 < 0} ∈ nhds x :=
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.continuousAt
          (Iio_mem_nhds hxneg)
      have heq : (fun y : (ℝ^2) ↦ F (R y)) =ᶠ[nhds x]
          fun y ↦ F (radialSignFlip2D y) := by
        filter_upwards [hnegNhd] with y hy
        congr 1
        ext i
        fin_cases i <;> simp [R, abs_of_neg hy]
      exact hcomp.congr_of_eventuallyEq heq
    · have hposNhd : {y : (ℝ^2) | 0 < y 0} ∈ nhds x :=
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.continuousAt
          (Ioi_mem_nhds hxpos)
      have heq : (fun y : (ℝ^2) ↦ F (R y)) =ᶠ[nhds x] F := by
        filter_upwards [hposNhd] with y hy
        congr 1
        ext i
        fin_cases i <;> simp [R, abs_of_pos hy]
      exact hFdiff.differentiableAt.congr_of_eventuallyEq heq

/-- If `A` is `C¹` on `ℝ²` and vanishes on the axis `y 0 = 0`, then its odd reflection,
`-A (radialSignFlip2D y)` for `y 0 < 0` and `A y` otherwise, is differentiable. -/
theorem differentiable_oddRadialReflection
    (A : (ℝ^2) → ℝ) (hA : ContDiff ℝ 1 A)
    (haxis : ∀ z : ℝ, A (EuclideanSpace.single (1 : Fin 2) z) = 0) :
    Differentiable ℝ (fun y : (ℝ^2) ↦ if y 0 < 0 then
      -A (radialSignFlip2D y) else A y) := by
  let O : (ℝ^2) → ℝ := fun y ↦ if y 0 < 0 then
    -A (radialSignFlip2D y) else A y
  have hAdiff : Differentiable ℝ A := hA.differentiable (by norm_num)
  change Differentiable ℝ O
  intro x
  by_cases hx : x 0 = 0
  · have hxaxis : EuclideanSpace.single (1 : Fin 2) (x 1) = x := by
      ext i
      fin_cases i <;> simp [hx]
    have hAx : A x = 0 := by
      rw [← hxaxis]
      exact haxis (x 1)
    have hline : (fun t : ℝ ↦ A
        (x + t • EuclideanSpace.single (1 : Fin 2) 1)) = fun _ ↦ 0 := by
      funext t
      rw [← haxis (x 1 + t)]
      congr 1
      ext i
      fin_cases i <;> simp [hx]
    have hLax : (fderiv ℝ A x)
        (EuclideanSpace.single (1 : Fin 2) 1) = 0 := by
      rw [← (hAdiff x).lineDeriv_eq_fderiv]
      unfold lineDeriv
      rw [hline]
      simp
    exact (hasFDerivAt_oddRadialReflection_axis A (fderiv ℝ A x) x hx hAx
      hAdiff.differentiableAt.hasFDerivAt hLax).differentiableAt
  · rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · have hcomp : DifferentiableAt ℝ
          (fun y : (ℝ^2) ↦ -A (radialSignFlip2D y)) x :=
        ((hAdiff (radialSignFlip2D x)).comp x
          radialSignFlip2D.differentiableAt).neg
      have hnegNhd : {y : (ℝ^2) | y 0 < 0} ∈ nhds x :=
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.continuousAt
          (Iio_mem_nhds hxneg)
      have heq : O =ᶠ[nhds x] fun y ↦ -A (radialSignFlip2D y) := by
        filter_upwards [hnegNhd] with y hy
        simp [O, hy]
      exact hcomp.congr_of_eventuallyEq heq
    · have hposNhd : {y : (ℝ^2) | 0 < y 0} ∈ nhds x :=
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.continuousAt
          (Ioi_mem_nhds hxpos)
      have heq : O =ᶠ[nhds x] A := by
        filter_upwards [hposNhd] with y hy
        simp [O, not_lt.mpr hy.le]
      exact hAdiff.differentiableAt.congr_of_eventuallyEq heq

/-- If `A` is `C¹` on `ℝ²` and vanishes on the axis, then the derivative of its odd reflection at
`y` in the direction `v` is `-(fderiv ℝ A (σ y)) (σ v)` if `y 0 < 0` and `(fderiv ℝ A y) v`
otherwise, where `σ = radialSignFlip2D`. -/
theorem fderiv_oddRadialReflection_apply
    (A : (ℝ^2) → ℝ) (hA : ContDiff ℝ 1 A)
    (haxis : ∀ z : ℝ, A (EuclideanSpace.single (1 : Fin 2) z) = 0)
    (y v : (ℝ^2)) :
    (fderiv ℝ (fun x : (ℝ^2) ↦ if x 0 < 0 then
      -A (radialSignFlip2D x) else A x) y) v =
      if y 0 < 0 then
        -(fderiv ℝ A (radialSignFlip2D y)) (radialSignFlip2D v)
      else (fderiv ℝ A y) v := by
  let O : (ℝ^2) → ℝ := fun x ↦ if x 0 < 0 then
    -A (radialSignFlip2D x) else A x
  have hAdiff : Differentiable ℝ A := hA.differentiable (by norm_num)
  by_cases hyneg : y 0 < 0
  · have hnegNhd : {x : (ℝ^2) | x 0 < 0} ∈ nhds y :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.continuousAt
        (Iio_mem_nhds hyneg)
    have heq : O =ᶠ[nhds y] fun x ↦ -A (radialSignFlip2D x) := by
      filter_upwards [hnegNhd] with x hx
      simp [O, hx]
    have hcomp := ((hAdiff (radialSignFlip2D y)).hasFDerivAt.comp y
      radialSignFlip2D.hasFDerivAt).neg
    have hcompDeriv : fderiv ℝ (fun x ↦ -A (radialSignFlip2D x)) y =
        -((fderiv ℝ A (radialSignFlip2D y)).comp radialSignFlip2D) :=
      hcomp.fderiv
    change (fderiv ℝ O y) v = _
    rw [heq.fderiv_eq, hcompDeriv]
    simp [hyneg]
  · by_cases hy0 : y 0 = 0
    · have hyaxis : EuclideanSpace.single (1 : Fin 2) (y 1) = y := by
        ext i
        fin_cases i <;> simp [hy0]
      have hAy : A y = 0 := by
        rw [← hyaxis]
        exact haxis (y 1)
      have hline : (fun t : ℝ ↦ A
          (y + t • EuclideanSpace.single (1 : Fin 2) 1)) = fun _ ↦ 0 := by
        funext t
        rw [← haxis (y 1 + t)]
        congr 1
        ext i
        fin_cases i <;> simp [hy0]
      have hLax : (fderiv ℝ A y)
          (EuclideanSpace.single (1 : Fin 2) 1) = 0 := by
        rw [← (hAdiff y).lineDeriv_eq_fderiv]
        unfold lineDeriv
        rw [hline]
        simp
      have haxisDeriv := hasFDerivAt_oddRadialReflection_axis
        A (fderiv ℝ A y) y hy0 hAy hAdiff.differentiableAt.hasFDerivAt hLax
      change (fderiv ℝ O y) v = _
      rw [haxisDeriv.fderiv]
      simp [hyneg]
    · have hypos : 0 < y 0 := lt_of_le_of_ne (le_of_not_gt hyneg) (Ne.symm hy0)
      have hposNhd : {x : (ℝ^2) | 0 < x 0} ∈ nhds y :=
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.continuousAt
          (Ioi_mem_nhds hypos)
      have heq : O =ᶠ[nhds y] A := by
        filter_upwards [hposNhd] with x hx
        simp [O, not_lt.mpr hx.le]
      change (fderiv ℝ O y) v = _
      rw [heq.fderiv_eq]
      simp [hyneg]

/-- If `A` is `C¹` on `ℝ²` and vanishes on the axis, then the radial partial derivative of its odd
reflection at `y` is `(∂[0] A) (EuclideanSpace.single 0 |y 0| + EuclideanSpace.single 1 (y 1))`. -/
theorem partialDeriv_oddRadialReflection_radial
    (A : (ℝ^2) → ℝ) (hA : ContDiff ℝ 1 A)
    (haxis : ∀ z : ℝ, A (EuclideanSpace.single (1 : Fin 2) z) = 0)
    (y : (ℝ^2)) :
    (∂[0]
        (fun x : (ℝ^2) ↦ if x 0 < 0 then -A (radialSignFlip2D x) else A x)) y =
      (∂[0] A)
        (EuclideanSpace.single 0 |y 0| + EuclideanSpace.single 1 (y 1)) := by
  unfold partialDeriv
  rw [fderiv_oddRadialReflection_apply A hA haxis]
  by_cases hy : y 0 < 0
  · have hflip : radialSignFlip2D (EuclideanSpace.single (0 : Fin 2) 1) =
        -(EuclideanSpace.single (0 : Fin 2) 1) := by
      ext i
      fin_cases i <;> simp [radialSignFlip2D]
    have hpoint : EuclideanSpace.single (0 : Fin 2) |y 0| +
        EuclideanSpace.single (1 : Fin 2) (y 1) = radialSignFlip2D y := by
      ext i
      fin_cases i <;> simp [radialSignFlip2D, abs_of_neg hy]
    rw [hflip, map_neg, hpoint]
    simp [hy]
  · have hpoint : EuclideanSpace.single (0 : Fin 2) |y 0| +
        EuclideanSpace.single (1 : Fin 2) (y 1) = y := by
      ext i
      fin_cases i <;> simp [abs_of_nonneg (le_of_not_gt hy)]
    simp [hy, hpoint]

/-- If `A` is `C¹` on `ℝ²` and vanishes on the axis, then the axial partial derivative of its odd
reflection at `y` is `-(∂[1] A) (radialSignFlip2D y)` if `y 0 < 0` and `(∂[1] A) y` otherwise. -/
theorem partialDeriv_oddRadialReflection_axial
    (A : (ℝ^2) → ℝ) (hA : ContDiff ℝ 1 A)
    (haxis : ∀ z : ℝ, A (EuclideanSpace.single (1 : Fin 2) z) = 0)
    (y : (ℝ^2)) :
    (∂[1]
        (fun x : (ℝ^2) ↦ if x 0 < 0 then -A (radialSignFlip2D x) else A x)) y =
      if y 0 < 0 then
        -(∂[1] A) (radialSignFlip2D y)
      else (∂[1] A) y := by
  unfold partialDeriv
  rw [fderiv_oddRadialReflection_apply A hA haxis]
  by_cases hy : y 0 < 0
  · have hflip : radialSignFlip2D (EuclideanSpace.single (1 : Fin 2) 1) =
        EuclideanSpace.single (1 : Fin 2) 1 := by
      ext i
      fin_cases i <;> simp [radialSignFlip2D]
    rw [hflip]
  · simp [hy]

/-- If `F` is `C¹` on `ℝ²` and `∂[0] F` vanishes on the axis, then the derivative of
`x ↦ F (EuclideanSpace.single 0 |x 0| + EuclideanSpace.single 1 (x 1))` at `y` in the direction `v`
is `(fderiv ℝ F (σ y)) (σ v)` if `y 0 < 0` and `(fderiv ℝ F y) v` otherwise, where
`σ = radialSignFlip2D`. -/
theorem fderiv_evenRadialReflection_apply
    (F : (ℝ^2) → ℝ) (hF : ContDiff ℝ 1 F)
    (htrace : ∀ z : ℝ,
      (∂[0] F)
        (EuclideanSpace.single (1 : Fin 2) z) = 0)
    (y v : (ℝ^2)) :
    (fderiv ℝ (fun x : (ℝ^2) ↦
      F (EuclideanSpace.single 0 |x 0| + EuclideanSpace.single 1 (x 1))) y) v =
      if y 0 < 0 then
        (fderiv ℝ F (radialSignFlip2D y)) (radialSignFlip2D v)
      else (fderiv ℝ F y) v := by
  let R : (ℝ^2) → (ℝ^2) := fun x ↦ EuclideanSpace.single (0 : Fin 2) |x 0| +
    EuclideanSpace.single (1 : Fin 2) (x 1)
  have hFdiff : Differentiable ℝ F := hF.differentiable (by norm_num)
  by_cases hyneg : y 0 < 0
  · have hnegNhd : {x : (ℝ^2) | x 0 < 0} ∈ nhds y :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.continuousAt
        (Iio_mem_nhds hyneg)
    have heq : (fun x : (ℝ^2) ↦ F (R x)) =ᶠ[nhds y]
        fun x ↦ F (radialSignFlip2D x) := by
      filter_upwards [hnegNhd] with x hx
      congr 1
      ext i
      fin_cases i <;> simp [R, abs_of_neg hx]
    have hcomp := (hFdiff (radialSignFlip2D y)).hasFDerivAt.comp y
      radialSignFlip2D.hasFDerivAt
    have hcompDeriv : fderiv ℝ (fun x ↦ F (radialSignFlip2D x)) y =
        (fderiv ℝ F (radialSignFlip2D y)).comp radialSignFlip2D := hcomp.fderiv
    rw [show fderiv ℝ (fun x ↦ F (R x)) y =
        fderiv ℝ (fun x ↦ F (radialSignFlip2D x)) y from heq.fderiv_eq]
    rw [hcompDeriv]
    simp [hyneg]
  · by_cases hy0 : y 0 = 0
    · have hyaxis : EuclideanSpace.single (1 : Fin 2) (y 1) = y := by
        ext i
        fin_cases i <;> simp [hy0]
      have hrad : (fderiv ℝ F y)
          (EuclideanSpace.single (0 : Fin 2) 1) = 0 := by
        change (∂[0] F) y = 0
        rw [← hyaxis]
        exact htrace (y 1)
      have haxis := hasFDerivAt_evenRadialReflection_axis
        F (fderiv ℝ F y) y hy0 hFdiff.differentiableAt.hasFDerivAt hrad
      rw [haxis.fderiv]
      simp [hyneg]
    · have hypos : 0 < y 0 := lt_of_le_of_ne (le_of_not_gt hyneg) (Ne.symm hy0)
      have hposNhd : {x : (ℝ^2) | 0 < x 0} ∈ nhds y :=
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.continuousAt
          (Ioi_mem_nhds hypos)
      have heq : (fun x : (ℝ^2) ↦ F (R x)) =ᶠ[nhds y] F := by
        filter_upwards [hposNhd] with x hx
        congr 1
        ext i
        fin_cases i <;> simp [R, abs_of_pos hx]
      rw [heq.fderiv_eq]
      simp [hyneg]

/-- On `ℝ²`, `fderiv ℝ H y = (∂[0] H) y • PiLp.proj 2 _ 0 + (∂[1] H) y • PiLp.proj 2 _ 1`, with no
hypothesis on `H`. This is `PDE.fderiv_apply_eq_sum_smul_partialDeriv` with `n = 2`. -/
theorem fderiv_eq_partialDeriv_smul_projections
    (H : (ℝ^2) → ℝ) (y : (ℝ^2)) :
    fderiv ℝ H y =
      ((∂[0] H) y) •
          PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0 +
        ((∂[1] H) y) •
          PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 1 := by
  ext v
  rw [PDE.fderiv_apply_eq_sum_smul_partialDeriv, Fin.sum_univ_two]
  simp [mul_comm]

/-- If `F` is `C¹` on `ℝ²` and `∂[0] F` vanishes on the axis, then the radial partial derivative of
`x ↦ F (EuclideanSpace.single 0 |x 0| + EuclideanSpace.single 1 (x 1))` at `y` is
`-(∂[0] F) (radialSignFlip2D y)` if `y 0 < 0` and `(∂[0] F) y` otherwise. -/
theorem partialDeriv_evenRadialReflection_radial
    (F : (ℝ^2) → ℝ) (hF : ContDiff ℝ 1 F)
    (htrace : ∀ z : ℝ,
      (∂[0] F)
        (EuclideanSpace.single (1 : Fin 2) z) = 0)
    (y : (ℝ^2)) :
    (∂[0]
        (fun x : (ℝ^2) ↦ F (EuclideanSpace.single 0 |x 0| +
          EuclideanSpace.single 1 (x 1)))) y =
      if y 0 < 0 then
        -(∂[0] F) (radialSignFlip2D y)
      else (∂[0] F) y := by
  unfold partialDeriv
  rw [fderiv_evenRadialReflection_apply F hF htrace]
  by_cases hy : y 0 < 0
  · have hflip : radialSignFlip2D (EuclideanSpace.single (0 : Fin 2) 1) =
        -(EuclideanSpace.single (0 : Fin 2) 1) := by
      ext i
      fin_cases i <;> simp [radialSignFlip2D]
    rw [hflip, map_neg]
  · simp [hy]

/-- If `F` is `C¹` on `ℝ²` and `∂[0] F` vanishes on the axis, then the axial partial derivative of
`x ↦ F (EuclideanSpace.single 0 |x 0| + EuclideanSpace.single 1 (x 1))` at `y` is
`(∂[1] F) (EuclideanSpace.single 0 |y 0| + EuclideanSpace.single 1 (y 1))`. -/
theorem partialDeriv_evenRadialReflection_axial
    (F : (ℝ^2) → ℝ) (hF : ContDiff ℝ 1 F)
    (htrace : ∀ z : ℝ,
      (∂[0] F)
        (EuclideanSpace.single (1 : Fin 2) z) = 0)
    (y : (ℝ^2)) :
    (∂[1]
        (fun x : (ℝ^2) ↦ F (EuclideanSpace.single 0 |x 0| +
          EuclideanSpace.single 1 (x 1)))) y =
      (∂[1] F)
        (EuclideanSpace.single 0 |y 0| + EuclideanSpace.single 1 (y 1)) := by
  unfold partialDeriv
  rw [fderiv_evenRadialReflection_apply F hF htrace]
  by_cases hy : y 0 < 0
  · have hflip : radialSignFlip2D (EuclideanSpace.single (1 : Fin 2) 1) =
        EuclideanSpace.single (1 : Fin 2) 1 := by
      ext i
      fin_cases i <;> simp [radialSignFlip2D]
    have hpoint : EuclideanSpace.single (0 : Fin 2) |y 0| +
        EuclideanSpace.single (1 : Fin 2) (y 1) = radialSignFlip2D y := by
      ext i
      fin_cases i <;> simp [radialSignFlip2D, abs_of_neg hy]
    rw [hflip, hpoint]
    simp [hy]
  · have hpoint : EuclideanSpace.single (0 : Fin 2) |y 0| +
        EuclideanSpace.single (1 : Fin 2) (y 1) = y := by
      ext i
      fin_cases i <;> simp [abs_of_nonneg (le_of_not_gt hy)]
    simp [hy, hpoint]

end SobolevSpace.Weighted
