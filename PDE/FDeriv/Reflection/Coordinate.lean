/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean.CoordinateReflection
public import PDE.FDeriv.Operators
import PDE.FDeriv.Calculus

/-!
# Differential calculus for coordinate reflections

Let `σᵢ` be the reflection of `ℝ^n` in the coordinate hyperplane `{xᵢ = 0}`. Pulling a function
back by `σᵢ` flips the sign of the `i`-th coordinate derivative and leaves the others unchanged,
so the second derivatives `∂ⱼ∂ⱼ` and hence the Laplacian commute with the pullback. These are
the calculus facts behind the method of reflection for even and odd extensions across a flat
boundary. We also prove two facts on the hyperplane, both for functions differentiable at the
point in question: an even function has zero normal derivative on the reflecting hyperplane, and
a function vanishing on the hyperplane has zero derivative in every tangential coordinate.

## Main results

* `partialDeriv_comp_coordinateReflection_same`,
  `partialDeriv_comp_coordinateReflection_of_ne`: the first-order chain rules
  `∂ᵢ(f ∘ σᵢ) = -(∂ᵢf) ∘ σᵢ` and `∂ⱼ(f ∘ σᵢ) = (∂ⱼf) ∘ σᵢ` for `j ≠ i`, for `f` differentiable
  at the reflected point.
* `secondPartialDeriv_comp_coordinateReflection_at`, `laplacian_comp_coordinateReflection_at`:
  `∂ⱼ∂ⱼ` and `Δ` commute with the pullback, given a `C²` germ at the reflected point.
* `IsEvenUnderCoordinateReflection.partialDeriv_same`,
  `IsOddUnderCoordinateReflection.partialDeriv_same`, and the `_of_ne` variants: parity of
  the coordinate derivatives of even and odd functions.
* `IsEvenUnderCoordinateReflection.partialDeriv_eq_zero`: zero normal derivative of an even
  function on the hyperplane.
* `VanishesOnCoordinateHyperplane.partialDeriv_eq_zero_of_ne`: zero tangential derivatives of
  a zero trace.
-/

@[expose] public section

noncomputable section


namespace PDE.Common

open Filter

private theorem fderiv_coordinateReflection
    {n : ℕ} (i : Fin n) (x : ℝ^n) :
    fderiv ℝ (coordinateReflection i : ℝ^n → ℝ^n) x =
      (coordinateReflectionLinearIsometryEquiv i).toContinuousLinearEquiv := by
  exact
    ((coordinateReflectionLinearIsometryEquiv i).toContinuousLinearEquiv.hasFDerivAt
      (x := x)).fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Differentiating a pullback in the reflected coordinate introduces one
minus sign. -/
theorem partialDeriv_comp_coordinateReflection_same
    {n : ℕ} (i : Fin n) (f : ℝ^n → E) (x : ℝ^n)
    (hf : DifferentiableAt ℝ f (coordinateReflection i x)) :
    (∂[i] (fun y ↦ f (coordinateReflection i y))) x =
      -(∂[i] f) (coordinateReflection i x) := by
  have hreflection :
      DifferentiableAt ℝ (coordinateReflection i : ℝ^n → ℝ^n) x :=
    (coordinateReflectionLinearIsometryEquiv i).toContinuousLinearEquiv.differentiableAt
  unfold partialDeriv
  change
    (fderiv ℝ (f ∘ coordinateReflection i) x)
        (EuclideanSpace.single i 1) = _
  rw [fderiv_comp x hf hreflection]
  rw [fderiv_coordinateReflection, ContinuousLinearMap.comp_apply]
  change
    (fderiv ℝ f (coordinateReflection i x))
        (coordinateReflection i (EuclideanSpace.single i 1)) = _
  rw [coordinateReflection_single_same]
  rw [show EuclideanSpace.single i (-1 : ℝ) =
      -EuclideanSpace.single i (1 : ℝ) by
    ext j
    by_cases hji : j = i <;> simp [hji]]
  rw [map_neg]

/-- Differentiating a pullback in a coordinate distinct from the reflected
one introduces no sign. -/
theorem partialDeriv_comp_coordinateReflection_of_ne
    {n : ℕ} (i j : Fin n) (hji : j ≠ i) (f : ℝ^n → E) (x : ℝ^n)
    (hf : DifferentiableAt ℝ f (coordinateReflection i x)) :
    (∂[j] (fun y ↦ f (coordinateReflection i y))) x =
      (∂[j] f) (coordinateReflection i x) := by
  have hreflection :
      DifferentiableAt ℝ (coordinateReflection i : ℝ^n → ℝ^n) x :=
    (coordinateReflectionLinearIsometryEquiv i).toContinuousLinearEquiv.differentiableAt
  unfold partialDeriv
  change
    (fderiv ℝ (f ∘ coordinateReflection i) x)
        (EuclideanSpace.single j 1) = _
  rw [fderiv_comp x hf hreflection]
  rw [fderiv_coordinateReflection, ContinuousLinearMap.comp_apply]
  change
    (fderiv ℝ f (coordinateReflection i x))
        (coordinateReflection i (EuclideanSpace.single j 1)) = _
  rw [coordinateReflection_single_of_ne i j hji]

/-- Two derivatives in the same coordinate commute with pullback by a coordinate reflection.
Only a `C²` germ at the reflected evaluation point is needed. -/
theorem secondPartialDeriv_comp_coordinateReflection_at
    {n : ℕ} (i j : Fin n) (f : ℝ^n → ℝ) (x : ℝ^n)
    (hf : ContDiffAt ℝ 2 f (coordinateReflection i x)) :
    (∂[j] (fun y ↦ (∂[j] (fun z ↦ f (coordinateReflection i z))) y)) x =
      (∂[j] (fun y ↦ (∂[j] f) y))
        (coordinateReflection i x) := by
  have hf_near : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 f (coordinateReflection i y) :=
    (coordinateReflectionLinearIsometryEquiv i).continuous.continuousAt.eventually
      (hf.eventually (by norm_num))
  have hpartialDiff : DifferentiableAt ℝ (fun y ↦ (∂[j] f) y)
      (coordinateReflection i x) :=
    (contDiffAt_partialDeriv 1 hf j).differentiableAt one_ne_zero
  by_cases hji : j = i
  · subst j
    have hfirst :
        (fun y ↦ (∂[i] (fun z ↦ f (coordinateReflection i z))) y) =ᶠ[nhds x]
          fun y ↦ -(∂[i] f) (coordinateReflection i y) := by
      filter_upwards [hf_near] with y hfy
      exact partialDeriv_comp_coordinateReflection_same i f y
        (hfy.differentiableAt (by norm_num))
    rw [partialDeriv_congr_nhds i hfirst]
    change (∂[i] (-(fun y ↦ (∂[i] f) (coordinateReflection i y)))) x = _
    rw [partialDeriv_neg]
    rw [partialDeriv_comp_coordinateReflection_same i
      (fun y ↦ (∂[i] f) y) x hpartialDiff]
    ring
  · have hfirst :
        (fun y ↦ (∂[j] (fun z ↦ f (coordinateReflection i z))) y) =ᶠ[nhds x]
          fun y ↦ (∂[j] f) (coordinateReflection i y) := by
      filter_upwards [hf_near] with y hfy
      exact partialDeriv_comp_coordinateReflection_of_ne i j hji f y
        (hfy.differentiableAt (by norm_num))
    rw [partialDeriv_congr_nhds j hfirst]
    exact partialDeriv_comp_coordinateReflection_of_ne i j hji
      (fun y ↦ (∂[j] f) y) x hpartialDiff

/-- Global `C²` specialization of
`secondPartialDeriv_comp_coordinateReflection_at`. -/
theorem secondPartialDeriv_comp_coordinateReflection
    {n : ℕ} (i j : Fin n) (f : ℝ^n → ℝ) (x : ℝ^n)
    (hf : ContDiff ℝ 2 f) :
    (∂[j] (fun y ↦ (∂[j] (fun z ↦ f (coordinateReflection i z))) y)) x =
      (∂[j] (fun y ↦ (∂[j] f) y))
        (coordinateReflection i x) :=
  secondPartialDeriv_comp_coordinateReflection_at i j f x hf.contDiffAt

/-- The Euclidean coordinate Laplacian is invariant under reflection in a coordinate hyperplane
when the scalar field is `C²` at the reflected point. -/
theorem laplacian_comp_coordinateReflection_at
    {n : ℕ} (i : Fin n) (f : ℝ^n → ℝ) (x : ℝ^n)
    (hf : ContDiffAt ℝ 2 f (coordinateReflection i x)) :
    laplacian (fun y ↦ f (coordinateReflection i y)) x =
      laplacian f (coordinateReflection i x) := by
  unfold laplacian
  apply Finset.sum_congr rfl
  intro j _
  exact secondPartialDeriv_comp_coordinateReflection_at i j f x hf

/-- The Euclidean coordinate Laplacian is invariant under reflection in any
coordinate hyperplane. -/
theorem laplacian_comp_coordinateReflection
    {n : ℕ} (i : Fin n) (f : ℝ^n → ℝ) (x : ℝ^n)
    (hf : ContDiff ℝ 2 f) :
    laplacian (fun y ↦ f (coordinateReflection i y)) x =
      laplacian f (coordinateReflection i x) :=
  laplacian_comp_coordinateReflection_at i f x hf.contDiffAt

/-- The derivative of a reflection-odd function in the reflected coordinate
is reflection-even. -/
theorem IsOddUnderCoordinateReflection.partialDeriv_same
    {n : ℕ} {i : Fin n} {f : ℝ^n → ℝ}
    (hf : IsOddUnderCoordinateReflection i f) (hcont : ContDiff ℝ 1 f) :
    IsEvenUnderCoordinateReflection i (fun x ↦ (∂[i] f) x) := by
  intro x
  have hfun : (fun y ↦ f (coordinateReflection i y)) = -f := by
    funext y
    exact hf y
  have hchain := partialDeriv_comp_coordinateReflection_same i f x
    (hcont.differentiable (by norm_num)).differentiableAt
  rw [hfun, partialDeriv_neg] at hchain
  exact (neg_inj.mp hchain).symm

/-- A derivative of a reflection-odd function in a distinct coordinate
remains reflection-odd. -/
theorem IsOddUnderCoordinateReflection.partialDeriv_of_ne
    {n : ℕ} {i j : Fin n} (hji : j ≠ i) {f : ℝ^n → ℝ}
    (hf : IsOddUnderCoordinateReflection i f) (hcont : ContDiff ℝ 1 f) :
    IsOddUnderCoordinateReflection i (fun x ↦ (∂[j] f) x) := by
  intro x
  have hfun : (fun y ↦ f (coordinateReflection i y)) = -f := by
    funext y
    exact hf y
  have hchain := partialDeriv_comp_coordinateReflection_of_ne i j hji f x
    (hcont.differentiable (by norm_num)).differentiableAt
  rw [hfun, partialDeriv_neg] at hchain
  exact hchain.symm

/-- The derivative of a reflection-even function in the reflected coordinate
is reflection-odd. -/
theorem IsEvenUnderCoordinateReflection.partialDeriv_same
    {n : ℕ} {i : Fin n} {f : ℝ^n → ℝ}
    (hf : IsEvenUnderCoordinateReflection i f) (hcont : ContDiff ℝ 1 f) :
    IsOddUnderCoordinateReflection i (fun x ↦ (∂[i] f) x) := by
  intro x
  have hfun : (fun y ↦ f (coordinateReflection i y)) = f := by
    funext y
    exact hf y
  have hchain := partialDeriv_comp_coordinateReflection_same i f x
    (hcont.differentiable (by norm_num)).differentiableAt
  rw [hfun] at hchain
  linarith

/-- A derivative of a reflection-even function in a distinct coordinate
remains reflection-even. -/
theorem IsEvenUnderCoordinateReflection.partialDeriv_of_ne
    {n : ℕ} {i j : Fin n} (hji : j ≠ i) {f : ℝ^n → ℝ}
    (hf : IsEvenUnderCoordinateReflection i f) (hcont : ContDiff ℝ 1 f) :
    IsEvenUnderCoordinateReflection i (fun x ↦ (∂[j] f) x) := by
  intro x
  have hfun : (fun y ↦ f (coordinateReflection i y)) = f := by
    funext y
    exact hf y
  have hchain := partialDeriv_comp_coordinateReflection_of_ne i j hji f x
    (hcont.differentiable (by norm_num)).differentiableAt
  rw [hfun] at hchain
  exact hchain.symm

/-- The normal derivative of an even function vanishes on its reflecting
hyperplane. -/
theorem IsEvenUnderCoordinateReflection.partialDeriv_eq_zero
    {n : ℕ} {i : Fin n} {f : ℝ^n → ℝ}
    (hf : IsEvenUnderCoordinateReflection i f) {x : ℝ^n}
    (hx : x ∈ coordinateHyperplane i) (hdiff : DifferentiableAt ℝ f x) :
    (∂[i] f) x = 0 := by
  have hfixed : coordinateReflection i x = x :=
    (coordinateReflection_eq_self_iff i x).2 hx
  have hfun : (fun y ↦ f (coordinateReflection i y)) = f := by
    funext y
    exact hf y
  have hchain := partialDeriv_comp_coordinateReflection_same i f x (by
    simpa [hfixed] using hdiff)
  rw [hfun, hfixed] at hchain
  linarith

/-- A differentiable zero trace on one coordinate hyperplane has zero
derivative in every tangential coordinate. -/
theorem VanishesOnCoordinateHyperplane.partialDeriv_eq_zero_of_ne
    {n : ℕ} {i j : Fin n} (hji : j ≠ i) {f : ℝ^n → ℝ}
    (hf : VanishesOnCoordinateHyperplane i f) {x : ℝ^n}
    (hx : x ∈ coordinateHyperplane i) (hdiff : DifferentiableAt ℝ f x) :
    (∂[j] f) x = 0 := by
  rw [partialDeriv_eq_deriv_coordinateLine j x hdiff]
  have hline : f ∘ coordinateLine j x = fun _ ↦ 0 := by
    funext s
    apply hf
    change coordinateLine j x s i = 0
    rw [show coordinateLine j x s i = x i by
      simp [coordinateLine, Ne.symm hji]]
    exact hx
  rw [hline]
  simp

end PDE.Common
