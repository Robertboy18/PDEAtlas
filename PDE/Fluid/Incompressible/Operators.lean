/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.SpaceTime.Gradient.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.FDeriv.Operators
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import PDE.FDeriv.SpaceTime
import Mathlib.Data.Nat.Choose.Multinomial
import PDE.Analysis.Integration.CompactByParts
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.PartialDeriv.Support

/-!
# Operators for incompressible flow

Differential operators and pointwise and distributional incompressibility shared by the Euler,
Stokes, and Navier–Stokes equations on `ℝ^n`. Scalar divergence and Laplacian are the canonical
building blocks for the incompressibility predicate and vector Laplacian.

Spacetime is `ℝ^(n + 1)`: coordinate `0` is time and coordinate `i.succ` is the `i`-th spatial
coordinate. Viscosity-specific operators are in `PDE.Fluid.NavierStokes.Operators`.

All operators are built from LeanPDE's totalized coordinate derivative `partialDeriv`, so each
definition has a value everywhere and carries no regularity of its own; lemmas that need the
classical meaning of a derivative state the differentiability hypotheses explicitly. The
material derivative and the incompressibility constraint are set up as in Majda and Bertozzi
(Chapter 1). The weak form of `div v = 0`, tested against gradients of smooth compactly supported
functions, is the condition that defines Temam's divergence-free function spaces (Chapter I).

## Main definitions

* `timeDerivative`, `convectiveDerivative`, `materialDerivative`: `∂ₜv`, `(u·∇)v`, and
  `Dₜᵘv = ∂ₜv + (u·∇)v` for spacetime vector fields; `scalarMaterialDerivative` is the scalar
  version, with the Leibniz rules `scalarMaterialDerivative_add`, `_mul`, `_const_mul`.
* `spatialDivergence`, `spatialLaplacian`, `spatialVectorLaplacian`: divergence and Laplacians
  taken in the spatial coordinates only; `spatialLaplacian_timeSpaceCons` identifies the latter
  with the ordinary Laplacian of the fixed-time slice.
* `DivergenceFreeAt`, `DivergenceFreeOn`, `DivergenceFree`: pointwise incompressibility
  `∇·u = 0` at a point, on a set, and everywhere.
* `SpatialFieldDivergenceFree`, `DistributionallyDivergenceFree`: for a vector field on space,
  pointwise incompressibility and the weak form `∫ v·∇ψ = 0` for every smooth compactly
  supported `ψ`, with `SpatialFieldDivergenceFree.distributionallyDivergenceFree` showing that a
  `C¹` pointwise divergence-free field is distributionally divergence free.

## References

* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001, Chapter 1.
  <https://doi.org/10.1017/CBO9780511613203>
* R. Temam, *Navier–Stokes Equations: Theory and Numerical Analysis*, AMS Chelsea Publishing, 2001,
  Chapter I.
  <https://doi.org/10.1090/chel/343>
-/

open scoped Gradient

@[expose] public section

open PDE (SpaceTime partialDeriv laplacian spatialGradient)

namespace IncompressibleFlow

open EuclideanSpace MeasureTheory Order
open PDE.Common
open scoped Topology

set_option linter.missingDocs true

/-- Pointwise time derivative of a spacetime vector field. -/
noncomputable def timeDerivative (n : ℕ) (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) : ℝ^n :=
  WithLp.toLp 2 fun i ↦
    (∂[(0 : Fin (n + 1))] (fun y ↦ u y i)) x

/-- Component formula for the pointwise time derivative. -/
@[simp]
theorem timeDerivative_apply (n : ℕ) (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) (i : Fin n) :
    timeDerivative n u x i =
      (∂[(0 : Fin (n + 1))] (fun y ↦ u y i)) x := by
  simp [timeDerivative, PiLp.toLp_apply]

/-- Pointwise convective derivative `(u · ∇)v`. -/
noncomputable def convectiveDerivative (n : ℕ)
    (u v : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) : ℝ^n :=
  WithLp.toLp 2 fun i ↦
    ∑ j : Fin n, u x j * (∂[j.succ] (fun y ↦ v y i)) x

/-- Component formula for the pointwise convective derivative. -/
@[simp]
theorem convectiveDerivative_apply (n : ℕ)
    (u v : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) (i : Fin n) :
    convectiveDerivative n u v x i =
      ∑ j : Fin n, u x j * (∂[j.succ] (fun y ↦ v y i)) x := by
  simp [convectiveDerivative, PiLp.toLp_apply]

/-- Material derivative `Dₜᵘv = ∂ₜv + (u · ∇)v`.

Only spatial derivatives occur in the transport term. -/
noncomputable def materialDerivative (n : ℕ) (u : ℝ^(n + 1) → ℝ^n) :
    (ℝ^(n + 1) → ℝ^n) → (ℝ^(n + 1) → ℝ^n) :=
  fun v x ↦
    WithLp.toLp 2 fun i ↦
      (∂[0] (fun y ↦ v y i)) x +
        ∑ j : Fin n, u x j * (∂[j.succ] (fun y ↦ v y i)) x

/-- Component formula for the material derivative. -/
@[simp]
theorem materialDerivative_apply (n : ℕ)
    (u v : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) (i : Fin n) :
    materialDerivative n u v x i =
      (∂[(0 : Fin (n + 1))] (fun y ↦ v y i)) x +
        ∑ j : Fin n, u x j * (∂[j.succ] (fun y ↦ v y i)) x := by
  simp [materialDerivative, PiLp.toLp_apply]

/-- The material derivative is the sum of the time and convective derivatives. -/
theorem materialDerivative_eq_timeDerivative_add_convectiveDerivative
    (n : ℕ) (u v : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) :
    materialDerivative n u v x =
      timeDerivative n v x + convectiveDerivative n u v x := by
  ext i
  simp

/-- Spatial advection `u · ∇ₓw` of a scalar spacetime field.

The Euclidean inner product is the canonical definition; the coordinate sum
is exposed by `spatialScalarAdvection_eq_sum`. -/
noncomputable def spatialScalarAdvection (n : ℕ)
    (u : ℝ^(n + 1) → ℝ^n) (w : ℝ^(n + 1) → ℝ)
    (x : ℝ^(n + 1)) : ℝ :=
  inner ℝ (u x) (spatialGradient w x)

/-- Coordinate formula for spatial scalar advection. -/
theorem spatialScalarAdvection_eq_sum (n : ℕ)
    (u : ℝ^(n + 1) → ℝ^n) (w : ℝ^(n + 1) → ℝ)
    (x : ℝ^(n + 1)) :
    spatialScalarAdvection n u w x =
      ∑ j : Fin n, u x j * (∂[j.succ] w) x := by
  simp [spatialScalarAdvection, PiLp.inner_apply, PDE.spatialGradient_apply,
    RCLike.inner_apply, mul_comm]

/-- Material derivative `Dₜᵘw = ∂ₜw + u · ∇w` of a scalar field. -/
noncomputable def scalarMaterialDerivative (n : ℕ)
    (u : ℝ^(n + 1) → ℝ^n) (w : ℝ^(n + 1) → ℝ)
    (x : ℝ^(n + 1)) : ℝ :=
  (∂[(0 : Fin (n + 1))] w) x +
    spatialScalarAdvection n u w x

/-- Coordinate formula for the scalar material derivative. -/
@[simp]
theorem scalarMaterialDerivative_apply (n : ℕ)
    (u : ℝ^(n + 1) → ℝ^n) (w : ℝ^(n + 1) → ℝ)
    (x : ℝ^(n + 1)) :
    scalarMaterialDerivative n u w x =
      (∂[(0 : Fin (n + 1))] w) x +
        ∑ j : Fin n, u x j * (∂[j.succ] w) x :=
  by
    rw [scalarMaterialDerivative, spatialScalarAdvection_eq_sum]

/-- A vector material derivative is the scalar material derivative of each
component. -/
theorem materialDerivative_apply_eq_scalarMaterialDerivative
    (n : ℕ) (u v : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) (i : Fin n) :
    materialDerivative n u v x i =
      scalarMaterialDerivative n u (fun y ↦ v y i) x := by
  rw [materialDerivative_apply, scalarMaterialDerivative_apply]

/-- The scalar material derivative is additive at points where both scalar
fields are differentiable. -/
theorem scalarMaterialDerivative_add
    {n : ℕ} (u : ℝ^(n + 1) → ℝ^n) {f g : ℝ^(n + 1) → ℝ}
    (x : ℝ^(n + 1)) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    scalarMaterialDerivative n u (fun y ↦ f y + g y) x =
      scalarMaterialDerivative n u f x +
        scalarMaterialDerivative n u g x := by
  rw [scalarMaterialDerivative_apply, scalarMaterialDerivative_apply,
    scalarMaterialDerivative_apply]
  rw [PDE.partialDeriv_add hf hg]
  simp_rw [PDE.partialDeriv_add hf hg, mul_add]
  rw [Finset.sum_add_distrib]
  ring

/-- The scalar material derivative commutes with negation. -/
theorem scalarMaterialDerivative_neg
    {n : ℕ} (u : ℝ^(n + 1) → ℝ^n) (f : ℝ^(n + 1) → ℝ)
    (x : ℝ^(n + 1)) :
    scalarMaterialDerivative n u (fun y ↦ -f y) x =
      -scalarMaterialDerivative n u f x := by
  rw [scalarMaterialDerivative_apply, scalarMaterialDerivative_apply]
  simp_rw [show (fun y ↦ -f y) = -f by rfl, PDE.partialDeriv_neg, mul_neg]
  rw [Finset.sum_neg_distrib]
  ring

/-- The scalar material derivative is subtractive at points where both scalar
fields are differentiable. -/
theorem scalarMaterialDerivative_sub
    {n : ℕ} (u : ℝ^(n + 1) → ℝ^n) {f g : ℝ^(n + 1) → ℝ}
    (x : ℝ^(n + 1)) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    scalarMaterialDerivative n u (fun y ↦ f y - g y) x =
      scalarMaterialDerivative n u f x -
        scalarMaterialDerivative n u g x := by
  rw [scalarMaterialDerivative_apply, scalarMaterialDerivative_apply,
    scalarMaterialDerivative_apply]
  rw [PDE.partialDeriv_sub hf hg]
  simp_rw [PDE.partialDeriv_sub hf hg, mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

/-- A constant scalar can be pulled through a scalar material derivative. -/
theorem scalarMaterialDerivative_const_mul
    {n : ℕ} (u : ℝ^(n + 1) → ℝ^n) (c : ℝ)
    (f : ℝ^(n + 1) → ℝ) (x : ℝ^(n + 1)) :
    scalarMaterialDerivative n u (fun y ↦ c * f y) x =
      c * scalarMaterialDerivative n u f x := by
  rw [scalarMaterialDerivative_apply, scalarMaterialDerivative_apply]
  have hpartial (i : Fin (n + 1)) :
      (∂[i] (fun y ↦ c * f y)) x = c * (∂[i] f) x := by
    simpa [smul_eq_mul] using
      PDE.partialDeriv_const_smul (n := n + 1) c (i := i) (f := f) (x := x)
  rw [hpartial]
  simp_rw [hpartial]
  calc
    c * (∂[0] f) x +
        ∑ j, u x j * (c * (∂[j.succ] f) x) =
        c * (∂[0] f) x +
          c * ∑ j, u x j * (∂[j.succ] f) x := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = c * ((∂[0] f) x +
        ∑ j, u x j * (∂[j.succ] f) x) := by
      ring

/-- The scalar material derivative obeys the product rule. -/
theorem scalarMaterialDerivative_mul
    {n : ℕ} (u : ℝ^(n + 1) → ℝ^n) {f g : ℝ^(n + 1) → ℝ}
    (x : ℝ^(n + 1)) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    scalarMaterialDerivative n u (fun y ↦ f y * g y) x =
      scalarMaterialDerivative n u f x * g x +
        f x * scalarMaterialDerivative n u g x := by
  rw [scalarMaterialDerivative_apply, scalarMaterialDerivative_apply,
    scalarMaterialDerivative_apply]
  rw [PDE.partialDeriv_mul hf hg]
  simp_rw [PDE.partialDeriv_mul hf hg, mul_add]
  rw [Finset.sum_add_distrib]
  have hfirst :
      (∑ j, u x j * ((∂[j.succ] f) x * g x)) =
        (∑ j, u x j * (∂[j.succ] f) x) * g x := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hsecond :
      (∑ j, u x j * (f x * (∂[j.succ] g) x)) =
        f x * ∑ j, u x j * (∂[j.succ] g) x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  rw [hfirst, hsecond]
  ring

/-- Multiplication by a spatial coordinate obeys the expected material
derivative product rule. -/
theorem scalarMaterialDerivative_spatialCoordinate_mul
    {n : ℕ} (u : ℝ^(n + 1) → ℝ^n) {f : ℝ^(n + 1) → ℝ}
    (x : ℝ^(n + 1)) (j : Fin n) (hf : DifferentiableAt ℝ f x) :
    scalarMaterialDerivative n u (fun y ↦ y j.succ * f y) x =
      u x j * f x + x j.succ * scalarMaterialDerivative n u f x := by
  have hproduct (i : Fin (n + 1)) :
      (∂[i] (fun y ↦ y j.succ * f y)) x =
        (if i = j.succ then 1 else 0) * f x +
          x j.succ * (∂[i] f) x := by
    rw [PDE.partialDeriv_mul (by fun_prop) hf, PDE.partialDeriv_coord]
  have hzero : (0 : Fin (n + 1)) ≠ j.succ := by
    intro h
    have hval := congrArg Fin.val h
    simp at hval
  rw [scalarMaterialDerivative_apply, scalarMaterialDerivative_apply]
  simp_rw [hproduct]
  simp only [ite_mul, one_mul, zero_mul, Fin.succ_inj]
  rw [ite_eq_right hzero]
  simp only [zero_add, mul_add, Finset.sum_add_distrib, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  ring_nf

/-- Spatial divergence of a spacetime vector field. -/
noncomputable def spatialDivergence (n : ℕ) (v : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) : ℝ :=
  ∑ i : Fin n, (∂[i.succ] (fun y ↦ v y i)) x

/-- Coordinate formula for spatial divergence. -/
@[simp]
theorem spatialDivergence_apply (n : ℕ) (v : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) :
    spatialDivergence n v x =
      ∑ i : Fin n, (∂[i.succ] (fun y ↦ v y i)) x :=
  rfl

/-- Spatial Laplacian of a scalar field on spacetime. -/
noncomputable def spatialLaplacian (n : ℕ) (f : ℝ^(n + 1) → ℝ)
    (x : ℝ^(n + 1)) : ℝ :=
  ∑ i : Fin n,
    (∂[i.succ] (fun y ↦ (∂[i.succ] f) y)) x

/-- Coordinate formula for the spatial scalar Laplacian. -/
@[simp]
theorem spatialLaplacian_apply (n : ℕ) (f : ℝ^(n + 1) → ℝ)
    (x : ℝ^(n + 1)) :
    spatialLaplacian n f x =
      ∑ i : Fin n,
        (∂[i.succ] (fun y ↦ (∂[i.succ] f) y)) x :=
  rfl

/-- The spacetime spatial Laplacian at `(t,x)` is the ordinary Laplacian of
the fixed-time spatial slice. -/
theorem spatialLaplacian_timeSpaceCons {n : ℕ}
    {f : SpaceTime n → ℝ} (hf : ContDiff ℝ 2 f)
    (t : ℝ) (x : ℝ^n) :
    spatialLaplacian n f (timeSpaceCons t x) =
      laplacian (fun y ↦ f (timeSpaceCons t y)) x := by
  unfold spatialLaplacian laplacian
  apply Finset.sum_congr rfl
  intro i _
  have hfDiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hdfDiff : Differentiable ℝ (∂[i.succ] f) :=
    (PDE.contDiff_partialDeriv_of_succ hf).differentiable (by norm_num)
  have hinner :
      (fun y : ℝ^n ↦ (∂[i] (fun z ↦ f (timeSpaceCons t z))) y) =
        fun y ↦ (∂[i.succ] f) (timeSpaceCons t y) := by
    funext y
    exact PDE.partialDeriv_timeSpaceCons_spatial i f t y
      hfDiff.differentiableAt
  rw [hinner]
  exact (PDE.partialDeriv_timeSpaceCons_spatial i
    (∂[i.succ] f) t x hdfDiff.differentiableAt).symm

/-- Pointwise incompressibility at one spacetime point. -/
def DivergenceFreeAt {n : ℕ} (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) : Prop :=
  spatialDivergence n u x = 0

/-- Pointwise incompressibility on a spacetime set. -/
def DivergenceFreeOn {n : ℕ} (u : ℝ^(n + 1) → ℝ^n)
    (s : Set (ℝ^(n + 1))) : Prop :=
  ∀ x ∈ s, DivergenceFreeAt u x

/-- The pointwise incompressibility condition `∇ · u = 0` on all spacetime. -/
abbrev DivergenceFree {n : ℕ} (u : ℝ^(n + 1) → ℝ^n) : Prop :=
  DivergenceFreeOn u Set.univ

/-- Global pointwise incompressibility implies incompressibility at each point. -/
theorem DivergenceFree.at {n : ℕ} {u : ℝ^(n + 1) → ℝ^n}
    (hu : DivergenceFree u) (x : ℝ^(n + 1)) :
    DivergenceFreeAt u x :=
  hu x (Set.mem_univ x)

/-- Global pointwise incompressibility restricts to every spacetime set. -/
theorem DivergenceFree.on {n : ℕ} {u : ℝ^(n + 1) → ℝ^n}
    (hu : DivergenceFree u) (s : Set (ℝ^(n + 1))) :
    DivergenceFreeOn u s := by
  intro x _hx
  exact hu.at x

/-- Incompressibility on a set holds at each point of that set. -/
theorem DivergenceFreeOn.at {n : ℕ} {u : ℝ^(n + 1) → ℝ^n}
    {s : Set (ℝ^(n + 1))} (hu : DivergenceFreeOn u s)
    {x : ℝ^(n + 1)} (hx : x ∈ s) :
    DivergenceFreeAt u x :=
  hu x hx

/-- On an open set, pointwise incompressibility holds throughout a
neighborhood of each point. -/
theorem DivergenceFreeOn.eventually {n : ℕ}
    {u : ℝ^(n + 1) → ℝ^n} {s : Set (ℝ^(n + 1))}
    (hu : DivergenceFreeOn u s) (hs : IsOpen s)
    {x : ℝ^(n + 1)} (hx : x ∈ s) :
    ∀ᶠ y in 𝓝 x, DivergenceFreeAt u y := by
  filter_upwards [hs.mem_nhds hx] with y hy
  exact hu.at hy

/-- Spatial vector Laplacian `Δₓu`, excluding the time coordinate. -/
noncomputable def spatialVectorLaplacian (n : ℕ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) : ℝ^n :=
  WithLp.toLp 2 fun i ↦
    spatialLaplacian n (fun y ↦ u y i) x

/-- Component formula for the spatial vector Laplacian. -/
@[simp]
theorem spatialVectorLaplacian_apply (n : ℕ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) (i : Fin n) :
    spatialVectorLaplacian n u x i =
      spatialLaplacian n (fun y ↦ u y i) x := by
  simp [spatialVectorLaplacian, PiLp.toLp_apply]

/-- Euclidean divergence of a vector field on space. -/
noncomputable def spatialFieldDivergence {n : ℕ}
    (v : ℝ^n → ℝ^n) (x : ℝ^n) : ℝ :=
  ∑ i : Fin n, (∂[i] (fun y ↦ v y i)) x

/-- Coordinate formula for the divergence of a spatial vector field. -/
@[simp]
theorem spatialFieldDivergence_apply {n : ℕ}
    (v : ℝ^n → ℝ^n) (x : ℝ^n) :
    spatialFieldDivergence v x =
      ∑ i : Fin n, (∂[i] (fun y ↦ v y i)) x :=
  rfl

/-- Pointwise vanishing of the Euclidean divergence of a spatial vector field.

This predicate records only the displayed identity. Because `partialDeriv` is totalized, analytic
uses should supply differentiability separately. -/
def SpatialFieldDivergenceFree {n : ℕ} (v : ℝ^n → ℝ^n) : Prop :=
  ∀ x : ℝ^n, spatialFieldDivergence v x = 0

/-- Positive density `v · ∇ψ` in the weak divergence pairing of a spatial vector field.
For locally integrable `v` and a smooth compactly supported test function `ψ`, its integral
represents the action of negative distributional divergence `-div v` on `ψ`. -/
noncomputable def weakDivergencePairingDensity {n : ℕ}
    (v : ℝ^n → ℝ^n) (ψ : ℝ^n → ℝ) (x : ℝ^n) : ℝ :=
  inner ℝ (v x) (∇ ψ x)

/-- Coordinate formula for the weak divergence-pairing density. -/
theorem weakDivergencePairingDensity_eq_sum {n : ℕ}
    (v : ℝ^n → ℝ^n) (ψ : ℝ^n → ℝ) (x : ℝ^n) :
    weakDivergencePairingDensity v ψ x =
      ∑ i : Fin n, v x i * (∂[i] ψ) x := by
  calc
    weakDivergencePairingDensity v ψ x =
        (fderiv ℝ ψ x) (v x) := by
      simp [weakDivergencePairingDensity]
    _ = ∑ i : Fin n, (∂[i] ψ) x * v x i :=
      PDE.fderiv_apply_eq_sum_partialDeriv_mul ψ x (v x)
    _ = ∑ i : Fin n, v x i * (∂[i] ψ) x := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact mul_comm _ _

/-- Positive weak pairing `∫ v · ∇ψ` with a scalar test function.
For locally integrable `v` and smooth compactly supported `ψ`, this is the distributional
action of `-div v`, rather than `div v`. The zero-divergence condition is unaffected. -/
noncomputable def weakDivergencePairing {n : ℕ}
    (v : ℝ^n → ℝ^n) (ψ : ℝ^n → ℝ) : ℝ :=
  ∫ x : ℝ^n, weakDivergencePairingDensity v ψ x

/-- Distributional incompressibility of a spatial vector field.

The integrability clause is explicit because Lean's integral is totalized. For every smooth
compactly supported scalar test `ψ`, this is the identity `∫ v · ∇ψ = 0`, equivalent to
`div v = 0` in distributions. -/
def DistributionallyDivergenceFree {n : ℕ} (v : ℝ^n → ℝ^n) : Prop :=
  ∀ ψ : ℝ^n → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) ψ →
    HasCompactSupport ψ →
      Integrable (weakDivergencePairingDensity v ψ) ∧
      weakDivergencePairing v ψ = 0

/-- The density in every admissible weak divergence pairing is integrable. -/
theorem DistributionallyDivergenceFree.weakDivergencePairingDensity_integrable
    {n : ℕ} {v : ℝ^n → ℝ^n} (hv : DistributionallyDivergenceFree v)
    (ψ : ℝ^n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψcompact : HasCompactSupport ψ) :
    Integrable (weakDivergencePairingDensity v ψ) :=
  (hv ψ hψ hψcompact).1

/-- Every admissible weak divergence pairing of a distributionally divergence-free field
vanishes. -/
theorem DistributionallyDivergenceFree.weakDivergencePairing_eq_zero
    {n : ℕ} {v : ℝ^n → ℝ^n} (hv : DistributionallyDivergenceFree v)
    (ψ : ℝ^n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψcompact : HasCompactSupport ψ) :
    weakDivergencePairing v ψ = 0 :=
  (hv ψ hψ hψcompact).2

/-- The zero spatial vector field is distributionally divergence-free. -/
theorem distributionallyDivergenceFree_zero (n : ℕ) :
    DistributionallyDivergenceFree (fun _ : ℝ^n ↦ 0) := by
  intro ψ _hψ _hψcompact
  constructor
  · have hdensity :
        weakDivergencePairingDensity (fun _ : ℝ^n ↦ 0) ψ = 0 := by
      funext x
      simp [weakDivergencePairingDensity]
    rw [hdensity]
    exact MeasureTheory.integrable_zero (ℝ^n) ℝ MeasureTheory.volume
  · rw [weakDivergencePairing]
    apply integral_eq_zero_of_ae
    filter_upwards with x
    simp [weakDivergencePairingDensity]

/-- Distributional incompressibility is preserved by sums. -/
theorem DistributionallyDivergenceFree.add {n : ℕ} {u v : ℝ^n → ℝ^n}
    (hu : DistributionallyDivergenceFree u) (hv : DistributionallyDivergenceFree v) :
    DistributionallyDivergenceFree (u + v) := by
  intro ψ hψ hψc
  obtain ⟨hui, hu0⟩ := hu ψ hψ hψc
  obtain ⟨hvi, hv0⟩ := hv ψ hψ hψc
  have hdens : weakDivergencePairingDensity (u + v) ψ =
      fun x ↦ weakDivergencePairingDensity u ψ x + weakDivergencePairingDensity v ψ x := by
    funext x
    simp only [weakDivergencePairingDensity, Pi.add_apply, inner_add_left]
  refine ⟨hdens ▸ hui.add hvi, ?_⟩
  rw [weakDivergencePairing] at hu0 hv0 ⊢
  rw [hdens, integral_add hui hvi, hu0, hv0, add_zero]

/-- A `C¹` pointwise divergence-free spatial field is distributionally divergence-free. -/
theorem SpatialFieldDivergenceFree.distributionallyDivergenceFree
    {n : ℕ} {v : ℝ^n → ℝ^n}
    (hdiv : SpatialFieldDivergenceFree v)
    (hv : ContDiff ℝ 1 v) :
    DistributionallyDivergenceFree v := by
  intro ψ hψ hψcompact
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hv1 (i : Fin n) : ContDiff ℝ 1 (fun x ↦ v x i) := (contDiff_piLp (p := (2 : ENNReal))).1 hv i
  have htestIntegrable (i : Fin n) : Integrable (fun x ↦ v x i * (∂[i] ψ) x) :=
    ((hv1 i).continuous.mul (hψ1.continuous_partialDeriv i)).integrable_of_hasCompactSupport
      (hψcompact.partialDeriv i).mul_left
  have hdivIntegrable (i : Fin n) : Integrable (fun x ↦ (∂[i] (fun y ↦ v y i)) x * ψ x) :=
    (((hv1 i).continuous_partialDeriv i).mul hψ.continuous).integrable_of_hasCompactSupport
      hψcompact.mul_left
  refine ⟨(integrable_finsetSum Finset.univ fun i _ ↦ htestIntegrable i).congr
    (.of_forall fun x ↦ (weakDivergencePairingDensity_eq_sum v ψ x).symm), ?_⟩
  have hparts (i : Fin n) :
      ∫ x, v x i * (∂[i] ψ) x = -∫ x, (∂[i] (fun y ↦ v y i)) x * ψ x := by
    have h := PDE.Analysis.integral_mul_partialDeriv_eq_neg i hψ1 (hv1 i) hψcompact
    simp only [mul_comm (ψ _)] at h
    simp only [mul_comm (v _ i)]
    linarith
  rw [weakDivergencePairing]
  simp_rw [weakDivergencePairingDensity_eq_sum]
  rw [integral_finsetSum Finset.univ fun i _ ↦ htestIntegrable i]
  simp_rw [hparts]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum Finset.univ fun i _ ↦ hdivIntegrable i,
    neg_eq_zero]
  refine integral_eq_zero_of_ae (.of_forall fun x ↦ ?_)
  beta_reduce
  rw [Pi.zero_apply, ← Finset.sum_mul, ← spatialFieldDivergence_apply, hdiv x, zero_mul]

end IncompressibleFlow
