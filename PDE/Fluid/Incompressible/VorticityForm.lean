/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.VorticityEvolution
public import PDE.Fluid.Incompressible.Vorticity
import PDE.FDeriv.Calculus
import PDE.FDeriv.SpaceTime
import PDE.Fluid.Incompressible.Locality
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The vorticity two-form and the spacetime curl

In arbitrary spatial dimension the vorticity of a velocity field `u : ℝ^(n + 1) → ℝ^n`
is most naturally the antisymmetric two-tensor

```text
Omega_ij = partial_i u_j - partial_j u_i,
```

and its transport-diffusion equation is

```text
D_t Omega_ij
  + sum_k (partial_i u_k Omega_kj + partial_j u_k Omega_ik)
  = nu Delta Omega_ij.
```

The deformation terms are the coordinate expression of the Lie derivative of a two-form
(Arnold–Khesin, *Topological Methods in Hydrodynamics*). Here `nu` is only a real
parameter; at `nu = 0` this is the Euler vorticity equation, so the definitions belong to the
shared incompressible layer and do not depend on the viscosity-specific modules.

In three dimensions the two-form is the familiar vector vorticity read through the spatial
curl of each time slice, `spacetimeSpatialCurl`. Componentwise identities relate the
two-form residual to the vector residual `vorticityTransportResidual`, including the exact
`(div u)ω` correction that incompressibility removes. The pressure reconstruction that uses
these identities together with the viscous term is in
`PDE.Fluid.NavierStokes.PressureFromVorticity`.

## Main declarations

* `vorticityFormTransportResidual`: the transport-diffusion residual of the vorticity two-form
  `spatialVorticityForm` of `Vorticity` in any spatial dimension, with the locality lemmas
  `spatialVorticityForm_eventuallyEq` and `vorticityFormTransportResidual_eventuallyEq`.
* `spacetimeSpatialCurl`: the spatial curl of every fixed-time slice as a spacetime field,
  with `spacetimeSpatialCurl_apply_zero`, `spacetimeSpatialCurl_apply_one`, and
  `spacetimeSpatialCurl_apply_two` identifying its components with two-form entries.
* `vorticityFormTransportResidual_apply_one_two`,
  `vorticityFormTransportResidual_apply_two_zero`,
  `vorticityFormTransportResidual_apply_zero_one`: each cyclic two-form component equals the
  corresponding vector residual plus `(div u)ω`.
* `vorticityTransportResidual_eq_zero_of_vorticityForm`: under incompressibility, the
  two-form equation implies the vector-vorticity equation.

## References

* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001, Chapter 1, for the three-dimensional vorticity
  equation `Dₜω = (ω · ∇)u + νΔω`.
  <https://doi.org/10.1017/CBO9780511613203>
* V. I. Arnold and B. A. Khesin, *Topological Methods in Hydrodynamics*, Applied Mathematical
  Sciences, Springer, 1998.
  <https://doi.org/10.1007/b97593>
-/

@[expose] public section

open PDE (time)

namespace IncompressibleFlow

open EuclideanSpace
open Filter
open scoped Topology

set_option linter.missingDocs true

noncomputable section

/-- Transport-diffusion residual of the spatial vorticity two-form.

The deformation terms are the coordinate expression of the Lie derivative of
a two-form.  At zero viscosity this is the Euler vorticity equation. -/
def vorticityFormTransportResidual (n : ℕ) (ν : ℝ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) : SpatialMatrix n :=
  WithLp.toLp 2 fun ij ↦
    scalarMaterialDerivative n u
        (fun y ↦ spatialVorticityForm n u y ij) x +
      ∑ k : Fin n,
        ((∂[ij.1.succ] (fun y ↦ u y k)) x *
            spatialVorticityForm n u x (k, ij.2) +
          (∂[ij.2.succ] (fun y ↦ u y k)) x *
            spatialVorticityForm n u x (ij.1, k)) -
      ν * spatialLaplacian n
        (fun y ↦ spatialVorticityForm n u y ij) x

/-- Coordinate formula for the vorticity-form transport residual. -/
@[simp]
theorem vorticityFormTransportResidual_apply (n : ℕ) (ν : ℝ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) (i j : Fin n) :
    vorticityFormTransportResidual n ν u x (i, j) =
      scalarMaterialDerivative n u
          (fun y ↦ spatialVorticityForm n u y (i, j)) x +
        ∑ k : Fin n,
          ((∂[i.succ] (fun y ↦ u y k)) x *
              spatialVorticityForm n u x (k, j) +
            (∂[j.succ] (fun y ↦ u y k)) x *
              spatialVorticityForm n u x (i, k)) -
        ν * spatialLaplacian n
          (fun y ↦ spatialVorticityForm n u y (i, j)) x := by
  simp [vorticityFormTransportResidual, PiLp.toLp_apply]

/-- The antisymmetric velocity derivative depends only on the velocity germ. -/
theorem spatialVorticityForm_eventuallyEq
    {n : ℕ} {u v : ℝ^(n + 1) → ℝ^n} {x : ℝ^(n + 1)} (hu : u =ᶠ[𝓝 x] v) :
    spatialVorticityForm n u =ᶠ[𝓝 x] spatialVorticityForm n v := by
  have hd : ∀ᶠ y in 𝓝 x, ∀ a i : Fin n,
      (∂[a.succ] (fun z ↦ u z i)) y = (∂[a.succ] (fun z ↦ v z i)) y := by
    simp only [eventually_all]
    intro a i
    exact (hu.fun_comp (fun z ↦ z i)).partialDeriv a.succ
  filter_upwards [hd] with y hy
  ext ij
  rcases ij with ⟨i, j⟩
  change spatialVorticityForm n u y (i, j) = spatialVorticityForm n v y (i, j)
  simp only [spatialVorticityForm_apply, hy]

/-- The vorticity two-form transport-diffusion residual depends only on the velocity germ. -/
theorem vorticityFormTransportResidual_eventuallyEq
    {n : ℕ} (ν : ℝ) {u v : ℝ^(n + 1) → ℝ^n} {x : ℝ^(n + 1)}
    (hu : u =ᶠ[𝓝 x] v) :
    vorticityFormTransportResidual n ν u =ᶠ[𝓝 x] vorticityFormTransportResidual n ν v := by
  have hf := spatialVorticityForm_eventuallyEq hu
  have hm : ∀ᶠ y in 𝓝 x, ∀ ij : Fin n × Fin n,
      scalarMaterialDerivative n u (fun z ↦ spatialVorticityForm n u z ij) y =
        scalarMaterialDerivative n v (fun z ↦ spatialVorticityForm n v z ij) y := by
    simp only [eventually_all]
    intro ij
    exact scalarMaterialDerivative_eventuallyEq hu (hf.fun_comp (fun z ↦ z ij))
  have hl : ∀ᶠ y in 𝓝 x, ∀ ij : Fin n × Fin n,
      spatialLaplacian n (fun z ↦ spatialVorticityForm n u z ij) y =
        spatialLaplacian n (fun z ↦ spatialVorticityForm n v z ij) y := by
    simp only [eventually_all]
    intro ij
    exact spatialLaplacian_eventuallyEq (hf.fun_comp (fun z ↦ z ij))
  have hd : ∀ᶠ y in 𝓝 x, ∀ a i : Fin n,
      (∂[a.succ] (fun z ↦ u z i)) y = (∂[a.succ] (fun z ↦ v z i)) y := by
    simp only [eventually_all]
    intro a i
    exact (hu.fun_comp (fun z ↦ z i)).partialDeriv a.succ
  filter_upwards [hf, hm, hl, hd] with y hy hmy hly hdy
  ext ij
  rcases ij with ⟨i, j⟩
  change vorticityFormTransportResidual n ν u y (i, j) =
    vorticityFormTransportResidual n ν v y (i, j)
  simp only [vorticityFormTransportResidual_apply, hmy, hly, hdy, hy]


/-! ## Three-dimensional vector vorticity -/

/-- The spatial curl of each fixed-time slice, assembled as a spacetime
vector field.  This is the general, non-axisymmetric wrapper around
`spatialCurl`. -/
def spacetimeSpatialCurl (u : ℝ^4 → ℝ^3) : ℝ^4 → ℝ^3 :=
  fun xt ↦ spatialCurl (velocitySlice u (time xt)) (PDE.Common.spatialPart xt)

/-- At a point `(t, x)`, `spacetimeSpatialCurl` is the ordinary curl of the velocity slice at
time `t`. -/
@[simp]
theorem spacetimeSpatialCurl_timeSpaceCons (u : ℝ^4 → ℝ^3)
    (t : ℝ) (x : ℝ^3) :
    spacetimeSpatialCurl u (PDE.Common.timeSpaceCons t x) =
      spatialCurl (velocitySlice u t) x := by
  simp [spacetimeSpatialCurl, time]

/-- Taking the curl on time slices preserves equality of spacetime germs. -/
theorem spacetimeSpatialCurl_eventuallyEq
    {u v : ℝ^4 → ℝ^3} {xt : ℝ^4} (hu : u =ᶠ[𝓝 xt] v) :
    spacetimeSpatialCurl u =ᶠ[𝓝 xt] spacetimeSpatialCurl v := by
  filter_upwards [hu.eventuallyEq_nhds] with y hy
  have hslice : velocitySlice u (time y) =ᶠ[𝓝 (PDE.Common.spatialPart y)]
      velocitySlice v (time y) := by
    apply hy.comp_tendsto
    have hmap : ContinuousAt (PDE.Common.timeSpaceCons (time y))
        (PDE.Common.spatialPart y) :=
      (PDE.Common.contDiff_timeSpaceCons_spatial 3 (time y) (m := 1)).continuous.continuousAt
    simpa only [ContinuousAt, time, PDE.Common.timeSpaceCons_spatialPart] using hmap
  exact (spatialCurl_eventuallyEq hslice).eq_of_nhds

/-- The first curl component is the `(1,2)` component of the spatial
vorticity two-form. -/
theorem spacetimeSpatialCurl_apply_zero
    (u : ℝ^4 → ℝ^3) (hu : ContDiff ℝ 1 u) (xt : ℝ^4) :
    spacetimeSpatialCurl u xt 0 = spatialVorticityForm 3 u xt (1, 2) := by
  rw [← PDE.Common.timeSpaceCons_spatialPart xt]
  simp only [spacetimeSpatialCurl_timeSpaceCons, spatialCurl_apply_zero,
    spatialVorticityForm_apply, velocitySlice]
  rw [PDE.partialDeriv_timeSpaceCons_spatial (1 : Fin 3) (fun y ↦ u y 2)
      (xt 0) (PDE.Common.spatialPart xt)
      ((contDiff_euclidean.1 hu 2).differentiable (by norm_num)).differentiableAt,
    PDE.partialDeriv_timeSpaceCons_spatial (2 : Fin 3) (fun y ↦ u y 1)
      (xt 0) (PDE.Common.spatialPart xt)
      ((contDiff_euclidean.1 hu 1).differentiable (by norm_num)).differentiableAt]

/-- The second curl component is the `(2,0)` component of the spatial
vorticity two-form. -/
theorem spacetimeSpatialCurl_apply_one
    (u : ℝ^4 → ℝ^3) (hu : ContDiff ℝ 1 u) (xt : ℝ^4) :
    spacetimeSpatialCurl u xt 1 = spatialVorticityForm 3 u xt (2, 0) := by
  rw [← PDE.Common.timeSpaceCons_spatialPart xt]
  simp only [spacetimeSpatialCurl_timeSpaceCons, spatialCurl_apply_one,
    spatialVorticityForm_apply, velocitySlice]
  rw [PDE.partialDeriv_timeSpaceCons_spatial (2 : Fin 3) (fun y ↦ u y 0)
      (xt 0) (PDE.Common.spatialPart xt)
      ((contDiff_euclidean.1 hu 0).differentiable (by norm_num)).differentiableAt,
    PDE.partialDeriv_timeSpaceCons_spatial (0 : Fin 3) (fun y ↦ u y 2)
      (xt 0) (PDE.Common.spatialPart xt)
      ((contDiff_euclidean.1 hu 2).differentiable (by norm_num)).differentiableAt]

/-- The third curl component is the `(0,1)` component of the spatial
vorticity two-form. -/
theorem spacetimeSpatialCurl_apply_two
    (u : ℝ^4 → ℝ^3) (hu : ContDiff ℝ 1 u) (xt : ℝ^4) :
    spacetimeSpatialCurl u xt 2 = spatialVorticityForm 3 u xt (0, 1) := by
  rw [← PDE.Common.timeSpaceCons_spatialPart xt]
  simp only [spacetimeSpatialCurl_timeSpaceCons, spatialCurl_apply_two,
    spatialVorticityForm_apply, velocitySlice]
  rw [PDE.partialDeriv_timeSpaceCons_spatial (0 : Fin 3) (fun y ↦ u y 1)
      (xt 0) (PDE.Common.spatialPart xt)
      ((contDiff_euclidean.1 hu 1).differentiable (by norm_num)).differentiableAt,
    PDE.partialDeriv_timeSpaceCons_spatial (1 : Fin 3) (fun y ↦ u y 0)
      (xt 0) (PDE.Common.spatialPart xt)
      ((contDiff_euclidean.1 hu 0).differentiable (by norm_num)).differentiableAt]

/-- The `(1,2)` two-form residual equals the first vector-vorticity residual
plus the divergence correction. -/
theorem vorticityFormTransportResidual_apply_one_two
    (ν : ℝ) (u : ℝ^4 → ℝ^3) (hu : ContDiff ℝ 1 u) (xt : ℝ^4) :
    vorticityFormTransportResidual 3 ν u xt (1, 2) =
      vorticityTransportResidual 3 ν u (spacetimeSpatialCurl u) xt 0 +
        spatialDivergence 3 u xt * spacetimeSpatialCurl u xt 0 := by
  have hω0 : (fun y ↦ spacetimeSpatialCurl u y 0) =
      fun y ↦ spatialVorticityForm 3 u y (1, 2) := by
    funext y
    exact spacetimeSpatialCurl_apply_zero u hu y
  have hω1 : (fun y ↦ spacetimeSpatialCurl u y 1) =
      fun y ↦ spatialVorticityForm 3 u y (2, 0) := by
    funext y
    exact spacetimeSpatialCurl_apply_one u hu y
  have hω2 : (fun y ↦ spacetimeSpatialCurl u y 2) =
      fun y ↦ spatialVorticityForm 3 u y (0, 1) := by
    funext y
    exact spacetimeSpatialCurl_apply_two u hu y
  simp only [vorticityFormTransportResidual_apply,
    scalarMaterialDerivative_apply, vorticityTransportResidual,
    vorticityStretching, materialDerivative_apply,
    convectiveDerivative_apply, spatialVectorLaplacian_apply,
    spatialDivergence_apply, PiLp.sub_apply, PiLp.smul_apply,
    Fin.sum_univ_three, smul_eq_mul]
  rw [hω0, congrFun hω0 xt, congrFun hω1 xt, congrFun hω2 xt]
  simp only [spatialVorticityForm_apply]
  ring

/-- The `(2,0)` two-form residual equals the second vector-vorticity residual
plus the divergence correction. -/
theorem vorticityFormTransportResidual_apply_two_zero
    (ν : ℝ) (u : ℝ^4 → ℝ^3) (hu : ContDiff ℝ 1 u) (xt : ℝ^4) :
    vorticityFormTransportResidual 3 ν u xt (2, 0) =
      vorticityTransportResidual 3 ν u (spacetimeSpatialCurl u) xt 1 +
        spatialDivergence 3 u xt * spacetimeSpatialCurl u xt 1 := by
  have hω0 : (fun y ↦ spacetimeSpatialCurl u y 0) =
      fun y ↦ spatialVorticityForm 3 u y (1, 2) := by
    funext y
    exact spacetimeSpatialCurl_apply_zero u hu y
  have hω1 : (fun y ↦ spacetimeSpatialCurl u y 1) =
      fun y ↦ spatialVorticityForm 3 u y (2, 0) := by
    funext y
    exact spacetimeSpatialCurl_apply_one u hu y
  have hω2 : (fun y ↦ spacetimeSpatialCurl u y 2) =
      fun y ↦ spatialVorticityForm 3 u y (0, 1) := by
    funext y
    exact spacetimeSpatialCurl_apply_two u hu y
  simp only [vorticityFormTransportResidual_apply,
    scalarMaterialDerivative_apply, vorticityTransportResidual,
    vorticityStretching, materialDerivative_apply,
    convectiveDerivative_apply, spatialVectorLaplacian_apply,
    spatialDivergence_apply, PiLp.sub_apply, PiLp.smul_apply,
    Fin.sum_univ_three, smul_eq_mul]
  rw [hω1, congrFun hω0 xt, congrFun hω1 xt, congrFun hω2 xt]
  simp only [spatialVorticityForm_apply]
  ring

/-- The `(0,1)` two-form residual equals the third vector-vorticity residual
plus the divergence correction. -/
theorem vorticityFormTransportResidual_apply_zero_one
    (ν : ℝ) (u : ℝ^4 → ℝ^3) (hu : ContDiff ℝ 1 u) (xt : ℝ^4) :
    vorticityFormTransportResidual 3 ν u xt (0, 1) =
      vorticityTransportResidual 3 ν u (spacetimeSpatialCurl u) xt 2 +
        spatialDivergence 3 u xt * spacetimeSpatialCurl u xt 2 := by
  have hω0 : (fun y ↦ spacetimeSpatialCurl u y 0) =
      fun y ↦ spatialVorticityForm 3 u y (1, 2) := by
    funext y
    exact spacetimeSpatialCurl_apply_zero u hu y
  have hω1 : (fun y ↦ spacetimeSpatialCurl u y 1) =
      fun y ↦ spatialVorticityForm 3 u y (2, 0) := by
    funext y
    exact spacetimeSpatialCurl_apply_one u hu y
  have hω2 : (fun y ↦ spacetimeSpatialCurl u y 2) =
      fun y ↦ spatialVorticityForm 3 u y (0, 1) := by
    funext y
    exact spacetimeSpatialCurl_apply_two u hu y
  simp only [vorticityFormTransportResidual_apply,
    scalarMaterialDerivative_apply, vorticityTransportResidual,
    vorticityStretching, materialDerivative_apply,
    convectiveDerivative_apply, spatialVectorLaplacian_apply,
    spatialDivergence_apply, PiLp.sub_apply, PiLp.smul_apply,
    Fin.sum_univ_three, smul_eq_mul]
  rw [hω2, congrFun hω0 xt, congrFun hω1 xt, congrFun hω2 xt]
  simp only [spatialVorticityForm_apply]
  ring

/-- Under incompressibility, vanishing of the intrinsic two-form residual
implies vanishing of the familiar three-dimensional vector residual. -/
theorem vorticityTransportResidual_eq_zero_of_vorticityForm
    (ν : ℝ) (u : ℝ^4 → ℝ^3) (hu : ContDiff ℝ 1 u) (xt : ℝ^4)
    (hdiv : DivergenceFreeAt u xt)
    (hvorticity : vorticityFormTransportResidual 3 ν u xt = 0) :
    vorticityTransportResidual 3 ν u (spacetimeSpatialCurl u) xt = 0 := by
  have hdiv' : spatialDivergence 3 u xt = 0 := hdiv
  have hform0 := congrArg (fun Ω : SpatialMatrix 3 ↦ Ω (1, 2)) hvorticity
  have hform1 := congrArg (fun Ω : SpatialMatrix 3 ↦ Ω (2, 0)) hvorticity
  have hform2 := congrArg (fun Ω : SpatialMatrix 3 ↦ Ω (0, 1)) hvorticity
  rw [vorticityFormTransportResidual_apply_one_two ν u hu xt,
    hdiv', zero_mul, add_zero] at hform0
  rw [vorticityFormTransportResidual_apply_two_zero ν u hu xt,
    hdiv', zero_mul, add_zero] at hform1
  rw [vorticityFormTransportResidual_apply_zero_one ν u hu xt,
    hdiv', zero_mul, add_zero] at hform2
  ext i
  fin_cases i
  · simpa using hform0
  · simpa using hform1
  · simpa using hform2


end

end IncompressibleFlow
