/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.VorticityEvolution
public import PDE.Fluid.Incompressible.Vorticity
import PDE.FDeriv.Calculus

/-!
# Locality of incompressible-flow differential operators

The material derivative, spatial Laplacian, divergence, and vorticity equation depend only
on the input fields in a neighborhood of the evaluation point. These identities allow
local classical solutions to use differential calculations stated for global fields.
They do not require regularity: Mathlib's total derivatives respect equality of germs.
-/

@[expose] public section

open Filter
open scoped Topology

namespace IncompressibleFlow

/-- Locally equal velocity and transported fields have locally equal material derivatives. -/
theorem materialDerivative_eventuallyEq
    {n : ℕ} {u v u' v' : ℝ^(n + 1) → ℝ^n} {x : ℝ^(n + 1)}
    (hu : u =ᶠ[𝓝 x] u') (hv : v =ᶠ[𝓝 x] v') :
    materialDerivative n u v =ᶠ[𝓝 x] materialDerivative n u' v' := by
  have hd : ∀ᶠ y in 𝓝 x, ∀ a : Fin (n + 1), ∀ i : Fin n,
      (∂[a] (fun z ↦ v z i)) y = (∂[a] (fun z ↦ v' z i)) y := by
    simp only [eventually_all]
    intro a i
    exact (hv.fun_comp (fun z ↦ z i)).partialDeriv a
  filter_upwards [hu, hd] with y hy hdy
  ext i
  simp only [materialDerivative_apply, hdy, hy]

/-- The scalar material derivative depends only on the velocity and scalar germs. -/
theorem scalarMaterialDerivative_eventuallyEq
    {n : ℕ} {u u' : ℝ^(n + 1) → ℝ^n} {f g : ℝ^(n + 1) → ℝ}
    {x : ℝ^(n + 1)} (hu : u =ᶠ[𝓝 x] u') (hf : f =ᶠ[𝓝 x] g) :
    scalarMaterialDerivative n u f =ᶠ[𝓝 x] scalarMaterialDerivative n u' g := by
  have hd : ∀ᶠ y in 𝓝 x, ∀ a : Fin (n + 1),
      (∂[a] f) y = (∂[a] g) y := by
    simp only [eventually_all]
    exact hf.partialDeriv
  filter_upwards [hu, hd] with y hy hdy
  simp only [scalarMaterialDerivative_apply, hdy, hy]

/-- The spatial Laplacian depends only on the scalar germ. -/
theorem spatialLaplacian_eventuallyEq
    {n : ℕ} {f g : ℝ^(n + 1) → ℝ} {x : ℝ^(n + 1)} (hf : f =ᶠ[𝓝 x] g) :
    spatialLaplacian n f =ᶠ[𝓝 x] spatialLaplacian n g := by
  have hd : ∀ᶠ y in 𝓝 x, ∀ i : Fin n,
      (∂[i.succ] (∂[i.succ] f)) y =
        (∂[i.succ] (∂[i.succ] g)) y := by
    simp only [eventually_all]
    intro i
    exact (hf.partialDeriv i.succ).partialDeriv i.succ
  filter_upwards [hd] with y hy
  simp only [spatialLaplacian_apply, hy]

/-- The spatial vector Laplacian depends only on the vector-field germ. -/
theorem spatialVectorLaplacian_eventuallyEq
    {n : ℕ} {u v : ℝ^(n + 1) → ℝ^n} {x : ℝ^(n + 1)} (hu : u =ᶠ[𝓝 x] v) :
    spatialVectorLaplacian n u =ᶠ[𝓝 x] spatialVectorLaplacian n v := by
  have hd : ∀ᶠ y in 𝓝 x, ∀ i : Fin n,
      spatialLaplacian n (fun z ↦ u z i) y = spatialLaplacian n (fun z ↦ v z i) y := by
    simp only [eventually_all]
    intro i
    exact spatialLaplacian_eventuallyEq (hu.fun_comp (fun z ↦ z i))
  filter_upwards [hd] with y hy
  ext i
  simp only [spatialVectorLaplacian_apply, hy]

/-- Spatial divergence is unchanged by replacement with the same local field. -/
theorem spatialDivergence_eventuallyEq
    {n : ℕ} {u v : ℝ^(n + 1) → ℝ^n} {x : ℝ^(n + 1)} (hu : u =ᶠ[𝓝 x] v) :
    spatialDivergence n u =ᶠ[𝓝 x] spatialDivergence n v := by
  have hd : ∀ᶠ y in 𝓝 x, ∀ i : Fin n,
      (∂[i.succ] (fun z ↦ u z i)) y = (∂[i.succ] (fun z ↦ v z i)) y := by
    simp only [eventually_all]
    intro i
    exact (hu.fun_comp (fun z ↦ z i)).partialDeriv i.succ
  filter_upwards [hd] with y hy
  simp only [spatialDivergence_apply, hy]

/-- The divergence of a spatial field depends only on its spatial germ. -/
theorem spatialFieldDivergence_eventuallyEq
    {n : ℕ} {u v : ℝ^n → ℝ^n} {x : ℝ^n} (hu : u =ᶠ[𝓝 x] v) :
    spatialFieldDivergence u =ᶠ[𝓝 x] spatialFieldDivergence v := by
  have hd : ∀ᶠ y in 𝓝 x, ∀ i : Fin n,
      (∂[i] (fun z ↦ u z i)) y = (∂[i] (fun z ↦ v z i)) y := by
    simp only [eventually_all]
    intro i
    exact (hu.fun_comp (fun z ↦ z i)).partialDeriv i
  filter_upwards [hd] with y hy
  simp only [spatialFieldDivergence_apply, hy]

/-- The convective derivative depends only on the two vector-field germs. -/
theorem convectiveDerivative_eventuallyEq
    {n : ℕ} {u v u' v' : ℝ^(n + 1) → ℝ^n} {x : ℝ^(n + 1)}
    (hu : u =ᶠ[𝓝 x] u') (hv : v =ᶠ[𝓝 x] v') :
    convectiveDerivative n u v =ᶠ[𝓝 x] convectiveDerivative n u' v' := by
  have hd : ∀ᶠ y in 𝓝 x, ∀ a i : Fin n,
      (∂[a.succ] (fun z ↦ v z i)) y =
        (∂[a.succ] (fun z ↦ v' z i)) y := by
    simp only [eventually_all]
    intro a i
    exact (hv.fun_comp (fun z ↦ z i)).partialDeriv a.succ
  filter_upwards [hu, hd] with y hy hdy
  ext i
  simp only [convectiveDerivative_apply, hdy, hy]

/-- The vector vorticity equation is local in both velocity and vorticity. -/
theorem vorticityTransportResidual_eventuallyEq
    {n : ℕ} (ν : ℝ) {u ω v η : ℝ^(n + 1) → ℝ^n} {x : ℝ^(n + 1)}
    (hu : u =ᶠ[𝓝 x] v) (hω : ω =ᶠ[𝓝 x] η) :
    vorticityTransportResidual n ν u ω =ᶠ[𝓝 x] vorticityTransportResidual n ν v η := by
  filter_upwards [materialDerivative_eventuallyEq hu hω,
    convectiveDerivative_eventuallyEq hω hu,
    spatialVectorLaplacian_eventuallyEq hω] with y hmat hconv hlap
  simp only [vorticityTransportResidual, vorticityStretching, hmat, hconv, hlap]

/-- The Cartesian spatial curl depends only on the spatial velocity germ. -/
theorem spatialCurl_eventuallyEq
    {u v : ℝ^3 → ℝ^3} {x : ℝ^3} (hu : u =ᶠ[𝓝 x] v) :
    spatialCurl u =ᶠ[𝓝 x] spatialCurl v := by
  have hd : ∀ᶠ y in 𝓝 x, ∀ a i : Fin 3,
      (∂[a] (fun z ↦ u z i)) y = (∂[a] (fun z ↦ v z i)) y := by
    simp only [eventually_all]
    intro a i
    exact (hu.fun_comp (fun z ↦ z i)).partialDeriv a
  filter_upwards [hd] with y hy
  ext i
  fin_cases i
  · change spatialCurl u y 0 = spatialCurl v y 0
    simp only [spatialCurl_apply_zero, hy]
  · change spatialCurl u y 1 = spatialCurl v y 1
    simp only [spatialCurl_apply_one, hy]
  · change spatialCurl u y 2 = spatialCurl v y 2
    simp only [spatialCurl_apply_two, hy]

end IncompressibleFlow
