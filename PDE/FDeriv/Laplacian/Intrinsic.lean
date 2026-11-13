/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Laplacian
public import PDE.FDeriv.PartialDeriv

/-!
# Coordinate operations on Mathlib's Laplacian

Coordinate partials commute with `Δ` at a C³ point. Projection of a vector
Laplacian equals the Laplacian of the projected component at a C² point.
These statements concern Mathlib's intrinsic `Δ`, so callers need no conversion
to LeanPDE's coordinate Laplacian.

The proofs use the directional commutator of `PDE.Analysis.Calculus.Laplacian` and Mathlib's
theorem for
composition with continuous linear maps. The component theorem applies to
finite products with any `ℓᵖ` norm, in particular Euclidean vector targets.
-/

@[expose] public noncomputable section

open PDE (partialDeriv)
open scoped ENNReal Laplacian

namespace InnerProductSpace

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {f : ℝ^n → F} {x : ℝ^n}

/-- A coordinate partial commutes with Mathlib's Laplacian at a C³ point. -/
theorem partialDeriv_laplacian_at (i : Fin n) (hf : ContDiffAt ℝ 3 f x) :
    (∂[i] (Δ f)) x = Δ (∂[i] f) x :=
  (hf.laplacian_fderiv_apply (EuclideanSpace.single i 1)).symm

/-- Function-valued commutation of coordinate partials and Mathlib's Laplacian. -/
theorem partialDeriv_laplacian (i : Fin n) (hf : ContDiff ℝ 3 f) :
    ∂[i] (Δ f) = Δ (∂[i] f) :=
  funext fun _ ↦ partialDeriv_laplacian_at i hf.contDiffAt

/-- Coordinate partials commute with Mathlib's Laplacian throughout an open C³ domain. -/
theorem partialDeriv_laplacian_eqOn (i : Fin n) {s : Set (ℝ^n)}
    (hf : ContDiffOn ℝ 3 f s) (hs : IsOpen s) :
    Set.EqOn (∂[i] (Δ f)) (Δ (∂[i] f)) s :=
  fun _ hx ↦ partialDeriv_laplacian_at i (hf.contDiffAt (hs.mem_nhds hx))

end InnerProductSpace

/-- Each component of a vector Laplacian is the scalar or vector component's Laplacian.
The finite product may carry any `ℓᵖ` norm with `p ≥ 1`, including the Euclidean norm. -/
theorem ContDiffAt.laplacian_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] {F : ι → Type*}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : E → PiLp p F} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (i : ι) :
    (Δ f x) i = Δ (fun y ↦ f y i) x :=
  (hf.laplacian_CLM_comp_left (l := PiLp.proj p F i)).symm
