/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.ModelHierarchy
public import PDE.Fluid.Incompressible.Solenoidal
public import PDE.Analysis.Calculus.Potential.Convex

/-!
# Pressure reconstruction from the momentum residual

The abstract pressure recovery of `Solenoidal` applies to the Euler, Stokes, and
Navier–Stokes momentum residuals.

Let `div : H →L[ℝ] K` be a weak divergence operator between real Hilbert
spaces. If a pressure-free momentum residual `r : H` is orthogonal to every
solenoidal test vector, closed-range factorization constructs a canonical
pressure `p` in `range div` such that

```text
r - div.adjoint p = 0.
```

The sign records the weak identity `grad p = -div.adjoint p`. Requiring the
pressure to lie in `range div` removes the freedom to add an element of
`ker div.adjoint` and gives uniqueness. This kernel need not consist only of
constant pressures for an abstract operator. The pointwise results at the end
state the pressure gradient identities for the Euler, Stokes, and
Navier–Stokes residuals.

The final section is the classical counterpart, the Poincaré lemma on an open convex spatial
domain: a differentiable vector field with symmetric Jacobian there is the gradient of a scalar
potential. Mathlib proves it for closed one-forms on convex sets
(`Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric`), and
`InnerProductSpace.exists_potential_of_fderiv_symmetric` restates it for vector fields.

## Main results

* `reconstructedPressure`, `existsUnique_pressure_weakMomentumResidual_eq_zero`:
  the abstract Hilbert-space statement. If `div` has closed range and the
  residual `r` annihilates `SolenoidalSpace div`, there is exactly one
  `p ∈ range div` with `r = div.adjoint p`.
* `exists_pressure_weakMomentumResidual_eq_zero_iff`: conversely, solvability
  with a range-normalized pressure characterizes annihilation of the solenoidal
  space.
* `eulerMomentumResidual_eq_zero_iff_spatialGradient_eq` and the Stokes and
  Navier–Stokes analogues: a vanishing pointwise residual is the same as a
  formula for `grad p` in terms of velocity and force.
* `exists_pressure_family_of_fderiv_symmetric`: a pressure on every time slice of an open
  convex domain, from the Poincaré lemma `InnerProductSpace.exists_potential_of_fderiv_symmetric`
  of `PDE.Analysis.Calculus.Potential.Convex`.
* `exists_pressure_navierStokes_momentum_equation_of_partialDeriv_comm`: a
  slice-wise Navier–Stokes pressure on an open convex spatial domain whenever
  the coordinate derivatives of `ν Δu + f - D_t u` commute.

## References

* R. Temam, *Navier–Stokes Equations: Theory and Numerical Analysis*, AMS Chelsea Publishing, 2001,
  Chapter I, for the characterization of gradients as the functionals that vanish on divergence-free
  fields.
  <https://doi.org/10.1090/chel/343>
* M. Spivak, *Calculus on Manifolds: A Modern Approach to Classical Theorems of Advanced Calculus*,
  CRC Press, 2018.
  <https://doi.org/10.1201/9780429501906>
-/

@[expose] public section

noncomputable section

open PDE (spatialGradient)
open scoped InnerProductSpace

namespace IncompressibleFlow

set_option linter.missingDocs true

section AbstractPressure

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Weak momentum residual obtained by adding the pressure force
`-div.adjoint p` to a pressure-free residual `r`. -/
def weakMomentumResidual (div : H →L[ℝ] K) (r : H) (p : K) : H :=
  r - div.adjoint p

/-- Vanishing of the weak momentum residual is the adjoint divergence
equation for pressure. -/
theorem weakMomentumResidual_eq_zero_iff
    (div : H →L[ℝ] K) (r : H) (p : K) :
    weakMomentumResidual div r p = 0 ↔ div.adjoint p = r := by
  rw [weakMomentumResidual, sub_eq_zero, eq_comm]

/-- A pressure solving the weak momentum equation forces the pressure-free
residual to vanish on every solenoidal test vector. -/
theorem inner_eq_zero_on_solenoidal_of_weakMomentumResidual_eq_zero
    (div : H →L[ℝ] K) (r : H) (p : K)
    (hresidual : weakMomentumResidual div r p = 0)
    (v : SolenoidalSpace div) :
    ⟪r, (v : H)⟫_ℝ = 0 := by
  have hadjoint : div.adjoint p = r :=
    (weakMomentumResidual_eq_zero_iff div r p).1 hresidual
  rw [← hadjoint, div.adjoint_inner_left]
  have hdiv : div (v : H) = 0 := v.property
  rw [hdiv, inner_zero_right]

/-- Canonical pressure reconstructed from a pressure-free momentum residual
that vanishes on all solenoidal test vectors. -/
def reconstructedPressure
    (div : H →L[ℝ] K) (r : H)
    (hannihilates : ∀ v : SolenoidalSpace div, ⟪r, (v : H)⟫_ℝ = 0)
    (hclosed : IsClosed (div.range : Set K)) : K :=
  recoveredPressure div (innerSL ℝ r) (by
    intro v
    simpa only [innerSL_apply_apply] using hannihilates v) hclosed

/-- The reconstructed pressure is normalized to lie in the divergence
range. -/
theorem reconstructedPressure_mem_range
    (div : H →L[ℝ] K) (r : H)
    (hannihilates : ∀ v : SolenoidalSpace div, ⟪r, (v : H)⟫_ℝ = 0)
    (hclosed : IsClosed (div.range : Set K)) :
    reconstructedPressure div r hannihilates hclosed ∈ div.range := by
  exact recoveredPressure_mem_range div (innerSL ℝ r) _ hclosed

/-- The adjoint divergence of the reconstructed pressure is the original
pressure-free momentum residual. -/
theorem adjoint_reconstructedPressure_eq
    (div : H →L[ℝ] K) (r : H)
    (hannihilates : ∀ v : SolenoidalSpace div, ⟪r, (v : H)⟫_ℝ = 0)
    (hclosed : IsClosed (div.range : Set K)) :
    div.adjoint (reconstructedPressure div r hannihilates hclosed) = r := by
  unfold reconstructedPressure
  rw [adjoint_recoveredPressure_eq]
  exact (InnerProductSpace.toDual ℝ H).symm_apply_apply r

/-- Adding the reconstructed pressure closes the weak momentum equation. -/
theorem weakMomentumResidual_reconstructedPressure_eq_zero
    (div : H →L[ℝ] K) (r : H)
    (hannihilates : ∀ v : SolenoidalSpace div, ⟪r, (v : H)⟫_ℝ = 0)
    (hclosed : IsClosed (div.range : Set K)) :
    weakMomentumResidual div r
      (reconstructedPressure div r hannihilates hclosed) = 0 := by
  rw [weakMomentumResidual_eq_zero_iff,
    adjoint_reconstructedPressure_eq]

/-- Any range-normalized pressure solving the weak momentum equation is the
canonical reconstructed pressure. -/
theorem eq_reconstructedPressure_of_weakMomentumResidual_eq_zero
    (div : H →L[ℝ] K) (r : H)
    (hannihilates : ∀ v : SolenoidalSpace div, ⟪r, (v : H)⟫_ℝ = 0)
    (hclosed : IsClosed (div.range : Set K))
    (p : K) (hp : p ∈ div.range)
    (hresidual : weakMomentumResidual div r p = 0) :
    p = reconstructedPressure div r hannihilates hclosed := by
  apply recoveredPressure_unique_of_mem_range
  · exact hp
  · intro v
    have hadjoint : div.adjoint p = r :=
      (weakMomentumResidual_eq_zero_iff div r p).1 hresidual
    calc
      ⟪p, div v⟫_ℝ = ⟪div.adjoint p, v⟫_ℝ :=
        (div.adjoint_inner_left v p).symm
      _ = ⟪r, v⟫_ℝ := congrArg (fun z : H ↦ ⟪z, v⟫_ℝ) hadjoint
      _ = innerSL ℝ r v := (innerSL_apply_apply ℝ r v).symm

/-- A pressure-free residual orthogonal to all solenoidal tests determines a
unique range-normalized pressure that closes the weak momentum equation. -/
theorem existsUnique_pressure_weakMomentumResidual_eq_zero
    (div : H →L[ℝ] K) (r : H)
    (hannihilates : ∀ v : SolenoidalSpace div, ⟪r, (v : H)⟫_ℝ = 0)
    (hclosed : IsClosed (div.range : Set K)) :
    ∃! p : K, p ∈ div.range ∧ weakMomentumResidual div r p = 0 := by
  refine ⟨reconstructedPressure div r hannihilates hclosed, ?_, ?_⟩
  · exact ⟨reconstructedPressure_mem_range div r hannihilates hclosed,
      weakMomentumResidual_reconstructedPressure_eq_zero
        div r hannihilates hclosed⟩
  · rintro p ⟨hp, hresidual⟩
    exact eq_reconstructedPressure_of_weakMomentumResidual_eq_zero
      div r hannihilates hclosed p hp hresidual

/-- A range-normalized pressure closes the weak momentum equation exactly
when the pressure-free residual is orthogonal to every solenoidal test. -/
theorem exists_pressure_weakMomentumResidual_eq_zero_iff
    (div : H →L[ℝ] K) (r : H)
    (hclosed : IsClosed (div.range : Set K)) :
    (∃ p : K, p ∈ div.range ∧ weakMomentumResidual div r p = 0) ↔
      ∀ v : SolenoidalSpace div, ⟪r, (v : H)⟫_ℝ = 0 := by
  constructor
  · rintro ⟨p, _hp, hresidual⟩ v
    exact inner_eq_zero_on_solenoidal_of_weakMomentumResidual_eq_zero
      div r p hresidual v
  · intro hannihilates
    exact (existsUnique_pressure_weakMomentumResidual_eq_zero
      div r hannihilates hclosed).exists

end AbstractPressure

section PointwisePressure

/-- A vanishing Euler residual determines the pressure gradient from velocity
and force at the evaluation point. -/
theorem eulerMomentumResidual_eq_zero_iff_spatialGradient_eq
    (n : ℕ) (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ)
    (f : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) :
    eulerMomentumResidual n u p f x = 0 ↔
      spatialGradient p x = f x - materialDerivative n u u x := by
  constructor
  · intro h
    rw [eq_sub_iff_add_eq]
    simpa [add_comm] using (eulerMomentumResidual_eq_zero_iff n u p f x).1 h
  · intro h
    apply (eulerMomentumResidual_eq_zero_iff n u p f x).2
    rw [add_comm]
    exact (eq_sub_iff_add_eq.mp h)

/-- A vanishing Stokes residual determines the pressure gradient from
velocity, viscosity, and force at the evaluation point. -/
theorem stokesMomentumResidual_eq_zero_iff_spatialGradient_eq
    (n : ℕ) (ν : ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (p : ℝ^(n + 1) → ℝ) (f : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) :
    stokesMomentumResidual n ν u p f x = 0 ↔
      spatialGradient p x =
        NavierStokes.viscousTerm n ν u x + f x - timeDerivative n u x := by
  constructor
  · intro h
    rw [eq_sub_iff_add_eq]
    simpa [add_comm] using
      (stokesMomentumResidual_eq_zero_iff n ν u p f x).1 h
  · intro h
    apply (stokesMomentumResidual_eq_zero_iff n ν u p f x).2
    rw [add_comm]
    exact (eq_sub_iff_add_eq.mp h)

/-- A vanishing Navier–Stokes residual determines the pressure gradient from
velocity, viscosity, and force at the evaluation point. -/
theorem navierStokesMomentumResidual_eq_zero_iff_spatialGradient_eq
    (n : ℕ) (ν : ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (p : ℝ^(n + 1) → ℝ) (f : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) :
    navierStokesMomentumResidual n ν u p f x = 0 ↔
      spatialGradient p x = NavierStokes.viscousTerm n ν u x + f x -
        materialDerivative n u u x := by
  constructor
  · intro h
    rw [eq_sub_iff_add_eq]
    simpa [add_comm] using
      (navierStokesMomentumResidual_eq_zero_iff n ν u p f x).1 h
  · intro h
    apply (navierStokesMomentumResidual_eq_zero_iff n ν u p f x).2
    rw [add_comm]
    exact (eq_sub_iff_add_eq.mp h)

/-- Two pressures closing the same Euler momentum equation have the same
gradient at the evaluation point. -/
theorem spatialGradient_eq_of_eulerMomentumResidual_eq_zero
    (n : ℕ) (u : ℝ^(n + 1) → ℝ^n) (p q : ℝ^(n + 1) → ℝ)
    (f : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1))
    (hp : eulerMomentumResidual n u p f x = 0)
    (hq : eulerMomentumResidual n u q f x = 0) :
    spatialGradient p x = spatialGradient q x := by
  rw [(eulerMomentumResidual_eq_zero_iff_spatialGradient_eq
    n u p f x).1 hp,
    (eulerMomentumResidual_eq_zero_iff_spatialGradient_eq
      n u q f x).1 hq]

/-- Two pressures closing the same Stokes momentum equation have the same
gradient at the evaluation point. -/
theorem spatialGradient_eq_of_stokesMomentumResidual_eq_zero
    (n : ℕ) (ν : ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (p q : ℝ^(n + 1) → ℝ) (f : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1))
    (hp : stokesMomentumResidual n ν u p f x = 0)
    (hq : stokesMomentumResidual n ν u q f x = 0) :
    spatialGradient p x = spatialGradient q x := by
  rw [(stokesMomentumResidual_eq_zero_iff_spatialGradient_eq
    n ν u p f x).1 hp,
    (stokesMomentumResidual_eq_zero_iff_spatialGradient_eq
      n ν u q f x).1 hq]

/-- Two pressures closing the same Navier–Stokes momentum equation have the
same gradient at the evaluation point. -/
theorem spatialGradient_eq_of_navierStokesMomentumResidual_eq_zero
    (n : ℕ) (ν : ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (p q : ℝ^(n + 1) → ℝ) (f : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1))
    (hp : navierStokesMomentumResidual n ν u p f x = 0)
    (hq : navierStokesMomentumResidual n ν u q f x = 0) :
    spatialGradient p x = spatialGradient q x := by
  rw [(navierStokesMomentumResidual_eq_zero_iff_spatialGradient_eq
    n ν u p f x).1 hp,
    (navierStokesMomentumResidual_eq_zero_iff_spatialGradient_eq
      n ν u q f x).1 hq]

end PointwisePressure

section ClassicalPressure

open scoped Gradient

variable {n : ℕ}

/-- A spatially closed spacetime vector field admits a scalar potential on
every time slice of an open convex domain.

The spatial Poincaré lemma is applied independently at each time, so the family `p`
carries no time regularity. -/
theorem exists_pressure_family_of_fderiv_symmetric
    {s : Set (ℝ^n)} (hs : Convex ℝ s) (hso : IsOpen s)
    {g : ℝ^(n + 1) → ℝ^n}
    (hg : ∀ t : ℝ, DifferentiableOn ℝ
      (fun x ↦ g (PDE.Common.timeSpaceCons t x)) s)
    (hsymm : ∀ (t : ℝ) (x : ℝ^n), x ∈ s → ∀ a b : ℝ^n,
      inner ℝ
          ((fderiv ℝ (fun y ↦ g (PDE.Common.timeSpaceCons t y)) x) a) b =
        inner ℝ
          ((fderiv ℝ (fun y ↦ g (PDE.Common.timeSpaceCons t y)) x) b) a) :
    ∃ p : ℝ → ℝ^n → ℝ, ∀ (t : ℝ) (x : ℝ^n), x ∈ s →
      HasGradientAt (p t) (g (PDE.Common.timeSpaceCons t x)) x := by
  have hpotential (t : ℝ) :
      ∃ p : ℝ^n → ℝ, ∀ x ∈ s,
        HasGradientAt p (g (PDE.Common.timeSpaceCons t x)) x :=
    InnerProductSpace.exists_potential_of_fderiv_symmetric hs hso (hg t) (hsymm t)
  choose p hp using hpotential
  exact ⟨p, hp⟩

/-- Spatial closedness of the pressure-gradient candidate produces a pressure
family satisfying the Navier–Stokes momentum equation on each time slice.

The pressure-gradient candidate is
`ν Δu + f - D_t u`. Its symmetric-Jacobian hypothesis is the coordinate-free
form of vanishing spatial curl. The conclusion is the physical momentum
balance with an ordinary scalar potential on every spatial slice, chosen slice by
slice. -/
theorem exists_pressure_navierStokes_momentum_equation_of_fderiv_symmetric
    {s : Set (ℝ^n)} (hs : Convex ℝ s) (hso : IsOpen s)
    (ν : ℝ) (u f : ℝ^(n + 1) → ℝ^n)
    (hg : ∀ t : ℝ, DifferentiableOn ℝ
      (fun x ↦
        NavierStokes.viscousTerm n ν u (PDE.Common.timeSpaceCons t x) +
          f (PDE.Common.timeSpaceCons t x) -
          materialDerivative n u u (PDE.Common.timeSpaceCons t x)) s)
    (hsymm : ∀ (t : ℝ) (x : ℝ^n), x ∈ s → ∀ a b : ℝ^n,
      let g : ℝ^n → ℝ^n := fun y ↦
        NavierStokes.viscousTerm n ν u (PDE.Common.timeSpaceCons t y) +
          f (PDE.Common.timeSpaceCons t y) -
          materialDerivative n u u (PDE.Common.timeSpaceCons t y)
      inner ℝ ((fderiv ℝ g x) a) b = inner ℝ ((fderiv ℝ g x) b) a) :
    ∃ p : ℝ → ℝ^n → ℝ, ∀ (t : ℝ) (x : ℝ^n), x ∈ s →
      HasGradientAt (p t)
          (NavierStokes.viscousTerm n ν u
              (PDE.Common.timeSpaceCons t x) +
            f (PDE.Common.timeSpaceCons t x) -
            materialDerivative n u u (PDE.Common.timeSpaceCons t x)) x ∧
        materialDerivative n u u (PDE.Common.timeSpaceCons t x) +
            ∇ (p t) x =
          NavierStokes.viscousTerm n ν u (PDE.Common.timeSpaceCons t x) +
            f (PDE.Common.timeSpaceCons t x) := by
  let g : ℝ^(n + 1) → ℝ^n := fun xt ↦
    NavierStokes.viscousTerm n ν u xt + f xt -
      materialDerivative n u u xt
  have hg' : ∀ t : ℝ, DifferentiableOn ℝ
      (fun x ↦ g (PDE.Common.timeSpaceCons t x)) s := hg
  have hsymm' : ∀ (t : ℝ) (x : ℝ^n), x ∈ s → ∀ a b : ℝ^n,
      inner ℝ
          ((fderiv ℝ (fun y ↦ g (PDE.Common.timeSpaceCons t y)) x) a) b =
        inner ℝ
          ((fderiv ℝ (fun y ↦ g (PDE.Common.timeSpaceCons t y)) x) b) a :=
    hsymm
  obtain ⟨p, hp⟩ :=
    exists_pressure_family_of_fderiv_symmetric hs hso hg' hsymm'
  refine ⟨p, fun t x hx ↦ ⟨hp t x hx, ?_⟩⟩
  rw [(hp t x hx).gradient]
  dsimp [g]
  abel

/-- Coordinate form of the classical Navier–Stokes pressure reconstruction
criterion. It is enough to prove that every pair of spatial coordinate
derivatives of `ν Δu + f - D_t u` commutes. In three dimensions this is
equivalent to the vanishing of its ordinary spatial curl. -/
theorem exists_pressure_navierStokes_momentum_equation_of_partialDeriv_comm
    {s : Set (ℝ^n)} (hs : Convex ℝ s) (hso : IsOpen s)
    (ν : ℝ) (u f : ℝ^(n + 1) → ℝ^n)
    (hg : ∀ t : ℝ, DifferentiableOn ℝ
      (fun x ↦
        NavierStokes.viscousTerm n ν u (PDE.Common.timeSpaceCons t x) +
          f (PDE.Common.timeSpaceCons t x) -
          materialDerivative n u u (PDE.Common.timeSpaceCons t x)) s)
    (hcomm : ∀ (t : ℝ) (x : ℝ^n), x ∈ s → ∀ i j : Fin n,
      let g : ℝ^n → ℝ^n := fun y ↦
        NavierStokes.viscousTerm n ν u (PDE.Common.timeSpaceCons t y) +
          f (PDE.Common.timeSpaceCons t y) -
          materialDerivative n u u (PDE.Common.timeSpaceCons t y)
      (∂[i] (fun y ↦ g y j)) x =
        (∂[j] (fun y ↦ g y i)) x) :
    ∃ p : ℝ → ℝ^n → ℝ, ∀ (t : ℝ) (x : ℝ^n), x ∈ s →
      HasGradientAt (p t)
          (NavierStokes.viscousTerm n ν u
              (PDE.Common.timeSpaceCons t x) +
            f (PDE.Common.timeSpaceCons t x) -
            materialDerivative n u u (PDE.Common.timeSpaceCons t x)) x ∧
        materialDerivative n u u (PDE.Common.timeSpaceCons t x) +
            ∇ (p t) x =
          NavierStokes.viscousTerm n ν u (PDE.Common.timeSpaceCons t x) +
            f (PDE.Common.timeSpaceCons t x) := by
  apply exists_pressure_navierStokes_momentum_equation_of_fderiv_symmetric
    hs hso ν u f hg
  intro t x hx
  let g : ℝ^n → ℝ^n := fun y ↦
    NavierStokes.viscousTerm n ν u (PDE.Common.timeSpaceCons t y) +
      f (PDE.Common.timeSpaceCons t y) -
      materialDerivative n u u (PDE.Common.timeSpaceCons t y)
  exact EuclideanSpace.inner_fderiv_apply_comm_of_partialDeriv_comm g x
    ((hg t x hx).differentiableAt (hso.mem_nhds hx)) (hcomm t x hx)

end ClassicalPressure

end IncompressibleFlow
