/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.TrilinearForm
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Quadratic weak evolution equations in a Gelfand space

A continuous trilinear form produces a quadratic dual-valued nonlinearity
`u ↦ N u u`. We state the weak equation `u' + A u + N(u, u) = ℓ` in `V*`, at one time and
on a set of times. When `N` is skew in its last two arguments, testing with the state removes
the nonlinearity, and the difference of two solutions with the same load satisfies an
energy identity whose only nonlinear term is `N(u₁ - u₂, u₂, u₁ - u₂)`. Incompressible
convection is the main example.
-/

@[expose] public section

noncomputable section


namespace PDE.Analysis.Evolution

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/--
A quadratic weak evolution equation at one time.

The identity is
`du(v) + A(u,v) + N(u,u,v) = ell(v)` for every `v`.
-/
def SatisfiesQuadraticGelfandWeakEvolutionAt
    (A : V →L[ℝ] StrongDual ℝ V)
    (N : PDE.Analysis.ContinuousTrilinearForm V V V)
    (ell : StrongDual ℝ V) (u : V) (du : StrongDual ℝ V) : Prop :=
  ∀ v : V, du v + A u v + N u u v = ell v

namespace SatisfiesQuadraticGelfandWeakEvolutionAt

variable {A : V →L[ℝ] StrongDual ℝ V}
variable {N : PDE.Analysis.ContinuousTrilinearForm V V V}
variable {ell : StrongDual ℝ V}
variable {u u₁ u₂ : V} {du du₁ du₂ : StrongDual ℝ V}

/--
Testing a quadratic weak evolution against its state removes a nonlinearity
that is skew in its last two arguments.
-/
theorem energy_equation
    (hN : N.IsSkewInLastTwo)
    (h : SatisfiesQuadraticGelfandWeakEvolutionAt A N ell u du) :
    du u + A u u = ell u := by
  have hu := h u
  rw [hN.energy_eq_zero] at hu
  simpa using hu

/-- Subtracting two quadratic weak equations with the same forcing gives the
exact difference equation. -/
theorem difference_same_forcing
    (h₁ : SatisfiesQuadraticGelfandWeakEvolutionAt A N ell u₁ du₁)
    (h₂ : SatisfiesQuadraticGelfandWeakEvolutionAt A N ell u₂ du₂) :
    ∀ v : V,
      (du₁ - du₂) v + A (u₁ - u₂) v +
          (N u₁ u₁ v - N u₂ u₂ v) = 0 := by
  intro v
  have h₁v := h₁ v
  have h₂v := h₂ v
  simp only [sub_apply, map_sub]
  linarith

/--
For a skew trilinear form, the nonlinear term in the difference energy is
`N(u₁-u₂,u₂,u₁-u₂)`.
-/
theorem difference_energy_equation
    (hN : N.IsSkewInLastTwo)
    (h₁ : SatisfiesQuadraticGelfandWeakEvolutionAt A N ell u₁ du₁)
    (h₂ : SatisfiesQuadraticGelfandWeakEvolutionAt A N ell u₂ du₂) :
    let d := u₁ - u₂
    (du₁ - du₂) d + A d d + N d u₂ d = 0 := by
  let d := u₁ - u₂
  have hdiff := h₁.difference_same_forcing h₂ d
  rw [hN.quadratic_difference] at hdiff
  exact hdiff

end SatisfiesQuadraticGelfandWeakEvolutionAt

/-- A quadratic Gelfand weak evolution equation on a set of times. -/
def SatisfiesQuadraticGelfandWeakEvolutionOn
    (A : ℝ → V →L[ℝ] StrongDual ℝ V)
    (N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V)
    (ell : ℝ → StrongDual ℝ V) (u : ℝ → V)
    (du : ℝ → StrongDual ℝ V) (I : Set ℝ) : Prop :=
  ∀ t ∈ I,
    SatisfiesQuadraticGelfandWeakEvolutionAt
      (A t) (N t) (ell t) (u t) (du t)

namespace SatisfiesQuadraticGelfandWeakEvolutionOn

variable {A : ℝ → V →L[ℝ] StrongDual ℝ V}
variable {N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V}
variable {ell : ℝ → StrongDual ℝ V}
variable {u : ℝ → V} {du : ℝ → StrongDual ℝ V}
variable {I J : Set ℝ}

/-- Restrict a quadratic weak evolution identity to a smaller time set. -/
theorem mono
    (h : SatisfiesQuadraticGelfandWeakEvolutionOn A N ell u du I)
    (hJI : J ⊆ I) :
    SatisfiesQuadraticGelfandWeakEvolutionOn A N ell u du J := by
  intro t ht
  exact h t (hJI ht)

/-- Pointwise skew cancellation gives the state-tested energy equation on
the whole time set. -/
theorem energy_equation
    (hN : ∀ t ∈ I, (N t).IsSkewInLastTwo)
    (h : SatisfiesQuadraticGelfandWeakEvolutionOn A N ell u du I) :
    ∀ t ∈ I, du t (u t) + A t (u t) (u t) = ell t (u t) := by
  intro t ht
  exact (h t ht).energy_equation (hN t ht)

end SatisfiesQuadraticGelfandWeakEvolutionOn

end PDE.Analysis.Evolution
