/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import PDE.Analysis.Evolution.Gelfand.Equation
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Weak evolution equations

For a real inner product space `V`, a bounded bilinear form `B : V →L[ℝ] V*` and
`ℓ ∈ V*`, `SatisfiesWeakEvolutionAt B ℓ u u'` is the weak evolution equation
`⟪u', v⟫ + B(u, v) = ℓ(v)` for every `v ∈ V` at a single time.
`SatisfiesWeakEvolutionOn B ℓ u u' I` asks for

`⟪u'(t), v⟫ + B(t)(u(t), v) = ℓ(t)(v)`

at every `t ∈ I`. Both are linear in the triple `(ℓ, u, u')`: sums, negatives,
scalar multiples and linear combinations of solutions are solutions, and the
difference of two solutions with the same forcing solves the homogeneous
equation. The pointwise equation is the Gelfand-triple equation
`SatisfiesGelfandWeakEvolutionAt` with the dual vector `⟪u', ·⟫` in place of
`u'`, and its linearity lemmas are obtained from the Gelfand ones.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.1, equation (9) and the definition of weak solution
  that follows it. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Evolution

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The weak evolution equation at one time:
`⟨u',v⟩ + B(u,v) = ℓ(v)` for every test vector `v`. -/
def SatisfiesWeakEvolutionAt
    (B : V →L[ℝ] StrongDual ℝ V) (ell : StrongDual ℝ V)
    (u du : V) : Prop :=
  ∀ v : V, inner ℝ du v + B u v = ell v

/-- The weak equation in `V` is the Gelfand weak equation for the dual vector
`innerSL ℝ du`. -/
theorem satisfiesWeakEvolutionAt_iff_gelfand
    {B : V →L[ℝ] StrongDual ℝ V} {ell : StrongDual ℝ V} {u du : V} :
    SatisfiesWeakEvolutionAt B ell u du ↔
      SatisfiesGelfandWeakEvolutionAt B ell u (innerSL ℝ du) :=
  Iff.rfl

namespace SatisfiesWeakEvolutionAt

variable {B : V →L[ℝ] StrongDual ℝ V}
variable {ell ell₁ ell₂ : StrongDual ℝ V} {u u₁ u₂ du du₁ du₂ : V}

/-- The zero state with zero derivative satisfies the homogeneous weak equation. -/
@[simp]
theorem zero (B : V →L[ℝ] StrongDual ℝ V) :
    SatisfiesWeakEvolutionAt B 0 0 0 := by
  intro v
  simp

/-- Weak evolution identities are closed under pointwise addition. -/
theorem add
    (h₁ : SatisfiesWeakEvolutionAt B ell₁ u₁ du₁)
    (h₂ : SatisfiesWeakEvolutionAt B ell₂ u₂ du₂) :
    SatisfiesWeakEvolutionAt B (ell₁ + ell₂) (u₁ + u₂) (du₁ + du₂) := by
  rw [satisfiesWeakEvolutionAt_iff_gelfand, map_add]
  exact SatisfiesGelfandWeakEvolutionAt.add h₁ h₂

/-- Negating the state, derivative, and forcing preserves the weak equation. -/
theorem neg
    (h : SatisfiesWeakEvolutionAt B ell u du) :
    SatisfiesWeakEvolutionAt B (-ell) (-u) (-du) := by
  rw [satisfiesWeakEvolutionAt_iff_gelfand, map_neg]
  exact SatisfiesGelfandWeakEvolutionAt.neg h

/-- Subtracting weak evolution identities subtracts their forcing terms. -/
theorem sub
    (h₁ : SatisfiesWeakEvolutionAt B ell₁ u₁ du₁)
    (h₂ : SatisfiesWeakEvolutionAt B ell₂ u₂ du₂) :
    SatisfiesWeakEvolutionAt B (ell₁ - ell₂) (u₁ - u₂) (du₁ - du₂) := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

/-- Scalar multiplication preserves a weak evolution identity. -/
theorem smul (c : ℝ)
    (h : SatisfiesWeakEvolutionAt B ell u du) :
    SatisfiesWeakEvolutionAt B (c • ell) (c • u) (c • du) := by
  rw [satisfiesWeakEvolutionAt_iff_gelfand, map_smulₛₗ, RCLike.conj_to_real]
  exact SatisfiesGelfandWeakEvolutionAt.smul c h

/-- Linear combinations of two weak evolution identities at a fixed time. -/
theorem linear_combination (c₁ c₂ : ℝ)
    (h₁ : SatisfiesWeakEvolutionAt B ell₁ u₁ du₁)
    (h₂ : SatisfiesWeakEvolutionAt B ell₂ u₂ du₂) :
    SatisfiesWeakEvolutionAt B (c₁ • ell₁ + c₂ • ell₂)
      (c₁ • u₁ + c₂ • u₂) (c₁ • du₁ + c₂ • du₂) :=
  (h₁.smul c₁).add (h₂.smul c₂)

/-- Difference of two weak evolution identities with the same forcing is homogeneous. -/
theorem difference_same_forcing_homogeneous
    (h₁ : SatisfiesWeakEvolutionAt B ell u₁ du₁)
    (h₂ : SatisfiesWeakEvolutionAt B ell u₂ du₂) :
    SatisfiesWeakEvolutionAt B 0 (u₁ - u₂) (du₁ - du₂) := by
  simpa using h₁.sub h₂

end SatisfiesWeakEvolutionAt

/--
Weak evolution equation on a time set.

For every admissible time `t`, the trajectory satisfies

`⟨u'(t), v⟩ + B(t)(u(t), v) = ℓ(t)(v)`

against every test vector `v`. The time set `I` is an arbitrary subset of `ℝ`.
-/
def SatisfiesWeakEvolutionOn
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V) (u du : ℝ → V) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, SatisfiesWeakEvolutionAt (B t) (ell t) (u t) (du t)

namespace SatisfiesWeakEvolutionOn

variable {B : ℝ → V →L[ℝ] StrongDual ℝ V}
variable {ell ell₁ ell₂ : ℝ → StrongDual ℝ V}
variable {u u₁ u₂ du du₁ du₂ : ℝ → V} {I J : Set ℝ}

/-- The zero trajectory satisfies the homogeneous weak equation on every time set. -/
@[simp]
theorem zero (B : ℝ → V →L[ℝ] StrongDual ℝ V) (I : Set ℝ) :
    SatisfiesWeakEvolutionOn B (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0) I := by
  intro t ht
  simp [SatisfiesWeakEvolutionAt.zero]

/-- Restrict a weak evolution identity to a smaller time set. -/
theorem mono
    (h : SatisfiesWeakEvolutionOn B ell u du I) (hJI : J ⊆ I) :
    SatisfiesWeakEvolutionOn B ell u du J := by
  intro t ht
  exact h t (hJI ht)

/-- Superposition for two weak evolutions on the same time set. -/
theorem add
    (h₁ : SatisfiesWeakEvolutionOn B ell₁ u₁ du₁ I)
    (h₂ : SatisfiesWeakEvolutionOn B ell₂ u₂ du₂ I) :
    SatisfiesWeakEvolutionOn B (fun t ↦ ell₁ t + ell₂ t)
      (fun t ↦ u₁ t + u₂ t) (fun t ↦ du₁ t + du₂ t) I := by
  intro t ht
  exact (h₁ t ht).add (h₂ t ht)

/-- Negating a weak evolution negates the forcing and trajectory. -/
theorem neg
    (h : SatisfiesWeakEvolutionOn B ell u du I) :
    SatisfiesWeakEvolutionOn B (fun t ↦ -ell t) (fun t ↦ -u t) (fun t ↦ -du t) I := by
  intro t ht
  exact (h t ht).neg

/-- Difference of weak evolutions solves the equation with difference forcing. -/
theorem sub
    (h₁ : SatisfiesWeakEvolutionOn B ell₁ u₁ du₁ I)
    (h₂ : SatisfiesWeakEvolutionOn B ell₂ u₂ du₂ I) :
    SatisfiesWeakEvolutionOn B (fun t ↦ ell₁ t - ell₂ t)
      (fun t ↦ u₁ t - u₂ t) (fun t ↦ du₁ t - du₂ t) I := by
  intro t ht
  exact (h₁ t ht).sub (h₂ t ht)

/-- Scaling a weak evolution scales the forcing, trajectory, and time derivative. -/
theorem smul (c : ℝ)
    (h : SatisfiesWeakEvolutionOn B ell u du I) :
    SatisfiesWeakEvolutionOn B (fun t ↦ c • ell t)
      (fun t ↦ c • u t) (fun t ↦ c • du t) I := by
  intro t ht
  exact (h t ht).smul c

/-- Linear combinations of weak evolutions on a common time set. -/
theorem linear_combination (c₁ c₂ : ℝ)
    (h₁ : SatisfiesWeakEvolutionOn B ell₁ u₁ du₁ I)
    (h₂ : SatisfiesWeakEvolutionOn B ell₂ u₂ du₂ I) :
    SatisfiesWeakEvolutionOn B (fun t ↦ c₁ • ell₁ t + c₂ • ell₂ t)
      (fun t ↦ c₁ • u₁ t + c₂ • u₂ t)
      (fun t ↦ c₁ • du₁ t + c₂ • du₂ t) I := by
  intro t ht
  exact (h₁ t ht).linear_combination c₁ c₂ (h₂ t ht)

/-- Difference of two weak evolutions with the same forcing is homogeneous. -/
theorem difference_same_forcing_homogeneous
    (h₁ : SatisfiesWeakEvolutionOn B ell u₁ du₁ I)
    (h₂ : SatisfiesWeakEvolutionOn B ell u₂ du₂ I) :
    SatisfiesWeakEvolutionOn B (fun _ ↦ 0)
      (fun t ↦ u₁ t - u₂ t) (fun t ↦ du₁ t - du₂ t) I := by
  intro t ht
  exact (h₁ t ht).difference_same_forcing_homogeneous (h₂ t ht)

end SatisfiesWeakEvolutionOn

end PDE.Analysis.Evolution
