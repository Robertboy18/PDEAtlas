/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Weak evolution equations in a Gelfand triple

For a form `B : V → V*`, a load `ℓ ∈ V*`, a state `u ∈ V` and a dual derivative `u' ∈ V*`, the
weak evolution equation at one time is `u'(v) + B(u, v) = ℓ(v)` for all `v ∈ V`, that is,
`u' + B u = ℓ` in the strong dual `V*`. We define it at one time and on a set of times, and
show that it is preserved by sums, differences, scalar multiples and restriction to smaller
time sets. The difference of two solutions with the same load solves the homogeneous equation.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.1, condition (i) in the definition of weak solution.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section


open Set

namespace PDE.Analysis.Evolution

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The weak evolution equation `u' + B u = ℓ` in `V*` at one time:
`u'(v) + B(u, v) = ℓ(v)` for every `v ∈ V`. -/
def SatisfiesGelfandWeakEvolutionAt
    (B : V →L[ℝ] StrongDual ℝ V) (ell : StrongDual ℝ V)
    (u : V) (du : StrongDual ℝ V) : Prop :=
  ∀ v : V, du v + B u v = ell v

namespace SatisfiesGelfandWeakEvolutionAt

variable {B : V →L[ℝ] StrongDual ℝ V}
variable {ell ell₁ ell₂ : StrongDual ℝ V}
variable {u u₁ u₂ : V} {du du₁ du₂ : StrongDual ℝ V}

/-- The zero trajectory and zero dual derivative satisfy the homogeneous equation. -/
@[simp]
theorem zero (B : V →L[ℝ] StrongDual ℝ V) :
    SatisfiesGelfandWeakEvolutionAt B 0 0 0 := by
  intro v
  simp

/-- Pointwise Gelfand weak evolution identities are closed under addition. -/
theorem add
    (h₁ : SatisfiesGelfandWeakEvolutionAt B ell₁ u₁ du₁)
    (h₂ : SatisfiesGelfandWeakEvolutionAt B ell₂ u₂ du₂) :
    SatisfiesGelfandWeakEvolutionAt B (ell₁ + ell₂) (u₁ + u₂) (du₁ + du₂) := by
  intro v
  have h₁v := h₁ v
  have h₂v := h₂ v
  simp [map_add] at h₁v h₂v ⊢
  linarith

/-- Negating a pointwise weak evolution identity negates all of its data. -/
theorem neg
    (h : SatisfiesGelfandWeakEvolutionAt B ell u du) :
    SatisfiesGelfandWeakEvolutionAt B (-ell) (-u) (-du) := by
  intro v
  have hv := h v
  simp at hv ⊢
  linarith

/-- Subtracting pointwise weak evolution identities subtracts their data. -/
theorem sub
    (h₁ : SatisfiesGelfandWeakEvolutionAt B ell₁ u₁ du₁)
    (h₂ : SatisfiesGelfandWeakEvolutionAt B ell₂ u₂ du₂) :
    SatisfiesGelfandWeakEvolutionAt B (ell₁ - ell₂) (u₁ - u₂) (du₁ - du₂) := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

/-- Scaling a pointwise weak evolution identity scales its forcing, state, and derivative. -/
theorem smul (c : ℝ)
    (h : SatisfiesGelfandWeakEvolutionAt B ell u du) :
    SatisfiesGelfandWeakEvolutionAt B (c • ell) (c • u) (c • du) := by
  intro v
  have hv := h v
  calc
    (c • du) v + B (c • u) v =
        c * (du v + B u v) := by
      simp [mul_add]
    _ = c * ell v := by rw [hv]
    _ = (c • ell) v := by simp

/-- Linear combinations of two Gelfand weak evolution identities at a fixed time. -/
theorem linear_combination (c₁ c₂ : ℝ)
    (h₁ : SatisfiesGelfandWeakEvolutionAt B ell₁ u₁ du₁)
    (h₂ : SatisfiesGelfandWeakEvolutionAt B ell₂ u₂ du₂) :
    SatisfiesGelfandWeakEvolutionAt B (c₁ • ell₁ + c₂ • ell₂)
      (c₁ • u₁ + c₂ • u₂) (c₁ • du₁ + c₂ • du₂) :=
  (h₁.smul c₁).add (h₂.smul c₂)

/-- Difference of two Gelfand weak evolution identities with the same forcing is homogeneous. -/
theorem difference_same_forcing_homogeneous
    (h₁ : SatisfiesGelfandWeakEvolutionAt B ell u₁ du₁)
    (h₂ : SatisfiesGelfandWeakEvolutionAt B ell u₂ du₂) :
    SatisfiesGelfandWeakEvolutionAt B 0 (u₁ - u₂) (du₁ - du₂) := by
  simpa using h₁.sub h₂

end SatisfiesGelfandWeakEvolutionAt

/--
Gelfand-triple weak evolution equation on a time set.

For every `t ∈ I`, this records

`u'(t) + B(t)u(t) = ell(t)` in `V*`,

tested against every vector of the energy space `V`.
-/
def SatisfiesGelfandWeakEvolutionOn
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V) (u : ℝ → V)
    (du : ℝ → StrongDual ℝ V) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, SatisfiesGelfandWeakEvolutionAt (B t) (ell t) (u t) (du t)

namespace SatisfiesGelfandWeakEvolutionOn

variable {B : ℝ → V →L[ℝ] StrongDual ℝ V}
variable {ell ell₁ ell₂ : ℝ → StrongDual ℝ V}
variable {u u₁ u₂ : ℝ → V} {du du₁ du₂ : ℝ → StrongDual ℝ V} {I J : Set ℝ}

/-- The zero trajectory satisfies the homogeneous weak evolution on every time set. -/
@[simp]
theorem zero (B : ℝ → V →L[ℝ] StrongDual ℝ V) (I : Set ℝ) :
    SatisfiesGelfandWeakEvolutionOn B (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0) I := by
  intro t ht
  simp [SatisfiesGelfandWeakEvolutionAt.zero]

/-- Restrict a Gelfand weak evolution identity to a smaller time set. -/
theorem mono
    (h : SatisfiesGelfandWeakEvolutionOn B ell u du I) (hJI : J ⊆ I) :
    SatisfiesGelfandWeakEvolutionOn B ell u du J := by
  intro t ht
  exact h t (hJI ht)

/-- Superposition for two Gelfand weak evolutions on the same time set. -/
theorem add
    (h₁ : SatisfiesGelfandWeakEvolutionOn B ell₁ u₁ du₁ I)
    (h₂ : SatisfiesGelfandWeakEvolutionOn B ell₂ u₂ du₂ I) :
    SatisfiesGelfandWeakEvolutionOn B (fun t ↦ ell₁ t + ell₂ t)
      (fun t ↦ u₁ t + u₂ t) (fun t ↦ du₁ t + du₂ t) I := by
  intro t ht
  exact (h₁ t ht).add (h₂ t ht)

/-- Negating a Gelfand weak evolution negates the forcing, trajectory, and derivative. -/
theorem neg
    (h : SatisfiesGelfandWeakEvolutionOn B ell u du I) :
    SatisfiesGelfandWeakEvolutionOn B (fun t ↦ -ell t)
      (fun t ↦ -u t) (fun t ↦ -du t) I := by
  intro t ht
  exact (h t ht).neg

/-- Difference of Gelfand weak evolutions solves the equation with difference forcing. -/
theorem sub
    (h₁ : SatisfiesGelfandWeakEvolutionOn B ell₁ u₁ du₁ I)
    (h₂ : SatisfiesGelfandWeakEvolutionOn B ell₂ u₂ du₂ I) :
    SatisfiesGelfandWeakEvolutionOn B (fun t ↦ ell₁ t - ell₂ t)
      (fun t ↦ u₁ t - u₂ t) (fun t ↦ du₁ t - du₂ t) I := by
  intro t ht
  exact (h₁ t ht).sub (h₂ t ht)

/-- Scaling a Gelfand weak evolution scales every term by the same real constant. -/
theorem smul (c : ℝ)
    (h : SatisfiesGelfandWeakEvolutionOn B ell u du I) :
    SatisfiesGelfandWeakEvolutionOn B (fun t ↦ c • ell t)
      (fun t ↦ c • u t) (fun t ↦ c • du t) I := by
  intro t ht
  exact (h t ht).smul c

/-- Linear combinations of two Gelfand weak evolutions on a common time set. -/
theorem linear_combination (c₁ c₂ : ℝ)
    (h₁ : SatisfiesGelfandWeakEvolutionOn B ell₁ u₁ du₁ I)
    (h₂ : SatisfiesGelfandWeakEvolutionOn B ell₂ u₂ du₂ I) :
    SatisfiesGelfandWeakEvolutionOn B (fun t ↦ c₁ • ell₁ t + c₂ • ell₂ t)
      (fun t ↦ c₁ • u₁ t + c₂ • u₂ t)
      (fun t ↦ c₁ • du₁ t + c₂ • du₂ t) I := by
  intro t ht
  exact (h₁ t ht).linear_combination c₁ c₂ (h₂ t ht)

/-- Difference of two Gelfand weak evolutions with the same forcing is homogeneous. -/
theorem difference_same_forcing_homogeneous
    (h₁ : SatisfiesGelfandWeakEvolutionOn B ell u₁ du₁ I)
    (h₂ : SatisfiesGelfandWeakEvolutionOn B ell u₂ du₂ I) :
    SatisfiesGelfandWeakEvolutionOn B (fun _ ↦ 0)
      (fun t ↦ u₁ t - u₂ t) (fun t ↦ du₁ t - du₂ t) I := by
  intro t ht
  exact (h₁ t ht).difference_same_forcing_homogeneous (h₂ t ht)

end SatisfiesGelfandWeakEvolutionOn

end PDE.Analysis.Evolution
