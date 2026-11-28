/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.Uniqueness
public import PDE.Fluid.Boussinesq.HalfPlane.LevelK

/-!
# Regular solutions of order `k` of half-plane systems

The local theory of a half-plane system is set in the class `ω ∈ C^{1,α}`, `θ ∈ C^{2,α}`. This
module defines the class of solutions in which the propagation of higher regularity is stated:
regular solutions of order `k`.

The data class of order `k` is `Boussinesq.HalfPlane.IsHolderDataOf k ω₀ θ₀ α R N`: `ω₀ ∈ C^{k,α}`
and `θ₀ ∈ C^{k+1,α}` within the closed half-plane `H̄`, both vanishing there outside the disc of
radius `R`, with every derivative within `H̄` and the Hölder constants of the top derivatives at
most `N`. A regular solution of order `k` on the times `I`
(`IsRegularSolutionOfOn U κ R₀ k sol I α`) is a solution in the class `IsSolutionOn U κ R₀` whose
time slices are data of order `k` with a support radius less than `R₀` and a bound that are uniform
on every compact subinterval of `I`, and whose spatial derivatives within `H̄`, of orders at most
`k` for the vorticity and `k + 1` for the temperature, are continuous in time uniformly on `H̄`. All
conditions are on the closed half-plane, so the class passes to any solution with the same values
there.

## Main results

* `IsRegularSolutionOfOn`: regular solutions of order `k`.
* `IsRegularSolutionOfOn.mono`: for `α ∈ [0, 1]`, a regular solution of order `k` is a regular
  solution of every order `j ≤ k`, with twice the bound.
* `IsRegularSolutionOfOn.exists_isHolderDataOf`: at every time a slice is data of order `k` with a
  support radius less than `R₀`.
* `IsRegularSolutionOfOn.congr`: the class passes to a solution with the same values on the closed
  half-plane at every time.

Restriction to fewer times and shifts of the time are not stated here.

`IterationHigher.lean` constructs regular solutions of order `k` locally, `Persistence.lean`
propagates the class along a solution, `PersistenceCanonical.lean` shows that the canonical
representative keeps it, `PersistenceMaximal.lean` states the theorem on maximal solutions in it,
and `RegularField.lean` derives the regularity of the velocity field. The library has the same class
for the Boussinesq system (`Boussinesq.HalfPlane.IsRegularSolutionOfOn`).
-/

@[expose] public section

noncomputable section

open Set
open Boussinesq.HalfPlane

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- A **regular solution of order `k`** of the half-plane system with the velocity law `U` and the
forcing coefficient `κ` on the times `I`: a solution whose time slices are data of order `k` with
a support radius less than `R₀` and a bound that are uniform on every compact subinterval of the
times, and whose spatial derivatives within the closed half-plane, of orders at most `k` for the
vorticity and `k + 1` for the temperature, are continuous in time uniformly on the closed
half-plane. -/
structure IsRegularSolutionOfOn (U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2) (κ : ℝ^2 → ℝ) (R₀ : ℝ) (k : ℕ)
    (sol : Fields) (I : Set ℝ) (α : ℝ) : Prop extends IsSolutionOn U κ R₀ sol I where
  /-- Uniform `C^{k,α} × C^{k+1,α}` bounds of the slices on compact subintervals, with a support
  radius less than `R₀`. -/
  holderData : ∀ a b : ℝ, Icc a b ⊆ I → ∃ R < R₀, ∃ N : ℝ, ∀ t ∈ Icc a b,
    IsHolderDataOf k (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R N
  /-- The derivatives of the vorticity of order at most `k` are continuous in time uniformly on
  the closed half-plane. -/
  vorticity_uniform : ∀ j ≤ k, ∀ t ∈ I, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ I, |s - t| < δ →
    ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖iteratedFDerivWithin ℝ j (fun y ↦ sol.vorticity y s) H̄ x -
        iteratedFDerivWithin ℝ j (fun y ↦ sol.vorticity y t) H̄ x‖ ≤ ε
  /-- The derivatives of the temperature of order at most `k + 1` are continuous in time
  uniformly on the closed half-plane. -/
  temperature_uniform : ∀ j ≤ k + 1, ∀ t ∈ I, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ I, |s - t| < δ →
    ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖iteratedFDerivWithin ℝ j (fun y ↦ sol.temperature y s) H̄ x -
        iteratedFDerivWithin ℝ j (fun y ↦ sol.temperature y t) H̄ x‖ ≤ ε

namespace IsRegularSolutionOfOn

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {κ : ℝ^2 → ℝ} {R₀ : ℝ} {k : ℕ} {sol : Fields}
  {I : Set ℝ} {α : ℝ}

/-- Regular solutions of order `k` are regular solutions of every order `j ≤ k`. -/
theorem mono (h : IsRegularSolutionOfOn U κ R₀ k sol I α) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {j : ℕ}
    (hj : j ≤ k) : IsRegularSolutionOfOn U κ R₀ j sol I α where
  toIsSolutionOn := h.toIsSolutionOn
  holderData a b hab := by
    obtain ⟨R, hR, N, hRN⟩ := h.holderData a b hab
    exact ⟨R, hR, 2 * N, fun t ht ↦ (hRN t ht).mono hα0 hα1 hj⟩
  vorticity_uniform i hi := h.vorticity_uniform i (hi.trans hj)
  temperature_uniform i hi := h.temperature_uniform i (by omega)

/-- At every time a slice of a regular solution of order `k` is data of order `k` with a support
radius less than `R₀`. -/
theorem exists_isHolderDataOf (h : IsRegularSolutionOfOn U κ R₀ k sol I α) {t : ℝ}
    (ht : t ∈ I) : ∃ R < R₀, ∃ N : ℝ,
      IsHolderDataOf k (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α R N := by
  obtain ⟨R, hR, N, hRN⟩ := h.holderData t t (by simpa using ht)
  exact ⟨R, hR, N, hRN t ⟨le_rfl, le_rfl⟩⟩

/-- **Regularity depends only on the values on the closed half-plane**: a solution on `I` that
agrees on the closed half-plane at every time of `I` with a regular solution of order `k` is a
regular solution of order `k`. -/
theorem congr (h : IsRegularSolutionOfOn U κ R₀ k sol I α) {sol' : Fields}
    (h' : IsSolutionOn U κ R₀ sol' I)
    (heq : ∀ t ∈ I, ∀ x : ℝ^2, 0 ≤ x 1 →
      sol'.vorticity x t = sol.vorticity x t ∧ sol'.temperature x t = sol.temperature x t) :
    IsRegularSolutionOfOn U κ R₀ k sol' I α where
  toIsSolutionOn := h'
  holderData a b hab := by
    obtain ⟨R, hR, N, hRN⟩ := h.holderData a b hab
    exact ⟨R, hR, N, fun t ht ↦ (hRN t ht).congr (fun x hx ↦ (heq t (hab ht) x hx).1)
      (fun x hx ↦ (heq t (hab ht) x hx).2)⟩
  vorticity_uniform j hj t ht ε hε := by
    obtain ⟨δ, hδ, hδε⟩ := h.vorticity_uniform j hj t ht ε hε
    refine ⟨δ, hδ, fun s hs hst x hx ↦ ?_⟩
    have hE {r : ℝ} (hr : r ∈ I) :
        EqOn (fun y ↦ sol'.vorticity y r) (fun y ↦ sol.vorticity y r) H̄ :=
      fun y hy ↦ (heq r hr y hy).1
    rw [iteratedFDerivWithin_congr (hE hs) hx, iteratedFDerivWithin_congr (hE ht) hx]
    exact hδε s hs hst x hx
  temperature_uniform j hj t ht ε hε := by
    obtain ⟨δ, hδ, hδε⟩ := h.temperature_uniform j hj t ht ε hε
    refine ⟨δ, hδ, fun s hs hst x hx ↦ ?_⟩
    have hE {r : ℝ} (hr : r ∈ I) :
        EqOn (fun y ↦ sol'.temperature y r) (fun y ↦ sol.temperature y r) H̄ :=
      fun y hy ↦ (heq r hr y hy).2
    rw [iteratedFDerivWithin_congr (hE hs) hx, iteratedFDerivWithin_congr (hE ht) hx]
    exact hδε s hs hst x hx

end IsRegularSolutionOfOn

end HalfPlaneSystem
