/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.Distribution

/-!
# Fundamental solutions of distributional operators

A distribution `T` is a fundamental solution for `P` at an interior pole `x` when `P T` is
the Dirac mass at `x`; the action characterization reduces this equality to evaluation on every
test function.

The interiority condition is part of the predicate. Mathlib's `Distribution.delta x` on an
open set `Ω` is zero when `x ∉ Ω`, so omitting this condition would let a homogeneous
equation be presented as a fundamental-solution equation at an exterior point.
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace Distribution

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A distribution `T` is a fundamental solution for `P` at the interior pole `x` when
`P T = δₓ`. -/
def IsFundamentalSolutionAt
    {Ω : Opens E}
    (P : 𝓓'(Ω, ℝ) →L[ℝ] 𝓓'(Ω, ℝ))
    (T : 𝓓'(Ω, ℝ)) (x : E) : Prop :=
  x ∈ Ω ∧ P T = delta x

/-- The pole of a fundamental solution belongs to the distribution domain. -/
theorem IsFundamentalSolutionAt.mem
    {Ω : Opens E}
    {P : 𝓓'(Ω, ℝ) →L[ℝ] 𝓓'(Ω, ℝ)}
    {T : 𝓓'(Ω, ℝ)} {x : E}
    (h : IsFundamentalSolutionAt P T x) :
    x ∈ Ω :=
  h.1

/-- A fundamental solution satisfies its defining distribution equation. -/
theorem IsFundamentalSolutionAt.eq
    {Ω : Opens E}
    {P : 𝓓'(Ω, ℝ) →L[ℝ] 𝓓'(Ω, ℝ)}
    {T : 𝓓'(Ω, ℝ)} {x : E}
    (h : IsFundamentalSolutionAt P T x) :
    P T = delta x :=
  h.2

/-- A fundamental-solution equation evaluates to the test function at its pole. -/
theorem IsFundamentalSolutionAt.apply
    {Ω : Opens E}
    {P : 𝓓'(Ω, ℝ) →L[ℝ] 𝓓'(Ω, ℝ)}
    {T : 𝓓'(Ω, ℝ)} {x : E}
    (h : IsFundamentalSolutionAt P T x)
    (φ : 𝓓(Ω, ℝ)) :
    P T φ = φ x := by
  rw [h.eq, delta_apply]

/-- Having an interior pole and satisfying `P T = δₓ` is equivalent to the corresponding
test-function action identity. -/
theorem isFundamentalSolutionAt_iff
    {Ω : Opens E}
    {P : 𝓓'(Ω, ℝ) →L[ℝ] 𝓓'(Ω, ℝ)}
    {T : 𝓓'(Ω, ℝ)} {x : E} :
    IsFundamentalSolutionAt P T x ↔
      x ∈ Ω ∧ ∀ φ : 𝓓(Ω, ℝ), P T φ = φ x := by
  constructor
  · intro h
    exact ⟨h.mem, h.apply⟩
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    ext φ
    simpa using h φ

end Distribution
