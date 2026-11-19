/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Transport.Bootstrap
import PDE.Analysis.Calculus.Deriv.FiniteExceptionalSet

/-!
# Scalar unknowns with corners

A scalar function that is continuous on `[t₀, T]` and solves `f' = -a f + B` at every time of
`(t₀, T)` outside a finite set, with a right-continuous forcing `B`, solves the equation from the
right at every time of `[t₀, T)`, which is the form `SolvesAlongPaths` asks for. This covers
energy components with corners at finitely many times.

## Main results

* `SolvesAlongPaths.of_hasDerivAt_off_finite`: a function continuous on `[t₀, T]` with
  `f' = -a f + B` on `(t₀, T)` off a finite set, `B` right-continuous on `[t₀, T)`, solves the
  equation from the right at every time of `[t₀, T)`.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace PDE.Hyperbolic.Transport.SolvesAlongPaths

/-- **A scalar ODE off finitely many times.** If `f` is continuous on `[t₀, T]`, satisfies
`f' = -a f + B` at every time of `(t₀, T)` outside a finite set, and `B` is right-continuous on
`[t₀, T)`, then `f` solves the equation from the right at every time of `[t₀, T)`, as Lemma A.2
requires. -/
theorem of_hasDerivAt_off_finite {X : Type*} {D : Set X} {a : ℝ} {B f : ℝ → ℝ} {t₀ T : ℝ}
    {s : Set ℝ} (hs : s.Finite) (hf : ContinuousOn f (Icc t₀ T))
    (hderiv : ∀ t ∈ Ioo t₀ T \ s, HasDerivAt f (-a * f t + B t) t)
    (hB : ∀ t ∈ Ico t₀ T, ContinuousWithinAt B (Ici t) t) :
    SolvesAlongPaths D (fun _ _ ↦ a) (fun _ t ↦ B t) (fun _ t ↦ f t) t₀ T := by
  refine SolvesAlongPaths.of_hasDerivWithinAt (fun _ _ ↦ hf) fun _ _ t ht ↦ ?_
  refine PDE.Analysis.Calculus.hasDerivWithinAt_Ici_of_off_finite hs hf hderiv (fun u hu ↦ ?_) ht
  have hfu : ContinuousWithinAt f (Ici u) u :=
    (hf u (Ico_subset_Icc_self hu)).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE hu.2) (Icc_subset_Icc_left hu.1))
  exact (continuousWithinAt_const.mul hfu).add (hB u hu)

end PDE.Hyperbolic.Transport.SolvesAlongPaths
