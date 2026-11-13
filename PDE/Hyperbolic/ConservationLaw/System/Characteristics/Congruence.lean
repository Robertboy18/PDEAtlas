/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.Ordered

/-!
# Characteristic speeds under equality of flux germs

Equal flux germs have equal derivatives. Strict hyperbolicity therefore passes
between them, and uniqueness of the ordered eigenvalue list identifies every
canonical characteristic speed. The flux and its dimension are arbitrary.
-/

@[expose] public noncomputable section

open Filter Set PDE.Analysis
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System

/-- A flux germ preserves strict hyperbolicity, including differentiability. -/
theorem IsStrictlyHyperbolicAt.congr_of_eventuallyEq {m : ℕ} {f g : ℝ^m → ℝ^m} {x : ℝ^m}
    (hg : IsStrictlyHyperbolicAt g x) (hfg : f =ᶠ[𝓝 x] g) :
    IsStrictlyHyperbolicAt f x := by
  have hD : fderiv ℝ f x = fderiv ℝ g x := hfg.fderiv_eq
  refine ⟨hg.1.congr_of_eventuallyEq hfg, ?_⟩
  simpa only [hD] using hg.2

/-- Equal flux germs have the same canonical ordered speeds. The
ordered-eigenbasis uniqueness theorem removes any dependence on basis choices. -/
theorem characteristicSpeed_eq_of_eventuallyEq {m : ℕ} {f g : ℝ^m → ℝ^m} {x : ℝ^m}
    (hg : IsStrictlyHyperbolicAt g x) (hfg : f =ᶠ[𝓝 x] g) :
    (fun k ↦ characteristicSpeed f k x) = fun k ↦ characteristicSpeed g k x := by
  obtain ⟨horder, basis, hbasis⟩ := characteristicSpeed_spec hg
  apply characteristicSpeed_eq_of_eigenbasis basis horder
  intro k
  have hD : fderiv ℝ f x = fderiv ℝ g x := hfg.fderiv_eq
  rw [hD]
  exact hbasis k

end PDE.Hyperbolic.ConservationLaw.System
