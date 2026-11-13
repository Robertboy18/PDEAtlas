/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.SpacetimeWeakFormulation
public import PDE.Spaces.Sobolev.Approximation.Density.H1TimeSlices
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Regularity of the vector spacetime tests

The H¹-valued slice is continuous in its graph norm. Its base L² curve is
continuously differentiable, with the time derivative of the test as derivative.
A spacetime test supported strictly before the terminal time has zero terminal slice.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Sobolev ENNReal InnerProductSpace Topology Distributions

namespace PDE.Hyperbolic.FirstOrder

open SobolevSpace SobolevSpace.GraphSpace

open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ}

local notation "D" => DerivLp n 2 univ
local notation "H" => PiLp 2 (fun _ : Fin m ↦ D)

/-- A vector spacetime test is continuous as a curve in the product H¹ graph space.
Continuity includes the weak spatial derivative rows, not just the base L² row. -/
theorem continuous_spacetimeTestH1Slice (Φ : Fin m → 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ)) :
    Continuous (spacetimeTestH1Slice Φ) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p ↦
    continuous_globalTestFunctionToWkpOn_sliceRight (p := 2) (Ω := univ) (Φ p))

/-- Differentiating the base L² curve gives the base curve of the
time derivative of the spacetime test. -/
theorem hasDerivAt_transportBase_spacetimeTestH1Slice
    (Φ : Fin m → 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ)) (t : ℝ) :
    HasDerivAt (fun s ↦ transportBaseCLM (spacetimeTestH1Slice Φ s))
      (transportBaseCLM (spacetimeTestH1Slice
        (fun p ↦ TestFunction.lineDerivCLM ℝ (1, 0) (Φ p)) t)) t := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ D)).symm
  have hcoords : HasDerivAt (fun s p ↦ (globalTestFunctionToWkpOn (k := 1) (p := 2) (Ω := univ)
        (TestFunction.sliceRight s (Φ p)) : WkpAmbientOn n 1 2 univ) (baseIndex n 1))
      (fun p ↦ (globalTestFunctionToWkpOn (k := 1) (p := 2) (Ω := univ)
        (TestFunction.sliceRight t (TestFunction.lineDerivCLM ℝ (1, 0) (Φ p))) :
          WkpAmbientOn n 1 2 univ) (baseIndex n 1)) t :=
    hasDerivAt_pi.mpr fun p ↦ hasDerivAt_wkpBase_sliceRight (p := 2) (Ω := univ) (Φ p) t
  have h := e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hcoords
  apply HasDerivAt.of_isLittleO
  exact h.isLittleO

/-- Support strictly before the terminal time makes the terminal spatial test zero,
including every H¹ graph coordinate. -/
theorem spacetimeTestH1Slice_eq_zero_of_support_before (Φ : Fin m → 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ))
    (b : ℝ) (hΦ : ∀ p, tsupport (Φ p) ⊆ {z | z.1 < b}) :
    spacetimeTestH1Slice Φ b = 0 := by
  refine PiLp.ext fun p ↦ ?_
  have hs : TestFunction.sliceRight b (Φ p) = 0 := by
    ext x
    change Φ p (b, x) = 0
    exact image_eq_zero_of_notMem_tsupport fun hx ↦ (lt_irrefl b) (hΦ p hx)
  change globalTestFunctionToWkpOn (k := 1) (p := 2) (Ω := univ)
    (TestFunction.sliceRight b (Φ p)) = 0
  rw [hs]
  exact (globalTestFunctionToWkpOnLinear (n := n) (k := 1) (p := 2) (Ω := univ)).map_zero

end PDE.Hyperbolic.FirstOrder
