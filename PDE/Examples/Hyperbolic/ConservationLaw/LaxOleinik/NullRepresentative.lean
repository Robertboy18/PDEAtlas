/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Hyperbolic.ConservationLaw.LaxOleinik.AffineFlux
public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Representation

/-!
# A null change of a rough initial representative

An arbitrarily large value at one point changes neither the integral primitive
nor the selected footpoint solution. The datum hypothesis of the
Lax–Oleinik theorem is essential boundedness, without a pointwise bound on the
chosen representative.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Hyperbolic.ConservationLaw
open PDE.Hyperbolic.ConservationLaw.LaxOleinik
open scoped ENNReal

namespace PDE.Examples.ConservationLaw.LaxOleinik

/-- Replace the value at one point of the two-jump, nondecaying datum. -/
def spikedDatum (A x : ℝ) : ℝ :=
  if x = 0 then A else roughDatum x

/-- The spiked datum equals `roughDatum` almost everywhere. -/
theorem spikedDatum_ae_eq (A : ℝ) : spikedDatum A =ᵐ[volume] roughDatum := by
  filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
  simp only [spikedDatum, ite_eq_right hx]

/-- The spiked datum is essentially bounded. -/
theorem spikedDatum_memLp (A : ℝ) : MemLp (spikedDatum A) ∞ volume :=
  roughDatum_memLp.ae_eq (spikedDatum_ae_eq A).symm

/-- Null changes preserve the selected solution pointwise, not just almost
everywhere, because they preserve its primitive. -/
theorem spikedDatum_solution_eq (A : ℝ) :
    solution (affineQuadraticFlux 2 (-3)) (spikedDatum A) =
      solution (affineQuadraticFlux 2 (-3)) roughDatum :=
  solution_congr_ae (spikedDatum_ae_eq A)

/-- For every spike height `A`, the Lax–Oleinik solution with the spiked datum is an
essentially bounded weak solution. -/
theorem spikedDatum_solution (A : ℝ) :
    IsWeakInitialValueSolution (affineQuadraticFlux 2 (-3)) (spikedDatum A)
      (solution (affineQuadraticFlux 2 (-3)) (spikedDatum A)) ∧
      MemLp (solution (affineQuadraticFlux 2 (-3)) (spikedDatum A)) ∞ volume :=
  affineQuadraticFlux_solution 2 (-3) (spikedDatum_memLp A)

end PDE.Examples.ConservationLaw.LaxOleinik
