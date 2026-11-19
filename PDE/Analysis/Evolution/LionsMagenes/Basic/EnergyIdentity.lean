/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.PivotDerivative
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import PDE.Analysis.Evolution.LionsMagenes.Basic.IntegratedDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import PDE.Analysis.Evolution.Core.EnergyIdentity
import PDE.Analysis.Evolution.LionsMagenes.Basic.Continuity

/-!
# Energy identities for integrated Gelfand evolutions

Energy identities for absolutely continuous Hilbert-space trajectories and
for integrated dual evolutions whose derivative has a pivot-space
representative. The time-regularization argument needed for the full
Lions–Magenes theorem is in `RegularizedEnergy`.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped InnerProductSpace Interval Topology

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

section AbsolutelyContinuousEnergy

/-- Energy identity for an absolutely continuous Hilbert-space trajectory
with an almost-everywhere strong derivative.  This is the nonsmooth version
of `hasDerivAt_half_norm_sq` used inside the Lions–Magenes approximation
argument. -/
theorem absolutelyContinuous_energy_identity
    {w dw : ℝ → H} {a b : ℝ}
    (hw : AbsolutelyContinuousOnInterval w a b)
    (hderiv : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt w (dw t) t) :
    ‖w b‖ ^ 2 - ‖w a‖ ^ 2 =
      ∫ t in a..b, 2 * inner ℝ (dw t) (w t) := by
  have henergyAC :=
    absolutelyContinuousOnInterval_norm_sq hw
  calc
    ‖w b‖ ^ 2 - ‖w a‖ ^ 2 =
        ∫ t in a..b, deriv (fun s ↦ ‖w s‖ ^ 2) t :=
      henergyAC.integral_deriv_eq_sub.symm
    _ = ∫ t in a..b, 2 * inner ℝ (dw t) (w t) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hderiv] with t ht htI
      have htI' : t ∈ uIcc a b := uIoc_subset_uIcc htI
      have hhalf := hasDerivAt_half_norm_sq (ht htI')
      have hfull : HasDerivAt (fun s ↦ ‖w s‖ ^ 2)
          (2 * inner ℝ (dw t) (w t)) t := by
        exact (hhalf.const_mul 2).congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun s ↦ by ring)
      exact hfull.deriv

/-- Gelfand-triple form of the absolutely continuous energy identity.  If
`g(t) ∈ V*` is represented by the pivot derivative `duH(t)`, the Hilbert
pairing in the energy law is exactly the duality pairing `g(t)(u(t))`. -/
theorem gelfand_absolutelyContinuous_energy_identity
    (T : GelfandTriple (V := V) (H := H))
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V} {duH : ℝ → H} {a b : ℝ}
    (huAC : AbsolutelyContinuousOnInterval
      (fun t ↦ T.inclusion (u t)) a b)
    (hderiv : ∀ᵐ t, t ∈ uIcc a b →
      HasDerivAt (fun s ↦ T.inclusion (u s)) (duH t) t)
    (hrep : ∀ᵐ t, t ∈ uIcc a b →
      RepresentsPivotDerivative T (g t) (duH t)) :
    ‖T.inclusion (u b)‖ ^ 2 - ‖T.inclusion (u a)‖ ^ 2 =
      2 * ∫ t in a..b, g t (u t) := by
  have henergy := absolutelyContinuous_energy_identity huAC hderiv
  calc
    ‖T.inclusion (u b)‖ ^ 2 - ‖T.inclusion (u a)‖ ^ 2 =
        ∫ t in a..b, 2 * inner ℝ (duH t) (T.inclusion (u t)) := henergy
    _ = ∫ t in a..b, 2 * g t (u t) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hrep] with t ht htI
      exact congrArg (2 * ·) (ht (uIoc_subset_uIcc htI) (u t)).symm
    _ = 2 * ∫ t in a..b, g t (u t) :=
      intervalIntegral.integral_const_mul 2 _

/-- Energy identity obtained directly from an integrated `V*` evolution when
the derivative is represented by an integrable pivot-space velocity.  This
states the strong-derivative case with the same data as weak evolution
equations. -/
theorem integrated_pivotDerivative_energy_identity
    [CompleteSpace H]
    (T : GelfandTriple (V := V) (H := H))
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V} {duH : ℝ → H} {a b : ℝ}
    (hint : HasIntegratedDualDerivativeOn T
      (fun t ↦ T.inclusion (u t)) g a b)
    (hduH : IntervalIntegrable duH volume a b)
    (hrep : ∀ t ∈ uIcc a b,
      RepresentsPivotDerivative T (g t) (duH t))
    (hderiv : ∀ᵐ t, t ∈ uIcc a b →
      HasDerivAt (fun s ↦ T.inclusion (u s)) (duH t) t) :
    ‖T.inclusion (u b)‖ ^ 2 - ‖T.inclusion (u a)‖ ^ 2 =
      2 * ∫ t in a..b, g t (u t) := by
  apply gelfand_absolutelyContinuous_energy_identity T
  · exact hint.absolutelyContinuousOnInterval_of_pivotDerivative duH hduH hrep
  · exact hderiv
  · filter_upwards with t
    exact fun ht ↦ hrep t ht

end AbsolutelyContinuousEnergy

end PDE.Analysis.Evolution
