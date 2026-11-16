/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Sobolev.ContinuousRepresentative
public import PDE.Analysis.Fourier.HilbertTransform.RealPair.PrincipalValue
public import PDE.Spaces.Sobolev.Calculus.Slicing.LineRepresentative.ContinuousDerivative
import PDE.Analysis.Fourier.HilbertTransform.RealPair.Derivative

/-!
# Classical derivatives of the Hilbert velocity

Weak differentiation identifies the second classical derivative of the normalized
Hilbert velocity almost everywhere. The input need only be compact and Lipschitz:
corners at the support endpoints are permitted. This is a case of
`IsHilbertPair.deriv_of_weak`, the derivative of a Hilbert pair in weak form.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace PDE.Analysis

/-- The second velocity derivative is the Hilbert transform of the
almost-everywhere classical vorticity derivative, including for compact
Lipschitz inputs with endpoint slope jumps. -/
theorem isHilbertPair_deriv_deriv_hilbertPVVelocity_of_lipschitzWith_compactSupport
    {q : ℝ → ℝ} {K : ℝ≥0} (hq : LipschitzWith K q) (hc : HasCompactSupport q) :
    IsHilbertPair (deriv q) (deriv (deriv (hilbertPVVelocity q))) :=
  (isHilbertPair_deriv_hilbertPVVelocity_of_lipschitzWith_compactSupport hq hc).deriv_of_weak
    (Calculus.memLp_deriv_of_lipschitzWith_compactSupport hq hc 2)
    (Calculus.hasWeakTimeDerivativeOn_of_lipschitzWith_compactSupport hq hc)
    ((contDiff_one_hilbertPVVelocity_of_lipschitzWith_compactSupport hq hc).continuous_deriv le_rfl)

/-- Additivity of the normalized velocity for compact Lipschitz inputs. -/
theorem hilbertPVVelocity_add_of_lipschitzWith_compactSupport
    {f q : ℝ → ℝ} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hfc : HasCompactSupport f)
    (hq : LipschitzWith J q) (hqc : HasCompactSupport q) :
    hilbertPVVelocity (fun x ↦ f x + q x) =
      fun x ↦ hilbertPVVelocity f x + hilbertPVVelocity q x := by
  have hp (x : ℝ) : hilbertPV (fun y ↦ f y + q y) x = hilbertPV f x + hilbertPV q x :=
    ((hasHilbertPV_of_lipschitzWith_compactSupport hf hfc x).add
      (hasHilbertPV_of_lipschitzWith_compactSupport hq hqc x)).hilbertPV_eq
  funext x
  simp only [hilbertPVVelocity, hp]
  exact intervalIntegral.integral_add
    ((continuous_hilbertPV_of_lipschitzWith_compactSupport hf hfc).intervalIntegrable 0 x)
    ((continuous_hilbertPV_of_lipschitzWith_compactSupport hq hqc).intervalIntegrable 0 x)

end PDE.Analysis
