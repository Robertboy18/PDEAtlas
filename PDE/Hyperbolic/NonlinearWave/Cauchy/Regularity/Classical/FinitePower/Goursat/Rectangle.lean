/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.Integration
import CAS.ExactTactic

/-!
# Integration on characteristic rectangles

Restriction, pullback and bounded integration on compact rectangles define the characteristic
integral operator and its descent to the plane.
-/

@[expose] public noncomputable section

section

open Set MeasureTheory BoundedContinuousFunction
open WaveEquation.SmallData.Classical.LocalPower
open scoped unitInterval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- The fixed normalized characteristic rectangle. -/
abbrev Rectangle := I × I

/-- Multiplication of both normalized characteristic coordinates. -/
def descend (q r : Rectangle) : Rectangle := (q.1 * r.1, q.2 * r.2)

/-- Restriction coordinates depend continuously on both rectangle points. -/
theorem continuous_descend : Continuous (fun z : Rectangle × Rectangle ↦ descend z.1 z.2) :=
  (continuous_fst.fst.mul continuous_snd.fst).prodMk (continuous_fst.snd.mul continuous_snd.snd)

/-- Successive rectangle restrictions associate. -/
theorem descend_assoc (q r s : Rectangle) : descend (descend q r) s = descend q (descend r s) :=
  Prod.ext (mul_assoc _ _ _) (mul_assoc _ _ _)

/-- Restriction to a normalized subrectangle as a bounded linear map. -/
def restrictRectangle (q : Rectangle) : (Rectangle →ᵇ ℝ) →L[ℝ] (Rectangle →ᵇ ℝ) :=
  compContinuousCLM ℝ ℝ
    ⟨descend q, continuous_descend.comp (continuous_const.prodMk continuous_id)⟩

/-- The rectangle restriction is literal precomposition. -/
@[simp] theorem restrictRectangle_apply (q : Rectangle) (f : Rectangle →ᵇ ℝ) (r : Rectangle) :
    restrictRectangle q f r = f (descend q r) := rfl

/-- Restriction does not enlarge the uniform norm. -/
theorem norm_restrictRectangle_le (q : Rectangle) (f : Rectangle →ᵇ ℝ) :
    ‖restrictRectangle q f‖ ≤ ‖f‖ := norm_compContinuous_le _ _

/-- Pull a rectangle field back to the two integration parameters. -/
def rectangularPullback :
    (Rectangle →ᵇ ℝ) →L[ℝ] (((Rectangle × I) × I) →ᵇ ℝ) :=
  compContinuousCLM ℝ ℝ ⟨fun z ↦ descend z.1.1 (z.1.2, z.2),
    continuous_descend.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))⟩

/-- The product of the normalized characteristic side lengths. -/
def areaWeight : Rectangle →ᵇ ℝ :=
  mkOfCompact ⟨fun q ↦ (q.1 : ℝ) * (q.2 : ℝ),
    (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)⟩

/-- Oriented double integration after rescaling to the fixed unit rectangle. -/
def rectangularOperator : (Rectangle →ᵇ ℝ) →L[ℝ] (Rectangle →ᵇ ℝ) :=
  ((ContinuousLinearMap.mul ℝ (Rectangle →ᵇ ℝ)) areaWeight).comp
    ((partialIntegralCLM (volume : Measure I)).comp
      ((partialIntegralCLM (volume : Measure I)).comp rectangularPullback))

/-- The bounded operator evaluates to the ordinary iterated unit-interval integral. -/
theorem rectangularOperator_apply (f : Rectangle →ᵇ ℝ) (q : Rectangle) :
    rectangularOperator f q = (q.1 : ℝ) * (q.2 : ℝ) * ∫ s : I, ∫ t : I, f (descend q (s, t)) := by
  simp only [rectangularOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply', BoundedContinuousFunction.mul_apply,
    partialIntegralCLM_apply, areaWeight, mkOfCompact_apply, ContinuousMap.coe_mk,
    rectangularPullback, compContinuousCLM_apply, compContinuous_apply]

/-- Rectangle restriction extracts the two side-length factors. -/
theorem rectangularOperator_descend (q r : Rectangle) (f : Rectangle →ᵇ ℝ) :
    rectangularOperator f (descend q r) = (q.1 : ℝ) * (q.2 : ℝ) *
      rectangularOperator (restrictRectangle q f) r := by
  simp only [rectangularOperator_apply, descend_assoc, restrictRectangle_apply]
  change ((q.1 : ℝ) * (r.1 : ℝ)) * ((q.2 : ℝ) * (r.2 : ℝ)) * _ = _
  generalize (∫ s : I, ∫ t : I, f (descend q (descend r (s, t)))) = J
  cas

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end
