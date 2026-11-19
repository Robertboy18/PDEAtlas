/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.Congruence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Coordinate reflection and almost-everywhere mollification

Convolution depends only on the almost-everywhere class of each factor. If the kernel is
invariant under a coordinate reflection, mollification commutes with that reflection and sends
almost-everywhere even functions to pointwise even functions. Thus an arbitrary representative
of an even Sobolev function produces even smooth tests.

Only symmetry in the selected coordinate is required of the kernel. Radiality implies this
condition, whereas symmetry under simultaneous negation of all coordinates does not.
-/

@[expose] public noncomputable section

open MeasureTheory Filter PDE.Common
open scoped Convolution

namespace SobolevSpace.Approximation

variable {n : ℕ}

/-- Mollification commutes with a coordinate reflection when the kernel is invariant under
that reflection. The input function need not be continuous or integrable. -/
theorem mollify_comp_coordinateReflection (μ : Mollifier n) (i : Fin n)
    (hμ : IsEvenUnderCoordinateReflection i μ.ρ) {ε : ℝ} (hε : 0 < ε)
    (f : ℝ^n → ℝ) :
    mollify μ ε (f ∘ coordinateReflection i) =
      mollify μ ε f ∘ coordinateReflection i := by
  have hscaled (y : ℝ^n) :
      scaled μ ε (coordinateReflection i y) = scaled μ ε y := by
    rw [scaled_of_pos μ hε]
    simpa only [coordinateReflection, map_smul] using
      congrArg (fun r : ℝ ↦ ε⁻¹ ^ n * r) (hμ (ε⁻¹ • y))
  funext x
  symm
  calc
    mollify μ ε f (coordinateReflection i x) =
        ∫ y, scaled μ ε (coordinateReflection i y) *
          f (coordinateReflection i x - coordinateReflection i y) := by
      simpa only [mollify, convolution_lsmul, smul_eq_mul, coordinateReflection] using
        (integral_comp (coordinateReflectionLinearIsometryEquiv i)
          (fun y ↦ scaled μ ε y * f (coordinateReflection i x - y))).symm
    _ = mollify μ ε (f ∘ coordinateReflection i) x := by
      change (∫ y, _) = ∫ y, scaled μ ε y * f (coordinateReflection i (x - y))
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hscaled, coordinateReflection_sub]

/-- Almost-everywhere evenness becomes pointwise evenness after convolution with a kernel
even in the same coordinate. The conclusion includes the reflecting hyperplane. -/
theorem mollify_even_of_ae (μ : Mollifier n) (i : Fin n)
    (hμ : IsEvenUnderCoordinateReflection i μ.ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ^n → ℝ} (hf : f ∘ coordinateReflection i =ᵐ[volume] f) :
    IsEvenUnderCoordinateReflection i (mollify μ ε f) := by
  have h := mollify_congr_ae μ ε hf
  rw [mollify_comp_coordinateReflection μ i hμ hε f] at h
  exact congrFun h

/-- A representative agreeing almost everywhere with an even profile has pointwise even
mollification. In particular, no pointwise symmetry of an `Lᵖ` representative is assumed. -/
theorem mollify_even_of_ae_eq (μ : Mollifier n) (i : Fin n)
    (hμ : IsEvenUnderCoordinateReflection i μ.ρ) {ε : ℝ} (hε : 0 < ε)
    {f g : ℝ^n → ℝ} (hfg : f =ᵐ[volume] g)
    (hg : IsEvenUnderCoordinateReflection i g) :
    IsEvenUnderCoordinateReflection i (mollify μ ε f) := by
  rw [mollify_congr_ae μ ε hfg]
  exact mollify_even_of_ae μ i hμ hε (Eventually.of_forall hg)

end SobolevSpace.Approximation
