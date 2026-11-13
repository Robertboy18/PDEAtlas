/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean.HalfSpace
public import PDE.Spaces.Sobolev.Inequalities.PlanarEmbedding.Representative
public import PDE.Spaces.Sobolev.Weighted.PlanarReflection
import PDE.Spaces.Sobolev.Weighted.DerivativeInterpolation.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Planar Sobolev embedding for reflected functions

The odd reflection gives a continuous representative of a global
`H²` class, so the planar pointwise estimate applies without a classical
second derivative across the axis. For finite products of reflected
functions, the exact `√2` reflection norm controls the nondistinguished
factors; weighted Cauchy–Schwarz controls the remaining pair.

The embedding and representative proofs are in
`PDE.Spaces.Sobolev.Inequalities.PlanarEmbedding.Representative`; we apply them
to the parity reflections and the weighted product certificate.

Throughout, `H₊ = {x : ℝ² | 0 ≤ x₀}` is the closed right half-plane.

## Main results

* `SobolevSpace.oddRadialReflection_swapped_pointwise`: the pointwise bound for the odd
  reflection of a `C²` function vanishing on the axis.
* `SobolevSpace.whole_plane_product_multifactor_from_reflected_H2`: the weighted bound for a
  product of reflected factors against a test function.

## References

* V. Duruisseaux, A. Ganeshram, R. J. George and A. Anandkumar, "Stability Framework for the
  Singularity of the Euler Equations on ℝ³", arXiv:2609.10860v2, Appendix B.4, Proposition 8, (251)
  and (257), for the parity reflection and its exact norm identity, and Appendix B.5, Proposition
  10, (277)-(281), for the Leibniz product bound with `K∞ = 3 / √(2π)`.
  <https://arxiv.org/abs/2609.10860v2>
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open PDE.Common (coordinateClosedHalfSpace)

local notation "H₊" => coordinateClosedHalfSpace (0 : Fin 2)

open MeasureTheory Filter
open PDE.FDeriv
open SobolevSpace.Weighted
open LineDeriv
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap Topology Sobolev

namespace SobolevSpace

/-- Let `A` be a `C²` function on `ℝ²` that vanishes on the axis `{x₀ = 0}` and such that the
derivatives of `A ∘ radialCoordinateSwap2D` through order two are in `L²` of the upper
half-plane. Then the odd radial reflection of `A`, composed with `radialCoordinateSwap2D`, is
almost everywhere the base coordinate of some `V ∈ W^{2,2}(ℝ²)`, and it is bounded at every
point by `(3 / (2√π)) ‖V‖`. No classical second derivative across the axis is assumed.
-/
theorem oddRadialReflection_swapped_pointwise
    (A : (ℝ^2) → ℝ) (hA : ContDiff ℝ 2 A)
    (haxis : ∀ z : ℝ, A (EuclideanSpace.single (1 : Fin 2) z) = 0)
    (hmem : ∀ a : GraphSpace.DerivIndex 2 2,
      MemLp (iteratedPartialDeriv (n := 2) a.toList
        (A ∘ SobolevSpace.Weighted.radialCoordinateSwap2D)) 2
        (domainMeasure 2 (HalfSpace.upper 2))) :
    ∃ V : W^{2,2}(ℝ^2),
      ((((V : GraphSpace.WkpAmbientOn 2 2 2 Set.univ)
        (GraphSpace.baseIndex 2 2)) : (ℝ^2) → ℝ)) =ᵐ[volume]
          ((fun x : (ℝ^2) ↦ if x 0 < 0 then
            -A (SobolevSpace.Weighted.radialSignFlip2D x) else A x) ∘
              SobolevSpace.Weighted.radialCoordinateSwap2D) ∧
      ∀ y : (ℝ^2),
        |((fun x : (ℝ^2) ↦ if x 0 < 0 then
            -A (SobolevSpace.Weighted.radialSignFlip2D x) else A x) ∘
              SobolevSpace.Weighted.radialCoordinateSwap2D) y| ≤
          (3 / (2 * √Real.pi)) * ‖V‖ := by
  obtain ⟨V, hV⟩ := SobolevSpace.Weighted.oddRadialReflection_swapped_globalH2 A hA haxis hmem
  let O : (ℝ^2) → ℝ := fun x ↦ if x 0 < 0 then
    -A (SobolevSpace.Weighted.radialSignFlip2D x) else A x
  let g : (ℝ^2) → ℝ := O ∘ SobolevSpace.Weighted.radialCoordinateSwap2D
  have hA1 : ContDiff ℝ 1 A := hA.of_le (by norm_num)
  have hg : Continuous g := by
    exact ((SobolevSpace.Weighted.contDiff_one_oddRadialReflection A hA1 haxis).comp
      SobolevSpace.Weighted.radialCoordinateSwap2D.contDiff).continuous
  refine ⟨V, hV, ?_⟩
  simpa [g, O] using
    (orderTwoSobolev_pointwise_of_continuous_ae V g hg hV.symm)

/-- The complete reflected multifactor product certificate used in the
energy estimates.  Each non-distinguished factor is a continuous
representative of an even or odd global `H²` reflection.  The proof derives
the `L∞` bound from the whole-plane Sobolev endpoint and the exact `√2`
reflection norm, then applies weighted Cauchy to the distinguished factor and
the test function.

The half-plane bundle norm squared is the six-row sum over derivatives of
orders at most two, giving a factor
`(3 / √(2π)) * sqrt(sum_{|γ|≤2} ‖D^(σ+γ)F‖₂²)` for every non-distinguished
Leibniz factor.
-/
theorem whole_plane_product_multifactor_from_reflected_H2
    {ι : Type*} [Fintype ι]
    (odd : ι → Prop) [DecidablePred odd]
    (coeff Ainf Q : ℝ) (A : (ℝ^2) → ℝ) (F : ι → (ℝ^2) → ℝ)
    (star H Wi Wstar : (ℝ^2) → ℝ)
    (Uhalf : ι → W^{2,2}(SobolevSpace.HalfSpace.upper 2))
    (Ufull : ι → W^{2,2}(ℝ^2))
    (hreflection : ∀ i,
      (Ufull i : SobolevSpace.GraphSpace.WkpAmbientOn 2 2 2 Set.univ) =
        if odd i then
          SobolevSpace.GraphSpace.HigherOrderReflection.oddReflectAmbient
            (n := 2) (m := 2)
            (Uhalf i : SobolevSpace.GraphSpace.WkpAmbientOn 2 2 2
              (SobolevSpace.HalfSpace.upper 2))
        else
          SobolevSpace.GraphSpace.HigherOrderReflection.evenReflectAmbient
            (n := 2) (m := 2)
            (Uhalf i : SobolevSpace.GraphSpace.WkpAmbientOn 2 2 2
              (SobolevSpace.HalfSpace.upper 2)))
    (hFcontinuous : ∀ i, Continuous (F i))
    (hFrep : ∀ i, F i =ᵐ[volume]
      ((((Ufull i : SobolevSpace.GraphSpace.WkpAmbientOn 2 2 2 Set.univ)
        (SobolevSpace.GraphSpace.baseIndex 2 2)) : (ℝ^2) → ℝ)))
    (hcoeff : 0 ≤ coeff) (hAinf : 0 ≤ Ainf) (hQ : 0 ≤ Q)
    (hAbound : ∀ x, |A x| ≤ Ainf)
    (hWi : ∀ x, 0 ≤ Wi x) (hWstar : ∀ x, 0 ≤ Wstar x)
    (hcompare : ∀ x,
      |Wi x| ≤ Q * √(Wstar x) * √(Wi x))
    (hstar : MemLp (fun x ↦ star x * √(Wstar x)) 2
      (volume.restrict H₊))
    (hH : MemLp (fun x ↦ H x * √(Wi x)) 2
      (volume.restrict H₊))
    (hcore : Integrable (fun x ↦ star x * H x * Wi x)
      (volume.restrict H₊))
    (hfull : Integrable
      (fun x ↦ (coeff * A x * ∏ i, F i x) * (star x * H x * Wi x))
      (volume.restrict H₊)) :
    |∫ x, (coeff * A x * ∏ i, F i x) * (star x * H x * Wi x)
        ∂(volume.restrict H₊)| ≤
      coeff * Ainf *
        (∏ i, (3 / √(2 * Real.pi)) *
          √(‖Uhalf i‖ ^ 2)) * Q *
        √(∫ x, star x ^ 2 * Wstar x
          ∂(volume.restrict H₊)) *
        √(∫ x, H x ^ 2 * Wi x
          ∂(volume.restrict H₊)) := by
  have hnormSq (i : ι) : ‖Ufull i‖ ^ 2 = 2 * ‖Uhalf i‖ ^ 2 := by
    change
      ‖(Ufull i : SobolevSpace.GraphSpace.WkpAmbientOn 2 2 2 Set.univ)‖ ^ 2 =
        2 * ‖(Uhalf i : SobolevSpace.GraphSpace.WkpAmbientOn 2 2 2
          (SobolevSpace.HalfSpace.upper 2))‖ ^ 2
    rw [hreflection i]
    split_ifs
    · exact SobolevSpace.GraphSpace.HigherOrderReflection.norm_oddReflectAmbient_sq 2 2 _
    · exact SobolevSpace.GraphSpace.HigherOrderReflection.norm_evenReflectAmbient_sq 2 2 _
  have hFbound (i : ι) (x : ℝ^2) :
      |F i x| ≤ (3 / √(2 * Real.pi)) * √(‖Uhalf i‖ ^ 2) := by
    rw [Real.sqrt_sq (norm_nonneg _), ← SobolevSpace.Weighted.reflectedKInfinity_constant_eq]
    calc |F i x| ≤ (3 / (2 * √Real.pi)) * ‖Ufull i‖ :=
          orderTwoSobolev_pointwise_of_continuous_ae (Ufull i) (F i) (hFcontinuous i) (hFrep i) x
      _ = _ := by
        rw [← Real.sqrt_sq (norm_nonneg (Ufull i)), hnormSq, Real.sqrt_mul (by norm_num),
          Real.sqrt_sq (norm_nonneg _)]
        ring
  exact whole_plane_product_multifactor_certificate
    (μ := volume.restrict H₊)
    coeff Ainf Q (3 / √(2 * Real.pi)) A F
    (fun i ↦ ‖Uhalf i‖ ^ 2) star H Wi Wstar
    hcoeff hAinf hQ (by positivity) hAbound hFbound hWi hWstar hcompare
    hstar hH hcore hfull

end SobolevSpace
