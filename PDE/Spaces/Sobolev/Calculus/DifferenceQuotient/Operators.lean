/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Pointwise
public import PDE.Spaces.Sobolev.Compactness.Translation.H1

/-!
# Bundled difference-quotient operators

The forward difference quotient in direction `eᵢ` with step `h ≠ 0`,

`Dᵢʰ u (x) = (u (x + h eᵢ) - u x) / h`,

as a bounded operator on global `Lᵖ(ℝ^n)` and on the complete `H¹(ℝ^n)` derivative bundle.
Both are built from the translation operators of `Compactness.Translation`: the quotient is
`h⁻¹ (τ_{h eᵢ} - id)`, so on the `H¹` bundle every weak derivative coordinate is differenced
in the same way as the function itself. The elementary bound `‖Dᵢʰ U‖ ≤ 2|h|⁻¹ ‖U‖` recorded
here is only what follows from translation invariance; the `h`-uniform estimate
`‖Dᵢʰ u‖_{L²} ≤ ‖∂ᵢu‖_{L²}` (compare Evans, §5.8.2, Theorem 3(i)) is proved in
`DifferenceQuotient.WeakDerivative`.

## Main results

* `differenceQuotientLp`, `differenceQuotientLp_apply_ae`: the `Lᵖ` operator and its a.e.
  representative `x ↦ h⁻¹ (u (x + h eᵢ) - u x)`.
* `differenceQuotientH1`, `differenceQuotientH1_coordinate`: the `H¹` bundle operator, acting
  coordinatewise as the `L²` operator.
* `norm_differenceQuotientH1_le`: the crude bound `2 |h|⁻¹ ‖U‖`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.2, Theorem 3, pp. 291-293, for the estimate
  `‖D^h u‖_{Lᵖ(V)} ≤ C ‖Du‖_{Lᵖ(U)}` and its converse for `1 < p < ∞`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open MeasureTheory Set Function
open scoped ENNReal Topology InnerProductSpace RealInnerProductSpace
open SobolevSpace.GraphSpace.Rellich

variable {n : ℕ}

/-- Forward coordinate difference quotient on global `Lᵖ(ℝ^n)`. -/
noncomputable def differenceQuotientLp (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (i : Fin n) (h : ℝ) :
    DerivLp n p Set.univ →L[ℝ] DerivLp n p Set.univ :=
  h⁻¹ • ((translateLp p (coordinateStep i h)).toContinuousLinearMap -
    ContinuousLinearMap.id ℝ (DerivLp n p Set.univ))

/-- Coordinate difference quotient on the complete global `H¹` derivative
bundle.  Every represented weak derivative is translated and differenced in
the same way. -/
noncomputable def differenceQuotientH1 (i : Fin n) (h : ℝ) :
    H¹(ℝ^n) →L[ℝ] H¹(ℝ^n) :=
  h⁻¹ • (translateH1 (n := n) (coordinateStep i h) -
    ContinuousLinearMap.id ℝ (H¹(ℝ^n)))

/-- Unfolding lemma: the `H¹` difference quotient is `h⁻¹ (τ_{h eᵢ} U - U)`. -/
@[simp]
theorem differenceQuotientH1_apply (i : Fin n) (h : ℝ)
    (U : H¹(ℝ^n)) :
    differenceQuotientH1 i h U =
      h⁻¹ • (translateH1 (n := n) (coordinateStep i h) U - U) := by
  rfl

/-- Every coordinate of the `H¹` difference quotient is the corresponding
`L²` difference quotient. -/
theorem differenceQuotientH1_coordinate (i : Fin n) (h : ℝ)
    (U : H¹(ℝ^n)) (q : DerivIndex n 1) :
    (((differenceQuotientH1 i h U : H¹(ℝ^n)) :
      WkpAmbientOn n 1 2 Set.univ) q) =
      differenceQuotientLp 2 i h ((U : WkpAmbientOn n 1 2 Set.univ) q) := by
  simp [differenceQuotientH1_apply, differenceQuotientLp, translateH1_apply]

/-- A full-bundle difference quotient has the elementary bound
`‖D_i^h U‖_{H¹} ≤ 2 |h|⁻¹ ‖U‖_{H¹}`.  The sharper uniform estimate used for
the base coordinate is proved separately from the weak equation. -/
theorem norm_differenceQuotientH1_le (i : Fin n) (h : ℝ)
    (U : H¹(ℝ^n)) :
    ‖differenceQuotientH1 i h U‖ ≤ 2 * |h|⁻¹ * ‖U‖ := by
  rw [differenceQuotientH1_apply, norm_smul, Real.norm_eq_abs, abs_inv]
  calc
    |h|⁻¹ * ‖translateH1 (n := n) (coordinateStep i h) U - U‖
        ≤ |h|⁻¹ *
            (‖translateH1 (n := n) (coordinateStep i h) U‖ + ‖U‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr (abs_nonneg h))
    _ = 2 * |h|⁻¹ * ‖U‖ := by rw [norm_translateH1]; ring

/-- Unfolding lemma for the `L²` difference quotient. -/
theorem differenceQuotientL2_apply (i : Fin n) (h : ℝ)
    (u : DerivLp n 2 Set.univ) :
    differenceQuotientLp 2 i h u =
      h⁻¹ • (translateLp 2 (coordinateStep i h) u - u) := by
  rfl

/-- Unfolding lemma: the `Lᵖ` difference quotient is `h⁻¹ (τ_{h eᵢ} u - u)`. -/
@[simp]
theorem differenceQuotientLp_apply (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (i : Fin n) (h : ℝ) (u : DerivLp n p Set.univ) :
    differenceQuotientLp p i h u =
      h⁻¹ • (translateLp p (coordinateStep i h) u - u) := by
  rfl

/-- An `Lᵖ` difference quotient has its expected representative almost
everywhere. -/
theorem differenceQuotientLp_apply_ae (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (i : Fin n) (h : ℝ) (u : DerivLp n p Set.univ) :
    ((differenceQuotientLp p i h u : DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[MeasureTheory.volume]
        fun x ↦ h⁻¹ * (u (x + coordinateStep i h) - u x) := by
  have htrans :
      (((translateLp p (coordinateStep i h) u - u : DerivLp n p Set.univ) :
          ℝ^n → ℝ)) =ᵐ[MeasureTheory.volume]
        fun x ↦ u (x + coordinateStep i h) - u x := by
    have ht := translateLp_apply_ae (n := n) p (coordinateStep i h) u
    have hs := MeasureTheory.Lp.coeFn_sub
      (translateLp p (coordinateStep i h) u) u
    have hsvol :
        (((translateLp p (coordinateStep i h) u - u :
          DerivLp n p Set.univ) : ℝ^n → ℝ)) =ᵐ[MeasureTheory.volume]
            ((translateLp p (coordinateStep i h) u : ℝ^n → ℝ) -
              (u : ℝ^n → ℝ)) := by
      simpa only [domainMeasure, Measure.restrict_univ] using hs
    have hs' :
        (((translateLp p (coordinateStep i h) u - u :
          DerivLp n p Set.univ) : ℝ^n → ℝ)) =ᵐ[MeasureTheory.volume]
            fun x ↦ translateLp p (coordinateStep i h) u x - u x := by
      filter_upwards [hsvol] with x hx
      simpa only [Pi.sub_apply] using hx
    filter_upwards [show
        ((translateLp p (coordinateStep i h) u : DerivLp n p Set.univ) :
          ℝ^n → ℝ) =ᵐ[MeasureTheory.volume]
            fun x ↦ u (x + coordinateStep i h) by
          simpa [domainMeasure] using ht,
      hs'] with x htx hsx
    rw [hsx, htx]
  have hsmul :
      (((h⁻¹ • (translateLp p (coordinateStep i h) u - u) :
          DerivLp n p Set.univ) : ℝ^n → ℝ)) =ᵐ[MeasureTheory.volume]
        h⁻¹ • (((translateLp p (coordinateStep i h) u - u :
          DerivLp n p Set.univ) : ℝ^n → ℝ)) := by
    simpa using MeasureTheory.Lp.coeFn_smul h⁻¹
      (translateLp p (coordinateStep i h) u - u)
  filter_upwards [hsmul, htrans] with x hsmulx hsub
  rw [differenceQuotientLp_apply, hsmulx]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hsub]

/-- `L²` specialization of the general representative theorem. -/
theorem differenceQuotientL2_apply_ae (i : Fin n) (h : ℝ)
    (u : DerivLp n 2 Set.univ) :
    ((differenceQuotientLp 2 i h u : DerivLp n 2 Set.univ) : ℝ^n → ℝ)
      =ᵐ[MeasureTheory.volume]
        fun x ↦ h⁻¹ * (u (x + coordinateStep i h) - u x) :=
  differenceQuotientLp_apply_ae (n := n) 2 i h u
end SobolevSpace.GraphSpace.DifferenceQuotient
