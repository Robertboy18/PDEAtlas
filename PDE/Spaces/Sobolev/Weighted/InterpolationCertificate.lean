/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Weighted.Interpolation

/-!
# Certificates for weighted Sobolev interpolation

A certificate is a stored upper bound for a density-weighted Sobolev gauge.
Two endpoint certificates interpolate to a certificate for every geometrically
interpolated weight.  Eventually finite certificates along a filter are the
form a continuation argument would consume, together with a model-specific
continuation criterion proved elsewhere.

## References

* L. Caffarelli, R. Kohn and L. Nirenberg, "First order interpolation inequalities with weights",
  *Compositio Math.* 53 (1984), no. 3, 259-275, for interpolation inequalities between a function
  and its gradient with power weights `|x|^a`.
  <https://www.numdam.org/item/CM_1984__53_3_259_0/>
* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, 2nd ed., Cambridge Mathematical
  Library, Cambridge University Press, 1988.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology Sobolev

namespace SobolevSpace
namespace Weighted

set_option linter.missingDocs true

/-- A checked upper bound for one extended nonnegative gauge value. -/
abbrev WeightedGaugeCertificate (gauge : ℝ≥0∞) :=
  {upper : ℝ≥0∞ // gauge ≤ upper}

namespace WeightedGaugeCertificate

variable {gauge : ℝ≥0∞}

/-- Certified upper bound. -/
abbrev upper (certificate : WeightedGaugeCertificate gauge) : ℝ≥0∞ :=
  certificate.1

/-- The stored bound dominates the gauge. -/
theorem sound (certificate : WeightedGaugeCertificate gauge) :
    gauge ≤ certificate.upper :=
  certificate.2

/-- Weaken a weighted-gauge certificate to a larger upper bound. -/
def weaken (certificate : WeightedGaugeCertificate gauge)
    {upper : ℝ≥0∞} (hupper : certificate.upper ≤ upper) :
    WeightedGaugeCertificate gauge :=
  ⟨upper, certificate.sound.trans hupper⟩

/-- A finite certificate proves that the gauge itself is finite. -/
theorem gauge_ne_top (certificate : WeightedGaugeCertificate gauge)
    (hfinite : certificate.upper ≠ ⊤) :
    gauge ≠ ⊤ :=
  ne_top_of_le_ne_top hfinite certificate.sound

/-- A finite extended upper certificate gives the corresponding real-valued
bound. -/
theorem toReal_le (certificate : WeightedGaugeCertificate gauge)
    (hfinite : certificate.upper ≠ ⊤) :
    gauge.toReal ≤ certificate.upper.toReal :=
  ENNReal.toReal_mono hfinite certificate.sound

end WeightedGaugeCertificate

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- Upper certificate for a finite derivative-family weighted power gauge. -/
abbrev DerivativeFamilyGaugeCertificate
    (q : ℝ) (density : ℝ^n → ℝ≥0∞)
    (family : Finset (GraphSpace.DerivIndex n k))
    (U : W^{k,p}(Ω)) :=
  WeightedGaugeCertificate
    (derivativeFamilyPowerGaugeWithDensity q density family U)

namespace DerivativeFamilyGaugeCertificate

/-- Interpolate two endpoint weighted-gauge certificates. -/
def interpolate
    {q θ : ℝ} {w₀ w₁ : ℝ^n → ℝ≥0∞}
    (hq : 0 < q)
    (family : Finset (GraphSpace.DerivIndex n k))
    (U : W^{k,p}(Ω))
    (left : DerivativeFamilyGaugeCertificate q w₀ family U)
    (right : DerivativeFamilyGaugeCertificate q w₁ family U)
    (hw₀ : AEMeasurable w₀ (domainMeasure n Ω))
    (hw₁ : AEMeasurable w₁ (domainMeasure n Ω))
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    DerivativeFamilyGaugeCertificate q
      (geometricDensity θ w₀ w₁) family U :=
  ⟨left.upper ^ (1 - θ) * right.upper ^ θ, by
      refine
        (derivativeFamilyPowerGaugeWithDensity_geometricDensity_le
          hq family U hw₀ hw₁ hθ₀ hθ₁).trans ?_
      exact mul_le_mul'
        (ENNReal.rpow_le_rpow left.sound (sub_nonneg.mpr hθ₁))
        (ENNReal.rpow_le_rpow right.sound hθ₀)⟩

end DerivativeFamilyGaugeCertificate

/-- Upper certificate for the complete weighted Sobolev graph gauge. -/
abbrev SobolevGaugeCertificate
    (q : ℝ) (density : ℝ^n → ℝ≥0∞)
    (U : W^{k,p}(Ω)) :=
  WeightedGaugeCertificate
    (derivativeFamilyPowerGaugeWithDensity q density Finset.univ U)

namespace SobolevGaugeCertificate

/-- Interpolate complete weighted Sobolev graph certificates. -/
def interpolate
    {q θ : ℝ} {w₀ w₁ : ℝ^n → ℝ≥0∞}
    (hq : 0 < q)
    (U : W^{k,p}(Ω))
    (left : SobolevGaugeCertificate q w₀ U)
    (right : SobolevGaugeCertificate q w₁ U)
    (hw₀ : AEMeasurable w₀ (domainMeasure n Ω))
    (hw₁ : AEMeasurable w₁ (domainMeasure n Ω))
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    SobolevGaugeCertificate q (geometricDensity θ w₀ w₁) U :=
  DerivativeFamilyGaugeCertificate.interpolate
    hq Finset.univ U left right hw₀ hw₁ hθ₀ hθ₁

end SobolevGaugeCertificate

/-- Upper certificate for a weighted anisotropic derivative-budget gauge. -/
abbrev AnisotropicGaugeCertificate
    (q : ℝ) (density : ℝ^n → ℝ≥0∞)
    (cost : Fin n → ℕ) (budget : ℕ)
    (U : W^{k,p}(Ω)) :=
  WeightedGaugeCertificate
    (derivativeFamilyPowerGaugeWithDensity q density
      (anisotropicDerivativeFamily cost budget) U)

namespace AnisotropicGaugeCertificate

/-- Interpolate weighted anisotropic derivative-budget certificates. -/
def interpolate
    {q θ : ℝ} {w₀ w₁ : ℝ^n → ℝ≥0∞}
    (hq : 0 < q)
    (cost : Fin n → ℕ) (budget : ℕ)
    (U : W^{k,p}(Ω))
    (left : AnisotropicGaugeCertificate q w₀ cost budget U)
    (right : AnisotropicGaugeCertificate q w₁ cost budget U)
    (hw₀ : AEMeasurable w₀ (domainMeasure n Ω))
    (hw₁ : AEMeasurable w₁ (domainMeasure n Ω))
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    AnisotropicGaugeCertificate q
      (geometricDensity θ w₀ w₁) cost budget U :=
  DerivativeFamilyGaugeCertificate.interpolate
    hq (anisotropicDerivativeFamily cost budget) U
    left right hw₀ hw₁ hθ₀ hθ₁

end AnisotropicGaugeCertificate

/-- An eventual finite upper bound for an extended nonnegative gauge along a
filter.

The upper bound is stored in `NNReal`, rather than as an extended nonnegative
real with a separate finiteness proof. Thus finiteness is enforced by the
type and cannot become inconsistent with the numerical bound. -/
abbrev EventualFiniteGaugeCertificate
    (gauge : ℝ → ℝ≥0∞) (l : Filter ℝ) :=
  {upper : NNReal // ∀ᶠ t in l, gauge t ≤ (upper : ℝ≥0∞)}

namespace EventualFiniteGaugeCertificate

variable {gauge : ℝ → ℝ≥0∞} {l : Filter ℝ}

/-- Eventual upper bound. -/
abbrev upper
    (certificate : EventualFiniteGaugeCertificate gauge l) : NNReal :=
  certificate.1

/-- The gauge is eventually below the upper bound. -/
theorem sound
    (certificate : EventualFiniteGaugeCertificate gauge l) :
    ∀ᶠ t in l, gauge t ≤ (certificate.upper : ℝ≥0∞) :=
  certificate.2

/-- The extended-real view of the stored upper bound is finite. -/
theorem upper_ne_top
    (certificate : EventualFiniteGaugeCertificate gauge l) :
    (certificate.upper : ℝ≥0∞) ≠ ⊤ :=
  ENNReal.coe_ne_top

/-- An eventual finite extended bound gives an eventual real-valued bound. -/
theorem eventually_toReal_le
    (certificate : EventualFiniteGaugeCertificate gauge l) :
    ∀ᶠ t in l, (gauge t).toReal ≤ (certificate.upper : ℝ) := by
  filter_upwards [certificate.sound] with t ht
  exact ENNReal.toReal_le_coe_of_le_coe ht

/-- Interpolate two eventual endpoint certificates for a trajectory in one
Sobolev graph space. -/
def interpolateDerivativeFamily
    {q θ : ℝ} {w₀ w₁ : ℝ^n → ℝ≥0∞}
    {family : Finset (GraphSpace.DerivIndex n k)}
    {trajectory : ℝ → W^{k,p}(Ω)}
    (hq : 0 < q)
    (left :
      EventualFiniteGaugeCertificate
        (fun t ↦
          derivativeFamilyPowerGaugeWithDensity q w₀ family
            (trajectory t)) l)
    (right :
      EventualFiniteGaugeCertificate
        (fun t ↦
          derivativeFamilyPowerGaugeWithDensity q w₁ family
            (trajectory t)) l)
    (hw₀ : AEMeasurable w₀ (domainMeasure n Ω))
    (hw₁ : AEMeasurable w₁ (domainMeasure n Ω))
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    EventualFiniteGaugeCertificate
      (fun t ↦
        derivativeFamilyPowerGaugeWithDensity q
          (geometricDensity θ w₀ w₁) family (trajectory t)) l :=
  ⟨(((left.upper : ℝ≥0∞) ^ (1 - θ)) *
      ((right.upper : ℝ≥0∞) ^ θ)).toNNReal,
    by
      have hupper_ne_top :
          ((left.upper : ℝ≥0∞) ^ (1 - θ)) *
              ((right.upper : ℝ≥0∞) ^ θ) ≠ ⊤ :=
        ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg
            (sub_nonneg.mpr hθ₁) ENNReal.coe_ne_top)
          (ENNReal.rpow_ne_top_of_nonneg hθ₀ ENNReal.coe_ne_top)
      filter_upwards [left.sound, right.sound] with t hleft hright
      refine
        (derivativeFamilyPowerGaugeWithDensity_geometricDensity_le
          hq family (trajectory t) hw₀ hw₁ hθ₀ hθ₁).trans ?_
      rw [ENNReal.coe_toNNReal hupper_ne_top]
      exact mul_le_mul'
        (ENNReal.rpow_le_rpow hleft (sub_nonneg.mpr hθ₁))
        (ENNReal.rpow_le_rpow hright hθ₀)⟩

end EventualFiniteGaugeCertificate

end Weighted
end SobolevSpace
