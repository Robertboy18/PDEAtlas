/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import PDE.Analysis.Integration.SingularEndpoints

/-!
# Weighted square integration by parts

Interval and half-line identities for arbitrary scalar fields and weights.
The boundary products and all integrability assumptions are explicit.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open Asymptotics
open scoped Topology

namespace SobolevSpace
namespace Weighted

set_option linter.missingDocs true

/-- Weighted square energy on an open bounded interval. -/
def weightedSquareEnergy
    (a b : ℝ) (weight field : ℝ → ℝ) : ℝ :=
  ∫ x in Ioo a b, weight x * field x ^ 2

/-- Primitive-field cross term on an open bounded interval. -/
def weightedPrimitiveCross
    (a b : ℝ) (primitive field fieldDerivative : ℝ → ℝ) : ℝ :=
  ∫ x in Ioo a b, primitive x * field x * fieldDerivative x

/-- Weighted square energy on the half-line `(a, ∞)`. -/
def weightedSquareEnergyIoi
    (a : ℝ) (weight field : ℝ → ℝ) : ℝ :=
  ∫ x in Ioi a, weight x * field x ^ 2

/-- Primitive-field cross term on the half-line `(a, ∞)`. -/
def weightedPrimitiveCrossIoi
    (a : ℝ) (primitive field fieldDerivative : ℝ → ℝ) : ℝ :=
  ∫ x in Ioi a, primitive x * field x * fieldDerivative x

/-- Growth of a primitive and decay of a field imply vanishing of their
quadratic boundary flux whenever the corresponding product of majorants tends
to zero. -/
theorem tendsto_primitive_mul_sq_zero_of_isBigO
    {α : Type*} {l : Filter α}
    {primitive field primitiveMajorant fieldMajorant : α → ℝ}
    (hprimitive : primitive =O[l] primitiveMajorant)
    (hfield : field =O[l] fieldMajorant)
    (hmajorant : Tendsto
      (fun x ↦ primitiveMajorant x * fieldMajorant x ^ 2) l (𝓝 0)) :
    Tendsto (fun x ↦ primitive x * field x ^ 2) l (𝓝 0) :=
  (hprimitive.mul (hfield.pow 2)).trans_tendsto hmajorant

variable {a b : ℝ}
variable {weight primitive field fieldDerivative : ℝ → ℝ}

/-- The exact hypotheses under which a field admits weighted square
integration by parts on an open interval.  Nonnegativity of the weight alone
implies neither smoothness nor endpoint behavior, so both are listed. -/
def IsSquareIBPAdmissibleOn
    (a b : ℝ) (weight primitive field fieldDerivative : ℝ → ℝ) : Prop :=
  (∀ x ∈ Ioo a b, HasDerivAt primitive (weight x) x) ∧
  (∀ x ∈ Ioo a b, HasDerivAt field (fieldDerivative x) x) ∧
  IntegrableOn (fun x ↦ weight x * field x ^ 2) (Ioo a b) ∧
  IntegrableOn
    (fun x ↦ primitive x * field x * fieldDerivative x) (Ioo a b) ∧
  Tendsto (fun x ↦ primitive x * field x ^ 2) (𝓝[>] a) (𝓝 0) ∧
  Tendsto (fun x ↦ primitive x * field x ^ 2) (𝓝[<] b) (𝓝 0)

/-- Exact weighted square integration-by-parts identity. -/
theorem weightedSquareEnergy_eq_neg_two_cross
    (hab : a < b)
    (hprimitive :
      ∀ x ∈ Ioo a b, HasDerivAt primitive (weight x) x)
    (hfield :
      ∀ x ∈ Ioo a b, HasDerivAt field (fieldDerivative x) x)
    (hweighted :
      IntegrableOn (fun x ↦ weight x * field x ^ 2) (Ioo a b))
    (hcross :
      IntegrableOn
        (fun x ↦ primitive x * field x * fieldDerivative x)
        (Ioo a b))
    (hboundaryLower :
      Tendsto
        (fun x ↦ primitive x * field x ^ 2)
        (𝓝[>] a) (𝓝 0))
    (hboundaryUpper :
      Tendsto
        (fun x ↦ primitive x * field x ^ 2)
        (𝓝[<] b) (𝓝 0)) :
    weightedSquareEnergy a b weight field =
      -2 * weightedPrimitiveCross a b primitive field fieldDerivative := by
  have hfieldSquare : ∀ x ∈ Ioo a b, HasDerivAt (fun y ↦ field y ^ 2)
      (2 * field x * fieldDerivative x) x := fun x hx ↦
    (((hfield x hx).mul (hfield x hx)).congr_deriv (by ring)).congr_of_eventuallyEq
      (.of_forall fun y ↦ by simp only [Pi.mul_apply, pow_two])
  have hcrossTwo : IntegrableOn (fun x ↦ primitive x * (2 * field x * fieldDerivative x))
      (Ioo a b) := IntegrableOn.congr_fun (hcross.const_mul 2) (fun x _ ↦ by ring) measurableSet_Ioo
  have hparts : (∫ x in Ioo a b, primitive x * (2 * field x * fieldDerivative x)) =
      -∫ x in Ioo a b, weight x * field x ^ 2 := by
    simpa only [Pi.mul_apply] using PDE.Analysis.integral_Ioo_mul_deriv_eq_neg_deriv_mul hab
      hprimitive hfieldSquare hweighted hcrossTwo hboundaryLower hboundaryUpper
  have htwo : (∫ x in Ioo a b, primitive x * (2 * field x * fieldDerivative x)) =
      2 * weightedPrimitiveCross a b primitive field fieldDerivative :=
    (integral_congr_ae (.of_forall fun x ↦ by ring)).trans (integral_const_mul 2 _)
  rw [weightedSquareEnergy]
  linarith

/-- The weighted square identity in terms of the admissibility predicate. -/
theorem IsSquareIBPAdmissibleOn.energy_eq_neg_two_cross
    (hab : a < b)
    (h : IsSquareIBPAdmissibleOn
      a b weight primitive field fieldDerivative) :
    weightedSquareEnergy a b weight field =
      -2 * weightedPrimitiveCross a b primitive field fieldDerivative := by
  rcases h with ⟨hprimitive, hfield, hweighted, hcross, hlower, hupper⟩
  exact weightedSquareEnergy_eq_neg_two_cross hab hprimitive hfield
    hweighted hcross hlower hupper

/-- If the field's topological support lies strictly inside `(a,b)`, then
every primitive-field square product vanishes near both endpoints.  No bound
on the primitive at the endpoints is needed. -/
theorem tendsto_primitive_mul_sq_at_endpoints_of_tsupport_subset
    (hsupport : tsupport field ⊆ Ioo a b) :
    Tendsto (fun x ↦ primitive x * field x ^ 2) (𝓝[>] a) (𝓝 0) ∧
      Tendsto (fun x ↦ primitive x * field x ^ 2) (𝓝[<] b) (𝓝 0) := by
  have ha : a ∉ tsupport field := by
    intro ha
    exact (lt_irrefl a) (hsupport ha).1
  have hb : b ∉ tsupport field := by
    intro hb
    exact (lt_irrefl b) (hsupport hb).2
  have hzero (x : ℝ) (hx : x ∉ tsupport field) :
      Tendsto (fun y ↦ primitive y * field y ^ 2) (𝓝 x) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [((isClosed_tsupport field).isOpen_compl.mem_nhds hx)] with y hy
    simp [image_eq_zero_of_notMem_tsupport hy]
  exact ⟨(hzero a ha).mono_left nhdsWithin_le_nhds,
    (hzero b hb).mono_left nhdsWithin_le_nhds⟩

/-- Interior topological support supplies the endpoint part of weighted
square-IBP admissibility. -/
theorem isSquareIBPAdmissibleOn_of_tsupport_subset
    (hprimitive : ∀ x ∈ Ioo a b, HasDerivAt primitive (weight x) x)
    (hfield : ∀ x ∈ Ioo a b, HasDerivAt field (fieldDerivative x) x)
    (hweighted :
      IntegrableOn (fun x ↦ weight x * field x ^ 2) (Ioo a b))
    (hcross : IntegrableOn
      (fun x ↦ primitive x * field x * fieldDerivative x) (Ioo a b))
    (hsupport : tsupport field ⊆ Ioo a b) :
    IsSquareIBPAdmissibleOn
      a b weight primitive field fieldDerivative := by
  obtain ⟨hlower, hupper⟩ :=
    tendsto_primitive_mul_sq_at_endpoints_of_tsupport_subset
      (primitive := primitive) hsupport
  exact ⟨hprimitive, hfield, hweighted, hcross, hlower, hupper⟩

/-- Compactly supported interior fields satisfy the weighted square identity
without separately supplied endpoint-flux limits. -/
theorem weightedSquareEnergy_eq_neg_two_cross_of_tsupport_subset
    (hab : a < b)
    (hprimitive : ∀ x ∈ Ioo a b, HasDerivAt primitive (weight x) x)
    (hfield : ∀ x ∈ Ioo a b, HasDerivAt field (fieldDerivative x) x)
    (hweighted :
      IntegrableOn (fun x ↦ weight x * field x ^ 2) (Ioo a b))
    (hcross : IntegrableOn
      (fun x ↦ primitive x * field x * fieldDerivative x) (Ioo a b))
    (hsupport : tsupport field ⊆ Ioo a b) :
    weightedSquareEnergy a b weight field =
      -2 * weightedPrimitiveCross a b primitive field fieldDerivative := by
  exact (isSquareIBPAdmissibleOn_of_tsupport_subset
    hprimitive hfield hweighted hcross hsupport).energy_eq_neg_two_cross hab

/-! ## Half-line identities -/

/-- The exact hypotheses for weighted square integration by parts on `(a, ∞)`.

The last two conjuncts are the two boundary-flux conditions: the one-sided
limit at `a` and the far-field limit at infinity. -/
def IsSquareIBPAdmissibleOnIoi
    (a : ℝ) (weight primitive field fieldDerivative : ℝ → ℝ) : Prop :=
  (∀ x ∈ Ioi a, HasDerivAt primitive (weight x) x) ∧
  (∀ x ∈ Ioi a, HasDerivAt field (fieldDerivative x) x) ∧
  IntegrableOn (fun x ↦ weight x * field x ^ 2) (Ioi a) ∧
  IntegrableOn
    (fun x ↦ primitive x * field x * fieldDerivative x) (Ioi a) ∧
  Tendsto (fun x ↦ primitive x * field x ^ 2) (𝓝[>] a) (𝓝 0) ∧
  Tendsto (fun x ↦ primitive x * field x ^ 2) atTop (𝓝 0)

/-- Asymptotic growth and decay estimates discharge both boundary-flux
conditions in half-line weighted square integration by parts. -/
theorem isSquareIBPAdmissibleOnIoi_of_isBigO
    (hprimitiveDerivative : ∀ x ∈ Ioi a,
      HasDerivAt primitive (weight x) x)
    (hfieldDerivative : ∀ x ∈ Ioi a,
      HasDerivAt field (fieldDerivative x) x)
    (hweighted : IntegrableOn
      (fun x ↦ weight x * field x ^ 2) (Ioi a))
    (hcross : IntegrableOn
      (fun x ↦ primitive x * field x * fieldDerivative x) (Ioi a))
    {primitiveLower fieldLower primitiveInfinity fieldInfinity : ℝ → ℝ}
    (hprimitiveLower : primitive =O[𝓝[>] a] primitiveLower)
    (hfieldLower : field =O[𝓝[>] a] fieldLower)
    (hlower : Tendsto
      (fun x ↦ primitiveLower x * fieldLower x ^ 2) (𝓝[>] a) (𝓝 0))
    (hprimitiveInfinity : primitive =O[atTop] primitiveInfinity)
    (hfieldInfinity : field =O[atTop] fieldInfinity)
    (hinfinity : Tendsto
      (fun x ↦ primitiveInfinity x * fieldInfinity x ^ 2) atTop (𝓝 0)) :
    IsSquareIBPAdmissibleOnIoi
      a weight primitive field fieldDerivative := by
  exact ⟨hprimitiveDerivative, hfieldDerivative, hweighted, hcross,
    tendsto_primitive_mul_sq_zero_of_isBigO hprimitiveLower hfieldLower hlower,
    tendsto_primitive_mul_sq_zero_of_isBigO hprimitiveInfinity hfieldInfinity hinfinity⟩

/-- Exact weighted square integration-by-parts identity on `(a, ∞)`. -/
theorem weightedSquareEnergyIoi_eq_neg_two_cross
    (hprimitive : ∀ x ∈ Ioi a, HasDerivAt primitive (weight x) x)
    (hfield : ∀ x ∈ Ioi a, HasDerivAt field (fieldDerivative x) x)
    (hweighted : IntegrableOn
      (fun x ↦ weight x * field x ^ 2) (Ioi a))
    (hcross : IntegrableOn
      (fun x ↦ primitive x * field x * fieldDerivative x) (Ioi a))
    (hboundaryLower : Tendsto
      (fun x ↦ primitive x * field x ^ 2) (𝓝[>] a) (𝓝 0))
    (hboundaryInfinity : Tendsto
      (fun x ↦ primitive x * field x ^ 2) atTop (𝓝 0)) :
    weightedSquareEnergyIoi a weight field =
      -2 * weightedPrimitiveCrossIoi a primitive field fieldDerivative := by
  have hfieldSquare : ∀ x ∈ Ioi a, HasDerivAt (fun y ↦ field y ^ 2)
      (2 * field x * fieldDerivative x) x := fun x hx ↦
    (((hfield x hx).mul (hfield x hx)).congr_deriv (by ring)).congr_of_eventuallyEq
      (.of_forall fun y ↦ by simp only [Pi.mul_apply, pow_two])
  have hcrossTwo : IntegrableOn (fun x ↦ primitive x * (2 * field x * fieldDerivative x))
      (Ioi a) := IntegrableOn.congr_fun (hcross.const_mul 2) (fun x _ ↦ by ring) measurableSet_Ioi
  have hparts : (∫ x in Ioi a, primitive x * (2 * field x * fieldDerivative x)) =
      -∫ x in Ioi a, weight x * field x ^ 2 := by
    simpa only [Pi.mul_apply, sub_zero, zero_sub] using
      MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul hprimitive hfieldSquare hcrossTwo
        hweighted hboundaryLower hboundaryInfinity
  have htwo : (∫ x in Ioi a, primitive x * (2 * field x * fieldDerivative x)) =
      2 * weightedPrimitiveCrossIoi a primitive field fieldDerivative :=
    (integral_congr_ae (.of_forall fun x ↦ by ring)).trans (integral_const_mul 2 _)
  rw [weightedSquareEnergyIoi]
  linarith

/-- The half-line weighted square identity via the admissibility predicate. -/
theorem IsSquareIBPAdmissibleOnIoi.energy_eq_neg_two_cross
    (h : IsSquareIBPAdmissibleOnIoi
      a weight primitive field fieldDerivative) :
    weightedSquareEnergyIoi a weight field =
      -2 * weightedPrimitiveCrossIoi a primitive field fieldDerivative := by
  rcases h with ⟨hprimitive, hfield, hweighted, hcross, hlower, hinfinity⟩
  exact weightedSquareEnergyIoi_eq_neg_two_cross hprimitive hfield
    hweighted hcross hlower hinfinity

/-- A field supported strictly to the right of `a` and with compact support
has zero primitive-square flux at both ends of `(a, ∞)`. -/
theorem tendsto_primitive_mul_sq_at_Ioi_endpoints_of_compactSupport
    (hsupport : tsupport field ⊆ Ioi a)
    (hcompact : HasCompactSupport field) :
    Tendsto (fun x ↦ primitive x * field x ^ 2) (𝓝[>] a) (𝓝 0) ∧
      Tendsto (fun x ↦ primitive x * field x ^ 2) atTop (𝓝 0) := by
  have ha : a ∉ tsupport field := by
    intro ha
    exact (lt_irrefl a) (hsupport ha)
  have hlower : Tendsto
      (fun x ↦ primitive x * field x ^ 2) (𝓝[>] a) (𝓝 0) := by
    have hzero : Tendsto
        (fun x ↦ primitive x * field x ^ 2) (𝓝 a) (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [((isClosed_tsupport field).isOpen_compl.mem_nhds ha)] with x hx
      simp [image_eq_zero_of_notMem_tsupport hx]
    exact hzero.mono_left nhdsWithin_le_nhds
  obtain ⟨bound, hbound⟩ := hcompact.bddAbove
  have hfieldTop : field =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop bound] with x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxsupport
    exact (not_le_of_gt hx) (hbound hxsupport)
  have hinfinity : Tendsto
      (fun x ↦ primitive x * field x ^ 2) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hfieldTop] with x hx
    simp [hx]
  exact ⟨hlower, hinfinity⟩

/-- Compactly supported half-line fields satisfy the exact weighted square
identity without separately supplied endpoint-flux limits. -/
theorem weightedSquareEnergyIoi_eq_neg_two_cross_of_compactSupport
    (hprimitive : ∀ x ∈ Ioi a, HasDerivAt primitive (weight x) x)
    (hfield : ∀ x ∈ Ioi a, HasDerivAt field (fieldDerivative x) x)
    (hweighted : IntegrableOn
      (fun x ↦ weight x * field x ^ 2) (Ioi a))
    (hcross : IntegrableOn
      (fun x ↦ primitive x * field x * fieldDerivative x) (Ioi a))
    (hsupport : tsupport field ⊆ Ioi a)
    (hcompact : HasCompactSupport field) :
    weightedSquareEnergyIoi a weight field =
      -2 * weightedPrimitiveCrossIoi a primitive field fieldDerivative := by
  obtain ⟨hlower, hinfinity⟩ :=
    tendsto_primitive_mul_sq_at_Ioi_endpoints_of_compactSupport
      (primitive := primitive) hsupport hcompact
  exact weightedSquareEnergyIoi_eq_neg_two_cross hprimitive hfield
    hweighted hcross hlower hinfinity

/-! ## Meridian-slice identities -/

/-- The half-line weighted square identity integrated over a second variable.
Each radial slice carries its own axis and far-field flux hypotheses. -/
theorem integral_weightedSquareEnergyIoi_eq_neg_two_cross
    {weight primitive field fieldDerivative : ℝ → ℝ → ℝ}
    (hprimitive : ∀ z x, x ∈ Ioi a →
      HasDerivAt (fun r ↦ primitive r z) (weight x z) x)
    (hfield : ∀ z x, x ∈ Ioi a →
      HasDerivAt (fun r ↦ field r z) (fieldDerivative x z) x)
    (hweighted : ∀ z, IntegrableOn
      (fun x ↦ weight x z * field x z ^ 2) (Ioi a))
    (hcross : ∀ z, IntegrableOn
      (fun x ↦ primitive x z * field x z * fieldDerivative x z) (Ioi a))
    (hboundaryLower : ∀ z, Tendsto
      (fun x ↦ primitive x z * field x z ^ 2) (𝓝[>] a) (𝓝 0))
    (hboundaryInfinity : ∀ z, Tendsto
      (fun x ↦ primitive x z * field x z ^ 2) atTop (𝓝 0)) :
    (∫ z : ℝ, weightedSquareEnergyIoi a
      (fun x ↦ weight x z) (fun x ↦ field x z)) =
      -2 * ∫ z : ℝ, weightedPrimitiveCrossIoi a
        (fun x ↦ primitive x z) (fun x ↦ field x z)
        (fun x ↦ fieldDerivative x z) := by
  rw [← integral_const_mul]
  exact integral_congr_ae (.of_forall fun z ↦ weightedSquareEnergyIoi_eq_neg_two_cross
    (hprimitive z) (hfield z) (hweighted z) (hcross z) (hboundaryLower z) (hboundaryInfinity z))

/-- Meridian-slice half-line integration by parts for compactly supported
radial slices lying strictly to the right of the axis endpoint. -/
theorem integral_weightedSquareEnergyIoi_eq_neg_two_cross_of_compactSupport
    {weight primitive field fieldDerivative : ℝ → ℝ → ℝ}
    (hprimitive : ∀ z x, x ∈ Ioi a →
      HasDerivAt (fun r ↦ primitive r z) (weight x z) x)
    (hfield : ∀ z x, x ∈ Ioi a →
      HasDerivAt (fun r ↦ field r z) (fieldDerivative x z) x)
    (hweighted : ∀ z, IntegrableOn
      (fun x ↦ weight x z * field x z ^ 2) (Ioi a))
    (hcross : ∀ z, IntegrableOn
      (fun x ↦ primitive x z * field x z * fieldDerivative x z) (Ioi a))
    (hsupport : ∀ z, tsupport (fun x ↦ field x z) ⊆ Ioi a)
    (hcompact : ∀ z, HasCompactSupport (fun x ↦ field x z)) :
    (∫ z : ℝ, weightedSquareEnergyIoi a
      (fun x ↦ weight x z) (fun x ↦ field x z)) =
      -2 * ∫ z : ℝ, weightedPrimitiveCrossIoi a
        (fun x ↦ primitive x z) (fun x ↦ field x z)
        (fun x ↦ fieldDerivative x z) := by
  have h (z : ℝ) := tendsto_primitive_mul_sq_at_Ioi_endpoints_of_compactSupport
    (primitive := fun x ↦ primitive x z) (hsupport z) (hcompact z)
  exact integral_weightedSquareEnergyIoi_eq_neg_two_cross hprimitive hfield hweighted hcross
    (fun z ↦ (h z).1) fun z ↦ (h z).2

/-- The singular-endpoint weighted square identity integrated over a second
variable. This is the form used on a finite meridian strip
`(a,b) × ℝ`: every radial slice carries its own primitive and boundary-flux
hypotheses. -/
theorem integral_weightedSquareEnergy_eq_neg_two_cross
    {weight primitive field fieldDerivative : ℝ → ℝ → ℝ}
    (hab : a < b)
    (hprimitive : ∀ z x, x ∈ Ioo a b →
      HasDerivAt (fun r ↦ primitive r z) (weight x z) x)
    (hfield : ∀ z x, x ∈ Ioo a b →
      HasDerivAt (fun r ↦ field r z) (fieldDerivative x z) x)
    (hweighted : ∀ z,
      IntegrableOn (fun x ↦ weight x z * field x z ^ 2) (Ioo a b))
    (hcross : ∀ z, IntegrableOn
      (fun x ↦ primitive x z * field x z * fieldDerivative x z)
      (Ioo a b))
    (hboundaryLower : ∀ z, Tendsto
      (fun x ↦ primitive x z * field x z ^ 2) (𝓝[>] a) (𝓝 0))
    (hboundaryUpper : ∀ z, Tendsto
      (fun x ↦ primitive x z * field x z ^ 2) (𝓝[<] b) (𝓝 0)) :
    (∫ z : ℝ, weightedSquareEnergy a b
      (fun x ↦ weight x z) (fun x ↦ field x z)) =
      -2 * ∫ z : ℝ, weightedPrimitiveCross a b
        (fun x ↦ primitive x z) (fun x ↦ field x z)
        (fun x ↦ fieldDerivative x z) := by
  rw [← integral_const_mul]
  exact integral_congr_ae (.of_forall fun z ↦ weightedSquareEnergy_eq_neg_two_cross hab
    (hprimitive z) (hfield z) (hweighted z) (hcross z) (hboundaryLower z) (hboundaryUpper z))

/-- Meridian-slice weighted square integration by parts when every radial
slice has topological support strictly inside the radial interval. -/
theorem integral_weightedSquareEnergy_eq_neg_two_cross_of_tsupport_subset
    {weight primitive field fieldDerivative : ℝ → ℝ → ℝ}
    (hab : a < b)
    (hprimitive : ∀ z x, x ∈ Ioo a b →
      HasDerivAt (fun r ↦ primitive r z) (weight x z) x)
    (hfield : ∀ z x, x ∈ Ioo a b →
      HasDerivAt (fun r ↦ field r z) (fieldDerivative x z) x)
    (hweighted : ∀ z,
      IntegrableOn (fun x ↦ weight x z * field x z ^ 2) (Ioo a b))
    (hcross : ∀ z, IntegrableOn
      (fun x ↦ primitive x z * field x z * fieldDerivative x z) (Ioo a b))
    (hsupport : ∀ z, tsupport (fun x ↦ field x z) ⊆ Ioo a b) :
    (∫ z : ℝ, weightedSquareEnergy a b
      (fun x ↦ weight x z) (fun x ↦ field x z)) =
      -2 * ∫ z : ℝ, weightedPrimitiveCross a b
        (fun x ↦ primitive x z) (fun x ↦ field x z)
        (fun x ↦ fieldDerivative x z) := by
  have h (z : ℝ) := tendsto_primitive_mul_sq_at_endpoints_of_tsupport_subset
    (primitive := fun x ↦ primitive x z) (hsupport z)
  exact integral_weightedSquareEnergy_eq_neg_two_cross hab hprimitive hfield hweighted hcross
    (fun z ↦ (h z).1) fun z ↦ (h z).2

/--
A pointwise integrable majorant for twice the cross term bounds the weighted
square energy.
-/
theorem energy_le_integral_majorant
    (hab : a < b)
    (hprimitive :
      ∀ x ∈ Ioo a b, HasDerivAt primitive (weight x) x)
    (hfield :
      ∀ x ∈ Ioo a b, HasDerivAt field (fieldDerivative x) x)
    (hweighted :
      IntegrableOn (fun x ↦ weight x * field x ^ 2) (Ioo a b))
    (hcross :
      IntegrableOn
        (fun x ↦ primitive x * field x * fieldDerivative x)
        (Ioo a b))
    (hboundaryLower :
      Tendsto
        (fun x ↦ primitive x * field x ^ 2)
        (𝓝[>] a) (𝓝 0))
    (hboundaryUpper :
      Tendsto
        (fun x ↦ primitive x * field x ^ 2)
        (𝓝[<] b) (𝓝 0))
    {majorant : ℝ → ℝ}
    (hmajorant : IntegrableOn majorant (Ioo a b))
    (hpointwise :
      ∀ x ∈ Ioo a b,
        2 * |primitive x * field x * fieldDerivative x| ≤ majorant x) :
    weightedSquareEnergy a b weight field ≤
      ∫ x in Ioo a b, majorant x := by
  let cross : ℝ → ℝ :=
    fun x ↦ primitive x * field x * fieldDerivative x
  have hcrossAbs :
      IntegrableOn (fun x ↦ 2 * |cross x|) (Ioo a b) :=
    hcross.norm.const_mul 2
  have hcrossIntegral :
      -2 * weightedPrimitiveCross a b primitive field fieldDerivative ≤
        ∫ x in Ioo a b, 2 * |cross x| := by
    change -2 * (∫ x in Ioo a b, cross x) ≤ _
    rw [integral_const_mul]
    linarith [neg_le_abs (∫ x in Ioo a b, cross x),
      abs_integral_le_integral_abs (f := cross) (μ := volume.restrict (Ioo a b))]
  rw [weightedSquareEnergy_eq_neg_two_cross
    hab hprimitive hfield hweighted hcross hboundaryLower hboundaryUpper]
  exact hcrossIntegral.trans <|
    MeasureTheory.integral_mono_ae hcrossAbs hmajorant <|
      MeasureTheory.ae_restrict_of_forall_mem
        measurableSet_Ioo hpointwise

/--
Young's inequality applied after a pointwise factorization bound for the
primitive.

The factorization need only hold in absolute value:
`|primitive| ≤ |lowerFactor * upperFactor|`.
-/
theorem energy_le_young
    (hab : a < b)
    (hprimitive :
      ∀ x ∈ Ioo a b, HasDerivAt primitive (weight x) x)
    (hfield :
      ∀ x ∈ Ioo a b, HasDerivAt field (fieldDerivative x) x)
    (hweighted :
      IntegrableOn (fun x ↦ weight x * field x ^ 2) (Ioo a b))
    (hcross :
      IntegrableOn
        (fun x ↦ primitive x * field x * fieldDerivative x)
        (Ioo a b))
    (hboundaryLower :
      Tendsto
        (fun x ↦ primitive x * field x ^ 2)
        (𝓝[>] a) (𝓝 0))
    (hboundaryUpper :
      Tendsto
        (fun x ↦ primitive x * field x ^ 2)
        (𝓝[<] b) (𝓝 0))
    {lowerFactor upperFactor : ℝ → ℝ} {ε : ℝ}
    (hε : 0 < ε)
    (hfactor :
      ∀ x ∈ Ioo a b,
        |primitive x| ≤ |lowerFactor x * upperFactor x|)
    (hlower :
      IntegrableOn
        (fun x ↦ (lowerFactor x * field x) ^ 2)
        (Ioo a b))
    (hupper :
      IntegrableOn
        (fun x ↦ (upperFactor x * fieldDerivative x) ^ 2)
        (Ioo a b)) :
    weightedSquareEnergy a b weight field ≤
      ε * (∫ x in Ioo a b, (lowerFactor x * field x) ^ 2) +
        ε⁻¹ *
          ∫ x in Ioo a b,
            (upperFactor x * fieldDerivative x) ^ 2 := by
  let majorant : ℝ → ℝ :=
    fun x ↦
      ε * (lowerFactor x * field x) ^ 2 +
        ε⁻¹ * (upperFactor x * fieldDerivative x) ^ 2
  have hmajorant : IntegrableOn majorant (Ioo a b) :=
    (hlower.const_mul ε).add (hupper.const_mul ε⁻¹)
  have hpointwise :
      ∀ x ∈ Ioo a b,
        2 * |primitive x * field x * fieldDerivative x| ≤
          majorant x := by
    intro x hx
    calc
      2 * |primitive x * field x * fieldDerivative x| =
          2 * |primitive x| * |field x| * |fieldDerivative x| := by
        rw [abs_mul, abs_mul]
        ring
      _ ≤
          2 * |lowerFactor x * upperFactor x| *
            |field x| * |fieldDerivative x| := by
        gcongr 2 * ?_ * _ * _
        exact hfactor x hx
      _ =
          2 * |lowerFactor x * field x| *
            |upperFactor x * fieldDerivative x| := by
        simp only [abs_mul]
        ring
      _ ≤
          ε * |lowerFactor x * field x| ^ 2 +
            ε⁻¹ * |upperFactor x * fieldDerivative x| ^ 2 :=
        two_mul_le_add_mul_sq hε
      _ = majorant x := by
        simp only [majorant, sq_abs]
  exact (energy_le_integral_majorant hab hprimitive hfield hweighted hcross hboundaryLower
    hboundaryUpper hmajorant hpointwise).trans_eq <|
      (integral_add (hlower.const_mul ε) (hupper.const_mul ε⁻¹)).trans
        (by rw [integral_const_mul, integral_const_mul])

/--
Convenience form of `energy_le_young` for an exact primitive
factorization.
-/
theorem energy_le_young_of_primitive_eq_mul
    (hab : a < b)
    (hprimitive :
      ∀ x ∈ Ioo a b, HasDerivAt primitive (weight x) x)
    (hfield :
      ∀ x ∈ Ioo a b, HasDerivAt field (fieldDerivative x) x)
    (hweighted :
      IntegrableOn (fun x ↦ weight x * field x ^ 2) (Ioo a b))
    (hcross :
      IntegrableOn
        (fun x ↦ primitive x * field x * fieldDerivative x)
        (Ioo a b))
    (hboundaryLower :
      Tendsto
        (fun x ↦ primitive x * field x ^ 2)
        (𝓝[>] a) (𝓝 0))
    (hboundaryUpper :
      Tendsto
        (fun x ↦ primitive x * field x ^ 2)
        (𝓝[<] b) (𝓝 0))
    {lowerFactor upperFactor : ℝ → ℝ} {ε : ℝ}
    (hε : 0 < ε)
    (hfactor :
      ∀ x ∈ Ioo a b,
        primitive x = lowerFactor x * upperFactor x)
    (hlower :
      IntegrableOn
        (fun x ↦ (lowerFactor x * field x) ^ 2)
        (Ioo a b))
    (hupper :
      IntegrableOn
        (fun x ↦ (upperFactor x * fieldDerivative x) ^ 2)
        (Ioo a b)) :
    weightedSquareEnergy a b weight field ≤
      ε * (∫ x in Ioo a b, (lowerFactor x * field x) ^ 2) +
        ε⁻¹ *
          ∫ x in Ioo a b,
            (upperFactor x * fieldDerivative x) ^ 2 := by
  exact energy_le_young hab hprimitive hfield hweighted hcross hboundaryLower hboundaryUpper hε
    (fun x hx ↦ by rw [hfactor x hx]) hlower hupper

end Weighted
end SobolevSpace

