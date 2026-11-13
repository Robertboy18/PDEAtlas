/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import PDE.Elliptic.Variational.DivergenceSolution
public import PDE.Elliptic.Variational.LowerOrderDependence
public import PDE.Elliptic.Variational.MeasurableForm
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.H10L2

/-!
# Raw measurable parabolic coefficients

The coefficients `BoundedMeasurableCoefficients` are scalar functions on spacetime, with
joint measurability and essential bounds, as in Evans's (5). Their spatial L∞ sections
define the divergence form, Evans's bilinear form (8).
Measurability of each dual-valued form evaluation follows from Fubini and the
separability of H¹₀. No measurability in the L∞ or operator norm is required.
Joint ellipticity almost everywhere, Evans's uniform parabolicity (4), gives the Gårding
inequality (22) at almost every time (`ae_garding`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.1, (2) and (4), p. 372, and (5) and (8), p. 373; §7.1.2,
  (22), p. 376.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Sobolev

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace HeatEquation.Variational

open SobolevSpace SobolevSpace.GraphSpace

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

/-- Jointly bounded measurable principal, drift, and potential coefficients.
The common bound loses no generality for finitely many L∞ coefficients. -/
structure BoundedMeasurableCoefficients (n : ℕ) (Ω : Set (ℝ^n)) (μ : Measure ℝ) where
  /-- Principal divergence coefficients on spacetime. -/
  principal : Fin n → Fin n → ℝ × (ℝ^n) → ℝ
  /-- First-order drift coefficients on spacetime. -/
  drift : Fin n → ℝ × (ℝ^n) → ℝ
  /-- Zeroth-order potential on spacetime. -/
  potential : ℝ × (ℝ^n) → ℝ
  /-- A common essential bound for all scalar coefficients. -/
  bound : ℝ≥0
  principal_measurable : ∀ i j,
    AEStronglyMeasurable (principal i j) (μ.prod (domainMeasure n Ω))
  drift_measurable : ∀ i,
    AEStronglyMeasurable (drift i) (μ.prod (domainMeasure n Ω))
  potential_measurable : AEStronglyMeasurable potential (μ.prod (domainMeasure n Ω))
  principal_bound : ∀ i j, ∀ᵐ z ∂μ.prod (domainMeasure n Ω), ‖principal i j z‖ ≤ bound
  drift_bound : ∀ i, ∀ᵐ z ∂μ.prod (domainMeasure n Ω), ‖drift i z‖ ≤ bound
  potential_bound : ∀ᵐ z ∂μ.prod (domainMeasure n Ω), ‖potential z‖ ≤ bound

namespace BoundedMeasurableCoefficients

variable {n : ℕ} {Ω : Set (ℝ^n)} {μ : Measure ℝ}

/-- Spatial L∞ sections, uniformly bounded even at exceptional times. -/
def principalSection (C : BoundedMeasurableCoefficients n Ω μ)
    (t : ℝ) (i j : Fin n) : DerivLp n ∞ Ω :=
  (exists_bounded_Linfty_sections (C.principal_measurable i j)
    C.bound.2 (C.principal_bound i j)).choose t

/-- Spatial L∞ sections of the drift coefficients. -/
def driftSection (C : BoundedMeasurableCoefficients n Ω μ)
    (t : ℝ) (i : Fin n) : DerivLp n ∞ Ω :=
  (exists_bounded_Linfty_sections (C.drift_measurable i)
    C.bound.2 (C.drift_bound i)).choose t

/-- Spatial L∞ sections of the potential. -/
def potentialSection (C : BoundedMeasurableCoefficients n Ω μ)
    (t : ℝ) : DerivLp n ∞ Ω :=
  (exists_bounded_Linfty_sections C.potential_measurable
    C.bound.2 C.potential_bound).choose t

/-- Every chosen principal section obeys the original essential coefficient bound. -/
theorem norm_principalSection_le (C : BoundedMeasurableCoefficients n Ω μ)
    (t : ℝ) (i j : Fin n) : ‖C.principalSection t i j‖ ≤ C.bound :=
  (exists_bounded_Linfty_sections (C.principal_measurable i j)
    C.bound.2 (C.principal_bound i j)).choose_spec.1 t

/-- Every chosen drift section obeys the original essential coefficient bound. -/
theorem norm_driftSection_le (C : BoundedMeasurableCoefficients n Ω μ)
    (t : ℝ) (i : Fin n) : ‖C.driftSection t i‖ ≤ C.bound :=
  (exists_bounded_Linfty_sections (C.drift_measurable i)
    C.bound.2 (C.drift_bound i)).choose_spec.1 t

/-- Every chosen potential section obeys the original essential coefficient bound. -/
theorem norm_potentialSection_le (C : BoundedMeasurableCoefficients n Ω μ)
    (t : ℝ) : ‖C.potentialSection t‖ ≤ C.bound :=
  (exists_bounded_Linfty_sections C.potential_measurable
    C.bound.2 C.potential_bound).choose_spec.1 t

/-- The principal sections represent the raw coefficients at almost every time. -/
theorem principalSection_ae (C : BoundedMeasurableCoefficients n Ω μ) (i j : Fin n) :
    ∀ᵐ t ∂μ, (fun x ↦ C.principal i j (t, x)) =ᵐ[domainMeasure n Ω]
      (C.principalSection t i j : (ℝ^n) → ℝ) :=
  (exists_bounded_Linfty_sections (C.principal_measurable i j)
    C.bound.2 (C.principal_bound i j)).choose_spec.2

/-- The drift sections represent the raw coefficients at almost every time. -/
theorem driftSection_ae (C : BoundedMeasurableCoefficients n Ω μ) (i : Fin n) :
    ∀ᵐ t ∂μ, (fun x ↦ C.drift i (t, x)) =ᵐ[domainMeasure n Ω]
      (C.driftSection t i : (ℝ^n) → ℝ) :=
  (exists_bounded_Linfty_sections (C.drift_measurable i)
    C.bound.2 (C.drift_bound i)).choose_spec.2

/-- The potential sections represent the raw coefficient at almost every time. -/
theorem potentialSection_ae (C : BoundedMeasurableCoefficients n Ω μ) :
    ∀ᵐ t ∂μ, (fun x ↦ C.potential (t, x)) =ᵐ[domainMeasure n Ω]
      (C.potentialSection t : (ℝ^n) → ℝ) :=
  (exists_bounded_Linfty_sections C.potential_measurable
    C.bound.2 C.potential_bound).choose_spec.2

/-- The full divergence form associated with the raw coefficient sections. -/
def form (C : BoundedMeasurableCoefficients n Ω μ)
    (t : ℝ) : H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
  fullDivergenceForm (multiplicationCoefficientOperator (C.principalSection t))
    (fun i ↦ mulLpLeft (C.driftSection t i)) (mulLpLeft (C.potentialSection t))

/-- A data-only bound for the induced form. -/
def formBound (C : BoundedMeasurableCoefficients n Ω μ) : ℝ≥0 :=
  n * n * C.bound + n * C.bound + C.bound

/-- The form norm is bounded using only dimension and the raw coefficient bound. -/
theorem norm_form_le (C : BoundedMeasurableCoefficients n Ω μ) (t : ℝ) :
    ‖C.form t‖ ≤ C.formBound := by
  let D := derivCoordCLM (n := n) (Ω := Ω)
  let P := baseCoordCLM (n := n) (Ω := Ω)
  have hprincipal :
      ‖variableCoeffForm (multiplicationCoefficientOperator (C.principalSection t))‖ ≤
        (n : ℝ) * n * C.bound := by
    refine (norm_variableCoeffFormOf_le (H¹₀(Ω)) (H¹₀(Ω))
      D (derivCoordCLM_norm_le (n := n) (Ω := Ω))
      D (derivCoordCLM_norm_le (n := n) (Ω := Ω))
      (multiplicationCoefficientOperator (C.principalSection t))).trans ?_
    calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, (C.bound : ℝ) := by
        exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
          (norm_mulLpLeft_le (p := 2) _).trans (C.norm_principalSection_le t i j)
      _ = _ := by simp [mul_assoc]
  have hlower :
      ‖lowerOrderForm (fun i ↦ mulLpLeft (C.driftSection t i))
        (mulLpLeft (C.potentialSection t))‖ ≤ (n : ℝ) * C.bound + C.bound := by
    refine (norm_multiplicationLowerOrderFormOf_le (H¹₀(Ω))
      D (derivCoordCLM_norm_le (n := n) (Ω := Ω))
      P (baseCoordCLM_norm_le (n := n) (Ω := Ω))
      (C.driftSection t) (C.potentialSection t)).trans ?_
    calc
      _ ≤ (∑ _i : Fin n, (C.bound : ℝ)) + C.bound :=
        add_le_add (Finset.sum_le_sum fun i _ ↦ C.norm_driftSection_le t i)
          (C.norm_potentialSection_le t)
      _ = _ := by simp
  change ‖variableCoeffForm (multiplicationCoefficientOperator (C.principalSection t)) +
    lowerOrderForm (fun i ↦ mulLpLeft (C.driftSection t i))
      (mulLpLeft (C.potentialSection t))‖ ≤ _
  refine (norm_add_le
    (variableCoeffForm (multiplicationCoefficientOperator (C.principalSection t)))
    (lowerOrderForm (fun i ↦ mulLpLeft (C.driftSection t i))
      (mulLpLeft (C.potentialSection t)))).trans ?_
  simpa [formBound, add_assoc] using add_le_add hprincipal hlower

/-- The raw coefficient hypotheses imply the measurability needed by evolution theory. -/
theorem aestronglyMeasurable_form_apply (C : BoundedMeasurableCoefficients n Ω μ)
    (u : H¹₀(Ω)) : AEStronglyMeasurable (fun t ↦ C.form t u) μ := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (DerivLp n 2 Ω) := Lp.SecondCountableTopology
  have : SeparableSpace (H¹₀(Ω)) := inferInstance
  exact aestronglyMeasurable_multiplicationFullForm_apply_of_joint (H¹₀(Ω))
    (derivCoordCLM (n := n) (Ω := Ω)) (derivCoordCLM_norm_le (n := n) (Ω := Ω))
    (baseCoordCLM (n := n) (Ω := Ω)) (baseCoordCLM_norm_le (n := n) (Ω := Ω))
    C.principal_measurable C.drift_measurable C.potential_measurable
    C.principalSection_ae C.driftSection_ae C.potentialSection_ae u

/-- Joint almost-everywhere ellipticity passes to the spatial L∞ classes. -/
theorem ae_integratedElliptic (C : BoundedMeasurableCoefficients n Ω μ)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hElliptic : ∀ᵐ z ∂μ.prod (domainMeasure n Ω), ∀ ξ : Fin n → ℝ,
      alpha * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, C.principal i j z * ξ j * ξ i) :
    ∀ᵐ t ∂μ,
      IntegratedElliptic (multiplicationCoefficientOperator (C.principalSection t)) alpha := by
  have hsection : ∀ᵐ t ∂μ, ∀ i j,
      (fun x ↦ C.principal i j (t, x)) =ᵐ[domainMeasure n Ω]
        (C.principalSection t i j : (ℝ^n) → ℝ) := by
    exact ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦ C.principalSection_ae i j
  filter_upwards [Measure.ae_ae_of_ae_prod hElliptic, hsection] with t ht hs
  apply integratedElliptic_multiplication_of_ae
  refine ⟨halpha, ?_⟩
  have hs' : ∀ᵐ x ∂domainMeasure n Ω, ∀ i j,
      C.principal i j (t, x) = C.principalSection t i j x :=
    ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦ hs i j
  filter_upwards [ht, hs'] with x hx hxs
  simpa only [hxs] using hx

/-- The drift and potential bounds hold at every time for the chosen sections. -/
theorem lowerOrderBounds (C : BoundedMeasurableCoefficients n Ω μ) (t : ℝ) :
    LowerOrderBounds (fun i ↦ mulLpLeft (C.driftSection t i))
      (mulLpLeft (C.potentialSection t)) C.bound C.bound :=
  ⟨C.bound.2, C.bound.2,
    fun i ↦ (norm_mulLpLeft_le (p := 2) _).trans (C.norm_driftSection_le t i),
    (norm_mulLpLeft_le (p := 2) _).trans (C.norm_potentialSection_le t)⟩

/-- Raw joint ellipticity and bounds give the Gårding inequality at almost every time,
as in Evans's (22). -/
theorem ae_garding (C : BoundedMeasurableCoefficients n Ω μ) (hΩopen : IsOpen Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hElliptic : ∀ᵐ z ∂μ.prod (domainMeasure n Ω), ∀ ξ : Fin n → ℝ,
      alpha * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, C.principal i j z * ξ j * ξ i) :
    ∀ᵐ t ∂μ, ∀ u : H¹₀(Ω),
      (alpha / 2) * ‖u‖ ^ 2 ≤ C.form t u u +
        coerciveShift (n := n) alpha C.bound C.bound *
          ‖(h10L2GelfandTriple hΩopen).inclusion u‖ ^ 2 := by
  filter_upwards [C.ae_integratedElliptic halpha hElliptic] with t ht u
  simpa only [form, shiftedDivergenceForm_apply, h10L2GelfandTriple_inclusion_apply,
    real_inner_self_eq_norm_sq, pow_two, mul_assoc] using
      shiftedDivergenceForm_coercive_bound _ _ _ ht (C.lowerOrderBounds t) u

end BoundedMeasurableCoefficients

end HeatEquation.Variational
