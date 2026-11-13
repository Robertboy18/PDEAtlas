/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.BoundedSections
public import PDE.Analysis.MeasureTheory.StronglyMeasurable.Hilbert
public import PDE.Elliptic.Variational.DivergenceSolution
public import PDE.Elliptic.Variational.PivotOperator
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Measurable drift and potential as an `L²` load

Jointly measurable, essentially bounded scalar coefficients define the lower-order
expression `b(t) · Du + c(t)u`. Its values on each fixed `H¹₀` state are strongly
measurable in `L²`, even when the coefficient sections are not measurable in the
`L∞` norm. Neither a sign condition nor time derivatives of these coefficients are needed.
-/

@[expose] public noncomputable section

open scoped Sobolev
open MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace

namespace PDE.Parabolic.DivergenceFormHeat.LowerOrder

open SobolevSpace SobolevSpace.GraphSpace

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

/-- Bounded measurable drift and potential on a time-space cylinder.
All bounds are absolute bounds; both coefficients may have either sign. -/
structure BoundedCoefficients (n : ℕ) (Ω : Set (ℝ^n)) (μ : Measure ℝ) where
  /-- The scalar components of the drift vector on the time-space cylinder. -/
  drift : Fin n → ℝ × (ℝ^n) → ℝ
  /-- The scalar potential on the time-space cylinder. -/
  potential : ℝ × (ℝ^n) → ℝ
  /-- A common essential absolute bound for every drift component and the potential. -/
  bound : ℝ≥0
  drift_measurable : ∀ i, AEStronglyMeasurable (drift i) (μ.prod (domainMeasure n Ω))
  potential_measurable : AEStronglyMeasurable potential (μ.prod (domainMeasure n Ω))
  drift_bound : ∀ i, ∀ᵐ z ∂μ.prod (domainMeasure n Ω), ‖drift i z‖ ≤ bound
  potential_bound : ∀ᵐ z ∂μ.prod (domainMeasure n Ω), ‖potential z‖ ≤ bound

namespace BoundedCoefficients

variable {n : ℕ} {Ω : Set (ℝ^n)} {μ : Measure ℝ}

/-- Bounded spatial sections of the drift, chosen to be bounded at exceptional times too. -/
def driftSection (C : BoundedCoefficients n Ω μ) (t : ℝ) (i : Fin n) :
    DerivLp n ∞ Ω :=
  (exists_bounded_Linfty_sections (C.drift_measurable i)
    C.bound.2 (C.drift_bound i)).choose t

/-- Bounded spatial sections of the potential. -/
def potentialSection (C : BoundedCoefficients n Ω μ) (t : ℝ) : DerivLp n ∞ Ω :=
  (exists_bounded_Linfty_sections C.potential_measurable
    C.bound.2 C.potential_bound).choose t

/-- Every chosen drift section obeys the coefficient bound. -/
theorem norm_driftSection_le (C : BoundedCoefficients n Ω μ) (t : ℝ) (i : Fin n) :
    ‖C.driftSection t i‖ ≤ C.bound :=
  (exists_bounded_Linfty_sections (C.drift_measurable i)
    C.bound.2 (C.drift_bound i)).choose_spec.1 t

/-- Every chosen potential section obeys the coefficient bound. -/
theorem norm_potentialSection_le (C : BoundedCoefficients n Ω μ) (t : ℝ) :
    ‖C.potentialSection t‖ ≤ C.bound :=
  (exists_bounded_Linfty_sections C.potential_measurable
    C.bound.2 C.potential_bound).choose_spec.1 t

/-- The chosen drift sections represent the given scalar drift almost everywhere. -/
theorem driftSection_ae (C : BoundedCoefficients n Ω μ) (i : Fin n) :
    ∀ᵐ t ∂μ, (fun x ↦ C.drift i (t, x)) =ᵐ[domainMeasure n Ω]
      (C.driftSection t i : (ℝ^n) → ℝ) :=
  (exists_bounded_Linfty_sections (C.drift_measurable i)
    C.bound.2 (C.drift_bound i)).choose_spec.2

/-- The chosen potential sections represent the given scalar potential almost everywhere. -/
theorem potentialSection_ae (C : BoundedCoefficients n Ω μ) :
    ∀ᵐ t ∂μ, (fun x ↦ C.potential (t, x)) =ᵐ[domainMeasure n Ω]
      (C.potentialSection t : (ℝ^n) → ℝ) :=
  (exists_bounded_Linfty_sections C.potential_measurable
    C.bound.2 C.potential_bound).choose_spec.2

/-- The lower-order expression as a bounded map from `H¹₀` to `L²`. -/
def operator (C : BoundedCoefficients n Ω μ) (t : ℝ) :
    H¹₀(Ω) →L[ℝ] DerivLp n 2 Ω :=
  lowerOrderOperator (fun i ↦ mulLpLeft (C.driftSection t i))
    (mulLpLeft (C.potentialSection t))

/-- A uniform bound for the lower-order operator, depending only on the coefficients. -/
def operatorBound (C : BoundedCoefficients n Ω μ) : ℝ≥0 :=
  (n + 1) * C.bound

/-- The lower-order operator is uniformly bounded independently of time and state. -/
theorem norm_operator_le (C : BoundedCoefficients n Ω μ) (t : ℝ) :
    ‖C.operator t‖ ≤ C.operatorBound := by
  apply (C.operator t).opNorm_le_bound C.operatorBound.2
  intro u
  have hmul (d : DerivLp n ∞ Ω) (hd : ‖d‖ ≤ C.bound)
      (w : DerivLp n 2 Ω) (hw : ‖w‖ ≤ ‖u‖) :
      ‖mulLpLeft d w‖ ≤ C.bound * ‖u‖ :=
    ((mulLpLeft d).le_opNorm w).trans
      (mul_le_mul ((norm_mulLpLeft_le (p := 2) d).trans hd) hw
        (norm_nonneg _) C.bound.2)
  change ‖lowerOrderOperator _ _ u‖ ≤ _
  rw [lowerOrderOperator_apply]
  calc
    _ ≤ (∑ i, ‖mulLpLeft (C.driftSection t i) (derivCoordCLM i u)‖) +
        ‖mulLpLeft (C.potentialSection t) (baseCoordCLM u)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) le_rfl)
    _ ≤ (∑ _i : Fin n, (C.bound : ℝ) * ‖u‖) + C.bound * ‖u‖ :=
      add_le_add (Finset.sum_le_sum fun i _ ↦
        hmul _ (C.norm_driftSection_le t i) _ (derivCoordCLM_norm_le i u))
        (hmul _ (C.norm_potentialSection_le t) _ (baseCoordCLM_norm_le u))
    _ = C.operatorBound * ‖u‖ := by simp [operatorBound, add_mul, mul_assoc]

/-- Joint scalar measurability suffices for strong `L²` measurability of each evaluation. -/
theorem aestronglyMeasurable_operator_apply
    (C : BoundedCoefficients n Ω μ) (u : H¹₀(Ω)) :
    AEStronglyMeasurable (fun t ↦ C.operator t u) μ := by
  let : Fact ((2 : ENNReal) ≠ ∞) := ⟨by norm_num⟩
  let : SecondCountableTopology (DerivLp n 2 Ω) := Lp.SecondCountableTopology
  apply aestronglyMeasurable_of_forall_inner
  intro v
  have h (t : ℝ) : inner ℝ v (C.operator t u) =
      (∑ i, inner ℝ (C.driftSection t i • derivCoordCLM i u : DerivLp n 2 Ω) v) +
        inner ℝ (C.potentialSection t • baseCoordCLM u : DerivLp n 2 Ω) v := by
    rw [real_inner_comm]
    simp only [operator, lowerOrderOperator_apply, inner_add_left, sum_inner]
    rfl
  simp_rw [h]
  exact (Finset.aestronglyMeasurable_fun_sum _ fun i _ ↦
    aestronglyMeasurable_inner_Linfty_sections (C.drift_measurable i)
      (C.driftSection_ae i) (derivCoordCLM i u) v).add
    (aestronglyMeasurable_inner_Linfty_sections C.potential_measurable
      C.potentialSection_ae (baseCoordCLM u) v)

/-- The full form associated with a principal coefficient matrix and these lower-order terms. -/
def form (C : BoundedCoefficients n Ω μ)
    (A : ℝ → Fin n → Fin n → DerivLp n ∞ Ω) (t : ℝ) :
    H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
  fullDivergenceForm (multiplicationCoefficientOperator (A t))
    (fun i ↦ mulLpLeft (C.driftSection t i)) (mulLpLeft (C.potentialSection t))

/-- The full form is exactly its principal part plus the lower-order pivot load. -/
theorem form_eq_principal_add_pivot (C : BoundedCoefficients n Ω μ) (hΩ : IsOpen Ω)
    (A : ℝ → Fin n → Fin n → DerivLp n ∞ Ω) (t : ℝ) :
    C.form A t = variableCoeffForm (multiplicationCoefficientOperator (A t)) +
      (h10L2GelfandTriple hΩ).pivotToDual.comp (C.operator t) :=
  fullDivergenceForm_eq_principal_add_pivot_comp hΩ _ _ _

end BoundedCoefficients

end PDE.Parabolic.DivergenceFormHeat.LowerOrder
