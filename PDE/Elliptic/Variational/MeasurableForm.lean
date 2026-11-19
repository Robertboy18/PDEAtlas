/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.BoundedSections
public import PDE.Analysis.MeasureTheory.StronglyMeasurable.Hilbert
public import PDE.Elliptic.Variational.LowerOrderForm

/-!
# Measurable divergence forms from joint scalar representatives

On a separable energy Hilbert space, scalar measurability of each form evaluation
gives strong measurability of the dual-valued form applied to each fixed state.
Fubini supplies the scalar measurability from joint representatives of the principal,
drift, and potential coefficients. The L∞-valued coefficients need not be strongly
measurable in norm.
-/

@[expose] public section

open MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SobolevSpace.GraphSpace

/-- Jointly measurable scalar coefficients give strongly measurable form evaluations.
Only the energy Hilbert space is assumed separable; no operator-norm measurability occurs. -/
theorem aestronglyMeasurable_multiplicationFullForm_apply_of_joint
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {n : ℕ} {Ω : Set (ℝ^n)}
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [SeparableSpace V]
    (D : Fin n → V →L[ℝ] DerivLp n 2 Ω) (hD : ∀ i u, ‖D i u‖ ≤ ‖u‖)
    (P : V →L[ℝ] DerivLp n 2 Ω) (hP : ∀ u, ‖P u‖ ≤ ‖u‖)
    {A : Fin n → Fin n → α × (ℝ^n) → ℝ}
    {B : Fin n → α × (ℝ^n) → ℝ} {C : α × (ℝ^n) → ℝ}
    {a : α → Fin n → Fin n → DerivLp n ∞ Ω}
    {b : α → Fin n → DerivLp n ∞ Ω} {c : α → DerivLp n ∞ Ω}
    (hA : ∀ i j, AEStronglyMeasurable (A i j) (μ.prod (domainMeasure n Ω)))
    (hB : ∀ i, AEStronglyMeasurable (B i) (μ.prod (domainMeasure n Ω)))
    (hC : AEStronglyMeasurable C (μ.prod (domainMeasure n Ω)))
    (ha : ∀ i j, ∀ᵐ t ∂μ,
      (fun x ↦ A i j (t, x)) =ᵐ[domainMeasure n Ω] (a t i j : (ℝ^n) → ℝ))
    (hb : ∀ i, ∀ᵐ t ∂μ,
      (fun x ↦ B i (t, x)) =ᵐ[domainMeasure n Ω] (b t i : (ℝ^n) → ℝ))
    (hc : ∀ᵐ t ∂μ, (fun x ↦ C (t, x)) =ᵐ[domainMeasure n Ω] (c t : (ℝ^n) → ℝ))
    (u : V) :
    AEStronglyMeasurable (fun t ↦
      (variableCoeffFormOf V V D hD D hD (multiplicationCoefficientOperator (a t)) +
        lowerOrderFormOf V D hD P hP (fun i ↦ mulLpLeft (b t i)) (mulLpLeft (c t))) u)
      μ := by
  apply ContinuousLinearMap.aestronglyMeasurable_dual_of_forall_apply
  intro v
  change AEStronglyMeasurable (fun t ↦
    (∑ i : Fin n, ∑ j : Fin n, inner ℝ (a t i j • D j u : DerivLp n 2 Ω) (D i v)) +
      ((∑ i : Fin n, inner ℝ (b t i • D i u : DerivLp n 2 Ω) (P v)) +
        inner ℝ (c t • P u : DerivLp n 2 Ω) (P v))) μ
  apply AEStronglyMeasurable.add
  · apply Finset.aestronglyMeasurable_fun_sum
    intro i _
    apply Finset.aestronglyMeasurable_fun_sum
    intro j _
    exact aestronglyMeasurable_inner_Linfty_sections (hA i j) (ha i j) (D j u) (D i v)
  · apply AEStronglyMeasurable.add
    · apply Finset.aestronglyMeasurable_fun_sum
      intro i _
      exact aestronglyMeasurable_inner_Linfty_sections (hB i) (hb i) (D i u) (P v)
    · exact aestronglyMeasurable_inner_Linfty_sections hC hc (P u) (P v)

end SobolevSpace.GraphSpace
