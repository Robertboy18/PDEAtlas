/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.LowerOrderForm
public import PDE.Elliptic.Variational.CoefficientDependence

/-!
# Multiplication coefficients in the lower-order wave form

The drift and potential form satisfies a stronger estimate than mere boundedness
on the energy space: its second argument needs only its `L²` norm. This is the
estimate used to control the lower-order work in the wave energy identity.

The coefficient-to-form map constructed here also makes the time measurability
assumption concrete. Strong measurability of a curve in the `L∞` coefficient
space implies strong measurability of its form in operator norm.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (D : Fin n → V →L[ℝ] DerivLp n 2 Ω) (hD : ∀ i u, ‖D i u‖ ≤ ‖u‖)
  (P : V →L[ℝ] DerivLp n 2 Ω) (hP : ∀ u, ‖P u‖ ≤ ‖u‖)

/-- For multiplication coefficients the lower-order wave bound is controlled by
the sum of the essential suprema of the drift entries and the potential. No
spatial derivatives, symmetry, or sign condition on these coefficients is used. -/
theorem norm_multiplicationLowerOrderFormOf_apply_le_base
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω) (u v : V) :
    ‖lowerOrderFormOf V D hD P hP (fun i ↦ mulLpLeft (b i)) (mulLpLeft c) u v‖ ≤
      ((∑ i : Fin n, ‖b i‖) + ‖c‖) * ‖u‖ * ‖P v‖ := by
  refine (norm_lowerOrderFormLinOf_apply_le_base V D hD P hP _ _ u v).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact add_le_add
    (Finset.sum_le_sum fun i _ ↦ norm_mulLpLeft_le (p := 2) (b i))
    (norm_mulLpLeft_le (p := 2) c)

/-- The operator norm of the multiplication lower-order form is at most the sum
of the drift-entry and potential `L∞` norms. This also bounds the full form after
adding the principal-part estimate. -/
theorem norm_multiplicationLowerOrderFormOf_le
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω) :
    ‖lowerOrderFormOf V D hD P hP (fun i ↦ mulLpLeft (b i)) (mulLpLeft c)‖ ≤
      (∑ i : Fin n, ‖b i‖) + ‖c‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  exact (norm_multiplicationLowerOrderFormOf_apply_le_base V D hD P hP b c u v).trans
    (mul_le_mul_of_nonneg_left (hP v) (by positivity))

/-- The bounded linear map from the drift and potential in `L∞` to their
lower-order bilinear form. Its construction uses pointwise multiplication,
so it does not assume an operator-valued coefficient realization. -/
def multiplicationLowerOrderFormCLMOf :
    ((Fin n → DerivLp n ∞ Ω) × DerivLp n ∞ Ω) →L[ℝ] (V →L[ℝ] V →L[ℝ] ℝ) := by
  classical
  let L : ((Fin n → DerivLp n ∞ Ω) × DerivLp n ∞ Ω) →ₗ[ℝ]
      (V →L[ℝ] V →L[ℝ] ℝ) :=
    { toFun := fun z ↦
        lowerOrderFormOf V D hD P hP (fun i ↦ mulLpLeft (z.1 i)) (mulLpLeft z.2)
      map_add' := by
        intro z w
        ext u v
        change (∑ i : Fin n, inner ℝ ((z.1 i + w.1 i) • D i u) (P v)) +
            inner ℝ ((z.2 + w.2) • P u) (P v) =
          ((∑ i : Fin n, inner ℝ (z.1 i • D i u) (P v)) +
            inner ℝ (z.2 • P u) (P v)) +
          ((∑ i : Fin n, inner ℝ (w.1 i • D i u) (P v)) +
            inner ℝ (w.2 • P u) (P v))
        simp only [Lp.smul_add, inner_add_left, Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro r z
        ext u v
        change (∑ i : Fin n, inner ℝ ((r • z.1 i) • D i u) (P v)) +
            inner ℝ ((r • z.2) • P u) (P v) =
          r * ((∑ i : Fin n, inner ℝ (z.1 i • D i u) (P v)) +
            inner ℝ (z.2 • P u) (P v))
        simp only [Lp.smul_assoc, real_inner_smul_left, ← Finset.mul_sum, mul_add] }
  refine LinearMap.mkContinuous
    (E := (Fin n → DerivLp n ∞ Ω) × DerivLp n ∞ Ω)
    (F := V →L[ℝ] V →L[ℝ] ℝ) L ((n : ℝ) + 1) ?_
  intro z
  have hz :
      (∑ i : Fin n, ‖z.1 i‖) + ‖z.2‖ ≤ ((n : ℝ) + 1) * ‖z‖ := by
    calc
      _ ≤ (∑ _i : Fin n, ‖z‖) + ‖z‖ :=
        add_le_add
          (Finset.sum_le_sum fun i _ ↦
            (norm_le_pi_norm z.1 i).trans (norm_fst_le z))
          (norm_snd_le z)
      _ = ((n : ℝ) + 1) * ‖z‖ := by simp [add_mul]
  exact (norm_multiplicationLowerOrderFormOf_le V D hD P hP z.1 z.2).trans hz

/-- Strongly measurable curves of principal, drift, and potential coefficients
in `L∞` produce a strongly measurable curve of full forms in operator norm.
The time measure is arbitrary, and no spatial boundary regularity is needed. -/
theorem aestronglyMeasurable_multiplicationFullFormOf
    {ι : Type*} [MeasurableSpace ι] {ν : Measure ι}
    {a : ι → Fin n → Fin n → DerivLp n ∞ Ω}
    {z : ι → (Fin n → DerivLp n ∞ Ω) × DerivLp n ∞ Ω}
    (ha : AEStronglyMeasurable a ν) (hz : AEStronglyMeasurable z ν) :
    AEStronglyMeasurable
      (fun t ↦
        variableCoeffFormOf V V D hD D hD (multiplicationCoefficientOperator (a t)) +
        lowerOrderFormOf V D hD P hP
          (fun i ↦ mulLpLeft ((z t).1 i)) (mulLpLeft (z t).2)) ν := by
  let : IsTopologicalAddGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
    ContinuousLinearMap.isTopologicalAddGroup
  let : ContinuousAdd (V →L[ℝ] V →L[ℝ] ℝ) :=
    ContinuousLinearMap.isTopologicalAddGroup.toContinuousAdd
  change AEStronglyMeasurable
    (fun t ↦ multiplicationCoeffFormCLMOf V V D hD D hD (a t) +
      multiplicationLowerOrderFormCLMOf V D hD P hP (z t)) ν
  exact AEStronglyMeasurable.add (β := V →L[ℝ] V →L[ℝ] ℝ)
    ((multiplicationCoeffFormCLMOf V V D hD D hD).continuous.comp_aestronglyMeasurable ha)
    ((multiplicationLowerOrderFormCLMOf V D hD P hP).continuous.comp_aestronglyMeasurable hz)

end SobolevSpace.GraphSpace
