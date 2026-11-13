/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.LionsMagenes.Basic.Primitives
public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Basic
import PDE.Analysis.Evolution.LionsMagenes.EndpointRegularity.BackwardPrimitive
import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Uniqueness.Subtraction

/-!
# Coefficient integrability for Evans weak-wave uniqueness

We prove the three scalar `IntervalIntegrable` hypotheses of the
backward-energy theorem. They follow from:

* the `L²(a,b;V)` regularity already carried by a weak wave;
* strong measurability of the time-dependent operator fields;
* the usual uniform principal, time-derivative, and lower-order bounds.

For a divergence-form wave equation, strong measurability of the operator
fields follows from measurability of the coefficient functions after
integration against fixed spatial test functions.  Uniform ellipticity and
essential boundedness of the coefficients give the three bounds below.
Thus the final uniqueness theorem has Evans-style coefficient hypotheses
and no scalar pairing-integrability hypotheses.

For an autonomous symmetric coercive form, the coefficient conditions reduce to
symmetry and coercivity. The resulting corollary identifies the displacement,
velocity, and acceleration Bochner classes for a fixed load and initial data.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.1, assumptions (5)-(7), and §7.2.2, Theorem 4.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution

namespace IsGelfandWeakWaveSolution

variable
  {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {a b : ℝ}
  {T : GelfandTriple (V := V) (H := H)}
  {B : ℝ → V →L[ℝ] StrongDual ℝ V}
  {ell : Lp (StrongDual ℝ V) 2
    (volume.restrict (Set.Ioc a b))}
  {q₀ : V} {p₀ : H}

/-- Strongly measurable operator fields remain strongly measurable after
evaluation on two strongly measurable trajectories. -/
theorem aestronglyMeasurable_operator_pairing {μ : Measure ℝ} {C : ℝ → V →L[ℝ] StrongDual ℝ V}
    {x y : ℝ → V} (hC : AEStronglyMeasurable C μ) (hx : AEStronglyMeasurable x μ)
    (hy : AEStronglyMeasurable y μ) :
    AEStronglyMeasurable (fun t ↦ C t (x t) (y t)) μ := by
  have hCx : AEStronglyMeasurable (fun t ↦ C t (x t)) μ :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hC hx
  exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hCx hy

/-- A uniformly quadratically bounded, strongly measurable operator field
is integrable along an `L²` trajectory. -/
theorem integrable_quadratic_operator_pairing {μ : Measure ℝ} {C : ℝ → V →L[ℝ] StrongDual ℝ V}
    (x : Lp V 2 μ) (hC : AEStronglyMeasurable C μ) (L : ℝ)
    (hbound : ∀ᵐ t ∂μ, |C t (x t) (x t)| ≤ L * ‖x t‖ ^ 2) :
    Integrable (fun t ↦ C t (x t) (x t)) μ := by
  have hmeas : AEStronglyMeasurable (fun t ↦ C t (x t) (x t)) μ :=
    aestronglyMeasurable_operator_pairing hC (Lp.aestronglyMeasurable x) (Lp.aestronglyMeasurable x)
  have hmajorant : Integrable (fun t ↦ L * ‖x t‖ ^ 2) μ :=
    ((Lp.memLp x).integrable_norm_pow (by norm_num)).const_mul L
  apply hmajorant.mono' hmeas
  filter_upwards [hbound] with t ht
  simpa only [Real.norm_eq_abs] using ht

/-- A uniformly bounded, strongly measurable bilinear form is integrable
on two `L²` trajectories. -/
theorem integrable_bounded_operator_pairing {μ : Measure ℝ} {C : ℝ → V →L[ℝ] StrongDual ℝ V}
    (x y : Lp V 2 μ) (hC : AEStronglyMeasurable C μ) (L : ℝ)
    (hbound : ∀ᵐ t ∂μ, |C t (x t) (y t)| ≤ L * ‖x t‖ * ‖y t‖) :
    Integrable (fun t ↦ C t (x t) (y t)) μ := by
  have hmeas : AEStronglyMeasurable (fun t ↦ C t (x t) (y t)) μ :=
    aestronglyMeasurable_operator_pairing hC (Lp.aestronglyMeasurable x) (Lp.aestronglyMeasurable y)
  have hproduct : Integrable ((fun t ↦ ‖x t‖) * fun t ↦ ‖y t‖) μ :=
    (Lp.memLp x).norm.integrable_mul (Lp.memLp y).norm
  have hmajorant :
      Integrable (fun t ↦ L * (‖x t‖ * ‖y t‖)) μ := by
    simpa only [Pi.mul_apply] using hproduct.const_mul L
  apply hmajorant.mono' hmeas
  filter_upwards [hbound] with t ht
  simpa only [Real.norm_eq_abs, mul_assoc] using ht

/-- The quadratic coefficient-derivative pairing with Evans's backward
primitive is interval integrable. -/
theorem intervalIntegrable_quadratic_backwardTimePrimitive {C : ℝ → V →L[ℝ] StrongDual ℝ V}
    (u : Lp V 2 (volume.restrict (Set.Ioc a b))) (hab : a ≤ b)
    (hC : AEStronglyMeasurable C (volume.restrict (Set.Ioc a b))) (L : ℝ)
    (hbound : ∀ t ∈ Set.Icc a b, ∀ x : V, |C t x x| ≤ L * ‖x‖ ^ 2) {σ : ℝ} (hσ : σ ∈ Set.Icc a b) :
    IntervalIntegrable (fun t ↦ C t (backwardTimePrimitive (fun r ↦ u r) σ t)
      (backwardTimePrimitive (fun r ↦ u r) σ t)) volume a σ := by
  let μab := volume.restrict (Set.Ioc a b)
  let v : Lp V 2 μab := backwardTimePrimitiveLp u hab σ hσ
  have hboundAE :
      ∀ᵐ t ∂μab, |C t (v t) (v t)| ≤ L * ‖v t‖ ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hbound t ⟨ht.1.le, ht.2⟩ (v t)
  have hvIntegrable : Integrable (fun t ↦ C t (v t) (v t)) μab :=
    integrable_quadratic_operator_pairing v hC L hboundAE
  have hvCoe : ((v : ℝ → V) =ᵐ[μab] backwardTimePrimitive (fun r ↦ u r) σ) :=
    backwardTimePrimitiveLp_apply_ae u hab σ hσ
  have hactual : Integrable (fun t ↦ C t (backwardTimePrimitive (fun r ↦ u r) σ t)
            (backwardTimePrimitive (fun r ↦ u r) σ t))
        μab := by
    apply hvIntegrable.congr
    filter_upwards [hvCoe] with t ht
    rw [ht]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hσ.1]
  exact hactual.mono_measure <|
    (volume : Measure ℝ).restrict_mono_set <| by
      intro t ht
      exact ⟨ht.1, ht.2.trans hσ.2⟩

/-- A uniformly bounded principal form paired with an `L²` trajectory and
its backward primitive is interval integrable. -/
theorem intervalIntegrable_bounded_backwardTimePrimitive {C : ℝ → V →L[ℝ] StrongDual ℝ V}
    (u : Lp V 2 (volume.restrict (Set.Ioc a b))) (hab : a ≤ b)
    (hC : AEStronglyMeasurable C (volume.restrict (Set.Ioc a b))) (L : ℝ)
    (hbound : ∀ t ∈ Set.Icc a b, ∀ x y : V, |C t x y| ≤ L * ‖x‖ * ‖y‖) {σ : ℝ}
    (hσ : σ ∈ Set.Icc a b) :
    IntervalIntegrable (fun t ↦ C t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)) volume a
    σ := by
  let μab := volume.restrict (Set.Ioc a b)
  let v : Lp V 2 μab := backwardTimePrimitiveLp u hab σ hσ
  have hboundAE :
      ∀ᵐ t ∂μab, |C t (u t) (v t)| ≤ L * ‖u t‖ * ‖v t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hbound t ⟨ht.1.le, ht.2⟩ (u t) (v t)
  have hvIntegrable : Integrable (fun t ↦ C t (u t) (v t)) μab :=
    integrable_bounded_operator_pairing u v hC L hboundAE
  have hvCoe : ((v : ℝ → V) =ᵐ[μab] backwardTimePrimitive (fun r ↦ u r) σ) :=
    backwardTimePrimitiveLp_apply_ae u hab σ hσ
  have hactual : Integrable (fun t ↦ C t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t))
        μab := by
    apply hvIntegrable.congr
    filter_upwards [hvCoe] with t ht
    rw [ht]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hσ.1]
  exact hactual.mono_measure <|
    (volume : Measure ℝ).restrict_mono_set <| by
      intro t ht
      exact ⟨ht.1, ht.2.trans hσ.2⟩

/-- A lower-order form bounded on `H × V` is integrable against the
energy-space trajectory and its backward primitive. -/
theorem intervalIntegrable_pivotBounded_backwardTimePrimitive {C : ℝ → V →L[ℝ] StrongDual ℝ V}
    (u : Lp V 2 (volume.restrict (Set.Ioc a b))) (hab : a ≤ b)
    (hC : AEStronglyMeasurable C (volume.restrict (Set.Ioc a b))) (L : ℝ)
    (hbound : ∀ t ∈ Set.Icc a b, ∀ x y : V, |C t x y| ≤ L * ‖T.inclusion x‖ * ‖y‖) {σ : ℝ}
    (hσ : σ ∈ Set.Icc a b) :
    IntervalIntegrable (fun t ↦ C t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)) volume a
    σ := by
  let μab := volume.restrict (Set.Ioc a b)
  let v : Lp V 2 μab := backwardTimePrimitiveLp u hab σ hσ
  have hmeas : AEStronglyMeasurable (fun t ↦ C t (u t) (v t)) μab :=
    aestronglyMeasurable_operator_pairing hC (Lp.aestronglyMeasurable u) (Lp.aestronglyMeasurable v)
  have hproduct : Integrable ((fun t ↦ ‖T.inclusion (u t)‖) * fun t ↦ ‖v t‖) μab :=
    (T.inclusion.comp_memLp u).norm.integrable_mul (Lp.memLp v).norm
  have hmajorant : Integrable
        (fun t ↦ L * (‖T.inclusion (u t)‖ * ‖v t‖)) μab := by
    simpa only [Pi.mul_apply] using hproduct.const_mul L
  have hboundAE : ∀ᵐ t ∂μab, ‖C t (u t) (v t)‖ ≤
          L * (‖T.inclusion (u t)‖ * ‖v t‖) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [Real.norm_eq_abs, mul_assoc] using hbound t ⟨ht.1.le, ht.2⟩ (u t) (v t)
  have hvIntegrable : Integrable (fun t ↦ C t (u t) (v t)) μab := hmajorant.mono' hmeas hboundAE
  have hvCoe : ((v : ℝ → V) =ᵐ[μab] backwardTimePrimitive (fun r ↦ u r) σ) :=
    backwardTimePrimitiveLp_apply_ae u hab σ hσ
  have hactual : Integrable (fun t ↦ C t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t))
        μab := by
    apply hvIntegrable.congr
    filter_upwards [hvCoe] with t ht
    rw [ht]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hσ.1]
  exact hactual.mono_measure <|
    (volume : Measure ℝ).restrict_mono_set <| by
      intro t ht
      exact ⟨ht.1, ht.2.trans hσ.2⟩

/-- The full operator pairing in a homogeneous weak wave is integrable.

Indeed, the weak equation identifies `B(t)u(t)` with `-uₜₜ(t)` almost
everywhere.  The acceleration and backward primitive are both `L²`, so
their duality pairing belongs to `L¹`. -/
theorem intervalIntegrable_operator_backwardTimePrimitive_of_homogeneous [CompleteSpace V]
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))} {velocity : Lp H 2 (volume.restrict (Set.Ioc a b))}
    {acceleration : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h : IsGelfandWeakWaveSolution T B 0 u velocity acceleration 0 0) {σ : ℝ}
    (hσ : σ ∈ Set.Icc a b) :
    IntervalIntegrable (fun t ↦ B t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)) volume a
    σ := by
  let μab := volume.restrict (Set.Ioc a b)
  let v : Lp V 2 μab := backwardTimePrimitiveLp u h.interval_nonempty.le σ hσ
  have haccelerationPairing : Integrable (fun t ↦ acceleration t (v t)) μab :=
    integrable_dual_pairing acceleration v
  have hvCoe : ((v : ℝ → V) =ᵐ[μab] backwardTimePrimitive (fun r ↦ u r) σ) :=
    backwardTimePrimitiveLp_apply_ae u h.interval_nonempty.le σ hσ
  have hzero : (((0 : Lp (StrongDual ℝ V) 2 μab) : ℝ → StrongDual ℝ V) =ᵐ[μab] 0) :=
    Lp.coeFn_zero (StrongDual ℝ V) 2 μab
  have hoperatorPairing : Integrable (fun t ↦ B t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t))
        μab := by
    apply haccelerationPairing.neg.congr
    filter_upwards [h.equationAE, hvCoe, hzero] with t heq hv hz
    have heqZero : acceleration t + B t (u t) = 0 := by
      simpa only [hz, Pi.zero_apply] using heq
    have hB : B t (u t) = -acceleration t := eq_neg_of_add_eq_zero_right heqZero
    change -(acceleration t (v t)) = B t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)
    rw [hB, ← hv, neg_apply]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hσ.1]
  exact hoperatorPairing.mono_measure <|
    (volume : Measure ℝ).restrict_mono_set <| by
      intro t ht
      exact ⟨ht.1, ht.2.trans hσ.2⟩

/-- Integrability of the principal pairing follows from the homogeneous
weak equation and an integrable lower-order pairing.

The pairing `B(u,v)` is an `L²`-`L²` duality product and
`A(u,v) = B(u,v) - R(u,v)`. -/
theorem intervalIntegrable_principal_backwardTimePrimitive_of_split [CompleteSpace V]
    {A R : ℝ → V →L[ℝ] StrongDual ℝ V} {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {velocity : Lp H 2 (volume.restrict (Set.Ioc a b))}
    {acceleration : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h : IsGelfandWeakWaveSolution T B 0 u velocity acceleration 0 0)
    (hBsplit : ∀ t ∈ Set.Icc a b, ∀ x y : V, B t x y = A t x y + R t x y) {σ : ℝ}
    (hσ : σ ∈ Set.Icc a b)
    (hRIntegrable :
      IntervalIntegrable (fun t ↦ R t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)) volume a σ) :
    IntervalIntegrable (fun t ↦ A t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)) volume a
    σ := by
  have hBIntegrable := h.intervalIntegrable_operator_backwardTimePrimitive_of_homogeneous hσ
  apply (hBIntegrable.sub hRIntegrable).congr
  intro t ht
  have htIcc : t ∈ Set.Icc a b := by
    rw [Set.uIoc_of_le hσ.1] at ht
    exact ⟨ht.1.le, ht.2.trans hσ.2⟩
  have hsplit := hBsplit t htIcc (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)
  linarith

/--
Evans, §7.2.2 weak-wave uniqueness with coefficient-level assumptions.

Unlike `eq_of_evans_coefficients`, this theorem has no scalar `IntervalIntegrable` hypotheses. The
`L²` solution types and homogeneous weak equation provide integrability of `B(u,v)`, hence of
`A(u,v)=B(u,v)-R(u,v)`. Strong measurability is needed only for `Adot` and `R`, the two fields not
already represented by the weak equation. In concrete divergence form it follows from measurability
of the coefficient fields. `hAdotBound` follows from uniform bounds on the time derivative of the
principal coefficients. `hRBound` puts the `H` norm on the solution slot, so it follows from uniform
bounds on `c`, `b` and `div b` after a spatial integration by parts; bounds on `b` alone do not give
it.
-/
theorem eq_of_evans_coefficients_of_operator_measurable [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)] [CompleteSpace V]
    [CompleteSpace H] {A R Adot : ℝ → V →L[ℝ] StrongDual ℝ V}
    {u₁ u₂ : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {velocity₁ velocity₂ : Lp H 2 (volume.restrict (Set.Ioc a b))}
    {acceleration₁ acceleration₂ : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h₁ : IsGelfandWeakWaveSolution T B ell u₁ velocity₁ acceleration₁ q₀ p₀)
    (h₂ : IsGelfandWeakWaveSolution T B ell u₂ velocity₂ acceleration₂ q₀ p₀)
    (hBsplit : ∀ t ∈ Set.Icc a b, ∀ x y : V, B t x y = A t x y + R t x y)
    (hAAC : AbsolutelyContinuousOnInterval A a b)
    (hAderiv : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), HasDerivAt A (Adot t) t)
    (hAdotMeasurable : AEStronglyMeasurable Adot (volume.restrict (Set.Ioc a b)))
    (hRMeasurable : AEStronglyMeasurable R (volume.restrict (Set.Ioc a b)))
    (hAsymm : ∀ t ∈ Set.Icc a b, ∀ x y : V, A t x y = A t y x) (κ LA LR : ℝ) (hκ : 0 < κ)
    (hLA : 0 ≤ LA) (hLR : 0 ≤ LR) (hcoercive : ∀ t ∈ Set.Icc a b, ∀ x : V, κ * ‖x‖ ^ 2 ≤ A t x x)
    (hAdotBound : ∀ t ∈ Set.Icc a b, ∀ x : V, |Adot t x x| ≤ LA * ‖x‖ ^ 2)
    (hRBound : ∀ t ∈ Set.Icc a b, ∀ x y : V, |R t x y| ≤ LR * ‖T.inclusion x‖ * ‖y‖) :
    u₁ = u₂ ∧ velocity₁ = velocity₂ ∧ acceleration₁ = acceleration₂ := by
  have hab : a < b := h₁.interval_nonempty
  have hdifference := h₁.sub_same_data h₂
  have hAdotIntegrable : ∀ {σ : ℝ}, σ ∈ Set.Icc a b → IntervalIntegrable (fun t ↦ Adot t
              (backwardTimePrimitive (fun r ↦ (u₁ - u₂) r) σ t) (backwardTimePrimitive
                (fun r ↦ (u₁ - u₂) r) σ t))
          volume a σ := by
    intro σ hσ
    exact intervalIntegrable_quadratic_backwardTimePrimitive
      (u₁ - u₂) hab.le hAdotMeasurable LA hAdotBound hσ
  have hRIntegrable : ∀ {σ : ℝ}, σ ∈ Set.Icc a b → IntervalIntegrable (fun t ↦ R t ((u₁ - u₂) t)
              (backwardTimePrimitive (fun r ↦ (u₁ - u₂) r) σ t))
          volume a σ := by
    intro σ hσ
    exact intervalIntegrable_pivotBounded_backwardTimePrimitive
      (T := T) (u₁ - u₂) hab.le hRMeasurable LR hRBound hσ
  have hAIntegrable : ∀ {σ : ℝ}, σ ∈ Set.Icc a b → IntervalIntegrable (fun t ↦ A t ((u₁ - u₂) t)
              (backwardTimePrimitive (fun r ↦ (u₁ - u₂) r) σ t))
          volume a σ := by
    intro σ hσ
    exact hdifference.intervalIntegrable_principal_backwardTimePrimitive_of_split
        hBsplit hσ (hRIntegrable hσ)
  exact eq_of_evans_coefficients (h₁ := h₁) (h₂ := h₂) hBsplit hAAC hAderiv hAsymm
    hAdotIntegrable hAIntegrable hRIntegrable κ LA LR hκ hLA hLR hcoercive hAdotBound hRBound

end IsGelfandWeakWaveSolution

end Hyperbolic.Variational

section AutonomousUniqueness

open Filter
open scoped Topology InnerProductSpace Interval BigOperators ENNReal

namespace Hyperbolic.Variational.IsGelfandWeakWaveSolution

open PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- An autonomous symmetric coercive form determines at most one weak wave
with prescribed forcing and initial data. Equality holds for all three
Bochner classes. -/
theorem eq_of_autonomous_symmetric_coercive {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : V →L[ℝ] StrongDual ℝ V} {ell : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))} {q₀ : V}
    {p₀ : H} {u₁ u₂ : Lp V 2 (volume.restrict (Ioc a b))}
    {velocity₁ velocity₂ : Lp H 2 (volume.restrict (Ioc a b))}
    {acceleration₁ acceleration₂ : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (h₁ : IsGelfandWeakWaveSolution T (fun _ ↦ B) ell u₁ velocity₁ acceleration₁ q₀ p₀)
    (h₂ : IsGelfandWeakWaveSolution T (fun _ ↦ B) ell u₂ velocity₂ acceleration₂ q₀ p₀)
    (hsymm : ∀ x y : V, B x y = B y x) {κ : ℝ} (hκ : 0 < κ)
    (hcoercive : ∀ x : V, κ * ‖x‖ ^ 2 ≤ B x x) :
    u₁ = u₂ ∧ velocity₁ = velocity₂ ∧ acceleration₁ = acceleration₂ := by
  let : MeasurableSpace V := borel V
  have : BorelSpace V := ⟨rfl⟩
  let : MeasurableSpace (StrongDual ℝ V) := borel (StrongDual ℝ V)
  have : BorelSpace (StrongDual ℝ V) := ⟨rfl⟩
  have hAC : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ B) a b :=
    (LipschitzWith.const B).lipschitzOnWith.absolutelyContinuousOnInterval
  have hderiv : ∀ᵐ t ∂volume.restrict (Ioc a b),
      HasDerivAt (fun _ : ℝ ↦ B) (0 : V →L[ℝ] StrongDual ℝ V) t :=
    Filter.Eventually.of_forall fun t ↦ hasDerivAt_const t B
  refine h₁.eq_of_evans_coefficients_of_operator_measurable h₂
    (A := fun _ ↦ B) (R := fun _ ↦ 0) (Adot := fun _ ↦ 0)
    (fun _ _ x y ↦ by simp) hAC hderiv aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _ _ x y ↦ hsymm x y) κ 0 0 hκ le_rfl le_rfl (fun _ _ x ↦ hcoercive x) ?_ ?_
  · intro t ht x
    simp
  · intro t ht x y
    simp

end Hyperbolic.Variational.IsGelfandWeakWaveSolution

end AutonomousUniqueness
