/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Signed integrals with an integrable lower bound

The extended integral is the difference of the positive and negative
part integrals. An integrable lower bound makes the negative part finite.
Adding the opposite lower bound therefore changes this signed integral by
exactly its real integral, even when the positive part is infinite.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace PDE.Analysis

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g b : X → ℝ}

/-- The difference of the positive and negative part integrals in `EReal`.
An integrable lower bound guarantees that the negative part is finite. -/
def lowerBoundedIntegral (μ : Measure X) (f : X → ℝ) : EReal :=
  ((∫⁻ x, ENNReal.ofReal (f x) ∂μ) : EReal) -
    ((∫⁻ x, ENNReal.ofReal (-f x) ∂μ) : EReal)

/-- An a.e. integrable lower bound makes the negative part integral finite. -/
theorem lintegral_neg_part_lt_top_of_ae_lower_bound
    (hb : Integrable b μ) (hlower : ∀ᵐ x ∂μ, -b x ≤ f x) :
    ∫⁻ x, ENNReal.ofReal (-f x) ∂μ < ∞ := by
  refine (lintegral_mono_ae (hlower.mono fun x hx ↦ ?_)).trans_lt hb.hasFiniteIntegral
  exact (ENNReal.ofReal_le_ofReal (by linarith : -f x ≤ b x)).trans
    (Real.ofReal_le_enorm (b x))

/-- On integrable real functions, the extended signed integral agrees with
the ordinary Bochner integral. -/
theorem lowerBoundedIntegral_eq_integral (hf : Integrable f μ) :
    lowerBoundedIntegral μ f = ((∫ x, f x ∂μ : ℝ) : EReal) := by
  have hp : ∫⁻ x, ENNReal.ofReal (f x) ∂μ < ∞ :=
    (lintegral_mono fun x ↦ Real.ofReal_le_enorm (f x)).trans_lt hf.hasFiniteIntegral
  have hn : ∫⁻ x, ENNReal.ofReal (-f x) ∂μ < ∞ :=
    (lintegral_mono fun x ↦ Real.ofReal_le_enorm (-f x)).trans_lt hf.neg.hasFiniteIntegral
  rw [lowerBoundedIntegral, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf,
    EReal.coe_sub, EReal.coe_ennreal_toReal hp.ne, EReal.coe_ennreal_toReal hn.ne]

/-- Adding an integrable opposite lower bound gives the nonnegative integral,
up to its finite real integral. Infinite positive energies are retained. -/
theorem lowerBoundedIntegral_eq_lintegral_add_sub
    (hf : AEStronglyMeasurable f μ) (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, -b x ≤ f x) :
    lowerBoundedIntegral μ f =
      ((∫⁻ x, ENNReal.ofReal (f x + b x) ∂μ) : EReal) -
        ((∫ x, b x ∂μ : ℝ) : EReal) := by
  have hnonneg : ∀ᵐ x ∂μ, 0 ≤ f x + b x :=
    hlower.mono fun _ hx ↦ by linarith
  have hmeas : AEStronglyMeasurable (fun x ↦ f x + b x) μ :=
    hf.add hb.aestronglyMeasurable
  by_cases hfi : Integrable f μ
  · have hj := (lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).mpr (hfi.add hb)
    rw [lowerBoundedIntegral_eq_integral hfi, ← EReal.coe_ennreal_toReal hj,
      ← integral_eq_lintegral_of_nonneg_ae hnonneg hmeas, integral_add hfi hb,
      EReal.coe_add, EReal.add_sub_cancel_right]
  · have hn := lintegral_neg_part_lt_top_of_ae_lower_bound hb hlower
    have hp : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ∞ := by
      by_contra hp
      have hpos := integrable_toReal_of_lintegral_ne_top
        hf.aemeasurable.ennreal_ofReal hp
      have hneg := integrable_toReal_of_lintegral_ne_top
        hf.neg.aemeasurable.ennreal_ofReal hn.ne
      apply hfi
      convert hpos.sub hneg using 1
      funext x
      simp only [Pi.sub_apply, Pi.neg_apply, ENNReal.toReal_ofReal',
        max_zero_sub_max_neg_zero_eq_self]
    have hj : ∫⁻ x, ENNReal.ofReal (f x + b x) ∂μ = ∞ := by
      by_contra hj
      exact hfi ((integrable_add_iff_integrable_left hb).mp
        ((lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).mp hj))
    rw [lowerBoundedIntegral, hp, hj, EReal.coe_ennreal_top,
      ← EReal.coe_ennreal_toReal hn.ne]
    simp only [EReal.top_sub_coe]

/-- A common integrable shift preserves the order of signed energies,
including infinite energies. -/
theorem lowerBoundedIntegral_le_iff
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hb : Integrable b μ) (hf_lower : ∀ᵐ x ∂μ, -b x ≤ f x)
    (hg_lower : ∀ᵐ x ∂μ, -b x ≤ g x) :
    lowerBoundedIntegral μ f ≤ lowerBoundedIntegral μ g ↔
      ∫⁻ x, ENNReal.ofReal (f x + b x) ∂μ ≤
        ∫⁻ x, ENNReal.ofReal (g x + b x) ∂μ := by
  rw [lowerBoundedIntegral_eq_lintegral_add_sub hf hb hf_lower,
    lowerBoundedIntegral_eq_lintegral_add_sub hg hb hg_lower]
  simp only [sub_eq_add_neg, ← EReal.coe_neg,
    (EReal.addLECancellable_coe _).add_le_add_iff_right,
    EReal.coe_ennreal_le_coe_ennreal_iff]

/-- A lower-bounded signed energy is infinite exactly when its nonnegative
shifted integral is infinite. -/
theorem lowerBoundedIntegral_eq_top_iff
    (hf : AEStronglyMeasurable f μ) (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, -b x ≤ f x) :
    lowerBoundedIntegral μ f = ⊤ ↔
      ∫⁻ x, ENNReal.ofReal (f x + b x) ∂μ = ∞ := by
  rw [lowerBoundedIntegral_eq_lintegral_add_sub hf hb hlower]
  simp [sub_eq_add_neg, ← EReal.coe_neg]

/-- For a measurable real function with an integrable lower bound, finite
signed energy is equivalent to integrability of the original function. -/
theorem integrable_iff_lowerBoundedIntegral_ne_top
    (hf : AEStronglyMeasurable f μ) (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, -b x ≤ f x) :
    Integrable f μ ↔ lowerBoundedIntegral μ f ≠ ⊤ := by
  rw [ne_eq, lowerBoundedIntegral_eq_top_iff hf hb hlower]
  have hnonneg : ∀ᵐ x ∂μ, 0 ≤ f x + b x :=
    hlower.mono fun _ hx ↦ by linarith
  exact (integrable_add_iff_integrable_left hb).symm.trans
    (lintegral_ofReal_ne_top_iff_integrable
      (hf.add hb.aestronglyMeasurable) hnonneg).symm

/-- An integrable lower bound excludes negative infinite energy. -/
theorem lowerBoundedIntegral_ne_bot
    (hf : AEStronglyMeasurable f μ) (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, -b x ≤ f x) :
    lowerBoundedIntegral μ f ≠ ⊥ := by
  rw [lowerBoundedIntegral_eq_lintegral_add_sub hf hb hlower]
  simp [sub_eq_add_neg, ← EReal.coe_neg]

/-- On a finite measure space, a constant shift changes the original
signed energy by the constant times the measure of the whole space. -/
theorem lowerBoundedIntegral_eq_lintegral_add_const_sub [IsFiniteMeasure μ]
    (hf : AEStronglyMeasurable f μ) (β : ℝ) (hlower : ∀ᵐ x ∂μ, -β ≤ f x) :
    lowerBoundedIntegral μ f =
      ((∫⁻ x, ENNReal.ofReal (f x + β) ∂μ) : EReal) -
        ((β * μ.real Set.univ : ℝ) : EReal) := by
  simpa only [integral_const, smul_eq_mul, mul_comm] using
    lowerBoundedIntegral_eq_lintegral_add_sub hf (integrable_const β) hlower

/-- A common integrable shift preserves minimizers on any admissible class. -/
theorem isMinOn_lowerBoundedIntegral_iff
    {U : Type*} {A : Set U} {F : U → X → ℝ} {u : U}
    (hF : ∀ v ∈ A, AEStronglyMeasurable (F v) μ)
    (hb : Integrable b μ) (hlower : ∀ v ∈ A, ∀ᵐ x ∂μ, -b x ≤ F v x)
    (hu : u ∈ A) :
    IsMinOn (fun v ↦ lowerBoundedIntegral μ (F v)) A u ↔
      IsMinOn (fun v ↦ ∫⁻ x, ENNReal.ofReal (F v x + b x) ∂μ) A u := by
  constructor <;> intro h v hv
  · exact (lowerBoundedIntegral_le_iff (hF u hu) (hF v hv) hb
      (hlower u hu) (hlower v hv)).mp (h hv)
  · exact (lowerBoundedIntegral_le_iff (hF u hu) (hF v hv) hb
      (hlower u hu) (hlower v hv)).mpr (h hv)

/-- Coercion to signed extended values and a finite shift commute with liminf.
The statement includes sequences whose liminf is infinite. -/
theorem liminf_coe_ennreal_sub {ι : Type*} (l : Filter ι) [NeBot l]
    (a : ι → ℝ≥0∞) (c : ℝ) :
    liminf (fun i ↦ (a i : EReal) - (c : EReal)) l =
      ((liminf a l : ℝ≥0∞) : EReal) - (c : EReal) := by
  have hmono : Monotone (fun r : ℝ≥0∞ ↦ (r : EReal) + ((-c : ℝ) : EReal)) :=
    fun _ _ h ↦ add_le_add (EReal.coe_ennreal_le_coe_ennreal_iff.mpr h) le_rfl
  have hcont : Continuous (fun r : ℝ≥0∞ ↦ (r : EReal) + ((-c : ℝ) : EReal)) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _))
      (Or.inr (EReal.coe_ne_top _))).comp
        (continuous_coe_ennreal_ereal.continuousAt.prodMk continuousAt_const)
  simpa only [sub_eq_add_neg, ← EReal.coe_neg, Function.comp_def] using
    (hmono.map_liminf_of_continuousAt a hcont.continuousAt).symm

/-- Lower semicontinuity of nonnegative shifted energies implies lower
semicontinuity of the original signed integrals, with the same lower bound. -/
theorem lowerBoundedIntegral_le_liminf
    {ι : Type*} {l : Filter ι} [NeBot l] {F : ι → X → ℝ}
    (hf : AEStronglyMeasurable f μ) (hF : ∀ i, AEStronglyMeasurable (F i) μ)
    (hb : Integrable b μ) (hf_lower : ∀ᵐ x ∂μ, -b x ≤ f x)
    (hF_lower : ∀ i, ∀ᵐ x ∂μ, -b x ≤ F i x)
    (hlim : ∫⁻ x, ENNReal.ofReal (f x + b x) ∂μ ≤
      liminf (fun i ↦ ∫⁻ x, ENNReal.ofReal (F i x + b x) ∂μ) l) :
    lowerBoundedIntegral μ f ≤ liminf (fun i ↦ lowerBoundedIntegral μ (F i)) l := by
  simp_rw [lowerBoundedIntegral_eq_lintegral_add_sub hf hb hf_lower,
    lowerBoundedIntegral_eq_lintegral_add_sub (hF _) hb (hF_lower _)]
  rw [liminf_coe_ennreal_sub]
  simp only [sub_eq_add_neg, ← EReal.coe_neg,
    (EReal.addLECancellable_coe _).add_le_add_iff_right]
  exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr hlim

end PDE.Analysis
