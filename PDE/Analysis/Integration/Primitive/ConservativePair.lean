/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Primitive.WeakPairing
public import PDE.Analysis.Integration.LocallyIntegrable

/-!
# The primitive of a conservative pair

The potential is the spatial primitive of the initial datum minus the time
primitive of the flux. Its time derivative follows from the fundamental
theorem for measurable integrands. Its spatial derivative follows from the
initial weak conservation identity, tested with a compact backward primitive.

The construction extends the initial primitive constantly to negative time.
Consequently its global spatial weak derivative is the conserved field at
positive time and the initial datum at nonpositive time. The initial weak
identity is exactly what makes these two parts fit together.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions NNReal Topology

namespace PDE.Analysis

/-- The primitive determined by an initial datum and a flux field. -/
def conservativePrimitive (g : ℝ → ℝ) (q : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (∫ x in 0..p.2, g x) - forwardPrimitive q p

/-- The construction has its prescribed initial value at every spatial point. -/
@[simp] theorem conservativePrimitive_initial (g : ℝ → ℝ) (q : ℝ × ℝ → ℝ)
    (x : ℝ) :
    conservativePrimitive g q (0, x) = ∫ y in 0..x, g y := by
  rw [conservativePrimitive, forwardPrimitive_eq_zero_of_nonpos q le_rfl, sub_zero]

/-- A bounded flux controls the deviation from the initial primitive all the
way down to time zero. No regularity of the flux is required for this bound. -/
theorem norm_conservativePrimitive_sub_initial_le
    (g : ℝ → ℝ) (q : ℝ × ℝ → ℝ) (B : ℝ≥0)
    (hB : ∀ p, ‖q p‖ ≤ B) (p : ℝ × ℝ) :
    ‖conservativePrimitive g q p - ∫ x in 0..p.2, g x‖ ≤
      B * max p.1 0 := by
  simpa only [conservativePrimitive, sub_sub_cancel_left, norm_neg] using
    norm_forwardPrimitive_le B hB p

/-- The constructed potential is locally integrable on the entire plane. -/
theorem locallyIntegrable_conservativePrimitive
    {g : ℝ → ℝ} (hg : LocallyIntegrable g volume)
    {q : ℝ × ℝ → ℝ} (hq : StronglyMeasurable q)
    (B : ℝ≥0) (hB : ∀ p, ‖q p‖ ≤ B) :
    LocallyIntegrable (conservativePrimitive g q) volume := by
  have hh : LocallyIntegrable (fun x ↦ ∫ y in 0..x, g y) volume :=
    locallyIntegrableOn_univ.mp
      (Evolution.hasWeakTimeDerivativeOn_intervalPrimitive hg 0).locallyIntegrable_f
  have hh' : LocallyIntegrable (fun p : ℝ × ℝ ↦ ∫ y in 0..p.2, g y) volume := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    exact hh.comp_snd
  exact hh'.sub (locallyIntegrable_forwardPrimitive volume hq B hB)

/-- The weak time derivative of the potential is the negative flux
at positive time, extended by zero at nonpositive time. -/
theorem integral_conservativePrimitive_mul_timeDeriv
    {g : ℝ → ℝ} (hg : LocallyIntegrable g volume)
    {q : ℝ × ℝ → ℝ} (hq : StronglyMeasurable q)
    (B : ℝ≥0) (hB : ∀ p, ‖q p‖ ≤ B)
    (φ : 𝓓((⊤ : Opens (ℝ × ℝ)), ℝ)) :
    (∫ p, conservativePrimitive g q p *
        (TestFunction.lineDerivCLM (k := ⊤) ℝ (1, 0) φ) p) =
      ∫ p, ({p : ℝ × ℝ | 0 < p.1}.indicator q) p * φ p := by
  have hq' : LocallyIntegrable q volume :=
    locallyIntegrable_of_aestronglyMeasurable_norm_le_const hq.aestronglyMeasurable
      B.coe_nonneg (.of_forall hB)
  have hd (x : ℝ) : Evolution.HasWeakTimeDerivativeOn univ
      (fun t ↦ conservativePrimitive g q (t, x))
      (fun t ↦ -({p : ℝ × ℝ | 0 < p.1}.indicator q) (t, x)) := by
    have hc : Evolution.HasWeakTimeDerivativeOn univ
        (fun _ : ℝ ↦ ∫ y in 0..x, g y) (fun _ ↦ (0 : ℝ)) :=
      Evolution.HasWeakTimeDerivativeOn.of_absolutelyContinuousOnInterval
        (locallyIntegrable_const _) (locallyIntegrable_const _)
        (fun _ _ ↦ (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval)
        (.of_forall fun t ↦ hasDerivAt_const t _)
    have hind : (fun t ↦ (Ioi 0).indicator (fun t ↦ q (t, x)) t) =
        fun t ↦ ({p : ℝ × ℝ | 0 < p.1}.indicator q) (t, x) := by
      funext t
      by_cases ht : 0 < t <;> simp [ht]
    simpa only [conservativePrimitive, zero_sub, hind] using
      hc.sub (hasWeakTimeDerivativeOn_forwardPrimitive hq B hB x)
  have hz : LocallyIntegrable (fun p ↦ -({p : ℝ × ℝ | 0 < p.1}.indicator q) p) volume :=
    (hq'.indicator (measurableSet_lt measurable_const measurable_fst)).neg
  simpa only [neg_mul, integral_neg, neg_neg] using
    integral_mul_timeDeriv_of_weakTimeDerivative
      (locallyIntegrable_conservativePrimitive hg hq B hB) hz hd φ

/-- The initial conservation identity forces the spatial weak derivative of
the constructed potential. On nonpositive time it is the initial datum,
because the potential was extended constantly there. -/
theorem integral_conservativePrimitive_mul_spaceDeriv
    {g : ℝ → ℝ} (hg : LocallyIntegrable g volume)
    {r q : ℝ × ℝ → ℝ} (hr : LocallyIntegrable r volume)
    (hrzero : ∀ p : ℝ × ℝ, p.1 ≤ 0 → r p = 0)
    (hq : StronglyMeasurable q) (B : ℝ≥0) (hB : ∀ p, ‖q p‖ ≤ B)
    (hweak : ∀ ψ : 𝓓((⊤ : Opens (ℝ × ℝ)), ℝ),
      (∫ p, r p * (TestFunction.lineDerivCLM (k := ⊤) ℝ (1, 0) ψ) p) +
        (∫ p, ({p : ℝ × ℝ | 0 < p.1}.indicator q) p *
          (TestFunction.lineDerivCLM (k := ⊤) ℝ (0, 1) ψ) p) +
        (∫ x, g x * ψ (0, x)) = 0)
    (φ : 𝓓((⊤ : Opens (ℝ × ℝ)), ℝ)) :
    (∫ p, conservativePrimitive g q p *
        (TestFunction.lineDerivCLM (k := ⊤) ℝ (0, 1) φ) p) =
      -(∫ p, (r p +
        ({p : ℝ × ℝ | p.1 ≤ 0}.indicator (fun p ↦ g p.2)) p) * φ p) := by
  have hint {f : ℝ × ℝ → ℝ} (hf : LocallyIntegrable f volume)
      (ψ : 𝓓((⊤ : Opens (ℝ × ℝ)), ℝ)) : Integrable (fun p ↦ f p * ψ p) volume :=
    hf.integrable_smul_right_of_hasCompactSupport ψ.contDiff.continuous ψ.hasCompactSupport
  have hh := Evolution.hasWeakTimeDerivativeOn_intervalPrimitive hg 0
  have hH : LocallyIntegrable (fun p : ℝ × ℝ ↦ ∫ y in 0..p.2, g y) volume := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    exact (locallyIntegrableOn_univ.mp hh.locallyIntegrable_f).comp_snd
  have hg' : LocallyIntegrable (fun p : ℝ × ℝ ↦ g p.2) volume := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    exact hg.comp_snd
  -- test the weak identity with a backward primitive `ψ` of `φ`
  obtain ⟨R, hR, ψ, hzero, hvalue, hdt⟩ := TestFunction.exists_backwardPrimitive φ
  have hboundary : (∫ x, g x * ψ (0, x)) =
      ∫ p, ({p : ℝ × ℝ | 0 < p.1}.indicator fun p ↦ g p.2) p * φ p := by
    rw [← integral_mul_backwardPrimitive_initial hg φ hR.le hzero]
    exact integral_congr_ae (.of_forall fun x ↦ by simp only [hvalue (0, x) le_rfl])
  have hstate : (∫ p, r p * (TestFunction.lineDerivCLM (k := ⊤) ℝ (1, 0) ψ) p) =
      -∫ p, r p * φ p := by
    rw [← integral_neg]
    refine integral_congr_ae (.of_forall fun p ↦ ?_)
    by_cases ht : 0 < p.1
    · simp only [hdt p ht, mul_neg]
    · simp [hrzero p (le_of_not_gt ht)]
  have hw := hweak ψ
  rw [hstate, hboundary,
    ← integral_forwardPrimitive_mul_spaceDeriv_of_timeDeriv hq B hB φ ψ hdt] at hw
  have hS : MeasurableSet {p : ℝ × ℝ | 0 < p.1} := measurableSet_lt measurable_const measurable_fst
  have hparts : (∫ p, g p.2 * φ p) =
      (∫ p, ({p : ℝ × ℝ | 0 < p.1}.indicator fun p ↦ g p.2) p * φ p) +
        ∫ p, ({p : ℝ × ℝ | 0 < p.1}ᶜ.indicator fun p ↦ g p.2) p * φ p := by
    rw [← integral_add (hint (hg'.indicator hS) φ) (hint (hg'.indicator hS.compl) φ)]
    simp only [← add_mul, indicator_self_add_compl_apply]
  simp only [compl_ofPred, not_lt] at hparts
  have hS' : MeasurableSet {p : ℝ × ℝ | p.1 ≤ 0} := measurableSet_le measurable_fst measurable_const
  simp only [conservativePrimitive, sub_mul, add_mul]
  rw [integral_sub (hint hH _) (hint (locallyIntegrable_forwardPrimitive volume hq B hB) _),
    integral_add (hint hr φ) (hint (hg'.indicator hS') φ),
    integral_mul_spaceDeriv_of_weakTimeDerivative hH hg' (fun _ ↦ hh) φ]
  linarith

end PDE.Analysis
