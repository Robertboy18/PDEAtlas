/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Primitive.SpaceTime
public import PDE.DistributionTheory.TestFunction.Slice
public import PDE.DistributionTheory.TestFunction.SpaceTime.Primitive
import PDE.Analysis.Integration.LocallyIntegrable

/-!
# Testing time primitives on a product

Fubini promotes the weak derivative on each time fiber to a joint
distributional identity. Local integrability gives integrability of both
tested terms.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions NNReal Topology

namespace PDE.Analysis

/-- Fiberwise weak differentiation may be tested by a family of one-dimensional tests
whenever both resulting product integrands are integrable. No joint smoothness of the
test family is required. -/
theorem integral_mul_fiberDeriv_of_weakTimeDerivative
    {f g : ℝ × ℝ → ℝ}
    (hd : ∀ x, Evolution.HasWeakTimeDerivativeOn univ
      (fun t ↦ f (t, x)) (fun t ↦ g (t, x)))
    (φ : ℝ → 𝓓((⊤ : Opens ℝ), ℝ))
    (hf : Integrable (fun p : ℝ × ℝ ↦ f p * deriv (φ p.2 : ℝ → ℝ) p.1)
      (volume.prod volume))
    (hg : Integrable (fun p : ℝ × ℝ ↦ g p * φ p.2 p.1) (volume.prod volume)) :
    (∫ p : ℝ × ℝ, f p * deriv (φ p.2 : ℝ → ℝ) p.1 ∂volume.prod volume) =
      -(∫ p : ℝ × ℝ, g p * φ p.2 p.1 ∂volume.prod volume) := by
  rw [integral_prod_symm _ hf, integral_prod_symm _ hg, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  have he := (hd x).integral_eq (ContinuousLinearMap.id ℝ ℝ)
    (φ x) (φ x).contDiff (φ x).hasCompactSupport (subset_univ _)
  simp only [ContinuousLinearMap.id_apply] at he
  simpa only [neg_neg] using congrArg Neg.neg he.symm

/-- Fiberwise weak differentiation gives joint integration by parts against
every smooth compactly supported test on the plane. -/
theorem integral_mul_timeDeriv_of_weakTimeDerivative
    {f g : ℝ × ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (hd : ∀ x, Evolution.HasWeakTimeDerivativeOn univ
      (fun t ↦ f (t, x)) (fun t ↦ g (t, x)))
    (φ : 𝓓((⊤ : Opens (ℝ × ℝ)), ℝ)) :
    (∫ p, f p * (TestFunction.lineDerivCLM (k := ⊤) ℝ (1, 0) φ) p) =
      -(∫ p, g p * φ p) := by
  let D : 𝓓((⊤ : Opens (ℝ × ℝ)), ℝ) := TestFunction.lineDerivCLM ℝ (1, 0) φ
  have hi : Integrable (fun p ↦ f p * D p) volume :=
    hf.integrable_smul_right_of_hasCompactSupport D.contDiff.continuous
      D.hasCompactSupport
  have hj : Integrable (fun p ↦ g p * φ p) volume :=
    hg.integrable_smul_right_of_hasCompactSupport φ.contDiff.continuous
      φ.hasCompactSupport
  rw [Measure.volume_eq_prod ℝ ℝ] at hi hj ⊢
  have hdφ (t x : ℝ) :
      deriv (TestFunction.sliceLeft x φ : ℝ → ℝ) t = D (t, x) := by
    have he := congrArg (fun ψ : 𝓓((⊤ : Opens ℝ), ℝ) ↦ ψ t)
      (TestFunction.lineDerivCLM_sliceLeft x (1 : ℝ) φ)
    simpa only [TestFunction.lineDerivCLM_apply_eq_fderiv,
      fderiv_apply_one_eq_deriv, TestFunction.sliceLeft_apply, D] using he
  simpa only [hdφ, TestFunction.sliceLeft_apply] using
    integral_mul_fiberDeriv_of_weakTimeDerivative hd (fun x ↦ TestFunction.sliceLeft x φ)
      (by simpa only [hdφ] using hi)
      (by simpa only [TestFunction.sliceLeft_apply] using hj)

/-- The corresponding joint identity when the second coordinate is the
variable of weak differentiation. -/
theorem integral_mul_spaceDeriv_of_weakTimeDerivative
    {f g : ℝ × ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (hd : ∀ t, Evolution.HasWeakTimeDerivativeOn univ
      (fun x ↦ f (t, x)) (fun x ↦ g (t, x)))
    (φ : 𝓓((⊤ : Opens (ℝ × ℝ)), ℝ)) :
    (∫ p, f p * (TestFunction.lineDerivCLM (k := ⊤) ℝ (0, 1) φ) p) =
      -(∫ p, g p * φ p) := by
  let D : 𝓓((⊤ : Opens (ℝ × ℝ)), ℝ) := TestFunction.lineDerivCLM ℝ (0, 1) φ
  have hi : Integrable (fun p ↦ f p * D p) volume :=
    hf.integrable_smul_right_of_hasCompactSupport D.contDiff.continuous
      D.hasCompactSupport
  have hj : Integrable (fun p ↦ g p * φ p) volume :=
    hg.integrable_smul_right_of_hasCompactSupport φ.contDiff.continuous
      φ.hasCompactSupport
  rw [Measure.volume_eq_prod ℝ ℝ] at hi hj ⊢
  have hdφ (x t : ℝ) :
      deriv (TestFunction.sliceRight t φ : ℝ → ℝ) x = D (t, x) := by
    have he := congrArg (fun ψ : 𝓓((⊤ : Opens ℝ), ℝ) ↦ ψ x)
      (TestFunction.lineDerivCLM_sliceRight t (1 : ℝ) φ)
    simpa only [TestFunction.lineDerivCLM_apply_eq_fderiv,
      fderiv_apply_one_eq_deriv, TestFunction.sliceRight_apply, D] using he
  have he := integral_mul_fiberDeriv_of_weakTimeDerivative
    (f := fun p ↦ f p.swap) (g := fun p ↦ g p.swap) hd
    (fun t ↦ TestFunction.sliceRight t φ)
    (by simpa only [hdφ, Function.comp_def, Prod.swap] using hi.swap)
    (by simpa only [TestFunction.sliceRight_apply, Function.comp_def, Prod.swap] using hj.swap)
  simp only [hdφ, TestFunction.sliceRight_apply] at he
  change (∫ p, (fun q ↦ f q * D q) p.swap ∂volume.prod volume) =
    -(∫ p, (fun q ↦ g q * φ q) p.swap ∂volume.prod volume) at he
  rwa [integral_prod_swap (fun q : ℝ × ℝ ↦ f q * D q),
    integral_prod_swap (fun q : ℝ × ℝ ↦ g q * φ q)] at he

/-- The time primitive of a bounded measurable field has its joint
weak time derivative, including its zero extension across the initial time. -/
theorem integral_forwardPrimitive_mul_timeDeriv
    {q : ℝ × ℝ → ℝ} (hq : StronglyMeasurable q)
    (B : ℝ≥0) (hB : ∀ p, ‖q p‖ ≤ B)
    (φ : 𝓓((⊤ : Opens (ℝ × ℝ)), ℝ)) :
    (∫ p, forwardPrimitive q p * (TestFunction.lineDerivCLM (k := ⊤) ℝ (1, 0) φ) p) =
      -(∫ p, ({p : ℝ × ℝ | 0 < p.1}.indicator q) p * φ p) := by
  apply integral_mul_timeDeriv_of_weakTimeDerivative
    (locallyIntegrable_forwardPrimitive volume hq B hB)
  · have hm : StronglyMeasurable ({p : ℝ × ℝ | 0 < p.1}.indicator q) :=
      hq.indicator (measurableSet_lt measurable_const measurable_fst)
    have hb : ∀ p, ‖({p : ℝ × ℝ | 0 < p.1}.indicator q) p‖ ≤ B := by
      intro p
      by_cases hp : 0 < p.1
      · simpa [hp] using hB p
      · simp [hp]
    exact (memLp_top_of_bound (μ := volume) hm.aestronglyMeasurable (B : ℝ)
      (Filter.Eventually.of_forall hb)).locallyIntegrable (by simp)
  · intro x
    change Evolution.HasWeakTimeDerivativeOn univ
      (fun t ↦ forwardPrimitive q (t, x)) ((Ioi 0).indicator (fun t ↦ q (t, x)))
    exact hasWeakTimeDerivativeOn_forwardPrimitive hq B hB x

/-- A backward test transfers a spatial derivative of the forward primitive
to the original field. Only derivatives of smooth tests are commuted. -/
theorem integral_forwardPrimitive_mul_spaceDeriv_of_timeDeriv
    {q : ℝ × ℝ → ℝ} (hq : StronglyMeasurable q)
    (B : ℝ≥0) (hB : ∀ p, ‖q p‖ ≤ B)
    (φ ψ : 𝓓((⊤ : Opens (ℝ × ℝ)), ℝ))
    (hψ : ∀ p : ℝ × ℝ, 0 < p.1 →
      (TestFunction.lineDerivCLM (k := ⊤) ℝ (1, 0) ψ) p = -φ p) :
    (∫ p, forwardPrimitive q p *
        (TestFunction.lineDerivCLM (k := ⊤) ℝ (0, 1) φ) p) =
      ∫ p, ({p : ℝ × ℝ | 0 < p.1}.indicator q) p *
        (TestFunction.lineDerivCLM (k := ⊤) ℝ (0, 1) ψ) p := by
  let Dt : 𝓓((⊤ : Opens (ℝ × ℝ)), ℝ) →L[ℝ]
      𝓓((⊤ : Opens (ℝ × ℝ)), ℝ) := TestFunction.lineDerivCLM ℝ (1, 0)
  let Dx : 𝓓((⊤ : Opens (ℝ × ℝ)), ℝ) →L[ℝ]
      𝓓((⊤ : Opens (ℝ × ℝ)), ℝ) := TestFunction.lineDerivCLM ℝ (0, 1)
  have hmixed (p : ℝ × ℝ) (hp : 0 < p.1) : Dt (Dx ψ) p = -Dx φ p := by
    have hcomm := congrArg
      (fun A : 𝓓((⊤ : Opens (ℝ × ℝ)), ℝ) →L[ℝ]
          𝓓((⊤ : Opens (ℝ × ℝ)), ℝ) ↦ A ψ p)
      (TestFunction.lineDerivCLM_commute (Ω := ⊤) (F := ℝ)
        ((1, 0) : ℝ × ℝ) (0, 1))
    change Dt (Dx ψ) p = Dx (Dt ψ) p at hcomm
    rw [hcomm]
    have hnear : (Dt ψ : ℝ × ℝ → ℝ) =ᶠ[𝓝 p] (-φ : ℝ × ℝ → ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hp] with y hy
      exact hψ y hy
    change fderiv ℝ (Dt ψ) p (0, 1) = -Dx φ p
    rw [hnear.fderiv_eq, fderiv_neg]
    rfl
  have he := integral_forwardPrimitive_mul_timeDeriv hq B hB (Dx ψ)
  have hi :
      (∫ p, forwardPrimitive q p * Dt (Dx ψ) p) =
        -(∫ p, forwardPrimitive q p * Dx φ p) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with p
    by_cases hp : 0 < p.1
    · rw [hmixed p hp, mul_neg]
    · rw [forwardPrimitive_eq_zero_of_nonpos q (le_of_not_gt hp)]
      simp
  rw [hi] at he
  exact neg_injective he

/-- The initial value of a backward primitive pairs with the initial datum
as an integral over the positive half-plane. Local integrability of the
datum and compact support of the test justify Fubini. -/
theorem integral_mul_backwardPrimitive_initial
    {g : ℝ → ℝ} (hg : LocallyIntegrable g volume)
    (φ : 𝓓((⊤ : Opens (ℝ × ℝ)), ℝ)) {R : ℝ} (hR : 0 ≤ R)
    (hzero : ∀ p : ℝ × ℝ, R ≤ p.1 → φ p = 0) :
    (∫ x, g x * backwardPrimitive φ R (0, x)) =
      ∫ p, ({p : ℝ × ℝ | 0 < p.1}.indicator (fun p ↦ g p.2)) p * φ p := by
  have hS : MeasurableSet {p : ℝ × ℝ | 0 < p.1} :=
    measurableSet_lt measurable_const measurable_fst
  have hg' : LocallyIntegrable (fun p : ℝ × ℝ ↦ g p.2) volume := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    exact hg.comp_snd
  have hi : Integrable
      (fun p : ℝ × ℝ ↦ ({p : ℝ × ℝ | 0 < p.1}.indicator
        (fun p ↦ g p.2)) p * φ p) volume := by
    convert (hg'.integrable_smul_right_of_hasCompactSupport
      φ.contDiff.continuous φ.hasCompactSupport).indicator hS using 1
    ext p
    by_cases hp : 0 < p.1 <;> simp [hp]
  rw [Measure.volume_eq_prod ℝ ℝ] at hi ⊢
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards with x
  have hφ : Integrable (fun t ↦ φ (t, x)) volume :=
    (TestFunction.sliceLeft x φ).contDiff.continuous.integrable_of_hasCompactSupport
      (TestFunction.sliceLeft x φ).hasCompactSupport
  have hz : (∫ t in Ioi R, φ (t, x)) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero (fun t ht ↦ hzero (t, x) ht.le)
  have hinterval := intervalIntegral.integral_Ioi_sub_Ioi hφ.integrableOn hR
  rw [hz, sub_zero] at hinterval
  change g x * (∫ t in 0..R, φ (t, x)) = _
  rw [← hinterval, ← integral_indicator measurableSet_Ioi, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : 0 < t <;> simp [ht]

end PDE.Analysis
