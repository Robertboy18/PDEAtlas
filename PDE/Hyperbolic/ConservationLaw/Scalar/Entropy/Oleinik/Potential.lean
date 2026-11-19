/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.InitialValueWeakForm
public import PDE.Spaces.Sobolev.Calculus.Primitive.ConservativePair
import PDE.Hyperbolic.ConservationLaw.InitialBoundary.TimeCutoff
import PDE.Analysis.MeasureTheory.Lp.Continuous
import PDE.DistributionTheory.TestFunction

/-!
# Potentials of bounded scalar weak solutions

The initial weak conservation identity determines the spatial derivative of
the time-integrated flux. Together with the initial spatial primitive, this
constructs a potential with both weak partials whose initial value is the
primitive. Essential boundedness enters through a bounded measurable flux
representative.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace PDE.Common
open scoped Distributions ENNReal NNReal

namespace PDE.Hyperbolic.ConservationLaw

private theorem weak_initial_eq_planePair {F g : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (hu : IsWeakInitialValueSolution F g u) (huBdd : MemLp u ∞ (volume.restrict forwardHalfSpace))
    {q : ℝ^2 → ℝ} (hq : StronglyMeasurable q) (B : ℝ≥0) (hB : ∀ p, ‖q p‖ ≤ B)
    (heq : (F ∘ u) =ᵐ[volume.restrict forwardHalfSpace] q) (ψ : 𝓓((⊤ : Opens (ℝ × ℝ)), ℝ)) :
    (∫ p : ℝ × ℝ,
      (forwardHalfSpace : Set ℝ^2).indicator u (spaceTimePair p) *
        (TestFunction.lineDerivCLM (k := ⊤) ℝ (1, 0) ψ) p) +
      (∫ p : ℝ × ℝ,
        {p : ℝ × ℝ | 0 < p.1}.indicator (q ∘ spaceTimePair) p *
          (TestFunction.lineDerivCLM (k := ⊤) ℝ (0, 1) ψ) p) +
      (∫ x, g x * ψ (0, x)) = 0 := by
  let e : ℝ^2 ≃L[ℝ] ℝ × ℝ := (EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  let φSmooth : 𝓓((⊤ : Opens ℝ^2), ℝ) :=
    TestFunction.precompProper e e.contDiff e.toHomeomorph.isProperMap ψ
  let φ : InitialValueTestFunction :=
    .mk φSmooth (φSmooth.contDiff.of_le (by simp)) φSmooth.hasCompactSupport φSmooth.tsupport_subset
  have hφ (p : ℝ × ℝ) : φ (spaceTimePair p) = ψ p := by
    change ψ (e (spaceTimePair p)) = ψ p
    rfl
  have hφ₀ (x : ℝ) : φ !₂[0, x] = ψ (0, x) := by
    simpa only [spaceTimePair_apply] using hφ (0, x)
  have hderiv (i : Fin 2) (p : ℝ × ℝ) : (∂[i] (φ : ℝ^2 → ℝ)) (spaceTimePair p) =
        (TestFunction.lineDerivCLM (k := ⊤) ℝ (e (EuclideanSpace.single i 1)) ψ) p := by
    rw [TestFunction.lineDerivCLM_apply_eq_fderiv]
    change fderiv ℝ ((ψ : ℝ × ℝ → ℝ) ∘ e) (spaceTimePair p) (EuclideanSpace.single i 1) = _
    rw [fderiv_comp _ (ψ.contDiff.differentiable (by simp)).differentiableAt
      e.differentiableAt, e.fderiv, ContinuousLinearMap.comp_apply]
    rfl
  have hs : MeasurableSet (forwardHalfSpace : Set ℝ^2) := forwardHalfSpace.isOpen.measurableSet
  let U := (forwardHalfSpace : Set ℝ^2).indicator u
  let Q := (forwardHalfSpace : Set ℝ^2).indicator q
  have hU : LocallyIntegrable U volume :=
    ((memLp_indicator_iff_restrict hs.nullMeasurableSet).2 huBdd).locallyIntegrable le_top
  have hQ : LocallyIntegrable Q volume := (locallyIntegrable_of_aestronglyMeasurable_norm_le_const
      hq.aestronglyMeasurable B.coe_nonneg (Filter.Eventually.of_forall hB)).indicator hs
  have hiU : Integrable (fun p ↦ U p * (∂[0] (φ : ℝ^2 → ℝ)) p) volume :=
    φ.integrable_mul_partialDeriv (hU.locallyIntegrableOn univ) 0
  have hiQ : Integrable (fun p ↦ Q p * (∂[1] (φ : ℝ^2 → ℝ)) p) volume :=
    φ.integrable_mul_partialDeriv (hQ.locallyIntegrableOn univ) 1
  have hQeq : (forwardHalfSpace : Set ℝ^2).indicator (F ∘ u) =ᵐ[volume] Q :=
    (ae_eq_restrict_iff_indicator_ae_eq hs).1 heq
  have hinterior : (∫ p, U p * (∂[0] (φ : ℝ^2 → ℝ)) p + Q p * (∂[1] (φ : ℝ^2 → ℝ)) p) =
        ∫ p in forwardHalfSpace, InteriorWeakForm.integrand u (F ∘ u) φ p := by
    rw [← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [hQeq] with p hp
    rw [← hp]
    by_cases hmem : p ∈ forwardHalfSpace
    · simp only [U, Set.indicator_of_mem hmem, InteriorWeakForm.integrand, smul_eq_mul, mul_comm]
    · simp only [U, Set.indicator_of_notMem hmem, zero_mul, zero_add]
  have hn : (∫ p, U p * (∂[0] (φ : ℝ^2 → ℝ)) p) +
        (∫ p, Q p * (∂[1] (φ : ℝ^2 → ℝ)) p) + (∫ x, g x * φ !₂[0, x]) = 0 := by
    rw [← integral_add hiU hiQ, hinterior]
    simpa only [smul_eq_mul, mul_comm, Function.comp_def] using hu.weak_initial_eq φ
  have hleft := measurePreserving_spaceTimePair.integral_comp
    spaceTimePair.measurableEmbedding (fun p ↦ U p * (∂[0] (φ : ℝ^2 → ℝ)) p)
  have hright := measurePreserving_spaceTimePair.integral_comp
    spaceTimePair.measurableEmbedding (fun p ↦ Q p * (∂[1] (φ : ℝ^2 → ℝ)) p)
  rw [← hleft, ← hright] at hn
  have hQpair (p : ℝ × ℝ) : Q (spaceTimePair p) =
        {p : ℝ × ℝ | 0 < p.1}.indicator (q ∘ spaceTimePair) p := by
    by_cases hp : 0 < p.1 <;> simp [Q, forwardHalfSpace, spaceTimePair_apply, hp]
  have he0 : e (EuclideanSpace.single 0 1) = (1, 0) := by
    ext <;> simp [e]
  have he1 : e (EuclideanSpace.single 1 1) = (0, 1) := by
    ext <;> simp [e]
  simpa only [hderiv, hφ₀, hQpair, he0, he1] using hn

/-- A bounded weak initial solution has a constructed conservative potential.
Both derivatives are weak partials on the whole plane, extending the
initial primitive constantly to nonpositive time. The initial value is exact,
and the uniform time modulus follows from boundedness of the flux on the
essential range of the solution. -/
theorem IsWeakInitialValueSolution.exists_conservativePotential {F g : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (hu : IsWeakInitialValueSolution F g u) (huBdd : MemLp u ∞ (volume.restrict forwardHalfSpace))
    (hF : Continuous F) :
    ∃ (W : ℝ^2 → ℝ) (B : ℝ≥0),
      SobolevSpace.HasWeakDerivativeOn univ [0] W
        (fun p ↦ -(forwardHalfSpace : Set ℝ^2).indicator (F ∘ u) p) ∧
      SobolevSpace.HasWeakDerivativeOn univ [1] W
        (fun p ↦ if 0 < p 0 then u p else g (p 1)) ∧
      (∀ x, W !₂[0, x] = ∫ y in 0..x, g y) ∧
      (∀ p, ‖W p - ∫ y in 0..p 1, g y‖ ≤ B * max (p 0) 0) := by
  have hFu := hF.comp_memLp_top huBdd
  have hbound : eLpNormEssSup (F ∘ u) (volume.restrict forwardHalfSpace) < ⊤ := by
    simpa only [eLpNorm_exponent_top hFu.aestronglyMeasurable] using hFu.eLpNorm_lt_top
  obtain ⟨B, hB⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp hbound
  have hmem : ∀ᵐ p ∂volume.restrict forwardHalfSpace,
      (F ∘ u) p ∈ Metric.closedBall (0 : ℝ) B := by
    filter_upwards [hB] with p hp
    simpa only [Metric.mem_closedBall, dist_zero_right] using (show ‖(F ∘ u) p‖ ≤ (B : ℝ) from hp)
  obtain ⟨q, hq, hqB, heq⟩ := hFu.aestronglyMeasurable.exists_stronglyMeasurable_range_subset
    Metric.isClosed_closedBall.measurableSet (Metric.nonempty_closedBall.mpr B.coe_nonneg) hmem
  have hqnorm (p : ℝ^2) : ‖q p‖ ≤ B := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hqB p
  let Q : ℝ × ℝ → ℝ := q ∘ spaceTimePair
  let r : ℝ × ℝ → ℝ := (forwardHalfSpace : Set ℝ^2).indicator u ∘ spaceTimePair
  have hQ : StronglyMeasurable Q := hq.comp_measurable spaceTimePair.measurable
  have hQB (p : ℝ × ℝ) : ‖Q p‖ ≤ B := hqnorm (spaceTimePair p)
  have hs := forwardHalfSpace.isOpen.measurableSet
  have hr : LocallyIntegrable r volume :=
    (((memLp_indicator_iff_restrict hs.nullMeasurableSet).2 huBdd).comp_measurePreserving
      measurePreserving_spaceTimePair).locallyIntegrable le_top
  have hrzero (p : ℝ × ℝ) (hp : p.1 ≤ 0) : r p = 0 := by
    simp [r, forwardHalfSpace, spaceTimePair_apply, not_lt.mpr hp]
  have hweak := weak_initial_eq_planePair hu huBdd hq B hqnorm heq
  let W : ℝ^2 → ℝ := fun p ↦ PDE.Analysis.conservativePrimitive g Q (p 0, p 1)
  have htime := SobolevSpace.hasWeakDerivativeOn_conservativePrimitive_time
    hu.initial_locallyIntegrable hQ B hQB
  have hspace := SobolevSpace.hasWeakDerivativeOn_conservativePrimitive_space
    hu.initial_locallyIntegrable hr hrzero hQ B hQB hweak
  have hpair (p : ℝ^2) : spaceTimePair (p 0, p 1) = p := by
    rw [spaceTimePair_apply]
    ext i
    fin_cases i <;> simp
  have htimeeq : (fun p : ℝ^2 ↦ -{p : ℝ × ℝ | 0 < p.1}.indicator Q (p 0, p 1)) =ᵐ[volume]
        fun p ↦ -(forwardHalfSpace : Set ℝ^2).indicator (F ∘ u) p := by
    have h := (ae_eq_restrict_iff_indicator_ae_eq hs).1 heq
    filter_upwards [h] with p hp
    rw [hp]
    by_cases ht : 0 < p 0 <;> simp [Q, forwardHalfSpace, ht, hpair]
  have hspaceeq (p : ℝ^2) : r (p 0, p 1) +
        {p : ℝ × ℝ | p.1 ≤ 0}.indicator (fun p ↦ g p.2) (p 0, p 1) =
      if 0 < p 0 then u p else g (p 1) := by
    by_cases ht : 0 < p 0
    · simp [r, hpair, forwardHalfSpace, ht, not_le.mpr ht]
    · simp [r, hpair, forwardHalfSpace, ht, le_of_not_gt ht]
  refine ⟨W, B, ?_, ?_, ?_, ?_⟩
  · apply htime.congr_ae (Filter.EventuallyEq.refl _ _)
    simpa only [SobolevSpace.domainMeasure, Measure.restrict_univ] using htimeeq
  · apply hspace.congr_ae (Filter.EventuallyEq.refl _ _)
    exact Filter.Eventually.of_forall hspaceeq
  · exact fun x ↦ PDE.Analysis.conservativePrimitive_initial g Q x
  · exact fun p ↦ PDE.Analysis.norm_conservativePrimitive_sub_initial_le g Q B hQB (p 0, p 1)

end PDE.Hyperbolic.ConservationLaw
