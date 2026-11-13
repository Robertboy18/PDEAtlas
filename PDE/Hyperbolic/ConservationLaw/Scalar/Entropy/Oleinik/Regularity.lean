/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.Oleinik.Potential
public import PDE.Spaces.Sobolev.Inequalities.Morrey.Endpoint.TimeAverage
import PDE.Analysis.MeasureTheory.Lp.Continuous
import PDE.Hyperbolic.ConservationLaw.InitialBoundary.TimeCutoff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Regularity forced by the weak initial conservation identity

The constructed potential approaches the initial spatial primitive uniformly
as time decreases to zero. Positive-time averages therefore transfer the
solution's essential bound to the Lipschitz constant of that primitive.
Lebesgue differentiation then bounds the initial datum itself.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Common
open scoped ENNReal NNReal

namespace PDE.Hyperbolic.ConservationLaw

/-- A bounded weak initial solution forces its initial spatial primitive to
have the solution's spatial Lipschitz bound. The bound is derived from the
initial weak identity. -/
theorem IsWeakInitialValueSolution.lipschitzWith_initialPrimitive {F g : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (hu : IsWeakInitialValueSolution F g u) (huBdd : MemLp u ∞ (volume.restrict forwardHalfSpace))
    (hF : Continuous F) (A : ℝ≥0) (hA : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖u p‖ ≤ A) :
    LipschitzWith A (fun x ↦ ∫ y in 0..x, g y) := by
  obtain ⟨W, B, _htime, hspace, _hzero, hmod⟩ := hu.exists_conservativePotential huBdd hF
  let v : ℝ^1 → ℝ := fun x ↦ ∫ y in 0..x 0, g y
  have hprim : Continuous (fun x ↦ ∫ y in (0 : ℝ)..x, g y) := intervalIntegral.continuous_primitive
      (fun _ _ ↦ (hu.initial_locallyIntegrable.integrableOn_isCompact
        isCompact_uIcc).intervalIntegrable) 0
  have hv : Continuous v := hprim.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 ↦ ℝ) 0).continuous
  let r : Fin 1 → ℝ^2 → ℝ := fun _ p ↦ if 0 < p 0 then u p else g (p 1)
  have hweak (j : Fin 1) :
      SobolevSpace.HasWeakDerivativeOn univ [j.succ] W (r j) := by
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hspace
  have hbound (j : Fin 1) : ∀ᵐ p ∂volume, 0 < p 0 → ‖r j p‖ ≤ A := by
    have hA' := (ae_restrict_iff' forwardHalfSpace.isOpen.measurableSet).mp hA
    filter_upwards [hA'] with p hp ht
    simpa only [r, ite_eq_left ht] using hp ht
  have hmod' (p : ℝ^2) : ‖W p - v (spatialPart p)‖ ≤ B * max (p 0) 0 := hmod p
  have hLip := SobolevSpace.lipschitzWith_initial_of_positiveTime_weak_derivative_bound
    (locallyIntegrableOn_univ.mp hspace.locallyIntegrable_f) hv r hweak (fun _ ↦ A) hbound B hmod'
  have hLip' : LipschitzWith A v := by
    simpa only [Fin.sum_univ_one] using hLip
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  simpa only [v, PiLp.single_eq_same, PiLp.dist_single_same] using
    hLip'.dist_le_mul (PiLp.single 2 (0 : Fin 1) x) (PiLp.single 2 (0 : Fin 1) y)

/-- The initial datum of a bounded weak initial solution has the same
essential bound. This follows by differentiating the initial primitive, after
its Lipschitz estimate has been derived from positive times. -/
theorem IsWeakInitialValueSolution.ae_norm_initial_le {F g : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (hu : IsWeakInitialValueSolution F g u) (huBdd : MemLp u ∞ (volume.restrict forwardHalfSpace))
    (hF : Continuous F) (A : ℝ≥0) (hA : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖u p‖ ≤ A) :
    ∀ᵐ x ∂volume, ‖g x‖ ≤ A := by
  have hLip := hu.lipschitzWith_initialPrimitive huBdd hF A hA
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hu.initial_locallyIntegrable] with x hx
  exact (hx 0).le_of_lipschitz hLip

/-- The conservative potential has a globally Lipschitz representative with
both weak partials and its exact initial value. Its uniform approach to
the initial primitive survives the passage to this continuous representative. -/
theorem IsWeakInitialValueSolution.exists_lipschitzConservativePotential {F g : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (hu : IsWeakInitialValueSolution F g u) (huBdd : MemLp u ∞ (volume.restrict forwardHalfSpace))
    (hF : Continuous F) :
    ∃ (V : ℝ^2 → ℝ) (L B : ℝ≥0),
      LipschitzWith L V ∧
      SobolevSpace.HasWeakDerivativeOn univ [0] V
        (fun p ↦ -(forwardHalfSpace : Set ℝ^2).indicator (F ∘ u) p) ∧
      SobolevSpace.HasWeakDerivativeOn univ [1] V
        (fun p ↦ if 0 < p 0 then u p else g (p 1)) ∧
      (∀ x, V !₂[0, x] = ∫ y in 0..x, g y) ∧
      (∀ p, ‖V p - ∫ y in 0..p 1, g y‖ ≤ B * max (p 0) 0) := by
  have huEss : eLpNormEssSup u (volume.restrict forwardHalfSpace) < ⊤ := by
    simpa only [eLpNorm_exponent_top huBdd.aestronglyMeasurable] using huBdd.eLpNorm_lt_top
  obtain ⟨A, hA⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp huEss
  have hA' : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖u p‖ ≤ (A : ℝ) := hA
  have hg := hu.ae_norm_initial_le huBdd hF A hA'
  have hgPair : ∀ᵐ p : ℝ × ℝ ∂volume, ‖g p.2‖ ≤ (A : ℝ) := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_snd.ae hg
  have hgPlane : ∀ᵐ p : ℝ^2 ∂volume, ‖g (p 1)‖ ≤ (A : ℝ) := by
    have h := measurePreserving_spaceTimePair.symm.quasiMeasurePreserving.ae hgPair
    filter_upwards [h] with p hp
    have hcoord : (spaceTimePair.symm p).2 = p 1 := by
      have hc := congrArg (fun q : ℝ^2 ↦ q 1) (spaceTimePair.apply_symm_apply p)
      rwa [spaceTimePair_apply] at hc
    simpa only [hcoord] using hp
  have hFu := hF.comp_memLp_top huBdd
  have hFuEss : eLpNormEssSup (F ∘ u) (volume.restrict forwardHalfSpace) < ⊤ := by
    simpa only [eLpNorm_exponent_top hFu.aestronglyMeasurable] using hFu.eLpNorm_lt_top
  obtain ⟨D, hD⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp hFuEss
  have hD' : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖(F ∘ u) p‖ ≤ (D : ℝ) := hD
  obtain ⟨W, B, ht, hx, _hzero, hmod⟩ := hu.exists_conservativePotential huBdd hF
  let q : Fin 2 → ℝ^2 → ℝ := ![fun p ↦ -(forwardHalfSpace : Set ℝ^2).indicator (F ∘ u) p,
      fun p ↦ if 0 < p 0 then u p else g (p 1)]
  let C : Fin 2 → ℝ≥0 := ![D, A]
  have hq (i : Fin 2) : SobolevSpace.HasWeakDerivativeOn univ [i] W (q i) := by
    fin_cases i
    · exact ht
    · exact hx
  have hC (i : Fin 2) : ∀ᵐ p ∂volume, ‖q i p‖ ≤ C i := by
    have hAwhole := (ae_restrict_iff' forwardHalfSpace.isOpen.measurableSet).mp hA'
    have hDwhole := (ae_restrict_iff' forwardHalfSpace.isOpen.measurableSet).mp hD'
    fin_cases i
    · filter_upwards [hDwhole] with p hp
      change ‖-(forwardHalfSpace : Set ℝ^2).indicator (F ∘ u) p‖ ≤ (D : ℝ)
      by_cases hpos : p ∈ forwardHalfSpace
      · simpa only [Set.indicator_of_mem hpos, norm_neg] using hp hpos
      · simpa only [Set.indicator_of_notMem hpos, neg_zero, norm_zero] using D.coe_nonneg
    · filter_upwards [hAwhole, hgPlane] with p hp hgp
      change ‖if 0 < p 0 then u p else g (p 1)‖ ≤ (A : ℝ)
      by_cases hpos : 0 < p 0
      · simpa only [ite_eq_left hpos] using hp hpos
      · simpa only [ite_eq_right hpos] using hgp
  obtain ⟨V, hLip, heq⟩ := SobolevSpace.exists_lipschitzWith_ae_eq_of_weak_derivative_bound
      (locallyIntegrableOn_univ.mp ht.locallyIntegrable_f) q hq C hC
  have heq' : W =ᵐ[SobolevSpace.domainMeasure 2 univ] V := by
    simpa only [SobolevSpace.domainMeasure, Measure.restrict_univ] using heq.symm
  have hprim : Continuous (fun p : ℝ^2 ↦ ∫ y in (0 : ℝ)..p 1, g y) :=
    (intervalIntegral.continuous_primitive
      (fun _ _ ↦ (hu.initial_locallyIntegrable.integrableOn_isCompact
        isCompact_uIcc).intervalIntegrable) 0).comp (EuclideanSpace.proj 1).continuous
  have hmodV (p : ℝ^2) : ‖V p - ∫ y in 0..p 1, g y‖ ≤ B * max (p 0) 0 := by
    have hae : ∀ᵐ p ∂volume, ‖V p - ∫ y in 0..p 1, g y‖ ≤ B * max (p 0) 0 := by
      filter_upwards [heq] with p hp
      simpa only [hp] using hmod p
    exact (isClosed_le (hLip.continuous.sub hprim).norm (continuous_const.mul
        ((EuclideanSpace.proj 0).continuous.max continuous_const))).closure_subset
        ((volume : Measure (ℝ^2)).dense_of_ae hae p)
  refine ⟨V, ∑ i, C i, B, hLip, ht.congr_ae heq' (Filter.EventuallyEq.refl _ _),
    hx.congr_ae heq' (Filter.EventuallyEq.refl _ _), ?_, hmodV⟩
  intro x
  have hz : ‖V !₂[0, x] - ∫ y in 0..x, g y‖ ≤ 0 := by
    simpa using hmodV !₂[0, x]
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hz)

end PDE.Hyperbolic.ConservationLaw
