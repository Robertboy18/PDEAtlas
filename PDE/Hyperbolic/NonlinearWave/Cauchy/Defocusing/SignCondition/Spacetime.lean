/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.UniformEstimates
public import PDE.Analysis.MeasureTheory.Lp.JointRepresentative
import PDE.Analysis.MeasureTheory.Lp.Continuous

/-!
# Spacetime representatives and uniform reaction-product bounds

Every truncated energy wave has a jointly measurable L² representative on a
finite time interval and the whole spatial domain. Fubini identifies the
reaction product with the mixed pairing in the PDE estimate. The resulting
spacetime L¹ bound is independent of the truncation's Lipschitz constant.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

variable {n : ℕ} {f : ℝ → ℝ} {K : NNReal}
  {x : H¹(ℝ^n) × DerivLp n 2 univ}
  {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}

/-- On each finite time interval a displacement curve has a jointly strongly
measurable L² representative, agreeing with its spatial sections almost everywhere. -/
theorem exists_displacement_jointRepresentative (T : ℝ) (u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)) :
    ∃ U : ℝ × (ℝ^n) → ℝ, StronglyMeasurable U ∧
      MemLp U 2 ((volume.restrict (Ioc 0 T)).prod (domainMeasure n univ)) ∧
      ∀ᵐ t ∂volume.restrict (Ioc 0 T),
        (fun y ↦ U (t, y)) =ᵐ[domainMeasure n univ] (energyTriple n).inclusion (u t).1 := by
  have hc : Continuous (fun t ↦ (energyTriple n).inclusion (u t).1) := by fun_prop
  have hm : MemLp (fun t ↦ (energyTriple n).inclusion (u t).1) 2 (volume.restrict (Ioc 0 T)) :=
    hc.continuousOn.memLp_of_subset_isCompact isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
  exact hm.exists_jointRepresentative

/-- A joint representative of a Lipschitz sign-preserving energy wave obeys the
literal spacetime product bound supplied by the PDE. No source-norm constant
appears in the estimate. -/
theorem lintegral_reaction_product_le (hf : LipschitzWith K f) (hs : ∀ z, 0 ≤ z * f z)
    (hu : Cauchy.IsEnergySolution hf (reaction_zero hf.continuous hs) x u) {T E : ℝ} (hT : 0 ≤ T)
    (he : ∀ t, 0 ≤ t → physicalEnergy f (u t) ≤ E) {U : ℝ × (ℝ^n) → ℝ}
    (hU : MemLp U 2 ((volume.restrict (Ioc 0 T)).prod (domainMeasure n univ)))
    (hsection : ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      (fun y ↦ U (t, y)) =ᵐ[domainMeasure n univ] (energyTriple n).inclusion (u t).1) :
    (∫⁻ z, ‖U z * f (U z)‖ₑ ∂(volume.restrict (Ioc 0 T)).prod (domainMeasure n univ)) ≤
      ENNReal.ofReal (2 * Real.sqrt (2 * E) * (‖(energyTriple n).inclusion x.1‖ + T *
      Real.sqrt (2 * E)) + T * Real.sqrt (2 * E) ^ 2) := by
  have hF := hf.comp_memLp (reaction_zero hf.continuous hs) hU
  have hprod : Integrable (fun z ↦ U z * f (U z))
      ((volume.restrict (Ioc 0 T)).prod (domainMeasure n univ)) := hU.integrable_mul hF
  rw [← ofReal_integral_norm_eq_lintegral_enorm hprod]
  apply ENNReal.ofReal_le_ofReal
  have hnorm : (fun z ↦ ‖U z * f (U z)‖) = fun z ↦ U z * f (U z) := by
    funext z
    exact Real.norm_of_nonneg (hs (U z))
  rw [hnorm, integral_prod_real _ hprod]
  have hident : (∫ t in Ioc 0 T, ∫ y, U (t, y) * f (U (t, y)) ∂domainMeasure n univ) =
      ∫ t in (0 : ℝ)..T, ∫ y, (energyTriple n).inclusion (u t).1 y *
        f ((energyTriple n).inclusion (u t).1 y) ∂domainMeasure n univ := by
    rw [intervalIntegral.integral_of_le hT]
    apply integral_congr_ae
    filter_upwards [hsection] with t ht
    apply integral_congr_ae
    filter_upwards [ht] with y hy
    rw [hy]
  rw [hident]
  exact integral_reaction_self_le hf hs hu he hT

/-- Restricting the spatial domain preserves a common product bound. This supplies
the finite-cylinder hypothesis used by the uniform-integrability theorem. -/
theorem lintegral_reaction_product_restrict_le {U : ℝ × (ℝ^n) → ℝ} {T : ℝ} {B : ENNReal}
    (h : (∫⁻ z, ‖U z * f (U z)‖ₑ ∂(volume.restrict (Ioc 0 T)).prod (domainMeasure n univ)) ≤ B)
    (s : Set (ℝ^n)) :
    (∫⁻ z, ‖U z * f (U z)‖ₑ
      ∂(volume.restrict (Ioc 0 T)).prod ((domainMeasure n univ).restrict s)) ≤ B :=
  (lintegral_mono' (Measure.prod_mono le_rfl Measure.restrict_le_self) le_rfl).trans h

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
