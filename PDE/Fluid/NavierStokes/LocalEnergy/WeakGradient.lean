/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.LocalEnergy.Testing
import PDE.Analysis.MeasureTheory.StronglyMeasurable.Product
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
import PDE.Spaces.Sobolev.Calculus.Slicing.SpaceTime.TensorTesting
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Identifying the physical weak gradient at positive times

Uniqueness of weak derivatives identifies the stored gradient on each positive
time slice. Joint measurability then combines these identities by Fubini.
This supplies the gradient compatibility needed by the suitable-solution
constructor, without imposing regularity on the singular initial datum.
-/

@[expose] public noncomputable section

namespace NavierStokes

open MeasureTheory IncompressibleFlow PDE PDE.Common SobolevSpace

set_option linter.missingDocs true

/-- The stored weak gradient agrees with the classical gradient on every
interior time slice of a positive-time regular velocity. -/
theorem PressureWeakSolution.gradient_slice_ae_eq_of_positiveTime_regular
    {n : ℕ} {nse : Problem n} (sol : PressureWeakSolution nse)
    (hu : ∀ z ∈ finiteTimeDomain n sol.T, ContDiffAt ℝ 1 sol.u z)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 (sol.T : ℝ)) :
    (fun x ↦ sol.Du (timeSpaceCons t x)) =ᵐ[volume]
      fun x ↦ spatialVelocityGradient n sol.u (timeSpaceCons t x) := by
  have hcomp (i j : Fin n) :
      (fun x ↦ sol.Du (timeSpaceCons t x) (i, j)) =ᵐ[volume]
        ∂[j] (fun x ↦ sol.u (timeSpaceCons t x) i) := by
    have hf (x : ℝ^n) (_ : x ∈ Set.univ) :
        ContDiffAt ℝ 1 (fun x ↦ sol.u (timeSpaceCons t x) i) x := by
      have hz : timeSpaceCons t x ∈ finiteTimeDomain n sol.T := by
        simpa only [finiteTimeDomain, Set.mem_ofPred_eq, timeSpaceCons_zero, Set.mem_Ioo] using ht
      exact ((contDiffAt_piLp 2).mp (hu _ hz) i).comp x
        (contDiff_timeSpaceCons_spatial n t (m := 1)).contDiffAt
    simpa only [domainMeasure, Measure.restrict_univ] using
      (sol.hasWeakSpatialDerivative ⟨ht.1, ht.2.le⟩ i j).unique_ae isOpen_univ
        (hasWeakDerivativeOn_of_contDiffAt_one isOpen_univ hf j)
  have hall : ∀ᵐ x ∂volume, ∀ i j : Fin n,
      sol.Du (timeSpaceCons t x) (i, j) =
        (∂[j] (fun x ↦ sol.u (timeSpaceCons t x) i)) x :=
    ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦ hcomp i j
  filter_upwards [hall] with x hx
  ext ⟨i, j⟩
  rw [spatialVelocityGradient_apply, hx i j]
  apply partialDeriv_timeSpaceCons_spatial j (fun y ↦ sol.u y i) t x
  have hz : timeSpaceCons t x ∈ finiteTimeDomain n sol.T := by
    simpa only [finiteTimeDomain, Set.mem_ofPred_eq, timeSpaceCons_zero, Set.mem_Ioo] using ht
  exact ((contDiffAt_piLp 2).mp (hu _ hz) i).differentiableAt (by norm_num)

/-- Joint measurability turns the slice-wise weak-gradient identity into the
spacetime identity used by the local energy inequality. -/
theorem PressureWeakSolution.gradient_ae_eq_of_positiveTime_regular
    {n : ℕ} {nse : Problem n} (sol : PressureWeakSolution nse)
    (hu : ∀ z ∈ finiteTimeDomain n sol.T, ContDiffAt ℝ 2 sol.u z)
    (hD : AEStronglyMeasurable sol.Du (volume.restrict (finiteTimeDomain n sol.T))) :
    sol.Du =ᵐ[volume.restrict (finiteTimeDomain n sol.T)]
      spatialVelocityGradient n sol.u := by
  let μ := (volume : Measure ℝ).restrict (Set.Ioo 0 (sol.T : ℝ))
  let e := timeSpaceContinuousLinearEquiv n
  have hm : MeasurePreserving e.symm (μ.prod volume)
      (volume.restrict (finiteTimeDomain n sol.T)) := by
    simpa only [μ, e, finiteTimeDomain, Set.mem_Ioo] using
      Slices.measurePreserving_timeSpaceCons_restrict (n := n) (Set.Ioo 0 (sol.T : ℝ))
  have hG : AEStronglyMeasurable (spatialVelocityGradient n sol.u)
      (volume.restrict (finiteTimeDomain n sol.T)) := by
    have hc : ContinuousOn (spatialVelocityGradient n sol.u) (finiteTimeDomain n sol.T) :=
      fun z hz ↦ (continuousAt_spatialVelocityGradient (hu z hz)).continuousWithinAt
    exact hc.aestronglyMeasurable (isOpen_finiteTimeDomain n sol.T).measurableSet
  have hs : ∀ᵐ t ∂μ,
      (fun x ↦ sol.Du (e.symm (t, x))) =ᵐ[volume]
        fun x ↦ spatialVelocityGradient n sol.u (e.symm (t, x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simpa only [e, timeSpaceContinuousLinearEquiv_symm_apply] using
      sol.gradient_slice_ae_eq_of_positiveTime_regular
        (fun z hz ↦ (hu z hz).of_le (by norm_num)) ht
  have hprod := ae_eq_prod_of_ae_eq_sections
    (hD.comp_measurePreserving hm) (hG.comp_measurePreserving hm) hs
  have hback := MeasurePreserving.symm e.symm.toHomeomorph.toMeasurableEquiv hm
  have h := hback.quasiMeasurePreserving.ae hprod
  filter_upwards [h] with z hz
  change sol.Du (e.symm (e z)) = spatialVelocityGradient n sol.u (e.symm (e z)) at hz
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hz

/-- For a jointly measurable weak gradient, positive-time classical momentum
and the existing global Leray–Hopf bounds suffice for suitability. -/
def PressureRepresentativeLerayHopfSolution.toSuitableOfPositiveTimeRegularMeasurable
    {n : ℕ} {nse : Problem n} (sol : PressureRepresentativeLerayHopfSolution nse)
    (hforce : nse.forcing = 0)
    (hu : ∀ z ∈ finiteTimeDomain n sol.T, ContDiffAt ℝ 2 sol.u z)
    (hp : ∀ z ∈ finiteTimeDomain n sol.T, ContDiffAt ℝ 1 sol.p z)
    (hdiv : ∀ z ∈ finiteTimeDomain n sol.T, DivergenceFreeAt sol.u z)
    (hmom : ∀ z ∈ finiteTimeDomain n sol.T, MomentumEquationAt nse sol.u sol.p z)
    (hD : AEStronglyMeasurable sol.Du (volume.restrict (finiteTimeDomain n sol.T))) :
    SuitableLerayHopfSolution nse := by
  apply sol.toSuitableOfPositiveTimeRegular hforce hu hp hdiv hmom
  have h := sol.toPressureWeakSolution.gradient_ae_eq_of_positiveTime_regular hu hD
  exact ((ae_restrict_iff' (isOpen_finiteTimeDomain n sol.T).measurableSet).mp h).mono
    fun z hz hmem ↦ (hz hmem).symm

end NavierStokes
