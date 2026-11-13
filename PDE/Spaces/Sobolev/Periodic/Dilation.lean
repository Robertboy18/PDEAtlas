/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Periodic.EuclideanLift
public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.LocalizedPullback
public import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra

/-!
# Dilation of periodic Sobolev functions

The Euclidean weak chain rule applies on each open cell. Joining its pullbacks
gives the global distributional identity without assuming that a periodic
function is globally square-integrable on Euclidean space.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology

namespace SobolevSpace.Periodic

/-- The weak chain rule on the inverse image of an open periodic cell. -/
theorem hasWeakDerivativeOn_smul_openUnitCell {n : ℕ} (u : h1Space n)
    (c : ℝ) (hc : c ≠ 0) (a : Fin n → ℝ) (i : Fin n) :
    HasWeakDerivativeOn ((fun x : ℝ^n ↦ c • x) ⁻¹' openUnitCell a) [i]
      (fun x ↦ valueCLM n u (toTorus n (c • x)))
      (fun x ↦ c * gradientCLM n u (toTorus n (c • x)) i) := by
  let e : ℝ^n ≃L[ℝ] ℝ^n := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
  let E := (e.symm.toHomeomorph.toOpenPartialHomeomorph.restrOpen
    (openUnitCell a) (isOpen_openUnitCell a)).symm
  have htarget : E.target = openUnitCell a := by
    change univ ∩ openUnitCell a = openUnitCell a
    exact univ_inter _
  have hsource : E.source = (fun x : ℝ^n ↦ c • x) ⁻¹' openUnitCell a := by
    change univ ∩ (fun x : ℝ^n ↦ c • x) ⁻¹' openUnitCell a = _
    exact univ_inter _
  have hV : MemLp (fun x ↦ valueCLM n u (toTorus n x)) 2
      (domainMeasure n E.target) := by
    rw [htarget]
    exact (memLp_comp_toTorus a (valueCLM n u)).mono_measure
      (Measure.restrict_mono_set volume (openUnitCell_subset_unitCell a))
  have hG (j : Fin n) : MemLp (fun x ↦ gradientCLM n u (toTorus n x) j) 2
      (domainMeasure n E.target) := by
    rw [htarget]
    exact ((memLp_comp_toTorus a (gradientCLM n u)).continuousLinearMap_comp
      (EuclideanSpace.proj (𝕜 := ℝ) j)).mono_measure
        (Measure.restrict_mono_set volume (openUnitCell_subset_unitCell a))
  have hw (j : Fin n) : HasWeakDerivativeOn E.target [j]
      (fun x ↦ valueCLM n u (toTorus n x))
      (fun x ↦ gradientCLM n u (toTorus n x) j) := by
    rw [htarget]
    exact (hasWeakDerivativeOn_unitCell u a j).mono
      (isOpen_openUnitCell a).measurableSet (openUnitCell_subset_unitCell a)
  have h := WeakChangeOfVariables.hasWeakDerivativeOn_comp_partialHomeomorph_W1p_of_memLp
    (Approximation.standardMollifier n) (by simp : (2 : ℝ≥0∞) ≠ ∞)
    (E := E) e.contDiff e.symm.contDiff hV hG hw i
  have hder (x : ℝ^n) : fderiv ℝ (fun y ↦ E y) x =
      c • ContinuousLinearMap.id ℝ (ℝ^n) :=
    ((hasFDerivAt_id x).const_smul c).fderiv
  rw [hsource] at h
  simp only [hder, smul_apply, ContinuousLinearMap.id_apply,
    PiLp.smul_apply, PiLp.single_apply, smul_eq_mul] at h
  simpa [E, e, Finset.mul_sum, mul_comm] using h

/-- A nonzero dilation multiplies the periodic weak gradient by its dilation factor. -/
theorem hasWeakDerivativeOn_toTorus_smul {n : ℕ} (u : h1Space n)
    (c : ℝ) (hc : c ≠ 0) (i : Fin n) :
    HasWeakDerivativeOn univ [i]
      (fun x ↦ valueCLM n u (toTorus n (c • x)))
      (fun x ↦ c * gradientCLM n u (toTorus n (c • x)) i) := by
  refine hasWeakDerivativeOn_single_of_open_cover
    (fun a ↦ (fun x : ℝ^n ↦ c • x) ⁻¹' openUnitCell a)
    (fun a ↦ (isOpen_openUnitCell a).preimage (continuous_const_smul c)) ?_ i ?_
  · rw [← preimage_iUnion, iUnion_openUnitCell, preimage_univ]
  · exact fun a ↦ hasWeakDerivativeOn_smul_openUnitCell u c hc a i

/-- The scaled potential `ε u(x/ε)` has gradient `∇u(x/ε)`. -/
theorem hasWeakDerivativeOn_scaledPotential {n : ℕ} (u : h1Space n)
    (ε : ℝ) (hε : ε ≠ 0) (i : Fin n) :
    HasWeakDerivativeOn univ [i]
      (fun x ↦ ε * valueCLM n u (toTorus n (ε⁻¹ • x)))
      (fun x ↦ gradientCLM n u (toTorus n (ε⁻¹ • x)) i) := by
  have h := hasWeakDerivativeOn_smul ε
    (hasWeakDerivativeOn_toTorus_smul u ε⁻¹ (inv_ne_zero hε) i)
  change HasWeakDerivativeOn univ [i]
    (fun x ↦ ε * valueCLM n u (toTorus n (ε⁻¹ • x)))
    (fun x ↦ ε * (ε⁻¹ * gradientCLM n u (toTorus n (ε⁻¹ • x)) i)) at h
  simpa only [← mul_assoc, mul_inv_cancel₀ hε, one_mul] using h

end SobolevSpace.Periodic
