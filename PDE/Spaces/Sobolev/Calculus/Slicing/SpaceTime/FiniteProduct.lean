/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.SpaceTime.TimeDerivative
public import PDE.Analysis.Normed.Operator.FiniteProduct
import PDE.Analysis.Evolution.Time.WeakDerivative.FiniteProduct
import PDE.Analysis.MeasureTheory.Lp.FiniteCoordinates.Hilbert
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Finite-vector spacetime Sobolev slices

Raw vector H¹ data on an open slab determine Bochner H¹ spatial
slices and their L² time derivative. The output uses the finite
Hilbert product, with one common exceptional set for all components.
The half-open time measure is interchangeable with the open interval
because Lebesgue measure has no atoms; neither endpoint is used as a trace.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Slices

open MeasureTheory Set PDE.Common GraphSpace
open PDE.Analysis.Evolution
open scoped ENNReal Sobolev

variable {n m : ℕ} {a b : ℝ}

/-- Finite-vector H¹ spacetime data supply their spatial H¹ Bochner
class, time derivative, and all raw coordinate representatives. -/
theorem exists_vector_timeSlices_of_wkpSpaceOn
    (f : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(({p | p 0 ∈ Ioo a b} : Set (ℝ^(n + 1)))))) :
    ∃ F : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2
        (volume.restrict (Ioc a b)),
      ∃ G : Lp (PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ)) 2
          (volume.restrict (Ioc a b)),
        HasWeakTimeDerivativeOn (Ioo a b)
          (fun t ↦ ContinuousLinearMap.piLpMap 2
            (fun _ : Fin m ↦ (wkpBaseCoordinateCLM :
              W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)) (F t)) G ∧
        (∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ p,
          wkpBaseCoordinateCLM (F t p) x =
            wkpBaseCoordinateCLM (f p) (timeSpaceCons t x)) ∧
        (∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ p j,
          wkpCoordinateCLM (singleDerivIndex n j) (F t p) x =
            wkpCoordinateCLM (singleDerivIndex (n + 1) j.succ) (f p)
              (timeSpaceCons t x)) ∧
        (∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ p,
          G t p x = wkpCoordinateCLM (singleDerivIndex (n + 1) 0) (f p)
            (timeSpaceCons t x)) := by
  let : NormedSpace ℝ (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) :=
    PiLp.normedSpace 2 ℝ (fun _ : Fin m ↦ W^{1,2}(ℝ^n))
  let : NormedSpace ℝ (PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ)) :=
    PiLp.normedSpace 2 ℝ (fun _ : Fin m ↦ DerivLp n 2 univ)
  have : IsFiniteMeasure (volume.restrict (Ioo a b)) :=
    isFiniteMeasure_restrict.mpr (by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top)
  rw [← restrict_Ioo_eq_restrict_Ioc]
  have hs (i : Fin m) := exists_timeSlices_of_wkpSpaceOn isOpen_Ioo (f i)
  choose Fi Gi hw hbase hfirst htime using hs
  obtain ⟨F, hF, _hFnorm⟩ := Lp.exists_piLp_L2 Fi
  obtain ⟨G, hG, _hGnorm⟩ := Lp.exists_piLp_L2 Gi
  let P : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)) →L[ℝ]
      PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ) :=
    ContinuousLinearMap.piLpMap 2 (fun _ ↦ wkpBaseCoordinateCLM)
  refine ⟨F, G, ?_, ?_, ?_, ?_⟩
  · apply HasWeakTimeDerivativeOn.of_piLp_coordinates
    · have hP : IntegrableOn (fun t ↦ P (F t)) (Ioo a b) :=
        (P.comp_memLp F).integrable (by norm_num)
      exact hP.locallyIntegrableOn
    · have hGint : IntegrableOn (fun t ↦ G t) (Ioo a b) :=
        (Lp.memLp G).integrable (by norm_num)
      exact hGint.locallyIntegrableOn
    · intro i
      apply (hw i).congr_ae_restrict measurableSet_Ioo
      · filter_upwards [hF] with t ht
        simp only [ContinuousLinearMap.piLpMap_apply, ht]
      · filter_upwards [hG] with t ht
        exact (ht i).symm
  · filter_upwards [hF, ae_all_iff.mpr hbase] with t ht hb
    filter_upwards [ae_all_iff.mpr hb] with x hx
    intro p
    simpa only [ht p] using hx p
  · have hd := ae_all_iff.mpr fun p ↦ ae_all_iff.mpr (hfirst p)
    filter_upwards [hF, hd] with t ht hd
    have hx := ae_all_iff.mpr fun p ↦ ae_all_iff.mpr (hd p)
    filter_upwards [hx] with x hx
    intro p j
    simpa only [ht p] using hx p j
  · filter_upwards [hG, ae_all_iff.mpr htime] with t ht hg
    filter_upwards [ae_all_iff.mpr hg] with x hx
    intro p
    simpa only [ht p] using hx p

end SobolevSpace.Slices
