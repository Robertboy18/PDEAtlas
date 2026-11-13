/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.WeakDerivatives
public import PDE.Spaces.Sobolev.Approximation.VectorValued.ClassicalDerivatives
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Mollification of Banach-valued weak derivatives

Bochner convolution by a smooth compactly supported scalar kernel commutes with every
whole-space weak coordinate derivative. The proof applies continuous linear functionals,
uses the scalar convolution identity, and recovers equality by the separating dual.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory TopologicalSpace
open scoped Convolution

namespace SobolevSpace.Approximation

variable {n : ℕ} {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Mollification commutes with continuous linear maps of Banach codomains. -/
theorem mollifyVector_map (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (L : F →L[ℝ] G) {f : ℝ^n → F} (hf : LocallyIntegrable f volume) :
    L ∘ mollifyVector μ ε f = mollifyVector μ ε (L ∘ f) := by
  funext x
  have hint := (scaled_hasCompactSupport μ hε).convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (scaled_contDiff μ).continuous hf x
  change Integrable (fun y ↦ scaled μ ε y • f (x - y)) volume at hint
  change L (∫ y, scaled μ ε y • f (x - y)) =
    ∫ y, scaled μ ε y • L (f (x - y))
  rw [← L.integral_comp_comm hint]
  simp only [map_smul]

/-- At real codomain, the Bochner and scalar mollifications are the same convolution. -/
@[simp] theorem mollifyVector_real (μ : Mollifier n) (ε : ℝ) (f : ℝ^n → ℝ) :
    mollifyVector μ ε f = mollify μ ε f :=
  convolution_lsmul_eq_mul _ _

end SobolevSpace.Approximation

namespace SobolevSpace.VectorValued

open Approximation

variable {n : ℕ} {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Convolving a whole-space weak derivative gives the corresponding classical derivative
of the smooth convolution. The statement includes the derivative word of length zero. -/
theorem iteratedPartialDeriv_mollifyVector_eq (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    {α : List (Fin n)} {f g : ℝ^n → F} (hweak : HasWeakDerivativeOn ⊤ α f g) :
    iteratedPartialDeriv α (mollifyVector μ ε f) = mollifyVector μ ε g := by
  have hf : LocallyIntegrable f volume := locallyIntegrableOn_univ.mp hweak.locallyIntegrable_f
  have hg : LocallyIntegrable g volume := locallyIntegrableOn_univ.mp hweak.locallyIntegrable_g
  by_cases hα : α = []
  · subst α
    have heq : f =ᵐ[volume] g := by
      simpa [domainMeasure] using (hasWeakDerivativeOn_nil
        hweak.locallyIntegrable_f).ae_eq hweak
    exact convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) Filter.EventuallyEq.rfl heq
  · funext x
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
    intro L
    have hm := mollifyVector_contDiff_of_pos μ hε f hf
    have hmapf := mollifyVector_map μ hε L hf
    have hmapg := mollifyVector_map μ hε L hg
    have hderiv := L.iteratedPartialDeriv_comp (hm.of_le (by simp)) α le_rfl
    have hs := iteratedPartialDeriv_mollify_eq_mollify_of_hasWeakDerivative_univ μ hε hα
      (locallyIntegrableOn_univ.mp (hweak.map L).locallyIntegrable_f)
      (hasWeakDerivativeOn_real_iff.mp (hweak.map L))
    rw [hmapf, mollifyVector_real] at hderiv
    rw [mollifyVector_real] at hmapg
    exact (congrFun hderiv x).symm.trans ((congrFun hs x).trans (congrFun hmapg x).symm)

/-- Whole-space mollification preserves each Banach-valued weak derivative. -/
theorem HasWeakDerivativeOn.mollifyVector (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    {α : List (Fin n)} {f g : ℝ^n → F} (hweak : HasWeakDerivativeOn ⊤ α f g) :
    HasWeakDerivativeOn ⊤ α (mollifyVector μ ε f) (mollifyVector μ ε g) := by
  have hf : LocallyIntegrable f volume := locallyIntegrableOn_univ.mp hweak.locallyIntegrable_f
  have h := hasWeakDerivativeOn_iteratedPartialDeriv (Ω := ⊤)
    (mollifyVector_contDiff_of_pos μ hε f hf) α
  rwa [iteratedPartialDeriv_mollifyVector_eq μ hε hweak] at h

end SobolevSpace.VectorValued
