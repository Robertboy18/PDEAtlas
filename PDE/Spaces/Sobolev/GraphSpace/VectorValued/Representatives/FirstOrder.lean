/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.VectorValued.ClassicalToWeak
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.FirstOrder

/-!
# First-order classical representatives with Banach values

An interior `C¹` formula defines a Sobolev function when the formula and each
coordinate derivative belong to `Lᵖ`. The classical integration-by-parts theorem
supplies the weak derivative identities, and uniqueness of weak derivatives makes
the resulting Sobolev element independent of the chosen representatives.

No extension through the boundary is required. The domain is any open subset of
Euclidean space and the target is any real Banach space.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- An interior `C¹` formula with `Lᵖ` function and coordinate derivatives has a
unique first-order Sobolev representative, even when the domain is unbounded. -/
theorem existsUnique_firstOrder_of_contDiffOn_memLp
    {f : ℝ^n → F} (hf : ContDiffOn ℝ 1 f Ω)
    (hbase : MemLp f p (domainMeasure n Ω))
    (hpartial : ∀ i : Fin n, MemLp (∂[i] f) p (domainMeasure n Ω)) :
    ∃! U : W^{1,p}(Ω; F),
      (U.val (baseIndex n 1) : ℝ^n → F) =ᵐ[domainMeasure n Ω] f ∧
      ∀ i : Fin n, (U.val (singleDerivIndex n i) : ℝ^n → F)
        =ᵐ[domainMeasure n Ω] ∂[i] f := by
  let d : DerivIndex n 1 → ℝ^n → F := fun a ↦ iteratedPartialDeriv a.toList f
  have hmem (a : DerivIndex n 1) : MemLp (d a) p (domainMeasure n Ω) := by
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simpa only [d, baseIndex_toList, iteratedPartialDeriv] using hbase
    · simpa only [d, singleDerivIndex_toList, iteratedPartialDeriv] using hpartial i
  have hweak (a : DerivIndex n 1) :
      HasWeakDerivativeOn Ω a.toList (d (baseIndex n 1)) (d a) := by
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simpa only [d, baseIndex_toList, iteratedPartialDeriv] using
        hasWeakDerivativeOn_nil
          (hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)
    · simpa only [d, baseIndex_toList, singleDerivIndex_toList, iteratedPartialDeriv] using
        hasWeakDerivativeOn_of_contDiffOn_one hf i
  refine ⟨ofWeakDerivatives d hmem hweak, ⟨?_, ?_⟩, ?_⟩
  · simpa only [d, baseIndex_toList, iteratedPartialDeriv] using
      ofWeakDerivatives_apply_ae d hmem hweak (baseIndex n 1)
  · intro i
    simpa only [d, singleDerivIndex_toList, iteratedPartialDeriv] using
      ofWeakDerivatives_apply_ae d hmem hweak (singleDerivIndex n i)
  · intro V hV
    apply WkpSpaceOn.ext_of_base_ae
    exact hV.1.trans (by
      simpa only [d, baseIndex_toList, iteratedPartialDeriv] using
        (ofWeakDerivatives_apply_ae d hmem hweak (baseIndex n 1)).symm)

/-- For finite exponents, the Sobolev energy equals the `Lp` energies of any
almost-everywhere representatives of its function and first derivatives. -/
theorem norm_rpow_eq_of_firstOrder_ae [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (U : W^{1,p}(Ω; F)) {f : ℝ^n → F} {d : Fin n → ℝ^n → F}
    (hbase : (U.val (baseIndex n 1) : ℝ^n → F) =ᵐ[domainMeasure n Ω] f)
    (hpartial : ∀ i : Fin n,
      (U.val (singleDerivIndex n i) : ℝ^n → F) =ᵐ[domainMeasure n Ω] d i) :
    ‖U‖ ^ p.toReal =
      (eLpNorm f p (domainMeasure n Ω)).toReal ^ p.toReal +
        ∑ i : Fin n, (eLpNorm (d i) p (domainMeasure n Ω)).toReal ^ p.toReal := by
  rw [norm_rpow_eq_base_add_sum_partialDeriv hp]
  congr 1
  · rw [Lp.norm_def, eLpNorm_congr_ae hbase]
  · apply Finset.sum_congr rfl
    intro i _
    rw [norm_partialDeriv_eq_coordinate, Lp.norm_def, eLpNorm_congr_ae (hpartial i)]

end SobolevSpace.VectorValued
