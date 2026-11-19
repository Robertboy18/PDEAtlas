/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Representatives.Classical
public import PDE.Spaces.Sobolev.GraphSpace.Operators.FirstOrderEnergy
import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity

/-!
# First-order classical representatives

To put a smooth interior formula in `W^{1,p}(Ω)`, we check its function and
its coordinate derivatives in `Lᵖ`. The resulting Sobolev element is unique:
changing the chosen representatives cannot change its weak derivatives.
The graph norm then reads directly as the sum of these physical energies.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open MeasureTheory
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set ℝ^n}

/-- An interior `C¹` formula with `Lᵖ` function and derivatives has a unique
first-order Sobolev representative. The boundary need not be smooth. -/
theorem existsUnique_firstOrder_of_contDiffOn_memLp (hΩ : IsOpen Ω)
    {f : ℝ^n → ℝ} (hf : ContDiffOn ℝ 1 f Ω)
    (hbase : MemLp f p (domainMeasure n Ω))
    (hpartial : ∀ i : Fin n, MemLp (∂[i] f) p (domainMeasure n Ω)) :
    ∃! U : W^{1,p}(Ω),
      (wkpBaseCoordinateCLM U : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f ∧
      ∀ i : Fin n, (wkpCoordinateCLM (singleDerivIndex n i) U : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] ∂[i] f := by
  have hrows (a : DerivIndex n 1) :
      MemLp (iteratedPartialDeriv a.toList f) p (domainMeasure n Ω) := by
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simpa only [baseIndex_toList, iteratedPartialDeriv] using hbase
    · simpa only [singleDerivIndex_toList, iteratedPartialDeriv] using hpartial i
  obtain ⟨U, hU⟩ := exists_of_contDiffOn_memLp hΩ hf hrows
  refine ⟨U, ⟨?_, ?_⟩, ?_⟩
  · simpa only [wkpBaseCoordinateCLM_apply, baseIndex_toList, iteratedPartialDeriv]
      using hU (baseIndex n 1)
  · intro i
    simpa only [wkpCoordinateCLM_apply, singleDerivIndex_toList, iteratedPartialDeriv]
      using hU (singleDerivIndex n i)
  · intro V hV
    apply wkpBaseCoordinateCLM_injective hΩ
    apply Lp.ext
    exact hV.1.trans (by
      simpa only [wkpBaseCoordinateCLM_apply, baseIndex_toList, iteratedPartialDeriv]
        using (hU (baseIndex n 1)).symm)

/-- The Sobolev norm of a represented function is its function energy plus
the energies of its first weak derivatives. This also covers dimension zero. -/
theorem norm_rpow_eq_of_firstOrder_ae (hp : p ≠ ∞)
    (U : W^{1,p}(Ω)) {f : ℝ^n → ℝ} {d : Fin n → ℝ^n → ℝ}
    (hbase : (wkpBaseCoordinateCLM U : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f)
    (hpartial : ∀ i : Fin n,
      (wkpCoordinateCLM (singleDerivIndex n i) U : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] d i) :
    ‖U‖ ^ p.toReal =
      (eLpNorm f p (domainMeasure n Ω)).toReal ^ p.toReal +
        ∑ i : Fin n, (eLpNorm (d i) p (domainMeasure n Ω)).toReal ^ p.toReal := by
  rw [norm_rpow_eq_base_add_sum_partialDeriv hp]
  congr 1
  · rw [Lp.norm_def, eLpNorm_congr_ae hbase]
  · apply Finset.sum_congr rfl
    intro i _
    rw [norm_partialDeriv_eq_wkpCoordinateCLM, Lp.norm_def,
      eLpNorm_congr_ae (hpartial i)]

end SobolevSpace.GraphSpace
