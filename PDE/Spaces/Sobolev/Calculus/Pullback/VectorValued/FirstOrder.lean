/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.GraphOperator
public import PDE.Spaces.Sobolev.Foundations.VectorValued.Duality
public import PDE.Spaces.Sobolev.Calculus.Pullback.VectorValued.Lp

/-!
# The weak chain rule for Banach-valued chart pullback

On a bounded chart, composing with a `C¹` partial homeomorphism preserves local
Bochner integrability of a function and its candidate first derivatives.
Continuous linear functionals then reduce the weak chain rule to its scalar
counterpart. The codomain may be any real Banach space, at every exponent
`1 ≤ p ≤ ∞`.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.WeakChangeOfVariables

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {E : OpenPartialHomeomorph ℝ^n ℝ^n}

omit [Fact (1 ≤ p)] [CompleteSpace F] in
private theorem memLp_chainRow
    (hE : ContDiff ℝ 1 E) (hSymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target)
    (du : Fin n → ℝ^n → F)
    (hducomp : ∀ j, MemLp (fun x ↦ du j (E x)) p (domainMeasure n E.source))
    (i : Fin n) :
    MemLp (fun x ↦ ∑ j : Fin n,
      (∂[i] (E : ℝ^n → ℝ^n)) x j • du j (E x))
      p (domainMeasure n E.source) := by
  apply memLp_finsetSum
  intro j _
  exact (SobolevSpace.WeakChangeOfVariables.memLp_chartDerivative
    hE hSymm hTarget i j).smul (r := p) (hducomp j)

private theorem scalarized_chain
    (hE : ContDiff ℝ 1 E) (hSymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target)
    {u : ℝ^n → F} {du : Fin n → ℝ^n → F}
    (hu : MemLp u p (domainMeasure n E.target))
    (hdu : ∀ j, MemLp (du j) p (domainMeasure n E.target))
    (hweak : ∀ j, HasWeakDerivativeOn ⟨E.target, E.open_target⟩ [j] u (du j))
    (i : Fin n) (L : F →L[ℝ] ℝ) :
    SobolevSpace.HasWeakDerivativeOn E.source [i]
      (L ∘ fun x ↦ u (E x))
      (L ∘ fun x ↦ ∑ j : Fin n,
        (∂[i] (E : ℝ^n → ℝ^n)) x j • du j (E x)) := by
  have hscalar (j : Fin n) : SobolevSpace.HasWeakDerivativeOn E.target [j]
      (fun x ↦ L (u x)) (fun x ↦ L (du j x)) :=
    hasWeakDerivativeOn_real_iff.mp ((hweak j).map L)
  have hs :=
    SobolevSpace.WeakChangeOfVariables.hasWeakDerivativeOn_comp_partialHomeomorph_W1_of_memLp
    (Approximation.standardMollifier n) hE hSymm hTarget.measure_lt_top.ne
    (L.comp_memLp' hu) (fun j ↦ L.comp_memLp' (hdu j)) hscalar i
  have hrow : (L ∘ fun x ↦ ∑ j : Fin n,
      (∂[i] (E : ℝ^n → ℝ^n)) x j • du j (E x)) =
      (fun x ↦ ∑ j : Fin n,
        L (du j (E x)) * (∂[i] (E : ℝ^n → ℝ^n)) x j) := by
    funext x
    simp only [Function.comp_apply, map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  rw [hrow]
  exact hs

/-- A `C¹` chart with a `C¹` inverse transports Banach-valued weak first derivatives.
The derivative is the finite sum of chart coefficients acting on the original
weak derivatives. All integrability hypotheses concern the original target. -/
theorem hasWeakDerivativeOn_comp_partialHomeomorph
    (hE : ContDiff ℝ 1 E) (hSymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target)
    {u : ℝ^n → F} {du : Fin n → ℝ^n → F}
    (hu : MemLp u p (domainMeasure n E.target))
    (hdu : ∀ j, MemLp (du j) p (domainMeasure n E.target))
    (hweak : ∀ j, HasWeakDerivativeOn ⟨E.target, E.open_target⟩ [j] u (du j))
    (i : Fin n) :
    HasWeakDerivativeOn ⟨E.source, E.open_source⟩ [i] (fun x ↦ u (E x))
      (fun x ↦ ∑ j : Fin n,
        (∂[i] (E : ℝ^n → ℝ^n)) x j • du j (E x)) := by
  have hucomp : MemLp (fun x ↦ u (E x)) p (domainMeasure n E.source) :=
    SobolevSpace.WeakChangeOfVariables.memLp_comp_partialHomeomorph_on_bounded_chart
      hE hSymm hTarget hu
  have hducomp (j : Fin n) :
      MemLp (fun x ↦ du j (E x)) p (domainMeasure n E.source) :=
    SobolevSpace.WeakChangeOfVariables.memLp_comp_partialHomeomorph_on_bounded_chart
      hE hSymm hTarget (hdu j)
  have hrow := memLp_chainRow hE hSymm hTarget du hducomp i
  have huLoc : LocallyIntegrableOn (fun x ↦ u (E x)) E.source volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      (hucomp.locallyIntegrable (show 1 ≤ p from Fact.out))
  have hrowLoc : LocallyIntegrableOn (fun x ↦ ∑ j : Fin n,
      (∂[i] (E : ℝ^n → ℝ^n)) x j • du j (E x)) E.source volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      (hrow.locallyIntegrable (show 1 ≤ p from Fact.out))
  apply (hasWeakDerivativeOn_iff_forall_dual
    (Ω := ⟨E.source, E.open_source⟩) (α := [i]) huLoc hrowLoc).mpr
  exact scalarized_chain hE hSymm hTarget hu hdu hweak i

end SobolevSpace.VectorValued.WeakChangeOfVariables
