/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.VectorValued.Mollification.WeakDerivatives

/-!
# Interior mollification of Banach-valued weak derivatives

Inside an open set, mollification of a weak derivative agrees with the classical derivative
of the mollification whenever the translated kernel support stays in the set. Both functions
are extended by zero before convolution. Their local Bochner integrability is assumed
explicitly; local integrability on the open set alone need not control its boundary.

Continuous linear functionals reduce the identity to the scalar interior theorem. The empty
derivative word follows from uniqueness, so the result also applies in dimension zero.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory TopologicalSpace

namespace SobolevSpace.VectorValued

open Approximation

variable {n : ℕ} {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Interior mollification commutes with every Banach-valued weak derivative, including the
empty derivative word, when the zero extensions are locally Bochner integrable. -/
theorem iteratedPartialDeriv_mollifyVector_indicator_eq
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    {R : ℝ} (hR : tsupport μ.ρ ⊆ Metric.closedBall (0 : ℝ^n) R)
    {Ω : Opens ℝ^n} {α : List (Fin n)} {f g : ℝ^n → F}
    (hf : LocallyIntegrable ((Ω : Set ℝ^n).indicator f) volume)
    (hg : LocallyIntegrable ((Ω : Set ℝ^n).indicator g) volume)
    (hweak : HasWeakDerivativeOn Ω α f g)
    (x : ℝ^n) (hx : Metric.closedBall x (ε * R) ⊆ Ω) :
    iteratedPartialDeriv α (mollifyVector μ ε ((Ω : Set ℝ^n).indicator f)) x =
      mollifyVector μ ε ((Ω : Set ℝ^n).indicator g) x := by
  by_cases hα : α = []
  · subst α
    have heq : f =ᵐ[volume.restrict (Ω : Set ℝ^n)] g :=
      (hasWeakDerivativeOn_nil hweak.locallyIntegrable_f).ae_eq hweak
    have hzero := (ae_eq_restrict_iff_indicator_ae_eq Ω.isOpen.measurableSet).mp heq
    exact congrFun
      (convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) Filter.EventuallyEq.rfl hzero) x
  · apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
    intro L
    have hm := mollifyVector_contDiff_of_pos μ hε _ hf
    have hmapf := mollifyVector_map μ hε L hf
    have hmapg := mollifyVector_map μ hε L hg
    have hderiv := L.iteratedPartialDeriv_comp (hm.of_le (by simp)) α le_rfl
    have hLf : LocallyIntegrable ((Ω : Set ℝ^n).indicator (L ∘ f)) volume := by
      simpa only [Set.indicator_comp_of_zero L.map_zero] using
        (locallyIntegrableOn_univ.mp
          (L.locallyIntegrableOn_comp (locallyIntegrableOn_univ.mpr hf)))
    have hs := iteratedPartialDeriv_mollify_indicator_eq_mollify_indicator_of_hasWeakDerivativeOn
      μ hε hR hα hLf (hasWeakDerivativeOn_real_iff.mp (hweak.map L)) x hx
    rw [hmapf, ← Set.indicator_comp_of_zero L.map_zero, mollifyVector_real] at hderiv
    rw [← Set.indicator_comp_of_zero L.map_zero, mollifyVector_real] at hmapg
    exact (congrFun hderiv x).symm.trans (hs.trans (congrFun hmapg x).symm)

end SobolevSpace.VectorValued
