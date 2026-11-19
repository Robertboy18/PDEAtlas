/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.VectorValued.ClassicalToWeak

/-!
# Classical bilinear products on open domains

Local `C¹` regularity identifies Banach-valued coordinate derivatives with weak derivatives.
The bilinear product formula then holds for smooth representatives of the Sobolev graph,
without assumptions on their behavior outside the domain.
-/

@[expose] public noncomputable section

open PDE (partialDeriv)

open MeasureTheory TopologicalSpace

namespace SobolevSpace.VectorValued

variable {n : ℕ} {Ω : Opens ℝ^n} {F G H : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace F] [CompleteSpace G] in
/-- The weak coordinate derivative of a bilinear product of interior `C¹` functions is
the sum of the two classical Leibniz terms. -/
theorem hasWeakDerivativeOn_bilinear_of_contDiffOn
    (B : F →L[ℝ] G →L[ℝ] H) {f : ℝ^n → F} {g : ℝ^n → G}
    (hf : ContDiffOn ℝ 1 f Ω) (hg : ContDiffOn ℝ 1 g Ω) (i : Fin n) :
    HasWeakDerivativeOn Ω [i] (fun x ↦ B (f x) (g x))
      (fun x ↦ B ((∂[i] f) x) (g x) + B (f x) ((∂[i] g) x)) := by
  have hprod : ContDiffOn ℝ 1 (fun x ↦ B (f x) (g x)) Ω :=
    (B.contDiff.comp_contDiffOn hf).clm_apply hg
  apply (hasWeakDerivativeOn_of_contDiffOn_one hprod i).congr_ae
    Filter.EventuallyEq.rfl
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  have hfx := (hf.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by norm_num)
  have hgx := (hg.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by norm_num)
  simp only [partialDeriv, B.fderiv_of_bilinear hfx hgx,
    add_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply]
  exact add_comm _ _

end SobolevSpace.VectorValued
