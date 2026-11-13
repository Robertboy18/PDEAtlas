/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Pullback.Geometry
public import PDE.Spaces.Sobolev.Fractional.Domain.Pullback.Operator
public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.GraphOperator

/-!
# Intrinsic fractional equivalence under a bounded C1 chart

The C1 hypotheses and bounded target provide the numerical bounds in both
directions. The resulting equivalence acts by composition with the chart,
and its inverse acts by composition with the inverse chart. This concerns the
intrinsic domain spaces at finite exponents at least one, for real normed codomains.
No completeness or positive dimension is needed. A chart patch remains a patch,
so extending to the whole halfspace is a separate step.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FractionalSobolev

namespace SobolevSpace.Fractional.GagliardoSpace

variable {n : ℕ} {s : ℝ} {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (hs : 0 ≤ (n : ℝ) / p.toReal + s)
  (hE : ContDiff ℝ 1 (fun x ↦ E x))
  (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
  (hTarget : Bornology.IsBounded E.target)

/-- Intrinsic fractional spaces on the source and target of a bounded C1 chart
are continuously linearly equivalent, by physical composition. -/
def pullbackC1Equiv (hp : p ≠ ∞ := by norm_num) :
    W^{s,p}(E.target; F) ≃L[ℝ] W^{s,p}(E.source; F) :=
  let f := Pullback.exists_pullback_bounds_of_contDiff hE hSymm hTarget
  let b := Pullback.exists_pullback_bounds_of_contDiff (E := E.symm) hSymm hE
    (WeakChangeOfVariables.isBounded_source_of_isBounded_target hSymm.continuous hTarget)
  pullbackEquiv hs hE.continuous.measurable
    f.choose_spec.choose_spec.1 f.choose_spec.choose_spec.2
    hSymm.continuous.measurable b.choose_spec.choose_spec.1 b.choose_spec.choose_spec.2 hp

/-- The C1 equivalence has the expected physical composition formula. -/
theorem toLp_pullbackC1Equiv_apply_ae (u : W^{s,p}(E.target; F))
    (hp : p ≠ ∞ := by norm_num) :
    (toLp n s E.source (pullbackC1Equiv hs hE hSymm hTarget hp u) : ℝ^n → F)
      =ᵐ[volume.restrict E.source] (toLp n s E.target u : ℝ^n → F) ∘ E :=
  toLp_pullbackL_apply_ae hs _ _ _ hp u

/-- The inverse C1 equivalence is physical composition with the inverse chart. -/
theorem toLp_pullbackC1Equiv_symm_apply_ae (u : W^{s,p}(E.source; F))
    (hp : p ≠ ∞ := by norm_num) :
    (toLp n s E.target ((pullbackC1Equiv hs hE hSymm hTarget hp).symm u) : ℝ^n → F)
      =ᵐ[volume.restrict E.target] (toLp n s E.source u : ℝ^n → F) ∘ E.symm := by
  obtain ⟨M, J, _, hJ⟩ := Pullback.exists_pullback_bounds_of_contDiff
    (E := E.symm) hSymm hE
    (WeakChangeOfVariables.isBounded_source_of_isBounded_target hSymm.continuous hTarget)
  have hq : QuasiMeasurePreserving E.symm
      (volume.restrict E.target) (volume.restrict E.source) :=
    ⟨hSymm.continuous.measurable, Measure.absolutelyContinuous_of_le_smul hJ⟩
  have h := toLp_pullbackC1Equiv_apply_ae hs hE hSymm hTarget
    ((pullbackC1Equiv hs hE hSymm hTarget hp).symm u) hp
  simp only [ContinuousLinearEquiv.apply_symm_apply] at h
  filter_upwards [hq.ae h, ae_restrict_mem E.open_target.measurableSet] with y hy hyT
  simpa only [Function.comp_apply, E.right_inv hyT] using hy.symm

/-- The C1 equivalence agrees with ordinary pullback on intrinsic functions. -/
theorem pullbackC1Equiv_ofFunction {f : ℝ^n → F}
    (hf : MemGagliardo n s E.target f (p := p)) (hp : p ≠ ∞ := by norm_num) :
    pullbackC1Equiv hs hE hSymm hTarget hp (ofFunction f hf) =
      ofFunction (f ∘ E) (Pullback.memGagliardo_comp_of_contDiff hs hE hSymm hTarget hf) :=
  pullbackL_ofFunction hs _ _ _ hp hf

end SobolevSpace.Fractional.GagliardoSpace
