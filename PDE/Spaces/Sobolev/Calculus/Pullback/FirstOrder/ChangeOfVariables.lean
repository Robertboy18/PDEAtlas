/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalToWeak
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# First-order weak derivatives and change of variables

Three classical ingredients for first-order Sobolev pullbacks:

* a `C¹` scalar function has its classical partial derivatives as weak
  derivatives on every set;
* composition of `C¹` maps satisfies the corresponding weak chain rule;
* integration over the source and target of an open partial homeomorphism is
  related by the absolute Jacobian determinant; this is Mathlib's
  `MeasureTheory.integral_target_eq_integral_abs_det_fderiv_smul`, restated for scalar
  products.

These are the smooth ingredients of the change of coordinates that straightens the boundary in
the proof of Evans §5.4, Theorem 1 (step 5). The passage to Sobolev functions is in
`Pullback.FirstOrder.FiniteExponent`, which mollifies and takes limits with
`hasWeakDerivativeOn_of_tendsto_eLpNorm` from `Pullback.FirstOrder.Closure`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1, pp. 268-271, whose proof straightens the
  boundary near each boundary point with the map `Φ` of Appendix C.1 (step 5, p. 270).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open scoped Topology

namespace WeakChangeOfVariables

variable {n : ℕ}

variable {Ω : Set (ℝ^n)}

/-- A `C¹` scalar function has its classical first partial derivative as a
weak derivative on any domain. -/
theorem hasWeakDerivativeOn_of_contDiff_one {i : Fin n} {f : ℝ^n → ℝ}
    (hf : ContDiff ℝ 1 f) :
    HasWeakDerivativeOn (n := n) Ω [i] f (fun x ↦ (∂[i] f) x) := by
  have h := hasWeakDerivativeOn_of_contDiffAt_one (Ω := univ) isOpen_univ
    (fun x _ ↦ hf.contDiffAt) i
  refine ⟨h.locallyIntegrable_f.mono_set (subset_univ Ω),
    h.locallyIntegrable_g.mono_set (subset_univ Ω), fun φ hφΩ ↦ ?_⟩
  have hsupp (g : ℝ^n → ℝ) (hg : tsupport g ⊆ tsupport φ.toFun) (u : ℝ^n → ℝ) :
      ∫ x, u x * g x ∂ domainMeasure n Ω = ∫ x, u x * g x ∂ domainMeasure n univ := by
    rw [domainMeasure, domainMeasure, Measure.restrict_univ]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_
    by_contra hux
    exact hx (hφΩ (hg (subset_tsupport _ (Function.support_mul_subset_right u g hux))))
  have hderiv : tsupport (iteratedPartialDeriv (n := n) [i] φ.toFun) ⊆ tsupport φ.toFun :=
    tsupport_iteratedPartialDeriv_subset_tsupport [i] φ.toFun
  rw [hsupp _ hderiv f, hsupp _ subset_rfl (fun x ↦ (∂[i] f) x)]
  exact h.integral_identity φ (subset_univ _)

/-!
## Weak chain rule for `C¹` functions

The classical chain rule, stated as a weak derivative identity. Composition of Sobolev
functions with a `C¹` diffeomorphism needs approximation and density; see `FiniteExponent`.
-/

private theorem partialDeriv_comp_apply {u : ℝ^n → ℝ} {Φ : ℝ^n → ℝ^n} (hu : ContDiff ℝ 1 u)
    (hΦ : ContDiff ℝ 1 Φ) (i : Fin n) (x : ℝ^n) :
    (∂[i] (fun y ↦ u (Φ y))) x =
      (fderiv ℝ u (Φ x)) ((∂[i] Φ) x) := by
  have hu' : DifferentiableAt ℝ u (Φ x) :=
    (hu.differentiable (by simp)).differentiableAt
  have hΦ' : DifferentiableAt ℝ Φ x :=
    (hΦ.differentiable (by simp)).differentiableAt
  have hcomp :=
    congrArg (fun L : (ℝ^n) →L[ℝ] ℝ ↦ L (EuclideanSpace.single i (1 : ℝ)))
      (fderiv_comp x hu' hΦ')
  change (fderiv ℝ (fun y ↦ u (Φ y)) x) (EuclideanSpace.single i (1 : ℝ)) =
    _ at hcomp
  simpa [partialDeriv, LinearMap.comp_apply] using hcomp

/-- The classical chain rule for two `C¹` maps gives the corresponding first
weak derivative of their composition on any domain. -/
theorem hasWeakDerivativeOn_comp_of_contDiff_one {i : Fin n} {u : ℝ^n → ℝ} {Φ : ℝ^n → ℝ^n}
    (hu : ContDiff ℝ 1 u) (hΦ : ContDiff ℝ 1 Φ) :
    HasWeakDerivativeOn (n := n) Ω [i] (fun x ↦ u (Φ x))
      (fun x ↦ (fderiv ℝ u (Φ x)) ((∂[i] Φ) x)) := by
  have hbase :
      HasWeakDerivativeOn (n := n) Ω [i] (fun x ↦ u (Φ x))
        (fun x ↦ (∂[i] (fun y ↦ u (Φ y))) x) :=
    hasWeakDerivativeOn_of_contDiff_one (n := n) (Ω := Ω) (i := i) (hu.comp hΦ)
  simpa [partialDeriv_comp_apply (n := n) (hu := hu) (hΦ := hΦ)] using hbase

/-!
## Change of variables (Jacobian)

These identities transport `L^p` bounds and weak-derivative identities across boundary charts, as
in step 5 of the proof of Evans §5.4, Theorem 1.
-/

section Jacobian

variable {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
variable {E' : ℝ^n → (ℝ^n →L[ℝ] ℝ^n)}

/-- Change of variables from the source of an open partial homeomorphism to
its target, written with scalar multiplication by the absolute Jacobian
determinant. -/
theorem integral_target_eq_integral_abs_det_fderiv_mul
    (hE' : ∀ x ∈ E.source, HasFDerivAt E (E' x) x) (g : ℝ^n → ℝ) :
    (∫ x in E.target, g x ∂ (MeasureTheory.volume : Measure (ℝ^n))) =
      ∫ x in E.source, |(E' x).det| * g (E x) ∂ (MeasureTheory.volume : Measure (ℝ^n)) := by
  simpa [smul_eq_mul] using
    (MeasureTheory.integral_target_eq_integral_abs_det_fderiv_smul
      (μ := (MeasureTheory.volume : Measure (ℝ^n))) (f := E) (f' := E') hE' g)

/-- Change of variables from the target of an open partial homeomorphism back
to its source, expressed using the derivative of the inverse map. -/
theorem integral_source_eq_integral_abs_det_fderiv_mul
    (hE' : ∀ x ∈ E.target, HasFDerivAt E.symm (E' x) x) (g : ℝ^n → ℝ) :
    (∫ x in E.source, g x ∂ (MeasureTheory.volume : Measure (ℝ^n))) =
      ∫ x in E.target, |(E' x).det| * g (E.symm x) ∂ (MeasureTheory.volume : Measure (ℝ^n)) := by
  simpa using
    (integral_target_eq_integral_abs_det_fderiv_mul (n := n) (E := E.symm) (E' := E') hE' g)

end Jacobian

end WeakChangeOfVariables

end SobolevSpace
