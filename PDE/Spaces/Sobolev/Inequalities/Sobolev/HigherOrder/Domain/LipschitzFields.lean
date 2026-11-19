/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.ExponentRestriction
public import PDE.Spaces.Sobolev.Inequalities.Morrey.Endpoint.Embedding
public import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.Holder

/-!
# Lipschitz fields of higher-order Sobolev functions

Every derivative of order at most `k` of a `W^{k+1,∞}` function has a bounded
Lipschitz representative after first-order extension. On the domain closure these
fields agree with the finite-exponent Morrey representatives. This
identification lets the endpoint reuse their classical compatibility relations.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Inequalities

open GraphSpace
open scoped ENNReal

variable {n : ℕ} {Ω : Set (ℝ^n)}
variable [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω]

/-- The first-order bounded Lipschitz estimate and the operational extension norm. -/
def higherLipschitzDomainConstant : ℝ :=
  ((n : ℝ) + 1) * ‖Extension.C1.extensionCLM (n := n) (p := ∞) (Ω := Ω)‖

/-- The Lipschitz domain constant is nonnegative. -/
theorem higherLipschitzDomainConstant_nonneg :
    0 ≤ higherLipschitzDomainConstant (n := n) (Ω := Ω) := by
  unfold higherLipschitzDomainConstant
  positivity

end SobolevSpace.Inequalities

namespace SobolevSpace.GraphSpace

open MeasureTheory HolderSpace Inequalities Set
open scoped ENNReal Sobolev

variable {n m : ℕ} {Ω : Set (ℝ^n)}
variable [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω]

/-- The bounded Lipschitz representative of an extended weak derivative.
Only the first-order slice is extended. -/
def lipschitzDerivativeField (α : List (Fin n)) (hα : α.length + 1 ≤ m)
    (U : W^{m,∞}(Ω)) : C0GammaOn (ℝ^n) 1 :=
  (WkpSpaceOn.exists_holder_one_representative
    (Extension.C1.extensionCLM (derivativeWordCLM (r := 1) α hα U))).choose

/-- The Lipschitz field represents the original derivative almost everywhere on the domain. -/
theorem lipschitzDerivativeField_ae (α : List (Fin n)) (hα : α.length + 1 ≤ m)
    (U : W^{m,∞}(Ω)) :
    (fun x ↦ lipschitzDerivativeField α hα U x) =ᵐ[domainMeasure n Ω]
      (U.val (derivativeWordIndex α hα (baseIndex n 1)) : ℝ^n → ℝ) := by
  have h : (fun x ↦ lipschitzDerivativeField α hα U x) =ᵐ[volume]
      baseRepresentative (Extension.C1.extensionCLM (derivativeWordCLM (r := 1) α hα U)) :=
    (WkpSpaceOn.exists_holder_one_representative
      (Extension.C1.extensionCLM (derivativeWordCLM (r := 1) α hα U))).choose_spec.1
  exact Filter.EventuallyEq.trans (ae_restrict_of_ae h)
    (Extension.C1.extensionCLM_agree_ae (derivativeWordCLM (r := 1) α hα U))

/-- The full norm of every derivative field is bounded independently of its order. -/
theorem norm_lipschitzDerivativeField_le (α : List (Fin n)) (hα : α.length + 1 ≤ m)
    (U : W^{m,∞}(Ω)) :
    ‖lipschitzDerivativeField α hα U‖ ≤
      higherLipschitzDomainConstant (n := n) (Ω := Ω) * ‖U‖ := by
  let E := Extension.C1.extensionCLM (n := n) (p := ∞) (Ω := Ω)
  have h := (WkpSpaceOn.exists_holder_one_representative
    (E (derivativeWordCLM (r := 1) α hα U))).choose_spec.2
  exact h.trans
    ((mul_le_mul_of_nonneg_left
      ((E.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (norm_derivativeWordCLM_apply_le α hα U) (norm_nonneg E)))
      (by positivity : 0 ≤ (n : ℝ) + 1)).trans_eq (mul_assoc _ _ _).symm)

/-- Exponent restriction and extension give the same continuous derivative on the closure.
The finite-exponent representative already carries the classical derivative relations. -/
theorem lipschitzDerivativeField_eqOn_finiteMorrey
    {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (α : List (Fin n)) (hα : α.length + 1 ≤ m) (U : W^{m,∞}(Ω)) :
    EqOn (lipschitzDerivativeField α hα U)
      (finiteMorreyDerivativeRepresentativeOn hp hpq α hα
        (lowerExponentOfFiniteMeasure (show ENNReal.ofReal p ≤ ∞ from le_top) U))
      (closure Ω) := by
  let V := lowerExponentOfFiniteMeasure (show ENNReal.ofReal p ≤ ∞ from le_top) U
  have hV := (finiteMorreyDerivativeRepresentativeOn_ae hp hpq α hα V).trans
    (lowerExponentOfFiniteMeasure_apply_ae le_top U
      (derivativeWordIndex α hα (baseIndex n 1)))
  have hi := Measure.eqOn_open_of_ae_eq
    ((lipschitzDerivativeField_ae α hα U).trans hV.symm)
    Boundary.C1ExtensionAtlas.isOpen
    (lipschitzDerivativeField α hα U).continuous.continuousOn
    (continuous_finiteMorreyDerivativeRepresentativeOn hp hpq α hα V).continuousOn
  exact hi.of_subset_closure
    (lipschitzDerivativeField α hα U).continuous.continuousOn
    (continuous_finiteMorreyDerivativeRepresentativeOn hp hpq α hα V).continuousOn
    subset_closure Subset.rfl

end SobolevSpace.GraphSpace
