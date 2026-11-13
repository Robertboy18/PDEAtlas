/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.Algebra.Module.LinearPMap
public import PDE.Analysis.Operator.Resolvent

/-!
# Resolvents of partially defined operators

The hypotheses for contraction-semigroup generation are expressed on Mathlib's `LinearPMap`.
For every positive `λ`, the map `λI - A` is onto and satisfies
`‖x‖ ≤ λ⁻¹ ‖λx - Ax‖` on its domain. These conditions give a bounded inverse with norm
at most `λ⁻¹`.

This is the resolvent condition (17) of Evans §7.4.2, Theorem 4. Density and closedness are
separate properties of the partial operator.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.4.2, Theorem 4, condition (17), p. 439.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The positive resolvent range and norm conditions for a contraction generator. -/
structure HasContractionResolvent (A : E →ₗ.[ℝ] E) : Prop where
  /-- Each positive shift maps the operator domain onto the ambient space. -/
  surjective : ∀ (lambda : ℝ), 0 < lambda →
    Function.Surjective (lambda • A.domain.subtype - A.toFun)
  /-- The inverse estimate, stated directly on the operator domain. -/
  bound : ∀ (lambda : ℝ), 0 < lambda → ∀ x : A.domain,
    ‖(x : E)‖ ≤ lambda⁻¹ * ‖lambda • (x : E) - A x‖

namespace HasContractionResolvent

variable {A : E →ₗ.[ℝ] E} (hA : HasContractionResolvent A)
  {lambda mu : ℝ}

include hA in
/-- The resolvent estimate makes every positive shift injective. -/
theorem injective (hlambda : 0 < lambda) :
    Function.Injective (lambda • A.domain.subtype - A.toFun) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply Subtype.val_injective
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have h := hA.bound lambda hlambda (x - y)
  have hz : lambda • ((x - y : A.domain) : E) - A (x - y) = 0 := by
    change (lambda • A.domain.subtype - A.toFun) (x - y) = 0
    rw [map_sub, hxy, sub_self]
  simpa only [hz, norm_zero, mul_zero] using h

/-- A positive shift is a linear equivalence from the domain onto the ambient space. -/
def shiftEquiv (hlambda : 0 < lambda) : A.domain ≃ₗ[ℝ] E :=
  LinearEquiv.ofBijective (lambda • A.domain.subtype - A.toFun)
    ⟨hA.injective hlambda, hA.surjective lambda hlambda⟩

/-- The inverse of `λI - A`, with values retained in the operator domain. -/
def resolventToDomain (hlambda : 0 < lambda) : E →L[ℝ] A.domain :=
  (hA.shiftEquiv hlambda).symm.toLinearMap.mkContinuous lambda⁻¹ fun x ↦ by
    have h := hA.bound lambda hlambda ((hA.shiftEquiv hlambda).symm x)
    change ‖(hA.shiftEquiv hlambda).symm x‖ ≤
      lambda⁻¹ * ‖hA.shiftEquiv hlambda ((hA.shiftEquiv hlambda).symm x)‖ at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h

/-- The bounded resolvent acting on the ambient normed space. -/
def resolvent (hlambda : 0 < lambda) : E →L[ℝ] E :=
  A.domain.subtypeL.comp (hA.resolventToDomain hlambda)

/-- The ambient resolvent is the underlying vector of the domain-valued inverse. -/
@[simp]
theorem coe_resolventToDomain (hlambda : 0 < lambda) (x : E) :
    (hA.resolventToDomain hlambda x : E) = hA.resolvent hlambda x :=
  rfl

/-- Applying the shifted operator to its resolvent recovers the datum. -/
theorem shift_resolvent (hlambda : 0 < lambda) (x : E) :
    lambda • hA.resolvent hlambda x - A (hA.resolventToDomain hlambda x) = x :=
  (hA.shiftEquiv hlambda).apply_symm_apply x

/-- The resolvent inverts the shift on the operator domain. -/
theorem resolvent_shift (hlambda : 0 < lambda) (x : A.domain) :
    hA.resolvent hlambda (lambda • (x : E) - A x) = x :=
  congrArg Subtype.val ((hA.shiftEquiv hlambda).symm_apply_apply x)

/-- Every resolvent value belongs to the operator domain. -/
theorem resolvent_mem_domain (hlambda : 0 < lambda) (x : E) :
    hA.resolvent hlambda x ∈ A.domain :=
  (hA.resolventToDomain hlambda x).property

/-- The resolvent satisfies the pointwise estimate inherited from the shifted operator. -/
theorem norm_resolvent_apply_le (hlambda : 0 < lambda) (x : E) :
    ‖hA.resolvent hlambda x‖ ≤ lambda⁻¹ * ‖x‖ := by
  simpa only [coe_resolventToDomain, hA.shift_resolvent hlambda x] using
    hA.bound lambda hlambda (hA.resolventToDomain hlambda x)

/-- The operator-norm estimate `‖R_λ‖ ≤ λ⁻¹` for a positive resolvent. -/
theorem norm_resolvent_le (hlambda : 0 < lambda) :
    ‖hA.resolvent hlambda‖ ≤ lambda⁻¹ :=
  (hA.resolvent hlambda).opNorm_le_bound (inv_nonneg.mpr hlambda.le)
    (hA.norm_resolvent_apply_le hlambda)

/-- The generator value of a resolvent is `λR_λx - x`. -/
theorem apply_resolventToDomain (hlambda : 0 < lambda) (x : E) :
    A (hA.resolventToDomain hlambda x) = lambda • hA.resolvent hlambda x - x := by
  have h := hA.shift_resolvent hlambda x
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp h).symm

/-- On the operator domain, `λR_λx - x = R_λAx`. -/
theorem smul_resolvent_sub (hlambda : 0 < lambda) (x : A.domain) :
    lambda • hA.resolvent hlambda x - (x : E) = hA.resolvent hlambda (A x) := by
  have h := hA.resolvent_shift hlambda x
  rw [map_sub, map_smul] at h
  exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp h).trans (add_comm _ _))

/-- The two positive resolvents satisfy the first resolvent identity. -/
theorem resolvent_identity (hlambda : 0 < lambda) (hmu : 0 < mu) :
    hA.resolvent hlambda - hA.resolvent hmu =
      (mu - lambda) • (hA.resolvent hlambda).comp (hA.resolvent hmu) :=
  A.resolvent_identity (hA.resolvent_mem_domain hmu)
    (hA.resolvent_shift hlambda) (hA.shift_resolvent hmu)

/-- Positive resolvents commute. -/
theorem resolvent_commute (hlambda : 0 < lambda) (hmu : 0 < mu) :
    Commute (hA.resolvent hlambda) (hA.resolvent hmu) :=
  A.resolvent_commute (hA.resolvent_mem_domain hlambda) (hA.resolvent_mem_domain hmu)
    (hA.resolvent_shift hlambda) (hA.resolvent_shift hmu)
    (hA.shift_resolvent hlambda) (hA.shift_resolvent hmu)

end HasContractionResolvent

end PDE.Analysis.Evolution
