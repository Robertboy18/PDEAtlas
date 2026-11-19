/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.Resolvent
public import PDE.Analysis.Operator.Resolvent.Inverse

/-!
# The real resolvent set of a closed partial operator

Following the definitions in Evans, §7.4.1, a real parameter `λ` belongs to the resolvent set
when `λI - A` is bijective on the entire operator domain. For closed operators on Banach spaces
the inverse is bounded, by the closed graph theorem (`boundedInverse`, built on Mathlib's
`ContinuousLinearMap.ofIsClosedGraph`). This convention is used with an explicit closedness
hypothesis when constructing the inverse.

The first resolvent identity and commutation (Evans, §7.4.1, Theorem 3(i)) hold for every pair in
this set, including equal, zero, and negative parameters whenever they belong to the set.

## Main results

* `realResolventSet`: the real `λ` for which `λI - A` is bijective on `A.domain`.
* `realResolvent`: the bounded inverse of `λI - A` for a closed operator on a Banach space.
* `mem_realResolventSet_iff_exists_inverse`: for a closed operator, membership is equivalent to a
  bounded two-sided inverse with values in the domain.
* `realResolvent_identity`, `realResolvent_commute`: the identities of Theorem 3(i) on the whole
  set.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.4.1, Definitions (i) and (ii) of the resolvent set and
  the resolvent operator, p. 437, and Theorem 3(i), (12)-(13), p. 438.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : E →ₗ.[ℝ] E)

/-- The shift `λI - A` on exactly the domain of the partial operator. -/
def resolventShift (lambda : ℝ) : E →ₗ.[ℝ] E where
  domain := A.domain
  toFun := lambda • A.domain.subtype - A.toFun

/-- Shifting an operator preserves its entire domain. -/
@[simp]
theorem resolventShift_domain (lambda : ℝ) :
    (A.resolventShift lambda).domain = A.domain :=
  rfl

/-- The shifted operator acts by `λx - Ax` on its domain. -/
@[simp]
theorem resolventShift_apply (lambda : ℝ) (x : A.domain) :
    A.resolventShift lambda x = lambda • (x : E) - A x :=
  rfl

/-- The shifted graph is obtained by subtracting its second coordinate from `λx`. -/
theorem mem_graph_resolventShift_iff (lambda : ℝ) (x y : E) :
    (x, y) ∈ (A.resolventShift lambda).graph ↔
      (x, lambda • x - y) ∈ A.graph := by
  rw [LinearPMap.mem_graph_iff, LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨u, rfl, hu⟩
    refine ⟨u, rfl, ?_⟩
    change lambda • (u : E) - A u = y at hu
    rw [← hu, sub_sub_cancel]
  · rintro ⟨u, rfl, hu⟩
    refine ⟨u, rfl, ?_⟩
    change lambda • (u : E) - A u = y
    rw [hu, sub_sub_cancel]

/-- Every real shift of a closed operator is closed. -/
theorem isClosed_resolventShift (hclosed : A.IsClosed) (lambda : ℝ) :
    (A.resolventShift lambda).IsClosed := by
  change _root_.IsClosed ((A.resolventShift lambda).graph : Set (E × E))
  have h := hclosed.preimage
    (continuous_fst.prodMk ((continuous_fst.const_smul lambda).sub continuous_snd))
  convert h using 1
  ext p
  exact A.mem_graph_resolventShift_iff lambda p.1 p.2

/-- Real parameters whose shifts are bijective on the operator domain.
For closed operators on Banach spaces this is equivalent to having a bounded inverse. -/
def realResolventSet : Set ℝ :=
  {lambda | Function.Bijective (A.resolventShift lambda).toFun}

/-- Resolvent membership is bijectivity of the native shift on the original domain. -/
theorem mem_realResolventSet_iff (lambda : ℝ) :
    lambda ∈ A.realResolventSet ↔
      Function.Bijective (lambda • A.domain.subtype - A.toFun) :=
  Iff.rfl

/-- A bounded two-sided inverse on the operator domain gives resolvent membership. -/
theorem mem_realResolventSet_of_inverse {lambda : ℝ} (R : E →L[ℝ] E)
    (hR_domain : ∀ x : E, R x ∈ A.domain)
    (hleft : ∀ x : A.domain, R (lambda • (x : E) - A x) = x)
    (hright : ∀ x : E, lambda • R x - A ⟨R x, hR_domain x⟩ = x) :
    lambda ∈ A.realResolventSet := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    calc
      (x : E) = R (lambda • (x : E) - A x) := (hleft x).symm
      _ = R (lambda • (y : E) - A y) := congrArg R hxy
      _ = (y : E) := hleft y
  · intro x
    exact ⟨⟨R x, hR_domain x⟩, hright x⟩

variable [CompleteSpace E]

/-- The bounded resolvent constructed from closedness and real resolvent-set membership. -/
def realResolvent (hclosed : A.IsClosed) {lambda : ℝ}
    (hlambda : lambda ∈ A.realResolventSet) : E →L[ℝ] E :=
  (A.resolventShift lambda).boundedInverse (A.isClosed_resolventShift hclosed lambda) hlambda

/-- The real resolvent takes arbitrary ambient data into the original operator domain. -/
theorem realResolvent_mem_domain (hclosed : A.IsClosed) {lambda : ℝ}
    (hlambda : lambda ∈ A.realResolventSet) (x : E) :
    A.realResolvent hclosed hlambda x ∈ A.domain :=
  (A.resolventShift lambda).boundedInverse_mem_domain
    (A.isClosed_resolventShift hclosed lambda) hlambda x

/-- The real resolvent inverts the shift on every vector in the operator domain. -/
@[simp]
theorem realResolvent_shift (hclosed : A.IsClosed) {lambda : ℝ}
    (hlambda : lambda ∈ A.realResolventSet) (x : A.domain) :
    A.realResolvent hclosed hlambda (lambda • (x : E) - A x) = x :=
  (A.resolventShift lambda).boundedInverse_apply
    (A.isClosed_resolventShift hclosed lambda) hlambda x

/-- The shift inverts the real resolvent on all ambient data. -/
theorem shift_realResolvent (hclosed : A.IsClosed) {lambda : ℝ}
    (hlambda : lambda ∈ A.realResolventSet) (x : E) :
    lambda • A.realResolvent hclosed hlambda x -
      A ⟨A.realResolvent hclosed hlambda x, A.realResolvent_mem_domain hclosed hlambda x⟩ = x :=
  (A.resolventShift lambda).apply_boundedInverse
    (A.isClosed_resolventShift hclosed lambda) hlambda x

/-- Any bounded domain-valued right inverse is the constructed real resolvent. -/
theorem eq_realResolvent (hclosed : A.IsClosed) {lambda : ℝ}
    (hlambda : lambda ∈ A.realResolventSet) (R : E →L[ℝ] E)
    (hR_domain : ∀ x : E, R x ∈ A.domain)
    (hR : ∀ x : E, lambda • R x - A ⟨R x, hR_domain x⟩ = x) :
    R = A.realResolvent hclosed hlambda :=
  (A.resolventShift lambda).eq_boundedInverse
    (A.isClosed_resolventShift hclosed lambda) hlambda R hR_domain hR

/-- For a closed operator, bijective real shifts have exactly the bounded inverse contract. -/
theorem mem_realResolventSet_iff_exists_inverse (hclosed : A.IsClosed) (lambda : ℝ) :
    lambda ∈ A.realResolventSet ↔
      ∃ (R : E →L[ℝ] E) (hR_domain : ∀ x : E, R x ∈ A.domain),
        (∀ x : A.domain, R (lambda • (x : E) - A x) = x) ∧
        ∀ x : E, lambda • R x - A ⟨R x, hR_domain x⟩ = x := by
  constructor
  · intro hlambda
    exact ⟨A.realResolvent hclosed hlambda, A.realResolvent_mem_domain hclosed hlambda,
      A.realResolvent_shift hclosed hlambda, A.shift_realResolvent hclosed hlambda⟩
  · rintro ⟨R, hR_domain, hleft, hright⟩
    exact A.mem_realResolventSet_of_inverse R hR_domain hleft hright

/-- The first resolvent identity for every pair in the real resolvent set. -/
theorem realResolvent_identity (hclosed : A.IsClosed) {lambda mu : ℝ}
    (hlambda : lambda ∈ A.realResolventSet) (hmu : mu ∈ A.realResolventSet) :
    A.realResolvent hclosed hlambda - A.realResolvent hclosed hmu =
      (mu - lambda) •
        (A.realResolvent hclosed hlambda).comp (A.realResolvent hclosed hmu) :=
  A.resolvent_identity (A.realResolvent_mem_domain hclosed hmu)
    (A.realResolvent_shift hclosed hlambda) (A.shift_realResolvent hclosed hmu)

/-- Resolvents at arbitrary real resolvent parameters commute, including equal parameters. -/
theorem realResolvent_commute (hclosed : A.IsClosed) {lambda mu : ℝ}
    (hlambda : lambda ∈ A.realResolventSet) (hmu : mu ∈ A.realResolventSet) :
    Commute (A.realResolvent hclosed hlambda) (A.realResolvent hclosed hmu) :=
  A.resolvent_commute (A.realResolvent_mem_domain hclosed hlambda)
    (A.realResolvent_mem_domain hclosed hmu) (A.realResolvent_shift hclosed hlambda)
    (A.realResolvent_shift hclosed hmu) (A.shift_realResolvent hclosed hlambda)
    (A.shift_realResolvent hclosed hmu)

end LinearPMap
