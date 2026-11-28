/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Resolvent identities for partially defined operators

Bounded inverses of two shifts of a partial linear operator satisfy the first resolvent
identity, over any nontrivially normed field, and for real shifts they commute. The inverse
equations are stated on the graph or on the operator domain, while the inverses act as
bounded operators on the ambient space.

The parameters range over every value for which these bounded inverses exist.
These are the identities (12) and (13) of Evans, §7.4.1, Theorem 3(i), stated there for a closed
operator with the verification left to the reader (Problem 12); here the operator need not be
closed or densely defined.

## Main results

* `sub_eq_smul_mul_of_inverse`: `R - S = (w - z) R S`, from a left inverse `R` of `z - A` on
  the domain and a right inverse `S` of `w - A` with values in the domain.
* `resolvent_identity`: `Rλ - Rμ = (μ - λ) Rλ Rμ` for real shifts, the same statement with the
  hypotheses written on the domain.
* `resolvent_commute`: bounded two-sided inverses at any two real parameters commute.

## How it works

If `S y` is in the domain with `A (S y) = w S y - y`, then `z S y - A (S y) = y - (w - z) S y`,
and the left inverse `R` sends this vector back to `S y`. So `S y = R y - (w - z) R (S y)`, the
identity at `y`. `resolvent_identity` rewrites its hypotheses on the domain into this graph form.
`resolvent_commute` uses the identity at `(λ, μ)` and at `(μ, λ)`: both express `Rλ - Rμ`, so
`(μ - λ) Rλ Rμ = (μ - λ) Rμ Rλ`, and the factor cancels when `λ ≠ μ`. For `λ = μ` the identity
gives `Rλ = Rμ`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.4.1, Theorem 3(i), (12)-(13), p. 438.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace LinearPMap

section Field

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {A : E →ₗ.[𝕜] E} {z w : 𝕜} {R S : E →L[𝕜] E}

/-- **The first resolvent identity** `R - S = (w - z) R S`, from a left inverse `R` of `z - A`
on the domain and a right inverse `S` of `w - A` with values in the domain, for a partial
operator on a normed space over any nontrivially normed field. Both hypotheses are stated with
the graph of `A`. -/
theorem sub_eq_smul_mul_of_inverse (hR : ∀ ⦃x y⦄, (x, y) ∈ A.graph → R (z • x - y) = x)
    (hS : ∀ y, (S y, w • S y - y) ∈ A.graph) : R - S = (w - z) • (R * S) := by
  ext y
  have h1 := hR (hS y)
  have e : z • S y - (w • S y - y) = y - (w - z) • S y := by module
  rw [e, _root_.map_sub, _root_.map_smul] at h1
  simp only [_root_.sub_apply, _root_.smul_apply, mul_apply_eq_comp]
  exact sub_eq_iff_eq_add'.mpr (sub_eq_iff_eq_add.mp h1)

end Field

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (A : E →ₗ.[ℝ] E) {lambda mu : ℝ} {Rlambda Rmu : E →L[ℝ] E}

/-- The first resolvent identity for real shifts, from a left inverse at `λ` and a right
inverse at `μ` whose range lies in the operator domain. This is `sub_eq_smul_mul_of_inverse`
with the hypotheses written on the domain. -/
theorem resolvent_identity (hmu_domain : ∀ x : E, Rmu x ∈ A.domain)
    (hlambda : ∀ x : A.domain, Rlambda (lambda • (x : E) - A x) = x)
    (hmu : ∀ x : E, mu • Rmu x - A ⟨Rmu x, hmu_domain x⟩ = x) :
    Rlambda - Rmu = (mu - lambda) • Rlambda.comp Rmu := by
  refine sub_eq_smul_mul_of_inverse (A := A) (fun x y hxy ↦ ?_) fun y ↦ ?_
  · obtain ⟨u, rfl, rfl⟩ := (mem_graph_iff A).mp hxy
    exact hlambda u
  · refine (image_iff (hmu_domain y)).mp ?_
    exact sub_eq_iff_eq_add.mpr (sub_eq_iff_eq_add'.mp (hmu y))

/-- Bounded inverses of any two real shifts commute, including equal parameters. -/
theorem resolvent_commute (hlambda_domain : ∀ x : E, Rlambda x ∈ A.domain)
    (hmu_domain : ∀ x : E, Rmu x ∈ A.domain)
    (hlambda_left : ∀ x : A.domain, Rlambda (lambda • (x : E) - A x) = x)
    (hmu_left : ∀ x : A.domain, Rmu (mu • (x : E) - A x) = x)
    (hlambda_right : ∀ x : E,
      lambda • Rlambda x - A ⟨Rlambda x, hlambda_domain x⟩ = x)
    (hmu_right : ∀ x : E, mu • Rmu x - A ⟨Rmu x, hmu_domain x⟩ = x) :
    Commute Rlambda Rmu := by
  by_cases h : lambda = mu
  · have heq : Rlambda = Rmu := sub_eq_zero.mp (by
      simpa only [h, sub_self, zero_smul] using
        A.resolvent_identity hmu_domain hlambda_left hmu_right)
    rw [heq]
  apply smul_right_injective (E →L[ℝ] E) (sub_ne_zero.mpr (Ne.symm h))
  change (mu - lambda) • Rlambda.comp Rmu = (mu - lambda) • Rmu.comp Rlambda
  rw [← A.resolvent_identity hmu_domain hlambda_left hmu_right]
  have hneg : (mu - lambda) • Rmu.comp Rlambda =
      -((lambda - mu) • Rmu.comp Rlambda) := by module
  rw [hneg, ← A.resolvent_identity hlambda_domain hmu_left hlambda_right, neg_sub]

end LinearPMap
