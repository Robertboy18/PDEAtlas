/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Resolvent identities for partially defined operators

Bounded inverses of two real shifts of a partial linear operator satisfy the first
resolvent identity and commute. The inverse equations are stated on the operator
domain, while the inverses act as bounded operators on the ambient space.

The parameters range over every real value for which these bounded inverses exist.
These are the identities (12) and (13) of Evans, §7.4.1, Theorem 3(i), stated there for a closed
operator with the verification left to the reader (Problem 12); here the operator need not be
closed or densely defined.

## Main results

* `resolvent_identity`: `Rλ - Rμ = (μ - λ) Rλ Rμ`, from a left inverse at `λ` and a right
  inverse at `μ`.
* `resolvent_commute`: bounded two-sided inverses at any two real parameters commute.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.4.1, Theorem 3(i), (12)-(13), p. 438.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (A : E →ₗ.[ℝ] E) {lambda mu : ℝ} {Rlambda Rmu : E →L[ℝ] E}

/-- The first resolvent identity follows from a left inverse at `λ` and a right
inverse at `μ`, whose range lies in the operator domain. -/
theorem resolvent_identity (hmu_domain : ∀ x : E, Rmu x ∈ A.domain)
    (hlambda : ∀ x : A.domain, Rlambda (lambda • (x : E) - A x) = x)
    (hmu : ∀ x : E, mu • Rmu x - A ⟨Rmu x, hmu_domain x⟩ = x) :
    Rlambda - Rmu = (mu - lambda) • Rlambda.comp Rmu := by
  ext x
  have h := hlambda ⟨Rmu x, hmu_domain x⟩
  have hA : A ⟨Rmu x, hmu_domain x⟩ = mu • Rmu x - x := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp (hmu x)).symm
  change Rlambda (lambda • Rmu x - A ⟨Rmu x, hmu_domain x⟩) = Rmu x at h
  rw [hA] at h
  have he : lambda • Rmu x - (mu • Rmu x - x) =
      x - (mu - lambda) • Rmu x := by module
  rw [he, Rlambda.map_sub, Rlambda.map_smul] at h
  change Rlambda x - Rmu x = (mu - lambda) • Rlambda (Rmu x)
  exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp h).trans (add_comm _ _))

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
