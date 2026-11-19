/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jacobian.Minors.Divergence
public import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalToWeak

/-!
# Testing classical Jacobian minors

Compactly supported tests turn the local divergence identity into an integral
identity on any open domain. No boundary condition or boundary regularity enters.

`integral_det_jacobianMatrix_submatrix_mul_test` is identity (47) in step 2 of the proof of Evans's
lemma on weak continuity of determinants (§8.2.4(b)), for an `m × m` minor of a C² map in place of
the determinant of a smooth map. Evans obtains (47) from the row expansion (46) of `det Dw` and the
divergence-free rows of `cof Dw` (§8.1.4(b), (20)); the corresponding divergence form of a minor is
`PDE.Analysis.det_jacobianMatrix_submatrix_eq_sum_partialDeriv`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.1.4(b), Lemma (Divergence-free rows), (20), p. 462; and
  §8.2.4(b), proof of the Lemma (Weak continuity of determinants), step 2, (46)-(47), p. 477.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set TopologicalSpace PDE.Analysis
open scoped Distributions

namespace SobolevSpace

variable {m n : ℕ}

/-- For an open `Ω`, `u : ℝⁿ → ℝ^m` of class C² on `Ω`, directions `σ : Fin m → Fin n`, a row
`k` and a test function `φ` with `tsupport φ ⊆ Ω`, the minor `M = det ((Du)_{i, σ j})` satisfies
`∫_Ω M φ dx = -∑_j ∫_Ω u_k (adj M)_{j k} ∂_{σ j} φ dx`, where `adj M` is the adjugate of the
selected matrix. -/
theorem integral_det_jacobianMatrix_submatrix_mul_test
    {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω) {u : ℝ^n → ℝ^m}
    (hu : ContDiffOn ℝ 2 u Ω) (σ : Fin m → Fin n) (k : Fin m)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hφ : tsupport φ.toFun ⊆ Ω) :
    (∫ x, ((jacobianMatrix u x).submatrix id σ).det * φ x ∂domainMeasure n Ω) =
      -∑ j, ∫ x, u x k * ((jacobianMatrix u x).submatrix id σ).adjugate j k *
        (∂[σ j] φ.toFun) x ∂domainMeasure n Ω := by
  have hflux (j : Fin m) (x : ℝ^n) (hx : x ∈ Ω) :
      ContDiffAt ℝ 1
        (fun y ↦ u y k * ((jacobianMatrix u y).submatrix id σ).adjugate j k) x := by
    have hxU := hu.contDiffAt (hΩ.mem_nhds hx)
    exact ((EuclideanSpace.proj k : ℝ^m →L[ℝ] ℝ).contDiff.contDiffAt.comp x
      (hxU.of_le (by norm_num))).mul
        (contDiffAt_adjugate_jacobianMatrix_submatrix 1 hxU σ k j)
  have hweak (j : Fin m) :=
    hasWeakDerivativeOn_of_contDiffAt_one hΩ (hflux j) (σ j)
  calc
    _ = ∫ x, (∑ j, (∂[σ j]
        (fun y ↦ u y k * ((jacobianMatrix u y).submatrix id σ).adjugate j k)) x) *
          φ x ∂domainMeasure n Ω := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      rw [det_jacobianMatrix_submatrix_eq_sum_partialDeriv
        (hu.contDiffAt (hΩ.mem_nhds hx)) σ k]
    _ = ∑ j, ∫ x, (∂[σ j]
        (fun y ↦ u y k * ((jacobianMatrix u y).submatrix id σ).adjugate j k)) x *
          φ x ∂domainMeasure n Ω := by
      simp_rw [Finset.sum_mul]
      exact integral_finsetSum _ fun j _ ↦ (hweak j).integrable_mul_testFunction φ hφ
    _ = _ := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      have h := hweak j φ hφ
      simp only [iteratedPartialDeriv, List.length_cons, List.length_nil,
        Nat.zero_add, pow_one, neg_one_mul, _root_.TestFunction.toFun_eq_coe] at h
      simpa only [neg_neg, _root_.TestFunction.toFun_eq_coe] using
        (congrArg (fun t : ℝ ↦ -t) h).symm

end SobolevSpace
