/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Laplacian
public import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder
public import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder
public import PDE.FDeriv.Operators

/-!
# The H² Laplacian paired with H¹₀

The first weak derivative identities of the gradient extend to every H¹₀
test. Summing them identifies the Dirichlet pairing with the negative
Laplacian. A smooth compact lifting then gives the ordinary integral identity
used for nonzero Dirichlet data.
-/

@[expose] public noncomputable section

open PDE (laplacian iteratedPartialDeriv)

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal InnerProductSpace Sobolev Laplacian

variable {n : ℕ} {Ω : Set ℝ^n}

/-- Integration by parts for H² data and an arbitrary H¹₀ test
requires no regularity of the domain. -/
theorem sum_inner_gradient_eq_neg_inner_laplacian
    (U : W^{2,2}(Ω)) (t : H¹₀(Ω)) :
    (∑ i, ⟪wkpCoordinateCLM (singleDerivIndex n i)
      (lowerOrderCLM (by norm_num : 1 ≤ 2) U), derivCoordCLM i t⟫_ℝ) =
        -⟪Δ U, baseCoordCLM t⟫_ℝ := by
  rw [laplacian_eq_wkpLaplacianCLM, wkpLaplacianCLM_apply, sum_inner,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hw := U.property.hasWeakDerivativeOn_from_coordinate [i] [i] (by simp)
  simpa only [wkpCoordinateCLM_apply, lowerOrderCLM_apply,
    DerivIndex.castOrder_singleDerivIndex, List.cons_append, List.nil_append,
    derivIndexOfList_singleton, derivIndexOfList_pair, secondDerivIndex_two] using
    weakDerivative_integrationByParts_H10 i _ _ hw t

/-- A smooth compact lifting has its classical Laplacian as the load in the
Dirichlet pairing, even when the test has no compact support inside the domain. -/
theorem sum_inner_smooth_gradient_eq_neg_integral
    (A : ℝ^n → ℝ) (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAc : HasCompactSupport A)
    (t : H¹₀(Ω)) :
    (∑ i, ⟪wkpCoordinateCLM (singleDerivIndex n i)
      (mkWkpSpaceOnOfContDiff (k := 1) (p := 2) (Ω := Ω) A hA hAc),
        derivCoordCLM i t⟫_ℝ) =
      -(∫ x, baseCoordCLM t x * laplacian A x ∂domainMeasure n Ω) := by
  let U : W^{2,2}(Ω) := mkWkpSpaceOnOfContDiff A hA hAc
  have hD (i : Fin n) :
      wkpCoordinateCLM (singleDerivIndex n i) (lowerOrderCLM (by norm_num : 1 ≤ 2) U) =
        wkpCoordinateCLM (singleDerivIndex n i)
          (mkWkpSpaceOnOfContDiff (k := 1) (p := 2) (Ω := Ω) A hA hAc) := by
    apply Lp.ext
    filter_upwards
      [mkWkpSpaceOnOfContDiff_apply_ae (k := 2) (p := 2) (Ω := Ω) A hA hAc
        (firstDerivIndex n 2 (by omega) i),
       mkWkpSpaceOnOfContDiff_apply_ae (k := 1) (p := 2) (Ω := Ω) A hA hAc
        (singleDerivIndex n i)] with x hx hy
    simpa only [wkpCoordinateCLM_apply, lowerOrderCLM_apply,
      DerivIndex.castOrder_singleDerivIndex, firstDerivIndex_toList,
      singleDerivIndex_toList] using hx.trans hy.symm
  have hΔ : ((Δ U : DerivLp n 2 Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] laplacian A := by
    simp only [laplacian_eq_wkpLaplacianCLM]
    filter_upwards [wkpLaplacianCLM_coeFn U,
      ae_all_iff.mpr (fun i : Fin n ↦
        mkWkpSpaceOnOfContDiff_apply_ae (k := 2) (p := 2) (Ω := Ω)
          A hA hAc (pairDerivIndex n i i))] with x hx hd
    rw [hx]
    apply Finset.sum_congr rfl
    intro i _
    have hlist : (pairDerivIndex n i i).toList = [i, i] := by
      apply (List.perm_replicate (n := 2) (a := i)).mp
      simpa using pairDerivIndex_toList_perm i i
    simpa only [hlist, iteratedPartialDeriv] using hd i
  simp_rw [← hD]
  rw [sum_inner_gradient_eq_neg_inner_laplacian U t]
  congr 1
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hΔ] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial]

/-- Subtracting a smooth lifting from a weak harmonic field gives its negative
classical Laplacian as the load for every zero-trace test function. -/
theorem sum_inner_gradient_sub_smooth_eq_integral_laplacian
    {n : ℕ} {Ω : Set ℝ^n} (U : H¹(Ω))
    (A : ℝ^n → ℝ) (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAc : HasCompactSupport A)
    (w : H¹₀(Ω))
    (hw : (w : H¹(Ω)) = U - mkWkpSpaceOnOfContDiff A hA hAc)
    (hweak : ∀ t : H¹₀(Ω),
      (∑ i, ⟪wkpCoordinateCLM (singleDerivIndex n i) U, derivCoordCLM i t⟫_ℝ) = 0)
    (t : H¹₀(Ω)) :
    (∑ i, ⟪derivCoordCLM i w, derivCoordCLM i t⟫_ℝ) =
      ∫ z, baseCoordCLM t z * laplacian A z ∂domainMeasure n Ω := by
  have hD (i : Fin n) :
      derivCoordCLM i w = wkpCoordinateCLM (singleDerivIndex n i) U -
        wkpCoordinateCLM (singleDerivIndex n i)
          (mkWkpSpaceOnOfContDiff (k := 1) (p := 2) (Ω := Ω) A hA hAc) := by
    change wkpCoordinateCLM (singleDerivIndex n i) (w : H¹(Ω)) = _
    rw [hw, map_sub]
  simp only [hD, inner_sub_left, Finset.sum_sub_distrib, hweak t, zero_sub,
    sum_inner_smooth_gradient_eq_neg_integral, neg_neg]

end SobolevSpace.GraphSpace
