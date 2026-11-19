/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.DirichletEnergy.FiniteProduct
import PDE.Spaces.Sobolev.Inequalities.Poincare.FiniteExponent
import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates

/-!
# Estimates for the finite-family Dirichlet energy

The finite-family Dirichlet integral is a continuous convex quadratic energy.
After fixing Sobolev boundary data, Poincaré bounds its sublevels in the
zero-boundary perturbation space. These facts do not use the sphere constraint
or any boundary smoothness.
-/

@[expose] public noncomputable section

namespace PDE.CalculusOfVariations

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open FiniteProductComposition
open scoped Sobolev

variable {n m : ℕ} {Ω : Set ℝ^n}

/-- The vector Dirichlet integral is one half of the sum of the squared `L²`
norms of all scalar weak derivatives. -/
theorem vectorDirichletEnergy_eq_sum_norm_sq (U : Fin m → H¹(Ω)) :
    vectorDirichletEnergy U =
      (∑ j : Fin m, ∑ i : Fin n,
        ‖wkpCoordinateCLM (singleDerivIndex n i) (U j)‖ ^ 2) / 2 := by
  have hcol (i : Fin n) :
      (∫ x, ‖derivatives U i x‖ ^ 2 ∂domainMeasure n Ω) =
        ∑ j : Fin m, ‖wkpCoordinateCLM (singleDerivIndex n i) (U j)‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, derivatives]
    rw [integral_finsetSum _ (fun j _ ↦ (Lp.memLp _).norm.integrable_sq)]
    apply Finset.sum_congr rfl
    intro j _
    simpa only [real_inner_self_eq_norm_sq] using
      (L2.inner_def (𝕜 := ℝ) (wkpCoordinateCLM (singleDerivIndex n i) (U j))
        (wkpCoordinateCLM (singleDerivIndex n i) (U j))).symm
  rw [vectorDirichletEnergy, integral_div,
    integral_finsetSum _ (fun i _ ↦ (memLp_derivatives U i).norm.integrable_sq)]
  simp_rw [hcol]
  rw [Finset.sum_comm]

/-- The finite-family Dirichlet energy is continuous in the Sobolev norm. -/
theorem continuous_vectorDirichletEnergy :
    Continuous (vectorDirichletEnergy (n := n) (m := m) (Ω := Ω)) := by
  simp_rw [funext vectorDirichletEnergy_eq_sum_norm_sq]
  fun_prop

/-- Convexity of the squared norm makes the finite-family Dirichlet energy convex. -/
theorem convexOn_vectorDirichletEnergy :
    ConvexOn ℝ univ (vectorDirichletEnergy (n := n) (m := m) (Ω := Ω)) := by
  have hrow (j : Fin m) (i : Fin n) :
      ConvexOn ℝ univ (fun U : Fin m → H¹(Ω) ↦
        ‖wkpCoordinateCLM (singleDerivIndex n i) (U j)‖ ^ 2) := by
    let T : (Fin m → H¹(Ω)) →L[ℝ] DerivLp n 2 Ω :=
      (wkpCoordinateCLM (n := n) (p := 2) (Ω := Ω)
      (singleDerivIndex n i)).comp (ContinuousLinearMap.proj j)
    have h := (convexOn_univ_norm (E := DerivLp n 2 Ω)).comp_linearMap T.toLinearMap
    simpa [T, Function.comp_def] using! h.pow (fun _ _ ↦ norm_nonneg _) 2
  refine ⟨convex_univ, fun U _ V _ a b ha hb hab ↦ ?_⟩
  have h := Finset.sum_le_sum (s := Finset.univ) fun j _ ↦
    Finset.sum_le_sum (s := Finset.univ) fun i _ ↦
      (hrow j i).2 (mem_univ U) (mem_univ V) ha hb hab
  simp only [smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum] at h
  simp only [vectorDirichletEnergy_eq_sum_norm_sq, smul_eq_mul]
  linarith

/-- Subtraction costs at most twice the sum of the two Dirichlet energies. -/
theorem vectorDirichletEnergy_sub_le (U V : Fin m → H¹(Ω)) :
    vectorDirichletEnergy (U - V) ≤
      2 * vectorDirichletEnergy U + 2 * vectorDirichletEnergy V := by
  have hrow (j : Fin m) (i : Fin n) :
      ‖wkpCoordinateCLM (singleDerivIndex n i) ((U - V) j)‖ ^ 2 ≤
        2 * ‖wkpCoordinateCLM (singleDerivIndex n i) (U j)‖ ^ 2 +
        2 * ‖wkpCoordinateCLM (singleDerivIndex n i) (V j)‖ ^ 2 := by
    simp only [Pi.sub_apply, map_sub]
    have h := norm_sub_le (wkpCoordinateCLM (singleDerivIndex n i) (U j))
      (wkpCoordinateCLM (singleDerivIndex n i) (V j))
    nlinarith [norm_nonneg (wkpCoordinateCLM (singleDerivIndex n i) (U j) -
      wkpCoordinateCLM (singleDerivIndex n i) (V j)),
      sq_nonneg (‖wkpCoordinateCLM (singleDerivIndex n i) (U j)‖ -
        ‖wkpCoordinateCLM (singleDerivIndex n i) (V j)‖)]
  have h := Finset.sum_le_sum (s := Finset.univ) fun j _ ↦
    Finset.sum_le_sum (s := Finset.univ) fun i _ ↦ hrow j i
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  simp only [vectorDirichletEnergy_eq_sum_norm_sq]
  linarith

/-- Fixing the boundary data makes every vector Dirichlet energy sublevel
bounded in the full zero-boundary Sobolev norm. -/
theorem isBounded_sublevel_vectorDirichletEnergy
    (hn : 0 < n) (hbounded : Bornology.IsBounded Ω)
    (g : Fin m → H¹(Ω)) (R : ℝ) :
    Bornology.IsBounded {v : Fin m → H¹₀(Ω) |
      vectorDirichletEnergy (fun j ↦ g j + (v j : H¹(Ω))) ≤ R} := by
  obtain ⟨C, hC⟩ := exists_norm_le_wkpGradientCLM hn hbounded (by norm_num : (1 : NNReal) ≤ 2)
  let M := max 1 (4 * R + 4 * vectorDirichletEnergy g)
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C * M, fun v hv ↦ ?_⟩
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg C.coe_nonneg
    (zero_le_one.trans (le_max_left _ _)))).mpr
  intro j
  apply (hC (v j)).trans
  apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
  change ‖wkpGradientCLM (v j : H¹(Ω))‖ ≤ M
  change vectorDirichletEnergy (fun k ↦ g k + (v k : H¹(Ω))) ≤ R at hv
  have h := vectorDirichletEnergy_sub_le (fun k ↦ g k + (v k : H¹(Ω))) g
  have heq : (fun k ↦ g k + (v k : H¹(Ω))) - g = fun k ↦ (v k : H¹(Ω)) := by
    funext k
    simp
  rw [heq, vectorDirichletEnergy_eq_sum_norm_sq] at h
  have hj :
      ‖wkpGradientCLM (v j : H¹(Ω))‖ ^ 2 ≤
        ∑ k : Fin m, ∑ i : Fin n,
          ‖wkpCoordinateCLM (singleDerivIndex n i) (v k : H¹(Ω))‖ ^ 2 := by
    rw [norm_wkpGradientCLM_sq_eq_sum_deriv_sq]
    exact Finset.single_le_sum (f := fun k ↦
      ∑ i : Fin n, ‖wkpCoordinateCLM (singleDerivIndex n i) (v k : H¹(Ω))‖ ^ 2)
      (fun k _ ↦ Finset.sum_nonneg fun i _ ↦ sq_nonneg _) (Finset.mem_univ j)
  have hsq : ‖wkpGradientCLM (v j : H¹(Ω))‖ ^ 2 ≤ 4 * R + 4 * vectorDirichletEnergy g := by
    nlinarith
  have hM : (1 : ℝ) ≤ M := le_max_left _ _
  have hR : 4 * R + 4 * vectorDirichletEnergy g ≤ M := le_max_right _ _
  nlinarith [sq_nonneg (‖wkpGradientCLM (v j : H¹(Ω))‖ - 1)]

end PDE.CalculusOfVariations
