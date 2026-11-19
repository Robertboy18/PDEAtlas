/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Norms
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Laplacian

/-!
# Ordered Hessians and the second-order graph norm

The graph stores each symmetric derivative multiindex once. The ordered Hessian
counts both `(i,j)` and `(j,i)`. The estimates here compare these two conventions
without identifying their norms. They hold also in spatial dimension zero.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open scoped ENNReal Sobolev Laplacian

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A nonnegative sum over symmetric indices is bounded by the sum over the
base, first derivatives, and all ordered second derivatives. -/
theorem sum_derivIndex_two_le_ordered (f : DerivIndex n 2 → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (∑ a, f a) ≤ f (baseIndex n 2) +
      (∑ i : Fin n, f (firstDerivIndex n 2 (by omega) i)) +
        ∑ i : Fin n, ∑ j : Fin n, f (pairDerivIndex n i j) := by
  classical
  let e : Unit ⊕ (Fin n ⊕ (Fin n × Fin n)) → DerivIndex n 2 :=
    Sum.elim (fun _ ↦ baseIndex n 2)
      (Sum.elim (firstDerivIndex n 2 (by omega)) (fun p ↦ pairDerivIndex n p.1 p.2))
  have he : Function.Surjective e := by
    intro a
    induction a using DerivIndex.inductionOnOrderTwo with
    | base => exact ⟨Sum.inl (), rfl⟩
    | first i => exact ⟨Sum.inr (Sum.inl i), rfl⟩
    | second a i j ha =>
      exact ⟨Sum.inr (Sum.inr (i, j)), (a.eq_pairDerivIndex i j ha).symm⟩
  have hi : Finset.univ.image e = Finset.univ := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    exact he a
  have h := Finset.sum_image_le_of_nonneg (s := Finset.univ) (g := e)
    (f := f) (fun a _ ↦ hf a)
  rw [hi] at h
  simpa [e, Fintype.sum_sum_type, Fintype.sum_prod_type, add_assoc] using h

/-- The H² norm is controlled by the full ordered derivative energy.
Off-diagonal second derivatives may occur twice on the right. -/
theorem ambient_norm_sq_le_base_add_first_add_hessian (U : WkpAmbientOn n 2 2 Ω) :
    ‖U‖ ^ 2 ≤ ‖U (baseIndex n 2)‖ ^ 2 +
      (∑ i : Fin n, ‖U (firstDerivIndex n 2 (by omega) i)‖ ^ 2) +
        ∑ i : Fin n, ∑ j : Fin n, ‖U (pairDerivIndex n i j)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact sum_derivIndex_two_le_ordered _ (fun a ↦ sq_nonneg _)

/-- A dimension-dependent converse comparison for the ordered derivative energy.
The constant is also valid in dimension zero. -/
theorem base_add_first_add_hessian_le_ambient_norm_sq (U : WkpAmbientOn n 2 2 Ω) :
    ‖U (baseIndex n 2)‖ ^ 2 +
      (∑ i : Fin n, ‖U (firstDerivIndex n 2 (by omega) i)‖ ^ 2) +
        (∑ i : Fin n, ∑ j : Fin n, ‖U (pairDerivIndex n i j)‖ ^ 2) ≤
      (1 + (n : ℝ) + (n : ℝ) * n) * ‖U‖ ^ 2 := by
  have hc (a : DerivIndex n 2) : ‖U a‖ ^ 2 ≤ ‖U‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (PiLp.norm_apply_le U a)
  calc
    _ ≤ ‖U‖ ^ 2 + (∑ _i : Fin n, ‖U‖ ^ 2) +
        ∑ _i : Fin n, ∑ _j : Fin n, ‖U‖ ^ 2 :=
      add_le_add (add_le_add (hc _)
        (Finset.sum_le_sum fun i _ ↦ hc _))
        (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hc _)
    _ = _ := by simp [add_mul, mul_assoc]

/-- The squared L² norm of the weak Laplacian is at most the spatial dimension
times the full ordered Hessian energy. -/
theorem norm_wkpLaplacianCLM_sq_le_hessian (U : W^{2,2}(Ω)) :
    ‖Δ U‖ ^ 2 ≤ (n : ℝ) *
      ∑ i : Fin n, ∑ j : Fin n,
        ‖(U : WkpAmbientOn n 2 2 Ω) (pairDerivIndex n i j)‖ ^ 2 := by
  classical
  let d (i : Fin n) := (U : WkpAmbientOn n 2 2 Ω) (pairDerivIndex n i i)
  calc
    ‖Δ U‖ ^ 2 ≤ (∑ i : Fin n, ‖d i‖) ^ 2 := by
      apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ ↦ norm_nonneg _)).mpr
      simpa only [laplacian_eq_wkpLaplacianCLM, wkpLaplacianCLM_apply] using
        norm_sum_le Finset.univ d
    _ ≤ (n : ℝ) * ∑ i : Fin n, ‖d i‖ ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : Fin n ↦ (1 : ℝ)) (fun i ↦ ‖d i‖)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
      exact Finset.sum_le_sum fun i _ ↦
        Finset.single_le_sum
          (fun j _ ↦ sq_nonneg ‖(U : WkpAmbientOn n 2 2 Ω) (pairDerivIndex n i j)‖)
          (Finset.mem_univ i)

end SobolevSpace.GraphSpace
