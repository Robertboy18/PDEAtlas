/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LipschitzTopDeriv
public import PDE.FDeriv.PartialDeriv.HigherNorm

/-!
# Lipschitz top derivatives from coordinate words

A `C^k` function on `ℝ^n` whose coordinate derivative words of length `k` are all Lipschitz has a
Lipschitz `k`-th Fréchet derivative. The difference `D^k f(x) - D^k f(x + h)` is the `k`-th
derivative of `f - f(· + h)` at `x`, which the sum of the norms of its coordinate words controls.

A planar tensor sum `x ↦ ∑ᵢ fᵢ(x₁) gᵢ(x₂)` with compact support and factors of the local class
`C^{k,1}` therefore has a Lipschitz `k`-th derivative: every coordinate word is again a tensor sum
of one-dimensional derivatives of order at most `k`, hence locally Lipschitz with compact support.
This covers tensor-product splines of degree `k + 1`, whose `k`-th derivative is only Lipschitz.

## Main results

* `HasCompactSupport.exists_lipschitzWith_of_locallyLipschitz`: a locally Lipschitz function with
  compact support on a proper space is Lipschitz.
* `exists_lipschitzWith_iteratedFDeriv`: a `C^k` function whose coordinate words of length `k`
  are Lipschitz has a Lipschitz `k`-th Fréchet derivative.
* `iteratedPartialDeriv_tensor`: a coordinate word of length at most `k` of a planar tensor sum
  with `C^k` factors is the tensor sum of the one-dimensional derivatives.
* `exists_lipschitzWith_iteratedFDeriv_tensor`: a compactly supported planar tensor sum with
  factors in the local class `C^{k,1}` has a Lipschitz `k`-th Fréchet derivative.
-/

@[expose] public section

open scoped ContDiff NNReal
open PDE.Analysis

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A locally Lipschitz function with compact support on a proper space is Lipschitz. -/
theorem HasCompactSupport.exists_lipschitzWith_of_locallyLipschitz {E G : Type*}
    [PseudoMetricSpace E] [ProperSpace E] [SeminormedAddCommGroup G] {f : E → G}
    (hc : HasCompactSupport f) (hf : LocallyLipschitz f) : ∃ K, LipschitzWith K f := by
  have hT : IsCompact (Metric.cthickening 1 (tsupport f)) := hc.cthickening
  obtain ⟨L, hL⟩ := (hf.locallyLipschitzOn (s := Metric.cthickening 1 (tsupport f))
    ).exists_lipschitzOnWith_of_compact hT
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn hc hf.continuous.continuousOn
  have hST : tsupport f ⊆ Metric.cthickening 1 (tsupport f) :=
    Metric.self_subset_cthickening _
  have hzero : ∀ x, x ∉ tsupport f → f x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  obtain ⟨C, hLC, hMC⟩ : ∃ C : ℝ≥0, (L : ℝ) ≤ C ∧ M ≤ C :=
    ⟨max L (Real.toNNReal M), by exact_mod_cast le_max_left _ _,
      (Real.le_coe_toNNReal M).trans (by exact_mod_cast le_max_right _ _)⟩
  have hfar : ∀ x y, x ∉ Metric.cthickening 1 (tsupport f) →
      dist (f x) (f y) ≤ C * dist x y := by
    intro x y hx
    have hfx : f x = 0 := hzero x fun h ↦ hx (hST h)
    by_cases hy : y ∈ tsupport f
    · have h1 : 1 < dist x y := by
        by_contra hle
        exact hx (Metric.mem_cthickening_of_dist_le x y 1 _ hy (not_lt.mp hle))
      rw [hfx, dist_zero_left]
      nlinarith [hM y hy, NNReal.coe_nonneg C]
    · rw [hfx, hzero y hy, dist_self]
      exact mul_nonneg (NNReal.coe_nonneg C) dist_nonneg
  refine ⟨C, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  by_cases hx : x ∈ Metric.cthickening 1 (tsupport f)
  · by_cases hy : y ∈ Metric.cthickening 1 (tsupport f)
    · exact (hL.dist_le_mul x hx y hy).trans
        (mul_le_mul_of_nonneg_right hLC dist_nonneg)
    · rw [dist_comm, dist_comm x y]
      exact hfar y x hy
  · exact hfar x y hx

namespace PDE

/-- If all coordinate words of length `k` of a `C^k` function are Lipschitz, the coordinate norm
sum of `f - f(· + h)` of order `k` is bounded by a multiple of `‖h‖`. -/
theorem exists_iteratedCoordinateNormSum_sub_le {k : ℕ} {f : ℝ^n → F} (hf : ContDiff ℝ k f)
    (hw : ∀ α : List (Fin n), α.length = k → ∃ K, LipschitzWith K (iteratedPartialDeriv α f)) :
    ∃ C : ℝ, ∀ x h : ℝ^n,
      iteratedCoordinateNormSum k (fun y ↦ f y - f (y + h)) x ≤ C * ‖h‖ := by
  induction k generalizing f with
  | zero =>
    obtain ⟨K, hK⟩ := hw [] rfl
    refine ⟨K, fun x h ↦ ?_⟩
    have hdist := hK.dist_le_mul x (x + h)
    simp only [iteratedPartialDeriv, dist_self_add_right] at hdist
    simpa [iteratedCoordinateNormSum, ← dist_eq_norm] using hdist
  | succ k ih =>
    have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
    have hi : ∀ i : Fin n, ∃ C : ℝ, ∀ x h : ℝ^n,
        iteratedCoordinateNormSum k (fun y ↦ (∂[i] f) y - (∂[i] f) (y + h)) x ≤ C * ‖h‖ := by
      intro i
      refine ih (contDiff_partialDeriv_of_succ (by exact_mod_cast hf)) fun α hα ↦ ?_
      obtain ⟨K, hK⟩ := hw (α ++ [i]) (by simp [hα])
      refine ⟨K, ?_⟩
      have heq : iteratedPartialDeriv α (fun y ↦ (∂[i] f) y) =
          iteratedPartialDeriv (α ++ [i]) f :=
        funext fun y ↦ (iteratedPartialDeriv_append_single α i f y).symm
      rw [heq]
      exact hK
    choose C hC using hi
    refine ⟨∑ i, C i, fun x h ↦ ?_⟩
    have hpartial : ∀ i : Fin n, ∂[i] (fun y ↦ f y - f (y + h)) =
        fun y ↦ (∂[i] f) y - (∂[i] f) (y + h) := by
      intro i
      funext y
      rw [partialDeriv_sub (g := fun y ↦ f (y + h)) (hdiff y) ((hdiff (y + h)).comp y
        (differentiableAt_id.add_const h))]
      simp only [PDE.partialDeriv, fderiv_comp_add_right]
    simp only [iteratedCoordinateNormSum, hpartial, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ ↦ hC i x h

/-- A `C^k` function whose coordinate derivative words of length `k` are all Lipschitz has a
Lipschitz `k`-th Fréchet derivative. -/
theorem exists_lipschitzWith_iteratedFDeriv {k : ℕ} {f : ℝ^n → F} (hf : ContDiff ℝ k f)
    (hw : ∀ α : List (Fin n), α.length = k → ∃ K, LipschitzWith K (iteratedPartialDeriv α f)) :
    ∃ K, LipschitzWith K (iteratedFDeriv ℝ k f) := by
  obtain ⟨C, hC⟩ := exists_iteratedCoordinateNormSum_sub_le hf hw
  refine ⟨Real.toNNReal C, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  set h := y - x
  have hshift : ContDiff ℝ k (fun z ↦ f (z + h)) := hf.comp (contDiff_id.add contDiff_const)
  have heq : iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y =
      iteratedFDeriv ℝ k (fun z ↦ f z - f (z + h)) x := by
    change _ = iteratedFDeriv ℝ k (f - fun z ↦ f (z + h)) x
    rw [iteratedFDeriv_sub_apply hf.contDiffAt hshift.contDiffAt,
      iteratedFDeriv_comp_add_right, show x + h = y by simp [h]]
  have hdiff : ContDiff ℝ k (fun z ↦ f z - f (z + h)) := hf.sub hshift
  rw [dist_eq_norm, heq]
  calc ‖iteratedFDeriv ℝ k (fun z ↦ f z - f (z + h)) x‖
      ≤ iteratedCoordinateNormSum k (fun z ↦ f z - f (z + h)) x :=
        norm_iteratedFDeriv_le_iteratedCoordinateNormSum k hdiff.contDiffAt
    _ ≤ C * ‖h‖ := hC x h
    _ ≤ Real.toNNReal C * dist x y := by
        rw [dist_comm, dist_eq_norm]
        exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C) (norm_nonneg _)

/-- Coordinate derivatives of a planar tensor sum `∑ᵢ Aᵢ(x₁) Bᵢ(x₂)` in the first variable. -/
theorem partialDeriv_zero_tensor {ι : Type*} [Fintype ι] {A B : ι → ℝ → ℝ}
    (hA : ∀ i, Differentiable ℝ (A i)) (hB : ∀ i, Differentiable ℝ (B i)) (x : ℝ^2) :
    (∂[(0 : Fin 2)] (fun y : ℝ^2 ↦ ∑ i, A i (y 0) * B i (y 1))) x =
      ∑ i, deriv (A i) (x 0) * B i (x 1) := by
  have hd : DifferentiableAt ℝ (fun y : ℝ^2 ↦ ∑ i, A i (y 0) * B i (y 1)) x :=
    (Differentiable.fun_sum fun i _ ↦
      ((hA i).comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).differentiable).mul
        ((hB i).comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).differentiable)) x
  rw [partialDeriv_eq_deriv_coordinateLine 0 x hd]
  have hline : ((fun y : ℝ^2 ↦ ∑ i, A i (y 0) * B i (y 1)) ∘ coordinateLine 0 x) =
      fun t ↦ ∑ i, A i t * B i (x 1) := by
    funext t
    simp [coordinateLine]
  rw [hline, deriv_fun_sum (fun i _ ↦ ((hA i) (x 0)).mul_const _)]
  exact Finset.sum_congr rfl fun i _ ↦ deriv_mul_const ((hA i) (x 0)) _

/-- Coordinate derivatives of a planar tensor sum `∑ᵢ Aᵢ(x₁) Bᵢ(x₂)` in the second variable. -/
theorem partialDeriv_one_tensor {ι : Type*} [Fintype ι] {A B : ι → ℝ → ℝ}
    (hA : ∀ i, Differentiable ℝ (A i)) (hB : ∀ i, Differentiable ℝ (B i)) (x : ℝ^2) :
    (∂[(1 : Fin 2)] (fun y : ℝ^2 ↦ ∑ i, A i (y 0) * B i (y 1))) x =
      ∑ i, A i (x 0) * deriv (B i) (x 1) := by
  have hd : DifferentiableAt ℝ (fun y : ℝ^2 ↦ ∑ i, A i (y 0) * B i (y 1)) x :=
    (Differentiable.fun_sum fun i _ ↦
      ((hA i).comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).differentiable).mul
        ((hB i).comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).differentiable)) x
  rw [partialDeriv_eq_deriv_coordinateLine 1 x hd]
  have hline : ((fun y : ℝ^2 ↦ ∑ i, A i (y 0) * B i (y 1)) ∘ coordinateLine 1 x) =
      fun t ↦ ∑ i, A i (x 0) * B i t := by
    funext t
    simp [coordinateLine]
  rw [hline, deriv_fun_sum (fun i _ ↦ ((hB i) (x 1)).const_mul _)]
  exact Finset.sum_congr rfl fun i _ ↦ deriv_const_mul _ ((hB i) (x 1))

/-- A coordinate word of a planar tensor sum with `C^k` factors, of length at most `k`, is the
tensor sum of the one-dimensional derivatives whose orders count the occurrences of each
coordinate in the word. -/
theorem iteratedPartialDeriv_tensor {ι : Type*} [Fintype ι] {k : ℕ} {f g : ι → ℝ → ℝ}
    (hf : ∀ i, ContDiff ℝ k (f i)) (hg : ∀ i, ContDiff ℝ k (g i)) (α : List (Fin 2))
    (hα : α.length ≤ k) :
    iteratedPartialDeriv α (fun x : ℝ^2 ↦ ∑ i, f i (x 0) * g i (x 1)) =
      fun x ↦ ∑ i, iteratedDeriv (α.count 0) (f i) (x 0) *
        iteratedDeriv (α.count 1) (g i) (x 1) := by
  induction α with
  | nil =>
    funext x
    simp [iteratedPartialDeriv]
  | cons j rest ih =>
    have hrest : rest.length < k := by simpa using hα
    have hle : ∀ c : Fin 2, rest.count c < k := fun c ↦
      lt_of_le_of_lt List.count_le_length hrest
    have hA : ∀ i, Differentiable ℝ (iteratedDeriv (rest.count 0) (f i)) := fun i ↦
      (hf i).differentiable_iteratedDeriv _ (by exact_mod_cast hle 0)
    have hB : ∀ i, Differentiable ℝ (iteratedDeriv (rest.count 1) (g i)) := fun i ↦
      (hg i).differentiable_iteratedDeriv _ (by exact_mod_cast hle 1)
    funext x
    change (∂[j] (fun y ↦ iteratedPartialDeriv rest
      (fun x : ℝ^2 ↦ ∑ i, f i (x 0) * g i (x 1)) y)) x = _
    rw [ih hrest.le]
    rcases (by decide : ∀ c : Fin 2, c = 0 ∨ c = 1) j with rfl | rfl
    · rw [partialDeriv_zero_tensor hA hB x]
      simp [iteratedDeriv_succ]
    · rw [partialDeriv_one_tensor hA hB x]
      simp [iteratedDeriv_succ]

/-- A planar tensor sum `x ↦ ∑ᵢ fᵢ(x₁) gᵢ(x₂)` with compact support whose factors lie in the
local class `C^{k,1}` has a Lipschitz `k`-th Fréchet derivative. -/
theorem exists_lipschitzWith_iteratedFDeriv_tensor {ι : Type*} [Fintype ι] {k : ℕ}
    {f g : ι → ℝ → ℝ} (hf : ∀ i, LipschitzTopDeriv k (f i))
    (hg : ∀ i, LipschitzTopDeriv k (g i))
    (hc : HasCompactSupport (fun x : ℝ^2 ↦ ∑ i, f i (x 0) * g i (x 1))) :
    ∃ K, LipschitzWith K (iteratedFDeriv ℝ k (fun x : ℝ^2 ↦ ∑ i, f i (x 0) * g i (x 1))) := by
  have hproj : ∀ c : Fin 2, LocallyLipschitz fun x : ℝ^2 ↦ x c := fun c ↦
    (EuclideanSpace.proj (𝕜 := ℝ) c).lipschitzWith.locallyLipschitz
  have hcont : ContDiff ℝ k (fun x : ℝ^2 ↦ ∑ i, f i (x 0) * g i (x 1)) := by
    refine ContDiff.sum fun i _ ↦ ?_
    exact ((hf i).contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff).mul
      ((hg i).contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff)
  refine exists_lipschitzWith_iteratedFDeriv hcont fun α hα ↦ ?_
  have hword := iteratedPartialDeriv_tensor (fun i ↦ (hf i).contDiff)
    (fun i ↦ (hg i).contDiff) α hα.le
  have hloc : LocallyLipschitz (iteratedPartialDeriv α
      (fun x : ℝ^2 ↦ ∑ i, f i (x 0) * g i (x 1))) := by
    rw [hword]
    refine locallyLipschitz_sum _ fun i _ ↦ locallyLipschitz_mul ?_ ?_
    · exact ((hf i).locallyLipschitz_iteratedDeriv
        (hα ▸ List.count_le_length)).comp (hproj 0)
    · exact ((hg i).locallyLipschitz_iteratedDeriv
        (hα ▸ List.count_le_length)).comp (hproj 1)
  exact (hc.iteratedPartialDeriv α).exists_lipschitzWith_of_locallyLipschitz hloc

end PDE
