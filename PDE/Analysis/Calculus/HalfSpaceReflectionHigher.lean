/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.HalfSpaceReflection
import PDE.Analysis.Calculus.HalfSpaceGluingWithin
public import Mathlib.Topology.MetricSpace.Holder

/-!
# Derivatives of every order of the weighted reflection across a coordinate hyperplane

For `f : ℝ^n → ℝ` of class `C^k` within the closed half-space `H = {x | 0 ≤ x i}`, the weighted
reflection `E f = weightedReflectionFun i k f` is a global `C^k` function equal to `f` on `H` and
to `∑ⱼ cⱼ f (dⱼ x)` below it, where `dⱼ` multiplies the coordinate `i` by `-(j + 1)`. For every
order `m ≤ k` its `m`-th derivative is the `m`-th derivative of `f` within `H` on `H`, and the
weighted sum `∑ⱼ cⱼ D^m f(dⱼ x)(dⱼ ·, …, dⱼ ·)` below it. Below `H` the dilations stretch by at
most `k + 1`, and a pair of points on the two sides is split at the point of their segment on the
hyperplane; this gives the Hölder bound for the top derivative. The dilations do not decrease
norms, so the reflection keeps supports inside balls.

## Main definitions

* `reflectedIteratedFDeriv`: the pulled-back weighted sum `∑ⱼ cⱼ D^m f(dⱼ x)(dⱼ ·, …, dⱼ ·)`.

## Main results

* `iteratedFDeriv_weightedReflectionFun`: the `m`-th derivative of `E f`, `m ≤ k`, is the
  derivative within `H` on `H` and the pulled-back weighted sum below it.
* `norm_iteratedFDeriv_weightedReflectionFun_sub_le`: the `m`-th derivatives of `E f - E g` are
  bounded by `reflectionBound k m` times the corresponding bound on `H`.
* `holderWith_iteratedFDeriv_weightedReflectionFun`: an `α`-Hölder `k`-th derivative within `H`
  with constant `M` gives a globally `α`-Hölder `k`-th derivative of `E f` with constant
  `(reflectionBound k (k + 1) + 1) M`.
* `weightedReflectionFun_eq_zero_of_norm_lt`: `E f` vanishes outside the closed ball of radius
  `R` when `f` vanishes on `H` outside it.
* `continuousOn_iteratedFDeriv_weightedReflectionFun`: for a family `f t` whose derivatives within
  `H` are continuous in `t` uniformly on `H`, every derivative of order `m ≤ k` of `E (f t)` is
  jointly continuous.
* `weightedReflectionFun_comp_coordinateReflection`: the reflection keeps the parity of `f` under
  reflections in the other coordinates.
* `contDiff_weightedReflectionFun_of_le`: a reflection of order `K ≥ k` of a function `C^k` within
  `H` is `C^k`.
-/

@[expose] public section

noncomputable section

open Set Filter Metric
open scoped Topology NNReal
open SobolevSpace.GraphSpace.HigherOrderReflection PDE.Common

namespace PDE.Analysis

variable {n : ℕ}

/-! ### The dilations -/

/-- The operator norm of a reflection dilation is at most `j + 1`. -/
theorem opNorm_normalDilation_reflectionNode_le (i : Fin n) (k : ℕ) (j : Fin (k + 1)) :
    ‖normalDilation i (reflectionNode k j)‖ ≤ (j : ℝ) + 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (norm_normalDilation_reflectionNode_le i k j)

/-- A normal dilation by a factor of absolute value at least one does not decrease norms. -/
theorem norm_le_norm_normalDilation (i : Fin n) {a : ℝ} (ha : 1 ≤ |a|) (x : ℝ^n) :
    ‖x‖ ≤ ‖normalDilation i a x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro l _
  rw [normalDilation_apply, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, mul_pow]
  split_ifs
  · exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ ha)
  · rw [abs_one, one_pow, one_mul]

/-- The reflection dilations do not decrease norms. -/
theorem norm_le_norm_normalDilation_reflectionNode (i : Fin n) (k : ℕ) (j : Fin (k + 1))
    (x : ℝ^n) : ‖x‖ ≤ ‖normalDilation i (reflectionNode k j) x‖ := by
  apply norm_le_norm_normalDilation i
  rw [abs_reflectionNode]
  linarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg _]

/-- The reflection dilations map the closed lower half-space into the closed upper one. -/
theorem normalDilation_reflectionNode_nonneg (i : Fin n) (k : ℕ) (j : Fin (k + 1)) {x : ℝ^n}
    (hx : x i ≤ 0) : 0 ≤ normalDilation i (reflectionNode k j) x i := by
  simp only [normalDilation_apply, ↓reduceIte]
  exact mul_nonneg_of_nonpos_of_nonpos (reflectionNode_neg k j).le hx

/-- Pulling a multilinear map back along the same linear map in every slot multiplies its norm by
at most the `m`-th power of the norm of the linear map. -/
theorem norm_compContinuousLinearMap_const_le {m : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ ℝ^n) ℝ) (d : ℝ^n →L[ℝ] ℝ^n) :
    ‖A.compContinuousLinearMap (fun _ ↦ d)‖ ≤ ‖A‖ * ‖d‖ ^ m := by
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    A.norm_compContinuousLinearMap_le (fun _ ↦ d)

/-- Pullback along the same linear map in every slot is additive. -/
theorem compContinuousLinearMap_const_sub {m : ℕ}
    (A B : ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ ℝ^n) ℝ) (d : ℝ^n →L[ℝ] ℝ^n) :
    (A - B).compContinuousLinearMap (fun _ ↦ d) =
      A.compContinuousLinearMap (fun _ ↦ d) - B.compContinuousLinearMap (fun _ ↦ d) := by
  ext v
  simp

/-! ### The closed form of the derivatives -/

/-- The weighted sum `∑ⱼ cⱼ D^m f(dⱼ x)(dⱼ ·, …, dⱼ ·)` of the `m`-th derivatives within the
closed half-space at the dilated points, pulled back along the dilations: the `m`-th derivative
of the weighted reflection below the hyperplane. -/
def reflectedIteratedFDeriv (i : Fin n) (k m : ℕ) (f : ℝ^n → ℝ) (x : ℝ^n) :
    ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ ℝ^n) ℝ :=
  ∑ j, reflectionCoeff k j • (iteratedFDerivWithin ℝ m f {y | 0 ≤ y i}
    (normalDilation i (reflectionNode k j) x)).compContinuousLinearMap
      (fun _ ↦ normalDilation i (reflectionNode k j))

variable (i : Fin n) {k : ℕ} {f g : ℝ^n → ℝ}

/-- **The derivatives on the closed half-space.** On `H` the `m`-th derivative of the weighted
reflection of a `C^k` function, `m ≤ k`, is its `m`-th derivative within `H`. -/
theorem iteratedFDeriv_weightedReflectionFun_of_nonneg (hk : 1 ≤ k)
    (hf : ContDiffOn ℝ k f {y | 0 ≤ y i}) {m : ℕ} (hm : m ≤ k) {x : ℝ^n} (hx : 0 ≤ x i) :
    iteratedFDeriv ℝ m (weightedReflectionFun i k f) x =
      iteratedFDerivWithin ℝ m f {y | 0 ≤ y i} x := by
  have hE := contDiff_weightedReflectionFun i hk hf
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_coordinateHalfSpace i)
    ((hE.of_le (by exact_mod_cast hm)).contDiffAt) hx]
  exact iteratedFDerivWithin_congr
    (fun y hy ↦ weightedReflectionFun_eq_of_nonneg i k f y hy) hx m

/-- **The derivatives below the hyperplane.** Below `H` the `m`-th derivative of the weighted
reflection of a `C^k` function, `m ≤ k`, is the weighted sum of the `m`-th derivatives within `H`
at the dilated points, pulled back along the dilations. -/
theorem iteratedFDeriv_weightedReflectionFun_of_neg (hf : ContDiffOn ℝ k f {y | 0 ≤ y i})
    {m : ℕ} (hm : m ≤ k) {x : ℝ^n} (hx : x i < 0) :
    iteratedFDeriv ℝ m (weightedReflectionFun i k f) x = reflectedIteratedFDeriv i k m f x := by
  obtain ⟨F, hF, hFeq⟩ := exists_contDiff_extension_halfSpace i k hf
  have hEF : weightedReflectionFun i k f = weightedReflectionFun i k F :=
    weightedReflectionFun_congr i k (fun y hy ↦ (hFeq hy).symm)
  set d : Fin (k + 1) → ℝ^n →L[ℝ] ℝ^n := fun j ↦ normalDilation i (reflectionNode k j) with hd
  have hFm : ContDiff ℝ m F := hF.of_le (by exact_mod_cast hm)
  have hev : weightedReflectionFun i k F =ᶠ[𝓝 x] fun y ↦ ∑ j, reflectionCoeff k j • F (d j y) := by
    filter_upwards [(isOpen_lt (EuclideanSpace.proj i).continuous continuous_const).mem_nhds hx]
      with y hy
    simpa [smul_eq_mul, hd] using weightedReflectionFun_of_neg i k F hy
  have hterm (j : Fin (k + 1)) : ContDiff ℝ m (fun y ↦ reflectionCoeff k j • F (d j y)) :=
    (hFm.comp (d j).contDiff).const_smul _
  rw [hEF, (hev.iteratedFDeriv ℝ m).eq_of_nhds,
    iteratedFDeriv_sum (u := Finset.univ) (fun j _ ↦ hterm j), Finset.sum_apply]
  unfold reflectedIteratedFDeriv
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hy : 0 ≤ d j x i := le_of_lt (normalDilation_reflectionNode_pos i k j hx)
  have hs := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := reflectionCoeff k j)
    (f := fun y ↦ F (d j y)) (x := x) (i := m) ((hFm.comp (d j).contDiff).contDiffAt)
  rw [hs, show (fun y ↦ F (d j y)) = F ∘ d j from rfl,
    (d j).iteratedFDeriv_comp_right hFm x le_rfl,
    ← iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_coordinateHalfSpace i)
      hFm.contDiffAt hy, iteratedFDerivWithin_congr (fun y hy ↦ hFeq hy) hy m]

/-- **The closed form of the derivatives of the weighted reflection.** -/
theorem iteratedFDeriv_weightedReflectionFun (hk : 1 ≤ k) (hf : ContDiffOn ℝ k f {y | 0 ≤ y i})
    {m : ℕ} (hm : m ≤ k) (x : ℝ^n) :
    iteratedFDeriv ℝ m (weightedReflectionFun i k f) x =
      if x i < 0 then reflectedIteratedFDeriv i k m f x
      else iteratedFDerivWithin ℝ m f {y | 0 ≤ y i} x := by
  split_ifs with hx
  · exact iteratedFDeriv_weightedReflectionFun_of_neg i hf hm hx
  · exact iteratedFDeriv_weightedReflectionFun_of_nonneg i hk hf hm (not_lt.mp hx)

/-! ### Bounds -/

/-- The pulled-back sums of two functions differ by at most `reflectionBound k m` times the bound
of the difference of their `m`-th derivatives within the closed half-space. -/
theorem norm_reflectedIteratedFDeriv_sub_le {m : ℕ} {B : ℝ}
    (hB : ∀ y : ℝ^n, 0 ≤ y i →
      ‖iteratedFDerivWithin ℝ m f {y | 0 ≤ y i} y -
        iteratedFDerivWithin ℝ m g {y | 0 ≤ y i} y‖ ≤ B)
    {x : ℝ^n} (hx : x i ≤ 0) :
    ‖reflectedIteratedFDeriv i k m f x - reflectedIteratedFDeriv i k m g x‖ ≤
      reflectionBound k m * B := by
  unfold reflectedIteratedFDeriv
  rw [← Finset.sum_sub_distrib, reflectionBound, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [show ∀ (c : ℝ) (P Q : ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ ℝ^n) ℝ),
      c • P - c • Q = c • (P - Q) from fun c P Q ↦ (smul_sub c P Q).symm,
    ← compContinuousLinearMap_const_sub, norm_smul, Real.norm_eq_abs]
  have hj := hB _ (normalDilation_reflectionNode_nonneg i k j hx)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hj
  calc |reflectionCoeff k j| * ‖(iteratedFDerivWithin ℝ m f {y | 0 ≤ y i} _ -
          iteratedFDerivWithin ℝ m g {y | 0 ≤ y i} _).compContinuousLinearMap
            (fun _ ↦ normalDilation i (reflectionNode k j))‖
      ≤ |reflectionCoeff k j| * (B * ((j : ℝ) + 1) ^ m) := by
        gcongr
        refine (norm_compContinuousLinearMap_const_le _ _).trans ?_
        exact mul_le_mul hj (pow_le_pow_left₀ (norm_nonneg _)
          (opNorm_normalDilation_reflectionNode_le i k j) m) (by positivity) hB0
    _ = |reflectionCoeff k j| * ((j : ℝ) + 1) ^ m * B := by ring

/-- **Bounds of the derivatives.** The `m`-th derivatives, `m ≤ k`, of the weighted reflections
of two `C^k` functions differ everywhere by at most `reflectionBound k m` times the bound on the
closed half-space of the difference of their `m`-th derivatives within it. -/
theorem norm_iteratedFDeriv_weightedReflectionFun_sub_le (hk : 1 ≤ k)
    (hf : ContDiffOn ℝ k f {y | 0 ≤ y i}) (hg : ContDiffOn ℝ k g {y | 0 ≤ y i}) {m : ℕ}
    (hm : m ≤ k) {B : ℝ}
    (hB : ∀ y : ℝ^n, 0 ≤ y i →
      ‖iteratedFDerivWithin ℝ m f {y | 0 ≤ y i} y -
        iteratedFDerivWithin ℝ m g {y | 0 ≤ y i} y‖ ≤ B) (x : ℝ^n) :
    ‖iteratedFDeriv ℝ m (weightedReflectionFun i k f) x -
        iteratedFDeriv ℝ m (weightedReflectionFun i k g) x‖ ≤ reflectionBound k m * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by simp))
  by_cases hx : x i < 0
  · rw [iteratedFDeriv_weightedReflectionFun_of_neg i hf hm hx,
      iteratedFDeriv_weightedReflectionFun_of_neg i hg hm hx]
    exact norm_reflectedIteratedFDeriv_sub_le i hB hx.le
  · rw [iteratedFDeriv_weightedReflectionFun_of_nonneg i hk hf hm (not_lt.mp hx),
      iteratedFDeriv_weightedReflectionFun_of_nonneg i hk hg hm (not_lt.mp hx)]
    exact (hB x (not_lt.mp hx)).trans (le_mul_of_one_le_left hB0 (one_le_reflectionBound k m))

/-- The `m`-th derivative, `m ≤ k`, of the weighted reflection is bounded by
`reflectionBound k m` times the bound of the `m`-th derivative within the closed half-space. -/
theorem norm_iteratedFDeriv_weightedReflectionFun_le (hk : 1 ≤ k)
    (hf : ContDiffOn ℝ k f {y | 0 ≤ y i}) {m : ℕ} (hm : m ≤ k) {B : ℝ}
    (hB : ∀ y : ℝ^n, 0 ≤ y i → ‖iteratedFDerivWithin ℝ m f {y | 0 ≤ y i} y‖ ≤ B) (x : ℝ^n) :
    ‖iteratedFDeriv ℝ m (weightedReflectionFun i k f) x‖ ≤ reflectionBound k m * B := by
  have h := norm_iteratedFDeriv_weightedReflectionFun_sub_le i hk hf (g := fun _ ↦ 0)
    contDiffOn_const hm (fun y hy ↦ by simpa using hB y hy) x
  have hzero : weightedReflectionFun i k (fun _ : ℝ^n ↦ (0 : ℝ)) = fun _ ↦ 0 :=
    weightedReflectionFun_zero i k
  simpa [hzero] using h

/-! ### Hölder continuity of the top derivative -/

/-- The pulled-back sums are continuous on the closed lower half-space. -/
theorem continuousOn_reflectedIteratedFDeriv (hf : ContDiffOn ℝ k f {y | 0 ≤ y i}) {m : ℕ}
    (hm : m ≤ k) : ContinuousOn (reflectedIteratedFDeriv i k m f) {y | y i ≤ 0} := by
  have hA : ContinuousOn (iteratedFDerivWithin ℝ m f {y | 0 ≤ y i}) {y | 0 ≤ y i} :=
    hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast hm)
      (uniqueDiffOn_coordinateHalfSpace i)
  unfold reflectedIteratedFDeriv
  refine continuousOn_finsetSum _ fun j _ ↦ ?_
  have hd : ContinuousOn (fun y ↦ iteratedFDerivWithin ℝ m f {y | 0 ≤ y i}
      (normalDilation i (reflectionNode k j) y)) {y | y i ≤ 0} :=
    hA.comp (normalDilation i (reflectionNode k j)).continuous.continuousOn
      fun y hy ↦ normalDilation_reflectionNode_nonneg i k j hy
  refine (((ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin m ↦ normalDilation i (reflectionNode k j))).continuous.comp_continuousOn
      hd).const_smul (reflectionCoeff k j)).congr fun y _ ↦ ?_
  simp

/-- The closed lower half-space is the closure of the open one. -/
theorem subset_closure_lowerHalfSpace : {y : ℝ^n | y i ≤ 0} ⊆ closure {y : ℝ^n | y i < 0} := by
  intro y hy
  rw [Metric.mem_closure_iff]
  intro ε hε
  refine ⟨y - (ε / 2) • EuclideanSpace.single i 1, ?_, ?_⟩
  · have : (y : ℝ^n) i ≤ 0 := hy
    change (y - (ε / 2) • EuclideanSpace.single i (1 : ℝ)) i < 0
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    simp
    linarith
  · rw [dist_eq_norm, sub_sub_cancel, norm_smul]
    simp only [Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    simp only [PiLp.norm_single, norm_one, mul_one, half_lt_self_iff]
    exact hε

/-- **The top derivative on the closed lower half-space.** On `{x i ≤ 0}` the `k`-th derivative of
the weighted reflection of a `C^k` function is the pulled-back sum; on the hyperplane both forms
agree. -/
theorem iteratedFDeriv_weightedReflectionFun_of_nonpos (hk : 1 ≤ k)
    (hf : ContDiffOn ℝ k f {y | 0 ≤ y i}) {m : ℕ} (hm : m ≤ k) {x : ℝ^n} (hx : x i ≤ 0) :
    iteratedFDeriv ℝ m (weightedReflectionFun i k f) x = reflectedIteratedFDeriv i k m f x := by
  refine Set.EqOn.of_subset_closure (s := {y : ℝ^n | y i < 0}) (t := {y : ℝ^n | y i ≤ 0})
    (fun y hy ↦ iteratedFDeriv_weightedReflectionFun_of_neg i hf hm hy)
    ((contDiff_weightedReflectionFun i hk hf).continuous_iteratedFDeriv
      (by exact_mod_cast hm)).continuousOn
    (continuousOn_reflectedIteratedFDeriv i hf hm) (fun y (hy : y i < 0) ↦ hy.le)
    (subset_closure_lowerHalfSpace i) hx

/-- The pulled-back sums of an `α`-Hölder `k`-th derivative are `α`-Hölder on the closed lower
half-space with constant `reflectionBound k (k + 1) M`. -/
theorem norm_reflectedIteratedFDeriv_sub_rpow_le {α M : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hM : 0 ≤ M)
    (hH : ∀ y z : ℝ^n, 0 ≤ y i → 0 ≤ z i →
      ‖iteratedFDerivWithin ℝ k f {y | 0 ≤ y i} y -
        iteratedFDerivWithin ℝ k f {y | 0 ≤ y i} z‖ ≤ M * ‖y - z‖ ^ α)
    {x x' : ℝ^n} (hx : x i ≤ 0) (hx' : x' i ≤ 0) :
    ‖reflectedIteratedFDeriv i k k f x - reflectedIteratedFDeriv i k k f x'‖ ≤
      reflectionBound k (k + 1) * M * ‖x - x'‖ ^ α := by
  unfold reflectedIteratedFDeriv
  rw [← Finset.sum_sub_distrib, reflectionBound, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [show ∀ (c : ℝ) (P Q : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ ℝ^n) ℝ),
      c • P - c • Q = c • (P - Q) from fun c P Q ↦ (smul_sub c P Q).symm,
    ← compContinuousLinearMap_const_sub, norm_smul, Real.norm_eq_abs]
  set d := normalDilation i (reflectionNode k j)
  have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg _]
  have hdist : ‖d x - d x'‖ ≤ ((j : ℝ) + 1) * ‖x - x'‖ := by
    rw [← map_sub]
    exact norm_normalDilation_reflectionNode_le i k j _
  have hpow : ‖d x - d x'‖ ^ α ≤ ((j : ℝ) + 1) * ‖x - x'‖ ^ α := by
    calc ‖d x - d x'‖ ^ α ≤ (((j : ℝ) + 1) * ‖x - x'‖) ^ α :=
          Real.rpow_le_rpow (norm_nonneg _) hdist hα0
      _ = ((j : ℝ) + 1) ^ α * ‖x - x'‖ ^ α :=
          Real.mul_rpow (by positivity) (norm_nonneg _)
      _ ≤ ((j : ℝ) + 1) * ‖x - x'‖ ^ α := by
          gcongr
          simpa using Real.rpow_le_rpow_of_exponent_le hj1 hα1
  have hHj := hH (d x) (d x') (normalDilation_reflectionNode_nonneg i k j hx)
    (normalDilation_reflectionNode_nonneg i k j hx')
  calc |reflectionCoeff k j| * ‖(iteratedFDerivWithin ℝ k f {y | 0 ≤ y i} (d x) -
          iteratedFDerivWithin ℝ k f {y | 0 ≤ y i} (d x')).compContinuousLinearMap
            (fun _ ↦ d)‖
      ≤ |reflectionCoeff k j| * ((M * (((j : ℝ) + 1) * ‖x - x'‖ ^ α)) * ((j : ℝ) + 1) ^ k) := by
        gcongr
        refine (norm_compContinuousLinearMap_const_le _ _).trans ?_
        exact mul_le_mul (hHj.trans (mul_le_mul_of_nonneg_left hpow hM))
          (pow_le_pow_left₀ (norm_nonneg _) (opNorm_normalDilation_reflectionNode_le i k j) k)
          (by positivity) (by positivity)
    _ = |reflectionCoeff k j| * ((j : ℝ) + 1) ^ (k + 1) * M * ‖x - x'‖ ^ α := by ring

/-- **Hölder continuity of the top derivative.** If the `k`-th derivative within the closed
half-space of a `C^k` function is `α`-Hölder with constant `M`, `0 ≤ α ≤ 1`, the `k`-th derivative
of its weighted reflection is `α`-Hölder on the whole space with constant
`(reflectionBound k (k + 1) + 1) M`. -/
theorem norm_iteratedFDeriv_weightedReflectionFun_sub_rpow_le (hk : 1 ≤ k)
    (hf : ContDiffOn ℝ k f {y | 0 ≤ y i}) {α M : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hM : 0 ≤ M)
    (hH : ∀ y z : ℝ^n, 0 ≤ y i → 0 ≤ z i →
      ‖iteratedFDerivWithin ℝ k f {y | 0 ≤ y i} y -
        iteratedFDerivWithin ℝ k f {y | 0 ≤ y i} z‖ ≤ M * ‖y - z‖ ^ α) (x x' : ℝ^n) :
    ‖iteratedFDeriv ℝ k (weightedReflectionFun i k f) x -
        iteratedFDeriv ℝ k (weightedReflectionFun i k f) x'‖ ≤
      (reflectionBound k (k + 1) + 1) * M * ‖x - x'‖ ^ α := by
  set C := reflectionBound k (k + 1)
  have hC : 0 ≤ C := reflectionBound_nonneg k (k + 1)
  have hq : 0 ≤ ‖x - x'‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
  have hlow {y y' : ℝ^n} (hy : y i ≤ 0) (hy' : y' i ≤ 0) :
      ‖iteratedFDeriv ℝ k (weightedReflectionFun i k f) y -
        iteratedFDeriv ℝ k (weightedReflectionFun i k f) y'‖ ≤ C * M * ‖y - y'‖ ^ α := by
    rw [iteratedFDeriv_weightedReflectionFun_of_nonpos i hk hf le_rfl hy,
      iteratedFDeriv_weightedReflectionFun_of_nonpos i hk hf le_rfl hy']
    exact norm_reflectedIteratedFDeriv_sub_rpow_le i hα0 hα1 hM hH hy hy'
  have hup {y y' : ℝ^n} (hy : 0 ≤ y i) (hy' : 0 ≤ y' i) :
      ‖iteratedFDeriv ℝ k (weightedReflectionFun i k f) y -
        iteratedFDeriv ℝ k (weightedReflectionFun i k f) y'‖ ≤ M * ‖y - y'‖ ^ α := by
    rw [iteratedFDeriv_weightedReflectionFun_of_nonneg i hk hf le_rfl hy,
      iteratedFDeriv_weightedReflectionFun_of_nonneg i hk hf le_rfl hy']
    exact hH y y' hy hy'
  -- a pair with one point strictly below and one strictly above the hyperplane
  have hcross {y y' : ℝ^n} (hy : y i < 0) (hy' : 0 < y' i) :
      ‖iteratedFDeriv ℝ k (weightedReflectionFun i k f) y -
        iteratedFDeriv ℝ k (weightedReflectionFun i k f) y'‖ ≤
          (C + 1) * M * ‖y - y'‖ ^ α := by
    set c := y i / (y i - y' i)
    have hden : y i - y' i < 0 := by linarith
    have hc0 : 0 ≤ c := div_nonneg_of_nonpos hy.le hden.le
    have hc1 : c ≤ 1 := (div_le_one_of_neg hden).mpr (by linarith)
    set z := y + c • (y' - y)
    have hne : y i - y' i ≠ 0 := hden.ne
    have hz : z i = 0 := by
      simp only [z, c, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      field_simp
      ring
    have hyz : ‖y - z‖ ≤ ‖y - y'‖ := by
      rw [show y - z = -(c • (y' - y)) by simp only [z]; abel, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hc0, norm_sub_rev]
      exact mul_le_of_le_one_left (norm_nonneg _) hc1
    have hzy : ‖z - y'‖ ≤ ‖y - y'‖ := by
      rw [show z - y' = (1 - c) • (y - y') by simp only [z]; module, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
    have h1 := hlow hy.le hz.le
    have h2 := hup hz.ge hy'.le
    calc ‖iteratedFDeriv ℝ k (weightedReflectionFun i k f) y -
          iteratedFDeriv ℝ k (weightedReflectionFun i k f) y'‖
        ≤ ‖iteratedFDeriv ℝ k (weightedReflectionFun i k f) y -
            iteratedFDeriv ℝ k (weightedReflectionFun i k f) z‖ +
          ‖iteratedFDeriv ℝ k (weightedReflectionFun i k f) z -
            iteratedFDeriv ℝ k (weightedReflectionFun i k f) y'‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ C * M * ‖y - z‖ ^ α + M * ‖z - y'‖ ^ α := add_le_add h1 h2
      _ ≤ C * M * ‖y - y'‖ ^ α + M * ‖y - y'‖ ^ α := by
          gcongr
      _ = (C + 1) * M * ‖y - y'‖ ^ α := by ring
  rcases le_or_gt (x i) 0 with hx | hx
  · rcases le_or_gt (x' i) 0 with hx' | hx'
    · exact (hlow hx hx').trans (by nlinarith [mul_nonneg hM hq])
    · rcases hx.lt_or_eq with hx | hx
      · exact hcross hx hx'
      · exact (hup hx.ge hx'.le).trans (by nlinarith [mul_nonneg hM hq, mul_nonneg hC hM])
  · rcases le_or_gt (x' i) 0 with hx' | hx'
    · rcases hx'.lt_or_eq with hx' | hx'
      · rw [norm_sub_rev, norm_sub_rev x]
        exact hcross hx' hx
      · exact (hup hx.le hx'.ge).trans (by nlinarith [mul_nonneg hM hq, mul_nonneg hC hM])
    · exact (hup hx.le hx'.le).trans (by nlinarith [mul_nonneg hM hq, mul_nonneg hC hM])

/-- **The weighted reflection is of class `C^{k,α}`.** For a `C^k` function on the closed
half-space whose `k`-th derivative within it is `α`-Hölder with constant `M`, the `k`-th
derivative of the weighted reflection is globally `α`-Hölder. -/
theorem holderWith_iteratedFDeriv_weightedReflectionFun (hk : 1 ≤ k)
    (hf : ContDiffOn ℝ k f {y | 0 ≤ y i}) {α M : ℝ≥0} (hα1 : α ≤ 1)
    (hH : ∀ y z : ℝ^n, 0 ≤ y i → 0 ≤ z i →
      ‖iteratedFDerivWithin ℝ k f {y | 0 ≤ y i} y -
        iteratedFDerivWithin ℝ k f {y | 0 ≤ y i} z‖ ≤ M * ‖y - z‖ ^ (α : ℝ)) :
    HolderWith (Real.toNNReal ((reflectionBound k (k + 1) + 1) * M)) α
      (iteratedFDeriv ℝ k (weightedReflectionFun i k f)) := by
  intro x x'
  have hpos : 0 ≤ (reflectionBound k (k + 1) + 1) * (M : ℝ) :=
    mul_nonneg (by linarith [reflectionBound_nonneg k (k + 1)]) M.coe_nonneg
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
    ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hpos]
  exact norm_iteratedFDeriv_weightedReflectionFun_sub_rpow_le i hk hf α.coe_nonneg
    (by exact_mod_cast hα1) M.coe_nonneg hH x x'

/-! ### Time families -/

/-- **Joint continuity of the jets for time families.** For a family of `C^k` functions on the
closed half-space whose `m`-th derivatives within it, `m ≤ k`, are continuous in time uniformly on
the half-space, the `m`-th derivatives of the weighted reflections are jointly continuous. -/
theorem continuousOn_iteratedFDeriv_weightedReflectionFun (hk : 1 ≤ k) {F : ℝ → ℝ^n → ℝ}
    {I : Set ℝ} (hF : ∀ t ∈ I, ContDiffOn ℝ k (F t) {y | 0 ≤ y i}) {m : ℕ} (hm : m ≤ k)
    (hu : ∀ t ∈ I, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ I, |s - t| < δ → ∀ y : ℝ^n, 0 ≤ y i →
      ‖iteratedFDerivWithin ℝ m (F s) {y | 0 ≤ y i} y -
        iteratedFDerivWithin ℝ m (F t) {y | 0 ≤ y i} y‖ ≤ ε) :
    ContinuousOn (fun p : ℝ × ℝ^n ↦ iteratedFDeriv ℝ m (weightedReflectionFun i k (F p.1)) p.2)
      (I ×ˢ univ) := by
  refine continuousOn_prod_of_uniform_time (g := fun t x ↦
    iteratedFDeriv ℝ m (weightedReflectionFun i k (F t)) x)
    (fun t ht ↦ (contDiff_weightedReflectionFun i hk (hF t ht)).continuous_iteratedFDeriv
      (by exact_mod_cast hm)) fun t ht ε hε ↦ ?_
  have hR : 0 < reflectionBound k m := zero_lt_one.trans_le (one_le_reflectionBound k m)
  obtain ⟨δ, hδ, hδε⟩ := hu t ht (ε / reflectionBound k m) (div_pos hε hR)
  refine ⟨δ, hδ, fun s hs hst x ↦ ?_⟩
  rw [dist_eq_norm]
  calc ‖iteratedFDeriv ℝ m (weightedReflectionFun i k (F s)) x -
        iteratedFDeriv ℝ m (weightedReflectionFun i k (F t)) x‖
      ≤ reflectionBound k m * (ε / reflectionBound k m) :=
        norm_iteratedFDeriv_weightedReflectionFun_sub_le i hk (hF s hs) (hF t ht) hm
          (hδε s hs hst) x
    _ = ε := by field_simp

/-! ### Supports -/

/-- **Supports.** If the source vanishes on the closed half-space outside the closed ball of
radius `R`, its weighted reflection vanishes outside that ball. -/
theorem weightedReflectionFun_eq_zero_of_norm_lt {R : ℝ}
    (hR : ∀ y : ℝ^n, 0 ≤ y i → R < ‖y‖ → f y = 0) {x : ℝ^n} (hx : R < ‖x‖) :
    weightedReflectionFun i k f x = 0 := by
  by_cases hxi : x i < 0
  · rw [weightedReflectionFun_of_neg i k f hxi]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [hR _ (le_of_lt (normalDilation_reflectionNode_pos i k j hxi))
      (hx.trans_le (norm_le_norm_normalDilation_reflectionNode i k j x)), mul_zero]
  · rw [weightedReflectionFun_eq_of_nonneg i k f x (not_lt.mp hxi)]
    exact hR x (not_lt.mp hxi) hx

/-- The weighted reflection of a function vanishing on the closed half-space outside a ball has
compact support. -/
theorem hasCompactSupport_weightedReflectionFun {R : ℝ}
    (hR : ∀ y : ℝ^n, 0 ≤ y i → R < ‖y‖ → f y = 0) :
    HasCompactSupport (weightedReflectionFun i k f) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℝ^n) R) fun x hx ↦
    weightedReflectionFun_eq_zero_of_norm_lt i hR (by simpa using hx)

/-! ### Reflections in the other coordinates -/

/-- The reflection dilations commute with reflections in the other coordinates. -/
theorem normalDilation_coordinateReflection {l : Fin n} (hl : l ≠ i) (a : ℝ) (x : ℝ^n) :
    normalDilation i a (coordinateReflection l x) =
      coordinateReflection l (normalDilation i a x) := by
  ext m
  by_cases hm : m = l
  · subst hm
    simp [coordinateReflection_apply_same, normalDilation_apply, hl]
  · by_cases hmi : m = i
    · subst hmi
      simp [coordinateReflection_apply_of_ne _ _ hm, normalDilation_apply]
    · simp [coordinateReflection_apply_of_ne _ _ hm, normalDilation_apply, hmi]

/-- **Parity.** If the source has the parity `ε` under the reflection in a coordinate `l ≠ i` on the
closed half-space, its weighted reflection has the same parity everywhere. -/
theorem weightedReflectionFun_comp_coordinateReflection {l : Fin n} (hl : l ≠ i) {ε : ℝ}
    (hpar : ∀ y : ℝ^n, 0 ≤ y i → f (coordinateReflection l y) = ε * f y) (x : ℝ^n) :
    weightedReflectionFun i k f (coordinateReflection l x) =
      ε * weightedReflectionFun i k f x := by
  have hxi : coordinateReflection l x i = x i := coordinateReflection_apply_of_ne _ _ hl.symm x
  by_cases hneg : x i < 0
  · rw [weightedReflectionFun_of_neg i k f (by rwa [hxi]), weightedReflectionFun_of_neg i k f hneg,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [normalDilation_coordinateReflection i hl,
      hpar _ (le_of_lt (normalDilation_reflectionNode_pos i k j hneg))]
    ring
  · rw [weightedReflectionFun_eq_of_nonneg i k f _ (by rw [hxi]; exact not_lt.mp hneg),
      weightedReflectionFun_eq_of_nonneg i k f x (not_lt.mp hneg)]
    exact hpar x (not_lt.mp hneg)


/-! ### Reflections of order above the regularity -/



/-- A `C^k` derivative on the closed half-space gives a global `C^{k+1}` weighted reflection of
every order `K ≥ k + 1`. -/
theorem contDiff_succ_weightedReflectionFun_of_le (i : Fin n) {k K : ℕ} (hkK : k + 1 ≤ K)
    {f : ℝ^n → ℝ} {f' : ℝ^n → (ℝ^n →L[ℝ] ℝ)} (hf' : ContDiff ℝ k f')
    (hderiv : ∀ x, 0 ≤ x i → HasFDerivWithinAt f (f' x) {y | 0 ≤ y i} x) :
    ContDiff ℝ (k + 1) (weightedReflectionFun i K f) := by
  classical
  let D : ℝ^n → (ℝ^n →L[ℝ] ℝ) := fun x ↦
    if x i < 0 then
      ∑ j, reflectionCoeff K j •
        ((f' (normalDilation i (reflectionNode K j) x)).comp
          (normalDilation i (reflectionNode K j)))
    else f' x
  have hcoord (l : Fin n) : ContDiff ℝ k (fun x ↦ D x (EuclideanSpace.single l 1)) := by
    have heq : (fun x ↦ D x (EuclideanSpace.single l 1)) = fun x ↦
        if x i < 0 then
          reflectedJet i K (if l = i then 1 else 0) (fun y ↦ f' y (EuclideanSpace.single l 1)) x
        else f' x (EuclideanSpace.single l 1) := by
      funext x
      by_cases hx : x i < 0
      · simp only [D, hx, ↓reduceIte, sum_apply,
          smul_apply, ContinuousLinearMap.comp_apply, normalDilation_single,
          map_smul, smul_eq_mul, reflectedJet]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        split_ifs <;> simp [mul_assoc]
      · simp only [D, hx, ↓reduceIte]
    rw [heq]
    exact contDiff_piecewise_reflectedJet i K _ (by split_ifs <;> omega)
      (hf'.clm_apply contDiff_const)
  have hD : ContDiff ℝ k D := by
    have heq : D = fun x ↦ ∑ l, D x (EuclideanSpace.single l 1) • EuclideanSpace.proj l := by
      funext x
      ext v
      have hv : v = ∑ l, v l • EuclideanSpace.single l 1 := by
        ext l
        simp [Pi.single_apply]
      conv_lhs => rw [hv]
      simp only [map_sum, map_smul, sum_apply,
        smul_apply, smul_eq_mul, EuclideanSpace.coe_proj]
      exact Finset.sum_congr rfl fun l _ ↦ mul_comm _ _
    rw [heq]
    exact ContDiff.sum fun l _ ↦ (hcoord l).smul_const _
  exact contDiff_succ_iff_hasFDerivAt.mpr
    ⟨D, hD, hasFDerivAt_weightedReflectionFun i (by omega) hderiv⟩

/-- A function of class `C^k`, `k ≥ 1`, within the closed half-space has a global `C^k` weighted
reflection of every order `K ≥ k`. -/
theorem contDiff_weightedReflectionFun_of_le (i : Fin n) {k K : ℕ} (hk : 1 ≤ k) (hkK : k ≤ K)
    {f : ℝ^n → ℝ} (hf : ContDiffOn ℝ k f {x | 0 ≤ x i}) :
    ContDiff ℝ k (weightedReflectionFun i K f) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  let D := fderivWithin ℝ f {x : ℝ^n | 0 ≤ x i}
  have hD : ContDiffOn ℝ m D {x | 0 ≤ x i} :=
    hf.fderivWithin (uniqueDiffOn_coordinateHalfSpace i) (by push_cast; exact le_rfl)
  have hext (j : Fin n) : ∃ G : ℝ^n → ℝ, ContDiff ℝ m G ∧
      EqOn G (fun x ↦ D x (EuclideanSpace.single j 1)) {x | 0 ≤ x i} :=
    exists_contDiff_extension_halfSpace i m (hD.clm_apply contDiffOn_const)
  choose G hG hGeq using hext
  let L : ℝ^n → (ℝ^n →L[ℝ] ℝ) := fun x ↦ ∑ j, G j x • EuclideanSpace.proj j
  have hL : ContDiff ℝ m L := ContDiff.sum (fun j _ ↦ (hG j).smul_const _)
  have hLeq (x : ℝ^n) (hx : 0 ≤ x i) : L x = D x := by
    ext v
    have hv : v = ∑ j, v j • EuclideanSpace.single j 1 := by
      ext j
      simp [Pi.single_apply]
    change (∑ j, G j x • EuclideanSpace.proj j) v = D x v
    conv_rhs => rw [hv]
    simp only [sum_apply, smul_apply,
      EuclideanSpace.coe_proj, map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl (fun j _ ↦ by rw [hGeq j hx, mul_comm])
  have h := contDiff_succ_weightedReflectionFun_of_le i hkK hL (fun x hx ↦ by
    rw [hLeq x hx]
    exact (hf.differentiableOn (by simp) x hx).hasFDerivWithinAt)
  exact_mod_cast h


end PDE.Analysis
