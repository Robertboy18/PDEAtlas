/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.ClassicalExtension

/-!
# Derivatives and bounds of the weighted reflection across a coordinate hyperplane

For `f : ℝ^n → ℝ` of class `C^k` within the closed half-space `H = {x | 0 ≤ x i}`, the weighted
reflection `weightedReflectionFun i k f` (equal to `f` on `H` and to `∑ⱼ cⱼ f (dⱼ x)` below it,
where `dⱼ` multiplies the coordinate `i` by `-(j + 1)`) is a global `C^k` function. Its first and
second derivatives are the derivatives of `f` within `H` on `H`, and weighted sums of these
derivatives at the dilated points `dⱼ x` below `H`. Consequently the extension is linear in `f` and
its derivatives up to order `m ≤ min k 2` are bounded by `reflectionBound k m` times the
corresponding bounds of `f` on `H`, also for differences of two functions.

For a family `f t` depending on a time `t ∈ I` whose derivatives within `H` are continuous in `t`
uniformly on `H`, the extensions and their first two derivatives are jointly continuous on
`I × ℝ^n`. This is the form in which a field given on a closed half-space enters the flow theory
of time-dependent fields on the whole space.

## Main results

* `contDiff_weightedReflectionFun`: `C^k` within `H` gives a global `C^k` extension.
* `fderiv_weightedReflectionFun_of_nonneg`, `fderiv_weightedReflectionFun_of_neg`: the first
  derivative.
* `fderiv_fderiv_weightedReflectionFun_of_nonneg`,
  `fderiv_fderiv_weightedReflectionFun_apply_of_neg`: the second derivative.
* `abs_weightedReflectionFun_sub_le`, `norm_fderiv_weightedReflectionFun_sub_le`,
  `norm_fderiv_fderiv_weightedReflectionFun_sub_le`: bounds by `reflectionBound k m`.
* `continuousOn_weightedReflectionFun`, `continuousOn_fderiv_weightedReflectionFun`,
  `continuousOn_fderiv_fderiv_weightedReflectionFun`: joint continuity for time families.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology
open SobolevSpace.GraphSpace.HigherOrderReflection

namespace PDE.Analysis

variable {n : ℕ}

/-! ### The constants -/

/-- The constant `∑ⱼ |cⱼ| (j + 1) ^ m` bounding the `m`-th derivative of the weighted reflection of
order `k` by the `m`-th derivative of the source on the closed half-space. -/
def reflectionBound (k m : ℕ) : ℝ :=
  ∑ j : Fin (k + 1), |reflectionCoeff k j| * ((j : ℝ) + 1) ^ m

/-- The constant `reflectionBound k m` is at least `1`. -/
theorem one_le_reflectionBound (k m : ℕ) : 1 ≤ reflectionBound k m := by
  calc (1 : ℝ) = |∑ j, reflectionCoeff k j| := by rw [sum_reflectionCoeff, abs_one]
    _ ≤ ∑ j, |reflectionCoeff k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ reflectionBound k m := by
      apply Finset.sum_le_sum
      intro j _
      exact le_mul_of_one_le_right (abs_nonneg _) (one_le_pow₀ (by
        linarith [show (0 : ℝ) ≤ (j : ℕ) from Nat.cast_nonneg _]))

/-- The constant `reflectionBound k m` is nonnegative. -/
theorem reflectionBound_nonneg (k m : ℕ) : 0 ≤ reflectionBound k m :=
  zero_le_one.trans (one_le_reflectionBound k m)

/-- The reflection nodes have absolute value `j + 1`. -/
theorem abs_reflectionNode (k : ℕ) (j : Fin (k + 1)) :
    |reflectionNode k j| = (j : ℝ) + 1 := by
  rw [reflectionNode, abs_neg, abs_of_pos (show (0 : ℝ) < (j : ℕ) + 1 by positivity)]

/-- A normal dilation by a factor of absolute value at least one stretches by at most that
factor. -/
theorem norm_normalDilation_apply_le (i : Fin n) {a : ℝ} (ha : 1 ≤ |a|) (h : ℝ^n) :
    ‖normalDilation i a h‖ ≤ |a| * ‖h‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    ← Real.sqrt_sq (abs_nonneg a), ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l _
  rw [normalDilation_apply, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  split_ifs
  · exact le_rfl
  · rw [abs_one, one_pow]
    nlinarith [abs_nonneg a]

/-- The reflection dilations stretch by at most `j + 1`. -/
theorem norm_normalDilation_reflectionNode_le (i : Fin n) (k : ℕ) (j : Fin (k + 1))
    (h : ℝ^n) : ‖normalDilation i (reflectionNode k j) h‖ ≤ ((j : ℝ) + 1) * ‖h‖ := by
  have h1 : 1 ≤ |reflectionNode k j| := by
    rw [abs_reflectionNode]
    linarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg _]
  simpa only [abs_reflectionNode] using norm_normalDilation_apply_le i h1 h

/-- The reflection dilations map the open lower half-space into the open upper half-space. -/
theorem normalDilation_reflectionNode_pos (i : Fin n) (k : ℕ) (j : Fin (k + 1)) {x : ℝ^n}
    (hx : x i < 0) : 0 < normalDilation i (reflectionNode k j) x i := by
  simp only [normalDilation_apply, ↓reduceIte]
  exact mul_pos_of_neg_of_neg (reflectionNode_neg k j) hx

/-- The closed half-space is a neighbourhood of every dilated point of the open lower
half-space. -/
theorem halfSpace_mem_nhds_normalDilation (i : Fin n) (k : ℕ) (j : Fin (k + 1)) {x : ℝ^n}
    (hx : x i < 0) :
    {y : ℝ^n | 0 ≤ y i} ∈ 𝓝 (normalDilation i (reflectionNode k j) x) := by
  apply mem_of_superset ((isOpen_lt continuous_const (EuclideanSpace.proj i).continuous).mem_nhds
    (normalDilation_reflectionNode_pos i k j hx))
  intro y hy
  exact le_of_lt hy

/-! ### Linearity -/

/-- The weighted reflection of `f - g` is the difference of the weighted reflections of `f`
and `g`. -/
theorem weightedReflectionFun_sub (i : Fin n) (k : ℕ) (f g : ℝ^n → ℝ) :
    weightedReflectionFun i k (f - g) =
      weightedReflectionFun i k f - weightedReflectionFun i k g := by
  funext x
  simp only [weightedReflectionFun, reflectedJet, Pi.sub_apply]
  split_ifs
  · simp only [mul_sub, Finset.sum_sub_distrib]
  · rfl

/-- The weighted reflection of `c • f` is `c` times the weighted reflection of `f`. -/
theorem weightedReflectionFun_smul (i : Fin n) (k : ℕ) (c : ℝ) (f : ℝ^n → ℝ) :
    weightedReflectionFun i k (c • f) = c • weightedReflectionFun i k f := by
  funext x
  simp only [weightedReflectionFun, reflectedJet, Pi.smul_apply, smul_eq_mul]
  split_ifs
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  · rfl

/-- The weighted reflection of the zero function is zero. -/
@[simp]
theorem weightedReflectionFun_zero (i : Fin n) (k : ℕ) :
    weightedReflectionFun i k (0 : ℝ^n → ℝ) = 0 := by
  funext x
  simp [weightedReflectionFun, reflectedJet]

/-- Below the hyperplane the weighted reflection is the weighted sum of the dilated values. -/
theorem weightedReflectionFun_of_neg (i : Fin n) (k : ℕ) (f : ℝ^n → ℝ) {x : ℝ^n}
    (hx : x i < 0) :
    weightedReflectionFun i k f x =
      ∑ j, reflectionCoeff k j * f (normalDilation i (reflectionNode k j) x) := by
  simp [weightedReflectionFun, reflectedJet, hx]

/-- On the hyperplane the weighted reflection takes the values of the source; in particular a
source vanishing on the hyperplane has a reflection vanishing there. -/
theorem weightedReflectionFun_of_eq_zero (i : Fin n) (k : ℕ) (f : ℝ^n → ℝ) {x : ℝ^n}
    (hx : x i = 0) : weightedReflectionFun i k f x = f x :=
  weightedReflectionFun_eq_of_nonneg i k f x hx.ge

/-! ### Regularity -/

/-- A function of class `C^k`, `k ≥ 1`, within the closed half-space has a global `C^k` weighted
reflection. -/
theorem contDiff_weightedReflectionFun (i : Fin n) {k : ℕ} (hk : 1 ≤ k) {f : ℝ^n → ℝ}
    (hf : ContDiffOn ℝ k f {x | 0 ≤ x i}) :
    ContDiff ℝ k (weightedReflectionFun i k f) := by
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
  have h := contDiff_succ_weightedReflectionFun i m hL (fun x hx ↦ by
    rw [hLeq x hx]
    exact (hf.differentiableOn (by simp) x hx).hasFDerivWithinAt)
  exact_mod_cast h

/-- The derivative of the weighted reflection of a `C^k` function, `k ≥ 1`, from its derivative
within the closed half-space. -/
theorem hasFDerivAt_weightedReflectionFun_of_contDiffOn (i : Fin n) {k : ℕ} (hk : 1 ≤ k)
    {f : ℝ^n → ℝ} (hf : ContDiffOn ℝ k f {x | 0 ≤ x i}) (x : ℝ^n) :
    HasFDerivAt (weightedReflectionFun i k f)
      (if x i < 0 then
        ∑ j, reflectionCoeff k j •
          ((fderivWithin ℝ f {y | 0 ≤ y i} (normalDilation i (reflectionNode k j) x)).comp
            (normalDilation i (reflectionNode k j)))
      else fderivWithin ℝ f {y | 0 ≤ y i} x) x :=
  hasFDerivAt_weightedReflectionFun i hk (fun y hy ↦
    (hf.differentiableOn (by exact_mod_cast (show k ≠ 0 by omega)) y hy).hasFDerivWithinAt) x

/-- On the closed half-space the derivative of the weighted reflection is the derivative of the
source within the half-space. -/
theorem fderiv_weightedReflectionFun_of_nonneg (i : Fin n) {k : ℕ} (hk : 1 ≤ k) {f : ℝ^n → ℝ}
    (hf : ContDiffOn ℝ k f {x | 0 ≤ x i}) {x : ℝ^n} (hx : 0 ≤ x i) :
    fderiv ℝ (weightedReflectionFun i k f) x = fderivWithin ℝ f {y | 0 ≤ y i} x := by
  rw [(hasFDerivAt_weightedReflectionFun_of_contDiffOn i hk hf x).fderiv]
  simp [not_lt.mpr hx]

/-- Below the hyperplane the derivative of the weighted reflection is the weighted sum of the
derivatives within the half-space at the dilated points, composed with the dilations. -/
theorem fderiv_weightedReflectionFun_of_neg (i : Fin n) {k : ℕ} (hk : 1 ≤ k) {f : ℝ^n → ℝ}
    (hf : ContDiffOn ℝ k f {x | 0 ≤ x i}) {x : ℝ^n} (hx : x i < 0) :
    fderiv ℝ (weightedReflectionFun i k f) x =
      ∑ j, reflectionCoeff k j •
        ((fderivWithin ℝ f {y | 0 ≤ y i} (normalDilation i (reflectionNode k j) x)).comp
          (normalDilation i (reflectionNode k j))) := by
  rw [(hasFDerivAt_weightedReflectionFun_of_contDiffOn i hk hf x).fderiv]
  simp [hx]

/-- The applied form of `fderiv_weightedReflectionFun_of_neg`. -/
theorem fderiv_weightedReflectionFun_apply_of_neg (i : Fin n) {k : ℕ} (hk : 1 ≤ k)
    {f : ℝ^n → ℝ} (hf : ContDiffOn ℝ k f {x | 0 ≤ x i}) {x : ℝ^n} (hx : x i < 0) (h : ℝ^n) :
    fderiv ℝ (weightedReflectionFun i k f) x h =
      ∑ j, reflectionCoeff k j * fderivWithin ℝ f {y | 0 ≤ y i}
        (normalDilation i (reflectionNode k j) x) (normalDilation i (reflectionNode k j) h) := by
  rw [fderiv_weightedReflectionFun_of_neg i hk hf hx]
  simp only [sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]

/-- On the closed half-space the second derivative of the weighted reflection is the second
derivative of the source within the half-space. -/
theorem fderiv_fderiv_weightedReflectionFun_of_nonneg (i : Fin n) {k : ℕ} (hk : 2 ≤ k)
    {f : ℝ^n → ℝ} (hf : ContDiffOn ℝ k f {x | 0 ≤ x i}) {x : ℝ^n} (hx : 0 ≤ x i) :
    fderiv ℝ (fderiv ℝ (weightedReflectionFun i k f)) x =
      fderivWithin ℝ (fderivWithin ℝ f {y | 0 ≤ y i}) {y | 0 ≤ y i} x := by
  have hE := contDiff_weightedReflectionFun i (by omega) hf
  have hD : Differentiable ℝ (fderiv ℝ (weightedReflectionFun i k f)) :=
    (hE.fderiv_right (m := 1) (by exact_mod_cast hk)).differentiable (by simp)
  rw [← (hD x).fderivWithin (uniqueDiffOn_coordinateHalfSpace i x hx)]
  exact fderivWithin_congr (fun y hy ↦ fderiv_weightedReflectionFun_of_nonneg i (by omega) hf hy)
    (fderiv_weightedReflectionFun_of_nonneg i (by omega) hf hx)

/-- Below the hyperplane the second derivative of the weighted reflection is the weighted sum of
the second derivatives within the half-space at the dilated points, evaluated on the dilated
vectors. -/
theorem fderiv_fderiv_weightedReflectionFun_apply_of_neg (i : Fin n) {k : ℕ} (hk : 2 ≤ k)
    {f : ℝ^n → ℝ} (hf : ContDiffOn ℝ k f {x | 0 ≤ x i}) {x : ℝ^n} (hx : x i < 0)
    (h b : ℝ^n) :
    fderiv ℝ (fderiv ℝ (weightedReflectionFun i k f)) x h b =
      ∑ j, reflectionCoeff k j *
        fderivWithin ℝ (fderivWithin ℝ f {y | 0 ≤ y i}) {y | 0 ≤ y i}
          (normalDilation i (reflectionNode k j) x) (normalDilation i (reflectionNode k j) h)
          (normalDilation i (reflectionNode k j) b) := by
  set S := {y : ℝ^n | 0 ≤ y i} with hS
  set Df := fderivWithin ℝ f S with hDfdef
  set d : Fin (k + 1) → ℝ^n →L[ℝ] ℝ^n := fun j ↦ normalDilation i (reflectionNode k j) with hd
  let G : ℝ^n → ℝ^n →L[ℝ] ℝ := fun y ↦ ∑ j, reflectionCoeff k j • (Df (d j y)).comp (d j)
  have hev : fderiv ℝ (weightedReflectionFun i k f) =ᶠ[𝓝 x] G := by
    filter_upwards [(isOpen_lt (EuclideanSpace.proj i).continuous continuous_const).mem_nhds hx]
      with y hy
    exact fderiv_weightedReflectionFun_of_neg i (by omega) hf hy
  have hDf : ContDiffOn ℝ 1 Df S :=
    hf.fderivWithin (uniqueDiffOn_coordinateHalfSpace i) (by exact_mod_cast hk)
  have hterm (j : Fin (k + 1)) : HasFDerivAt (fun y ↦ (Df (d j y)).comp (d j))
      (((ContinuousLinearMap.compL ℝ (ℝ^n) (ℝ^n) ℝ).flip (d j)).comp
        ((fderivWithin ℝ Df S (d j x)).comp (d j))) x := by
    have h1 : HasFDerivAt Df (fderivWithin ℝ Df S (d j x)) (d j x) :=
      ((hDf.differentiableOn one_ne_zero _
        (le_of_lt (normalDilation_reflectionNode_pos i k j hx))).hasFDerivWithinAt).hasFDerivAt
        (halfSpace_mem_nhds_normalDilation i k j hx)
    have h2 := (h1.comp x (d j).hasFDerivAt).clm_comp (hasFDerivAt_const (d j) x)
    simpa using h2
  have hG : HasFDerivAt G (∑ j, reflectionCoeff k j •
      (((ContinuousLinearMap.compL ℝ (ℝ^n) (ℝ^n) ℝ).flip (d j)).comp
        ((fderivWithin ℝ Df S (d j x)).comp (d j)))) x :=
    HasFDerivAt.fun_sum (fun j _ ↦ (hterm j).fun_const_smul _)
  rw [hev.fderiv_eq, hG.fderiv]
  simp [smul_eq_mul, hd]

/-! ### Bounds -/

/-- The values of the weighted reflections of two functions differ by at most
`reflectionBound k 0` times the bound of their difference on the closed half-space. -/
theorem abs_weightedReflectionFun_sub_le (i : Fin n) (k : ℕ) {f g : ℝ^n → ℝ} {B : ℝ}
    (hB : ∀ y : ℝ^n, 0 ≤ y i → |f y - g y| ≤ B) (x : ℝ^n) :
    |weightedReflectionFun i k f x - weightedReflectionFun i k g x| ≤
      reflectionBound k 0 * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (by simp))
  by_cases hx : x i < 0
  · rw [weightedReflectionFun_of_neg i k f hx, weightedReflectionFun_of_neg i k g hx,
      ← Finset.sum_sub_distrib, reflectionBound, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    rw [← mul_sub, abs_mul, pow_zero, mul_one]
    exact mul_le_mul_of_nonneg_left
      (hB _ (le_of_lt (normalDilation_reflectionNode_pos i k j hx))) (abs_nonneg _)
  · rw [weightedReflectionFun_eq_of_nonneg i k f x (not_lt.mp hx),
      weightedReflectionFun_eq_of_nonneg i k g x (not_lt.mp hx)]
    exact (hB x (not_lt.mp hx)).trans (le_mul_of_one_le_left hB0 (one_le_reflectionBound k 0))

/-- The values of the weighted reflection are bounded by `reflectionBound k 0` times the bound of
the source on the closed half-space. -/
theorem abs_weightedReflectionFun_le (i : Fin n) (k : ℕ) {f : ℝ^n → ℝ} {B : ℝ}
    (hB : ∀ y : ℝ^n, 0 ≤ y i → |f y| ≤ B) (x : ℝ^n) :
    |weightedReflectionFun i k f x| ≤ reflectionBound k 0 * B := by
  simpa using abs_weightedReflectionFun_sub_le i k (g := 0) (fun y hy ↦ by simpa using hB y hy) x

/-- The derivatives of the weighted reflections of two `C^k` functions differ by at most
`reflectionBound k 1` times the bound of the difference of their derivatives within the closed
half-space. -/
theorem norm_fderiv_weightedReflectionFun_sub_le (i : Fin n) {k : ℕ} (hk : 1 ≤ k)
    {f g : ℝ^n → ℝ} (hf : ContDiffOn ℝ k f {x | 0 ≤ x i}) (hg : ContDiffOn ℝ k g {x | 0 ≤ x i})
    {B : ℝ} (hB : ∀ y : ℝ^n, 0 ≤ y i →
      ‖fderivWithin ℝ f {x | 0 ≤ x i} y - fderivWithin ℝ g {x | 0 ≤ x i} y‖ ≤ B) (x : ℝ^n) :
    ‖fderiv ℝ (weightedReflectionFun i k f) x - fderiv ℝ (weightedReflectionFun i k g) x‖ ≤
      reflectionBound k 1 * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by simp))
  by_cases hx : x i < 0
  · apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (reflectionBound_nonneg k 1) hB0)
    intro h
    rw [sub_apply, fderiv_weightedReflectionFun_apply_of_neg i hk hf hx,
      fderiv_weightedReflectionFun_apply_of_neg i hk hg hx, ← Finset.sum_sub_distrib,
      reflectionBound, Finset.sum_mul, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    rw [← mul_sub, ← sub_apply, norm_mul, Real.norm_eq_abs, pow_one]
    have hj := hB _ (le_of_lt (normalDilation_reflectionNode_pos i k j hx))
    have hdil := norm_normalDilation_reflectionNode_le i k j h
    calc |reflectionCoeff k j| * ‖(fderivWithin ℝ f {x | 0 ≤ x i} _ -
            fderivWithin ℝ g {x | 0 ≤ x i} _) (normalDilation i (reflectionNode k j) h)‖
        ≤ |reflectionCoeff k j| * (B * (((j : ℝ) + 1) * ‖h‖)) := by
          gcongr
          exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul hj hdil (norm_nonneg _) hB0)
      _ = |reflectionCoeff k j| * ((j : ℝ) + 1) * B * ‖h‖ := by ring
  · rw [fderiv_weightedReflectionFun_of_nonneg i hk hf (not_lt.mp hx),
      fderiv_weightedReflectionFun_of_nonneg i hk hg (not_lt.mp hx)]
    exact (hB x (not_lt.mp hx)).trans (le_mul_of_one_le_left hB0 (one_le_reflectionBound k 1))

/-- The derivative of the weighted reflection is bounded by `reflectionBound k 1` times the bound
of the derivative within the closed half-space. -/
theorem norm_fderiv_weightedReflectionFun_le (i : Fin n) {k : ℕ} (hk : 1 ≤ k)
    {f : ℝ^n → ℝ} (hf : ContDiffOn ℝ k f {x | 0 ≤ x i}) {B : ℝ}
    (hB : ∀ y : ℝ^n, 0 ≤ y i → ‖fderivWithin ℝ f {x | 0 ≤ x i} y‖ ≤ B) (x : ℝ^n) :
    ‖fderiv ℝ (weightedReflectionFun i k f) x‖ ≤ reflectionBound k 1 * B := by
  have h := norm_fderiv_weightedReflectionFun_sub_le i hk hf (g := fun _ ↦ 0) contDiffOn_const
    (fun y hy ↦ by simpa using hB y hy) x
  have hzero : weightedReflectionFun i k (fun _ : ℝ^n ↦ (0 : ℝ)) = fun _ ↦ 0 :=
    weightedReflectionFun_zero i k
  simpa [hzero] using h

/-- The second derivatives of the weighted reflections of two `C^k` functions, `k ≥ 2`, differ by
at most `reflectionBound k 2` times the bound of the difference of their second derivatives
within the closed half-space. -/
theorem norm_fderiv_fderiv_weightedReflectionFun_sub_le (i : Fin n) {k : ℕ} (hk : 2 ≤ k)
    {f g : ℝ^n → ℝ} (hf : ContDiffOn ℝ k f {x | 0 ≤ x i}) (hg : ContDiffOn ℝ k g {x | 0 ≤ x i})
    {B : ℝ} (hB : ∀ y : ℝ^n, 0 ≤ y i →
      ‖fderivWithin ℝ (fderivWithin ℝ f {x | 0 ≤ x i}) {x | 0 ≤ x i} y -
        fderivWithin ℝ (fderivWithin ℝ g {x | 0 ≤ x i}) {x | 0 ≤ x i} y‖ ≤ B) (x : ℝ^n) :
    ‖fderiv ℝ (fderiv ℝ (weightedReflectionFun i k f)) x -
        fderiv ℝ (fderiv ℝ (weightedReflectionFun i k g)) x‖ ≤ reflectionBound k 2 * B := by
  have hB0 : 0 ≤ B := by
    have h0 := hB 0 (by simp)
    exact le_trans (ContinuousLinearMap.opNorm_nonneg _) h0
  by_cases hx : x i < 0
  · apply ContinuousLinearMap.opNorm_le_bound₂ _ (mul_nonneg (reflectionBound_nonneg k 2) hB0)
    intro h b
    rw [sub_apply, sub_apply,
      fderiv_fderiv_weightedReflectionFun_apply_of_neg i hk hf hx,
      fderiv_fderiv_weightedReflectionFun_apply_of_neg i hk hg hx, ← Finset.sum_sub_distrib,
      reflectionBound, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    rw [← mul_sub, ← sub_apply, ← sub_apply, norm_mul,
      Real.norm_eq_abs]
    have hj := hB _ (le_of_lt (normalDilation_reflectionNode_pos i k j hx))
    have hdh := norm_normalDilation_reflectionNode_le i k j h
    have hdb := norm_normalDilation_reflectionNode_le i k j b
    have hpos : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
    calc |reflectionCoeff k j| * ‖(fderivWithin ℝ (fderivWithin ℝ f {x | 0 ≤ x i})
            {x | 0 ≤ x i} _ - fderivWithin ℝ (fderivWithin ℝ g {x | 0 ≤ x i}) {x | 0 ≤ x i} _)
            (normalDilation i (reflectionNode k j) h) (normalDilation i (reflectionNode k j) b)‖
        ≤ |reflectionCoeff k j| * (B * (((j : ℝ) + 1) * ‖h‖) * (((j : ℝ) + 1) * ‖b‖)) := by
          gcongr
          exact (ContinuousLinearMap.le_opNorm₂ _ _ _).trans
            (mul_le_mul (mul_le_mul hj hdh (norm_nonneg _) hB0) hdb (norm_nonneg _)
              (mul_nonneg hB0 (mul_nonneg hpos (norm_nonneg _))))
      _ = |reflectionCoeff k j| * ((j : ℝ) + 1) ^ 2 * B * ‖h‖ * ‖b‖ := by ring
  · rw [fderiv_fderiv_weightedReflectionFun_of_nonneg i hk hf (not_lt.mp hx),
      fderiv_fderiv_weightedReflectionFun_of_nonneg i hk hg (not_lt.mp hx)]
    exact (hB x (not_lt.mp hx)).trans (le_mul_of_one_le_left hB0 (one_le_reflectionBound k 2))

/-- The second derivative of the weighted reflection is bounded by `reflectionBound k 2` times the
bound of the second derivative within the closed half-space. -/
theorem norm_fderiv_fderiv_weightedReflectionFun_le (i : Fin n) {k : ℕ} (hk : 2 ≤ k)
    {f : ℝ^n → ℝ} (hf : ContDiffOn ℝ k f {x | 0 ≤ x i}) {B : ℝ}
    (hB : ∀ y : ℝ^n, 0 ≤ y i →
      ‖fderivWithin ℝ (fderivWithin ℝ f {x | 0 ≤ x i}) {x | 0 ≤ x i} y‖ ≤ B) (x : ℝ^n) :
    ‖fderiv ℝ (fderiv ℝ (weightedReflectionFun i k f)) x‖ ≤ reflectionBound k 2 * B := by
  have h := norm_fderiv_fderiv_weightedReflectionFun_sub_le i hk hf (g := fun _ ↦ 0)
    contDiffOn_const (fun y hy ↦ by simpa using hB y hy) x
  have hzero : weightedReflectionFun i k (fun _ : ℝ^n ↦ (0 : ℝ)) = fun _ ↦ 0 :=
    weightedReflectionFun_zero i k
  simpa [hzero] using h

/-! ### Time families -/

/-- A family of continuous functions that is continuous in time uniformly in space is jointly
continuous. -/
theorem continuousOn_prod_of_uniform_time {X Y : Type*} [TopologicalSpace X]
    [PseudoMetricSpace Y] {g : ℝ → X → Y} {I : Set ℝ} (hx : ∀ t ∈ I, Continuous (g t))
    (ht : ∀ t ∈ I, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ I, |s - t| < δ → ∀ x, dist (g s x) (g t x) ≤ ε) :
    ContinuousOn (fun p : ℝ × X ↦ g p.1 p.2) (I ×ˢ univ) := by
  rintro ⟨t₀, x₀⟩ ⟨ht₀, -⟩
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδt⟩ := ht t₀ ht₀ (ε / 2) (half_pos hε)
  have hcont : ∀ᶠ x in 𝓝 x₀, dist (g t₀ x) (g t₀ x₀) < ε / 2 :=
    Metric.tendsto_nhds.mp ((hx t₀ ht₀).tendsto x₀) _ (half_pos hε)
  have htime : ∀ᶠ p : ℝ × X in 𝓝 (t₀, x₀), |p.1 - t₀| < δ := by
    have hc : Continuous fun p : ℝ × X ↦ |p.1 - t₀| := (continuous_fst.sub continuous_const).abs
    have h0 : |(t₀, x₀).1 - t₀| < δ := by simpa using hδ
    exact hc.continuousAt.eventually (gt_mem_nhds h0)
  have hspace : ∀ᶠ p : ℝ × X in 𝓝 (t₀, x₀), dist (g t₀ p.2) (g t₀ x₀) < ε / 2 :=
    (continuous_snd.tendsto (t₀, x₀)).eventually hcont
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds htime, nhdsWithin_le_nhds hspace]
    with p hp h1 h2
  calc dist (g p.1 p.2) (g t₀ x₀) ≤ dist (g p.1 p.2) (g t₀ p.2) + dist (g t₀ p.2) (g t₀ x₀) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (hδt p.1 hp.1 h1 p.2) h2
    _ = ε := add_halves ε

/-- Weighted reflections of a family of `C^k` functions, `k ≥ 1`, that is continuous in time
uniformly on the closed half-space are jointly continuous in time and space. -/
theorem continuousOn_weightedReflectionFun (i : Fin n) {k : ℕ} (hk : 1 ≤ k)
    {f : ℝ → ℝ^n → ℝ} {I : Set ℝ} (hf : ∀ t ∈ I, ContDiffOn ℝ k (f t) {x | 0 ≤ x i})
    (h0 : ∀ t ∈ I, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ I, |s - t| < δ → ∀ y : ℝ^n, 0 ≤ y i →
      |f s y - f t y| ≤ ε) :
    ContinuousOn (fun p : ℝ × ℝ^n ↦ weightedReflectionFun i k (f p.1) p.2) (I ×ˢ univ) := by
  apply continuousOn_prod_of_uniform_time
    (g := fun t ↦ weightedReflectionFun i k (f t))
    (fun t ht ↦ (contDiff_weightedReflectionFun i hk (hf t ht)).continuous)
  intro t ht ε hε
  have hc := one_le_reflectionBound k 0
  obtain ⟨δ, hδ, hδt⟩ := h0 t ht (ε / reflectionBound k 0) (div_pos hε (by linarith))
  refine ⟨δ, hδ, fun s hs hst x ↦ ?_⟩
  rw [Real.dist_eq]
  calc _ ≤ reflectionBound k 0 * (ε / reflectionBound k 0) :=
        abs_weightedReflectionFun_sub_le i k (hδt s hs hst) x
    _ = ε := mul_div_cancel₀ ε (by linarith)

/-- Derivatives of the weighted reflections of a family of `C^k` functions, `k ≥ 1`, whose
derivatives within the closed half-space are continuous in time uniformly on the half-space are
jointly continuous in time and space. -/
theorem continuousOn_fderiv_weightedReflectionFun (i : Fin n) {k : ℕ} (hk : 1 ≤ k)
    {f : ℝ → ℝ^n → ℝ} {I : Set ℝ} (hf : ∀ t ∈ I, ContDiffOn ℝ k (f t) {x | 0 ≤ x i})
    (h1 : ∀ t ∈ I, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ I, |s - t| < δ → ∀ y : ℝ^n, 0 ≤ y i →
      ‖fderivWithin ℝ (f s) {x | 0 ≤ x i} y - fderivWithin ℝ (f t) {x | 0 ≤ x i} y‖ ≤ ε) :
    ContinuousOn (fun p : ℝ × ℝ^n ↦ fderiv ℝ (weightedReflectionFun i k (f p.1)) p.2)
      (I ×ˢ univ) := by
  apply continuousOn_prod_of_uniform_time
    (g := fun t ↦ fderiv ℝ (weightedReflectionFun i k (f t)))
    (fun t ht ↦ (contDiff_weightedReflectionFun i hk (hf t ht)).continuous_fderiv
      (by exact_mod_cast (show k ≠ 0 by omega)))
  intro t ht ε hε
  have hc := one_le_reflectionBound k 1
  obtain ⟨δ, hδ, hδt⟩ := h1 t ht (ε / reflectionBound k 1) (div_pos hε (by linarith))
  refine ⟨δ, hδ, fun s hs hst x ↦ ?_⟩
  rw [dist_eq_norm]
  calc _ ≤ reflectionBound k 1 * (ε / reflectionBound k 1) :=
        norm_fderiv_weightedReflectionFun_sub_le i hk (hf s hs) (hf t ht) (hδt s hs hst) x
    _ = ε := mul_div_cancel₀ ε (by linarith)

/-- Second derivatives of the weighted reflections of a family of `C^k` functions, `k ≥ 2`, whose
second derivatives within the closed half-space are continuous in time uniformly on the
half-space are jointly continuous in time and space. -/
theorem continuousOn_fderiv_fderiv_weightedReflectionFun (i : Fin n) {k : ℕ} (hk : 2 ≤ k)
    {f : ℝ → ℝ^n → ℝ} {I : Set ℝ} (hf : ∀ t ∈ I, ContDiffOn ℝ k (f t) {x | 0 ≤ x i})
    (h2 : ∀ t ∈ I, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ I, |s - t| < δ → ∀ y : ℝ^n, 0 ≤ y i →
      ‖fderivWithin ℝ (fderivWithin ℝ (f s) {x | 0 ≤ x i}) {x | 0 ≤ x i} y -
        fderivWithin ℝ (fderivWithin ℝ (f t) {x | 0 ≤ x i}) {x | 0 ≤ x i} y‖ ≤ ε) :
    ContinuousOn
      (fun p : ℝ × ℝ^n ↦ fderiv ℝ (fderiv ℝ (weightedReflectionFun i k (f p.1))) p.2)
      (I ×ˢ univ) := by
  apply continuousOn_prod_of_uniform_time
    (g := fun t ↦ fderiv ℝ (fderiv ℝ (weightedReflectionFun i k (f t))))
    (fun t ht ↦ ((contDiff_weightedReflectionFun i (by omega) (hf t ht)).fderiv_right (m := 1)
      (by exact_mod_cast hk)).continuous_fderiv one_ne_zero)
  intro t ht ε hε
  have hc := one_le_reflectionBound k 2
  obtain ⟨δ, hδ, hδt⟩ := h2 t ht (ε / reflectionBound k 2) (div_pos hε (by linarith))
  refine ⟨δ, hδ, fun s hs hst x ↦ ?_⟩
  rw [dist_eq_norm (fderiv ℝ (fderiv ℝ (weightedReflectionFun i k (f s))) x)
    (fderiv ℝ (fderiv ℝ (weightedReflectionFun i k (f t))) x)]
  calc _ ≤ reflectionBound k 2 * (ε / reflectionBound k 2) :=
        norm_fderiv_fderiv_weightedReflectionFun_sub_le i hk (hf s hs) (hf t ht)
          (hδt s hs hst) x
    _ = ε := mul_div_cancel₀ ε (by linarith)

end PDE.Analysis
