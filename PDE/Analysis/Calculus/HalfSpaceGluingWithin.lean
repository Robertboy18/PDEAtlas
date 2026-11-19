/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.HalfSpaceReflection
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Gluing across a hyperplane within a set, and reflection with a time parameter

Two functions with derivatives within a set `S`, whose values and derivatives agree on the
hyperplane `φ = 0` of a continuous linear functional `φ`, glue to a function `C¹` within `S`: at
points of the hyperplane the difference of the two functions vanishes to first order, so cutting
it off on one side keeps the derivative zero. No unique derivatives are needed for the gluing.

The weighted reflection across `x i = 0` of the slices of a field `F` on `ℝⁿ × ℝ` that is `C¹`
within `univ ×ˢ I` is again `C¹` within `univ ×ˢ I`: the reflected branch is a combination of
compositions of `F` with linear maps preserving `univ ×ˢ I`, and its values and derivatives agree
with those of `F` on the hyperplane by the moment identities of the reflection coefficients. Here
`I` must have unique derivatives so that the derivative within the set is continuous. The time
derivatives of the slices of the reflection are combinations of those of `F`.

## Main definitions

* `normalDilationProd`: the normal dilation acting on the space variable of `ℝⁿ × ℝ`.

## Main results

* `hasFDerivWithinAt_piecewise_of_eq`: two functions whose values and derivatives within `S`
  agree on the hyperplane glue to a function with a derivative within `S`.
* `contDiffOn_one_piecewise`: with continuous derivatives the glued function is `C¹` within `S`.
* `contDiffOn_one_of_hasFDerivWithinAt`: a derivative within `s` depending continuously on the
  point makes a function `C¹` within `s`.
* `contDiffOn_weightedReflectionFun_slice`: the weighted reflection of order `K ≥ 1` of the slices
  of a field `C¹` within `univ ×ˢ I` is `C¹` within `univ ×ˢ I`.
* `differentiableAt_weightedReflectionFun_slice`: the time slices of the weighted reflection are
  differentiable where those of `F` are.
-/

@[expose] public section

noncomputable section

open Set Filter Asymptotics
open scoped Topology
open SobolevSpace.GraphSpace.HigherOrderReflection

namespace PDE.Analysis

section Gluing

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- A function with a derivative within `s` at every point of `s` that depends continuously on
the point is `C¹` within `s`. -/
theorem contDiffOn_one_of_hasFDerivWithinAt {f : E → G} {f' : E → E →L[ℝ] G} {s : Set E}
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf' : ContinuousOn f' s) :
    ContDiffOn ℝ 1 f s := by
  have h1 : (1 : WithTop ℕ∞) = 0 + 1 := by simp
  rw [h1, contDiffOn_succ_iff_hasFDerivWithinAt (by simp)]
  intro x hx
  refine ⟨s, ?_, by simp, f', hf, contDiffOn_zero.mpr hf'⟩
  rw [insert_eq_of_mem hx]
  exact self_mem_nhdsWithin

variable {S : Set E} (φ : E →L[ℝ] ℝ) {f g : E → G} {f' g' : E → E →L[ℝ] G}

/-- **Gluing of derivatives.** If `f` and `g` have derivatives `f'` and `g'` within `S` and their
values and derivatives agree at the points of `S` on the hyperplane `φ = 0`, then the function
equal to `g` where `φ < 0` and to `f` elsewhere has the glued derivative within `S`. -/
theorem hasFDerivWithinAt_piecewise_of_eq
    (hf : ∀ p ∈ S, HasFDerivWithinAt f (f' p) S p)
    (hg : ∀ p ∈ S, HasFDerivWithinAt g (g' p) S p)
    (heq : ∀ p ∈ S, φ p = 0 → g p = f p) (heq' : ∀ p ∈ S, φ p = 0 → g' p = f' p)
    {p : E} (hp : p ∈ S) :
    HasFDerivWithinAt (fun q ↦ if φ q < 0 then g q else f q)
      (if φ p < 0 then g' p else f' p) S p := by
  rcases lt_trichotomy (φ p) 0 with hneg | hzero | hpos
  · have hU : {q : E | φ q < 0} ∈ 𝓝 p :=
      (isOpen_lt φ.continuous continuous_const).mem_nhds hneg
    simp only [hneg, ↓reduceIte]
    have hev : (fun q ↦ if φ q < 0 then g q else f q) =ᶠ[𝓝[S] p] g := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hU] with q hq
      simp [show φ q < 0 from hq]
    exact (hg p hp).congr_of_eventuallyEq hev (by simp [hneg])
  · set k : E → G := fun q ↦ if φ q < 0 then g q - f q else 0
    have hk0 : k p = 0 := by simp [k, hzero]
    have hgf : HasFDerivWithinAt (fun q ↦ g q - f q) (0 : E →L[ℝ] G) S p := by
      have h := (hg p hp).sub (hf p hp)
      rwa [heq' p hp hzero, sub_self] at h
    have hk : HasFDerivWithinAt k (0 : E →L[ℝ] G) S p := by
      rw [hasFDerivWithinAt_iff_isLittleO] at hgf ⊢
      have hgf0 : g p - f p = 0 := by rw [heq p hp hzero, sub_self]
      simp only [hgf0, sub_zero, zero_apply] at hgf
      simp only [hk0, sub_zero, zero_apply]
      refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 (Eventually.of_forall fun q ↦ ?_)) hgf
      by_cases hq : φ q < 0
      · simp [k, hq]
      · simp [k, hq]
    have hsum := (hf p hp).add hk
    rw [add_zero] at hsum
    simp only [hzero, lt_irrefl, ↓reduceIte]
    refine hsum.congr_of_eventuallyEq (Eventually.of_forall fun q ↦ ?_) ?_
    · by_cases hq : φ q < 0
      · simp [k, hq]
      · simp [k, hq]
    · simp [k, hzero]
  · have hU : {q : E | 0 < φ q} ∈ 𝓝 p :=
      (isOpen_lt continuous_const φ.continuous).mem_nhds hpos
    simp only [not_lt.mpr hpos.le, ↓reduceIte]
    have hev : (fun q ↦ if φ q < 0 then g q else f q) =ᶠ[𝓝[S] p] f := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hU] with q hq
      simp [not_lt.mpr (le_of_lt (show 0 < φ q from hq))]
    exact (hf p hp).congr_of_eventuallyEq hev (by simp [not_lt.mpr hpos.le])

/-- The glued derivative is continuous within `S` when `f'` and `g'` are and they agree on the
hyperplane. -/
theorem continuousOn_piecewise_of_eq (hf' : ContinuousOn f' S) (hg' : ContinuousOn g' S)
    (heq' : ∀ p ∈ S, φ p = 0 → g' p = f' p) :
    ContinuousOn (fun q ↦ if φ q < 0 then g' q else f' q) S := by
  intro p hp
  rcases lt_trichotomy (φ p) 0 with hneg | hzero | hpos
  · have hU : {q : E | φ q < 0} ∈ 𝓝 p :=
      (isOpen_lt φ.continuous continuous_const).mem_nhds hneg
    refine (hg' p hp).congr_of_eventuallyEq ?_ (by simp [hneg])
    filter_upwards [mem_nhdsWithin_of_mem_nhds hU] with q hq
    simp [show φ q < 0 from hq]
  · set k : E → E →L[ℝ] G := fun q ↦ if φ q < 0 then g' q - f' q else 0
    have hk : ContinuousWithinAt k S p := by
      have hd : Tendsto (fun q ↦ g' q - f' q) (𝓝[S] p) (𝓝 0) := by
        have h : Tendsto (fun q ↦ g' q - f' q) (𝓝[S] p) (𝓝 (g' p - f' p)) :=
          (hg' p hp).sub (hf' p hp)
        rwa [heq' p hp hzero, sub_self] at h
      have hk0 : k p = 0 := by simp [k, hzero]
      rw [ContinuousWithinAt, hk0]
      refine squeeze_zero_norm (fun q ↦ ?_) (tendsto_zero_iff_norm_tendsto_zero.mp hd)
      by_cases hq : φ q < 0
      · simp [k, hq]
      · simp only [k, hq, ↓reduceIte, norm_zero]
        exact norm_nonneg _
    refine ((hf' p hp).add hk).congr (fun q _ ↦ ?_) ?_
    · by_cases hq : φ q < 0
      · simp [k, hq]
      · simp [k, hq]
    · simp [k, hzero]
  · have hU : {q : E | 0 < φ q} ∈ 𝓝 p :=
      (isOpen_lt continuous_const φ.continuous).mem_nhds hpos
    refine (hf' p hp).congr_of_eventuallyEq ?_ (by simp [not_lt.mpr hpos.le])
    filter_upwards [mem_nhdsWithin_of_mem_nhds hU] with q hq
    simp [not_lt.mpr (le_of_lt (show 0 < φ q from hq))]

/-- **Gluing across a hyperplane.** Under the hypotheses of `hasFDerivWithinAt_piecewise_of_eq`
with continuous derivatives, the glued function is `C¹` within `S`. -/
theorem contDiffOn_one_piecewise
    (hf : ∀ p ∈ S, HasFDerivWithinAt f (f' p) S p)
    (hg : ∀ p ∈ S, HasFDerivWithinAt g (g' p) S p)
    (hf' : ContinuousOn f' S) (hg' : ContinuousOn g' S)
    (heq : ∀ p ∈ S, φ p = 0 → g p = f p) (heq' : ∀ p ∈ S, φ p = 0 → g' p = f' p) :
    ContDiffOn ℝ 1 (fun q ↦ if φ q < 0 then g q else f q) S :=
  contDiffOn_one_of_hasFDerivWithinAt
    (fun _ hp ↦ hasFDerivWithinAt_piecewise_of_eq φ hf hg heq heq' hp)
    (continuousOn_piecewise_of_eq φ hf' hg' heq')

end Gluing

section Reflection

variable {n : ℕ}

/-- The weighted reflection depends only on the values on the closed half-space. -/
theorem weightedReflectionFun_congr (i : Fin n) (K : ℕ) {f g : ℝ^n → ℝ}
    (h : ∀ y : ℝ^n, 0 ≤ y i → f y = g y) :
    weightedReflectionFun i K f = weightedReflectionFun i K g := by
  funext x
  by_cases hx : x i < 0
  · rw [weightedReflectionFun_of_neg i K f hx, weightedReflectionFun_of_neg i K g hx]
    exact Finset.sum_congr rfl fun j _ ↦ by
      rw [h _ (normalDilation_reflectionNode_pos i K j hx).le]
  · rw [weightedReflectionFun_eq_of_nonneg i K f x (not_lt.mp hx),
      weightedReflectionFun_eq_of_nonneg i K g x (not_lt.mp hx)]
    exact h x (not_lt.mp hx)

/-- The normal dilation acting on the space variable of `ℝⁿ × ℝ`. -/
def normalDilationProd (i : Fin n) (a : ℝ) : ℝ^n × ℝ →L[ℝ] ℝ^n × ℝ :=
  (normalDilation i a).prodMap (ContinuousLinearMap.id ℝ ℝ)

/-- `normalDilationProd i a` dilates the space variable and keeps the time variable. -/
@[simp]
theorem normalDilationProd_apply (i : Fin n) (a : ℝ) (p : ℝ^n × ℝ) :
    normalDilationProd i a p = (normalDilation i a p.1, p.2) := rfl

/-- The weighted combination of the normal dilations of the space variable is the identity. -/
theorem sum_reflectionCoeff_smul_normalDilationProd (i : Fin n) {K : ℕ} (hK : 1 ≤ K) :
    ∑ j, reflectionCoeff K j • normalDilationProd i (reflectionNode K j) =
      ContinuousLinearMap.id ℝ (ℝ^n × ℝ) := by
  have hsum : ∑ j, reflectionCoeff K j = 1 := by
    have h := sum_reflectionCoeff_mul_pow K 0 (Nat.zero_le K)
    simp only [pow_zero, mul_one] at h
    exact h
  have hdil := sum_reflectionCoeff_smul_normalDilation i hK
  refine ContinuousLinearMap.ext fun p ↦ Prod.ext ?_ ?_
  · have h1 := congrArg (fun L : ℝ^n →L[ℝ] ℝ^n ↦ L p.1) hdil
    have h2 : ((∑ j, reflectionCoeff K j • normalDilationProd i (reflectionNode K j)) p).1 =
        ∑ j, reflectionCoeff K j • normalDilation i (reflectionNode K j) p.1 := by
      simp [normalDilationProd, Prod.fst_sum]
    rw [h2]
    simpa using h1
  · have h2 : ((∑ j, reflectionCoeff K j • normalDilationProd i (reflectionNode K j)) p).2 =
        ∑ j, reflectionCoeff K j * p.2 := by
      simp [normalDilationProd, Prod.snd_sum]
    rw [h2, ← Finset.sum_mul, hsum, one_mul]
    rfl

variable {F : ℝ^n × ℝ → ℝ} {I : Set ℝ}

/-- The weighted reflection of the slices as a piecewise function on `ℝⁿ × ℝ`. -/
theorem weightedReflectionFun_slice_eq (i : Fin n) (K : ℕ) (F : ℝ^n × ℝ → ℝ) :
    (fun p : ℝ^n × ℝ ↦ weightedReflectionFun i K (fun y ↦ F (y, p.2)) p.1) =
      fun p ↦ if p.1 i < 0
        then ∑ j, reflectionCoeff K j * F (normalDilationProd i (reflectionNode K j) p)
        else F p := by
  funext p
  by_cases hp : p.1 i < 0
  · rw [weightedReflectionFun_of_neg i K _ hp]
    simp only [hp, ↓reduceIte]
    rfl
  · rw [weightedReflectionFun_eq_of_nonneg i K _ p.1 (not_lt.mp hp)]
    simp only [hp, ↓reduceIte]

/-- **Reflection of a jointly `C¹` field.** If `F` is `C¹` within `univ ×ˢ I` and `I` has unique
derivatives, the weighted reflection of order `K ≥ 1` of its slices across `x i = 0` is `C¹`
within `univ ×ˢ I`. -/
theorem contDiffOn_weightedReflectionFun_slice (i : Fin n) {K : ℕ} (hK : 1 ≤ K)
    (hI : UniqueDiffOn ℝ I) (hF : ContDiffOn ℝ 1 F (univ ×ˢ I)) :
    ContDiffOn ℝ 1 (fun p : ℝ^n × ℝ ↦ weightedReflectionFun i K (fun y ↦ F (y, p.2)) p.1)
      (univ ×ˢ I) := by
  rw [weightedReflectionFun_slice_eq]
  set φ : ℝ^n × ℝ →L[ℝ] ℝ := (EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ (ℝ^n) ℝ)
  have hφ (p : ℝ^n × ℝ) : φ p = p.1 i := rfl
  set S : Set (ℝ^n × ℝ) := univ ×ˢ I
  set L : Fin (K + 1) → ℝ^n × ℝ →L[ℝ] ℝ^n × ℝ := fun j ↦
    normalDilationProd i (reflectionNode K j)
  have hS : UniqueDiffOn ℝ S := UniqueDiffOn.prod uniqueDiffOn_univ hI
  have hmaps (j : Fin (K + 1)) : MapsTo (L j) S S := fun p hp ↦ ⟨mem_univ _, hp.2⟩
  set f' := fderivWithin ℝ F S
  have hf (p : ℝ^n × ℝ) (hp : p ∈ S) : HasFDerivWithinAt F (f' p) S p :=
    ((hF.differentiableOn one_ne_zero) p hp).hasFDerivWithinAt
  have hf' : ContinuousOn f' S := hF.continuousOn_fderivWithin hS le_rfl
  set g' : ℝ^n × ℝ → ℝ^n × ℝ →L[ℝ] ℝ := fun p ↦
    ∑ j, reflectionCoeff K j • (f' (L j p)).comp (L j)
  have hg (p : ℝ^n × ℝ) (hp : p ∈ S) :
      HasFDerivWithinAt (fun q ↦ ∑ j, reflectionCoeff K j * F (L j q)) (g' p) S p := by
    have hterm (j : Fin (K + 1)) :
        HasFDerivWithinAt (fun q ↦ reflectionCoeff K j * F (L j q))
          (reflectionCoeff K j • (f' (L j p)).comp (L j)) S p :=
      ((hf _ (hmaps j hp)).comp p (L j).hasFDerivAt.hasFDerivWithinAt (hmaps j)).const_mul _
    exact HasFDerivWithinAt.fun_sum (u := Finset.univ) fun j _ ↦ hterm j
  have hg' : ContinuousOn g' S := by
    refine continuousOn_finsetSum _ fun j _ ↦ ?_
    exact ((hf'.comp (L j).continuous.continuousOn (hmaps j)).clm_comp
      continuousOn_const).fun_const_smul _
  have hfix (p : ℝ^n × ℝ) (hp0 : p.1 i = 0) (j : Fin (K + 1)) : L j p = p := by
    simp only [L, normalDilationProd_apply, normalDilation_eq_self i _ _ hp0]
  have hpw := contDiffOn_one_piecewise φ hf hg hf' hg' ?_ ?_
  · simpa only [hφ] using hpw
  · intro p _ hp0
    rw [hφ] at hp0
    simp only [hfix p hp0, ← Finset.sum_mul]
    have h := sum_reflectionCoeff_mul_pow K 0 (Nat.zero_le K)
    simp only [pow_zero, mul_one] at h
    rw [h, one_mul]
  · intro p _ hp0
    rw [hφ] at hp0
    simp only [g', hfix p hp0, ← ContinuousLinearMap.comp_smul]
    rw [← ContinuousLinearMap.comp_finsetSum, sum_reflectionCoeff_smul_normalDilationProd i hK,
      ContinuousLinearMap.comp_id]

/-- The time slices of the weighted reflection are differentiable where those of `F` are. -/
theorem differentiableAt_weightedReflectionFun_slice (i : Fin n) (K : ℕ) {x : ℝ^n} {t : ℝ}
    (hF : ∀ y : ℝ^n, DifferentiableAt ℝ (fun s ↦ F (y, s)) t) :
    DifferentiableAt ℝ (fun s ↦ weightedReflectionFun i K (fun y ↦ F (y, s)) x) t := by
  by_cases hx : x i < 0
  · simp only [weightedReflectionFun_of_neg i K _ hx]
    exact DifferentiableAt.fun_sum fun j _ ↦ (hF _).const_mul _
  · simp only [weightedReflectionFun_eq_of_nonneg i K _ x (not_lt.mp hx)]
    exact hF x

end Reflection

end PDE.Analysis
