/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.FDeriv.PartialDeriv.HigherNorm
public import PDE.FDeriv.Calculus
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Square norms of higher derivatives in coordinates

## Motivation

How large is the `k`-th derivative of a function on `ℝ^n`, measured as a sum of squares, the
form that the maximum principle can use?

## The idea

The maximum principle is applied to squares of derivatives: an elliptic operator `L` gives
`L(z²) = 2 q(∇z) + 2 z Lz`, where `q(∇z)` is a positive quadratic form in the next derivatives.
A sum of squares of smooth functions is smooth, so it can be differentiated twice.
`iteratedCoordinateNormSq k f x` is the sum of `‖∂_w f(x)‖²` over all coordinate words `w` of
length `k`, and `iteratedCoordinateNorm k f x` is its square root. For a scalar function that
is `C^k` at the point this is the Frobenius norm of the `k`-th derivative in the standard
coordinates. That fact is not proved here; the module compares the norm with the operator norm
of `iteratedFDeriv` in both directions. Like
`iteratedCoordinateNormSum` it is recorded recursively: the square norm of order `k + 1` of `f`
is the sum over `i` of the square norms of order `k` of `∂ᵢ f`. Most statements below are
inductions on `k` along this recursion; the inequalities used are Minkowski's inequality in
`ℝ^n` and the Cauchy–Schwarz inequality.

## Main results

* `iteratedCoordinateNorm_add_le`, `iteratedCoordinateNorm_sum_le`: the triangle inequality, for
  all functions that are `C^k` at the point.
* `iteratedCoordinateNorm_clm_comp_le`: a continuous linear map `T` after `f` costs at most `‖T‖`.
* `norm_iteratedFDeriv_le_sqrt_mul_iteratedCoordinateNorm`: `‖Dᵏf(x)‖ ≤ √(n^k)` times the
  coordinate norm, for all `f` that are `C^k` at `x`.
* `iteratedCoordinateNormSq_le_pow_mul_norm_iteratedFDeriv_sq`: the coordinate square norm is at
  most `n^k ‖Dᵏf(x)‖²`.
* `ContDiffAt.iteratedCoordinateNormSq`: for values in an inner product space the square norm of
  order `k` of a `C^{k+m}` function is `C^m`.

## Relations

`iteratedCoordinateNorm_le_iteratedCoordinateNormSum` and
`iteratedCoordinateNormSum_le_sqrt_mul_iteratedCoordinateNorm` compare the square norm with
`iteratedCoordinateNormSum` (an `ℓ²` sum against an `ℓ¹` sum over the same words), and the bound
on `‖Dᵏf(x)‖` is `norm_iteratedFDeriv_le_iteratedCoordinateNormSum` followed by this comparison.
The Leibniz and chain rules for these norms are in `PDE.FDeriv.PartialDeriv.HigherNormSq.Leibniz`
and `PDE.FDeriv.PartialDeriv.HigherNormSq.Composition`.

## What stays open

Nothing here uses the symmetry of higher derivatives, so the words are not grouped into
multi-indices and no multinomial weights appear.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace PDE

/-- The sum of the squared norms of all coordinate words of length `k`, recorded recursively like
`iteratedCoordinateNormSum`. For a scalar function that is `C^k` at the point it is the squared
Frobenius norm of the `k`-th derivative in the standard coordinates. -/
def iteratedCoordinateNormSq : ℕ → (ℝ^n → F) → ℝ^n → ℝ
  | 0, f, x => ‖f x‖ ^ 2
  | k + 1, f, x => ∑ i : Fin n, iteratedCoordinateNormSq k (∂[i] f) x

/-- The coordinate square norm `iteratedCoordinateNormSq k f x` is nonnegative. -/
theorem iteratedCoordinateNormSq_nonneg (k : ℕ) (f : ℝ^n → F) (x : ℝ^n) :
    0 ≤ iteratedCoordinateNormSq k f x := by
  induction k generalizing f with
  | zero => exact sq_nonneg _
  | succ k ih => exact Finset.sum_nonneg fun i _ ↦ ih (∂[i] f)

/-- The `ℓ²` norm of all coordinate words of length `k`: the square root of
`iteratedCoordinateNormSq k f x`. -/
def iteratedCoordinateNorm (k : ℕ) (f : ℝ^n → F) (x : ℝ^n) : ℝ :=
  √(iteratedCoordinateNormSq k f x)

/-- The coordinate norm `iteratedCoordinateNorm k f x` is nonnegative. -/
theorem iteratedCoordinateNorm_nonneg (k : ℕ) (f : ℝ^n → F) (x : ℝ^n) :
    0 ≤ iteratedCoordinateNorm k f x :=
  Real.sqrt_nonneg _

/-- The square of the coordinate norm is the coordinate square norm. -/
theorem iteratedCoordinateNorm_sq (k : ℕ) (f : ℝ^n → F) (x : ℝ^n) :
    iteratedCoordinateNorm k f x ^ 2 = iteratedCoordinateNormSq k f x :=
  Real.sq_sqrt (iteratedCoordinateNormSq_nonneg k f x)

/-- At order zero the coordinate norm is the norm of the value. -/
@[simp]
theorem iteratedCoordinateNorm_zero (f : ℝ^n → F) (x : ℝ^n) :
    iteratedCoordinateNorm 0 f x = ‖f x‖ :=
  Real.sqrt_sq (norm_nonneg _)

/-- The recursion for the coordinate norm: order `k + 1` of `f` is the `ℓ²` norm over `i` of
order `k` of `∂ᵢ f`. -/
theorem iteratedCoordinateNorm_succ (k : ℕ) (f : ℝ^n → F) (x : ℝ^n) :
    iteratedCoordinateNorm (k + 1) f x =
      √(∑ i : Fin n, iteratedCoordinateNorm k (∂[i] f) x ^ 2) := by
  simp only [iteratedCoordinateNorm, iteratedCoordinateNormSq,
    Real.sq_sqrt (iteratedCoordinateNormSq_nonneg k _ x)]

/-- One coordinate derivative costs one order: the norm of order `k` of `∂ᵢ f` is at most the
norm of order `k + 1` of `f`. -/
theorem iteratedCoordinateNorm_partialDeriv_le (k : ℕ) (f : ℝ^n → F) (x : ℝ^n) (i : Fin n) :
    iteratedCoordinateNorm k (∂[i] f) x ≤ iteratedCoordinateNorm (k + 1) f x :=
  Real.sqrt_le_sqrt <| Finset.single_le_sum
    (f := fun j ↦ iteratedCoordinateNormSq k (∂[j] f) x)
    (fun _ _ ↦ iteratedCoordinateNormSq_nonneg k _ x) (Finset.mem_univ i)

/-- The coordinate square norm at `x` depends only on the germ of the function at `x`. -/
theorem _root_.Filter.EventuallyEq.iteratedCoordinateNormSq {f g : ℝ^n → F} {x : ℝ^n}
    (h : f =ᶠ[𝓝 x] g) (k : ℕ) :
    PDE.iteratedCoordinateNormSq k f x = PDE.iteratedCoordinateNormSq k g x := by
  induction k generalizing f g with
  | zero => simp only [PDE.iteratedCoordinateNormSq, h.self_of_nhds]
  | succ k ih => exact Finset.sum_congr rfl fun i _ ↦ ih (h.partialDeriv i)

/-- The coordinate norm at `x` depends only on the germ of the function at `x`. -/
theorem _root_.Filter.EventuallyEq.iteratedCoordinateNorm {f g : ℝ^n → F} {x : ℝ^n}
    (h : f =ᶠ[𝓝 x] g) (k : ℕ) :
    PDE.iteratedCoordinateNorm k f x = PDE.iteratedCoordinateNorm k g x := by
  simp only [PDE.iteratedCoordinateNorm, h.iteratedCoordinateNormSq k]

/-- A linear isometric equivalence after `f` does not change the coordinate square norm. No
differentiability is needed. -/
theorem iteratedCoordinateNormSq_linearIsometryEquiv_comp {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (e : F ≃ₗᵢ[ℝ] G) (k : ℕ) (f : ℝ^n → F) (x : ℝ^n) :
    iteratedCoordinateNormSq k (fun y ↦ e (f y)) x = iteratedCoordinateNormSq k f x := by
  induction k generalizing f with
  | zero => simp [iteratedCoordinateNormSq]
  | succ k ih =>
    have hd (i : Fin n) : ∂[i] (fun y ↦ e (f y)) = fun y ↦ e ((∂[i] f) y) := by
      funext y
      have h := e.toContinuousLinearEquiv.comp_fderiv (f := f) (x := y)
      exact congrArg (fun L : ℝ^n →L[ℝ] G ↦ L (EuclideanSpace.single i (1 : ℝ))) h
    simp only [iteratedCoordinateNormSq, hd, ih]

/-- **Minkowski's inequality with weights.** If `w i ≤ ∑ l ∈ s, c l * u l i` for every `i`, with
all terms nonnegative, then the `ℓ²` norm of `w` is at most `∑ l ∈ s, c l * ‖u l‖_{ℓ²}`. -/
theorem sqrt_sum_sq_le_sum_mul_sqrt {ι κ : Type*} [Fintype ι] (s : Finset κ) {w : ι → ℝ}
    {c : κ → ℝ} {u : κ → ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hc : ∀ l ∈ s, 0 ≤ c l)
    (h : ∀ i, w i ≤ ∑ l ∈ s, c l * u l i) :
    √(∑ i, w i ^ 2) ≤ ∑ l ∈ s, c l * √(∑ i, u l i ^ 2) := by
  calc √(∑ i, w i ^ 2) ≤ √(∑ i, (∑ l ∈ s, c l * u l i) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (hw i) (h i) 2)
    _ = ‖∑ l ∈ s, c l • (WithLp.toLp 2 (u l) : EuclideanSpace ℝ ι)‖ := by
        rw [EuclideanSpace.norm_eq]
        congr 1
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp [Real.norm_eq_abs, sq_abs]
    _ ≤ ∑ l ∈ s, ‖c l • (WithLp.toLp 2 (u l) : EuclideanSpace ℝ ι)‖ := norm_sum_le _ _
    _ = ∑ l ∈ s, c l * √(∑ i, u l i ^ 2) := by
        refine Finset.sum_congr rfl fun l hl ↦ ?_
        rw [norm_smul, Real.norm_of_nonneg (hc l hl), EuclideanSpace.norm_eq]
        simp [Real.norm_eq_abs, sq_abs]

/-- A function that is `C¹` at a point is differentiable near it, over every nontrivially
normed field. -/
theorem _root_.ContDiffAt.eventually_differentiableAt {𝕜 E G : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] {f : E → G} {x : E} {m : WithTop ℕ∞} (hf : ContDiffAt 𝕜 m f x)
    (hm : 1 ≤ m) : ∀ᶠ y in 𝓝 x, DifferentiableAt 𝕜 f y :=
  ((hf.of_le hm).eventually (by simp)).mono fun _ hy ↦ hy.differentiableAt one_ne_zero

/-- **Triangle inequality** for the coordinate norm of order `k`, for all functions that are
`C^k` at the point. -/
theorem iteratedCoordinateNorm_add_le (k : ℕ) {f g : ℝ^n → F} {x : ℝ^n}
    (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x) :
    iteratedCoordinateNorm k (fun y ↦ f y + g y) x ≤
      iteratedCoordinateNorm k f x + iteratedCoordinateNorm k g x := by
  induction k generalizing f g with
  | zero => simpa using norm_add_le (f x) (g x)
  | succ k ih =>
    have hk : (1 : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast Nat.le_add_left 1 k
    -- near `x` the derivative of the sum is the sum of the derivatives
    have hsum (i : Fin n) : ∂[i] (fun y ↦ f y + g y) =ᶠ[𝓝 x]
        fun y ↦ (∂[i] f) y + (∂[i] g) y := by
      filter_upwards [hf.eventually_differentiableAt hk, hg.eventually_differentiableAt hk]
        with y hfy hgy using partialDeriv_add hfy hgy
    have hstep (i : Fin n) : iteratedCoordinateNorm k (∂[i] (fun y ↦ f y + g y)) x ≤
        ∑ l : Fin 2, (1 : ℝ) * ![iteratedCoordinateNorm k (∂[i] f) x,
          iteratedCoordinateNorm k (∂[i] g) x] l := by
      rw [(hsum i).iteratedCoordinateNorm k]
      simpa using ih (hf.partialDeriv i le_rfl) (hg.partialDeriv i le_rfl)
    have h := sqrt_sum_sq_le_sum_mul_sqrt (Finset.univ : Finset (Fin 2))
      (u := fun l i ↦ ![iteratedCoordinateNorm k (∂[i] f) x,
        iteratedCoordinateNorm k (∂[i] g) x] l)
      (fun i ↦ iteratedCoordinateNorm_nonneg k _ x) (fun _ _ ↦ zero_le_one) hstep
    simpa [iteratedCoordinateNorm_succ] using h

/-- A constant has no derivatives: its coordinate square norm of positive order vanishes. -/
theorem iteratedCoordinateNormSq_const {k : ℕ} (hk : k ≠ 0) (c : F) (x : ℝ^n) :
    iteratedCoordinateNormSq k (fun _ : ℝ^n ↦ c) x = 0 := by
  induction k generalizing c with
  | zero => exact absurd rfl hk
  | succ k ih =>
    have hzero (i : Fin n) : ∂[i] (fun _ : ℝ^n ↦ c) = fun _ ↦ (0 : F) :=
      funext fun y ↦ partialDeriv_const c
    simp only [iteratedCoordinateNormSq, hzero]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp [iteratedCoordinateNormSq]
    · exact ih hpos.ne' (0 : F)

/-- A constant has no derivatives: its coordinate norm of positive order vanishes. -/
theorem iteratedCoordinateNorm_const {k : ℕ} (hk : k ≠ 0) (c : F) (x : ℝ^n) :
    iteratedCoordinateNorm k (fun _ : ℝ^n ↦ c) x = 0 := by
  simp [iteratedCoordinateNorm, iteratedCoordinateNormSq_const hk]

/-- Subtracting a function from a constant does not change its coordinate square norm of
positive order. No differentiability is needed. -/
theorem iteratedCoordinateNormSq_const_sub {k : ℕ} (hk : k ≠ 0) (c : F) (f : ℝ^n → F)
    (x : ℝ^n) :
    iteratedCoordinateNormSq k (fun y ↦ c - f y) x = iteratedCoordinateNormSq k f x := by
  have hneg (j : ℕ) (g : ℝ^n → F) :
      iteratedCoordinateNormSq j (fun y ↦ -g y) x = iteratedCoordinateNormSq j g x := by
    induction j generalizing g with
    | zero => simp [iteratedCoordinateNormSq]
    | succ j ih =>
      have hd (i : Fin n) : ∂[i] (fun y ↦ -g y) = fun y ↦ -(∂[i] g) y :=
        funext fun y ↦ partialDeriv_fun_neg
      simp only [iteratedCoordinateNormSq, hd, ih]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hd (i : Fin n) : ∂[i] (fun y ↦ c - f y) = fun y ↦ -(∂[i] f) y := by
    funext y
    simp only [partialDeriv, fderiv_const_sub, neg_apply]
  simp only [iteratedCoordinateNormSq, hd, hneg]

/-- **Triangle inequality** for a finite sum of functions that are `C^k` at the point. -/
theorem iteratedCoordinateNorm_sum_le {ι : Type*} (s : Finset ι) (k : ℕ) {f : ι → ℝ^n → F}
    {x : ℝ^n} (hf : ∀ j ∈ s, ContDiffAt ℝ k (f j) x) :
    iteratedCoordinateNorm k (fun y ↦ ∑ j ∈ s, f j y) x ≤
      ∑ j ∈ s, iteratedCoordinateNorm k (f j) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · simp [iteratedCoordinateNorm_const hk.ne']
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hs : ContDiffAt ℝ k (fun y ↦ ∑ j ∈ s, f j y) x :=
      ContDiffAt.sum fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)
    exact (iteratedCoordinateNorm_add_le k (hf a (Finset.mem_insert_self a s)) hs).trans
      (add_le_add_right (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)) _)

/-- A continuous linear map `T` after `f` costs at most `‖T‖` in the coordinate norm, for all
`f` that are `C^k` at the point. -/
theorem iteratedCoordinateNorm_clm_comp_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : F →L[ℝ] G) (k : ℕ) {f : ℝ^n → F} {x : ℝ^n} (hf : ContDiffAt ℝ k f x) :
    iteratedCoordinateNorm k (fun y ↦ T (f y)) x ≤ ‖T‖ * iteratedCoordinateNorm k f x := by
  induction k generalizing f with
  | zero => simpa using T.le_opNorm (f x)
  | succ k ih =>
    have hk : (1 : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast Nat.le_add_left 1 k
    have hcomp (i : Fin n) : ∂[i] (fun y ↦ T (f y)) =ᶠ[𝓝 x] fun y ↦ T ((∂[i] f) y) := by
      filter_upwards [hf.eventually_differentiableAt hk] with y hy
      simp only [partialDeriv]
      rw [show (fun z ↦ T (f z)) = T ∘ f from rfl, T.fderiv_comp_left hy]
      rfl
    have hstep (i : Fin n) : iteratedCoordinateNorm k (∂[i] (fun y ↦ T (f y))) x ≤
        ∑ _l : Fin 1, ‖T‖ * iteratedCoordinateNorm k (∂[i] f) x := by
      rw [(hcomp i).iteratedCoordinateNorm k]
      simpa using ih (hf.partialDeriv i le_rfl)
    have h := sqrt_sum_sq_le_sum_mul_sqrt (Finset.univ : Finset (Fin 1))
      (c := fun _ ↦ ‖T‖) (u := fun _ i ↦ iteratedCoordinateNorm k (∂[i] f) x)
      (fun i ↦ iteratedCoordinateNorm_nonneg k _ x) (fun _ _ ↦ norm_nonneg T) hstep
    simpa [iteratedCoordinateNorm_succ] using h

/-- The `ℓ²` coordinate norm is at most the `ℓ¹` coordinate norm sum. -/
theorem iteratedCoordinateNorm_le_iteratedCoordinateNormSum (k : ℕ) (f : ℝ^n → F) (x : ℝ^n) :
    iteratedCoordinateNorm k f x ≤ iteratedCoordinateNormSum k f x := by
  induction k generalizing f with
  | zero => simp [iteratedCoordinateNormSum]
  | succ k ih =>
    rw [iteratedCoordinateNorm_succ, iteratedCoordinateNormSum]
    apply Real.sqrt_le_iff.mpr
    refine ⟨Finset.sum_nonneg fun i _ ↦ iteratedCoordinateNormSum_nonneg k _ x, ?_⟩
    calc ∑ i : Fin n, iteratedCoordinateNorm k (∂[i] f) x ^ 2
        ≤ ∑ i : Fin n, iteratedCoordinateNormSum k (∂[i] f) x ^ 2 :=
          Finset.sum_le_sum fun i _ ↦
            pow_le_pow_left₀ (iteratedCoordinateNorm_nonneg k _ x) (ih (∂[i] f)) 2
      _ ≤ (∑ i : Fin n, iteratedCoordinateNormSum k (∂[i] f) x) ^ 2 :=
          Finset.sum_sq_le_sq_sum_of_nonneg fun i _ ↦ iteratedCoordinateNormSum_nonneg k _ x

/-- The `ℓ¹` coordinate norm sum of order `k` is at most `√(n^k)` times the `ℓ²` coordinate
norm: the Cauchy–Schwarz inequality over the `n^k` words. -/
theorem iteratedCoordinateNormSum_le_sqrt_mul_iteratedCoordinateNorm (k : ℕ) (f : ℝ^n → F)
    (x : ℝ^n) :
    iteratedCoordinateNormSum k f x ≤ √((n : ℝ) ^ k) * iteratedCoordinateNorm k f x := by
  induction k generalizing f with
  | zero => simp [iteratedCoordinateNormSum]
  | succ k ih =>
    rw [iteratedCoordinateNormSum, iteratedCoordinateNorm_succ]
    calc ∑ i : Fin n, iteratedCoordinateNormSum k (∂[i] f) x
        ≤ ∑ i : Fin n, √((n : ℝ) ^ k) * iteratedCoordinateNorm k (∂[i] f) x :=
          Finset.sum_le_sum fun i _ ↦ ih (∂[i] f)
      _ = √((n : ℝ) ^ k) * ∑ i : Fin n, 1 * iteratedCoordinateNorm k (∂[i] f) x := by
          simp [Finset.mul_sum]
      _ ≤ √((n : ℝ) ^ k) * (√(∑ _i : Fin n, (1 : ℝ) ^ 2) *
            √(∑ i : Fin n, iteratedCoordinateNorm k (∂[i] f) x ^ 2)) :=
          mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) (Real.sqrt_nonneg _)
      _ = √((n : ℝ) ^ (k + 1)) *
            √(∑ i : Fin n, iteratedCoordinateNorm k (∂[i] f) x ^ 2) := by
          rw [← mul_assoc, ← Real.sqrt_mul (by positivity)]
          simp [pow_succ]

/-- The coordinate norm controls the full derivative: `‖Dᵏf(x)‖ ≤ √(n^k)` times the coordinate
norm, for all `f` that are `C^k` at `x`. -/
theorem norm_iteratedFDeriv_le_sqrt_mul_iteratedCoordinateNorm (k : ℕ) {f : ℝ^n → F} {x : ℝ^n}
    (hf : ContDiffAt ℝ k f x) :
    ‖iteratedFDeriv ℝ k f x‖ ≤ √((n : ℝ) ^ k) * iteratedCoordinateNorm k f x :=
  (norm_iteratedFDeriv_le_iteratedCoordinateNormSum k hf).trans
    (iteratedCoordinateNormSum_le_sqrt_mul_iteratedCoordinateNorm k f x)

/-- The full derivative controls the coordinate square norm: it is at most `n^k ‖Dᵏf(x)‖²`,
for all `f` that are `C^k` at `x`. -/
theorem iteratedCoordinateNormSq_le_pow_mul_norm_iteratedFDeriv_sq (k : ℕ) {f : ℝ^n → F}
    {x : ℝ^n} (hf : ContDiffAt ℝ k f x) :
    iteratedCoordinateNormSq k f x ≤ (n : ℝ) ^ k * ‖iteratedFDeriv ℝ k f x‖ ^ 2 := by
  induction k generalizing f with
  | zero => simp [iteratedCoordinateNormSq, norm_iteratedFDeriv_zero]
  | succ k ih =>
    have hfd : ContDiffAt ℝ k (fderiv ℝ f) x := hf.fderiv_right (by simp)
    have hi (i : Fin n) : iteratedCoordinateNormSq k (∂[i] f) x ≤
        (n : ℝ) ^ k * ‖iteratedFDeriv ℝ (k + 1) f x‖ ^ 2 := by
      refine (ih (hf.partialDeriv i le_rfl)).trans ?_
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) (by positivity)
      have h := norm_iteratedFDeriv_clm_apply_const (c := EuclideanSpace.single i (1 : ℝ))
        hfd le_rfl
      rwa [norm_iteratedFDeriv_fderiv, PiLp.norm_single, norm_one, one_mul] at h
    calc iteratedCoordinateNormSq (k + 1) f x
        ≤ ∑ _i : Fin n, (n : ℝ) ^ k * ‖iteratedFDeriv ℝ (k + 1) f x‖ ^ 2 :=
          Finset.sum_le_sum fun i _ ↦ hi i
      _ = (n : ℝ) ^ (k + 1) * ‖iteratedFDeriv ℝ (k + 1) f x‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_succ]
          ring

/-- For values in an inner product space the coordinate square norm of order `k` of a function
that is `C^{k+m}` at a point is `C^m` there. -/
theorem _root_.ContDiffAt.iteratedCoordinateNormSq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (k : ℕ) {m : ℕ} {f : ℝ^n → H} {x : ℝ^n}
    (hf : ContDiffAt ℝ (k + m : ℕ) f x) :
    ContDiffAt ℝ m (iteratedCoordinateNormSq k f) x := by
  induction k generalizing f with
  | zero =>
    have h : ContDiffAt ℝ m f x := hf.of_le (by simp)
    exact h.norm_sq ℝ
  | succ k ih =>
    have hi (i : Fin n) : ContDiffAt ℝ (k + m : ℕ) (∂[i] f) x :=
      hf.partialDeriv i (by exact_mod_cast (by omega : k + m + 1 ≤ k + 1 + m))
    exact ContDiffAt.sum fun i _ ↦ ih (hi i)

end PDE
