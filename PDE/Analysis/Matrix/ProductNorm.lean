/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Matrix.Order
public import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# Norms of finite-rank products from a congruence certificate

For a positive semidefinite `G` and a symmetric `H`, the largest eigenvalue of
`G^{1/2} H G^{1/2}` is at most `g ≥ 0` as soon as `g G - G H G` is positive semidefinite. This
congruence needs no square root, inverse or factor of `G`, and `G` may be singular: if
`v = G^{1/2} u + z` with `G^{1/2} z = 0`, then `G^{1/2} v = G u` and
`(G u)ᵀ H (G u) ≤ g uᵀ G u = g |G^{1/2} u|² ≤ g |v|²`.

The same argument in an inner product space bounds a finite-rank map: if `G` is the Gram matrix
of `q` and `a j = ⟪q j, f⟫`, then `a = G c` for the coefficients `c` of the orthogonal projection
of `f` onto the span of `q`, so `aᵀ H a ≤ g ‖f‖²`. With `H` the Gram matrix of `φ` this is the
operator bound `‖∑ j, ⟪q j, f⟫ • φ j‖² ≤ g ‖f‖²`.

The same bound follows from the dual side: if `∑ j, ∑ k, ⟪φ j, w⟫ G j k ⟪φ k, w⟫ ≤ g ‖w‖²` for
every `w`, test `‖v‖²` for `v = ∑ j, ⟪q j, f⟫ • φ j` against `w = v`. For values `φ j ∈ ℝ^n` the
hypothesis is `g I - Φ G Φᵀ ⪰ 0` for the `n × n` matrix with columns `φ j`, which for `n = 3`
is one Sylvester test per point.
-/

@[expose] public section

open Finset Matrix
open scoped Matrix MatrixOrder RealInnerProductSpace

namespace PDE.Analysis.Matrix

variable {ι : Type*} [Fintype ι]

/-- The congruence form of the certificate gives the matrix inequality on the range of `G`:
`(G c)ᵀ H (G c) ≤ g cᵀ G c`. -/
theorem mulVec_dotProduct_le_of_sandwich {G H : _root_.Matrix ι ι ℝ} {g : ℝ}
    (hG : G.IsSymm)
    (hcert : ∀ c : ι → ℝ, 0 ≤ ∑ i, ∑ j, (g * G i j - (G * H * G) i j) * c i * c j)
    (c : ι → ℝ) : (G *ᵥ c) ⬝ᵥ (H *ᵥ (G *ᵥ c)) ≤ g * (c ⬝ᵥ (G *ᵥ c)) := by
  have h := hcert c
  have hsplit : ∑ i, ∑ j, (g * G i j - (G * H * G) i j) * c i * c j =
      g * (c ⬝ᵥ (G *ᵥ c)) - c ⬝ᵥ ((G * H * G) *ᵥ c) := by
    simp only [dotProduct, mulVec, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
  have hGt : Gᵀ = G := hG
  have hleft : c ⬝ᵥ ((G * H * G) *ᵥ c) = (G *ᵥ c) ⬝ᵥ (H *ᵥ (G *ᵥ c)) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, hGt]
  linarith [hsplit, hleft]

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Finite-rank product bound.** If `G` is the Gram matrix of `q`, `g ≥ 0` and
`g G - G H G` is positive semidefinite, then the analysis coefficients `a j = ⟪q j, f⟫`
satisfy `aᵀ H a ≤ g ‖f‖²` for every `f`. The matrix `H` need not be positive. -/
theorem dotProduct_mulVec_inner_le_of_sandwich (q : ι → E) {H : _root_.Matrix ι ι ℝ} {g : ℝ}
    (hg : 0 ≤ g)
    (hcert : ∀ c : ι → ℝ,
      0 ≤ ∑ i, ∑ j, (g * gram ℝ q i j - (gram ℝ q * H * gram ℝ q) i j) * c i * c j)
    (f : E) :
    (fun j ↦ ⟪q j, f⟫) ⬝ᵥ (H *ᵥ fun j ↦ ⟪q j, f⟫) ≤ g * ‖f‖ ^ 2 := by
  classical
  set K : Submodule ℝ E := Submodule.span ℝ (Set.range q)
  have : FiniteDimensional ℝ K := FiniteDimensional.span_of_finite ℝ (Set.finite_range q)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (K.starProjection_apply_mem f)
  set p : E := ∑ i, c i • q i
  have horth : ∀ j, ⟪q j, f - p⟫ = 0 := by
    intro j
    have hmem := K.sub_starProjection_mem_orthogonal f
    rw [← hc] at hmem
    exact (Submodule.mem_orthogonal K _).mp hmem (q j) (Submodule.subset_span ⟨j, rfl⟩)
  have hG : (gram ℝ q).IsSymm := by
    ext i j
    simp [gram_apply, real_inner_comm]
  have ha : (fun j ↦ ⟪q j, f⟫) = gram ℝ q *ᵥ c := by
    funext j
    have h := horth j
    rw [inner_sub_right, sub_eq_zero] at h
    rw [h]
    simp only [p, inner_sum, real_inner_smul_right, mulVec, dotProduct, gram_apply]
    exact sum_congr rfl fun i _ ↦ mul_comm _ _
  have hp : c ⬝ᵥ (gram ℝ q *ᵥ c) = ‖p‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simpa using star_dotProduct_gram_mulVec (𝕜 := ℝ) q c c
  have hpf : ‖p‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    have hpp : ⟪p, f - p⟫ = 0 := by
      simp only [p, sum_inner, real_inner_smul_left, horth, mul_zero, sum_const_zero]
    have hnorm : ‖f‖ ^ 2 = ‖p‖ ^ 2 + ‖f - p‖ ^ 2 := by
      have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p (f - p) hpp
      rw [add_sub_cancel] at this
      simpa only [sq] using this
    nlinarith [sq_nonneg ‖f - p‖]
  rw [ha]
  calc (gram ℝ q *ᵥ c) ⬝ᵥ (H *ᵥ (gram ℝ q *ᵥ c)) ≤ g * (c ⬝ᵥ (gram ℝ q *ᵥ c)) :=
        mulVec_dotProduct_le_of_sandwich hG hcert c
    _ ≤ g * ‖f‖ ^ 2 := by rw [hp]; exact mul_le_mul_of_nonneg_left hpf hg

/-- **Norm of a finite-rank map.** If `g G_q - G_q G_φ G_q` is positive semidefinite, where
`G_q` and `G_φ` are the Gram matrices of `q` and `φ`, then
`‖∑ j, ⟪q j, f⟫ • φ j‖² ≤ g ‖f‖²`, that is, the map has norm at most `√g`. The constant is
`λmax(G_q^{1/2} G_φ G_q^{1/2})` at best. -/
theorem norm_sum_inner_smul_sq_le_of_sandwich (q : ι → E) (φ : ι → F) {g : ℝ} (hg : 0 ≤ g)
    (hcert : ∀ c : ι → ℝ,
      0 ≤ ∑ i, ∑ j, (g * gram ℝ q i j - (gram ℝ q * gram ℝ φ * gram ℝ q) i j) * c i * c j)
    (f : E) : ‖∑ j, ⟪q j, f⟫ • φ j‖ ^ 2 ≤ g * ‖f‖ ^ 2 := by
  have h := dotProduct_mulVec_inner_le_of_sandwich q hg hcert f
  have hid := star_dotProduct_gram_mulVec (𝕜 := ℝ) φ (fun j ↦ ⟪q j, f⟫) (fun j ↦ ⟪q j, f⟫)
  rw [star_trivial, real_inner_self_eq_norm_sq] at hid
  rwa [hid] at h

/-- **Largest eigenvalue of `G^{1/2} H G^{1/2}`.** For `G ⪰ 0`, a symmetric `H` and `g ≥ 0`,
positive semidefiniteness of `g G - G H G` gives the Loewner bound
`G^{1/2} H G^{1/2} ≤ g • 1`, that is `λmax(G^{1/2} H G^{1/2}) ≤ g`. -/
theorem productNorm_le [DecidableEq ι] {G H : _root_.Matrix ι ι ℝ} {g : ℝ} (hg : 0 ≤ g)
    (hG : G.PosSemidef) (hH : H.IsHermitian)
    (hcert : ∀ c : ι → ℝ, 0 ≤ ∑ i, ∑ j, (g * G i j - (G * H * G) i j) * c i * c j) :
    CFC.sqrt G * H * CFC.sqrt G ≤ g • (1 : _root_.Matrix ι ι ℝ) := by
  set S := CFC.sqrt G
  have hS : S.PosSemidef := (CFC.sqrt_nonneg G).posSemidef
  have hSS : S * S = G := CFC.sqrt_mul_sqrt_self G hG.nonneg
  have hSt : Sᵀ = S := by simpa using hS.isHermitian.eq
  -- the columns of `S` in Euclidean space have Gram matrix `G`
  set q : ι → EuclideanSpace ℝ ι := fun j ↦ WithLp.toLp 2 fun i ↦ S i j
  have hgram : gram ℝ q = G := by
    ext i j
    rw [gram_apply, EuclideanSpace.inner_toLp_toLp, ← hSS, mul_apply]
    simp only [dotProduct, star_trivial]
    refine sum_congr rfl fun k _ ↦ ?_
    have : S k i = S i k := by simpa using congrFun (congrFun hSt i) k
    rw [this, mul_comm]
  have hquad : ∀ v : ι → ℝ, (S *ᵥ v) ⬝ᵥ (H *ᵥ (S *ᵥ v)) ≤ g * (v ⬝ᵥ v) := by
    intro v
    have h := dotProduct_mulVec_inner_le_of_sandwich q (H := H) hg (by rw [hgram]; exact hcert)
      (WithLp.toLp 2 v)
    have hcoord : (fun j ↦ ⟪q j, WithLp.toLp 2 v⟫) = S *ᵥ v := by
      funext j
      rw [EuclideanSpace.inner_toLp_toLp]
      simp only [dotProduct, star_trivial, mulVec]
      refine sum_congr rfl fun k _ ↦ ?_
      have : S k j = S j k := by simpa using congrFun (congrFun hSt j) k
      rw [this, mul_comm]
    have hnorm : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ ^ 2 = v ⬝ᵥ v := by
      rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial]
    rwa [hcoord, hnorm] at h
  rw [Matrix.le_iff]
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v ↦ ?_
  · have hSH : S.IsHermitian := hS.isHermitian
    unfold _root_.Matrix.IsHermitian
    rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, conjTranspose_mul,
      conjTranspose_mul, hSH.eq, hH.eq, star_trivial, mul_assoc]
  · rw [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul,
      smul_eq_mul, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec v S, ← mulVec_transpose,
      hSt]
    linarith [hquad v]

/-- **Finite-rank map, dual form.** If `w ↦ ∑ j, ∑ k, ⟪φ j, w⟫ G j k ⟪φ k, w⟫` is at most
`g ‖w‖²`, where `G` is the Gram matrix of `q`, then `‖∑ j, ⟪q j, f⟫ • φ j‖² ≤ g ‖f‖²`. -/
theorem norm_sum_inner_smul_sq_le_of_dual (q : ι → E) (φ : ι → F) {g : ℝ} (hg : 0 ≤ g)
    (h : ∀ w : F, ∑ j, ∑ k, gram ℝ q j k * ⟪φ j, w⟫ * ⟪φ k, w⟫ ≤ g * ‖w‖ ^ 2) (f : E) :
    ‖∑ j, ⟪q j, f⟫ • φ j‖ ^ 2 ≤ g * ‖f‖ ^ 2 := by
  set v : F := ∑ j, ⟪q j, f⟫ • φ j
  set u : E := ∑ j, ⟪φ j, v⟫ • q j
  have hvv : ‖v‖ ^ 2 = ⟪u, f⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [v, u, sum_inner, real_inner_smul_left]
    exact sum_congr rfl fun j _ ↦ by ring
  have huu : ‖u‖ ^ 2 ≤ g * ‖v‖ ^ 2 := by
    have hid := star_dotProduct_gram_mulVec (𝕜 := ℝ) q (fun j ↦ ⟪φ j, v⟫) (fun j ↦ ⟪φ j, v⟫)
    rw [star_trivial, real_inner_self_eq_norm_sq] at hid
    rw [← hid]
    refine le_of_eq_of_le ?_ (h v)
    simp only [dotProduct, mulVec, mul_sum]
    exact sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ by ring
  have hcs : ‖v‖ ^ 2 * ‖v‖ ^ 2 ≤ g * ‖v‖ ^ 2 * ‖f‖ ^ 2 := by
    have h1 : ⟪u, f⟫ ≤ ‖u‖ * ‖f‖ := real_inner_le_norm u f
    have h2 : (‖u‖ * ‖f‖) ^ 2 ≤ g * ‖v‖ ^ 2 * ‖f‖ ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right huu (sq_nonneg _)
    have h3 : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
    calc ‖v‖ ^ 2 * ‖v‖ ^ 2 = ⟪u, f⟫ ^ 2 := by rw [← hvv]; ring
      _ ≤ (‖u‖ * ‖f‖) ^ 2 := by
          rw [← hvv] at h1 ⊢
          exact pow_le_pow_left₀ h3 h1 2
      _ ≤ _ := h2
  by_cases hv : ‖v‖ ^ 2 = 0
  · rw [hv]
    exact mul_nonneg hg (sq_nonneg _)
  · have hpos : 0 < ‖v‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hv)
    nlinarith

/-- **Pointwise finite-rank bound in `ℝ^n`.** If `g I - Φ G Φᵀ` is positive semidefinite, where
`Φ` has the columns `φ j` and `G` is the Gram matrix of `q`, then
`‖∑ j, ⟪q j, f⟫ • φ j‖² ≤ g ‖f‖²`. For `n = 3` the hypothesis is one Sylvester test. -/
theorem norm_sum_inner_smul_sq_le_of_pointwise {n : ℕ} (q : ι → E) (φ : ι → ℝ^n) {g : ℝ}
    (hg : 0 ≤ g)
    (h : ∀ w : Fin n → ℝ, 0 ≤ ∑ a, ∑ b, ((if a = b then g else 0) -
      ∑ j, ∑ k, φ j a * gram ℝ q j k * φ k b) * w a * w b) (f : E) :
    ‖∑ j, ⟪q j, f⟫ • φ j‖ ^ 2 ≤ g * ‖f‖ ^ 2 := by
  classical
  refine norm_sum_inner_smul_sq_le_of_dual q φ hg (fun w ↦ ?_) f
  have hw := h (fun a ↦ w a)
  have hnorm : ‖w‖ ^ 2 = ∑ a, w a ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.real_inner_eq_sum]
    exact sum_congr rfl fun a _ ↦ by ring
  have hdiag : ∀ a, ∑ b, (if a = b then g else 0) * w a * w b = g * w a ^ 2 := by
    intro a
    rw [← Fintype.sum_ite_eq a (fun b ↦ g * w b ^ 2)]
    refine sum_congr rfl fun b _ ↦ ?_
    by_cases hab : a = b
    · subst hab
      simp only [ite_true]
      ring
    · simp [hab]
  set G := gram ℝ q
  set T : Fin n → Fin n → ι → ι → ℝ := fun a b j k ↦ φ j a * G j k * φ k b * w a * w b
  have hform : ∑ j, ∑ k, G j k * ⟪φ j, w⟫ * ⟪φ k, w⟫ =
      ∑ a, ∑ b, (∑ j, ∑ k, φ j a * G j k * φ k b) * w a * w b := by
    calc ∑ j, ∑ k, G j k * ⟪φ j, w⟫ * ⟪φ k, w⟫ = ∑ j, ∑ k, ∑ a, ∑ b, T a b j k := by
          refine sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ ?_
          rw [EuclideanSpace.real_inner_eq_sum, EuclideanSpace.real_inner_eq_sum, mul_assoc,
            sum_mul_sum, mul_sum]
          exact sum_congr rfl fun a _ ↦ by
            rw [mul_sum]; exact sum_congr rfl fun b _ ↦ by simp only [T]; ring
      _ = ∑ j, ∑ a, ∑ k, ∑ b, T a b j k := sum_congr rfl fun j _ ↦ sum_comm
      _ = ∑ a, ∑ j, ∑ k, ∑ b, T a b j k := sum_comm
      _ = ∑ a, ∑ j, ∑ b, ∑ k, T a b j k :=
          sum_congr rfl fun a _ ↦ sum_congr rfl fun j _ ↦ sum_comm
      _ = ∑ a, ∑ b, ∑ j, ∑ k, T a b j k := sum_congr rfl fun a _ ↦ sum_comm
      _ = _ := by
          refine sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ ?_
          simp only [T, sum_mul]
  have hsplit : ∑ a, ∑ b, ((if a = b then g else 0) -
      ∑ j, ∑ k, φ j a * G j k * φ k b) * w a * w b =
      g * ∑ a, w a ^ 2 - ∑ a, ∑ b, (∑ j, ∑ k, φ j a * G j k * φ k b) * w a * w b := by
    simp only [sub_mul, sum_sub_distrib, hdiag, mul_sum]
  rw [hform, hnorm]
  linarith

end PDE.Analysis.Matrix
