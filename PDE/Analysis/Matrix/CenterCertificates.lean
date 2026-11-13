/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Algebra.Order.Chebyshev
public import CAS.Analysis.Matrix.QuadraticFormBounds
import Mathlib.Algebra.BigOperators.Field

/-!
# Matrix certificates at a center

A real matrix `S` known only through a center `a` and a bound on `S - a` satisfies an
inequality once a certificate holds at the center with a margin that absorbs the distance. The
distance is measured by `BilinearBound D ε`, `(yᵀ D z)² ≤ ε² |y|² |z|²`, which an entrywise
envelope `|D k l| ≤ t k u l + u k t l` gives with `ε = 2 T U` (`bilinearBound_of_envelope`).

The main theorem concerns the finite-rank capture matrix
`X(S) = K diag(e) - S + (S C) Λ⁻¹ (S C)ᵀ` for coefficient columns `C` and positive weights
`Λ = diag(μ)`. Its form is not linear in `S`, but its quadratic part only helps: for any
approximation `V` of `a C`,
`cᵀ X(S) c ≥ cᵀ (K diag(e) - a + V W Vᵀ) c - (linear terms in S - a and a C - V)` with
`W ≤ Λ⁻¹`, and the linear terms are bounded by the norms of `C` and of `Λ⁻¹ Vᵀ`
(`capture_form_nonneg_of_center`). Three companions transfer the one-sided Gram bound
`Cᵀ (S - δ M) C ⪰ θ Λ` (`gram_form_ge_of_center`), the residual bound
`Λ⁻¹ Rᵀ E⁻¹ R Λ⁻¹ ≤ ε² Cᵀ E C` for `R = S C - E C Λ` (`residual_form_le_of_center`) and an
upper bound for `Λ⁻¹ H Λ⁻¹` (`scaled_form_le_of_center`). Every certificate at the center is a
matrix inequality with explicit rational entries.
-/

@[expose] public section

open Finset Matrix

namespace PDE.Analysis.Matrix

open CAS.Analysis.Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The bilinear form of `D` is bounded by `ε`: `(yᵀ D z)² ≤ ε² |y|² |z|²`. -/
def BilinearBound (D : ι → ι → ℝ) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ∀ y z : ι → ℝ,
    (∑ k, ∑ l, y k * D k l * z l) ^ 2 ≤ ε ^ 2 * (∑ k, y k ^ 2) * ∑ l, z l ^ 2

/-- Cauchy–Schwarz with absolute values. -/
theorem sq_sum_mul_abs_le (t x : ι → ℝ) :
    (∑ k, t k * |x k|) ^ 2 ≤ (∑ k, t k ^ 2) * ∑ k, x k ^ 2 := by
  simpa only [sq_abs] using sum_mul_sq_le_sq_mul_sq univ t fun k ↦ |x k|

/-- Cauchy–Schwarz over index pairs for a bilinear form. -/
theorem sq_sum_sum_mul_le (F : ι → κ → ℝ) (y : ι → ℝ) (z : κ → ℝ) :
    (∑ k, ∑ j, y k * F k j * z j) ^ 2 ≤
      (∑ k, ∑ j, F k j ^ 2) * ((∑ k, y k ^ 2) * ∑ j, z j ^ 2) := by
  have h := sum_mul_sq_le_sq_mul_sq (univ : Finset (ι × κ)) (fun p ↦ F p.1 p.2)
    (fun p ↦ y p.1 * z p.2)
  simp only [← univ_product_univ, sum_product] at h
  have h1 : ∑ k, ∑ j, y k * F k j * z j = ∑ k, ∑ j, F k j * (y k * z j) :=
    sum_congr rfl fun k _ ↦ sum_congr rfl fun j _ ↦ by ring
  have h2 : ∑ k, ∑ j, (y k * z j) ^ 2 = (∑ k, y k ^ 2) * ∑ j, z j ^ 2 := by
    rw [sum_mul_sum]
    exact sum_congr rfl fun k _ ↦ sum_congr rfl fun j _ ↦ by ring
  rw [h1]
  exact h.trans_eq (by rw [h2])

/-- The rows of a matrix with Frobenius norm at most `Φ` map `z` into norm at most `Φ |z|`. -/
theorem sum_sq_sum_mul_le_frobenius (F : ι → κ → ℝ) (z : κ → ℝ) :
    ∑ k, (∑ j, F k j * z j) ^ 2 ≤ (∑ k, ∑ j, F k j ^ 2) * ∑ j, z j ^ 2 := by
  rw [sum_mul]
  exact sum_le_sum fun k _ ↦ sum_mul_sq_le_sq_mul_sq univ (F k) z

/-- A square bound with a common factor gives an absolute bound. -/
theorem abs_le_of_sq_le_mul {q c X : ℝ} (hc : 0 ≤ c) (hX : 0 ≤ X) (h : q ^ 2 ≤ c ^ 2 * X ^ 2) :
    |q| ≤ c * X :=
  abs_le_of_sq_le_sq (h.trans_eq (by ring)) (mul_nonneg hc hX)

namespace BilinearBound

variable {D : ι → ι → ℝ} {ε : ℝ}

theorem nonneg (h : BilinearBound D ε) : 0 ≤ ε := h.1

/-- The bound on vectors with `|y|² ≤ p² X` and `|z|² ≤ q² X`. -/
theorem abs_le (h : BilinearBound D ε) {y z : ι → ℝ} {p q X : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hX : 0 ≤ X) (hy : ∑ k, y k ^ 2 ≤ p ^ 2 * X) (hz : ∑ l, z l ^ 2 ≤ q ^ 2 * X) :
    |∑ k, ∑ l, y k * D k l * z l| ≤ ε * p * q * X := by
  refine abs_le_of_sq_le_mul (by have := h.1; positivity) hX ((h.2 y z).trans ?_)
  calc ε ^ 2 * (∑ k, y k ^ 2) * ∑ l, z l ^ 2 ≤ ε ^ 2 * (p ^ 2 * X) * (q ^ 2 * X) := by gcongr
    _ = (ε * p * q) ^ 2 * X ^ 2 := by ring

/-- The matrix-vector product: `|D z|² ≤ ε² |z|²`. -/
theorem sum_sq_le (h : BilinearBound D ε) (z : ι → ℝ) :
    ∑ k, (∑ l, D k l * z l) ^ 2 ≤ ε ^ 2 * ∑ l, z l ^ 2 := by
  set y : ι → ℝ := fun k ↦ ∑ l, D k l * z l
  have hY : ∑ k, ∑ l, y k * D k l * z l = ∑ k, y k ^ 2 := by
    refine sum_congr rfl fun k _ ↦ ?_
    simp only [mul_assoc, ← mul_sum, sq]
    rfl
  have h2 := h.2 y z
  rw [hY] at h2
  set Y := ∑ k, y k ^ 2
  have hY0 : 0 ≤ Y := sum_nonneg fun k _ ↦ sq_nonneg _
  rcases hY0.eq_or_lt with h0 | hpos
  · rw [← h0]; exact mul_nonneg (sq_nonneg _) (sum_nonneg fun l _ ↦ sq_nonneg _)
  · have : Y * Y ≤ Y * (ε ^ 2 * ∑ l, z l ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left this hpos

/-- Bounds add. -/
theorem add {D₁ D₂ : ι → ι → ℝ} {ε₁ ε₂ : ℝ} (h₁ : BilinearBound D₁ ε₁)
    (h₂ : BilinearBound D₂ ε₂) : BilinearBound (fun k l ↦ D₁ k l + D₂ k l) (ε₁ + ε₂) := by
  refine ⟨add_nonneg h₁.1 h₂.1, fun y z ↦ ?_⟩
  set B₁ := ∑ k, ∑ l, y k * D₁ k l * z l
  set B₂ := ∑ k, ∑ l, y k * D₂ k l * z l
  set W := (∑ k, y k ^ 2) * ∑ l, z l ^ 2
  have hW : 0 ≤ W := mul_nonneg (sum_nonneg fun k _ ↦ sq_nonneg _)
    (sum_nonneg fun l _ ↦ sq_nonneg _)
  have hsum : ∑ k, ∑ l, y k * (D₁ k l + D₂ k l) * z l = B₁ + B₂ := by
    simp only [B₁, B₂, ← sum_add_distrib]
    exact sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ by ring
  have e₁ : B₁ ^ 2 ≤ ε₁ ^ 2 * W := (h₁.2 y z).trans_eq (by ring)
  have e₂ : B₂ ^ 2 ≤ ε₂ ^ 2 * W := (h₂.2 y z).trans_eq (by ring)
  have hprod : B₁ * B₂ ≤ ε₁ * ε₂ * W := by
    have hab : (B₁ * B₂) ^ 2 ≤ (ε₁ * ε₂ * W) ^ 2 := by
      calc (B₁ * B₂) ^ 2 = B₁ ^ 2 * B₂ ^ 2 := by ring
        _ ≤ (ε₁ ^ 2 * W) * (ε₂ ^ 2 * W) :=
          mul_le_mul e₁ e₂ (sq_nonneg _) (mul_nonneg (sq_nonneg _) hW)
        _ = _ := by ring
    exact (abs_le_of_sq_le_sq hab (by have := h₁.1; have := h₂.1; positivity)).trans'
      (le_abs_self _)
  rw [hsum]
  calc (B₁ + B₂) ^ 2 = B₁ ^ 2 + 2 * (B₁ * B₂) + B₂ ^ 2 := by ring
    _ ≤ ε₁ ^ 2 * W + 2 * (ε₁ * ε₂ * W) + ε₂ ^ 2 * W := by linarith
    _ = (ε₁ + ε₂) ^ 2 * (∑ k, y k ^ 2) * ∑ l, z l ^ 2 := by simp only [W]; ring

end BilinearBound

/-- **Envelope bound.** Entries `|D k l| ≤ t k u l + u k t l` with `|t| ≤ T`, `|u| ≤ U` give
the bilinear bound `2 T U`. -/
theorem bilinearBound_of_envelope {D : ι → ι → ℝ} {t u : ι → ℝ} {T U : ℝ}
    (hD : ∀ k l, |D k l| ≤ t k * u l + u k * t l) (ht : ∀ k, 0 ≤ t k) (hu : ∀ k, 0 ≤ u k)
    (hT0 : 0 ≤ T) (hU0 : 0 ≤ U)
    (hT : ∑ k, t k ^ 2 ≤ T ^ 2) (hU : ∑ k, u k ^ 2 ≤ U ^ 2) :
    BilinearBound D (2 * (T * U)) := by
  refine ⟨by positivity, fun y z ↦ ?_⟩
  set Y := ∑ k, y k ^ 2
  set Z := ∑ l, z l ^ 2
  have hY : 0 ≤ Y := sum_nonneg fun k _ ↦ sq_nonneg _
  have hZ : 0 ≤ Z := sum_nonneg fun l _ ↦ sq_nonneg _
  have habs : |∑ k, ∑ l, y k * D k l * z l| ≤
      (∑ k, t k * |y k|) * (∑ l, u l * |z l|) + (∑ k, u k * |y k|) * (∑ l, t l * |z l|) := by
    calc |∑ k, ∑ l, y k * D k l * z l| ≤ ∑ k, ∑ l, |y k| * (t k * u l + u k * t l) * |z l| := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ ↦ ?_)
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l _ ↦ ?_)
          rw [abs_mul, abs_mul]
          gcongr
          exact hD k l
      _ = _ := by
          rw [sum_mul_sum, sum_mul_sum, ← sum_add_distrib]
          refine sum_congr rfl fun k _ ↦ ?_
          rw [← sum_add_distrib]
          exact sum_congr rfl fun l _ ↦ by ring
  have hty := (sq_sum_mul_abs_le t y).trans (mul_le_mul_of_nonneg_right hT hY)
  have huy := (sq_sum_mul_abs_le u y).trans (mul_le_mul_of_nonneg_right hU hY)
  have htz := (sq_sum_mul_abs_le t z).trans (mul_le_mul_of_nonneg_right hT hZ)
  have huz := (sq_sum_mul_abs_le u z).trans (mul_le_mul_of_nonneg_right hU hZ)
  set P₁ := ∑ k, t k * |y k|
  set Q₁ := ∑ l, u l * |z l|
  set P₂ := ∑ k, u k * |y k|
  set Q₂ := ∑ l, t l * |z l|
  have hP₁ : 0 ≤ P₁ := sum_nonneg fun k _ ↦ mul_nonneg (ht k) (abs_nonneg _)
  have hQ₁ : 0 ≤ Q₁ := sum_nonneg fun l _ ↦ mul_nonneg (hu l) (abs_nonneg _)
  have hP₂ : 0 ≤ P₂ := sum_nonneg fun k _ ↦ mul_nonneg (hu k) (abs_nonneg _)
  have hQ₂ : 0 ≤ Q₂ := sum_nonneg fun l _ ↦ mul_nonneg (ht l) (abs_nonneg _)
  have h1 : (P₁ * Q₁) ^ 2 ≤ (T ^ 2 * Y) * (U ^ 2 * Z) := by
    rw [mul_pow]; exact mul_le_mul hty huz (sq_nonneg _) (by positivity)
  have h2 : (P₂ * Q₂) ^ 2 ≤ (U ^ 2 * Y) * (T ^ 2 * Z) := by
    rw [mul_pow]; exact mul_le_mul huy htz (sq_nonneg _) (by positivity)
  have hsq := sq_le_sq' (abs_le.mp habs).1 (abs_le.mp habs).2
  calc (∑ k, ∑ l, y k * D k l * z l) ^ 2 ≤ (P₁ * Q₁ + P₂ * Q₂) ^ 2 := hsq
    _ ≤ 2 * ((P₁ * Q₁) ^ 2 + (P₂ * Q₂) ^ 2) := by nlinarith [sq_nonneg (P₁ * Q₁ - P₂ * Q₂)]
    _ ≤ 2 * ((T ^ 2 * Y) * (U ^ 2 * Z) + (U ^ 2 * Y) * (T ^ 2 * Z)) := by gcongr
    _ = (2 * (T * U)) ^ 2 * Y * Z := by ring

/-- A weighted sum `∑ t k |y k|` with `|t| ≤ T` is at most `T |y|`. -/
theorem sum_mul_abs_le_mul_sqrt {t y : ι → ℝ} {T : ℝ} (hT0 : 0 ≤ T)
    (hT : ∑ k, t k ^ 2 ≤ T ^ 2) :
    ∑ k, t k * |y k| ≤ T * √(∑ k, y k ^ 2) := by
  have hY : 0 ≤ ∑ k, y k ^ 2 := sum_nonneg fun k _ ↦ sq_nonneg _
  refine (le_abs_self _).trans (abs_le_of_sq_le_mul hT0 (Real.sqrt_nonneg _) ?_)
  rw [Real.sq_sqrt hY]
  exact (sq_sum_mul_abs_le t y).trans (mul_le_mul_of_nonneg_right hT hY)

/-- **Sums of envelopes.** Entries bounded by a sum of envelopes
`|D k l| ≤ ∑ r, (t r k u r l + u r k t r l)` with `|t r| ≤ T r`, `|u r| ≤ U r` give the bilinear
bound `∑ r, 2 T r U r`. -/
theorem bilinearBound_of_envelopes {R : Type*} [Fintype R] {D : ι → ι → ℝ} {t u : R → ι → ℝ}
    {T U : R → ℝ} (hD : ∀ k l, |D k l| ≤ ∑ r, (t r k * u r l + u r k * t r l))
    (ht : ∀ r k, 0 ≤ t r k) (hu : ∀ r k, 0 ≤ u r k) (hT0 : ∀ r, 0 ≤ T r) (hU0 : ∀ r, 0 ≤ U r)
    (hT : ∀ r, ∑ k, t r k ^ 2 ≤ T r ^ 2) (hU : ∀ r, ∑ k, u r k ^ 2 ≤ U r ^ 2) :
    BilinearBound D (∑ r, 2 * (T r * U r)) := by
  have hK : 0 ≤ ∑ r, 2 * (T r * U r) :=
    sum_nonneg fun r _ ↦ mul_nonneg zero_le_two (mul_nonneg (hT0 r) (hU0 r))
  refine ⟨hK, fun y z ↦ ?_⟩
  set Y := ∑ k, y k ^ 2
  set Z := ∑ l, z l ^ 2
  have hY : 0 ≤ Y := sum_nonneg fun k _ ↦ sq_nonneg _
  have hZ : 0 ≤ Z := sum_nonneg fun l _ ↦ sq_nonneg _
  have habs : |∑ k, ∑ l, y k * D k l * z l| ≤ ∑ r, ((∑ k, t r k * |y k|) *
      (∑ l, u r l * |z l|) + (∑ k, u r k * |y k|) * (∑ l, t r l * |z l|)) := by
    calc |∑ k, ∑ l, y k * D k l * z l|
        ≤ ∑ k, ∑ l, |y k| * (∑ r, (t r k * u r l + u r k * t r l)) * |z l| := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ ↦ ?_)
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l _ ↦ ?_)
          rw [abs_mul, abs_mul]
          gcongr
          exact hD k l
      _ = ∑ k, ∑ l, ∑ r, |y k| * (t r k * u r l + u r k * t r l) * |z l| := by
          refine sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ ?_
          rw [mul_sum, sum_mul]
      _ = ∑ r, ∑ k, ∑ l, |y k| * (t r k * u r l + u r k * t r l) * |z l| := by
          rw [sum_congr rfl fun k _ ↦ sum_comm, sum_comm]
      _ = _ := by
          refine sum_congr rfl fun r _ ↦ ?_
          rw [sum_mul_sum, sum_mul_sum, ← sum_add_distrib]
          refine sum_congr rfl fun k _ ↦ ?_
          rw [← sum_add_distrib]
          exact sum_congr rfl fun l _ ↦ by ring
  have hbound : ∑ r, ((∑ k, t r k * |y k|) * (∑ l, u r l * |z l|) +
      (∑ k, u r k * |y k|) * (∑ l, t r l * |z l|)) ≤
      (∑ r, 2 * (T r * U r)) * (√Y * √Z) := by
    rw [sum_mul]
    refine sum_le_sum fun r _ ↦ ?_
    have h1 := sum_mul_abs_le_mul_sqrt (y := y) (hT0 r) (hT r)
    have h2 := sum_mul_abs_le_mul_sqrt (y := z) (hU0 r) (hU r)
    have h3 := sum_mul_abs_le_mul_sqrt (y := y) (hU0 r) (hU r)
    have h4 := sum_mul_abs_le_mul_sqrt (y := z) (hT0 r) (hT r)
    have p1 : 0 ≤ ∑ k, t r k * |y k| := sum_nonneg fun k _ ↦ mul_nonneg (ht r k) (abs_nonneg _)
    have p2 : 0 ≤ ∑ l, u r l * |z l| := sum_nonneg fun l _ ↦ mul_nonneg (hu r l) (abs_nonneg _)
    have p3 : 0 ≤ ∑ k, u r k * |y k| := sum_nonneg fun k _ ↦ mul_nonneg (hu r k) (abs_nonneg _)
    have p4 : 0 ≤ ∑ l, t r l * |z l| := sum_nonneg fun l _ ↦ mul_nonneg (ht r l) (abs_nonneg _)
    calc (∑ k, t r k * |y k|) * (∑ l, u r l * |z l|) +
          (∑ k, u r k * |y k|) * (∑ l, t r l * |z l|)
        ≤ (T r * √Y) * (U r * √Z) + (U r * √Y) * (T r * √Z) :=
          add_le_add (mul_le_mul h1 h2 p2 (by have := hT0 r; positivity))
            (mul_le_mul h3 h4 p4 (by have := hU0 r; positivity))
      _ = 2 * (T r * U r) * (√Y * √Z) := by ring
  have hfin := habs.trans hbound
  have hsq := sq_le_sq' (abs_le.mp hfin).1 (abs_le.mp hfin).2
  refine hsq.trans_eq ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt hY, Real.sq_sqrt hZ]
  ring

/-- **Diagonal bound.** A matrix vanishing off the diagonal with diagonal entries at most `τ` in
absolute value has the bilinear bound `τ`. -/
theorem bilinearBound_of_diagonal {D : ι → ι → ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hoff : ∀ k l, k ≠ l → D k l = 0) (hdiag : ∀ k, |D k k| ≤ τ) : BilinearBound D τ := by
  classical
  refine ⟨hτ, fun y z ↦ ?_⟩
  have hsum : ∑ k, ∑ l, y k * D k l * z l = ∑ k, y k * D k k * z k := by
    refine sum_congr rfl fun k _ ↦ ?_
    rw [Finset.sum_eq_single k (fun l _ hl ↦ by rw [hoff k l (Ne.symm hl)]; ring)
      (fun h ↦ absurd (mem_univ k) h)]
  rw [hsum]
  have habs : |∑ k, y k * D k k * z k| ≤ τ * ∑ k, |y k| * |z k| := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun k _ ↦ ?_
    rw [abs_mul, abs_mul]
    calc |y k| * |D k k| * |z k| = |D k k| * (|y k| * |z k|) := by ring
      _ ≤ τ * (|y k| * |z k|) := by gcongr; exact hdiag k
  have hcs : (∑ k, |y k| * |z k|) ^ 2 ≤ (∑ k, y k ^ 2) * ∑ k, z k ^ 2 := by
    have := sum_mul_sq_le_sq_mul_sq univ (fun k ↦ |y k|) fun k ↦ |z k|
    simpa only [sq_abs] using this
  have hsq := sq_le_sq' (abs_le.mp habs).1 (abs_le.mp habs).2
  calc (∑ k, y k * D k k * z k) ^ 2 ≤ (τ * ∑ k, |y k| * |z k|) ^ 2 := hsq
    _ = τ ^ 2 * (∑ k, |y k| * |z k|) ^ 2 := by ring
    _ ≤ τ ^ 2 * ((∑ k, y k ^ 2) * ∑ k, z k ^ 2) := by gcongr
    _ = _ := by ring

/-- A bilinear bound holds for every larger constant. -/
theorem BilinearBound.mono {D : ι → ι → ℝ} {ε ε' : ℝ} (h : BilinearBound D ε) (hε : ε ≤ ε') :
    BilinearBound D ε' := by
  refine ⟨h.1.trans hε, fun y z ↦ (h.2 y z).trans ?_⟩
  have hY : 0 ≤ ∑ k, y k ^ 2 := sum_nonneg fun k _ ↦ sq_nonneg _
  have hZ : 0 ≤ ∑ l, z l ^ 2 := sum_nonneg fun l _ ↦ sq_nonneg _
  have : ε ^ 2 ≤ ε' ^ 2 := pow_le_pow_left₀ h.1 hε 2
  gcongr

/-! ### The capture matrix -/

/-- **Capture matrix from a certificate at the center.** Let `S` be within the bilinear bound
`ε_S` of a center `a`, `V` an approximation of `a C` with `|a C - V|_F ≤ Φ`, `|C v| ≤ ζ |v|`,
`|Λ⁻¹ Vᵀ x| ≤ κ₀ |x|`, `W = diag(w) ≤ Λ⁻¹` and `e ≥ e_lo`. If the center matrix
`K diag(e_lo) - a + V W Vᵀ` has form at least `ν |x|²` with
`ν ≥ ε_S (1 + 2 ζ κ₀) + 2 κ₀ Φ`, then `K diag(e) - S + (S C) Λ⁻¹ (S C)ᵀ` has a nonnegative form. -/
theorem capture_form_nonneg_of_center {S a : ι → ι → ℝ} {e elo : ι → ℝ} {C V : ι → κ → ℝ}
    {μ w : κ → ℝ} {K εS ζ κ₀ Φ ν : ℝ}
    (hS : BilinearBound (fun k l ↦ S k l - a k l) εS) (hK : 0 ≤ K) (he : ∀ k, elo k ≤ e k)
    (hμ : ∀ j, 0 < μ j) (hw : ∀ j, w j ≤ (μ j)⁻¹) (hζ : 0 ≤ ζ)
    (hC : ∀ v : κ → ℝ, ∑ l, (∑ j, C l j * v j) ^ 2 ≤ ζ ^ 2 * ∑ j, v j ^ 2) (hκ₀ : 0 ≤ κ₀)
    (hκ : ∀ x : ι → ℝ, ∑ j, ((∑ k, x k * V k j) / μ j) ^ 2 ≤ κ₀ ^ 2 * ∑ k, x k ^ 2)
    (hΦ0 : 0 ≤ Φ) (hΦ : ∑ k, ∑ j, (∑ l, a k l * C l j - V k j) ^ 2 ≤ Φ ^ 2)
    (hν : εS * (1 + 2 * ζ * κ₀) + 2 * κ₀ * Φ ≤ ν)
    (hcert : ∀ x : ι → ℝ, ν * ∑ k, x k ^ 2 ≤ K * ∑ k, elo k * x k ^ 2 -
      ∑ k, ∑ l, a k l * x k * x l + ∑ j, w j * (∑ k, x k * V k j) ^ 2) (c : ι → ℝ) :
    0 ≤ K * ∑ k, e k * c k ^ 2 - ∑ k, ∑ l, S k l * c k * c l +
      ∑ j, (∑ k, c k * ∑ l, S k l * C l j) ^ 2 / μ j := by
  set X := ∑ k, c k ^ 2 with hXdef
  have hX0 : 0 ≤ X := sum_nonneg fun k _ ↦ sq_nonneg _
  set p : κ → ℝ := fun j ↦ ∑ k, c k * V k j with hp
  set q : κ → ℝ := fun j ↦ ∑ k, c k * ∑ l, S k l * C l j with hq
  set v : κ → ℝ := fun j ↦ p j / μ j with hv
  set z : ι → ℝ := fun l ↦ ∑ j, C l j * v j with hz
  set F : ι → κ → ℝ := fun k j ↦ ∑ l, a k l * C l j - V k j with hF
  have hvX : ∑ j, v j ^ 2 ≤ κ₀ ^ 2 * X := hκ c
  have hzX : ∑ l, z l ^ 2 ≤ (ζ * κ₀) ^ 2 * X := by
    calc ∑ l, z l ^ 2 ≤ ζ ^ 2 * ∑ j, v j ^ 2 := hC v
      _ ≤ ζ ^ 2 * (κ₀ ^ 2 * X) := by gcongr
      _ = (ζ * κ₀) ^ 2 * X := by ring
  have hcX : ∑ k, c k ^ 2 ≤ 1 ^ 2 * X := by rw [one_pow, one_mul]
  -- the diagonal
  have h1 : K * ∑ k, elo k * c k ^ 2 ≤ K * ∑ k, e k * c k ^ 2 := by gcongr with k; exact he k
  -- the linear part
  have h2 : ∑ k, ∑ l, S k l * c k * c l = ∑ k, ∑ l, a k l * c k * c l +
      ∑ k, ∑ l, c k * (S k l - a k l) * c l := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [← sum_add_distrib]
    exact sum_congr rfl fun l _ ↦ by ring
  have hB : |∑ k, ∑ l, c k * (S k l - a k l) * c l| ≤ εS * 1 * 1 * X :=
    hS.abs_le zero_le_one zero_le_one hX0 hcX hcX
  -- the quadratic part, expanded at `V`
  have h3 : ∑ j, w j * p j ^ 2 + 2 * ∑ j, v j * (q j - p j) ≤ ∑ j, q j ^ 2 / μ j := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun j _ ↦ ?_
    have hμj := hμ j
    have hwp : w j * p j ^ 2 ≤ p j ^ 2 / μ j := by
      rw [div_eq_mul_inv, mul_comm (p j ^ 2)]
      exact mul_le_mul_of_nonneg_right (hw j) (sq_nonneg _)
    have key : q j ^ 2 / μ j - (p j ^ 2 / μ j + 2 * (v j * (q j - p j))) =
        (q j - p j) ^ 2 / μ j := by
      simp only [hv]
      field_simp
      ring
    have : 0 ≤ (q j - p j) ^ 2 / μ j := div_nonneg (sq_nonneg _) hμj.le
    linarith
  -- the linear terms of the expansion
  have hqp : ∀ j, q j - p j = ∑ k, c k * ∑ l, (S k l - a k l) * C l j + ∑ k, c k * F k j := by
    intro j
    simp only [hq, hp, hF, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ ↦ ?_
    simp only [sub_mul, sum_sub_distrib]
    ring
  have h4 : ∑ j, v j * (q j - p j) = ∑ k, ∑ l, c k * (S k l - a k l) * z l +
      ∑ k, ∑ j, c k * F k j * v j := by
    simp only [hqp, mul_add, sum_add_distrib]
    congr 1
    · simp only [hz, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun k _ ↦ ?_
      rw [sum_comm]
      exact sum_congr rfl fun l _ ↦ sum_congr rfl fun j _ ↦ by ring
    · simp only [mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun k _ ↦ sum_congr rfl fun j _ ↦ by ring
  have hBz : |∑ k, ∑ l, c k * (S k l - a k l) * z l| ≤ εS * 1 * (ζ * κ₀) * X :=
    hS.abs_le zero_le_one (mul_nonneg hζ hκ₀) hX0 hcX hzX
  have hFv : |∑ k, ∑ j, c k * F k j * v j| ≤ Φ * κ₀ * X := by
    refine abs_le_of_sq_le_mul (mul_nonneg hΦ0 hκ₀) hX0 ((sq_sum_sum_mul_le F c v).trans ?_)
    calc (∑ k, ∑ j, F k j ^ 2) * (X * ∑ j, v j ^ 2) ≤ Φ ^ 2 * (X * (κ₀ ^ 2 * X)) := by gcongr
      _ = (Φ * κ₀) ^ 2 * X ^ 2 := by ring
  have hcert' : ν * X ≤ K * ∑ k, elo k * c k ^ 2 - ∑ k, ∑ l, a k l * c k * c l +
      ∑ j, w j * p j ^ 2 := hcert c
  have hνX : (εS * (1 + 2 * ζ * κ₀) + 2 * κ₀ * Φ) * X ≤ ν * X :=
    mul_le_mul_of_nonneg_right hν hX0
  have hgoal : ∑ j, (∑ k, c k * ∑ l, S k l * C l j) ^ 2 / μ j = ∑ j, q j ^ 2 / μ j := rfl
  rw [h2, hgoal]
  have e1 := (abs_le.mp hB).2
  have e2 := (abs_le.mp hBz).1
  have e3 := (abs_le.mp hFv).1
  have hlin : εS * 1 * 1 * X + 2 * (εS * 1 * (ζ * κ₀) * X) + 2 * (Φ * κ₀ * X) =
      (εS * (1 + 2 * ζ * κ₀) + 2 * κ₀ * Φ) * X := by ring
  linarith

/-! ### The Gram matrix of the captured modes -/

/-- **One-sided Gram bound from a certificate at the center.** With `S` within `ε_S` of `a`,
`|a C - V|_F ≤ Φ`, `|C v| ≤ ζ |v|`, `M` diagonal with `M k k ≤ m_hi k` and `δ ≥ 0`, a
certificate `Cᵀ V - δ Cᵀ diag(m_hi) C - θ Λ ⪰ ν` with `ν ≥ ε_S ζ² + Φ ζ` gives
`Cᵀ (S - δ M) C ⪰ θ Λ`. -/
theorem gram_form_ge_of_center {S a M : ι → ι → ℝ} {mhi : ι → ℝ} {C V : ι → κ → ℝ}
    {μ : κ → ℝ} {δ θ εS ζ Φ ν : ℝ}
    (hS : BilinearBound (fun k l ↦ S k l - a k l) εS) (hζ : 0 ≤ ζ)
    (hC : ∀ v : κ → ℝ, ∑ l, (∑ j, C l j * v j) ^ 2 ≤ ζ ^ 2 * ∑ j, v j ^ 2)
    (hM : ∀ k l, k ≠ l → M k l = 0) (hMhi : ∀ k, M k k ≤ mhi k) (hδ : 0 ≤ δ)
    (hΦ0 : 0 ≤ Φ) (hΦ : ∑ k, ∑ j, (∑ l, a k l * C l j - V k j) ^ 2 ≤ Φ ^ 2)
    (hν : εS * ζ ^ 2 + Φ * ζ ≤ ν)
    (hcert : ∀ d : κ → ℝ, ν * ∑ j, d j ^ 2 ≤ ∑ i, ∑ j, (∑ k, C k i * V k j) * d i * d j -
      δ * ∑ k, mhi k * (∑ j, C k j * d j) ^ 2 - θ * ∑ j, μ j * d j ^ 2) (d : κ → ℝ) :
    θ * ∑ j, μ j * d j ^ 2 ≤
      ∑ k, ∑ l, (∑ i, C k i * d i) * (S k l - δ * M k l) * (∑ j, C l j * d j) := by
  set D := ∑ j, d j ^ 2
  have hD0 : 0 ≤ D := sum_nonneg fun j _ ↦ sq_nonneg _
  set y : ι → ℝ := fun k ↦ ∑ j, C k j * d j with hy
  set F : ι → κ → ℝ := fun k j ↦ ∑ l, a k l * C l j - V k j with hF
  have hyD : ∑ k, y k ^ 2 ≤ ζ ^ 2 * D := hC d
  have hdD : ∑ j, d j ^ 2 ≤ 1 ^ 2 * D := by rw [one_pow, one_mul]
  have hsplit : ∑ k, ∑ l, y k * (S k l - δ * M k l) * y l =
      ∑ k, ∑ l, y k * a k l * y l + ∑ k, ∑ l, y k * (S k l - a k l) * y l -
        δ * ∑ k, ∑ l, y k * M k l * y l := by
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun l _ ↦ by ring
  have hMdiag : ∑ k, ∑ l, y k * M k l * y l = ∑ k, M k k * y k ^ 2 := by
    refine sum_congr rfl fun k _ ↦ ?_
    rw [sum_eq_single k (fun l _ hl ↦ by rw [hM k l (Ne.symm hl)]; ring) (by simp)]
    ring
  have hMle : ∑ k, M k k * y k ^ 2 ≤ ∑ k, mhi k * y k ^ 2 :=
    sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_right (hMhi k) (sq_nonneg _)
  have hcenter : ∑ k, ∑ l, y k * a k l * y l =
      ∑ i, ∑ j, (∑ k, C k i * V k j) * d i * d j + ∑ k, ∑ j, y k * F k j * d j := by
    -- both sides split off `∑ k, ∑ j, y k * V k j * d j`
    have hV : ∑ i, ∑ j, (∑ k, C k i * V k j) * d i * d j = ∑ k, ∑ j, y k * V k j * d j := by
      simp only [hy, sum_mul]
      rw [sum_comm, sum_congr rfl fun j _ ↦ sum_comm, sum_comm]
      exact sum_congr rfl fun k _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun i _ ↦ by ring
    have hF' : ∑ k, ∑ j, y k * F k j * d j =
        ∑ k, ∑ l, y k * a k l * y l - ∑ k, ∑ j, y k * V k j * d j := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun k _ ↦ ?_
      simp only [hF, hy, mul_sum, sum_mul, mul_sub, sub_mul, sum_sub_distrib]
      rw [sum_comm]
      congr 1
      exact sum_congr rfl fun j _ ↦ sum_congr rfl fun l _ ↦ sum_congr rfl fun i _ ↦ by ring
    rw [hV, hF']
    ring
  have hB : |∑ k, ∑ l, y k * (S k l - a k l) * y l| ≤ εS * ζ * ζ * D :=
    hS.abs_le hζ hζ hD0 hyD hyD
  have hFd : |∑ k, ∑ j, y k * F k j * d j| ≤ Φ * ζ * D := by
    refine abs_le_of_sq_le_mul (mul_nonneg hΦ0 hζ) hD0 ((sq_sum_sum_mul_le F y d).trans ?_)
    calc (∑ k, ∑ j, F k j ^ 2) * ((∑ k, y k ^ 2) * D) ≤ Φ ^ 2 * ((ζ ^ 2 * D) * D) := by gcongr
      _ = (Φ * ζ) ^ 2 * D ^ 2 := by ring
  have hcert' := hcert d
  have hνD : (εS * ζ ^ 2 + Φ * ζ) * D ≤ ν * D := mul_le_mul_of_nonneg_right hν hD0
  have hδM : δ * ∑ k, M k k * y k ^ 2 ≤ δ * ∑ k, mhi k * y k ^ 2 :=
    mul_le_mul_of_nonneg_left hMle hδ
  have e1 := (abs_le.mp hB).1
  have e2 := (abs_le.mp hFd).1
  have hgoal : ∑ k, ∑ l, (∑ i, C k i * d i) * (S k l - δ * M k l) * (∑ j, C l j * d j) =
      ∑ k, ∑ l, y k * (S k l - δ * M k l) * y l := rfl
  rw [hgoal, hsplit, hMdiag, hcenter]
  linarith

/-! ### The residuals of the captured modes -/

/-- Minkowski's inequality in squared form. -/
theorem sum_sq_add_le {p q : ι → ℝ} {P Q W : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hW : 0 ≤ W)
    (hp : ∑ k, p k ^ 2 ≤ P ^ 2 * W) (hq : ∑ k, q k ^ 2 ≤ Q ^ 2 * W) :
    ∑ k, (p k + q k) ^ 2 ≤ (P + Q) ^ 2 * W := by
  have hpq : ∑ k, p k * q k ≤ P * Q * W := by
    have h := sum_mul_sq_le_sq_mul_sq univ p q
    refine (le_abs_self _).trans (abs_le_of_sq_le_mul (mul_nonneg hP hQ) hW (h.trans ?_))
    calc (∑ k, p k ^ 2) * ∑ k, q k ^ 2 ≤ (P ^ 2 * W) * (Q ^ 2 * W) :=
          mul_le_mul hp hq (sum_nonneg fun k _ ↦ sq_nonneg _) (by positivity)
      _ = (P * Q) ^ 2 * W ^ 2 := by ring
  have hexp : ∑ k, (p k + q k) ^ 2 = ∑ k, p k ^ 2 + 2 * ∑ k, p k * q k + ∑ k, q k ^ 2 := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun k _ ↦ by ring
  rw [hexp]
  linarith

/-- **Residual bound from a certificate at the center.** For `R = S C - E C Λ` with `S` within
`ε_S` of `a`, `|a C - V|_F ≤ Φ`, `|C v| ≤ ζ |v|`, `|e - ê| ≤ ε_e`, `e ≥ e_lo > 0`,
`e_inv ≥ 1/e_lo`, `e_inv ≤ e_max` and `μ ≥ μ_lo > 0`, the certificate for the center residual
`R̂ = V - Ê C Λ`,
`(1 + θ) ∑_k e_inv k ((R̂ Λ⁻¹ b)_k)² + ν |b|² ≤ ε² ∑_k e_lo k ((C b)_k)²` with
`ν ≥ (1 + θ⁻¹) e_max (ε_S ζ / μ_lo + Φ / μ_lo + ε_e ζ)²`, gives
`∑_k ((R Λ⁻¹ b)_k)² / e_k ≤ ε² ∑_k e_k ((C b)_k)²`. -/
theorem residual_form_le_of_center {S a : ι → ι → ℝ} {e elo einv ehat : ι → ℝ}
    {C V : ι → κ → ℝ} {μ : κ → ℝ} {ε θ εS ζ Φ εe μlo emax ν : ℝ}
    (hS : BilinearBound (fun k l ↦ S k l - a k l) εS) (hζ : 0 ≤ ζ)
    (hC : ∀ v : κ → ℝ, ∑ l, (∑ j, C l j * v j) ^ 2 ≤ ζ ^ 2 * ∑ j, v j ^ 2)
    (hΦ0 : 0 ≤ Φ) (hΦ : ∑ k, ∑ j, (∑ l, a k l * C l j - V k j) ^ 2 ≤ Φ ^ 2)
    (he : ∀ k, elo k ≤ e k) (helo : ∀ k, 0 < elo k) (hinv : ∀ k, 1 ≤ einv k * elo k)
    (hmax : ∀ k, einv k ≤ emax) (hemax : 0 ≤ emax) (hεe : 0 ≤ εe) (heh : ∀ k, |e k - ehat k| ≤ εe)
    (hμlo : 0 < μlo) (hμ : ∀ j, μlo ≤ μ j) (hθ : 0 < θ)
    (hν : (1 + θ⁻¹) * emax * (εS * ζ / μlo + Φ / μlo + εe * ζ) ^ 2 ≤ ν)
    (hcert : ∀ b : κ → ℝ, (1 + θ) * ∑ k, einv k *
        (∑ j, (V k j - ehat k * C k j * μ j) * (b j / μ j)) ^ 2 + ν * ∑ j, b j ^ 2 ≤
      ε ^ 2 * ∑ k, elo k * (∑ j, C k j * b j) ^ 2) (b : κ → ℝ) :
    ∑ k, (∑ j, (∑ l, S k l * C l j - e k * C k j * μ j) * (b j / μ j)) ^ 2 / e k ≤
      ε ^ 2 * ∑ k, e k * (∑ j, C k j * b j) ^ 2 := by
  set B := ∑ j, b j ^ 2
  have hB0 : 0 ≤ B := sum_nonneg fun j _ ↦ sq_nonneg _
  have hμpos : ∀ j, 0 < μ j := fun j ↦ hμlo.trans_le (hμ j)
  set β : κ → ℝ := fun j ↦ b j / μ j with hβ
  have hβB : ∑ j, β j ^ 2 ≤ (1 / μlo) ^ 2 * B := by
    rw [mul_sum]
    refine sum_le_sum fun j _ ↦ ?_
    simp only [hβ, div_pow, one_div, inv_pow]
    rw [div_eq_mul_inv, mul_comm]
    gcongr
    exact hμ j
  set y : ι → ℝ := fun l ↦ ∑ j, C l j * β j
  set F : ι → κ → ℝ := fun k j ↦ ∑ l, a k l * C l j - V k j with hF
  set r : ι → ℝ := fun k ↦ ∑ j, (∑ l, S k l * C l j - e k * C k j * μ j) * β j
  set rh : ι → ℝ := fun k ↦ ∑ j, (V k j - ehat k * C k j * μ j) * β j
  set g : ι → ℝ := fun k ↦ ∑ l, (S k l - a k l) * y l
  set f : ι → ℝ := fun k ↦ ∑ j, F k j * β j
  set h : ι → ℝ := fun k ↦ -((e k - ehat k) * ∑ j, C k j * b j)
  have hdiff : ∀ k, r k - rh k = g k + f k + h k := by
    intro k
    have hCb : ∑ j, C k j * μ j * β j = ∑ j, C k j * b j :=
      sum_congr rfl fun j _ ↦ by simp only [hβ]; field_simp [(hμpos j).ne']
    have hg : g k = ∑ j, (∑ l, (S k l - a k l) * C l j) * β j := by
      simp only [g, y, mul_sum, sum_mul]
      rw [sum_comm]
      exact sum_congr rfl fun j _ ↦ sum_congr rfl fun l _ ↦ by ring
    simp only [r, rh, hg, f, h, hF, ← hCb]
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib, ← sum_neg_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    simp only [sub_mul, sum_sub_distrib, sum_mul]
    ring
  have hy : ∑ l, y l ^ 2 ≤ (ζ * (1 / μlo)) ^ 2 * B :=
    (hC β).trans (by rw [mul_pow, mul_assoc]; gcongr)
  have hg : ∑ k, g k ^ 2 ≤ (εS * ζ / μlo) ^ 2 * B :=
    (hS.sum_sq_le y).trans (by
      rw [show (εS * ζ / μlo) ^ 2 * B = εS ^ 2 * ((ζ * (1 / μlo)) ^ 2 * B) by ring]
      gcongr)
  have hf : ∑ k, f k ^ 2 ≤ (Φ / μlo) ^ 2 * B :=
    (sum_sq_sum_mul_le_frobenius F β).trans (by
      rw [show (Φ / μlo) ^ 2 * B = Φ ^ 2 * ((1 / μlo) ^ 2 * B) by ring]
      gcongr)
  have hh : ∑ k, h k ^ 2 ≤ (εe * ζ) ^ 2 * B := by
    calc ∑ k, h k ^ 2 ≤ ∑ k, εe ^ 2 * (∑ j, C k j * b j) ^ 2 := by
          refine sum_le_sum fun k _ ↦ ?_
          simp only [h, neg_sq, mul_pow]
          exact mul_le_mul_of_nonneg_right
            (sq_le_sq' (abs_le.mp (heh k)).1 (abs_le.mp (heh k)).2) (sq_nonneg _)
      _ ≤ (εe * ζ) ^ 2 * B := by rw [← mul_sum, mul_pow, mul_assoc]; gcongr; exact hC b
  have hgf := sum_sq_add_le (by have := hS.1; positivity) (by positivity) hB0 hg hf
  have hgfh := sum_sq_add_le (by have := hS.1; positivity) (by positivity) hB0 hgf hh
  have hrr : ∑ k, (r k - rh k) ^ 2 ≤ (εS * ζ / μlo + Φ / μlo + εe * ζ) ^ 2 * B := by
    simpa only [hdiff] using hgfh
  have hinv0 : ∀ k, 0 ≤ einv k := fun k ↦ by
    by_contra hneg
    nlinarith [hinv k, helo k, not_le.mp hneg]
  have hstep : ∀ k, r k ^ 2 / e k ≤ einv k * ((1 + θ) * rh k ^ 2 +
      (1 + θ⁻¹) * (r k - rh k) ^ 2) := by
    intro k
    have hek : 0 < e k := (helo k).trans_le (he k)
    have h1 : r k ^ 2 / e k ≤ einv k * r k ^ 2 := by
      rw [div_le_iff₀ hek]
      have : 1 ≤ einv k * e k :=
        (hinv k).trans (mul_le_mul_of_nonneg_left (he k) (hinv0 k))
      linarith [mul_le_mul_of_nonneg_right this (sq_nonneg (r k))]
    have h2 : r k ^ 2 ≤ (1 + θ) * rh k ^ 2 + (1 + θ⁻¹) * (r k - rh k) ^ 2 := by
      have hθ' : θ⁻¹ * θ = 1 := inv_mul_cancel₀ hθ.ne'
      have hsq : 0 ≤ (θ * rh k - (r k - rh k)) ^ 2 * θ⁻¹ :=
        mul_nonneg (sq_nonneg _) (inv_nonneg.mpr hθ.le)
      have hexp : (θ * rh k - (r k - rh k)) ^ 2 * θ⁻¹ =
          θ * rh k ^ 2 - 2 * rh k * (r k - rh k) + θ⁻¹ * (r k - rh k) ^ 2 := by
        field_simp
        ring
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (hinv0 k))
  have hsum : ∑ k, r k ^ 2 / e k ≤ (1 + θ) * ∑ k, einv k * rh k ^ 2 + ν * B := by
    calc ∑ k, r k ^ 2 / e k ≤ ∑ k, einv k * ((1 + θ) * rh k ^ 2 +
          (1 + θ⁻¹) * (r k - rh k) ^ 2) := sum_le_sum fun k _ ↦ hstep k
      _ = (1 + θ) * ∑ k, einv k * rh k ^ 2 +
          (1 + θ⁻¹) * ∑ k, einv k * (r k - rh k) ^ 2 := by
          rw [mul_sum, mul_sum, ← sum_add_distrib]
          exact sum_congr rfl fun k _ ↦ by ring
      _ ≤ (1 + θ) * ∑ k, einv k * rh k ^ 2 +
          (1 + θ⁻¹) * (emax * ((εS * ζ / μlo + Φ / μlo + εe * ζ) ^ 2 * B)) := by
          have hθ1 : 0 ≤ 1 + θ⁻¹ := by positivity
          gcongr
          exact (sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_right (hmax k) (sq_nonneg _)).trans
            ((mul_sum _ _ _).symm.trans_le (by gcongr))
      _ ≤ (1 + θ) * ∑ k, einv k * rh k ^ 2 + ν * B := by
          linarith [mul_le_mul_of_nonneg_right hν hB0]
  exact hsum.trans ((hcert b).trans (by gcongr with k; exact he k))

/-! ### Gram matrices with weights -/

/-- **Weighted Gram bound from a certificate at the center.** If `|H - Ĥ| ≤ h` entrywise and
`Ĥ + n h I ≤ g Λ²` as forms, then `Λ⁻¹ H Λ⁻¹ ≤ g I`. -/
theorem scaled_form_le_of_center {H Hc : κ → κ → ℝ} {μ : κ → ℝ} {h g : ℝ}
    (hμ : ∀ j, μ j ≠ 0) (hH : ∀ i j, |H i j - Hc i j| ≤ h)
    (hcert : ∀ y : κ → ℝ, ∑ i, ∑ j, Hc i j * y i * y j +
      Fintype.card κ * h * ∑ j, y j ^ 2 ≤ g * ∑ j, μ j ^ 2 * y j ^ 2) (c : κ → ℝ) :
    ∑ i, ∑ j, H i j / (μ i * μ j) * c i * c j ≤ g * ∑ j, c j ^ 2 := by
  set y : κ → ℝ := fun j ↦ c j / μ j
  have hc : ∀ j, c j = μ j * y j := fun j ↦ by simp only [y]; field_simp [hμ j]
  have h1 : ∑ i, ∑ j, H i j / (μ i * μ j) * c i * c j = ∑ i, ∑ j, H i j * y i * y j :=
    sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by
      simp only [y]; field_simp [hμ i, hμ j]
  have h2 : ∑ i, ∑ j, H i j * y i * y j = ∑ i, ∑ j, Hc i j * y i * y j +
      ∑ i, ∑ j, (H i j - Hc i j) * y i * y j := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun i _ ↦ by rw [← sum_add_distrib]; exact sum_congr rfl fun j _ ↦ by ring
  have h3 := (abs_le.mp (abs_quadForm_le_of_abs_le hH y)).2
  have h4 : g * ∑ j, μ j ^ 2 * y j ^ 2 = g * ∑ j, c j ^ 2 := by
    congr 1
    exact sum_congr rfl fun j _ ↦ by rw [hc j]; ring
  rw [h1, h2, ← h4]
  linarith [hcert y]

/-! ### Diagonal scaling -/

/-- The capture form is invariant under the diagonal scaling `S ↦ σ S σ`, `e ↦ σ² e`,
`C ↦ σ⁻¹ C`, `c ↦ σ⁻¹ c`. -/
theorem capture_form_scale {σ : ι → ℝ} (hσ : ∀ k, σ k ≠ 0) (K : ℝ) (e : ι → ℝ)
    (S : ι → ι → ℝ) (C : ι → κ → ℝ) (μ : κ → ℝ) (c : ι → ℝ) :
    K * ∑ k, σ k ^ 2 * e k * (c k / σ k) ^ 2 -
        ∑ k, ∑ l, σ k * S k l * σ l * (c k / σ k) * (c l / σ l) +
        ∑ j, (∑ k, c k / σ k * ∑ l, σ k * S k l * σ l * (C l j / σ l)) ^ 2 / μ j =
      K * ∑ k, e k * c k ^ 2 - ∑ k, ∑ l, S k l * c k * c l +
        ∑ j, (∑ k, c k * ∑ l, S k l * C l j) ^ 2 / μ j := by
  have h1 : ∀ k, σ k ^ 2 * e k * (c k / σ k) ^ 2 = e k * c k ^ 2 := fun k ↦ by
    field_simp [hσ k]
  have h2 : ∀ k l, σ k * S k l * σ l * (c k / σ k) * (c l / σ l) = S k l * c k * c l :=
    fun k l ↦ by field_simp [hσ k, hσ l]
  have h3 : ∀ j k, c k / σ k * ∑ l, σ k * S k l * σ l * (C l j / σ l) =
      c k * ∑ l, S k l * C l j := fun j k ↦ by
    rw [mul_sum, mul_sum]
    exact sum_congr rfl fun l _ ↦ by field_simp [hσ k, hσ l]
  simp only [h1, h2, h3]

/-- The Gram form of combinations is invariant under `A ↦ σ A σ`, `C ↦ σ⁻¹ C`. -/
theorem gram_form_scale {σ : ι → ℝ} (hσ : ∀ k, σ k ≠ 0) (A : ι → ι → ℝ) (C : ι → κ → ℝ)
    (d : κ → ℝ) :
    ∑ k, ∑ l, (∑ i, C k i / σ k * d i) * (σ k * A k l * σ l) * (∑ j, C l j / σ l * d j) =
      ∑ k, ∑ l, (∑ i, C k i * d i) * A k l * (∑ j, C l j * d j) := by
  refine sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ ?_
  have hk : ∑ i, C k i / σ k * d i = (∑ i, C k i * d i) / σ k := by
    rw [sum_div]; exact sum_congr rfl fun i _ ↦ by ring
  have hl : ∑ j, C l j / σ l * d j = (∑ j, C l j * d j) / σ l := by
    rw [sum_div]; exact sum_congr rfl fun j _ ↦ by ring
  rw [hk, hl]
  field_simp [hσ k, hσ l]

/-- The two sides of the residual bound are invariant under `S ↦ σ S σ`, `e ↦ σ² e`,
`C ↦ σ⁻¹ C`. -/
theorem residual_form_scale {σ : ι → ℝ} (hσ : ∀ k, σ k ≠ 0) (S : ι → ι → ℝ) (e : ι → ℝ)
    (C : ι → κ → ℝ) (μ b : κ → ℝ) :
    (∑ k, (∑ j, (∑ l, σ k * S k l * σ l * (C l j / σ l) - σ k ^ 2 * e k * (C k j / σ k) *
        μ j) * (b j / μ j)) ^ 2 / (σ k ^ 2 * e k) =
      ∑ k, (∑ j, (∑ l, S k l * C l j - e k * C k j * μ j) * (b j / μ j)) ^ 2 / e k) ∧
    (∑ k, σ k ^ 2 * e k * (∑ j, C k j / σ k * b j) ^ 2 = ∑ k, e k * (∑ j, C k j * b j) ^ 2) := by
  constructor
  · refine sum_congr rfl fun k _ ↦ ?_
    have hrow : ∑ j, (∑ l, σ k * S k l * σ l * (C l j / σ l) - σ k ^ 2 * e k * (C k j / σ k) *
        μ j) * (b j / μ j) = σ k * ∑ j, (∑ l, S k l * C l j - e k * C k j * μ j) * (b j / μ j) := by
      rw [mul_sum]
      refine sum_congr rfl fun j _ ↦ ?_
      have hl : ∑ l, σ k * S k l * σ l * (C l j / σ l) = σ k * ∑ l, S k l * C l j := by
        rw [mul_sum]; exact sum_congr rfl fun l _ ↦ by field_simp [hσ l]
      rw [hl]
      field_simp [hσ k]
    rw [hrow]
    by_cases he : e k = 0
    · simp [he]
    · field_simp [hσ k, he]
  · refine sum_congr rfl fun k _ ↦ ?_
    have hk : ∑ j, C k j / σ k * b j = (∑ j, C k j * b j) / σ k := by
      rw [sum_div]; exact sum_congr rfl fun j _ ↦ by ring
    rw [hk]
    field_simp [hσ k]

/-! ### Norms of finite-rank maps from Gram matrices -/

/-- `|C v|² = vᵀ (Cᵀ C) v`. -/
theorem sum_sq_sum_mul_eq_gram (C : ι → κ → ℝ) (v : κ → ℝ) :
    ∑ l, (∑ j, C l j * v j) ^ 2 = ∑ i, ∑ j, (∑ l, C l i * C l j) * v i * v j := by
  calc ∑ l, (∑ j, C l j * v j) ^ 2 = ∑ l, ∑ i, ∑ j, C l i * v i * (C l j * v j) :=
        sum_congr rfl fun l _ ↦ by rw [sq, sum_mul_sum]
    _ = ∑ i, ∑ l, ∑ j, C l i * v i * (C l j * v j) := sum_comm
    _ = ∑ i, ∑ j, ∑ l, C l i * v i * (C l j * v j) := sum_congr rfl fun i _ ↦ sum_comm
    _ = _ := sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by
        rw [sum_mul, sum_mul]; exact sum_congr rfl fun l _ ↦ by ring

/-- **Norm of `x ↦ Λ⁻¹ Vᵀ x` from its Gram matrix.** If `uᵀ (Vᵀ V) u ≤ κ² ∑ μ_j² u_j²` for all
`u`, then `∑_j ((Vᵀ x)_j / μ_j)² ≤ κ² |x|²`. -/
theorem sum_sq_div_le_of_gram {V : ι → κ → ℝ} {μ : κ → ℝ} {κ₀ : ℝ} (hμ : ∀ j, μ j ≠ 0)
    (hG : ∀ u : κ → ℝ, ∑ i, ∑ j, (∑ k, V k i * V k j) * u i * u j ≤
      κ₀ ^ 2 * ∑ j, μ j ^ 2 * u j ^ 2) (x : ι → ℝ) :
    ∑ j, ((∑ k, x k * V k j) / μ j) ^ 2 ≤ κ₀ ^ 2 * ∑ k, x k ^ 2 := by
  set y : κ → ℝ := fun j ↦ (∑ k, x k * V k j) / μ j
  set u : κ → ℝ := fun j ↦ y j / μ j
  set z : ι → ℝ := fun k ↦ ∑ j, V k j * u j
  set Y := ∑ j, y j ^ 2
  set X := ∑ k, x k ^ 2
  have hY0 : 0 ≤ Y := sum_nonneg fun j _ ↦ sq_nonneg _
  have hX0 : 0 ≤ X := sum_nonneg fun k _ ↦ sq_nonneg _
  have hYxz : Y = ∑ k, x k * z k := by
    calc Y = ∑ j, u j * ∑ k, x k * V k j :=
          sum_congr rfl fun j _ ↦ by simp only [u, y]; ring
      _ = ∑ j, ∑ k, u j * (x k * V k j) := sum_congr rfl fun j _ ↦ mul_sum _ _ _
      _ = ∑ k, ∑ j, u j * (x k * V k j) := sum_comm
      _ = ∑ k, x k * z k := sum_congr rfl fun k _ ↦ by
          simp only [z, mul_sum]; exact sum_congr rfl fun j _ ↦ by ring
  have hz : ∑ k, z k ^ 2 ≤ κ₀ ^ 2 * Y := by
    have := hG u
    rw [← sum_sq_sum_mul_eq_gram] at this
    refine this.trans_eq ?_
    congr 1
    exact sum_congr rfl fun j _ ↦ by simp only [u]; field_simp [hμ j]
  have hcs := sum_mul_sq_le_sq_mul_sq univ x z
  rw [← hYxz] at hcs
  rcases hY0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have : Y * Y ≤ Y * (κ₀ ^ 2 * X) := by nlinarith [mul_le_mul_of_nonneg_left hz hX0]
    exact le_of_mul_le_mul_left this hpos

/-! ### Matrix forms -/

section MatrixForms

variable [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] in
/-- The form of `B Λ⁻¹ Bᵀ`. -/
theorem lowRank_dotProduct_eq (B : _root_.Matrix ι κ ℝ) (μ : κ → ℝ) (c : ι → ℝ) :
    c ⬝ᵥ ((B * diagonal (fun j ↦ (μ j)⁻¹) * Bᵀ) *ᵥ c) = ∑ j, (∑ k, c k * B k j) ^ 2 / μ j := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
  simp only [dotProduct, mulVec_diagonal]
  simp only [vecMul, mulVec, transpose_apply, dotProduct]
  refine sum_congr rfl fun j _ ↦ ?_
  have : ∑ x, B x j * c x = ∑ k, c k * B k j := sum_congr rfl fun k _ ↦ by ring
  rw [this, div_eq_mul_inv]
  ring

/-- The form of the capture matrix `K diag(e) - S + (S C) Λ⁻¹ (S C)ᵀ` as sums. -/
theorem captureMatrix_dotProduct_eq (K : ℝ) (e : ι → ℝ) (S : _root_.Matrix ι ι ℝ)
    (C : _root_.Matrix ι κ ℝ) (μ : κ → ℝ) (c : ι → ℝ) :
    c ⬝ᵥ ((K • diagonal e - S + (S * C) * diagonal (fun j ↦ (μ j)⁻¹) * (S * C)ᵀ) *ᵥ c) =
      K * ∑ k, e k * c k ^ 2 - ∑ k, ∑ l, S k l * c k * c l +
        ∑ j, (∑ k, c k * ∑ l, S k l * C l j) ^ 2 / μ j := by
  have h1 : c ⬝ᵥ (diagonal e *ᵥ c) = ∑ k, e k * c k ^ 2 := by
    simp only [dotProduct, mulVec_diagonal]
    exact sum_congr rfl fun k _ ↦ by ring
  have h2 : c ⬝ᵥ (S *ᵥ c) = ∑ k, ∑ l, S k l * c k * c l := by
    simp only [dotProduct, mulVec, mul_sum]
    exact sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ by ring
  rw [add_mulVec, sub_mulVec, dotProduct_add, dotProduct_sub, smul_mulVec, dotProduct_smul,
    lowRank_dotProduct_eq, smul_eq_mul, h1, h2]
  simp only [mul_apply]

omit [DecidableEq ι] in
/-- The form of `Cᵀ A C - θ diag(μ)` as sums. -/
theorem gramMatrix_dotProduct_eq (A : _root_.Matrix ι ι ℝ) (C : _root_.Matrix ι κ ℝ) (θ : ℝ)
    (μ : κ → ℝ) (d : κ → ℝ) :
    d ⬝ᵥ ((Cᵀ * A * C - θ • diagonal μ) *ᵥ d) =
      ∑ k, ∑ l, (∑ i, C k i * d i) * A k l * (∑ j, C l j * d j) - θ * ∑ j, μ j * d j ^ 2 := by
  have h1 : d ⬝ᵥ (diagonal μ *ᵥ d) = ∑ j, μ j * d j ^ 2 := by
    simp only [dotProduct, mulVec_diagonal]
    exact sum_congr rfl fun j _ ↦ by ring
  have h2 : d ⬝ᵥ ((Cᵀ * A * C) *ᵥ d) =
      ∑ k, ∑ l, (∑ i, C k i * d i) * A k l * (∑ j, C l j * d j) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    simp only [dotProduct, mulVec, mul_sum]
    exact sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ by ring_nf
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul, h1, h2]

/-- **Capture matrix certificate, matrix form.** The hypotheses of
`capture_form_nonneg_of_center` for the scaled matrix `σ S σ`, weights `σ² e` and coefficients
`σ⁻¹ C` give `K diag(e) - S + (S C) Λ⁻¹ (S C)ᵀ ⪰ 0`. -/
theorem captureMatrix_nonneg_of_center {S : _root_.Matrix ι ι ℝ} {e : ι → ℝ}
    {C : _root_.Matrix ι κ ℝ} {μ : κ → ℝ} {K : ℝ} {σ : ι → ℝ} (hσ : ∀ k, σ k ≠ 0)
    {a : ι → ι → ℝ} {elo : ι → ℝ} {V : ι → κ → ℝ} {w : κ → ℝ} {εS ζ κ₀ Φ ν : ℝ}
    (hS : BilinearBound (fun k l ↦ σ k * S k l * σ l - a k l) εS) (hK : 0 ≤ K)
    (he : ∀ k, elo k ≤ σ k ^ 2 * e k) (hμ : ∀ j, 0 < μ j) (hw : ∀ j, w j ≤ (μ j)⁻¹)
    (hζ : 0 ≤ ζ) (hC : ∀ v : κ → ℝ, ∑ l, (∑ j, C l j / σ l * v j) ^ 2 ≤ ζ ^ 2 * ∑ j, v j ^ 2)
    (hκ₀ : 0 ≤ κ₀)
    (hκ : ∀ x : ι → ℝ, ∑ j, ((∑ k, x k * V k j) / μ j) ^ 2 ≤ κ₀ ^ 2 * ∑ k, x k ^ 2)
    (hΦ0 : 0 ≤ Φ) (hΦ : ∑ k, ∑ j, (∑ l, a k l * (C l j / σ l) - V k j) ^ 2 ≤ Φ ^ 2)
    (hν : εS * (1 + 2 * ζ * κ₀) + 2 * κ₀ * Φ ≤ ν)
    (hcert : ∀ x : ι → ℝ, ν * ∑ k, x k ^ 2 ≤ K * ∑ k, elo k * x k ^ 2 -
      ∑ k, ∑ l, a k l * x k * x l + ∑ j, w j * (∑ k, x k * V k j) ^ 2) (c : ι → ℝ) :
    0 ≤ c ⬝ᵥ ((K • diagonal e - S + (S * C) * diagonal (fun j ↦ (μ j)⁻¹) * (S * C)ᵀ) *ᵥ c) := by
  have hcore := capture_form_nonneg_of_center (S := fun k l ↦ σ k * S k l * σ l)
    (e := fun k ↦ σ k ^ 2 * e k) (C := fun l j ↦ C l j / σ l) hS hK he hμ hw hζ hC hκ₀ hκ hΦ0
    hΦ hν hcert (fun k ↦ c k / σ k)
  have heq := capture_form_scale hσ K e (fun k l ↦ S k l) (fun l j ↦ C l j) μ c
  rw [captureMatrix_dotProduct_eq]
  beta_reduce at hcore heq
  linarith

omit [DecidableEq ι] in
/-- **Gram certificate, matrix form.** For `A = S - δ M` with `M` diagonal, the hypotheses of
`gram_form_ge_of_center` for `σ S σ`, `σ M σ` and `σ⁻¹ C` give `Cᵀ A C - θ diag(μ) ⪰ 0`. -/
theorem gramMatrix_nonneg_of_center {A S M : _root_.Matrix ι ι ℝ} {C : _root_.Matrix ι κ ℝ}
    {μ : κ → ℝ} {δ θ : ℝ} {σ : ι → ℝ} (hσ : ∀ k, σ k ≠ 0) (hA : A = S - δ • M)
    {a : ι → ι → ℝ} {mhi : ι → ℝ} {V : ι → κ → ℝ} {εS ζ Φ ν : ℝ}
    (hS : BilinearBound (fun k l ↦ σ k * S k l * σ l - a k l) εS) (hζ : 0 ≤ ζ)
    (hC : ∀ v : κ → ℝ, ∑ l, (∑ j, C l j / σ l * v j) ^ 2 ≤ ζ ^ 2 * ∑ j, v j ^ 2)
    (hM : ∀ k l, k ≠ l → M k l = 0) (hMhi : ∀ k, σ k ^ 2 * M k k ≤ mhi k) (hδ : 0 ≤ δ)
    (hΦ0 : 0 ≤ Φ) (hΦ : ∑ k, ∑ j, (∑ l, a k l * (C l j / σ l) - V k j) ^ 2 ≤ Φ ^ 2)
    (hν : εS * ζ ^ 2 + Φ * ζ ≤ ν)
    (hcert : ∀ d : κ → ℝ, ν * ∑ j, d j ^ 2 ≤
      ∑ i, ∑ j, (∑ k, C k i / σ k * V k j) * d i * d j -
        δ * ∑ k, mhi k * (∑ j, C k j / σ k * d j) ^ 2 - θ * ∑ j, μ j * d j ^ 2)
    (d : κ → ℝ) :
    0 ≤ d ⬝ᵥ ((Cᵀ * A * C - θ • diagonal μ) *ᵥ d) := by
  have heq := gram_form_scale hσ (fun k l ↦ A k l) (fun l j ↦ C l j) d
  rw [gramMatrix_dotProduct_eq, sub_nonneg]
  beta_reduce at heq
  rw [← heq]
  have h := gram_form_ge_of_center (S := fun k l ↦ σ k * S k l * σ l)
    (M := fun k l ↦ σ k * M k l * σ l) (C := fun l j ↦ C l j / σ l) hS hζ hC
    (fun k l hkl ↦ by simp [hM k l hkl])
    (fun k ↦ (by ring : σ k * M k k * σ k = σ k ^ 2 * M k k).trans_le (hMhi k)) hδ hΦ0 hΦ hν
    hcert d
  refine h.trans_eq (sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ ?_)
  rw [hA]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The entries of `S C - diag(e) C diag(μ)`. -/
theorem residualMatrix_apply (S : _root_.Matrix ι ι ℝ) (e : ι → ℝ) (C : _root_.Matrix ι κ ℝ)
    (μ : κ → ℝ) (k : ι) (j : κ) :
    (S * C - diagonal e * C * diagonal μ) k j = ∑ l, S k l * C l j - e k * C k j * μ j := by
  rw [Matrix.sub_apply, mul_diagonal, diagonal_mul, mul_apply]

/-- **Residual certificate, matrix form.** The hypotheses of `residual_form_le_of_center` for
`σ S σ`, `σ² e` and `σ⁻¹ C` give the Loewner bound for `R = S C - diag(e) C diag(μ)`. -/
theorem residualMatrix_le_of_center {S : _root_.Matrix ι ι ℝ} {e : ι → ℝ}
    {C : _root_.Matrix ι κ ℝ} {μ : κ → ℝ} {σ : ι → ℝ} (hσ : ∀ k, σ k ≠ 0)
    {a : ι → ι → ℝ} {elo einv ehat : ι → ℝ} {V : ι → κ → ℝ}
    {ε θ εS ζ Φ εe μlo emax ν : ℝ}
    (hS : BilinearBound (fun k l ↦ σ k * S k l * σ l - a k l) εS) (hζ : 0 ≤ ζ)
    (hC : ∀ v : κ → ℝ, ∑ l, (∑ j, C l j / σ l * v j) ^ 2 ≤ ζ ^ 2 * ∑ j, v j ^ 2)
    (hΦ0 : 0 ≤ Φ) (hΦ : ∑ k, ∑ j, (∑ l, a k l * (C l j / σ l) - V k j) ^ 2 ≤ Φ ^ 2)
    (he : ∀ k, elo k ≤ σ k ^ 2 * e k) (helo : ∀ k, 0 < elo k)
    (hinv : ∀ k, 1 ≤ einv k * elo k) (hmax : ∀ k, einv k ≤ emax) (hemax : 0 ≤ emax)
    (hεe : 0 ≤ εe) (heh : ∀ k, |σ k ^ 2 * e k - ehat k| ≤ εe)
    (hμlo : 0 < μlo) (hμ : ∀ j, μlo ≤ μ j) (hθ : 0 < θ)
    (hν : (1 + θ⁻¹) * emax * (εS * ζ / μlo + Φ / μlo + εe * ζ) ^ 2 ≤ ν)
    (hcert : ∀ b : κ → ℝ, (1 + θ) * ∑ k, einv k *
        (∑ j, (V k j - ehat k * (C k j / σ k) * μ j) * (b j / μ j)) ^ 2 + ν * ∑ j, b j ^ 2 ≤
      ε ^ 2 * ∑ k, elo k * (∑ j, C k j / σ k * b j) ^ 2) (b : κ → ℝ) :
    ∑ k, (∑ j, (S * C - diagonal e * C * diagonal μ) k j * (b j / μ j)) ^ 2 / e k ≤
      ε ^ 2 * ∑ k, e k * (C *ᵥ b) k ^ 2 := by
  have h := residual_form_le_of_center (S := fun k l ↦ σ k * S k l * σ l)
    (e := fun k ↦ σ k ^ 2 * e k) (C := fun l j ↦ C l j / σ l) hS hζ hC hΦ0 hΦ he helo hinv hmax
    hemax hεe heh hμlo hμ hθ hν hcert b
  obtain ⟨h1, h2⟩ := residual_form_scale hσ S e C μ b
  simp only [residualMatrix_apply, mulVec, dotProduct]
  rw [← h1, ← h2]
  exact h

end MatrixForms

end PDE.Analysis.Matrix
