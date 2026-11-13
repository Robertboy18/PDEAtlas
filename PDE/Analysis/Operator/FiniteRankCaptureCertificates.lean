/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.FiniteRankCapture
public import CAS.Analysis.Matrix.QuadraticFormBounds
import Mathlib.Algebra.BigOperators.Field

/-!
# Matrix certificates for the finite-rank capture hypotheses

The capture lemma of [FiniteRankCapture](FiniteRankCapture.lean) takes its constants through
form statements. Here they follow from positivity of explicit matrices, which the exact checks
of `PDE.Numerics.Certificates` certify.

- `capture_matrix_of_quadForm_nonneg`: the hypothesis of `capture_bound_of_matrix` (paper
  (4.17)) from positive semidefiniteness of `K₆ B - A + (A C) Λ⁻¹ (A C)ᵀ`.
- The angle bound `E(∑ (bⱼ / μⱼ) rⱼ) ≤ ε₄² E(∑ bⱼ ψ̄ⱼ)` of `form_sq_le_of_residual`, in two forms.
  `form_residual_le_of_appendBlocks` takes the block matrix
  `[[B, -R Λ⁻¹], [-Λ⁻¹ Rᵀ, ε₄² G_E]] ⪰ 0` on `Fin (N + m)`, where `B` is the energy Gram matrix
  of the trial family, `R k j = E(rⱼ, ψₖ)` and `G_E` the energy Gram matrix of the captured
  modes; it needs no inverse of `B` and is the exact Loewner condition
  `Λ⁻¹ Rᵀ B⁻¹ R Λ⁻¹ ≤ ε₄² G_E` when the residuals lie in the span of the trial family.
  `form_residual_le_of_gram_lower` takes residual norms `ρⱼ` and a lower bound `τ_E` for the
  smallest eigenvalue of `G_E`, with `ε₄² = ∑ⱼ (ρⱼ / |μⱼ|)² / τ_E`.
-/

@[expose] public section

open Finset Matrix CAS.Analysis.Matrix
open scoped Matrix

namespace PDE.Analysis.Operator

variable {H : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]

/-- The `K₆` hypothesis of `capture_bound_of_matrix` from positive semidefiniteness of
`K₆ B - A + (A C) Λ⁻¹ (A C)ᵀ`, for any matrices `A`, `B`. -/
theorem capture_matrix_of_quadForm_nonneg {N m : ℕ} (A Bm : Matrix (Fin N) (Fin N) ℝ)
    (C : Fin N → Fin m → ℝ) (μ : Fin m → ℝ) (K₆ : ℝ)
    (hK : ∀ c : Fin N → ℝ, 0 ≤ ∑ i, ∑ j, (K₆ * Bm i j - A i j +
      ∑ l, (A * Matrix.of C) i l * (A * Matrix.of C) j l / μ l) * c i * c j) :
    ∀ c : Fin N → ℝ, c ⬝ᵥ A *ᵥ c - ∑ j, (c ᵥ* (A * Matrix.of C)) j ^ 2 / μ j ≤
      K₆ * (c ⬝ᵥ Bm *ᵥ c) := by
  intro c
  set P : Matrix (Fin N) (Fin m) ℝ := A * Matrix.of C
  have h := hK c
  have hsq : ∑ i, ∑ j, (∑ l, P i l * P j l / μ l) * c i * c j =
      ∑ l, (c ᵥ* P) l ^ 2 / μ l := by
    have hv : ∀ l, (c ᵥ* P) l = ∑ i, c i * P i l := fun l ↦ rfl
    simp only [hv]
    calc ∑ i, ∑ j, (∑ l, P i l * P j l / μ l) * c i * c j
        = ∑ i, ∑ j, ∑ l, P i l * P j l / μ l * c i * c j := by simp only [sum_mul]
      _ = ∑ l, ∑ i, ∑ j, P i l * P j l / μ l * c i * c j :=
          (sum_congr rfl fun i _ ↦ sum_comm).trans sum_comm
      _ = ∑ l, (∑ i, c i * P i l) ^ 2 / μ l := by
          refine sum_congr rfl fun l _ ↦ ?_
          rw [sq, sum_mul_sum, sum_div]
          refine sum_congr rfl fun i _ ↦ ?_
          rw [sum_div]
          exact sum_congr rfl fun j _ ↦ by ring
  have hsplit : ∑ i, ∑ j, (K₆ * Bm i j - A i j + ∑ l, P i l * P j l / μ l) * c i * c j =
      K₆ * ∑ i, ∑ j, Bm i j * c i * c j - ∑ i, ∑ j, A i j * c i * c j +
        ∑ i, ∑ j, (∑ l, P i l * P j l / μ l) * c i * c j := by
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
  rw [hsplit, hsq, sum_sum_mul_mul_eq_dotProduct_mulVec A c,
    sum_sum_mul_mul_eq_dotProduct_mulVec Bm c] at h
  linarith

/-- **Angle bound from a block certificate.** If the residuals lie in the span of the trial
family `ψ`, `R k j = E(rⱼ, ψₖ)`, and
`cᵀ B c - 2 ∑ cₖ R k j (bⱼ / μⱼ) + ε₄² bᵀ G_E b ≥ 0` for all `c` and `b`, then
`E(∑ (bⱼ / μⱼ) rⱼ) ≤ ε₄² E(∑ bⱼ ψ̄ⱼ)`. -/
theorem form_residual_le_of_block {N m : ℕ} (Eform : H →L[ℝ] H →L[ℝ] ℝ) (ψ : Fin N → H)
    (ψbar r : Fin m → H) (μ : Fin m → ℝ)
    (hr : ∀ j, r j ∈ Submodule.span ℝ (Set.range ψ)) (R : Fin N → Fin m → ℝ)
    (hR : ∀ k j, Eform (r j) (ψ k) = R k j) {ε₄ : ℝ}
    (hblock : ∀ (c : Fin N → ℝ) (b : Fin m → ℝ),
      0 ≤ ∑ i, ∑ k, formMatrix Eform ψ ψ i k * c i * c k
        - 2 * ∑ k, ∑ j, c k * R k j * (b j / μ j)
        + ε₄ ^ 2 * ∑ i, ∑ j, formMatrix Eform ψbar ψbar i j * b i * b j) (b : Fin m → ℝ) :
    Eform (∑ j, (b j / μ j) • r j) (∑ j, (b j / μ j) • r j) ≤
      ε₄ ^ 2 * Eform (∑ j, b j • ψbar j) (∑ j, b j • ψbar j) := by
  have hX : ∀ j, ∃ x : Fin N → ℝ, ∑ k, x k • ψ k = r j :=
    fun j ↦ (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hr j)
  choose X hX using hX
  set a : Fin m → ℝ := fun j ↦ b j / μ j
  set y : Fin N → ℝ := fun k ↦ ∑ j, a j * X j k
  have hy : ∑ j, a j • r j = ∑ k, y k • ψ k := by
    simp only [← hX, smul_sum, smul_smul, y, sum_smul]
    exact sum_comm
  have hE1 : Eform (∑ j, a j • r j) (∑ j, a j • r j) =
      ∑ i, ∑ k, formMatrix Eform ψ ψ i k * y i * y k := by
    rw [hy, form_sum_smul_sum_smul, sum_sum_mul_mul_eq_dotProduct_mulVec]
  have hE2 : Eform (∑ j, a j • r j) (∑ j, a j • r j) = ∑ k, ∑ j, y k * R k j * a j := by
    calc Eform (∑ j, a j • r j) (∑ j, a j • r j) =
          Eform (∑ j, a j • r j) (∑ k, y k • ψ k) := by rw [← hy]
      _ = ∑ k, ∑ j, y k * R k j * a j := by
          rw [form_sum_smul_right]
          refine sum_congr rfl fun k _ ↦ ?_
          rw [form_sum_smul_left, mul_sum]
          exact sum_congr rfl fun j _ ↦ by rw [hR]; ring
  have h := hblock y b
  have hRHS : Eform (∑ j, b j • ψbar j) (∑ j, b j • ψbar j) =
      ∑ i, ∑ j, formMatrix Eform ψbar ψbar i j * b i * b j := by
    rw [form_sum_smul_sum_smul, ← sum_sum_mul_mul_eq_dotProduct_mulVec]
  rw [hRHS]
  have h' : Eform (∑ j, a j • r j) (∑ j, a j • r j) ≤
      ε₄ ^ 2 * ∑ i, ∑ j, formMatrix Eform ψbar ψbar i j * b i * b j := by
    linarith
  simpa only [a] using h'

/-- **Angle bound from the block matrix on `Fin (N + m)`.** Positive semidefiniteness of
`[[B, -R Λ⁻¹], [-Λ⁻¹ Rᵀ, ε₄² G_E]]` (`appendBlocks`), as certified by the packed `LDLᵀ` check of
size `N + m`, gives the hypothesis of `form_sq_le_of_residual`. -/
theorem form_residual_le_of_appendBlocks {N m : ℕ} (Eform : H →L[ℝ] H →L[ℝ] ℝ)
    (ψ : Fin N → H) (ψbar r : Fin m → H) (μ : Fin m → ℝ)
    (hr : ∀ j, r j ∈ Submodule.span ℝ (Set.range ψ)) (R : Fin N → Fin m → ℝ)
    (hR : ∀ k j, Eform (r j) (ψ k) = R k j) {ε₄ : ℝ}
    (hpsd : ∀ z : Fin (N + m) → ℝ, 0 ≤ ∑ i, ∑ j,
      appendBlocks (formMatrix Eform ψ ψ) (fun k j ↦ -(R k j / μ j))
        (fun i j ↦ ε₄ ^ 2 * formMatrix Eform ψbar ψbar i j) i j * z i * z j)
    (b : Fin m → ℝ) :
    Eform (∑ j, (b j / μ j) • r j) (∑ j, (b j / μ j) • r j) ≤
      ε₄ ^ 2 * Eform (∑ j, b j • ψbar j) (∑ j, b j • ψbar j) := by
  refine form_residual_le_of_block Eform ψ ψbar r μ hr R hR (fun c b' ↦ ?_) b
  have h := hpsd (Fin.append c b')
  rw [quadForm_appendBlocks (formMatrix Eform ψ ψ) (fun k j ↦ -(R k j / μ j))
    (fun i j ↦ ε₄ ^ 2 * formMatrix Eform ψbar ψbar i j) c b'] at h
  have hcross : ∑ i, ∑ j, c i * -(R i j / μ j) * b' j =
      -∑ k, ∑ j, c k * R k j * (b' j / μ j) := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun k _ ↦ by
      rw [← sum_neg_distrib]; exact sum_congr rfl fun j _ ↦ by ring
  have hD : ∑ i, ∑ j, ε₄ ^ 2 * formMatrix Eform ψbar ψbar i j * b' i * b' j =
      ε₄ ^ 2 * ∑ i, ∑ j, formMatrix Eform ψbar ψbar i j * b' i * b' j := by
    rw [mul_sum]
    exact sum_congr rfl fun i _ ↦ by
      rw [mul_sum]; exact sum_congr rfl fun j _ ↦ by ring
  rw [hcross, hD] at h
  linarith

/-- **Angle bound from residual norms.** With `E(rⱼ) ≤ ρⱼ²` and `τ_E |b|² ≤ bᵀ G_E b`, the
hypothesis of `form_sq_le_of_residual` holds with `ε₄² = ∑ⱼ (ρⱼ / |μⱼ|)² / τ_E`. -/
theorem form_residual_le_of_gram_lower {m : ℕ} (Eform : H →L[ℝ] H →L[ℝ] ℝ)
    (hEsymm : ∀ f g, Eform f g = Eform g f) (hEnonneg : ∀ f, 0 ≤ Eform f f)
    (ψbar r : Fin m → H) (μ ρ : Fin m → ℝ) (hρ0 : ∀ j, 0 ≤ ρ j)
    (hρ : ∀ j, Eform (r j) (r j) ≤ ρ j ^ 2) {τE : ℝ} (hτE : 0 < τE)
    (hGE : ∀ b : Fin m → ℝ, τE * ∑ i, b i ^ 2 ≤
      ∑ i, ∑ j, formMatrix Eform ψbar ψbar i j * b i * b j) (b : Fin m → ℝ) :
    Eform (∑ j, (b j / μ j) • r j) (∑ j, (b j / μ j) • r j) ≤
      (∑ j, (ρ j / |μ j|) ^ 2) / τE * Eform (∑ j, b j • ψbar j) (∑ j, b j • ψbar j) := by
  have h1 := form_sum_smul_self_le_sq Eform hEsymm hEnonneg r ρ hρ0 hρ (fun j ↦ b j / μ j)
  have hw : ∑ i, |b i / μ i| * ρ i = ∑ i, |b i| * (ρ i / |μ i|) := by
    refine sum_congr rfl fun i _ ↦ ?_
    rw [abs_div]
    by_cases h : μ i = 0
    · simp [h]
    · field_simp
  have hcs : (∑ i, |b i| * (ρ i / |μ i|)) ^ 2 ≤ (∑ i, b i ^ 2) * ∑ i, (ρ i / |μ i|) ^ 2 := by
    have h := sum_mul_sq_le_sq_mul_sq univ (fun i ↦ |b i|) (fun i ↦ ρ i / |μ i|)
    simpa only [sq_abs] using h
  have hG := hGE b
  have hRHS : Eform (∑ j, b j • ψbar j) (∑ j, b j • ψbar j) =
      ∑ i, ∑ j, formMatrix Eform ψbar ψbar i j * b i * b j := by
    rw [form_sum_smul_sum_smul, ← sum_sum_mul_mul_eq_dotProduct_mulVec]
  rw [hRHS]
  calc Eform (∑ j, (b j / μ j) • r j) (∑ j, (b j / μ j) • r j)
      ≤ (∑ i, |b i| * (ρ i / |μ i|)) ^ 2 := by rw [← hw]; exact h1
    _ ≤ (∑ i, b i ^ 2) * ∑ i, (ρ i / |μ i|) ^ 2 := hcs
    _ ≤ (∑ i, ∑ j, formMatrix Eform ψbar ψbar i j * b i * b j) / τE *
          ∑ i, (ρ i / |μ i|) ^ 2 := by
        have hW : 0 ≤ ∑ i, (ρ i / |μ i|) ^ 2 := sum_nonneg fun i _ ↦ sq_nonneg _
        have hb : ∑ i, b i ^ 2 ≤ (∑ i, ∑ j, formMatrix Eform ψbar ψbar i j * b i * b j) / τE := by
          rw [le_div_iff₀ hτE]
          linarith
        exact mul_le_mul_of_nonneg_right hb hW
    _ = (∑ j, (ρ j / |μ j|) ^ 2) / τE *
          ∑ i, ∑ j, formMatrix Eform ψbar ψbar i j * b i * b j := by ring

end PDE.Analysis.Operator
