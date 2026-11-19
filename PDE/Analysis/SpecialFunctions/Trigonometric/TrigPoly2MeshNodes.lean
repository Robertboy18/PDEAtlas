/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Mesh

/-!
# Mesh nodes of a matrix of tables from the nodes of the quadrant

Let `G` be a matrix of tables whose entries are all even in `β` about `0` and odd about `π/2`,
and whose angular reflections act by signs `G_{ik}(β, -θ) = σᵢ σ'ₖ G_{ik}(β, θ)` and
`G_{ik}(β, π - θ) = τᵢ τ'ₖ G_{ik}(β, θ)` with `σᵢ², σ'ₖ², τᵢ², τ'ₖ² = 1`, the frame matrix of the
derivative of an axisymmetric field with parities. The quadratic forms
`Φ(β, θ, u) = ∑ᵢ (∑ₖ uₖ G_{ik}(β, θ))²` then satisfy `Φ ≤ m |u|²` at every node
`(j π / (2N), n π / (2P))`, `j, n ∈ ℤ`, as soon as they do at the nodes of the quadrant
`0 ≤ j ≤ N`, `0 ≤ n ≤ P` (`quadForm_le_of_quadrant`): every node is the image of a quadrant node
under the `2π`-periodicity and the reflections, which change `u` by signs only.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.TrigPoly2

open Finset

variable {Mβ Mθ : ℕ}

/-- Every integer node index is, up to multiples of `4N`, an index of the quadrant or its
reflection about `N`, `2N` or `3N`. -/
theorem exists_quadrant_index {N : ℕ} (hN : 0 < N) (j : ℤ) : ∃ (j' : ℕ) (q : ℤ), j' ≤ N ∧
    (j = 4 * N * q + j' ∨ j = 4 * N * q + 2 * N - j' ∨ j = 4 * N * q + 2 * N + j' ∨
      j = 4 * N * q + 4 * N - j') := by
  set r := j % (4 * N)
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by positivity)
  have hr4 : r < 4 * N := Int.emod_lt_of_pos _ (by positivity)
  have hj : j = 4 * N * (j / (4 * N)) + r := (Int.mul_ediv_add_emod j (4 * N)).symm
  set q := j / (4 * N)
  rcases le_or_gt r N with h1 | h1
  · exact ⟨r.toNat, q, by omega, Or.inl (by omega)⟩
  rcases le_or_gt r (2 * N) with h2 | h2
  · exact ⟨(2 * N - r).toNat, q, by omega, Or.inr (Or.inl (by omega))⟩
  rcases le_or_gt r (3 * N) with h3 | h3
  · exact ⟨(r - 2 * N).toNat, q, by omega, Or.inr (Or.inr (Or.inl (by omega)))⟩
  · exact ⟨(4 * N - r).toNat, q, by omega, Or.inr (Or.inr (Or.inr (by omega)))⟩

/-- A trigonometric polynomial is `2π`-periodic in `β` under integer shifts. -/
theorem eval_add_int_mul_two_pi_β (p : TrigPoly2 Mβ Mθ ℝ) (q : ℤ) (β θ : ℝ) :
    p.eval (β + q * (2 * Real.pi)) θ = p.eval β θ := by
  have hper : Function.Periodic (fun t ↦ p.eval t θ) (2 * Real.pi) :=
    fun t ↦ eval_add_two_pi_β p t θ
  exact hper.int_mul q β

/-- A trigonometric polynomial is `2π`-periodic in `θ` under integer shifts. -/
theorem eval_add_int_mul_two_pi_θ (p : TrigPoly2 Mβ Mθ ℝ) (q : ℤ) (β θ : ℝ) :
    p.eval β (θ + q * (2 * Real.pi)) = p.eval β θ := by
  have hper : Function.Periodic (fun t ↦ p.eval β t) (2 * Real.pi) :=
    fun t ↦ eval_add_two_pi_θ p β t
  exact hper.int_mul q θ

/-- The quadratic form of a matrix of tables. -/
def quadForm {d d' : ℕ} (G : Fin d → Fin d' → TrigPoly2 Mβ Mθ ℝ) (β θ : ℝ) (u : Fin d' → ℝ) :
    ℝ :=
  ∑ i, (∑ k, u k * (G i k).eval β θ) ^ 2

variable {d d' : ℕ} (G : Fin d → Fin d' → TrigPoly2 Mβ Mθ ℝ)

theorem quadForm_sign {σ : Fin d → ℝ} {σ' : Fin d' → ℝ} (hσ : ∀ i, σ i ^ 2 = 1)
    {β β' θ θ' : ℝ} (h : ∀ i k, (G i k).eval β θ = σ i * σ' k * (G i k).eval β' θ')
    (u : Fin d' → ℝ) :
    quadForm G β θ u = quadForm G β' θ' (fun k ↦ σ' k * u k) := by
  unfold quadForm
  refine sum_congr rfl fun i _ ↦ ?_
  have : ∑ k, u k * (G i k).eval β θ = σ i * ∑ k, σ' k * u k * (G i k).eval β' θ' := by
    rw [mul_sum]
    exact sum_congr rfl fun k _ ↦ by rw [h i k]; ring
  rw [this, mul_pow, hσ i, one_mul]

/-- The quadratic form at every node from its values at the nodes of the quadrant. -/
theorem quadForm_le_of_quadrant {N P : ℕ} (hN : 0 < N) (hP : 0 < P)
    (hβ0 : ∀ i k, (G i k).IsEvenAtβ 0) (hβπ : ∀ i k, (G i k).IsOddAtβ (Real.pi / 2))
    {σ τ : Fin d → ℝ} {σ' τ' : Fin d' → ℝ} (hσ : ∀ i, σ i ^ 2 = 1) (hσ' : ∀ k, σ' k ^ 2 = 1)
    (hτ : ∀ i, τ i ^ 2 = 1) (hτ' : ∀ k, τ' k ^ 2 = 1)
    (hθ0 : ∀ i k β θ, (G i k).eval β (-θ) = σ i * σ' k * (G i k).eval β θ)
    (hθπ : ∀ i k β θ, (G i k).eval β (Real.pi - θ) = τ i * τ' k * (G i k).eval β θ)
    {m : ℝ}
    (hq : ∀ j n : ℕ, j ≤ N → n ≤ P → ∀ u : Fin d' → ℝ,
      quadForm G (j * (Real.pi / (2 * N))) (n * (Real.pi / (2 * P))) u ≤ m * ∑ k, u k ^ 2)
    (j n : ℤ) (u : Fin d' → ℝ) :
    quadForm G (j * (Real.pi / (2 * N))) (n * (Real.pi / (2 * P))) u ≤ m * ∑ k, u k ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  -- the reduction in `β` changes the entries by one common sign
  have hβred : ∀ θ, ∃ j' : ℕ, j' ≤ N ∧ ∃ s : ℝ, s ^ 2 = 1 ∧ ∀ i k,
      (G i k).eval (j * (Real.pi / (2 * N))) θ = s * 1 * (G i k).eval (j' * (Real.pi / (2 * N))) θ
      := by
    intro θ
    obtain ⟨j', q, hj', hcase⟩ := exists_quadrant_index hN j
    refine ⟨j', hj', ?_⟩
    have ev : ∀ i k x, (G i k).eval (-x) θ = (G i k).eval x θ := fun i k x ↦ by
      have := hβ0 i k θ x
      simpa only [mul_zero, zero_sub] using this
    have od : ∀ i k x, (G i k).eval (Real.pi - x) θ = -(G i k).eval x θ := fun i k x ↦ by
      have := hβπ i k θ x
      rwa [show 2 * (Real.pi / 2) - x = Real.pi - x by ring] at this
    rcases hcase with h | h | h | h
    · refine ⟨1, by norm_num, fun i k ↦ ?_⟩
      have : (j : ℝ) * (Real.pi / (2 * N)) = j' * (Real.pi / (2 * N)) + q * (2 * Real.pi) := by
        rw [h]; push_cast; field_simp; ring
      rw [this, eval_add_int_mul_two_pi_β]; ring
    · refine ⟨-1, by norm_num, fun i k ↦ ?_⟩
      have : (j : ℝ) * (Real.pi / (2 * N)) =
          (Real.pi - j' * (Real.pi / (2 * N))) + q * (2 * Real.pi) := by
        rw [h]; push_cast; field_simp; ring
      rw [this, eval_add_int_mul_two_pi_β, od]; ring
    · refine ⟨-1, by norm_num, fun i k ↦ ?_⟩
      have : (j : ℝ) * (Real.pi / (2 * N)) =
          (Real.pi - -(j' * (Real.pi / (2 * N)))) + q * (2 * Real.pi) := by
        rw [h]; push_cast; field_simp; ring
      rw [this, eval_add_int_mul_two_pi_β, od, ev]; ring
    · refine ⟨1, by norm_num, fun i k ↦ ?_⟩
      have : (j : ℝ) * (Real.pi / (2 * N)) = -(j' * (Real.pi / (2 * N))) + (q + 1) * (2 * Real.pi)
          := by
        rw [h]; push_cast; field_simp; ring
      have h2 : ((q + 1 : ℤ) : ℝ) = (q : ℝ) + 1 := by push_cast; ring
      rw [this, ← h2, eval_add_int_mul_two_pi_β, ev]; ring
  -- the reduction in `θ` changes `u` by signs
  have hθred : ∀ β, ∃ n' : ℕ, n' ≤ P ∧ ∃ ρ : Fin d' → ℝ, (∀ k, ρ k ^ 2 = 1) ∧
      ∃ ς : Fin d → ℝ, (∀ i, ς i ^ 2 = 1) ∧ ∀ i k,
        (G i k).eval β (n * (Real.pi / (2 * P))) =
          ς i * ρ k * (G i k).eval β (n' * (Real.pi / (2 * P))) := by
    intro β
    obtain ⟨n', q, hn', hcase⟩ := exists_quadrant_index hP n
    refine ⟨n', hn', ?_⟩
    rcases hcase with h | h | h | h
    · refine ⟨fun _ ↦ 1, fun _ ↦ by norm_num, fun _ ↦ 1, fun _ ↦ by norm_num, fun i k ↦ ?_⟩
      have : (n : ℝ) * (Real.pi / (2 * P)) = n' * (Real.pi / (2 * P)) + q * (2 * Real.pi) := by
        rw [h]; push_cast; field_simp; ring
      rw [this, eval_add_int_mul_two_pi_θ]; ring
    · refine ⟨τ', hτ', τ, hτ, fun i k ↦ ?_⟩
      have : (n : ℝ) * (Real.pi / (2 * P)) =
          (Real.pi - n' * (Real.pi / (2 * P))) + q * (2 * Real.pi) := by
        rw [h]; push_cast; field_simp; ring
      rw [this, eval_add_int_mul_two_pi_θ, hθπ]
    · refine ⟨fun k ↦ τ' k * σ' k, fun k ↦ by rw [mul_pow, hτ', hσ', one_mul],
        fun i ↦ τ i * σ i, fun i ↦ by rw [mul_pow, hτ, hσ, one_mul], fun i k ↦ ?_⟩
      have : (n : ℝ) * (Real.pi / (2 * P)) =
          (Real.pi - -(n' * (Real.pi / (2 * P)))) + q * (2 * Real.pi) := by
        rw [h]; push_cast; field_simp; ring
      rw [this, eval_add_int_mul_two_pi_θ, hθπ, hθ0]; ring
    · refine ⟨σ', hσ', σ, hσ, fun i k ↦ ?_⟩
      have : (n : ℝ) * (Real.pi / (2 * P)) = -(n' * (Real.pi / (2 * P))) + (q + 1) * (2 * Real.pi)
          := by
        rw [h]; push_cast; field_simp; ring
      have h2 : ((q + 1 : ℤ) : ℝ) = (q : ℝ) + 1 := by push_cast; ring
      rw [this, ← h2, eval_add_int_mul_two_pi_θ, hθ0]
  obtain ⟨j', hj', s, hs, hjs⟩ := hβred (n * (Real.pi / (2 * P)))
  obtain ⟨n', hn', ρ, hρ, ς, hς, hns⟩ := hθred (j' * (Real.pi / (2 * N)))
  rw [quadForm_sign G (σ := fun _ ↦ s) (σ' := fun _ ↦ 1) (fun _ ↦ hs) hjs u,
    quadForm_sign G hς hns]
  have := hq j' n' hj' hn' (fun k ↦ ρ k * (1 * u k))
  refine this.trans (le_of_eq ?_)
  congr 1
  exact sum_congr rfl fun k _ ↦ by rw [one_mul, mul_pow, hρ k, one_mul]

end PDE.Analysis.TrigPoly2
