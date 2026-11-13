/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2MeshNodes
public import PDE.Analysis.Approximation.BilinearInterpolation
public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Calculus

/-!
# Quadratic forms of matrices of tables on the cells of a mesh

A finite sum of squared tables `∑ᵢ Tᵢ(β, θ)²` exceeds its bilinear interpolant on a cell
`[a, b] × [c, e]` by at most
`2 ∑ᵢ (μ₁₀² + μ₀₀ μ₂₀) (b - a)² / 8 + 2 ∑ᵢ (μ₀₁² + μ₀₀ μ₀₂) (e - c)² / 8` in the coefficient
moments `μ_{ab}(Tᵢ)` (`sum_sq_eval_le_of_cell`), so a bound at the four
vertices bounds the sum on the cell. For a matrix `G` of tables and a vector `u`, the quadratic
form `Φ(β, θ, u) = ∑ᵢ (∑ₖ uₖ Gᵢₖ)²` is such a sum, and the moments of its rows are at most `|u|`
times bounds `R i a b` of the Euclidean norms of the moments of the rows of `G`; the cell bound is
then `|u|² cellError R (b - a) (e - c)` (`quadForm_le_of_cell`).

When every entry of `G` has the parities `e₀` about `β = 0` and `e₁` about `β = π/2`, and the
angular reflections act by signs, every point of the plane is a point of the quadrant
`[0, π/2]²` up to signs of `u` (`exists_quadrant_quadForm`), so a cover of the quadrant by cells
with bounded vertices bounds the form everywhere (`quadForm_le_of_cover`).
-/

@[expose] public noncomputable section

namespace PDE.Analysis.TrigPoly2

open Finset Set PDE.Analysis.Approximation

variable {Mβ Mθ : ℕ}

/-! ### Sums of squares on a cell -/

/-- The bound of the second `β`-derivative of a sum of squared tables. -/
def sqSumβBound {ι : Type*} [Fintype ι] (T : ι → TrigPoly2 Mβ Mθ ℝ) : ℝ :=
  2 * ∑ i, ((T i).moment 1 0 ^ 2 + (T i).moment 0 0 * (T i).moment 2 0)

/-- The bound of the second `θ`-derivative of a sum of squared tables. -/
def sqSumθBound {ι : Type*} [Fintype ι] (T : ι → TrigPoly2 Mβ Mθ ℝ) : ℝ :=
  2 * ∑ i, ((T i).moment 0 1 ^ 2 + (T i).moment 0 0 * (T i).moment 0 2)

/-- **A sum of squared tables on a cell.** A bound `m` at the four vertices of `[a, b] × [c, e]`
gives `m` plus the interpolation errors of the two pure second derivatives on the whole cell. -/
theorem sum_sq_eval_le_of_cell {ι : Type*} [Fintype ι] (T : ι → TrigPoly2 Mβ Mθ ℝ)
    {a b c e m : ℝ} (hab : a < b) (hce : c < e)
    (hac : ∑ i, (T i).eval a c ^ 2 ≤ m) (hae : ∑ i, (T i).eval a e ^ 2 ≤ m)
    (hbc : ∑ i, (T i).eval b c ^ 2 ≤ m) (hbe : ∑ i, (T i).eval b e ^ 2 ≤ m)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c e) :
    ∑ i, (T i).eval x y ^ 2 ≤
      m + sqSumβBound T * (b - a) ^ 2 / 8 + sqSumθBound T * (e - c) ^ 2 / 8 := by
  set f : ℝ → ℝ → ℝ := fun u w ↦ ∑ i, (T i).eval u w ^ 2
  have hfx : ∀ u w, HasDerivAt (fun z ↦ f z w)
      (∑ i, 2 * ((T i).eval u w * (T i).dβ.eval u w)) u := fun u w ↦ by
    refine HasDerivAt.fun_sum fun i _ ↦ ?_
    convert (hasDerivAt_eval_β (T i) u w).pow 2 using 1
    ring
  have hfxx : ∀ u w, HasDerivAt (fun z ↦ ∑ i, 2 * ((T i).eval z w * (T i).dβ.eval z w))
      (∑ i, 2 * ((T i).dβ.eval u w * (T i).dβ.eval u w +
        (T i).eval u w * (T i).dβ.dβ.eval u w)) u := fun u w ↦ by
    refine HasDerivAt.fun_sum fun i _ ↦ ?_
    exact ((hasDerivAt_eval_β (T i) u w).mul (hasDerivAt_eval_β (T i).dβ u w)).const_mul 2
  have hfy : ∀ u w, HasDerivAt (f u) (∑ i, 2 * ((T i).eval u w * (T i).dθ.eval u w)) w :=
    fun u w ↦ by
    refine HasDerivAt.fun_sum fun i _ ↦ ?_
    convert (hasDerivAt_eval_θ (T i) u w).pow 2 using 1
    ring
  have hfyy : ∀ u w, HasDerivAt (fun z ↦ ∑ i, 2 * ((T i).eval u z * (T i).dθ.eval u z))
      (∑ i, 2 * ((T i).dθ.eval u w * (T i).dθ.eval u w +
        (T i).eval u w * (T i).dθ.dθ.eval u w)) w := fun u w ↦ by
    refine HasDerivAt.fun_sum fun i _ ↦ ?_
    exact ((hasDerivAt_eval_θ (T i) u w).mul (hasDerivAt_eval_θ (T i).dθ u w)).const_mul 2
  have hbx : ∀ u w, |∑ i, 2 * ((T i).dβ.eval u w * (T i).dβ.eval u w +
      (T i).eval u w * (T i).dβ.dβ.eval u w)| ≤ sqSumβBound T := fun u w ↦ by
    unfold sqSumβBound
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ ?_)
    have := abs_two_mul_add_le (abs_eval_dβ_le (T i) u w) (abs_eval_dβ_le (T i) u w)
      (abs_eval_le_moment (T i) u w) (abs_eval_dβ_dβ_le (T i) u w)
    rw [sq]
    exact this
  have hby : ∀ u w, |∑ i, 2 * ((T i).dθ.eval u w * (T i).dθ.eval u w +
      (T i).eval u w * (T i).dθ.dθ.eval u w)| ≤ sqSumθBound T := fun u w ↦ by
    unfold sqSumθBound
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ ?_)
    have := abs_two_mul_add_le (abs_eval_dθ_le (T i) u w) (abs_eval_dθ_le (T i) u w)
      (abs_eval_le_moment (T i) u w) (abs_eval_dθ_dθ_le (T i) u w)
    rw [sq]
    exact this
  have hcont : ∀ w, Continuous fun z ↦ f z w := fun w ↦
    continuous_iff_continuousAt.2 fun z ↦ (hfx z w).continuousAt
  have hcont' : ∀ u, Continuous (f u) := fun u ↦
    continuous_iff_continuousAt.2 fun z ↦ (hfy u z).continuousAt
  have herr := abs_sub_bilinearInterpolant_le (f := f)
    (fx := fun u w ↦ ∑ i, 2 * ((T i).eval u w * (T i).dβ.eval u w))
    (fxx := fun u w ↦ ∑ i, 2 * ((T i).dβ.eval u w * (T i).dβ.eval u w +
      (T i).eval u w * (T i).dβ.dβ.eval u w))
    (fy := fun u w ↦ ∑ i, 2 * ((T i).eval u w * (T i).dθ.eval u w))
    (fyy := fun u w ↦ ∑ i, 2 * ((T i).dθ.eval u w * (T i).dθ.eval u w +
      (T i).eval u w * (T i).dθ.dθ.eval u w))
    hab hce (fun w _ ↦ (hcont w).continuousOn) (fun w _ u _ ↦ hfx u w)
    (fun w _ u _ ↦ hfxx u w) (fun w _ u _ ↦ hbx u w) (fun u _ ↦ (hcont' u).continuousOn)
    (fun u _ w _ ↦ hfy u w) (fun u _ w _ ↦ hfyy u w) (fun u _ w _ ↦ hby u w) hx hy
  have hint := bilinearInterpolant_le (f := f) hab hce hx hy hac hae hbc hbe
  have := (abs_le.mp herr).2
  change f x y ≤ _
  linarith

/-! ### Quadratic forms on a cell -/

variable {d d' : ℕ}

/-- The cell error of a matrix of tables with moment bounds `R`, for cell widths `h₁`, `h₂`. -/
def cellError (R : Fin d → ℕ → ℕ → ℝ) (h₁ h₂ : ℝ) : ℝ :=
  (2 * ∑ i, (R i 1 0 ^ 2 + R i 0 0 * R i 2 0)) * h₁ ^ 2 / 8 +
    (2 * ∑ i, (R i 0 1 ^ 2 + R i 0 0 * R i 0 2)) * h₂ ^ 2 / 8

theorem cellError_nonneg {R : Fin d → ℕ → ℕ → ℝ} (hR0 : ∀ i a b, 0 ≤ R i a b) (h₁ h₂ : ℝ) :
    0 ≤ cellError R h₁ h₂ := by
  unfold cellError
  have h1 : 0 ≤ ∑ i, (R i 1 0 ^ 2 + R i 0 0 * R i 2 0) :=
    sum_nonneg fun i _ ↦ add_nonneg (sq_nonneg _) (mul_nonneg (hR0 _ _ _) (hR0 _ _ _))
  have h2 : 0 ≤ ∑ i, (R i 0 1 ^ 2 + R i 0 0 * R i 0 2) :=
    sum_nonneg fun i _ ↦ add_nonneg (sq_nonneg _) (mul_nonneg (hR0 _ _ _) (hR0 _ _ _))
  positivity

/-- **The quadratic form of a matrix of tables on a cell.** With moment bounds
`∑ₖ μ_{ab}(Gᵢₖ)² ≤ R i a b ²`, a bound `m |u|²` at the four vertices of `[a, b] × [c, e]` gives
`(m + cellError R (b - a) (e - c)) |u|²` on the cell. -/
theorem quadForm_le_of_cell (G : Fin d → Fin d' → TrigPoly2 Mβ Mθ ℝ)
    (R : Fin d → ℕ → ℕ → ℝ) (hR0 : ∀ i a b, 0 ≤ R i a b)
    (hR : ∀ i a b, ∑ k, ((G i k).moment a b) ^ 2 ≤ R i a b ^ 2) {a b c e m : ℝ}
    (hab : a < b) (hce : c < e) (u : Fin d' → ℝ)
    (hac : quadForm G a c u ≤ m * ∑ k, u k ^ 2) (hae : quadForm G a e u ≤ m * ∑ k, u k ^ 2)
    (hbc : quadForm G b c u ≤ m * ∑ k, u k ^ 2) (hbe : quadForm G b e u ≤ m * ∑ k, u k ^ 2)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c e) :
    quadForm G x y u ≤ (m + cellError R (b - a) (e - c)) * ∑ k, u k ^ 2 := by
  set T : Fin d → TrigPoly2 Mβ Mθ ℝ := fun i ↦ ∑ k, u k • G i k
  have hT : ∀ β θ, quadForm G β θ u = ∑ i, (T i).eval β θ ^ 2 := by
    intro β θ
    unfold quadForm
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [T, eval_sum, eval_smul, Algebra.algebraMap_self, RingHom.id_apply]
  set S := ∑ k, u k ^ 2
  have hS : 0 ≤ S := sum_nonneg fun _ _ ↦ sq_nonneg _
  have hmom : ∀ i a b, (T i).moment a b ≤ √S * R i a b := fun i a b ↦
    moment_sum_smul_le u (G i) (hR0 i a b) a b (hR i a b)
  have hsq : ∀ i a b, (T i).moment a b ^ 2 ≤ S * R i a b ^ 2 := fun i a b ↦ by
    calc (T i).moment a b ^ 2 ≤ (√S * R i a b) ^ 2 :=
          pow_le_pow_left₀ (moment_nonneg _ a b) (hmom i a b) 2
      _ = S * R i a b ^ 2 := by rw [mul_pow, Real.sq_sqrt hS]
  have hprod : ∀ i a b a' b', (T i).moment a b * (T i).moment a' b' ≤
      S * (R i a b * R i a' b') := fun i a b a' b' ↦ by
    calc (T i).moment a b * (T i).moment a' b' ≤ (√S * R i a b) * (√S * R i a' b') :=
          mul_le_mul (hmom i a b) (hmom i a' b') (moment_nonneg _ _ _)
            (mul_nonneg (Real.sqrt_nonneg _) (hR0 i a b))
      _ = S * (R i a b * R i a' b') := by
          rw [show √S * R i a b * (√S * R i a' b') = (√S * √S) * (R i a b * R i a' b') by ring,
            Real.mul_self_sqrt hS]
  have hβb : sqSumβBound T ≤ S * (2 * ∑ i, (R i 1 0 ^ 2 + R i 0 0 * R i 2 0)) := by
    unfold sqSumβBound
    rw [mul_sum, mul_sum, mul_sum]
    refine sum_le_sum fun i _ ↦ ?_
    nlinarith [hsq i 1 0, hprod i 0 0 2 0]
  have hθb : sqSumθBound T ≤ S * (2 * ∑ i, (R i 0 1 ^ 2 + R i 0 0 * R i 0 2)) := by
    unfold sqSumθBound
    rw [mul_sum, mul_sum, mul_sum]
    refine sum_le_sum fun i _ ↦ ?_
    nlinarith [hsq i 0 1, hprod i 0 0 0 2]
  rw [hT] at hac hae hbc hbe ⊢
  have h := sum_sq_eval_le_of_cell T hab hce hac hae hbc hbe hx hy
  have h1 : sqSumβBound T * (b - a) ^ 2 / 8 ≤
      S * (2 * ∑ i, (R i 1 0 ^ 2 + R i 0 0 * R i 2 0)) * (b - a) ^ 2 / 8 := by
    have := mul_le_mul_of_nonneg_right hβb (sq_nonneg (b - a))
    linarith
  have h2 : sqSumθBound T * (e - c) ^ 2 / 8 ≤
      S * (2 * ∑ i, (R i 0 1 ^ 2 + R i 0 0 * R i 0 2)) * (e - c) ^ 2 / 8 := by
    have := mul_le_mul_of_nonneg_right hθb (sq_nonneg (e - c))
    linarith
  unfold cellError
  nlinarith

/-! ### Reduction to the quadrant -/

/-- Every real number is, up to multiples of `2π`, a number of `[0, π/2]` or its reflection
about `0`, `π/2` or `π`. -/
theorem exists_quadrant_real (x : ℝ) : ∃ x' ∈ Icc 0 (Real.pi / 2), ∃ q : ℤ,
    x = x' + q * (2 * Real.pi) ∨ x = -x' + q * (2 * Real.pi) ∨
      x = Real.pi - x' + q * (2 * Real.pi) ∨ x = Real.pi + x' + q * (2 * Real.pi) := by
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  set r := toIcoMod hp 0 x
  have hr : r ∈ Ico 0 (0 + 2 * Real.pi) := toIcoMod_mem_Ico hp 0 x
  rw [zero_add] at hr
  set q := toIcoDiv hp 0 x
  have hx : x = r + q * (2 * Real.pi) := by
    have := toIcoMod_add_toIcoDiv_zsmul hp 0 x
    rw [zsmul_eq_mul] at this
    linarith
  have hπ := Real.pi_pos
  rcases le_or_gt r (Real.pi / 2) with h1 | h1
  · exact ⟨r, ⟨hr.1, h1⟩, q, Or.inl hx⟩
  rcases le_or_gt r Real.pi with h2 | h2
  · exact ⟨Real.pi - r, ⟨by linarith, by linarith⟩, q, Or.inr (Or.inr (Or.inl (by linarith)))⟩
  rcases le_or_gt r (3 * Real.pi / 2) with h3 | h3
  · exact ⟨r - Real.pi, ⟨by linarith, by linarith⟩, q, Or.inr (Or.inr (Or.inr (by linarith)))⟩
  · refine ⟨2 * Real.pi - r, ⟨by linarith [hr.2], by linarith⟩, q + 1, Or.inr (Or.inl ?_)⟩
    push_cast
    linarith

variable (G : Fin d → Fin d' → TrigPoly2 Mβ Mθ ℝ)

/-- **Reduction of a quadratic form to the quadrant.** If all entries have the parities `e₀`
about `β = 0` and `e₁` about `β = π/2` and the angular reflections act by signs, the form at any
point equals the form at a point of `[0, π/2]²` for a vector with the same norm. -/
theorem exists_quadrant_quadForm {e₀ e₁ : Bool} (hβ0 : ∀ i k, (G i k).ParityAtβ 0 e₀)
    (hβπ : ∀ i k, (G i k).ParityAtβ (Real.pi / 2) e₁)
    {σ τ : Fin d → ℝ} {σ' τ' : Fin d' → ℝ} (hσ : ∀ i, σ i ^ 2 = 1) (hσ' : ∀ k, σ' k ^ 2 = 1)
    (hτ : ∀ i, τ i ^ 2 = 1) (hτ' : ∀ k, τ' k ^ 2 = 1)
    (hθ0 : ∀ i k β θ, (G i k).eval β (-θ) = σ i * σ' k * (G i k).eval β θ)
    (hθπ : ∀ i k β θ, (G i k).eval β (Real.pi - θ) = τ i * τ' k * (G i k).eval β θ)
    (β θ : ℝ) (u : Fin d' → ℝ) : ∃ β' ∈ Icc 0 (Real.pi / 2), ∃ θ' ∈ Icc 0 (Real.pi / 2),
      ∃ u' : Fin d' → ℝ, ∑ k, u' k ^ 2 = ∑ k, u k ^ 2 ∧
        quadForm G β θ u = quadForm G β' θ' u' := by
  have hs₀ : (cond e₀ 1 (-1) : ℝ) ^ 2 = 1 := by cases e₀ <;> norm_num
  have hs₁ : (cond e₁ 1 (-1) : ℝ) ^ 2 = 1 := by cases e₁ <;> norm_num
  -- the reduction in `β` changes all entries by one sign
  obtain ⟨β', hβ', qβ, hcβ⟩ := exists_quadrant_real β
  have hβred : ∃ s : ℝ, s ^ 2 = 1 ∧ ∀ i k θ,
      (G i k).eval β θ = s * 1 * (G i k).eval β' θ := by
    have ev : ∀ i k x θ, (G i k).eval (-x) θ = cond e₀ 1 (-1) * (G i k).eval x θ :=
      fun i k x θ ↦ by simpa only [mul_zero, zero_sub] using hβ0 i k θ x
    have od : ∀ i k x θ, (G i k).eval (Real.pi - x) θ = cond e₁ 1 (-1) * (G i k).eval x θ :=
      fun i k x θ ↦ by
        have := hβπ i k θ x
        rwa [show 2 * (Real.pi / 2) - x = Real.pi - x by ring] at this
    rcases hcβ with h | h | h | h
    · exact ⟨1, by norm_num, fun i k θ ↦ by rw [h, eval_add_int_mul_two_pi_β]; ring⟩
    · exact ⟨_, hs₀, fun i k θ ↦ by rw [h, eval_add_int_mul_two_pi_β, ev]; ring⟩
    · exact ⟨_, hs₁, fun i k θ ↦ by rw [h, eval_add_int_mul_two_pi_β, od]; ring⟩
    · refine ⟨cond e₁ 1 (-1) * cond e₀ 1 (-1), by rw [mul_pow, hs₁, hs₀, one_mul],
        fun i k θ ↦ ?_⟩
      rw [h, show Real.pi + β' = Real.pi - -β' by ring, eval_add_int_mul_two_pi_β, od, ev]
      ring
  -- the reduction in `θ` changes the rows and columns by signs
  obtain ⟨θ', hθ', qθ, hcθ⟩ := exists_quadrant_real θ
  have hθred : ∃ ρ : Fin d' → ℝ, (∀ k, ρ k ^ 2 = 1) ∧ ∃ ς : Fin d → ℝ, (∀ i, ς i ^ 2 = 1) ∧
      ∀ i k, (G i k).eval β' θ = ς i * ρ k * (G i k).eval β' θ' := by
    rcases hcθ with h | h | h | h
    · exact ⟨fun _ ↦ 1, fun _ ↦ by norm_num, fun _ ↦ 1, fun _ ↦ by norm_num,
        fun i k ↦ by rw [h, eval_add_int_mul_two_pi_θ]; ring⟩
    · exact ⟨σ', hσ', σ, hσ, fun i k ↦ by rw [h, eval_add_int_mul_two_pi_θ, hθ0]⟩
    · exact ⟨τ', hτ', τ, hτ, fun i k ↦ by rw [h, eval_add_int_mul_two_pi_θ, hθπ]⟩
    · refine ⟨fun k ↦ τ' k * σ' k, fun k ↦ by rw [mul_pow, hτ', hσ', one_mul],
        fun i ↦ τ i * σ i, fun i ↦ by rw [mul_pow, hτ, hσ, one_mul], fun i k ↦ ?_⟩
      rw [h, show Real.pi + θ' = Real.pi - -θ' by ring, eval_add_int_mul_two_pi_θ, hθπ, hθ0]
      ring
  obtain ⟨s, hs, hsβ⟩ := hβred
  obtain ⟨ρ, hρ, ς, hς, hρθ⟩ := hθred
  refine ⟨β', hβ', θ', hθ', fun k ↦ ρ k * (1 * u k), ?_, ?_⟩
  · exact sum_congr rfl fun k _ ↦ by simp only [one_mul, mul_pow, hρ k]
  · rw [quadForm_sign G (σ := fun _ ↦ s) (σ' := fun _ ↦ 1) (fun _ ↦ hs)
      (fun i k ↦ hsβ i k θ) u, quadForm_sign G hς hρθ]

/-- **A quadratic form from a cover of the quadrant.** If every point of `[0, π/2]²` lies in a
cell whose vertices bound the form by `m` minus the cell error, the form is at most `m |u|²`
everywhere. -/
theorem quadForm_le_of_cover {e₀ e₁ : Bool} (hβ0 : ∀ i k, (G i k).ParityAtβ 0 e₀)
    (hβπ : ∀ i k, (G i k).ParityAtβ (Real.pi / 2) e₁)
    {σ τ : Fin d → ℝ} {σ' τ' : Fin d' → ℝ} (hσ : ∀ i, σ i ^ 2 = 1) (hσ' : ∀ k, σ' k ^ 2 = 1)
    (hτ : ∀ i, τ i ^ 2 = 1) (hτ' : ∀ k, τ' k ^ 2 = 1)
    (hθ0 : ∀ i k β θ, (G i k).eval β (-θ) = σ i * σ' k * (G i k).eval β θ)
    (hθπ : ∀ i k β θ, (G i k).eval β (Real.pi - θ) = τ i * τ' k * (G i k).eval β θ)
    (R : Fin d → ℕ → ℕ → ℝ) (hR0 : ∀ i a b, 0 ≤ R i a b)
    (hR : ∀ i a b, ∑ k, ((G i k).moment a b) ^ 2 ≤ R i a b ^ 2) {m : ℝ}
    (hcover : ∀ β ∈ Icc 0 (Real.pi / 2), ∀ θ ∈ Icc 0 (Real.pi / 2), ∃ a b c e : ℝ,
      a < b ∧ c < e ∧ β ∈ Icc a b ∧ θ ∈ Icc c e ∧ ∀ u : Fin d' → ℝ,
        ∀ x ∈ ({a, b} : Set ℝ), ∀ y ∈ ({c, e} : Set ℝ),
          quadForm G x y u ≤ (m - cellError R (b - a) (e - c)) * ∑ k, u k ^ 2)
    (β θ : ℝ) (u : Fin d' → ℝ) : quadForm G β θ u ≤ m * ∑ k, u k ^ 2 := by
  obtain ⟨β', hβ', θ', hθ', u', hu', heq⟩ :=
    exists_quadrant_quadForm G hβ0 hβπ hσ hσ' hτ hτ' hθ0 hθπ β θ u
  obtain ⟨a, b, c, e, hab, hce, hβa, hθc, hv⟩ := hcover β' hβ' θ' hθ'
  have h := quadForm_le_of_cell G R hR0 hR hab hce u'
    (hv u' a (by simp) c (by simp)) (hv u' a (by simp) e (by simp))
    (hv u' b (by simp) c (by simp)) (hv u' b (by simp) e (by simp)) hβa hθc
  rw [heq, ← hu']
  simpa using h

end PDE.Analysis.TrigPoly2
