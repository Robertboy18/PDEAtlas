/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Moments
public import PDE.Analysis.Calculus.MeshMaximum

/-!
# Sums of squared tables from their values on a mesh

A finite sum of squared trigonometric tables `∑ᵢ Tᵢ(β, θ)²` is `2π`-periodic in both variables,
and its second partial derivatives are bounded by the coefficient moments `μ_{ab}(Tᵢ) =
∑ |c| k^a l^b` of the tables (`TrigPoly2.moment`): for instance
`|∂_β² ∑ Tᵢ²| ≤ 2 ∑ᵢ (μ₁₀(Tᵢ)² + μ₀₀(Tᵢ) μ₂₀(Tᵢ))`. A bound `m` at the nodes
`(j π / (2N), n π / (2P))`, `j, n ∈ ℤ`, therefore gives `m + meshError T N P` everywhere
(`sum_sq_eval_le_of_mesh`), with the mesh error of `PDE.Analysis.le_of_forall_mesh_le`. Moments are
subadditive and absolutely homogeneous (`moment_add_le`, `moment_smul`, `moment_sum_le`), so
linear combinations of tables have explicit bounds.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.TrigPoly2

open Finset

variable {Mβ Mθ : ℕ}

/-! ### Periodicity -/

theorem eval_add_two_pi_β (p : TrigPoly2 Mβ Mθ ℝ) (β θ : ℝ) :
    p.eval (β + 2 * Real.pi) θ = p.eval β θ := by
  unfold eval
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦
    sum_congr rfl fun l _ ↦ ?_
  have h : ((k : ℕ) : ℝ) * (β + 2 * Real.pi) = (k : ℕ) * β + (k : ℕ) * (2 * Real.pi) := by ring
  rw [h]
  fin_cases i <;> simp [trigMode, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]

theorem eval_add_two_pi_θ (p : TrigPoly2 Mβ Mθ ℝ) (β θ : ℝ) :
    p.eval β (θ + 2 * Real.pi) = p.eval β θ := by
  unfold eval
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦
    sum_congr rfl fun l _ ↦ ?_
  have h : ((l : ℕ) : ℝ) * (θ + 2 * Real.pi) = (l : ℕ) * θ + (l : ℕ) * (2 * Real.pi) := by ring
  rw [h]
  fin_cases j <;> simp [trigMode, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]

/-! ### Moments of combinations -/

theorem moment_add_le (p q : TrigPoly2 Mβ Mθ ℝ) (a b : ℕ) :
    (p + q).moment a b ≤ p.moment a b + q.moment a b := by
  unfold moment
  simp only [← sum_add_distrib]
  refine sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ sum_le_sum fun k _ ↦ sum_le_sum fun l _ ↦ ?_
  simp only [coeff_add, Algebra.algebraMap_self, RingHom.id_apply]
  have hk : (0 : ℝ) ≤ (k : ℝ) ^ a * (l : ℝ) ^ b := by positivity
  nlinarith [abs_add_le (p.coeff i j k l) (q.coeff i j k l)]

theorem moment_smul (c : ℝ) (p : TrigPoly2 Mβ Mθ ℝ) (a b : ℕ) :
    (c • p).moment a b = |c| * p.moment a b := by
  unfold moment
  simp only [coeff_smul, Algebra.algebraMap_self, RingHom.id_apply, abs_mul, mul_sum]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦
    sum_congr rfl fun l _ ↦ by ring

theorem moment_sum_le {ι : Type*} (s : Finset ι) (f : ι → TrigPoly2 Mβ Mθ ℝ) (a b : ℕ) :
    (∑ x ∈ s, f x).moment a b ≤ ∑ x ∈ s, (f x).moment a b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [moment]
  | insert x s hx ih =>
    rw [sum_insert hx, sum_insert hx]
    exact (moment_add_le _ _ a b).trans (by linarith)

theorem l1Norm_eq_moment (p : TrigPoly2 Mβ Mθ ℝ) : p.l1Norm = p.moment 0 0 := by
  simpa using l1Norm_iterate_dβ_dθ p 0 0

/-- The moments of a combination `∑ₖ uₖ Gₖ` of tables are at most `|u|` times a bound `R` of
the Euclidean norm of the moments of the tables. -/
theorem moment_sum_smul_le {d : ℕ} (u : Fin d → ℝ) (G : Fin d → TrigPoly2 Mβ Mθ ℝ) {R : ℝ}
    (hR0 : 0 ≤ R) (a b : ℕ) (hR : ∑ k, (G k).moment a b ^ 2 ≤ R ^ 2) :
    (∑ k, u k • G k).moment a b ≤ √(∑ k, u k ^ 2) * R := by
  calc (∑ k, u k • G k).moment a b ≤ ∑ k, (u k • G k).moment a b := moment_sum_le _ _ a b
    _ = ∑ k, |u k| * (G k).moment a b := by simp only [moment_smul]
    _ ≤ √(∑ k, |u k| ^ 2) * √(∑ k, (G k).moment a b ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ √(∑ k, u k ^ 2) * R := by
        simp only [sq_abs]
        exact mul_le_mul_of_nonneg_left
          ((Real.sqrt_le_sqrt hR).trans (Real.sqrt_sq hR0).le) (Real.sqrt_nonneg _)

/-! ### The mesh bound -/

/-- The mesh error of a family of tables with nodes `(j π / (2N), n π / (2P))`. -/
def meshError {ι : Type*} [Fintype ι] (T : ι → TrigPoly2 Mβ Mθ ℝ) (N P : ℕ) : ℝ :=
  (2 * ∑ i, ((T i).moment 1 0 ^ 2 + (T i).moment 0 0 * (T i).moment 2 0)) *
      (Real.pi / (2 * N)) ^ 2 / 8 +
    (2 * ∑ i, ((T i).moment 1 0 * (T i).moment 0 1 + (T i).moment 0 0 * (T i).moment 1 1)) *
      (Real.pi / (2 * N)) * (Real.pi / (2 * P)) / 4 +
    (2 * ∑ i, ((T i).moment 0 1 ^ 2 + (T i).moment 0 0 * (T i).moment 0 2)) *
      (Real.pi / (2 * P)) ^ 2 / 8

/-- A value of a table is at most its moment of order `(0, 0)`. -/
theorem abs_eval_le_moment (p : TrigPoly2 Mβ Mθ ℝ) (β θ : ℝ) :
    |p.eval β θ| ≤ p.moment 0 0 := by
  rw [← l1Norm_eq_moment]
  exact abs_eval_le_l1Norm p β θ

/-- A value of the `β`-derivative is at most the moment of order `(1, 0)`. -/
theorem abs_eval_dβ_le (p : TrigPoly2 Mβ Mθ ℝ) (β θ : ℝ) :
    |p.dβ.eval β θ| ≤ p.moment 1 0 := by
  rw [← l1Norm_iterate_dβ_dθ]
  exact abs_eval_le_l1Norm _ β θ

/-- A value of the `θ`-derivative is at most the moment of order `(0, 1)`. -/
theorem abs_eval_dθ_le (p : TrigPoly2 Mβ Mθ ℝ) (β θ : ℝ) :
    |p.dθ.eval β θ| ≤ p.moment 0 1 := by
  rw [← l1Norm_iterate_dβ_dθ]
  exact abs_eval_le_l1Norm _ β θ

/-- A value of the second `β`-derivative is at most the moment of order `(2, 0)`. -/
theorem abs_eval_dβ_dβ_le (p : TrigPoly2 Mβ Mθ ℝ) (β θ : ℝ) :
    |p.dβ.dβ.eval β θ| ≤ p.moment 2 0 := by
  rw [← l1Norm_iterate_dβ_dθ]
  exact abs_eval_le_l1Norm _ β θ

/-- A value of the mixed derivative is at most the moment of order `(1, 1)`. -/
theorem abs_eval_dθ_dβ_le (p : TrigPoly2 Mβ Mθ ℝ) (β θ : ℝ) :
    |p.dθ.dβ.eval β θ| ≤ p.moment 1 1 := by
  rw [← l1Norm_iterate_dβ_dθ]
  exact abs_eval_le_l1Norm _ β θ

/-- A value of the second `θ`-derivative is at most the moment of order `(0, 2)`. -/
theorem abs_eval_dθ_dθ_le (p : TrigPoly2 Mβ Mθ ℝ) (β θ : ℝ) :
    |p.dθ.dθ.eval β θ| ≤ p.moment 0 2 := by
  rw [← l1Norm_iterate_dβ_dθ]
  exact abs_eval_le_l1Norm _ β θ

/-- `|2 (x x' + y y')| ≤ 2 (X X' + Y Y')` from bounds on the absolute values of the factors. -/
theorem abs_two_mul_add_le {x x' y y' X X' Y Y' : ℝ} (hx : |x| ≤ X) (hx' : |x'| ≤ X')
    (hy : |y| ≤ Y) (hy' : |y'| ≤ Y') :
    |2 * (x * x' + y * y')| ≤ 2 * (X * X' + Y * Y') := by
  rw [abs_mul, abs_two]
  refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) (by norm_num)
  rw [abs_mul, abs_mul]
  exact add_le_add (mul_le_mul hx hx' (abs_nonneg _) ((abs_nonneg _).trans hx))
    (mul_le_mul hy hy' (abs_nonneg _) ((abs_nonneg _).trans hy))

/-- A bound `m` of `∑ᵢ Tᵢ²` at every node `(j π / (2N), n π / (2P))`, `j, n ∈ ℤ`, gives the bound
`m + meshError T N P` everywhere. -/
theorem sum_sq_eval_le_of_mesh {ι : Type*} [Fintype ι] (T : ι → TrigPoly2 Mβ Mθ ℝ) {N P : ℕ}
    (hN : 0 < N) (hP : 0 < P) {m : ℝ}
    (hnode : ∀ j n : ℤ, ∑ i, (T i).eval (j * (Real.pi / (2 * N))) (n * (Real.pi / (2 * P))) ^ 2
      ≤ m) (β θ : ℝ) :
    ∑ i, (T i).eval β θ ^ 2 ≤ m + meshError T N P := by
  have hβ : ∀ β θ, HasDerivAt (fun t ↦ ∑ i, (T i).eval t θ ^ 2)
      (∑ i, 2 * ((T i).eval β θ * (T i).dβ.eval β θ)) β := fun β θ ↦ by
    refine HasDerivAt.fun_sum fun i _ ↦ ?_
    convert (hasDerivAt_eval_β (T i) β θ).pow 2 using 1
    ring
  have hθ : ∀ β θ, HasDerivAt (fun t ↦ ∑ i, (T i).eval β t ^ 2)
      (∑ i, 2 * ((T i).eval β θ * (T i).dθ.eval β θ)) θ := fun β θ ↦ by
    refine HasDerivAt.fun_sum fun i _ ↦ ?_
    convert (hasDerivAt_eval_θ (T i) β θ).pow 2 using 1
    ring
  have hββ : ∀ β θ, HasDerivAt (fun t ↦ ∑ i, 2 * ((T i).eval t θ * (T i).dβ.eval t θ))
      (∑ i, 2 * ((T i).dβ.eval β θ * (T i).dβ.eval β θ +
        (T i).eval β θ * (T i).dβ.dβ.eval β θ)) β := fun β θ ↦ by
    refine HasDerivAt.fun_sum fun i _ ↦ ?_
    exact ((hasDerivAt_eval_β (T i) β θ).mul (hasDerivAt_eval_β (T i).dβ β θ)).const_mul 2
  have hθβ : ∀ β θ, HasDerivAt (fun t ↦ ∑ i, 2 * ((T i).eval t θ * (T i).dθ.eval t θ))
      (∑ i, 2 * ((T i).dβ.eval β θ * (T i).dθ.eval β θ +
        (T i).eval β θ * (T i).dθ.dβ.eval β θ)) β := fun β θ ↦ by
    refine HasDerivAt.fun_sum fun i _ ↦ ?_
    exact ((hasDerivAt_eval_β (T i) β θ).mul (hasDerivAt_eval_β (T i).dθ β θ)).const_mul 2
  have hθθ : ∀ β θ, HasDerivAt (fun t ↦ ∑ i, 2 * ((T i).eval β t * (T i).dθ.eval β t))
      (∑ i, 2 * ((T i).dθ.eval β θ * (T i).dθ.eval β θ +
        (T i).eval β θ * (T i).dθ.dθ.eval β θ)) θ := fun β θ ↦ by
    refine HasDerivAt.fun_sum fun i _ ↦ ?_
    exact ((hasDerivAt_eval_θ (T i) β θ).mul (hasDerivAt_eval_θ (T i).dθ β θ)).const_mul 2
  have ha : ∀ β θ, |∑ i, 2 * ((T i).dβ.eval β θ * (T i).dβ.eval β θ +
      (T i).eval β θ * (T i).dβ.dβ.eval β θ)| ≤
      2 * ∑ i, ((T i).moment 1 0 ^ 2 + (T i).moment 0 0 * (T i).moment 2 0) := fun β θ ↦ by
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ ?_)
    have := abs_two_mul_add_le (abs_eval_dβ_le (T i) β θ) (abs_eval_dβ_le (T i) β θ)
      (abs_eval_le_moment (T i) β θ) (abs_eval_dβ_dβ_le (T i) β θ)
    rw [sq]
    exact this
  have hb : ∀ β θ, |∑ i, 2 * ((T i).dβ.eval β θ * (T i).dθ.eval β θ +
      (T i).eval β θ * (T i).dθ.dβ.eval β θ)| ≤
      2 * ∑ i, ((T i).moment 1 0 * (T i).moment 0 1 + (T i).moment 0 0 * (T i).moment 1 1) :=
    fun β θ ↦ by
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ ?_)
    exact abs_two_mul_add_le (abs_eval_dβ_le (T i) β θ) (abs_eval_dθ_le (T i) β θ)
      (abs_eval_le_moment (T i) β θ) (abs_eval_dθ_dβ_le (T i) β θ)
  have hc : ∀ β θ, |∑ i, 2 * ((T i).dθ.eval β θ * (T i).dθ.eval β θ +
      (T i).eval β θ * (T i).dθ.dθ.eval β θ)| ≤
      2 * ∑ i, ((T i).moment 0 1 ^ 2 + (T i).moment 0 0 * (T i).moment 0 2) := fun β θ ↦ by
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ ?_)
    have := abs_two_mul_add_le (abs_eval_dθ_le (T i) β θ) (abs_eval_dθ_le (T i) β θ)
      (abs_eval_le_moment (T i) β θ) (abs_eval_dθ_dθ_le (T i) β θ)
    rw [sq]
    exact this
  have hcont : Continuous (Function.uncurry fun β θ ↦ ∑ i, (T i).eval β θ ^ 2) :=
    continuous_finsetSum _ fun i _ ↦ (T i).continuous_eval.pow 2
  have h := le_of_forall_mesh_le hcont hβ hθ hββ hθβ hθθ ha hb hc
    (by positivity : (0 : ℝ) < 2 * Real.pi) (by positivity : (0 : ℝ) < 2 * Real.pi)
    (fun β θ ↦ sum_congr rfl fun i _ ↦ by rw [eval_add_two_pi_β])
    (fun β θ ↦ sum_congr rfl fun i _ ↦ by rw [eval_add_two_pi_θ])
    (by positivity : (0 : ℝ) < Real.pi / (2 * N)) (by positivity : (0 : ℝ) < Real.pi / (2 * P))
    hnode β θ
  unfold meshError
  linarith

end PDE.Analysis.TrigPoly2
