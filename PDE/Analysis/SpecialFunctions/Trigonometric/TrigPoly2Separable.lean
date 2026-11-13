/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Bounds
public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Quotient

/-!
# Separable trigonometric tables

A table `ρ` of `β` alone (degree `0` in `θ`) and a table `τ` of `θ` alone give the table
`outer ρ τ` of the product `ρ(β) τ(θ)` (`eval_outer`). The partial derivatives and the quotients
by `sin β` and `sin θ` act on one factor (`dβ_outer`, `dθ_outer`, `divSinβ_outer`,
`divSinθ_outer`), and all four operations are additive and commute with scalars, so a finite
combination `∑ a_{ml} • outer (ρ m) (τ l)` keeps this form under every composition of them. A
single term is a scalar multiple of an outer product (`monomial_eq_smul_outer`).

`approxEval p A B` replaces the modes `trigMode i (k β)` and `trigMode j (l θ)` by numbers
`A i k` and `B j l`; it is the sum bounded by `abs_eval_sub_sum_le`. It is additive, and on an
outer product it is the product of the one-variable sums (`approxEval_outer`), so certificates
evaluate combinations of outer products at quadrature nodes one variable at a time.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.TrigPoly2

open Finset

variable {Mβ Mθ : ℕ} {R : Type} [Field R]

/-! ### Linearity of the derivatives and quotients -/

theorem coeffN_add (p q : TrigPoly2 Mβ Mθ R) (i j : Fin 2) (k l : ℕ) :
    (p + q).coeffN i j k l = p.coeffN i j k l + q.coeffN i j k l := by
  unfold coeffN
  split_ifs <;> simp

theorem coeffN_smul (c : R) (p : TrigPoly2 Mβ Mθ R) (i j : Fin 2) (k l : ℕ) :
    (c • p).coeffN i j k l = c * p.coeffN i j k l := by
  unfold coeffN
  split_ifs <;> simp

protected theorem smul_add (c : R) (p q : TrigPoly2 Mβ Mθ R) : c • (p + q) = c • p + c • q := by
  ext i j k l
  simp [mul_add]

protected theorem smul_smul (c d : R) (p : TrigPoly2 Mβ Mθ R) : c • d • p = (c * d) • p := by
  ext i j k l
  simp [mul_assoc]

protected theorem smul_sum {ι : Type*} (c : R) (s : Finset ι) (f : ι → TrigPoly2 Mβ Mθ R) :
    c • ∑ x ∈ s, f x = ∑ x ∈ s, c • f x :=
  map_sum (AddMonoidHom.mk' (fun p : TrigPoly2 Mβ Mθ R ↦ c • p) (TrigPoly2.smul_add c)) f s

theorem dβ_add (p q : TrigPoly2 Mβ Mθ R) : (p + q).dβ = p.dβ + q.dβ := by
  ext i j k l
  simp only [dβ, coeff_add]
  split_ifs <;> ring

theorem dθ_add (p q : TrigPoly2 Mβ Mθ R) : (p + q).dθ = p.dθ + q.dθ := by
  ext i j k l
  simp only [dθ, coeff_add]
  split_ifs <;> ring

theorem dβ_smul (c : R) (p : TrigPoly2 Mβ Mθ R) : (c • p).dβ = c • p.dβ := by
  ext i j k l
  simp only [dβ, coeff_smul]
  split_ifs <;> ring

theorem dθ_smul (c : R) (p : TrigPoly2 Mβ Mθ R) : (c • p).dθ = c • p.dθ := by
  ext i j k l
  simp only [dθ, coeff_smul]
  split_ifs <;> ring

theorem divSinβ_add (p q : TrigPoly2 Mβ Mθ R) : divSinβ (p + q) = divSinβ p + divSinβ q := by
  ext i j k l
  simp only [divSinβ, coeff_add, coeffN_add, mul_add, sum_add_distrib]
  split_ifs <;> simp

theorem divSinθ_add (p q : TrigPoly2 Mβ Mθ R) : divSinθ (p + q) = divSinθ p + divSinθ q := by
  ext i j k l
  simp only [divSinθ, coeff_add, coeffN_add, mul_add, sum_add_distrib]
  split_ifs <;> simp

theorem divSinβ_smul (c : R) (p : TrigPoly2 Mβ Mθ R) : divSinβ (c • p) = c • divSinβ p := by
  ext i j k l
  simp only [divSinβ, coeff_smul, coeffN_smul]
  split_ifs
  · rw [mul_sum]
    exact sum_congr rfl fun _ _ ↦ by ring
  · simp

theorem divSinθ_smul (c : R) (p : TrigPoly2 Mβ Mθ R) : divSinθ (c • p) = c • divSinθ p := by
  ext i j k l
  simp only [divSinθ, coeff_smul, coeffN_smul]
  split_ifs
  · rw [mul_sum]
    exact sum_congr rfl fun _ _ ↦ by ring
  · simp

/-- `dβ` as an additive map. -/
def dβHom : TrigPoly2 Mβ Mθ R →+ TrigPoly2 Mβ Mθ R := AddMonoidHom.mk' dβ dβ_add

/-- `dθ` as an additive map. -/
def dθHom : TrigPoly2 Mβ Mθ R →+ TrigPoly2 Mβ Mθ R := AddMonoidHom.mk' dθ dθ_add

/-- `divSinβ` as an additive map. -/
def divSinβHom : TrigPoly2 Mβ Mθ R →+ TrigPoly2 (Mβ - 1) Mθ R :=
  AddMonoidHom.mk' divSinβ divSinβ_add

/-- `divSinθ` as an additive map. -/
def divSinθHom : TrigPoly2 Mβ Mθ R →+ TrigPoly2 Mβ (Mθ - 1) R :=
  AddMonoidHom.mk' divSinθ divSinθ_add

theorem dβ_sum {ι : Type*} (s : Finset ι) (f : ι → TrigPoly2 Mβ Mθ R) :
    (∑ x ∈ s, f x).dβ = ∑ x ∈ s, (f x).dβ :=
  map_sum (dβHom (R := R)) f s

theorem dθ_sum {ι : Type*} (s : Finset ι) (f : ι → TrigPoly2 Mβ Mθ R) :
    (∑ x ∈ s, f x).dθ = ∑ x ∈ s, (f x).dθ :=
  map_sum (dθHom (R := R)) f s

theorem divSinβ_sum {ι : Type*} (s : Finset ι) (f : ι → TrigPoly2 Mβ Mθ R) :
    divSinβ (∑ x ∈ s, f x) = ∑ x ∈ s, divSinβ (f x) :=
  map_sum (divSinβHom (R := R)) f s

theorem divSinθ_sum {ι : Type*} (s : Finset ι) (f : ι → TrigPoly2 Mβ Mθ R) :
    divSinθ (∑ x ∈ s, f x) = ∑ x ∈ s, divSinθ (f x) :=
  map_sum (divSinθHom (R := R)) f s

/-! ### Outer products -/

/-- The table of `ρ(β) τ(θ)` for a table `ρ` of `β` alone and a table `τ` of `θ` alone. -/
def outer (ρ : TrigPoly2 Mβ 0 R) (τ : TrigPoly2 0 Mθ R) : TrigPoly2 Mβ Mθ R :=
  ⟨fun i j k l ↦ ρ.coeff i 0 k 0 * τ.coeff 0 j 0 l⟩

@[simp] theorem coeff_outer (ρ : TrigPoly2 Mβ 0 R) (τ : TrigPoly2 0 Mθ R) (i j : Fin 2)
    (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) :
    (outer ρ τ).coeff i j k l = ρ.coeff i 0 k 0 * τ.coeff 0 j 0 l := rfl

theorem outer_add_left (ρ ρ' : TrigPoly2 Mβ 0 R) (τ : TrigPoly2 0 Mθ R) :
    outer (ρ + ρ') τ = outer ρ τ + outer ρ' τ := by
  ext i j k l
  simp [add_mul]

theorem outer_add_right (ρ : TrigPoly2 Mβ 0 R) (τ τ' : TrigPoly2 0 Mθ R) :
    outer ρ (τ + τ') = outer ρ τ + outer ρ τ' := by
  ext i j k l
  simp [mul_add]

theorem outer_smul_left (c : R) (ρ : TrigPoly2 Mβ 0 R) (τ : TrigPoly2 0 Mθ R) :
    outer (c • ρ) τ = c • outer ρ τ := by
  ext i j k l
  simp [mul_assoc]

theorem outer_smul_right (c : R) (ρ : TrigPoly2 Mβ 0 R) (τ : TrigPoly2 0 Mθ R) :
    outer ρ (c • τ) = c • outer ρ τ := by
  ext i j k l
  simp only [coeff_outer, coeff_smul]
  ring

theorem outer_sum_left {ι : Type*} (s : Finset ι) (ρ : ι → TrigPoly2 Mβ 0 R)
    (τ : TrigPoly2 0 Mθ R) : outer (∑ x ∈ s, ρ x) τ = ∑ x ∈ s, outer (ρ x) τ :=
  map_sum (AddMonoidHom.mk' (fun ρ ↦ outer ρ τ) fun ρ ρ' ↦ outer_add_left ρ ρ' τ) ρ s

theorem outer_sum_right {ι : Type*} (s : Finset ι) (ρ : TrigPoly2 Mβ 0 R)
    (τ : ι → TrigPoly2 0 Mθ R) : outer ρ (∑ x ∈ s, τ x) = ∑ x ∈ s, outer ρ (τ x) :=
  map_sum (AddMonoidHom.mk' (fun τ ↦ outer ρ τ) fun τ τ' ↦ outer_add_right ρ τ τ') τ s

/-- A single coefficient is a multiple of the outer product of two single modes. -/
theorem monomial_eq_smul_outer (i j : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) (c : R) :
    (monomial i j k l c : TrigPoly2 Mβ Mθ R) =
      c • outer (monomial i 0 k 0 1) (monomial 0 j 0 l 1) := by
  ext i' j' k' l'
  simp only [monomial, coeff_smul, coeff_outer]
  by_cases hi : i' = i <;> by_cases hj : j' = j <;> by_cases hk : k' = k <;>
    by_cases hl : l' = l <;> simp [hi, hj, hk, hl]

theorem dβ_outer (ρ : TrigPoly2 Mβ 0 R) (τ : TrigPoly2 0 Mθ R) :
    (outer ρ τ).dβ = outer ρ.dβ τ := by
  ext i j k l
  simp only [dβ, coeff_outer]
  split_ifs <;> ring

theorem dθ_outer (ρ : TrigPoly2 Mβ 0 R) (τ : TrigPoly2 0 Mθ R) :
    (outer ρ τ).dθ = outer ρ τ.dθ := by
  ext i j k l
  simp only [dθ, coeff_outer]
  split_ifs <;> ring

theorem coeffN_outer (ρ : TrigPoly2 Mβ 0 R) (τ : TrigPoly2 0 Mθ R) (i j : Fin 2) (k : ℕ)
    (l : Fin (Mθ + 1)) : (outer ρ τ).coeffN i j k l = ρ.coeffN i 0 k 0 * τ.coeff 0 j 0 l := by
  unfold coeffN
  by_cases hk : k < Mβ + 1
  · simp [hk, l.isLt]
  · simp [hk]

theorem coeffN_outer' (ρ : TrigPoly2 Mβ 0 R) (τ : TrigPoly2 0 Mθ R) (i j : Fin 2)
    (k : Fin (Mβ + 1)) (l : ℕ) :
    (outer ρ τ).coeffN i j k l = ρ.coeff i 0 k 0 * τ.coeffN 0 j 0 l := by
  unfold coeffN
  by_cases hl : l < Mθ + 1
  · simp [hl, k.isLt]
  · simp [hl]

theorem divSinβ_outer (ρ : TrigPoly2 Mβ 0 R) (τ : TrigPoly2 0 Mθ R) :
    divSinβ (outer ρ τ) = outer (divSinβ ρ) τ := by
  ext i j k l
  simp only [divSinβ, coeff_outer, coeffN_outer, Fin.val_zero]
  split_ifs
  · rw [sum_mul]
    exact sum_congr rfl fun _ _ ↦ by ring
  · simp

theorem divSinθ_outer (ρ : TrigPoly2 Mβ 0 R) (τ : TrigPoly2 0 Mθ R) :
    divSinθ (outer ρ τ) = outer ρ (divSinθ τ) := by
  ext i j k l
  simp only [divSinθ, coeff_outer, coeffN_outer', Fin.val_zero]
  split_ifs
  · rw [mul_sum]
    exact sum_congr rfl fun _ _ ↦ by ring
  · simp

/-! ### Values -/

section Eval

variable [Algebra R ℝ]

/-- The sum `∑ coeff i j k l · A i k · B j l`, the value with the modes replaced by `A` and `B`. -/
def approxEval (p : TrigPoly2 Mβ Mθ R) (A B : Fin 2 → ℕ → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k : Fin (Mβ + 1), ∑ l : Fin (Mθ + 1),
    algebraMap R ℝ (p.coeff i j k l) * A i k * B j l

/-- The exact modes `trigMode i (k * α)` at the angle `α`, used for both `β` and `θ`. -/
def trigModes (α : ℝ) : Fin 2 → ℕ → ℝ := fun i k ↦ trigMode i (k * α)

theorem eval_eq_approxEval (p : TrigPoly2 Mβ Mθ R) (β θ : ℝ) :
    p.eval β θ = p.approxEval (trigModes β) (trigModes θ) := rfl

theorem approxEval_add (p q : TrigPoly2 Mβ Mθ R) (A B : Fin 2 → ℕ → ℝ) :
    (p + q).approxEval A B = p.approxEval A B + q.approxEval A B := by
  simp only [approxEval, coeff_add, map_add, add_mul, sum_add_distrib]

theorem approxEval_smul (c : R) (p : TrigPoly2 Mβ Mθ R) (A B : Fin 2 → ℕ → ℝ) :
    (c • p).approxEval A B = algebraMap R ℝ c * p.approxEval A B := by
  simp only [approxEval, coeff_smul, map_mul, mul_sum, mul_assoc]

theorem approxEval_sum {ι : Type*} (s : Finset ι) (f : ι → TrigPoly2 Mβ Mθ R)
    (A B : Fin 2 → ℕ → ℝ) : (∑ x ∈ s, f x).approxEval A B = ∑ x ∈ s, (f x).approxEval A B :=
  map_sum (AddMonoidHom.mk' (fun p : TrigPoly2 Mβ Mθ R ↦ p.approxEval A B)
    fun p q ↦ approxEval_add p q A B) f s

theorem approxEval_monomial (i j : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) (c : R)
    (A B : Fin 2 → ℕ → ℝ) :
    (monomial i j k l c).approxEval A B = algebraMap R ℝ c * A i k * B j l := by
  simp only [approxEval, monomial]
  rw [sum_eq_single i (fun i' _ hi' ↦ by simp [hi']) (by simp), sum_eq_single j
    (fun j' _ hj' ↦ by simp [hj']) (by simp), sum_eq_single k (fun k' _ hk' ↦ by simp [hk'])
    (by simp), sum_eq_single l (fun l' _ hl' ↦ by simp [hl']) (by simp)]
  simp

theorem approxEval_trigModes_zero_right (ρ : TrigPoly2 Mβ 0 R) (A : Fin 2 → ℕ → ℝ) :
    ρ.approxEval A (trigModes 0) =
      ∑ i, ∑ k : Fin (Mβ + 1), algebraMap R ℝ (ρ.coeff i 0 k 0) * A i k := by
  simp [approxEval, trigModes, trigMode, Fin.sum_univ_two]

theorem approxEval_trigModes_zero_left (τ : TrigPoly2 0 Mθ R) (B : Fin 2 → ℕ → ℝ) :
    τ.approxEval (trigModes 0) B =
      ∑ j, ∑ l : Fin (Mθ + 1), algebraMap R ℝ (τ.coeff 0 j 0 l) * B j l := by
  simp [approxEval, trigModes, trigMode, Fin.sum_univ_two]

/-- On an outer product the sum factors into the sums of the two variables; the modes of the
missing variable are the exact values `1` and `0` of `cos 0` and `sin 0`. -/
theorem approxEval_outer (ρ : TrigPoly2 Mβ 0 R) (τ : TrigPoly2 0 Mθ R) (A B : Fin 2 → ℕ → ℝ) :
    (outer ρ τ).approxEval A B =
      ρ.approxEval A (trigModes 0) * τ.approxEval (trigModes 0) B := by
  rw [approxEval_trigModes_zero_right, approxEval_trigModes_zero_left, sum_mul]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [sum_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [mul_sum]
  refine sum_congr rfl fun l _ ↦ ?_
  simp only [coeff_outer, map_mul]
  ring

theorem eval_outer (ρ : TrigPoly2 Mβ 0 R) (τ : TrigPoly2 0 Mθ R) (β θ : ℝ) :
    (outer ρ τ).eval β θ = ρ.eval β 0 * τ.eval 0 θ := by
  rw [eval_eq_approxEval, approxEval_outer]
  rfl

theorem l1Norm_outer_le (ρ : TrigPoly2 Mβ 0 R) (τ : TrigPoly2 0 Mθ R) :
    (outer ρ τ).l1Norm ≤ ρ.l1Norm * τ.l1Norm := by
  have hρ : ∑ i, ∑ k : Fin (Mβ + 1), |algebraMap R ℝ (ρ.coeff i 0 k 0)| ≤ ρ.l1Norm := by
    refine sum_le_sum fun i _ ↦ ?_
    calc ∑ k : Fin (Mβ + 1), |algebraMap R ℝ (ρ.coeff i 0 k 0)|
        ≤ ∑ k : Fin (Mβ + 1), ∑ l : Fin (0 + 1), |algebraMap R ℝ (ρ.coeff i 0 k l)| :=
          sum_le_sum fun k _ ↦ single_le_sum (f := fun l ↦ |algebraMap R ℝ (ρ.coeff i 0 k l)|)
            (fun _ _ ↦ abs_nonneg _) (mem_univ 0)
      _ ≤ ∑ j, ∑ k : Fin (Mβ + 1), ∑ l : Fin (0 + 1), |algebraMap R ℝ (ρ.coeff i j k l)| :=
          single_le_sum (f := fun j ↦ ∑ k : Fin (Mβ + 1), ∑ l : Fin (0 + 1),
            |algebraMap R ℝ (ρ.coeff i j k l)|)
            (fun _ _ ↦ sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _) (mem_univ 0)
  have hτ : ∑ j, ∑ l : Fin (Mθ + 1), |algebraMap R ℝ (τ.coeff 0 j 0 l)| ≤ τ.l1Norm := by
    calc ∑ j, ∑ l : Fin (Mθ + 1), |algebraMap R ℝ (τ.coeff 0 j 0 l)|
        ≤ ∑ j, ∑ k : Fin (0 + 1), ∑ l : Fin (Mθ + 1), |algebraMap R ℝ (τ.coeff 0 j k l)| :=
          sum_le_sum fun j _ ↦ single_le_sum (f := fun k ↦ ∑ l : Fin (Mθ + 1),
            |algebraMap R ℝ (τ.coeff 0 j k l)|) (fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _)
            (mem_univ 0)
      _ ≤ τ.l1Norm :=
          single_le_sum (f := fun i ↦ ∑ j, ∑ k : Fin (0 + 1), ∑ l : Fin (Mθ + 1),
            |algebraMap R ℝ (τ.coeff i j k l)|)
            (fun _ _ ↦ sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦
              abs_nonneg _) (mem_univ 0)
  calc (outer ρ τ).l1Norm
      = (∑ i, ∑ k : Fin (Mβ + 1), |algebraMap R ℝ (ρ.coeff i 0 k 0)|) *
          ∑ j, ∑ l : Fin (Mθ + 1), |algebraMap R ℝ (τ.coeff 0 j 0 l)| := by
        rw [sum_mul]
        refine sum_congr rfl fun i _ ↦ ?_
        rw [mul_sum]
        refine sum_congr rfl fun j _ ↦ ?_
        rw [sum_mul]
        refine sum_congr rfl fun k _ ↦ ?_
        rw [mul_sum]
        refine sum_congr rfl fun l _ ↦ ?_
        simp only [coeff_outer, map_mul, abs_mul]
    _ ≤ ρ.l1Norm * τ.l1Norm :=
        mul_le_mul hρ hτ (sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _)
          (l1Norm_nonneg ρ)

/-- The value with replaced modes of a combination of outer products. -/
theorem approxEval_sum_sum_smul_outer {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι → κ → R) (ρ : ι → TrigPoly2 Mβ 0 R) (τ : κ → TrigPoly2 0 Mθ R)
    (A B : Fin 2 → ℕ → ℝ) :
    (∑ m ∈ s, ∑ l ∈ t, a m l • outer (ρ m) (τ l)).approxEval A B =
      ∑ m ∈ s, ∑ l ∈ t, algebraMap R ℝ (a m l) * (ρ m).approxEval A (trigModes 0) *
        (τ l).approxEval (trigModes 0) B := by
  simp only [approxEval_sum, approxEval_smul, approxEval_outer, mul_assoc]

/-- The `ℓ¹` norm of a combination of outer products. -/
theorem l1Norm_sum_sum_smul_outer_le {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι → κ → R) (ρ : ι → TrigPoly2 Mβ 0 R) (τ : κ → TrigPoly2 0 Mθ R) :
    (∑ m ∈ s, ∑ l ∈ t, a m l • outer (ρ m) (τ l)).l1Norm ≤
      ∑ m ∈ s, ∑ l ∈ t, |algebraMap R ℝ (a m l)| * ((ρ m).l1Norm * (τ l).l1Norm) := by
  refine (l1Norm_sum_le _ _).trans (sum_le_sum fun m _ ↦ (l1Norm_sum_le _ _).trans
    (sum_le_sum fun l _ ↦ ?_))
  rw [l1Norm_smul]
  exact mul_le_mul_of_nonneg_left (l1Norm_outer_le _ _) (abs_nonneg _)

/-- Values with replaced modes are within `‖p‖₁ (εβ + εθ + εβ εθ)` of the values. -/
theorem abs_eval_sub_approxEval_le (p : TrigPoly2 Mβ Mθ R) (β θ : ℝ) (A B : Fin 2 → ℕ → ℝ)
    {εβ εθ : ℝ} (hA : ∀ i (k : Fin (Mβ + 1)), |A i k - trigMode i ((k : ℕ) * β)| ≤ εβ)
    (hB : ∀ j (l : Fin (Mθ + 1)), |B j l - trigMode j ((l : ℕ) * θ)| ≤ εθ) :
    |p.eval β θ - p.approxEval A B| ≤ p.l1Norm * (εβ + εθ + εβ * εθ) :=
  abs_eval_sub_sum_le p β θ A B hA hB

theorem approxEval_eq_sum_range (p : TrigPoly2 Mβ Mθ R) (A B : Fin 2 → ℕ → ℝ) :
    p.approxEval A B = ∑ i, ∑ j, ∑ k ∈ range (Mβ + 1), ∑ l ∈ range (Mθ + 1),
      algebraMap R ℝ (p.coeffN i j k l) * A i k * B j l := by
  unfold approxEval
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  simp only [← coeffN_coe p i j]
  rw [← Fin.sum_univ_eq_sum_range (fun k ↦ ∑ l ∈ range (Mθ + 1),
    algebraMap R ℝ (p.coeffN i j k l) * A i k * B j l)]
  refine sum_congr rfl fun k _ ↦ ?_
  exact Fin.sum_univ_eq_sum_range (fun l ↦
    algebraMap R ℝ (p.coeffN i j k l) * A i k * B j l) _

/-- The modes after a derivative: `cos (kβ)` contributes `-k` times the sine and `sin (kβ)`
contributes `k` times the cosine. -/
def derivModes (A : Fin 2 → ℕ → ℝ) : Fin 2 → ℕ → ℝ :=
  fun i k ↦ if i = 0 then -(k : ℝ) * A 1 k else (k : ℝ) * A 0 k

/-- The modes after the quotient by the sine: `sin (kx)` becomes `∑_{n < k} w(n, k) cos (nx)`;
cosines are dropped. -/
def divSinModes (A : Fin 2 → ℕ → ℝ) : Fin 2 → ℕ → ℝ :=
  fun i k ↦ if i = 0 then 0 else ∑ n ∈ range k, (trigQuotientWeight n k : ℝ) * A 0 n

theorem approxEval_dβ (p : TrigPoly2 Mβ Mθ R) (A B : Fin 2 → ℕ → ℝ) :
    p.dβ.approxEval A B = p.approxEval (derivModes A) B := by
  simp only [approxEval, dβ, derivModes, Fin.sum_univ_two, Fin.isValue, ↓reduceIte,
    one_ne_zero, map_mul, map_natCast, map_neg]
  rw [add_comm]
  congr 1 <;> congr 1 <;> refine sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ ?_ <;> ring

theorem approxEval_dθ (p : TrigPoly2 Mβ Mθ R) (A B : Fin 2 → ℕ → ℝ) :
    p.dθ.approxEval A B = p.approxEval A (derivModes B) := by
  simp only [approxEval, dθ, derivModes, Fin.sum_univ_two, Fin.isValue, ↓reduceIte,
    one_ne_zero, map_mul, map_natCast, map_neg]
  congr 1 <;> rw [add_comm] <;> congr 1 <;>
    refine sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ ?_ <;> ring

private theorem sum_range_trigQuotientWeight_eq {K k : ℕ} (hk : k ≤ K + 1) (f : ℕ → ℝ) :
    ∑ n ∈ range (K + 1), (trigQuotientWeight n k : ℝ) * f n =
      ∑ n ∈ range k, (trigQuotientWeight n k : ℝ) * f n := by
  rcases Nat.lt_or_ge K k with h | h
  · obtain rfl : k = K + 1 := by omega
    rfl
  · refine (sum_subset (range_subset_range.mpr (by omega)) fun n hn hn' ↦ ?_).symm
    rw [trigQuotientWeight_eq_zero (by simpa using hn'), Int.cast_zero, zero_mul]

private theorem sum_divSin_aux (M N : ℕ) (P : ℕ → ℕ → ℝ) (A B : ℕ → ℝ) :
    ∑ n ∈ range (M - 1 + 1), ∑ l ∈ range N,
        (∑ k ∈ range (M + 1), (trigQuotientWeight n k : ℝ) * P k l) * A n * B l =
      ∑ k ∈ range (M + 1), ∑ l ∈ range N,
        (P k l * ∑ n ∈ range k, (trigQuotientWeight n k : ℝ) * A n) * B l := by
  have h : ∀ k ∈ range (M + 1), ∀ l, (P k l * ∑ n ∈ range k, (trigQuotientWeight n k : ℝ) *
      A n) * B l = ∑ n ∈ range (M - 1 + 1), (trigQuotientWeight n k : ℝ) * P k l * A n * B l := by
    intro k hk l
    rw [← sum_range_trigQuotientWeight_eq (K := M - 1) (by have := mem_range.mp hk; omega),
      mul_sum, sum_mul]
    exact sum_congr rfl fun _ _ ↦ by ring
  rw [sum_congr rfl fun k hk ↦ sum_congr rfl fun l _ ↦ h k hk l]
  simp only [sum_mul]
  rw [sum_comm]
  refine Eq.trans (sum_congr rfl fun l _ ↦ sum_comm) ?_
  exact sum_comm

private theorem sum_divSin_aux' (M N : ℕ) (P : ℕ → ℕ → ℝ) (A B : ℕ → ℝ) :
    ∑ k ∈ range N, ∑ n ∈ range (M - 1 + 1),
        (∑ l ∈ range (M + 1), (trigQuotientWeight n l : ℝ) * P k l) * A k * B n =
      ∑ k ∈ range N, ∑ l ∈ range (M + 1),
        P k l * A k * ∑ n ∈ range l, (trigQuotientWeight n l : ℝ) * B n := by
  refine sum_congr rfl fun k _ ↦ ?_
  have h := sum_divSin_aux M 1 (fun l _ ↦ P k l) B (fun _ ↦ A k)
  simp only [sum_range_one] at h
  calc _ = ∑ n ∈ range (M - 1 + 1), (∑ l ∈ range (M + 1), (trigQuotientWeight n l : ℝ) *
        P k l) * B n * A k := sum_congr rfl fun _ _ ↦ by ring
    _ = _ := h
    _ = _ := sum_congr rfl fun _ _ ↦ by ring

theorem approxEval_divSinβ (p : TrigPoly2 Mβ Mθ R) (A B : Fin 2 → ℕ → ℝ) :
    (divSinβ p).approxEval A B = p.approxEval (divSinModes A) B := by
  rw [approxEval_eq_sum_range, approxEval_eq_sum_range]
  simp only [coeffN_divSinβ, divSinModes, Fin.sum_univ_two, Fin.isValue, ↓reduceIte,
    one_ne_zero, map_zero, zero_mul, sum_const_zero, add_zero, zero_add, mul_zero, map_sum,
    map_mul, map_intCast]
  congr 1
  · exact sum_divSin_aux Mβ (Mθ + 1) (fun k l ↦ algebraMap R ℝ (p.coeffN 1 0 k l)) (A 0)
      (B 0)
  · exact sum_divSin_aux Mβ (Mθ + 1) (fun k l ↦ algebraMap R ℝ (p.coeffN 1 1 k l)) (A 0)
      (B 1)

theorem approxEval_divSinθ (p : TrigPoly2 Mβ Mθ R) (A B : Fin 2 → ℕ → ℝ) :
    (divSinθ p).approxEval A B = p.approxEval A (divSinModes B) := by
  rw [approxEval_eq_sum_range, approxEval_eq_sum_range]
  simp only [coeffN_divSinθ, divSinModes, Fin.sum_univ_two, Fin.isValue, ↓reduceIte,
    one_ne_zero, map_zero, zero_mul, sum_const_zero, add_zero, zero_add, mul_zero, map_sum,
    map_mul, map_intCast]
  congr 1
  · exact sum_divSin_aux' Mθ (Mβ + 1) (fun k l ↦ algebraMap R ℝ (p.coeffN 0 1 k l)) (A 0)
      (B 0)
  · exact sum_divSin_aux' Mθ (Mβ + 1) (fun k l ↦ algebraMap R ℝ (p.coeffN 1 1 k l)) (A 1)
      (B 0)

theorem approxEval_monomial_trigModes_zero_right (i : Fin 2) (k : Fin (Mβ + 1)) (c : R)
    (A : Fin 2 → ℕ → ℝ) :
    (monomial i 0 k 0 c : TrigPoly2 Mβ 0 R).approxEval A (trigModes 0) =
      algebraMap R ℝ c * A i k := by
  simp [approxEval_monomial, trigModes, trigMode]

theorem approxEval_monomial_trigModes_zero_left (j : Fin 2) (l : Fin (Mθ + 1)) (c : R)
    (B : Fin 2 → ℕ → ℝ) :
    (monomial 0 j 0 l c : TrigPoly2 0 Mθ R).approxEval (trigModes 0) B =
      algebraMap R ℝ c * B j l := by
  simp [approxEval_monomial, trigModes, trigMode]

@[simp] theorem derivModes_zero (A : Fin 2 → ℕ → ℝ) (k : ℕ) :
    derivModes A 0 k = -(k : ℝ) * A 1 k := rfl

@[simp] theorem derivModes_one (A : Fin 2 → ℕ → ℝ) (k : ℕ) :
    derivModes A 1 k = (k : ℝ) * A 0 k := rfl

@[simp] theorem divSinModes_zero (A : Fin 2 → ℕ → ℝ) (k : ℕ) : divSinModes A 0 k = 0 := rfl

/-- The quotient modes of the sines satisfy `q (k + 2) = q k + 2 A_cos (k + 1)`, with `q 0 = 0` and
`q 1 = A_cos 0`: cumulative sums of every second cosine. -/
theorem divSinModes_one_add_two (A : Fin 2 → ℕ → ℝ) (k : ℕ) :
    divSinModes A 1 (k + 2) = divSinModes A 1 k + 2 * A 0 (k + 1) := by
  simp only [divSinModes, Fin.isValue, one_ne_zero, ↓reduceIte]
  rw [sum_range_succ, sum_range_succ]
  have h₁ : trigQuotientWeight k (k + 2) = 0 := by
    simp only [trigQuotientWeight]
    rw [ite_eq_right_iff.mpr fun h' ↦ absurd h'.2 (by omega)]
  have h₂ : trigQuotientWeight (k + 1) (k + 2) = 2 := by
    simp only [trigQuotientWeight]
    rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_right_iff.mpr fun h' ↦ absurd h' (by omega)]
  rw [h₁, h₂]
  push_cast
  rw [zero_mul, add_zero]
  congr 1
  refine sum_congr rfl fun n hn ↦ ?_
  have := mem_range.mp hn
  congr 2
  simp only [trigQuotientWeight]
  congr 1
  apply propext
  omega

theorem divSinModes_one_zero (A : Fin 2 → ℕ → ℝ) : divSinModes A 1 0 = 0 := by
  simp [divSinModes]

theorem divSinModes_one_one (A : Fin 2 → ℕ → ℝ) : divSinModes A 1 1 = A 0 0 := by
  simp [divSinModes, trigQuotientWeight]

/-! ### Weighted coefficient norms -/

/-- The weighted `ℓ¹` norm `∑ |coeff i j k l| U i k V j l`. -/
def l1Weighted (p : TrigPoly2 Mβ Mθ R) (U V : Fin 2 → ℕ → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k : Fin (Mβ + 1), ∑ l : Fin (Mθ + 1),
    |algebraMap R ℝ (p.coeff i j k l)| * U i k * V j l

/-- The weights `1` on the zero frequency cosine and `0` elsewhere, for a variable a table does
not depend on. -/
def zeroModes : Fin 2 → ℕ → ℝ := fun j _ ↦ if j = 0 then 1 else 0

theorem l1Norm_eq_l1Weighted (p : TrigPoly2 Mβ Mθ R) :
    p.l1Norm = p.l1Weighted (fun _ _ ↦ 1) (fun _ _ ↦ 1) := by
  simp [l1Norm, l1Weighted]

theorem l1Weighted_eq_sum_range (p : TrigPoly2 Mβ Mθ R) (U V : Fin 2 → ℕ → ℝ) :
    p.l1Weighted U V = ∑ i, ∑ j, ∑ k ∈ range (Mβ + 1), ∑ l ∈ range (Mθ + 1),
      |algebraMap R ℝ (p.coeffN i j k l)| * U i k * V j l := by
  unfold l1Weighted
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  simp only [← coeffN_coe p i j]
  rw [← Fin.sum_univ_eq_sum_range (fun k ↦ ∑ l ∈ range (Mθ + 1),
    |algebraMap R ℝ (p.coeffN i j k l)| * U i k * V j l)]
  refine sum_congr rfl fun k _ ↦ ?_
  exact Fin.sum_univ_eq_sum_range (fun l ↦
    |algebraMap R ℝ (p.coeffN i j k l)| * U i k * V j l) _

theorem l1Weighted_add_le (p q : TrigPoly2 Mβ Mθ R) {U V : Fin 2 → ℕ → ℝ}
    (hU : ∀ i k, 0 ≤ U i k) (hV : ∀ j l, 0 ≤ V j l) :
    (p + q).l1Weighted U V ≤ p.l1Weighted U V + q.l1Weighted U V := by
  simp only [l1Weighted, coeff_add, map_add, ← sum_add_distrib]
  refine sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ sum_le_sum fun k _ ↦ sum_le_sum fun l _ ↦ ?_
  rw [← add_mul, ← add_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (abs_add_le _ _) (hU _ _))
    (hV _ _)

theorem l1Weighted_sum_le {ι : Type*} (s : Finset ι) (f : ι → TrigPoly2 Mβ Mθ R)
    {U V : Fin 2 → ℕ → ℝ} (hU : ∀ i k, 0 ≤ U i k) (hV : ∀ j l, 0 ≤ V j l) :
    (∑ x ∈ s, f x).l1Weighted U V ≤ ∑ x ∈ s, (f x).l1Weighted U V := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1Weighted]
  | insert x s hx ih =>
    rw [sum_insert hx, sum_insert hx]
    exact (l1Weighted_add_le _ _ hU hV).trans (by gcongr)

theorem l1Weighted_smul (c : R) (p : TrigPoly2 Mβ Mθ R) (U V : Fin 2 → ℕ → ℝ) :
    (c • p).l1Weighted U V = |algebraMap R ℝ c| * p.l1Weighted U V := by
  simp only [l1Weighted, coeff_smul, map_mul, abs_mul, mul_sum, mul_assoc]

theorem l1Weighted_monomial (i j : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) (c : R)
    (U V : Fin 2 → ℕ → ℝ) :
    (monomial i j k l c).l1Weighted U V = |algebraMap R ℝ c| * U i k * V j l := by
  simp only [l1Weighted, monomial]
  rw [sum_eq_single i (fun i' _ hi' ↦ by simp [hi']) (by simp), sum_eq_single j
    (fun j' _ hj' ↦ by simp [hj']) (by simp), sum_eq_single k (fun k' _ hk' ↦ by simp [hk'])
    (by simp), sum_eq_single l (fun l' _ hl' ↦ by simp [hl']) (by simp)]
  simp

theorem l1Weighted_outer (ρ : TrigPoly2 Mβ 0 R) (τ : TrigPoly2 0 Mθ R)
    (U V : Fin 2 → ℕ → ℝ) :
    (outer ρ τ).l1Weighted U V = ρ.l1Weighted U zeroModes * τ.l1Weighted zeroModes V := by
  have hρ : ρ.l1Weighted U zeroModes =
      ∑ i, ∑ k : Fin (Mβ + 1), |algebraMap R ℝ (ρ.coeff i 0 k 0)| * U i k := by
    simp [l1Weighted, zeroModes, Fin.sum_univ_two]
  have hτ : τ.l1Weighted zeroModes V =
      ∑ j, ∑ l : Fin (Mθ + 1), |algebraMap R ℝ (τ.coeff 0 j 0 l)| * V j l := by
    simp [l1Weighted, zeroModes, Fin.sum_univ_two]
  rw [hρ, hτ, sum_mul]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [sum_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [mul_sum]
  refine sum_congr rfl fun l _ ↦ ?_
  simp only [coeff_outer, map_mul, abs_mul]
  ring

/-- The weights after a derivative. -/
def derivWeights (U : Fin 2 → ℕ → ℝ) : Fin 2 → ℕ → ℝ :=
  fun i k ↦ if i = 0 then (k : ℝ) * U 1 k else (k : ℝ) * U 0 k

theorem l1Weighted_dβ (p : TrigPoly2 Mβ Mθ R) (U V : Fin 2 → ℕ → ℝ) :
    p.dβ.l1Weighted U V = p.l1Weighted (derivWeights U) V := by
  simp only [l1Weighted, dβ, derivWeights, Fin.sum_univ_two, Fin.isValue, ↓reduceIte,
    one_ne_zero, map_mul, map_natCast, map_neg, abs_mul, abs_neg, Nat.abs_cast]
  rw [add_comm]
  congr 1 <;> congr 1 <;> refine sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ ?_ <;> ring

theorem l1Weighted_dθ (p : TrigPoly2 Mβ Mθ R) (U V : Fin 2 → ℕ → ℝ) :
    p.dθ.l1Weighted U V = p.l1Weighted U (derivWeights V) := by
  simp only [l1Weighted, dθ, derivWeights, Fin.sum_univ_two, Fin.isValue, ↓reduceIte,
    one_ne_zero, map_mul, map_natCast, map_neg, abs_mul, abs_neg, Nat.abs_cast]
  congr 1 <;> rw [add_comm] <;> congr 1 <;>
    refine sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ ?_ <;> ring

theorem l1Weighted_divSinβ_le (p : TrigPoly2 Mβ Mθ R) {U V : Fin 2 → ℕ → ℝ}
    (hU : ∀ i k, 0 ≤ U i k) (hV : ∀ j l, 0 ≤ V j l) :
    (divSinβ p).l1Weighted U V ≤ p.l1Weighted (divSinModes U) V := by
  rw [l1Weighted_eq_sum_range, l1Weighted_eq_sum_range]
  simp only [coeffN_divSinβ, divSinModes, Fin.sum_univ_two, Fin.isValue, ↓reduceIte,
    one_ne_zero, map_zero, abs_zero, zero_mul, sum_const_zero, add_zero, zero_add, mul_zero]
  have key : ∀ j, ∑ x ∈ range (Mβ - 1 + 1), ∑ l ∈ range (Mθ + 1),
      |algebraMap R ℝ (∑ k ∈ range (Mβ + 1), (trigQuotientWeight x k : R) * p.coeffN 1 j k l)| *
        U 0 x * V j l ≤
      ∑ x ∈ range (Mβ + 1), ∑ l ∈ range (Mθ + 1),
        |algebraMap R ℝ (p.coeffN 1 j x l)| *
          (∑ n ∈ range x, (trigQuotientWeight n x : ℝ) * U 0 n) * V j l := by
    intro j
    rw [← sum_divSin_aux Mβ (Mθ + 1) (fun k l ↦ |algebraMap R ℝ (p.coeffN 1 j k l)|) (U 0)
      (V j)]
    refine sum_le_sum fun n _ ↦ sum_le_sum fun l _ ↦ ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (hU _ _)) (hV _ _)
    simp only [map_sum, map_mul, map_intCast]
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun k _ ↦ ?_))
    rw [abs_mul, Int.cast_abs.symm.trans (congrArg _ (abs_of_nonneg ?_))]
    simp only [trigQuotientWeight]
    split_ifs <;> norm_num
  exact add_le_add (key 0) (key 1)

theorem l1Weighted_divSinθ_le (p : TrigPoly2 Mβ Mθ R) {U V : Fin 2 → ℕ → ℝ}
    (hU : ∀ i k, 0 ≤ U i k) (hV : ∀ j l, 0 ≤ V j l) :
    (divSinθ p).l1Weighted U V ≤ p.l1Weighted U (divSinModes V) := by
  rw [l1Weighted_eq_sum_range, l1Weighted_eq_sum_range]
  simp only [coeffN_divSinθ, divSinModes, Fin.sum_univ_two, Fin.isValue, ↓reduceIte,
    one_ne_zero, map_zero, abs_zero, zero_mul, sum_const_zero, add_zero, zero_add, mul_zero]
  have key : ∀ i, ∑ x ∈ range (Mβ + 1), ∑ n ∈ range (Mθ - 1 + 1),
      |algebraMap R ℝ (∑ l ∈ range (Mθ + 1), (trigQuotientWeight n l : R) * p.coeffN i 1 x l)| *
        U i x * V 0 n ≤
      ∑ x ∈ range (Mβ + 1), ∑ l ∈ range (Mθ + 1),
        |algebraMap R ℝ (p.coeffN i 1 x l)| * U i x *
          ∑ n ∈ range l, (trigQuotientWeight n l : ℝ) * V 0 n := by
    intro i
    rw [← sum_divSin_aux' Mθ (Mβ + 1) (fun k l ↦ |algebraMap R ℝ (p.coeffN i 1 k l)|) (U i)
      (V 0)]
    refine sum_le_sum fun k _ ↦ sum_le_sum fun n _ ↦ ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (hU _ _)) (hV _ _)
    simp only [map_sum, map_mul, map_intCast]
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun l _ ↦ ?_))
    rw [abs_mul, Int.cast_abs.symm.trans (congrArg _ (abs_of_nonneg ?_))]
    simp only [trigQuotientWeight]
    split_ifs <;> norm_num
  exact add_le_add (key 0) (key 1)

end Eval

/-! ### Single modes -/

section Monomials

theorem dβ_monomial_zero (j : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) (c : R) :
    (monomial 0 j k l c).dβ = monomial 1 j k l (-((k : ℕ) : R) * c) := by
  ext i' j' k' l'
  simp only [dβ, monomial]
  by_cases hi : i' = 0 <;> by_cases hj : j' = j <;> by_cases hk : k' = k <;>
    by_cases hl : l' = l <;> simp_all
  all_goals omega

theorem dβ_monomial_one (j : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) (c : R) :
    (monomial 1 j k l c).dβ = monomial 0 j k l (((k : ℕ) : R) * c) := by
  ext i' j' k' l'
  simp only [dβ, monomial]
  by_cases hi : i' = 0 <;> by_cases hj : j' = j <;> by_cases hk : k' = k <;>
    by_cases hl : l' = l <;> simp_all

theorem dθ_monomial_zero (i : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) (c : R) :
    (monomial i 0 k l c).dθ = monomial i 1 k l (-((l : ℕ) : R) * c) := by
  ext i' j' k' l'
  simp only [dθ, monomial]
  by_cases hi : i' = i <;> by_cases hj : j' = 0 <;> by_cases hk : k' = k <;>
    by_cases hl : l' = l <;> simp_all
  all_goals omega

theorem dθ_monomial_one (i : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) (c : R) :
    (monomial i 1 k l c).dθ = monomial i 0 k l (((l : ℕ) : R) * c) := by
  ext i' j' k' l'
  simp only [dθ, monomial]
  by_cases hi : i' = i <;> by_cases hj : j' = 0 <;> by_cases hk : k' = k <;>
    by_cases hl : l' = l <;> simp_all

end Monomials

end PDE.Analysis.TrigPoly2
