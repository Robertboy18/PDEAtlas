/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.Positivity.Finset

/-!
# The sign of a determinant from a preconditioner

A real matrix `1 + F` with `∑ᵢⱼ Fᵢⱼ² < 1` has positive determinant: the Frobenius norm bounds
the operator norm, so `1 + s F` is nonsingular for `0 ≤ s ≤ 1`, and the determinant cannot
change sign along the segment from `1`
(`det_one_add_pos_of_sum_sq_lt_one`). Hence a matrix `P` with `P X` close to `1` in the
Frobenius norm gives `X` the sign of `det P`, since `det P · det X = det (P X) > 0`
(`det_neg_of_sum_sq_mul_sub_one_lt_one`).

For the sign of a determinant known only through entrywise enclosures `|Xᵢⱼ - X⁰ᵢⱼ| ≤ ε`,
the residual `P X - 1 = (P X⁰ - 1) + P (X - X⁰)` has Frobenius norm at most
`‖P X⁰ - 1‖ + ‖P‖ · n ε` (`sum_sq_mul_sub_one_le`). The preconditioner of choice is the
product `U' L'` of approximate inverses of the factors of `X⁰ = L U`, with `L'` lower
unitriangular and `U'` upper triangular, so that `det P = ∏ᵢ U'ᵢᵢ`
(`det_upper_mul_lower`). The condition number of `X` enters only through `‖P‖`, while the
product of the row norms in Hadamard's bound would require much finer enclosures.
-/

@[expose] public section

open Finset Set

namespace PDE.Analysis.Matrix

variable {n : Type*} [Fintype n]

/-- Cauchy–Schwarz in every row: `|F v|² ≤ ‖F‖²_F |v|²`. -/
theorem sum_sq_mulVec_le (F : _root_.Matrix n n ℝ) (v : n → ℝ) :
    ∑ i, (F.mulVec v) i ^ 2 ≤ (∑ i, ∑ j, F i j ^ 2) * ∑ j, v j ^ 2 := by
  rw [sum_mul]
  refine sum_le_sum fun i _ ↦ ?_
  simp only [_root_.Matrix.mulVec, dotProduct]
  exact sum_mul_sq_le_sq_mul_sq _ _ _

/-- **Frobenius criterion.** A matrix `1 + F` with `∑ᵢⱼ Fᵢⱼ² < 1` has positive determinant. -/
theorem det_one_add_pos_of_sum_sq_lt_one [DecidableEq n] (F : _root_.Matrix n n ℝ)
    (hF : ∑ i, ∑ j, F i j ^ 2 < 1) : 0 < (1 + F).det := by
  have hinj : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ v : n → ℝ, (1 + s • F).mulVec v = 0 → v = 0 := by
    intro s hs v hv
    have hv' : v = -(s • F.mulVec v) := by
      rw [_root_.Matrix.add_mulVec, _root_.Matrix.one_mulVec, _root_.Matrix.smul_mulVec] at hv
      exact eq_neg_of_add_eq_zero_left hv
    have hnorm : ∑ j, v j ^ 2 = s ^ 2 * ∑ i, (F.mulVec v) i ^ 2 := by
      conv_lhs => rw [hv']
      simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, neg_sq, mul_pow, mul_sum]
    have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
    have hle := sum_sq_mulVec_le F v
    have hsum0 : 0 ≤ ∑ i, (F.mulVec v) i ^ 2 := sum_nonneg fun i _ ↦ sq_nonneg _
    have hv0 : 0 ≤ ∑ j, v j ^ 2 := sum_nonneg fun j _ ↦ sq_nonneg _
    have hzero : ∑ j, v j ^ 2 = 0 := by
      by_contra hne
      have hpos : 0 < ∑ j, v j ^ 2 := lt_of_le_of_ne hv0 (Ne.symm hne)
      have h1 : ∑ j, v j ^ 2 ≤ ∑ i, (F.mulVec v) i ^ 2 := by
        rw [hnorm]
        nlinarith
      nlinarith
    funext j
    have := (sum_eq_zero_iff_of_nonneg fun j _ ↦ sq_nonneg (v j)).mp hzero j (mem_univ j)
    simpa using this
  by_contra hle
  push Not at hle
  have hcont : ContinuousOn (fun s : ℝ ↦ (1 + s • F).det) (Set.Icc 0 1) :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det.continuousOn
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' zero_le_one hcont
    (show (0 : ℝ) ∈ Set.Icc _ _ from ⟨by simpa using hle, by simp⟩)
  obtain ⟨v, hv, hv0⟩ := _root_.Matrix.exists_mulVec_eq_zero_iff.mpr hs0
  exact hv (hinj s hs v hv0)

/-- **Preconditioned sign.** If `det P < 0` and `∑ᵢⱼ ((P X - 1)ᵢⱼ)² < 1`, then `det X < 0`. -/
theorem det_neg_of_sum_sq_mul_sub_one_lt_one [DecidableEq n] {P X : _root_.Matrix n n ℝ}
    (hP : P.det < 0) (h : ∑ i, ∑ j, (P * X - 1) i j ^ 2 < 1) : X.det < 0 := by
  have hpos := det_one_add_pos_of_sum_sq_lt_one (P * X - 1) h
  rw [add_sub_cancel, _root_.Matrix.det_mul] at hpos
  by_contra hX
  push Not at hX
  nlinarith

/-- Minkowski's inequality for double sums in the squared form. -/
theorem sum_sum_add_sq_le {a b : n → n → ℝ} {f e : ℝ} (hf : 0 ≤ f) (he : 0 ≤ e)
    (ha : ∑ i, ∑ j, a i j ^ 2 ≤ f ^ 2) (hb : ∑ i, ∑ j, b i j ^ 2 ≤ e ^ 2) :
    ∑ i, ∑ j, (a i j + b i j) ^ 2 ≤ (f + e) ^ 2 := by
  have hcs := sum_mul_sq_le_sq_mul_sq (univ : Finset (n × n)) (fun p ↦ a p.1 p.2)
    (fun p ↦ b p.1 p.2)
  simp only [← univ_product_univ, sum_product] at hcs
  set A := ∑ i, ∑ j, a i j ^ 2
  set B := ∑ i, ∑ j, b i j ^ 2
  set C := ∑ i, ∑ j, a i j * b i j
  have hA0 : 0 ≤ A := sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦ sq_nonneg _
  have hB0 : 0 ≤ B := sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦ sq_nonneg _
  have hexp : ∑ i, ∑ j, (a i j + b i j) ^ 2 = A + 2 * C + B := by
    simp only [A, B, C, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
  have hC : C ≤ f * e := by
    have hC2 : C ^ 2 ≤ (f * e) ^ 2 := by
      calc C ^ 2 ≤ A * B := hcs
        _ ≤ f ^ 2 * e ^ 2 := mul_le_mul ha hb hB0 (sq_nonneg f)
        _ = (f * e) ^ 2 := by ring
    by_contra hlt
    push Not at hlt
    have hfe : 0 ≤ f * e := mul_nonneg hf he
    nlinarith
  rw [hexp]
  nlinarith

/-- The Frobenius norm is submultiplicative, in the squared form. -/
theorem sum_sq_mul_le (P D : _root_.Matrix n n ℝ) :
    ∑ i, ∑ j, (P * D) i j ^ 2 ≤ (∑ i, ∑ k, P i k ^ 2) * ∑ j, ∑ k, D k j ^ 2 := by
  rw [sum_mul_sum]
  refine sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ ?_
  simp only [_root_.Matrix.mul_apply]
  exact sum_mul_sq_le_sq_mul_sq _ _ _

/-- **Perturbed residual.** For `|Xᵢⱼ - X⁰ᵢⱼ| ≤ ε`, `‖P X⁰ - 1‖²_F ≤ f²` and `‖P‖²_F ≤ p²`, the
residual satisfies `‖P X - 1‖²_F ≤ (f + p n ε)²`. -/
theorem sum_sq_mul_sub_one_le [DecidableEq n] {P X X₀ : _root_.Matrix n n ℝ} {f p ε : ℝ}
    (hf0 : 0 ≤ f) (hp0 : 0 ≤ p) (hε : 0 ≤ ε) (hf : ∑ i, ∑ j, (P * X₀ - 1) i j ^ 2 ≤ f ^ 2)
    (hp : ∑ i, ∑ j, P i j ^ 2 ≤ p ^ 2) (hX : ∀ i j, |X i j - X₀ i j| ≤ ε) :
    ∑ i, ∑ j, (P * X - 1) i j ^ 2 ≤ (f + p * (Fintype.card n * ε)) ^ 2 := by
  have hsplit : P * X - 1 = (P * X₀ - 1) + P * (X - X₀) := by
    rw [_root_.Matrix.mul_sub]
    abel
  have hD : ∑ j, ∑ k, (X - X₀) k j ^ 2 ≤ (Fintype.card n * ε) ^ 2 := by
    have hterm : ∀ j k, (X - X₀) k j ^ 2 ≤ ε ^ 2 := fun j k ↦ by
      rw [_root_.Matrix.sub_apply, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hX k j) 2
    calc ∑ j, ∑ k, (X - X₀) k j ^ 2 ≤ ∑ _j : n, ∑ _k : n, ε ^ 2 :=
          sum_le_sum fun j _ ↦ sum_le_sum fun k _ ↦ hterm j k
      _ = (Fintype.card n * ε) ^ 2 := by
          simp only [sum_const, card_univ, nsmul_eq_mul]
          ring
  have hPD : ∑ i, ∑ j, (P * (X - X₀)) i j ^ 2 ≤ (p * (Fintype.card n * ε)) ^ 2 := by
    calc ∑ i, ∑ j, (P * (X - X₀)) i j ^ 2 ≤
          (∑ i, ∑ k, P i k ^ 2) * ∑ j, ∑ k, (X - X₀) k j ^ 2 := sum_sq_mul_le P (X - X₀)
      _ ≤ p ^ 2 * (Fintype.card n * ε) ^ 2 :=
          mul_le_mul hp hD (sum_nonneg fun j _ ↦ sum_nonneg fun k _ ↦ sq_nonneg _)
            (sq_nonneg p)
      _ = (p * (Fintype.card n * ε)) ^ 2 := by ring
  rw [hsplit]
  simp only [_root_.Matrix.add_apply]
  exact sum_sum_add_sq_le hf0 (by positivity) hf hPD

/-- **Sign from enclosures.** If `det P < 0`, `‖P X⁰ - 1‖_F ≤ f`, `‖P‖_F ≤ p` and
`f + p n ε < 1`, every matrix `X` within `ε` of `X⁰` entrywise has negative determinant. -/
theorem det_neg_of_enclosure [DecidableEq n] {P X X₀ : _root_.Matrix n n ℝ} {f p ε : ℝ}
    (hP : P.det < 0) (hf0 : 0 ≤ f) (hp0 : 0 ≤ p) (hε : 0 ≤ ε)
    (hf : ∑ i, ∑ j, (P * X₀ - 1) i j ^ 2 ≤ f ^ 2)
    (hp : ∑ i, ∑ j, P i j ^ 2 ≤ p ^ 2) (hlt : f + p * (Fintype.card n * ε) < 1)
    (hX : ∀ i j, |X i j - X₀ i j| ≤ ε) : X.det < 0 := by
  refine det_neg_of_sum_sq_mul_sub_one_lt_one hP ?_
  have h := sum_sq_mul_sub_one_le hf0 hp0 hε hf hp hX
  have h0 : 0 ≤ f + p * (Fintype.card n * ε) := by positivity
  nlinarith

/-- An upper triangular matrix times a lower unitriangular one has the product of the
diagonal of the first as its determinant. -/
theorem det_upper_mul_lower {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {U L : _root_.Matrix ι ι ℝ} (hU : U.IsUpperTriangular) (hL : L.IsLowerTriangular)
    (hL1 : ∀ i, L i i = 1) : (U * L).det = ∏ i, U i i := by
  rw [_root_.Matrix.det_mul, _root_.Matrix.det_of_isUpperTriangular hU,
    _root_.Matrix.det_of_isLowerTriangular L hL]
  simp [hL1]

end PDE.Analysis.Matrix
