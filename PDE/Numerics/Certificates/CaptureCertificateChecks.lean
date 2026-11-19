/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Numerics.LowRankLDL
public import CAS.Numerics.MatrixPositivity
public import CAS.Numerics.TrigTable
public import PDE.Analysis.Matrix.CenterCertificates

/-!
# Small Gram checks for capture certificates

The capture certificates on `N` trial functions with `m` captured modes need, besides the large
packed check, bounds for a few `m × m` Gram matrices of `N`-vectors: `|C v| ≤ ζ |v|` for the
coefficient columns and `|Λ⁻¹ Vᵀ x| ≤ κ |x|` for the approximate products. Both follow from a
dense `LDLᵀ` check (`ldltCheck`) of `ζ² I - Cᵀ C` and of `κ² Λ² - Vᵀ V`, whose integer entries
are formed by `intGram`, one packed product of the transposed columns with the rows.
-/

@[expose] public section

open Finset

namespace CAS.Numerics

/-- The integer Gram matrix `Xᵀ Y` by packed row combinations. -/
def intGram {N m : ℕ} (w : ℕ) (X Y : Fin N → Fin m → ℤ) : Fin m → Fin m → ℤ :=
  packedMatMul w (fun i k ↦ X k i) Y

theorem intGram_eq {N m w a b : ℕ} (X Y : Fin N → Fin m → ℤ) (ha : ∀ k i, (X k i).natAbs ≤ a)
    (hb : ∀ k j, (Y k j).natAbs ≤ b) (hw : 2 * N * a * b < 2 ^ w) (i j : Fin m) :
    intGram w X Y i j = ∑ k, X k i * Y k j := by
  unfold intGram
  rw [packedMatMul_eq w _ Y (fun i k ↦ ha k i) hb hw]

/-- Stored rows equal to the packed product rows hold the Gram entries. -/
theorem signedSlot_eq_gram_of_rows {N m w a b : ℕ} (X Y : Fin N → Fin m → ℤ)
    (ha : ∀ k i, (X k i).natAbs ≤ a) (hb : ∀ k j, (Y k j).natAbs ≤ b) (hw : 2 * N * a * b < 2 ^ w)
    {rows : ℕ → ℕ} (hrows : ∀ i : Fin m, rows i.val = packedMatMulRow w (fun i k ↦ X k i) Y i)
    (i j : Fin m) : signedSlot w j.val (rows i.val) = ∑ k, X k i * Y k j := by
  rw [hrows]
  exact signedSlot_packedMatMulRow w _ Y (fun i k ↦ ha k i) hb hw i j

/-- The form of `diag(a) - c G`. -/
theorem quadForm_diagonal_sub {m : ℕ} (a : Fin m → ℝ) (c : ℝ) (G : Fin m → Fin m → ℝ)
    (u : Fin m → ℝ) :
    ∑ i, ∑ j, ((if i = j then a i else 0) - c * G i j) * u i * u j =
      ∑ i, a i * u i ^ 2 - c * ∑ i, ∑ j, G i j * u i * u j := by
  simp only [sub_mul, sum_sub_distrib, ite_mul, zero_mul, sum_ite_eq, mem_univ, ite_true,
    mul_sum]
  congr 1
  · exact sum_congr rfl fun i _ ↦ by ring
  · exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring

/-- The integer matrix `num 2^e diag(D) - den G` of a Gram bound. -/
def gramBoundMatrix {m : ℕ} (D : Fin m → ℤ) (G : Fin m → Fin m → ℤ) (num den e : ℕ) :
    Fin m → Fin m → ℤ :=
  fun i j ↦ (if i = j then (num : ℤ) * 2 ^ e * D i else 0) - den * G i j

/-- A passing dense check of `num 2^e diag(D) - den G` gives `den uᵀ G u ≤ num 2^e uᵀ D u`. -/
theorem quadForm_le_of_gramBoundCheck {m : ℕ} {D : Fin m → ℤ} {G : Fin m → Fin m → ℤ}
    {num den e s : ℕ} {L : Fin m → Fin m → ℤ} {d : Fin m → ℕ}
    (h : ldltCheck (gramBoundMatrix D G num den e) L d s 0 = true) (u : Fin m → ℝ) :
    (den : ℝ) * ∑ i, ∑ j, (G i j : ℝ) * u i * u j ≤
      (num : ℝ) * 2 ^ e * ∑ i, (D i : ℝ) * u i ^ 2 := by
  have h0 := quadForm_ge_of_ldltCheck _ L d s 0 h u
  simp only [Rat.cast_zero, zero_mul] at h0
  have hs : (0 : ℝ) < 2 ^ s := by positivity
  have hsum : ∑ i, ∑ j, ((gramBoundMatrix D G num den e i j : ℤ) : ℝ) / 2 ^ s * u i * u j =
      (∑ i, ((num : ℝ) * 2 ^ e * D i) * u i ^ 2 -
        (den : ℝ) * ∑ i, ∑ j, (G i j : ℝ) * u i * u j) / 2 ^ s := by
    rw [← quadForm_diagonal_sub, sum_div]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [sum_div]
    refine sum_congr rfl fun j _ ↦ ?_
    simp only [gramBoundMatrix]
    push_cast
    split_ifs <;> ring
  rw [hsum] at h0
  have h1 := (div_nonneg_iff.mp h0)
  have h2 : 0 ≤ ∑ i, ((num : ℝ) * 2 ^ e * D i) * u i ^ 2 -
      (den : ℝ) * ∑ i, ∑ j, (G i j : ℝ) * u i * u j := by
    rcases h1 with ⟨ha, _⟩ | ⟨_, hb⟩
    · exact ha
    · exact absurd hb (not_le.mpr hs)
  have h3 : ∑ i, ((num : ℝ) * 2 ^ e * D i) * u i ^ 2 =
      (num : ℝ) * 2 ^ e * ∑ i, (D i : ℝ) * u i ^ 2 := by
    rw [mul_sum]; exact sum_congr rfl fun i _ ↦ by ring
  linarith

/-- A passing dense check of an integer matrix that is a positive multiple `c Q` of a real
matrix `Q` makes the form of `Q` nonnegative: the bridge from the integer certificates of the
small fields (`ε₃`, `ε₄`, Gram) to their real forms. -/
theorem quadForm_nonneg_of_ldltCheck_eq {m s : ℕ} {M L : Fin m → Fin m → ℤ} {d : Fin m → ℕ}
    (h : ldltCheck M L d s 0 = true) {Q : Fin m → Fin m → ℝ} {c : ℝ} (hc : 0 < c)
    (hM : ∀ i j, (M i j : ℝ) = c * Q i j) (u : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, Q i j * u i * u j := by
  have h0 := quadForm_ge_of_ldltCheck M L d s 0 h u
  simp only [Rat.cast_zero, zero_mul, hM] at h0
  have hs : (0 : ℝ) < 2 ^ s := by positivity
  have heq : ∑ i, ∑ j, c * Q i j / 2 ^ s * u i * u j =
      c / 2 ^ s * ∑ i, ∑ j, Q i j * u i * u j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [heq] at h0
  exact (mul_nonneg_iff_of_pos_left (div_pos hc hs)).mp h0

/-- **Norm of the coefficient columns.** For `C̃ = Ct / 2^c`, a passing check of
`a² 2^(2c) I - b² Ctᵀ Ct` gives `|C̃ v| ≤ (a / b) |v|`. -/
theorem sum_sq_le_of_gramCheck {N m c a b s : ℕ} (Ct : Fin N → Fin m → ℤ)
    {G : Fin m → Fin m → ℤ} (hG : ∀ i j, G i j = ∑ k, Ct k i * Ct k j) (hb : 0 < b)
    {L : Fin m → Fin m → ℤ} {d : Fin m → ℕ}
    (h : ldltCheck (gramBoundMatrix (fun _ ↦ 1) G (a ^ 2) (b ^ 2) (2 * c)) L d s 0 = true)
    (v : Fin m → ℝ) :
    ∑ l, (∑ j, ((Ct l j : ℝ) / 2 ^ c) * v j) ^ 2 ≤ ((a : ℝ) / b) ^ 2 * ∑ j, v j ^ 2 := by
  have hq := quadForm_le_of_gramBoundCheck h v
  simp only [Int.cast_one, one_mul, hG] at hq
  push_cast at hq
  rw [PDE.Analysis.Matrix.sum_sq_sum_mul_eq_gram]
  have hb' : (0 : ℝ) < (b : ℝ) ^ 2 := by positivity
  have hc : (0 : ℝ) < 2 ^ (2 * c) := by positivity
  have heq : ∑ i, ∑ j, (∑ l, (Ct l i : ℝ) / 2 ^ c * ((Ct l j : ℝ) / 2 ^ c)) * v i * v j =
      (∑ i, ∑ j, (∑ l, (Ct l i : ℝ) * Ct l j) * v i * v j) / 2 ^ (2 * c) := by
    rw [sum_div]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [sum_div]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [sum_mul, sum_mul, sum_mul, sum_mul, sum_div]
    refine sum_congr rfl fun l _ ↦ ?_
    rw [pow_mul']
    field_simp
  rw [heq, div_le_iff₀ hc, div_pow]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hb']
  nlinarith [hq]

/-- **Norm of `x ↦ Λ⁻¹ Vᵀ x`.** For `Ṽ = Vt / 2^t` and `μ = lamNum / 2^c > 0`, a passing check
of `a² 2^(2t) diag(lamNum²) - b² 2^(2c) Vtᵀ Vt` gives `∑_j ((Ṽᵀ x)_j / μ_j)² ≤ (a / b)² |x|²`. -/
theorem sum_sq_div_le_of_gramCheck {N m c t a b s : ℕ} (Vt : Fin N → Fin m → ℤ)
    (lamNum : Fin m → ℤ) (hlam : ∀ j, lamNum j ≠ 0)
    {G : Fin m → Fin m → ℤ} (hG : ∀ i j, G i j = ∑ k, Vt k i * Vt k j) (hb : 0 < b)
    {L : Fin m → Fin m → ℤ} {d : Fin m → ℕ}
    (h : ldltCheck (gramBoundMatrix (fun j ↦ lamNum j ^ 2) G (a ^ 2)
      (b ^ 2 * 2 ^ (2 * c)) (2 * t)) L d s 0 = true) (x : Fin N → ℝ) :
    ∑ j, ((∑ k, x k * ((Vt k j : ℝ) / 2 ^ t)) / ((lamNum j : ℝ) / 2 ^ c)) ^ 2 ≤
      ((a : ℝ) / b) ^ 2 * ∑ k, x k ^ 2 := by
  refine PDE.Analysis.Matrix.sum_sq_div_le_of_gram
    (fun j ↦ div_ne_zero (by exact_mod_cast hlam j) (by positivity)) (fun u ↦ ?_) x
  have hq := quadForm_le_of_gramBoundCheck h u
  simp only [hG] at hq
  push_cast at hq
  have hb' : (0 : ℝ) < (b : ℝ) ^ 2 * 2 ^ (2 * c) := by positivity
  have ht : (0 : ℝ) < 2 ^ (2 * t) := by positivity
  have hl : ∑ i, ∑ j, (∑ k, (Vt k i : ℝ) / 2 ^ t * ((Vt k j : ℝ) / 2 ^ t)) * u i * u j =
      (∑ i, ∑ j, (∑ k, (Vt k i : ℝ) * Vt k j) * u i * u j) / 2 ^ (2 * t) := by
    rw [sum_div]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [sum_div]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [sum_mul, sum_mul, sum_mul, sum_mul, sum_div]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [pow_mul']
    field_simp
  have hr : ((a : ℝ) / b) ^ 2 * ∑ j, ((lamNum j : ℝ) / 2 ^ c) ^ 2 * u j ^ 2 =
      ((a : ℝ) ^ 2 * 2 ^ (2 * t) * ∑ j, ((lamNum j : ℝ) ^ 2) * u j ^ 2) /
        ((b : ℝ) ^ 2 * 2 ^ (2 * c)) / 2 ^ (2 * t) := by
    rw [mul_sum, mul_sum, sum_div, sum_div]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [pow_mul', pow_mul']
    field_simp
  rw [hl, hr, div_le_div_iff_of_pos_right ht, le_div_iff₀ hb']
  nlinarith [hq]

/-- The rounded scaled coefficient column `j`, `round(Cnum l j 2^(p l) / 2^(c - s))`, read at
natural indices. -/
def roundedColumn {N m : ℕ} (Cnum : Fin N → Fin m → ℤ) (pexp : Fin N → ℕ) (c s : ℕ) (j : Fin m)
    (l : ℕ) : ℤ :=
  if h : l < N then roundShift (c - s) (Cnum ⟨l, h⟩ j * 2 ^ pexp ⟨l, h⟩) else 0

/-- **Product checks to a Frobenius bound.** If the guard checks of `productRow` pass for every
column with the rounded coefficients, then the Frobenius norm of `ã C̃ - Ṽ` is at most `Φ`,
for `ã k l = A l k / 2^(s_A)`, `C̃ l j = Cnum l j 2^(p l) / 2^c` and `Ṽ k j = V k j / 2^(t_V)`. -/
theorem frobenius_le_of_productChecks {N m w αv sA sC tV gb ab vb BB c : ℕ}
    {Arow Vcol : ℕ → ℕ} (Cnum : Fin N → Fin m → ℤ) (pexp : Fin N → ℕ) (hc : sC + 1 ≤ c)
    (htV : tV ≤ sA + sC) (hgb : gb < w) (hab : ab < w) (hvb : vb < w)
    (hAg : ∀ l < N, signedGuardCheck w ab N (Arow l) = true)
    (hVg : ∀ j < m, signedGuardCheck w vb N (Vcol j) = true)
    (hCr : ∀ (j : Fin m) (l : ℕ), (roundedColumn Cnum pexp c sC j l).natAbs ≤ BB)
    (hαb : BB ≤ αv) (hαc : 2 ^ (sA + sC - tV) ≤ αv)
    (hfit : 2 * (N * (BB * slotBias ab) + 2 ^ (sA + sC - tV) * slotBias vb) < 2 ^ w)
    (hcheck : ∀ j : Fin m, signedGuardCheck w gb N (productRow w N αv (2 ^ (sA + sC - tV)) Arow
      (roundedColumn Cnum pexp c sC j) (Vcol j.val)) = true)
    {η Φ : ℝ} (hη : (slotBias gb : ℝ) / 2 ^ (sA + sC) +
      N * ((slotBias ab : ℝ) / 2 ^ sA) * (1 / 2 ^ (sC + 1)) ≤ η)
    (hΦ : (N : ℝ) * m * η ^ 2 ≤ Φ ^ 2) :
    ∑ k : Fin N, ∑ j : Fin m, (∑ l : Fin N, ((signedSlot w k.val (Arow l.val) : ℝ) / 2 ^ sA) *
      ((Cnum l j : ℝ) * 2 ^ pexp l / 2 ^ c) - (signedSlot w k.val (Vcol j.val) : ℝ) / 2 ^ tV) ^ 2
      ≤ Φ ^ 2 := by
  have hA : ∀ l < N, Arow l < 2 ^ (w * N) := fun l hl ↦ lt_of_signedGuardCheck (hAg l hl)
  have hAb : ∀ l < N, ∀ k' < N, (signedSlot w k' (Arow l)).natAbs ≤ slotBias ab :=
    fun l hl k' hk' ↦ natAbs_signedSlot_le_of_signedGuardCheck hab (hAg l hl) hk'
  have hentry : ∀ (k : Fin N) (j : Fin m), |∑ l : Fin N, ((signedSlot w k.val (Arow l.val) : ℝ) /
      2 ^ sA) * ((Cnum l j : ℝ) * 2 ^ pexp l / 2 ^ c) -
        (signedSlot w k.val (Vcol j.val) : ℝ) / 2 ^ tV| ≤ η := by
    intro k j
    have hV : Vcol j.val < 2 ^ (w * N) := lt_of_signedGuardCheck (hVg j j.isLt)
    have hVb : ∀ k' < N, (signedSlot w k' (Vcol j.val)).natAbs ≤ slotBias vb :=
      fun k' hk' ↦ natAbs_signedSlot_le_of_signedGuardCheck hvb (hVg j j.isLt) hk'
    have h1 := abs_product_sub_le_of_guard hgb htV (hcheck j) hA hAb hV hVb
      (fun l _ ↦ hCr j l) hαb hαc hfit k.isLt
    rw [← Fin.sum_univ_eq_sum_range (fun l ↦ ((signedSlot w k (Arow l) : ℝ) / 2 ^ sA) *
      ((roundedColumn Cnum pexp c sC j l : ℝ) / 2 ^ sC))] at h1
    have hround : ∀ l : Fin N, |((roundedColumn Cnum pexp c sC j l.val : ℝ) / 2 ^ sC) -
        (Cnum l j : ℝ) * 2 ^ pexp l / 2 ^ c| ≤ 1 / 2 ^ (sC + 1) := by
      intro l
      have hr := abs_roundShift_sub_le (c - sC) (by omega) (Cnum l j * 2 ^ pexp l)
      simp only [roundedColumn, l.isLt, dite_true]
      have hsplit : (2 : ℝ) ^ c = 2 ^ (c - sC) * 2 ^ sC := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]
      have heq : ((roundShift (c - sC) (Cnum l j * 2 ^ pexp l) : ℤ) : ℝ) / 2 ^ sC -
          (Cnum l j : ℝ) * 2 ^ pexp l / 2 ^ c =
          (((roundShift (c - sC) (Cnum l j * 2 ^ pexp l) : ℤ) : ℝ) -
            ((Cnum l j * 2 ^ pexp l : ℤ) : ℝ) / 2 ^ (c - sC)) / 2 ^ sC := by
        rw [hsplit]; push_cast; field_simp
      rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ sC), pow_succ]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hr, (by positivity : (0 : ℝ) < 2 ^ sC)]
    have h2 : |∑ l : Fin N, ((signedSlot w k.val (Arow l.val) : ℝ) / 2 ^ sA) *
        (((roundedColumn Cnum pexp c sC j l.val : ℝ) / 2 ^ sC) -
          (Cnum l j : ℝ) * 2 ^ pexp l / 2 ^ c)| ≤
        N * ((slotBias ab : ℝ) / 2 ^ sA) * (1 / 2 ^ (sC + 1)) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ l : Fin N, |((signedSlot w k.val (Arow l.val) : ℝ) / 2 ^ sA) *
            (((roundedColumn Cnum pexp c sC j l.val : ℝ) / 2 ^ sC) -
              (Cnum l j : ℝ) * 2 ^ pexp l / 2 ^ c)| ≤
          ∑ _l : Fin N, ((slotBias ab : ℝ) / 2 ^ sA) * (1 / 2 ^ (sC + 1)) := by
            refine sum_le_sum fun l _ ↦ ?_
            rw [abs_mul]
            refine mul_le_mul ?_ (hround l) (abs_nonneg _) (by positivity)
            rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ sA)]
            refine div_le_div_of_nonneg_right ?_ (by positivity)
            have := hAb l l.isLt k k.isLt
            rw [← Int.cast_abs, Int.abs_eq_natAbs]
            exact_mod_cast this
        _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    have hsum : ∑ l : Fin N, ((signedSlot w k.val (Arow l.val) : ℝ) / 2 ^ sA) *
        ((Cnum l j : ℝ) * 2 ^ pexp l / 2 ^ c) - (signedSlot w k.val (Vcol j.val) : ℝ) / 2 ^ tV =
        (∑ l : Fin N, ((signedSlot w k.val (Arow l.val) : ℝ) / 2 ^ sA) *
          ((roundedColumn Cnum pexp c sC j l.val : ℝ) / 2 ^ sC) -
            (signedSlot w k.val (Vcol j.val) : ℝ) / 2 ^ tV) -
        ∑ l : Fin N, ((signedSlot w k.val (Arow l.val) : ℝ) / 2 ^ sA) *
          (((roundedColumn Cnum pexp c sC j l.val : ℝ) / 2 ^ sC) -
            (Cnum l j : ℝ) * 2 ^ pexp l / 2 ^ c) := by
      have hd : ∑ l : Fin N, ((signedSlot w k.val (Arow l.val) : ℝ) / 2 ^ sA) *
          (((roundedColumn Cnum pexp c sC j l.val : ℝ) / 2 ^ sC) -
            (Cnum l j : ℝ) * 2 ^ pexp l / 2 ^ c) =
          ∑ l : Fin N, ((signedSlot w k.val (Arow l.val) : ℝ) / 2 ^ sA) *
            ((roundedColumn Cnum pexp c sC j l.val : ℝ) / 2 ^ sC) -
          ∑ l : Fin N, ((signedSlot w k.val (Arow l.val) : ℝ) / 2 ^ sA) *
            ((Cnum l j : ℝ) * 2 ^ pexp l / 2 ^ c) := by
        rw [← sum_sub_distrib]
        exact sum_congr rfl fun l _ ↦ by ring
      rw [hd]
      ring
    rw [hsum]
    exact (abs_sub _ _).trans (by linarith)
  have hsq : ∀ (k : Fin N) (j : Fin m), (∑ l : Fin N, ((signedSlot w k.val (Arow l.val) : ℝ) /
      2 ^ sA) * ((Cnum l j : ℝ) * 2 ^ pexp l / 2 ^ c) -
        (signedSlot w k.val (Vcol j.val) : ℝ) / 2 ^ tV) ^ 2 ≤ η ^ 2 := fun k j ↦
    sq_le_sq' (abs_le.mp (hentry k j)).1 (abs_le.mp (hentry k j)).2
  calc _ ≤ ∑ _k : Fin N, ∑ _j : Fin m, η ^ 2 :=
        sum_le_sum fun k _ ↦ sum_le_sum fun j _ ↦ hsq k j
    _ = (N : ℝ) * m * η ^ 2 := by simp [sum_const, card_univ]; ring
    _ ≤ Φ ^ 2 := hΦ

open Matrix in
/-- **The capture matrix certificate from packed checks.** Let `C = τ V₀` with
`V₀ k j = Cnum k j / 2^c`, `μ j = lamNum j / 2^(c_μ)`, scaling `σ k = 2^(q - p k)`, center
`ã k l = A l k / 2^(s_A)` (stored rows `Arow`) and approximate products `Ṽ k j = V k j / 2^(t_V)`
(stored columns `Vcol`). If the packed `LDLᵀ` row checks of `-ã + diag(g) + Ṽ diag(t) Ṽᵀ`, the
product checks of `ã C̃₀ ≈ Ṽ`, the Gram checks of `ζ` and `κ`, the weight bounds and the numeric
budget pass, then every `S` with `σ S σ` within the bilinear bound `ε_S` of `ã`, and every `e` with
`g k / 2^P ≤ K σ_k² e_k`, gives `K diag(e) - S + (S C) Λ⁻¹ (S C)ᵀ ⪰ 0`. -/
theorem captureMatrix_nonneg_of_packedChecks {m : ℕ} (p : PackedLDLParams)
    (S : Matrix (Fin p.size) (Fin p.size) ℝ) (e : Fin p.size → ℝ)
    (C : Matrix (Fin p.size) (Fin m) ℝ) (μ : Fin m → ℝ) (K τ : ℝ)
    (Cnum : Fin p.size → Fin m → ℤ) (lamNum : Fin m → ℤ) (pexp : Fin p.size → ℕ) {c cμ q : ℕ}
    {Arow Vcol t g Urow d : ℕ → ℕ} {α αv sA sC tV tW gb ab vb BB T G : ℕ}
    {ζa ζb κa κb wζ wκ sζ sκ Aζ : ℕ} {Lζ Lκ : Fin m → Fin m → ℤ} {dζ dκ : Fin m → ℕ}
    {τc εS Φ η : ℝ}
    (hτ : 0 < τ) (hC : ∀ k j, C k j = τ * ((Cnum k j : ℝ) / 2 ^ c))
    (hμ : ∀ j, μ j = (lamNum j : ℝ) / 2 ^ cμ) (hlam : ∀ j, 0 < lamNum j) (hK : 0 < K)
    (hp : p.valid = true) (hscale : 0 < p.scale) (hsA : sA ≤ 2 * tV + tW)
    (hrows : ∀ i < p.size, ldltRowCheck p
      (lowRankRow p.width p.size m α (2 ^ (2 * tV + tW - sA)) Arow Vcol t g) Urow d i = true)
    (hAg : ∀ i < p.size, signedGuardCheck p.width ab p.size (Arow i) = true)
    (hab : ab < p.width)
    (hVg : ∀ j < m, signedGuardCheck p.width vb p.size (Vcol j) = true) (hvb : vb < p.width)
    (ht : ∀ j < m, t j ≤ T) (hg : ∀ i < p.size, g i ≤ G) (hαc : 2 ^ (2 * tV + tW - sA) ≤ α)
    (hαV : slotBias vb * T ≤ α)
    (hfit : 2 * (m * (slotBias vb * T * slotBias vb) + 2 ^ (2 * tV + tW - sA) * slotBias ab + G)
      < 2 ^ p.width)
    (hτc : p.scale * 2 ^ (2 * tV + tW) * τc + p.size * slotBias p.residualBits ≤ p.shift)
    (hw : ∀ j : Fin m, (t j.val : ℝ) / 2 ^ tW ≤ τ ^ 2 / μ j)
    (hc : sC + 1 ≤ c + q) (htV : tV ≤ sA + sC) (hgb : gb < p.width)
    (hCr : ∀ (j : Fin m) (l : ℕ), (roundedColumn Cnum pexp (c + q) sC j l).natAbs ≤ BB)
    (hαb : BB ≤ αv) (hαc' : 2 ^ (sA + sC - tV) ≤ αv)
    (hfit' : 2 * (p.size * (BB * slotBias ab) + 2 ^ (sA + sC - tV) * slotBias vb) < 2 ^ p.width)
    (hcheck : ∀ j : Fin m, signedGuardCheck p.width gb p.size (productRow p.width p.size αv
      (2 ^ (sA + sC - tV)) Arow (roundedColumn Cnum pexp (c + q) sC j) (Vcol j.val)) = true)
    (hη : (slotBias gb : ℝ) / 2 ^ (sA + sC) +
      p.size * ((slotBias ab : ℝ) / 2 ^ sA) * (1 / 2 ^ (sC + 1)) ≤ η)
    (hΦ0 : 0 ≤ Φ) (hΦ : (p.size : ℝ) * m * η ^ 2 ≤ Φ ^ 2)
    (hAζ : ∀ k j, (Cnum k j * 2 ^ pexp k).natAbs ≤ Aζ) (hwζ : 2 * p.size * Aζ * Aζ < 2 ^ wζ)
    {rowsζ rowsκ : ℕ → ℕ}
    (hrowsζ : ∀ i : Fin m, rowsζ i.val = packedMatMulRow wζ (fun i k ↦ Cnum k i * 2 ^ pexp k)
      (fun k j ↦ Cnum k j * 2 ^ pexp k) i)
    (hζb : 0 < ζb)
    (hζ : ldltCheck (gramBoundMatrix (fun _ ↦ 1) (fun i j ↦ signedSlot wζ j.val (rowsζ i.val))
      (ζa ^ 2) (ζb ^ 2) (2 * (c + q))) Lζ dζ sζ 0 = true)
    (hwκ : 2 * p.size * slotBias vb * slotBias vb < 2 ^ wκ)
    (hrowsκ : ∀ i : Fin m, rowsκ i.val = packedMatMulRow wκ
      (fun (i : Fin m) (k : Fin p.size) ↦ signedSlot p.width k.val (Vcol i.val))
      (fun (k : Fin p.size) (j : Fin m) ↦ signedSlot p.width k.val (Vcol j.val)) i)
    (hκb : 0 < κb)
    (hκ : ldltCheck (gramBoundMatrix (fun j ↦ lamNum j ^ 2)
      (fun i j ↦ signedSlot wκ j.val (rowsκ i.val))
      (κa ^ 2) (κb ^ 2 * 2 ^ (2 * cμ)) (2 * tV)) Lκ dκ sκ 0 = true)
    (hν : εS * (1 + 2 * ((ζa : ℝ) / ζb) * (((κa : ℝ) / κb) * τ ^ 2)) +
      2 * (((κa : ℝ) / κb) * τ ^ 2) * Φ ≤ τc)
    (hS : PDE.Analysis.Matrix.BilinearBound (fun k l ↦ (2 : ℝ) ^ q * ((2 : ℝ) ^ pexp k)⁻¹ *
      S k l * ((2 : ℝ) ^ q * ((2 : ℝ) ^ pexp l)⁻¹) -
        (signedSlot p.width k.val (Arow l.val) : ℝ) / 2 ^ sA) εS)
    (he : ∀ k, (g k.val : ℝ) / 2 ^ (2 * tV + tW) ≤
      K * (((2 : ℝ) ^ q * ((2 : ℝ) ^ pexp k)⁻¹) ^ 2 * e k))
    (x : Fin p.size → ℝ) :
    0 ≤ x ⬝ᵥ ((K • diagonal e - S + (S * C) * diagonal (fun j ↦ (μ j)⁻¹) * (S * C)ᵀ) *ᵥ x) := by
  set σ : Fin p.size → ℝ := fun k ↦ (2 : ℝ) ^ q * ((2 : ℝ) ^ pexp k)⁻¹ with hσdef
  have hσ : ∀ k, σ k ≠ 0 := fun k ↦ by simp [σ]
  set V₀ : Matrix (Fin p.size) (Fin m) ℝ := Matrix.of fun k j ↦ (Cnum k j : ℝ) / 2 ^ c
  have hμpos : ∀ j, 0 < μ j := fun j ↦ by
    rw [hμ j]; exact div_pos (by exact_mod_cast hlam j) (by positivity)
  set μ' : Fin m → ℝ := fun j ↦ μ j / τ ^ 2
  have hμ'pos : ∀ j, 0 < μ' j := fun j ↦ div_pos (hμpos j) (by positivity)
  -- the field as sums, with `C = τ V₀` absorbed into `μ'`
  have hform : x ⬝ᵥ ((K • diagonal e - S + (S * C) * diagonal (fun j ↦ (μ j)⁻¹) * (S * C)ᵀ) *ᵥ
      x) = K * ∑ k, e k * x k ^ 2 - ∑ k, ∑ l, S k l * x k * x l +
        ∑ j, (∑ k, x k * ∑ l, S k l * V₀ l j) ^ 2 / μ' j := by
    rw [PDE.Analysis.Matrix.captureMatrix_dotProduct_eq]
    congr 1
    refine sum_congr rfl fun j _ ↦ ?_
    have hrow : ∑ k, x k * ∑ l, S k l * C l j = τ * ∑ k, x k * ∑ l, S k l * V₀ l j := by
      rw [mul_sum]
      refine sum_congr rfl fun k _ ↦ ?_
      rw [mul_sum, mul_sum, mul_sum]
      refine sum_congr rfl fun l _ ↦ ?_
      simp only [V₀, Matrix.of_apply, hC]
      ring
    rw [hrow]
    simp only [μ']
    field_simp
  rw [hform]
  have heq := PDE.Analysis.Matrix.capture_form_scale hσ K e (fun k l ↦ S k l)
    (fun l j ↦ V₀ l j) μ' x
  beta_reduce at heq
  rw [← heq]
  -- the center certificate from the packed rows
  have hA : ∀ i < p.size, Arow i < 2 ^ (p.width * p.size) :=
    fun i hi ↦ lt_of_signedGuardCheck (hAg i hi)
  have hAb : ∀ i < p.size, ∀ l < p.size, (signedSlot p.width l (Arow i)).natAbs ≤ slotBias ab :=
    fun i hi l hl ↦ natAbs_signedSlot_le_of_signedGuardCheck hab (hAg i hi) hl
  have hV : ∀ j < m, Vcol j < 2 ^ (p.width * p.size) :=
    fun j hj ↦ lt_of_signedGuardCheck (hVg j hj)
  have hVb : ∀ j < m, ∀ l < p.size, (signedSlot p.width l (Vcol j)).natAbs ≤ slotBias vb :=
    fun j hj l hl ↦ natAbs_signedSlot_le_of_signedGuardCheck hvb (hVg j hj) hl
  have hcert := capture_center_form_of_lowRankRowCheck p hp hscale hsA hrows hA hAb hV hVb ht hg
    hαc hαV hfit hK hτc
  -- the remaining hypotheses of the core
  have hζ' := sum_sq_le_of_gramCheck (fun k j ↦ Cnum k j * 2 ^ pexp k)
    (signedSlot_eq_gram_of_rows _ _ hAζ hAζ hwζ hrowsζ) hζb hζ
  have hκ' := sum_sq_div_le_of_gramCheck
    (fun (k : Fin p.size) (j : Fin m) ↦ signedSlot p.width k.val (Vcol j.val)) lamNum
    (fun j ↦ (hlam j).ne') (signedSlot_eq_gram_of_rows _ _
      (fun k j ↦ hVb j j.isLt k k.isLt) (fun k j ↦ hVb j j.isLt k k.isLt) hwκ hrowsκ) hκb hκ
  have hΦ' := frobenius_le_of_productChecks (c := c + q) (Arow := Arow) (Vcol := Vcol) Cnum pexp hc
    htV hgb hab
    hvb hAg hVg hCr hαb hαc' hfit' hcheck hη hΦ
  have hκ₀ : (0 : ℝ) ≤ (κa : ℝ) / κb * τ ^ 2 := by positivity
  have hζ₀ : (0 : ℝ) ≤ (ζa : ℝ) / ζb := by positivity
  refine PDE.Analysis.Matrix.capture_form_nonneg_of_center
    (S := fun k l ↦ σ k * S k l * σ l) (e := fun k ↦ σ k ^ 2 * e k)
    (C := fun l j ↦ V₀ l j / σ l) (μ := μ') (K := K) (a := fun k l ↦
      (signedSlot p.width k.val (Arow l.val) : ℝ) / 2 ^ sA)
    (elo := fun k ↦ (g k.val : ℝ) / 2 ^ (2 * tV + tW) / K)
    (V := fun k j ↦ (signedSlot p.width k.val (Vcol j.val) : ℝ) / 2 ^ tV)
    (w := fun j ↦ (t j.val : ℝ) / 2 ^ tW) (ζ := (ζa : ℝ) / ζb) (κ₀ := (κa : ℝ) / κb * τ ^ 2)
    (Φ := Φ) (ν := τc) hS hK.le ?_ hμ'pos ?_ hζ₀ ?_ hκ₀ ?_ hΦ0 ?_ hν ?_ (fun k ↦ x k / σ k)
  · intro k
    have := he k
    rw [div_le_iff₀ hK]
    simp only [σ]
    linarith
  · intro j
    rw [inv_div]
    exact hw j
  · intro v
    have h := hζ' v
    refine le_of_eq_of_le (sum_congr rfl fun l _ ↦ ?_) h
    congr 1
    refine sum_congr rfl fun j _ ↦ ?_
    simp only [V₀, Matrix.of_apply, σ]
    push_cast
    rw [pow_add]
    field_simp
  · intro y
    have h := hκ' y
    calc ∑ j, ((∑ k, y k * ((signedSlot p.width k.val (Vcol j.val) : ℝ) / 2 ^ tV)) / μ' j) ^ 2
        = (τ ^ 2) ^ 2 * ∑ j, ((∑ k, y k * ((signedSlot p.width k.val (Vcol j.val) : ℝ) /
            2 ^ tV)) / ((lamNum j : ℝ) / 2 ^ cμ)) ^ 2 := by
          rw [mul_sum]
          refine sum_congr rfl fun j _ ↦ ?_
          simp only [μ', hμ j]
          field_simp
      _ ≤ (τ ^ 2) ^ 2 * (((κa : ℝ) / κb) ^ 2 * ∑ k, y k ^ 2) := by gcongr
      _ = ((κa : ℝ) / κb * τ ^ 2) ^ 2 * ∑ k, y k ^ 2 := by ring
  · refine le_of_eq_of_le (sum_congr rfl fun k _ ↦ sum_congr rfl fun j _ ↦ ?_) hΦ'
    congr 1
    congr 1
    refine sum_congr rfl fun l _ ↦ ?_
    simp only [V₀, Matrix.of_apply, σ]
    rw [pow_add]
    field_simp
  · intro y
    have h := hcert y
    refine h.trans_eq ?_
    rfl

/-! ### The `ε₃` certificate -/

/-- The integer matrix `A₁ (G + Gᵀ) - diag(B₁ Ln + C₁)` of the `ε₃` certificate. -/
def gramCertMatrix {m : ℕ} (G : Fin m → Fin m → ℤ) (Ln : Fin m → ℤ) (A₁ B₁ C₁ : ℕ) :
    Fin m → Fin m → ℤ :=
  fun i j ↦ (A₁ : ℤ) * (G i j + G j i) - if i = j then (B₁ : ℤ) * Ln i + C₁ else 0

/-- **The `ε₃` certificate from a dense check.** For `G = Xᵀ (Vt 2^(cg + sd - tV) - diag(Dg) X)`
and a passing check of `gramCertMatrix G Ln (pd νd 2^c) (8 pn νd 2^(2cg + sd))
(2 νn pd 2^(2cg + sd + c))`, the form of `C̃ᵀ Ṽ - C̃ᵀ diag(Dg / 2^sd) C̃ - 4 (pn / pd) Λ`
with `C̃ = X / 2^cg`, `Ṽ = Vt / 2^tV`, `Λ = Ln / 2^c` is at least `(νn / νd) |u|²`. -/
theorem gram_cert_of_check {N m : ℕ} (X Vt : Fin N → Fin m → ℤ) (Dg : Fin N → ℤ)
    (Ln : Fin m → ℤ) {cg tV c sd : ℕ} (htV : tV ≤ cg + sd) {G : Fin m → Fin m → ℤ}
    (hG : ∀ i j, G i j = ∑ k, X k i * (Vt k j * 2 ^ (cg + sd - tV) - Dg k * X k j))
    {pn pd νn νd s : ℕ} (hpd : 0 < pd) (hνd : 0 < νd) {L : Fin m → Fin m → ℤ} {d : Fin m → ℕ}
    (h : ldltCheck (gramCertMatrix G Ln (pd * νd * 2 ^ c) (8 * pn * νd * 2 ^ (2 * cg + sd))
      (2 * νn * pd * 2 ^ (2 * cg + sd + c))) L d s 0 = true) (u : Fin m → ℝ) :
    (νn : ℝ) / νd * ∑ j, u j ^ 2 ≤
      ∑ i, ∑ j, (∑ k, ((X k i : ℝ) / 2 ^ cg) * ((Vt k j : ℝ) / 2 ^ tV)) * u i * u j -
        ∑ k, ((Dg k : ℝ) / 2 ^ sd) * (∑ j, ((X k j : ℝ) / 2 ^ cg) * u j) ^ 2 -
        4 * ((pn : ℝ) / pd) * ∑ j, ((Ln j : ℝ) / 2 ^ c) * u j ^ 2 := by
  set D := 2 * cg + sd
  set Q : Fin m → Fin m → ℝ := fun i j ↦ ((G i j : ℝ) + G j i) / (2 * 2 ^ D) -
    if i = j then 4 * ((pn : ℝ) / pd) * ((Ln i : ℝ) / 2 ^ c) + (νn : ℝ) / νd else 0
  have hcpos : (0 : ℝ) < 2 * 2 ^ D * pd * νd * 2 ^ c := by
    have : (0 : ℝ) < pd := by exact_mod_cast hpd
    have : (0 : ℝ) < νd := by exact_mod_cast hνd
    positivity
  have hM : ∀ i j, ((gramCertMatrix G Ln (pd * νd * 2 ^ c) (8 * pn * νd * 2 ^ D)
      (2 * νn * pd * 2 ^ (D + c)) i j : ℤ) : ℝ) = 2 * 2 ^ D * pd * νd * 2 ^ c * Q i j := by
    intro i j
    have hpd' : (pd : ℝ) ≠ 0 := by exact_mod_cast hpd.ne'
    have hνd' : (νd : ℝ) ≠ 0 := by exact_mod_cast hνd.ne'
    simp only [gramCertMatrix, Q]
    split_ifs
    · push_cast; rw [pow_add]; field_simp; ring
    · push_cast; field_simp; ring
  have hQ := quadForm_nonneg_of_ldltCheck_eq h hcpos hM u
  have hsym : ∑ i, ∑ j, Q i j * u i * u j = ∑ i, ∑ j, (G i j : ℝ) / 2 ^ D * u i * u j -
      ∑ j, (4 * ((pn : ℝ) / pd) * ((Ln j : ℝ) / 2 ^ c) + (νn : ℝ) / νd) * u j ^ 2 := by
    have hsplit : ∀ i j, Q i j * u i * u j = ((G i j : ℝ) / (2 * 2 ^ D) * u i * u j +
        (G j i : ℝ) / (2 * 2 ^ D) * u i * u j) -
        (if i = j then 4 * ((pn : ℝ) / pd) * ((Ln i : ℝ) / 2 ^ c) + (νn : ℝ) / νd else 0) *
          u i * u j := fun i j ↦ by simp only [Q]; ring
    simp only [hsplit, sum_sub_distrib, sum_add_distrib, ite_mul, zero_mul, sum_ite_eq,
      mem_univ, ite_true]
    rw [sum_comm (f := fun i j ↦ (G j i : ℝ) / (2 * 2 ^ D) * u i * u j)]
    have e1 : ∑ i, ∑ j, (G i j : ℝ) / (2 * 2 ^ D) * u i * u j +
        ∑ y, ∑ x, (G y x : ℝ) / (2 * 2 ^ D) * u x * u y =
        ∑ i, ∑ j, (G i j : ℝ) / 2 ^ D * u i * u j := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun i _ ↦ ?_
      rw [← sum_add_distrib]
      refine sum_congr rfl fun j _ ↦ ?_
      field_simp; ring
    rw [e1]
    congr 1
    exact sum_congr rfl fun j _ ↦ by ring
  have hG' : ∀ i j, (G i j : ℝ) / 2 ^ D =
      ∑ k, ((X k i : ℝ) / 2 ^ cg) * ((Vt k j : ℝ) / 2 ^ tV) -
        ∑ k, ((Dg k : ℝ) / 2 ^ sd) * ((X k i : ℝ) / 2 ^ cg) * ((X k j : ℝ) / 2 ^ cg) := by
    intro i j
    rw [hG]
    push_cast
    rw [sum_div, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ ↦ ?_
    have h1 : (2 : ℝ) ^ D = 2 ^ (cg + sd - tV) * 2 ^ tV * 2 ^ cg := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    have h2 : (2 : ℝ) ^ D = 2 ^ sd * 2 ^ cg * 2 ^ cg := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [mul_sub, sub_div]
    congr 1
    · rw [h1]; field_simp
    · rw [h2]; field_simp
  have hX : ∑ i, ∑ j, (∑ k, ((Dg k : ℝ) / 2 ^ sd) * ((X k i : ℝ) / 2 ^ cg) *
      ((X k j : ℝ) / 2 ^ cg)) * u i * u j =
      ∑ k, ((Dg k : ℝ) / 2 ^ sd) * (∑ j, ((X k j : ℝ) / 2 ^ cg) * u j) ^ 2 := by
    set g : Fin N → Fin m → Fin m → ℝ := fun k i j ↦
      ((Dg k : ℝ) / 2 ^ sd) * ((X k i : ℝ) / 2 ^ cg) * ((X k j : ℝ) / 2 ^ cg) * u i * u j
    have hl : ∑ i, ∑ j, (∑ k, ((Dg k : ℝ) / 2 ^ sd) * ((X k i : ℝ) / 2 ^ cg) *
        ((X k j : ℝ) / 2 ^ cg)) * u i * u j = ∑ i, ∑ j, ∑ k, g k i j := by
      refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
      rw [sum_mul, sum_mul]
    have hr : ∑ k, ((Dg k : ℝ) / 2 ^ sd) * (∑ j, ((X k j : ℝ) / 2 ^ cg) * u j) ^ 2 =
        ∑ k, ∑ i, ∑ j, g k i j := by
      refine sum_congr rfl fun k _ ↦ ?_
      rw [sq, sum_mul_sum, mul_sum]
      refine sum_congr rfl fun i _ ↦ ?_
      rw [mul_sum]
      exact sum_congr rfl fun j _ ↦ by simp only [g]; ring
    rw [hl, hr]
    calc ∑ i, ∑ j, ∑ k, g k i j = ∑ i, ∑ k, ∑ j, g k i j := sum_congr rfl fun i _ ↦ sum_comm
      _ = ∑ k, ∑ i, ∑ j, g k i j := sum_comm
  simp only [hG', sub_mul, sum_sub_distrib] at hsym
  rw [hX] at hsym
  have hsplit2 : ∑ j, (4 * ((pn : ℝ) / pd) * ((Ln j : ℝ) / 2 ^ c) + (νn : ℝ) / νd) * u j ^ 2 =
      4 * ((pn : ℝ) / pd) * ∑ j, ((Ln j : ℝ) / 2 ^ c) * u j ^ 2 +
        (νn : ℝ) / νd * ∑ j, u j ^ 2 := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun j _ ↦ by ring
  rw [hsplit2] at hsym
  linarith

/-! ### The Gram certificate -/

/-- The integer matrix `diag(gn hd 2^sH Ln² - m hn gd 2^(sH + 2c)) - gd hd 2^(2c) Hn` of the Gram
certificate. -/
def gramFieldMatrix {m : ℕ} (Hn : Fin m → Fin m → ℤ) (Ln : Fin m → ℤ) (sH c hn hd gn gd : ℕ) :
    Fin m → Fin m → ℤ :=
  fun i j ↦ (if i = j then (gn : ℤ) * hd * 2 ^ sH * Ln i ^ 2 - m * hn * gd * 2 ^ (sH + 2 * c)
    else 0) - (gd : ℤ) * hd * 2 ^ (2 * c) * Hn i j

/-- **The Gram certificate from a dense check.** A passing check of `gramFieldMatrix` gives
`yᵀ Ĥ y + m h |y|² ≤ g ∑ λ_j² y_j²` for `Ĥ = Hn / 2^sH`, `h = hn / hd`, `g = gn / gd` and
`λ = Ln / 2^c`. -/
theorem gram_field_of_check {m : ℕ} {Hn : Fin m → Fin m → ℤ} {Ln : Fin m → ℤ}
    {sH c hn hd gn gd s : ℕ} (hhd : 0 < hd) (hgd : 0 < gd) {L : Fin m → Fin m → ℤ}
    {d : Fin m → ℕ} (h : ldltCheck (gramFieldMatrix Hn Ln sH c hn hd gn gd) L d s 0 = true)
    (y : Fin m → ℝ) :
    ∑ i, ∑ j, ((Hn i j : ℝ) / 2 ^ sH) * y i * y j + m * ((hn : ℝ) / hd) * ∑ j, y j ^ 2 ≤
      (gn : ℝ) / gd * ∑ j, ((Ln j : ℝ) / 2 ^ c) ^ 2 * y j ^ 2 := by
  have hhd' : (0 : ℝ) < hd := by exact_mod_cast hhd
  have hgd' : (0 : ℝ) < gd := by exact_mod_cast hgd
  set Q : Fin m → Fin m → ℝ := fun i j ↦
    (if i = j then (gn : ℝ) / gd * ((Ln i : ℝ) / 2 ^ c) ^ 2 - m * ((hn : ℝ) / hd) else 0) -
      (Hn i j : ℝ) / 2 ^ sH
  have hcpos : (0 : ℝ) < gd * hd * 2 ^ (sH + 2 * c) := by positivity
  have hM : ∀ i j, ((gramFieldMatrix Hn Ln sH c hn hd gn gd i j : ℤ) : ℝ) =
      gd * hd * 2 ^ (sH + 2 * c) * Q i j := by
    intro i j
    simp only [gramFieldMatrix, Q]
    split_ifs
    · push_cast; rw [pow_add]; field_simp; ring
    · push_cast; rw [pow_add]; field_simp; ring
  have hQ := quadForm_nonneg_of_ldltCheck_eq h hcpos hM y
  have hsplit : ∑ i, ∑ j, Q i j * y i * y j = ∑ j, ((gn : ℝ) / gd * ((Ln j : ℝ) / 2 ^ c) ^ 2 -
      m * ((hn : ℝ) / hd)) * y j ^ 2 - ∑ i, ∑ j, ((Hn i j : ℝ) / 2 ^ sH) * y i * y j := by
    have e : ∀ i j, Q i j * y i * y j = (if i = j then ((gn : ℝ) / gd * ((Ln i : ℝ) / 2 ^ c) ^ 2 -
        m * ((hn : ℝ) / hd)) * y i * y j else 0) - ((Hn i j : ℝ) / 2 ^ sH) * y i * y j := by
      intro i j; simp only [Q]; split_ifs <;> ring
    simp only [e, sum_sub_distrib, sum_ite_eq, mem_univ, ite_true]
    congr 1
    exact sum_congr rfl fun j _ ↦ by ring
  rw [hsplit] at hQ
  have e2 : ∑ j, ((gn : ℝ) / gd * ((Ln j : ℝ) / 2 ^ c) ^ 2 - m * ((hn : ℝ) / hd)) * y j ^ 2 =
      (gn : ℝ) / gd * ∑ j, ((Ln j : ℝ) / 2 ^ c) ^ 2 * y j ^ 2 -
        m * ((hn : ℝ) / hd) * ∑ j, y j ^ 2 := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ ↦ by ring
  linarith

end CAS.Numerics
