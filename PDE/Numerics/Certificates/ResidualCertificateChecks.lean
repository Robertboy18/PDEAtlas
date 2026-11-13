/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.CaptureCertificateChecks

/-!
# Integer certificates of the residual bound of a capture estimate

The residual bound of the finite-rank capture estimate,
`(1 + θ) ∑_k e_inv k ((R̂ Λ⁻¹ b)_k)² + ν |b|² ≤ ε² ∑_k e_lo k ((C̃ b)_k)²` with
`R̂ = Ṽ - Ê C̃ Λ`, is a quadratic form in `u = Λ⁻¹ b`: its matrix is
`ε² Λ G_E Λ - (1 + θ) H_R - ν Λ²` with the Gram matrices `G_E = C̃ᵀ diag(e_lo) C̃` and
`H_R = R̂ᵀ diag(e_inv) R̂`. With every input on a binary grid, a positive multiple of that matrix
has integer entries (`residualCertMatrix`), and a dense check of it gives the bound
(`residual_cert_of_check`).
-/

@[expose] public section

open Finset

namespace CAS.Numerics

/-- The weighted Gram form: `∑_k w_k (∑_j R_kj u_j)² = uᵀ (Rᵀ diag(w) R) u`. -/
theorem sum_mul_sq_sum_mul_eq_gram {N m : ℕ} (w : Fin N → ℝ) (R : Fin N → Fin m → ℝ)
    (u : Fin m → ℝ) :
    ∑ k, w k * (∑ j, R k j * u j) ^ 2 = ∑ i, ∑ j, (∑ k, w k * R k i * R k j) * u i * u j := by
  have h1 : ∀ k, w k * (∑ j, R k j * u j) ^ 2 =
      ∑ i, ∑ j, w k * (R k i * u i) * (R k j * u j) := fun k ↦ by
    rw [sq, sum_mul_sum, mul_sum]
    exact sum_congr rfl fun i _ ↦ by rw [mul_sum]; exact sum_congr rfl fun j _ ↦ by ring
  calc ∑ k, w k * (∑ j, R k j * u j) ^ 2 = ∑ k, ∑ i, ∑ j, w k * (R k i * u i) * (R k j * u j) :=
        sum_congr rfl fun k _ ↦ h1 k
    _ = ∑ i, ∑ k, ∑ j, w k * (R k i * u i) * (R k j * u j) := sum_comm
    _ = ∑ i, ∑ j, ∑ k, w k * (R k i * u i) * (R k j * u j) := sum_congr rfl fun i _ ↦ sum_comm
    _ = _ := sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by
        rw [sum_mul, sum_mul]; exact sum_congr rfl fun k _ ↦ by ring

/-- The integer residual `R̂ = Ṽ - Ê C̃ Λ` on the grid `2^(-(s_e + c_g + c))`. -/
def residualInt {N m : ℕ} (Vt Ct : Fin N → Fin m → ℤ) (Ln : Fin m → ℤ) (eh : Fin N → ℤ)
    (sh : ℕ) (k : Fin N) (j : Fin m) : ℤ :=
  Vt k j * 2 ^ sh - eh k * Ct k j * Ln j

theorem natAbs_residualInt_le {N m : ℕ} {Vt Ct : Fin N → Fin m → ℤ} {Ln : Fin m → ℤ}
    {eh : Fin N → ℤ} {BV BC BL BH : ℕ} (sh : ℕ) (hV : ∀ k j, (Vt k j).natAbs ≤ BV)
    (hC : ∀ k j, (Ct k j).natAbs ≤ BC) (hL : ∀ j, (Ln j).natAbs ≤ BL)
    (hH : ∀ k, (eh k).natAbs ≤ BH) (k : Fin N) (j : Fin m) :
    (residualInt Vt Ct Ln eh sh k j).natAbs ≤ BV * 2 ^ sh + BH * BC * BL := by
  unfold residualInt
  refine (Int.natAbs_sub_le _ _).trans (Nat.add_le_add ?_ ?_)
  · rw [Int.natAbs_mul, Int.natAbs_pow]
    exact Nat.mul_le_mul (hV k j) le_rfl
  · rw [Int.natAbs_mul, Int.natAbs_mul]
    exact Nat.mul_le_mul (Nat.mul_le_mul (hH k) (hC k j)) (hL j)

/-- The Gram matrix of the integer residual from three Gram matrices of the base columns:
`2^(2s) G₁ - 2^s (G₂ Λ + Λ G₂ᵀ) + Λ G₃ Λ`. -/
def residualGram {m : ℕ} (G1 G2 G3 : Fin m → Fin m → ℤ) (Ln : Fin m → ℤ) (sh : ℕ) :
    Fin m → Fin m → ℤ :=
  fun i j ↦ 2 ^ (2 * sh) * G1 i j - 2 ^ sh * (Ln j * G2 i j + Ln i * G2 j i) +
    Ln i * Ln j * G3 i j

/-- With `G₁ = Vtᵀ E_i Vt`, `G₂ = Vtᵀ E_i E_h Ct` and `G₃ = Ctᵀ E_i E_h² Ct`, `residualGram` is
the weighted Gram matrix of the integer residual `Vt 2^s - E_h Ct Λ`. -/
theorem residualGram_eq {N m : ℕ} {Vt Ct : Fin N → Fin m → ℤ} {Ln : Fin m → ℤ}
    {eh ei : Fin N → ℤ} (sh : ℕ) {G1 G2 G3 : Fin m → Fin m → ℤ}
    (hG1 : ∀ i j, G1 i j = ∑ k, ei k * Vt k i * Vt k j)
    (hG2 : ∀ i j, G2 i j = ∑ k, ei k * eh k * Vt k i * Ct k j)
    (hG3 : ∀ i j, G3 i j = ∑ k, ei k * eh k ^ 2 * Ct k i * Ct k j) (i j : Fin m) :
    residualGram G1 G2 G3 Ln sh i j =
      ∑ k, ei k * residualInt Vt Ct Ln eh sh k i * residualInt Vt Ct Ln eh sh k j := by
  simp only [residualGram, hG1, hG2, hG3, residualInt, mul_sum, ← sum_add_distrib,
    ← sum_sub_distrib]
  refine sum_congr rfl fun k _ ↦ ?_
  ring

/-- The integer certificate matrix `c (ε² Λ G_E Λ - (1 + θ) H_R - ν Λ²)`. -/
def residualCertMatrix {m : ℕ} (GE HR : Fin m → Fin m → ℤ) (Ln : Fin m → ℤ)
    (a b d : ℕ) : Fin m → Fin m → ℤ :=
  fun i j ↦ (a : ℤ) * (Ln i * GE i j * Ln j) - b * HR i j -
    if i = j then (d : ℤ) * Ln i ^ 2 else 0

/-- **The residual bound from an integer check.** Inputs on binary grids: `Ṽ = Vt / 2^(t_V)`,
`C̃ = Ct / 2^(c_g)`, `λ = Ln / 2^c`, `ê = eh / 2^(s_e)`, `e_lo = el / 2^(s_l)`,
`e_inv = ei / 2^(s_i)`, and `ε = εn / εd`, `θ = θn / θd`, `ν = νn / νd`. With
`R = s_e + c_g + c` and the Gram matrices `GE = Σ el Ct Ct`, `HR = Σ ei R̂ R̂` of the integer
residual `R̂ = Vt 2^(R - t_V) - eh Ct Ln`, a passing check of
`εn² θd νd 2^(s_i + 2R) Λ GE Λ - εd² (θd + θn) νd 2^(2c + s_l + 2c_g) HR -
εd² θd νn 2^(s_l + 2c_g + s_i + 2R) Λ²` gives the residual bound. -/
theorem residual_cert_of_check {N m : ℕ} (Vt Ct : Fin N → Fin m → ℤ) (Ln : Fin m → ℤ)
    (eh el ei : Fin N → ℤ) {tV cg c se sl si : ℕ} (htV : tV ≤ se + cg + c)
    {εn εd θn θd νn νd s : ℕ} (hεd : 0 < εd) (hθd : 0 < θd) (hνd : 0 < νd)
    (hLn : ∀ j, 0 < Ln j) {GE HR : Fin m → Fin m → ℤ}
    (hGE : ∀ i j, GE i j = ∑ k, el k * Ct k i * Ct k j)
    (hHR : ∀ i j, HR i j = ∑ k, ei k * residualInt Vt Ct Ln eh (se + cg + c - tV) k i *
      residualInt Vt Ct Ln eh (se + cg + c - tV) k j)
    {L : Fin m → Fin m → ℤ} {d : Fin m → ℕ}
    (h : ldltCheck (residualCertMatrix GE HR Ln
      (εn ^ 2 * θd * νd * 2 ^ (si + 2 * (se + cg + c)))
      (εd ^ 2 * (θd + θn) * νd * 2 ^ (2 * c + sl + 2 * cg))
      (εd ^ 2 * θd * νn * 2 ^ (sl + 2 * cg + si + 2 * (se + cg + c)))) L d s 0 = true)
    (b : Fin m → ℝ) :
    (1 + (θn : ℝ) / θd) * ∑ k, ((ei k : ℝ) / 2 ^ si) *
        (∑ j, ((Vt k j : ℝ) / 2 ^ tV - ((eh k : ℝ) / 2 ^ se) * ((Ct k j : ℝ) / 2 ^ cg) *
          ((Ln j : ℝ) / 2 ^ c)) * (b j / ((Ln j : ℝ) / 2 ^ c))) ^ 2 +
        (νn : ℝ) / νd * ∑ j, b j ^ 2 ≤
      ((εn : ℝ) / εd) ^ 2 * ∑ k, ((el k : ℝ) / 2 ^ sl) *
        (∑ j, ((Ct k j : ℝ) / 2 ^ cg) * b j) ^ 2 := by
  set R := se + cg + c
  set μ : Fin m → ℝ := fun j ↦ (Ln j : ℝ) / 2 ^ c
  have hμ : ∀ j, 0 < μ j := fun j ↦ div_pos (by exact_mod_cast hLn j) (by positivity)
  set u : Fin m → ℝ := fun j ↦ b j / μ j
  have hb : ∀ j, b j = μ j * u j := fun j ↦ by simp only [u]; field_simp [(hμ j).ne']
  set Q : Fin m → Fin m → ℝ := fun i j ↦
    ((εn : ℝ) / εd) ^ 2 * (μ i * μ j * ∑ k, ((el k : ℝ) / 2 ^ sl) * ((Ct k i : ℝ) / 2 ^ cg) *
      ((Ct k j : ℝ) / 2 ^ cg)) -
    (1 + (θn : ℝ) / θd) * ∑ k, ((ei k : ℝ) / 2 ^ si) *
      ((residualInt Vt Ct Ln eh (R - tV) k i : ℝ) / 2 ^ R) *
      ((residualInt Vt Ct Ln eh (R - tV) k j : ℝ) / 2 ^ R) -
    if i = j then (νn : ℝ) / νd * μ i ^ 2 else 0
  have hcpos : (0 : ℝ) < (εd : ℝ) ^ 2 * θd * νd * 2 ^ (2 * c + sl + 2 * cg + si + 2 * R) := by
    positivity
  have hGEr : ∀ i j, ∑ k, ((el k : ℝ) / 2 ^ sl) * ((Ct k i : ℝ) / 2 ^ cg) * ((Ct k j : ℝ) / 2 ^ cg)
      = (GE i j : ℝ) / 2 ^ (sl + 2 * cg) := fun i j ↦ by
    rw [hGE]; push_cast; rw [sum_div]
    refine sum_congr rfl fun k _ ↦ ?_
    simp only [two_mul, pow_add]; field_simp
  have hHRr : ∀ i j, ∑ k, ((ei k : ℝ) / 2 ^ si) *
      ((residualInt Vt Ct Ln eh (R - tV) k i : ℝ) / 2 ^ R) *
      ((residualInt Vt Ct Ln eh (R - tV) k j : ℝ) / 2 ^ R) = (HR i j : ℝ) / 2 ^ (si + 2 * R) :=
    fun i j ↦ by
      rw [hHR]; push_cast; rw [sum_div]
      refine sum_congr rfl fun k _ ↦ ?_
      simp only [two_mul, pow_add]; field_simp
  have hM : ∀ i j, ((residualCertMatrix GE HR Ln
      (εn ^ 2 * θd * νd * 2 ^ (si + 2 * R)) (εd ^ 2 * (θd + θn) * νd * 2 ^ (2 * c + sl + 2 * cg))
      (εd ^ 2 * θd * νn * 2 ^ (sl + 2 * cg + si + 2 * R)) i j : ℤ) : ℝ) =
      (εd : ℝ) ^ 2 * θd * νd * 2 ^ (2 * c + sl + 2 * cg + si + 2 * R) * Q i j := by
    intro i j
    simp only [residualCertMatrix, Q, μ, hGEr, hHRr]
    push_cast
    have hεd' : (εd : ℝ) ≠ 0 := by positivity
    have hθd' : (θd : ℝ) ≠ 0 := by positivity
    have hνd' : (νd : ℝ) ≠ 0 := by positivity
    simp only [two_mul, pow_add]
    split_ifs
    · field_simp
    · field_simp
      ring
  have hQ := quadForm_nonneg_of_ldltCheck_eq h hcpos hM u
  have hR : ∀ k j, ((Vt k j : ℝ) / 2 ^ tV - ((eh k : ℝ) / 2 ^ se) * ((Ct k j : ℝ) / 2 ^ cg) *
      ((Ln j : ℝ) / 2 ^ c)) = (residualInt Vt Ct Ln eh (R - tV) k j : ℝ) / 2 ^ R := by
    intro k j
    simp only [residualInt]
    push_cast
    have h1 : (2 : ℝ) ^ R = 2 ^ (R - tV) * 2 ^ tV := by rw [← pow_add, Nat.sub_add_cancel htV]
    have h2 : (2 : ℝ) ^ R = 2 ^ se * 2 ^ cg * 2 ^ c := by simp only [R, pow_add]
    rw [sub_div]
    congr 1
    · rw [h1]; field_simp
    · rw [h2]; field_simp
  have e1 : ∑ k, ((ei k : ℝ) / 2 ^ si) *
      (∑ j, ((Vt k j : ℝ) / 2 ^ tV - ((eh k : ℝ) / 2 ^ se) * ((Ct k j : ℝ) / 2 ^ cg) *
        ((Ln j : ℝ) / 2 ^ c)) * (b j / ((Ln j : ℝ) / 2 ^ c))) ^ 2 =
      ∑ i, ∑ j, (∑ k, ((ei k : ℝ) / 2 ^ si) *
        ((residualInt Vt Ct Ln eh (R - tV) k i : ℝ) / 2 ^ R) *
        ((residualInt Vt Ct Ln eh (R - tV) k j : ℝ) / 2 ^ R)) * u i * u j := by
    simp only [hR]
    exact sum_mul_sq_sum_mul_eq_gram _ _ u
  have e2 : ∑ k, ((el k : ℝ) / 2 ^ sl) * (∑ j, ((Ct k j : ℝ) / 2 ^ cg) * b j) ^ 2 =
      ∑ i, ∑ j, (∑ k, ((el k : ℝ) / 2 ^ sl) * ((Ct k i : ℝ) / 2 ^ cg) *
        ((Ct k j : ℝ) / 2 ^ cg)) * (μ i * u i) * (μ j * u j) := by
    simp only [hb]
    exact sum_mul_sq_sum_mul_eq_gram _ _ (fun j ↦ μ j * u j)
  have e3 : ∑ j, b j ^ 2 = ∑ j, μ j ^ 2 * u j ^ 2 :=
    sum_congr rfl fun j _ ↦ by rw [hb]; ring
  have e4 : ∑ i, ∑ j, Q i j * u i * u j =
      ((εn : ℝ) / εd) ^ 2 * ∑ i, ∑ j, (∑ k, ((el k : ℝ) / 2 ^ sl) * ((Ct k i : ℝ) / 2 ^ cg) *
        ((Ct k j : ℝ) / 2 ^ cg)) * (μ i * u i) * (μ j * u j) -
      (1 + (θn : ℝ) / θd) * ∑ i, ∑ j, (∑ k, ((ei k : ℝ) / 2 ^ si) *
        ((residualInt Vt Ct Ln eh (R - tV) k i : ℝ) / 2 ^ R) *
        ((residualInt Vt Ct Ln eh (R - tV) k j : ℝ) / 2 ^ R)) * u i * u j -
      (νn : ℝ) / νd * ∑ j, μ j ^ 2 * u j ^ 2 := by
    have hsm : ∀ (a : ℝ) (X : Fin m → Fin m → ℝ),
        ∑ i, ∑ j, a * X i j * u i * u j = a * ∑ i, ∑ j, X i j * u i * u j := fun a X ↦ by
      rw [mul_sum]
      exact sum_congr rfl fun i _ ↦ by rw [mul_sum]; exact sum_congr rfl fun j _ ↦ by ring
    have hite : ∑ i, ∑ j, (if i = j then (νn : ℝ) / νd * μ i ^ 2 else 0) * u i * u j =
        (νn : ℝ) / νd * ∑ j, μ j ^ 2 * u j ^ 2 := by
      simp only [ite_mul, zero_mul, sum_ite_eq, mem_univ, ite_true, mul_sum]
      exact sum_congr rfl fun j _ ↦ by ring
    have hE : ∑ i, ∑ j, (μ i * μ j * ∑ k, ((el k : ℝ) / 2 ^ sl) * ((Ct k i : ℝ) / 2 ^ cg) *
        ((Ct k j : ℝ) / 2 ^ cg)) * u i * u j =
        ∑ i, ∑ j, (∑ k, ((el k : ℝ) / 2 ^ sl) * ((Ct k i : ℝ) / 2 ^ cg) *
          ((Ct k j : ℝ) / 2 ^ cg)) * (μ i * u i) * (μ j * u j) :=
      sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
    have hsplit : ∑ i, ∑ j, Q i j * u i * u j =
        ∑ i, ∑ j, ((εn : ℝ) / εd) ^ 2 * (μ i * μ j * ∑ k, ((el k : ℝ) / 2 ^ sl) *
          ((Ct k i : ℝ) / 2 ^ cg) * ((Ct k j : ℝ) / 2 ^ cg)) * u i * u j -
        ∑ i, ∑ j, (1 + (θn : ℝ) / θd) * (∑ k, ((ei k : ℝ) / 2 ^ si) *
          ((residualInt Vt Ct Ln eh (R - tV) k i : ℝ) / 2 ^ R) *
          ((residualInt Vt Ct Ln eh (R - tV) k j : ℝ) / 2 ^ R)) * u i * u j -
        ∑ i, ∑ j, (if i = j then (νn : ℝ) / νd * μ i ^ 2 else 0) * u i * u j := by
      rw [← sum_sub_distrib, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ ↦ ?_
      rw [← sum_sub_distrib, ← sum_sub_distrib]
      exact sum_congr rfl fun j _ ↦ by simp only [Q]; ring
    rw [hsplit, hsm, hsm, hite, hE]
  rw [e1, e2, e3]
  linarith

end CAS.Numerics
