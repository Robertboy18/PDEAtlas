/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2
public import CAS.Numerics.SignedPolynomial

/-!
# Exact products of two-variable trigonometric tables by one packed multiplication

An integer table `c : TrigPoly2 M L ℤ` of degrees `(M, L)` stands for the rational table
`PDE.Analysis.TrigPoly2.ofInt c d` with coefficients `c / d`. It is encoded by two
polynomials in two variables with integer coefficients, `encRe` and `encIm`, whose values at
`z = e^{iβ}`, `w = e^{iθ}` satisfy
`encRe + i encIm = 4 z^M w^L ∑ c i j k l · m_i (k β) · m_j (l θ)`
(`bivariateEval_encRe_add_I_mul`). The mode `cos (kx)` becomes `X^(M+k) + X^(M-k)` and
`sin (kx)` becomes `X^(M+k) - X^(M-k)` (`modePoly`), so the product of two tables is the product
of their exponential encodings: the identities `encRe r = encRe p · encRe q - encIm p · encIm q`
and `encIm r = encRe p · encIm q + encIm p · encRe q` make the value of `r` four times the
product of the values (`trigTableValue_eq_of_enc`).

Each identity is checked as one integer identity. The substitution of the outer variable by
`X ^ S` (`kroneckerSubstitution`) is injective on polynomials whose inner degrees stay below `S`
(`kroneckerSubstitution_injective`), and the substituted encodings are stored as balanced
coefficient trees (`reTree`, `imTree`, entry `n` at `(n / S, n % S)`, computed with at most four
table lookups by `encReCoeff` and `encImCoeff`). One packed identity `a b + σ c d = e` at base
`2 ^ bits`, with the margin `|a| |b| + |c| |d| + |e| < 2 ^ bits` on the absolute coefficient
masses, then identifies the polynomials (`signedPolynomial_mul_add_mul_eq_of_packed`), as in
`signedProductCheck_sound`. Packing uses `packSignedBinary`, whose strides are shifts.

`trigProductCheck S bits dp dq dr cp cq cr` combines the stride and depth conditions, the two
packed identities and the vanishing of the cells of `sin (0 · β)` and `sin (0 · θ)` of `cr`
(`zeroModesCheck`), and `TrigPoly2.eval_ofInt_eq_mul_of_trigProductCheck` turns a successful
check into `(ofInt cr (4uv)).eval = (ofInt cp u).eval * (ofInt cq v).eval` for all rational
`u`, `v`. The stride must exceed `2 (Lp + Lq)` and the tree depths must cover `S · 2M + 2L`.
The cells of `sin 0` do not enter the encoding, so the packed identities certify values; the
zero-mode condition makes the certified table the one without these cells
(`TrigPoly2.zeroModesVanish_ofInt_of_trigProductCheck`).

A table with a single nonzero block `(i, j)` (`blockInt`, `TrigPoly2.ofBlock`) has a real or an
imaginary encoding, and the product of the blocks `(i, j)` and `(i', j')` is the block
`(i + i', j + j')` up to the sign `blockProductSign` (`blockWeight_mul_blockWeight`).
`trigBlockProductCheck` then needs one packed product `signedProductCheck` of three trees, and
`TrigPoly2.eval_ofBlock_eq_mul_of_trigBlockProductCheck` gives the product of values. Fields of
definite parity in each variable, their derivatives, quotients and products are single blocks.

These checks are a tool for small tables in the default (native) profile. Their cost is linear
in the tree sizes, about a minute for a single-block product of two tables of degrees
`(604, 304)` and about three for the general check, and the kernel profile pays about a
millisecond per tree entry. Certificates on tables of that size work through values at the
quadrature nodes instead: separable evaluation of each factor at the nodes, pointwise products,
and the errors of `TrigPoly2.abs_eval_sub_sum_le` and `TrigPoly2.l1Norm_mul_le`.
-/

@[expose] public noncomputable section

namespace CAS.Numerics

open _root_.Polynomial Finset PDE.Analysis

/-- Kronecker substitution: the outer variable of a polynomial in two variables becomes
`X ^ S`, the inner one `X`. -/
def kroneckerSubstitution (S : ℕ) : Polynomial (Polynomial ℤ) →+* Polynomial ℤ :=
  Polynomial.evalRingHom (X ^ S)

/-- Every coefficient in the outer variable has degree at most `d` in the inner one. -/
def InnerDegreeLE (d : ℕ) (F : Polynomial (Polynomial ℤ)) : Prop :=
  ∀ k, (F.coeff k).natDegree ≤ d

theorem InnerDegreeLE.add {d : ℕ} {F G : Polynomial (Polynomial ℤ)} (hF : InnerDegreeLE d F)
    (hG : InnerDegreeLE d G) : InnerDegreeLE d (F + G) := fun k ↦ by
  rw [coeff_add]
  exact (natDegree_add_le _ _).trans (max_le (hF k) (hG k))

theorem InnerDegreeLE.neg {d : ℕ} {F : Polynomial (Polynomial ℤ)} (hF : InnerDegreeLE d F) :
    InnerDegreeLE d (-F) := fun k ↦ by
  rw [coeff_neg, natDegree_neg]
  exact hF k

theorem InnerDegreeLE.sub {d : ℕ} {F G : Polynomial (Polynomial ℤ)} (hF : InnerDegreeLE d F)
    (hG : InnerDegreeLE d G) : InnerDegreeLE d (F - G) := by
  rw [sub_eq_add_neg]
  exact hF.add hG.neg

theorem InnerDegreeLE.mul {d e : ℕ} {F G : Polynomial (Polynomial ℤ)}
    (hF : InnerDegreeLE d F) (hG : InnerDegreeLE e G) : InnerDegreeLE (d + e) (F * G) :=
  fun k ↦ by
    rw [coeff_mul]
    exact natDegree_sum_le_of_forall_le _ _ fun x _ ↦
      (natDegree_mul_le).trans (add_le_add (hF x.1) (hG x.2))

theorem InnerDegreeLE.mono {d e : ℕ} {F : Polynomial (Polynomial ℤ)} (hF : InnerDegreeLE d F)
    (hde : d ≤ e) : InnerDegreeLE e F := fun k ↦ (hF k).trans hde

/-- The coefficients of a Kronecker substitution are the coefficients of the two-variable
polynomial when the inner degrees stay below the stride. -/
theorem coeff_kroneckerSubstitution {S d : ℕ} {F : Polynomial (Polynomial ℤ)}
    (hF : InnerDegreeLE d F) (hdS : d < S) (k : ℕ) {l : ℕ} (hl : l < S) :
    (kroneckerSubstitution S F).coeff (S * k + l) = (F.coeff k).coeff l := by
  rw [kroneckerSubstitution, coe_evalRingHom, eval_eq_sum, Polynomial.sum, finsetSum_coeff]
  simp only [← pow_mul, coeff_mul_X_pow']
  rw [sum_eq_single k]
  · rw [ite_eq_left (by nlinarith), show S * k + l - S * k = l by omega]
  · intro n _ hn
    split_ifs with h
    · rcases lt_or_gt_of_ne hn with hlt | hgt
      · refine coeff_eq_zero_of_natDegree_lt ((hF n).trans_lt ?_)
        have : S * n + S ≤ S * k := by nlinarith
        omega
      · have : S * k + S ≤ S * n := by nlinarith
        omega
    · rfl
  · intro hk
    rw [notMem_support_iff.mp hk, coeff_zero]
    simp

/-- Past the degrees, the Kronecker substitution vanishes. -/
theorem coeff_kroneckerSubstitution_eq_zero {S d D : ℕ} {F : Polynomial (Polynomial ℤ)}
    (hF : InnerDegreeLE d F) (hD : ∀ k, D < k → F.coeff k = 0) (hdS : d < S) {n : ℕ}
    (hn : S * D + d < n) : (kroneckerSubstitution S F).coeff n = 0 := by
  have hS : 0 < S := by omega
  rw [← Nat.div_add_mod n S, coeff_kroneckerSubstitution hF hdS _ (Nat.mod_lt _ hS)]
  by_cases hk : D < n / S
  · rw [hD _ hk, coeff_zero]
  · refine coeff_eq_zero_of_natDegree_lt ((hF _).trans_lt ?_)
    have h₁ : S * (n / S) ≤ S * D := Nat.mul_le_mul_left _ (by omega)
    have h₂ := Nat.div_add_mod n S
    omega

/-- Kronecker substitution is injective on polynomials with inner degrees below the stride. -/
theorem kroneckerSubstitution_injective {S d : ℕ} {F G : Polynomial (Polynomial ℤ)}
    (hF : InnerDegreeLE d F) (hG : InnerDegreeLE d G) (hdS : d < S)
    (h : kroneckerSubstitution S F = kroneckerSubstitution S G) : F = G := by
  ext k l
  by_cases hl : l < S
  · rw [← coeff_kroneckerSubstitution hF hdS k hl, ← coeff_kroneckerSubstitution hG hdS k hl, h]
  · rw [coeff_eq_zero_of_natDegree_lt ((hF k).trans_lt (by omega)),
      coeff_eq_zero_of_natDegree_lt ((hG k).trans_lt (by omega))]

/-! ### Encodings of trigonometric tables -/

/-- The sign `1` for the cosine and `-1` for the sine. -/
def trigModeSign (i : Fin 2) : ℤ :=
  if i = 0 then 1 else -1

/-- The encoding of `cos (kx)` or `sin (kx)` centred at `X ^ M`: `X^(M+k) + X^(M-k)` and
`X^(M+k) - X^(M-k)`; at `X = e^{ix}` these are `2 e^{iMx} cos (kx)` and
`2i e^{iMx} sin (kx)`. -/
def modePoly (M : ℕ) (i : Fin 2) (k : ℕ) : Polynomial ℤ :=
  X ^ (M + k) + C (trigModeSign i) * X ^ (M - k)

theorem coeff_modePoly (M : ℕ) (i : Fin 2) (k a : ℕ) :
    (modePoly M i k).coeff a =
      (if a = M + k then 1 else 0) + trigModeSign i * (if a = M - k then 1 else 0) := by
  simp [modePoly, coeff_X_pow]

theorem natDegree_modePoly_le (M : ℕ) (i : Fin 2) (k : ℕ) :
    (modePoly M i k).natDegree ≤ M + k :=
  (natDegree_add_le _ _).trans (max_le (natDegree_X_pow_le _)
    ((natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le _).trans (by omega))))

/-- `∑_{k ≤ M} f k · [X^a] (modePoly M i k)`, computed with two lookups. -/
def modeCollapse (M : ℕ) (i : Fin 2) (a : ℕ) (f : ℕ → ℤ) : ℤ :=
  (if M ≤ a ∧ a ≤ 2 * M then f (a - M) else 0) + trigModeSign i * (if a ≤ M then f (M - a) else 0)

theorem sum_mul_coeff_modePoly (M : ℕ) (i : Fin 2) (a : ℕ) (f : ℕ → ℤ) :
    ∑ k ∈ range (M + 1), f k * (modePoly M i k).coeff a = modeCollapse M i a f := by
  simp only [coeff_modePoly, mul_add, sum_add_distrib, modeCollapse]
  congr 1
  · by_cases h : M ≤ a ∧ a ≤ 2 * M
    · rw [sum_eq_single (a - M), ite_eq_left (by omega), ite_eq_left h, mul_one]
      · intro k _ hk
        rw [ite_eq_right_iff.mpr fun h' ↦ absurd (by omega) hk, mul_zero]
      · intro hk
        exact absurd (mem_range.mpr (by omega)) hk
    · rw [ite_eq_right_iff.mpr fun h' ↦ absurd h' h]
      refine sum_eq_zero fun k hk ↦ ?_
      have := mem_range.mp hk
      rw [ite_eq_right_iff.mpr fun h' ↦ absurd ⟨by omega, by omega⟩ h, mul_zero]
  · by_cases h : a ≤ M
    · rw [sum_eq_single (M - a), ite_eq_left (by omega), ite_eq_left h]
      · ring
      · intro k hk hk'
        have := mem_range.mp hk
        rw [ite_eq_right_iff.mpr fun h' ↦ absurd (by omega) hk']
        ring
      · intro hk
        exact absurd (mem_range.mpr (by omega)) hk
    · rw [ite_eq_right_iff.mpr fun h' ↦ absurd h' h, mul_zero]
      refine sum_eq_zero fun k hk ↦ ?_
      rw [ite_eq_right_iff.mpr fun h' ↦ absurd (by omega) h]
      ring

/-- The block `(i, j)` of a coefficient table `F` (natural frequencies, `k ≤ M`, `l ≤ L`) as
a polynomial in two variables: `∑ F i j k l · modePoly M i k (outer) · modePoly L j l (inner)`. -/
def encPart (M L : ℕ) (F : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) (i j : Fin 2) :
    Polynomial (Polynomial ℤ) :=
  ∑ k ∈ range (M + 1), ∑ l ∈ range (L + 1),
    C (C (F i j k l)) * (modePoly M i k).map C * C (modePoly L j l)

/-- The coefficients of a block, computed with at most four lookups. -/
def encPartCoeff (M L : ℕ) (F : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) (i j : Fin 2) (a b : ℕ) : ℤ :=
  modeCollapse M i a fun k ↦ modeCollapse L j b fun l ↦ F i j k l

theorem coeff_encPart (M L : ℕ) (F : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) (i j : Fin 2) (a : ℕ) :
    (encPart M L F i j).coeff a = ∑ k ∈ range (M + 1), ∑ l ∈ range (L + 1),
      C (F i j k l * (modePoly M i k).coeff a) * modePoly L j l := by
  simp only [encPart, finsetSum_coeff, coeff_mul_C, coeff_C_mul, coeff_map, ← C_mul]

theorem coeff_coeff_encPart (M L : ℕ) (F : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) (i j : Fin 2) (a b : ℕ) :
    ((encPart M L F i j).coeff a).coeff b = encPartCoeff M L F i j a b := by
  rw [coeff_encPart, encPartCoeff, ← sum_mul_coeff_modePoly]
  simp only [finsetSum_coeff, coeff_C_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [← sum_mul_coeff_modePoly, sum_mul]
  exact sum_congr rfl fun l _ ↦ by ring

theorem innerDegreeLE_encPart (M L : ℕ) (F : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) (i j : Fin 2) :
    InnerDegreeLE (2 * L) (encPart M L F i j) := fun a ↦ by
  rw [coeff_encPart]
  refine natDegree_sum_le_of_forall_le _ _ fun k _ ↦ natDegree_sum_le_of_forall_le _ _
    fun l hl ↦ (natDegree_C_mul_le _ _).trans ((natDegree_modePoly_le L j l).trans ?_)
  have := mem_range.mp hl
  omega

theorem encPartCoeff_eq_zero (M L : ℕ) (F : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) (i j : Fin 2) {a : ℕ}
    (ha : 2 * M < a) (b : ℕ) : encPartCoeff M L F i j a b = 0 := by
  simp only [encPartCoeff, modeCollapse]
  rw [ite_eq_right_iff.mpr fun h ↦ absurd h.2 (by omega),
    ite_eq_right_iff.mpr fun h ↦ absurd h (by omega)]
  ring

theorem coeff_encPart_eq_zero (M L : ℕ) (F : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) (i j : Fin 2) {a : ℕ}
    (ha : 2 * M < a) : (encPart M L F i j).coeff a = 0 := by
  ext b
  rw [coeff_coeff_encPart, encPartCoeff_eq_zero M L F i j ha, coeff_zero]

/-- The real part of the exponential encoding: blocks `(0, 0)` minus `(1, 1)`. -/
def encRe (M L : ℕ) (F : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) : Polynomial (Polynomial ℤ) :=
  encPart M L F 0 0 - encPart M L F 1 1

/-- The imaginary part of the exponential encoding: minus the blocks `(0, 1)` and `(1, 0)`. -/
def encIm (M L : ℕ) (F : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) : Polynomial (Polynomial ℤ) :=
  -(encPart M L F 0 1 + encPart M L F 1 0)

/-- The coefficients of `encRe`. -/
def encReCoeff (M L : ℕ) (F : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) (a b : ℕ) : ℤ :=
  encPartCoeff M L F 0 0 a b - encPartCoeff M L F 1 1 a b

/-- The coefficients of `encIm`. -/
def encImCoeff (M L : ℕ) (F : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) (a b : ℕ) : ℤ :=
  -(encPartCoeff M L F 0 1 a b + encPartCoeff M L F 1 0 a b)

theorem coeff_coeff_encRe (M L : ℕ) (F : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) (a b : ℕ) :
    ((encRe M L F).coeff a).coeff b = encReCoeff M L F a b := by
  simp [encRe, encReCoeff, coeff_coeff_encPart]

theorem coeff_coeff_encIm (M L : ℕ) (F : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) (a b : ℕ) :
    ((encIm M L F).coeff a).coeff b = encImCoeff M L F a b := by
  simp [encIm, encImCoeff, coeff_coeff_encPart]

theorem innerDegreeLE_encRe (M L : ℕ) (F : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) :
    InnerDegreeLE (2 * L) (encRe M L F) :=
  (innerDegreeLE_encPart M L F 0 0).sub (innerDegreeLE_encPart M L F 1 1)

theorem innerDegreeLE_encIm (M L : ℕ) (F : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) :
    InnerDegreeLE (2 * L) (encIm M L F) :=
  ((innerDegreeLE_encPart M L F 0 1).add (innerDegreeLE_encPart M L F 1 0)).neg

theorem coeff_encRe_eq_zero (M L : ℕ) (F : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) {a : ℕ}
    (ha : 2 * M < a) : (encRe M L F).coeff a = 0 := by
  simp [encRe, coeff_encPart_eq_zero M L F _ _ ha]

theorem coeff_encIm_eq_zero (M L : ℕ) (F : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) {a : ℕ}
    (ha : 2 * M < a) : (encIm M L F).coeff a = 0 := by
  simp [encIm, coeff_encPart_eq_zero M L F _ _ ha]

/-! ### Evaluation on the unit torus -/

/-- Evaluation of a polynomial in two variables at `(z, w)`, the outer variable at `z`. -/
def bivariateEval (z w : ℂ) : Polynomial (Polynomial ℤ) →+* ℂ :=
  eval₂RingHom (eval₂RingHom (Int.castRingHom ℂ) w) z

theorem bivariateEval_C_C (z w : ℂ) (n : ℤ) : bivariateEval z w (C (C n)) = n := by
  simp [bivariateEval]

theorem bivariateEval_map_C (z w : ℂ) (P : Polynomial ℤ) :
    bivariateEval z w (P.map C) = P.eval₂ (Int.castRingHom ℂ) z := by
  rw [bivariateEval, coe_eval₂RingHom, eval₂_map]
  congr 1
  ext n
  simp

theorem bivariateEval_C (z w : ℂ) (P : Polynomial ℤ) :
    bivariateEval z w (C P) = P.eval₂ (Int.castRingHom ℂ) w := by
  simp [bivariateEval]

/-- The complex value of an encoded mode: `2 cos x` for the cosine, `2i sin x` for the sine. -/
def modeValue (i : Fin 2) (x : ℝ) : ℂ :=
  if i = 0 then 2 * (Real.cos x : ℂ) else 2 * Complex.I * (Real.sin x : ℂ)

/-- At `z = e^{ix}` the mode encoding is `z ^ M` times the mode value. -/
theorem eval₂_modePoly (M : ℕ) (i : Fin 2) {k : ℕ} (hk : k ≤ M) (x : ℝ) :
    (modePoly M i k).eval₂ (Int.castRingHom ℂ) (Complex.exp (x * Complex.I)) =
      Complex.exp (x * Complex.I) ^ M * modeValue i (k * x) := by
  set z := Complex.exp (x * Complex.I)
  have hzk : z ^ k = Complex.exp ((k * x : ℝ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hinv : z ^ (M - k) = z ^ M * Complex.exp (-((k * x : ℝ) * Complex.I)) := by
    have h₁ : z ^ (M - k) * z ^ k = z ^ M := pow_sub_mul_pow z hk
    rw [hzk] at h₁
    rw [← h₁, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  have hc : Complex.exp ((k * x : ℝ) * Complex.I) = Real.cos (k * x) + Real.sin (k * x) *
      Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hs : Complex.exp (-((k * x : ℝ) * Complex.I)) = Real.cos (k * x) - Real.sin (k * x) *
      Complex.I := by
    rw [← neg_mul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
    ring
  simp only [modePoly, eval₂_add, eval₂_mul, eval₂_C, eval₂_X_pow, pow_add, hzk, hinv, hc, hs]
  fin_cases i <;> simp [trigModeSign, modeValue] <;> ring

/-- The weights that combine the four blocks into `encRe + i encIm`. -/
def blockWeight (i j : Fin 2) : ℂ :=
  if i = j then (if i = 0 then 1 else -1) else -Complex.I

theorem modeValue_zero (x : ℝ) : modeValue 0 x = 2 * (Real.cos x : ℂ) := rfl

theorem modeValue_one (x : ℝ) : modeValue 1 x = 2 * Complex.I * (Real.sin x : ℂ) := rfl

theorem blockWeight_mul_modeValue (i j : Fin 2) (x y : ℝ) :
    blockWeight i j * (modeValue i x * modeValue j y) =
      4 * ((trigMode i x * trigMode j y : ℝ) : ℂ) := by
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, modeValue_zero, modeValue_one,
      trigMode_zero, trigMode_one, Complex.ofReal_mul]
  · rw [show blockWeight 0 0 = 1 from rfl]
    ring
  · rw [show blockWeight 0 1 = -Complex.I from rfl]
    linear_combination (-4 * (Real.cos x : ℂ) * (Real.sin y : ℂ)) * Complex.I_sq
  · rw [show blockWeight 1 0 = -Complex.I from rfl]
    linear_combination (-4 * (Real.sin x : ℂ) * (Real.cos y : ℂ)) * Complex.I_sq
  · rw [show blockWeight 1 1 = -1 from rfl]
    linear_combination (-4 * (Real.sin x : ℂ) * (Real.sin y : ℂ)) * Complex.I_sq

theorem bivariateEval_encPart (M L : ℕ) (F : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) (i j : Fin 2) (β θ : ℝ) :
    bivariateEval (Complex.exp (β * Complex.I)) (Complex.exp (θ * Complex.I)) (encPart M L F i j) =
      Complex.exp (β * Complex.I) ^ M * Complex.exp (θ * Complex.I) ^ L *
        ∑ k ∈ range (M + 1), ∑ l ∈ range (L + 1),
          (F i j k l : ℂ) * (modeValue i (k * β) * modeValue j (l * θ)) := by
  simp only [encPart, map_sum, map_mul, bivariateEval_C_C, bivariateEval_map_C, mul_sum]
  refine sum_congr rfl fun k hk ↦ sum_congr rfl fun l hl ↦ ?_
  rw [bivariateEval_C]
  rw [eval₂_modePoly M i (Nat.lt_succ_iff.mp (mem_range.mp hk)),
    eval₂_modePoly L j (Nat.lt_succ_iff.mp (mem_range.mp hl))]
  ring

/-- The value of an integer table: `∑ F i j k l · m_i (k β) · m_j (l θ)`. -/
def trigTableValue (M L : ℕ) (F : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) (β θ : ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k ∈ range (M + 1), ∑ l ∈ range (L + 1),
    (F i j k l : ℝ) * trigMode i (k * β) * trigMode j (l * θ)

/-- On the unit torus, `encRe + i encIm` combines the four blocks with the weights
`blockWeight`. -/
theorem bivariateEval_encRe_add_I_mul_eq_sum (M L : ℕ) (F : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) (z w : ℂ) :
    bivariateEval z w (encRe M L F) + Complex.I * bivariateEval z w (encIm M L F) =
      ∑ i, ∑ j, blockWeight i j * bivariateEval z w (encPart M L F i j) := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [encRe, encIm, map_sub, map_neg, map_add]
  rw [show blockWeight 0 0 = 1 from rfl, show blockWeight 0 1 = -Complex.I from rfl,
    show blockWeight 1 0 = -Complex.I from rfl, show blockWeight 1 1 = -1 from rfl]
  ring

/-- On the unit torus, a weighted block is `4 z^M w^L` times the value of the block. -/
theorem blockWeight_mul_bivariateEval_encPart (M L : ℕ) (F : Fin 2 → Fin 2 → ℕ → ℕ → ℤ)
    (i j : Fin 2) (β θ : ℝ) :
    blockWeight i j * bivariateEval (Complex.exp (β * Complex.I)) (Complex.exp (θ * Complex.I))
        (encPart M L F i j) =
      4 * Complex.exp (β * Complex.I) ^ M * Complex.exp (θ * Complex.I) ^ L *
        (∑ k ∈ range (M + 1), ∑ l ∈ range (L + 1),
          (F i j k l : ℝ) * trigMode i (k * β) * trigMode j (l * θ) : ℝ) := by
  push_cast
  rw [bivariateEval_encPart]
  simp only [mul_sum]
  refine sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ ?_
  have h := blockWeight_mul_modeValue i j (k * β) (l * θ)
  push_cast at h
  linear_combination ((F i j k l : ℂ) * Complex.exp (β * Complex.I) ^ M *
    Complex.exp (θ * Complex.I) ^ L) * h

/-- On the unit torus, `encRe + i encIm` is `4 z^M w^L` times the table value. -/
theorem bivariateEval_encRe_add_I_mul (M L : ℕ) (F : Fin 2 → Fin 2 → ℕ → ℕ → ℤ) (β θ : ℝ) :
    bivariateEval (Complex.exp (β * Complex.I)) (Complex.exp (θ * Complex.I)) (encRe M L F) +
        Complex.I * bivariateEval (Complex.exp (β * Complex.I)) (Complex.exp (θ * Complex.I))
          (encIm M L F) =
      4 * Complex.exp (β * Complex.I) ^ M * Complex.exp (θ * Complex.I) ^ L *
        trigTableValue M L F β θ := by
  rw [bivariateEval_encRe_add_I_mul_eq_sum, trigTableValue]
  simp only [blockWeight_mul_bivariateEval_encPart]
  push_cast
  simp only [mul_sum]

/-- Encodings that multiply as exponential sums give tables whose values multiply, with the
factor `4` of the two product-to-sum halvings. -/
theorem trigTableValue_eq_of_enc {Mp Lp Mq Lq : ℕ} (Fp Fq Fr : Fin 2 → Fin 2 → ℕ → ℕ → ℤ)
    (hRe : encRe (Mp + Mq) (Lp + Lq) Fr =
      encRe Mp Lp Fp * encRe Mq Lq Fq - encIm Mp Lp Fp * encIm Mq Lq Fq)
    (hIm : encIm (Mp + Mq) (Lp + Lq) Fr =
      encRe Mp Lp Fp * encIm Mq Lq Fq + encIm Mp Lp Fp * encRe Mq Lq Fq) (β θ : ℝ) :
    trigTableValue (Mp + Mq) (Lp + Lq) Fr β θ =
      4 * (trigTableValue Mp Lp Fp β θ * trigTableValue Mq Lq Fq β θ) := by
  set z := Complex.exp (β * Complex.I)
  set w := Complex.exp (θ * Complex.I)
  have hp := bivariateEval_encRe_add_I_mul Mp Lp Fp β θ
  have hq := bivariateEval_encRe_add_I_mul Mq Lq Fq β θ
  have hr := bivariateEval_encRe_add_I_mul (Mp + Mq) (Lp + Lq) Fr β θ
  rw [hRe, hIm, map_sub, map_add, map_mul, map_mul, map_mul, map_mul] at hr
  have h16 : 4 * z ^ (Mp + Mq) * w ^ (Lp + Lq) * trigTableValue (Mp + Mq) (Lp + Lq) Fr β θ =
      (4 * z ^ Mp * w ^ Lp * trigTableValue Mp Lp Fp β θ) *
        (4 * z ^ Mq * w ^ Lq * trigTableValue Mq Lq Fq β θ) := by
    rw [← hr, ← hp, ← hq]
    linear_combination
      (-(bivariateEval z w (encIm Mp Lp Fp) * bivariateEval z w (encIm Mq Lq Fq))) *
      Complex.I_sq
  have hne : 4 * z ^ (Mp + Mq) * w ^ (Lp + Lq) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (Complex.exp_ne_zero _)))
      (pow_ne_zero _ (Complex.exp_ne_zero _))
  have hc : (trigTableValue (Mp + Mq) (Lp + Lq) Fr β θ : ℂ) =
      4 * (trigTableValue Mp Lp Fp β θ * trigTableValue Mq Lq Fq β θ) := by
    refine mul_left_cancel₀ hne ?_
    rw [h16, pow_add, pow_add]
    ring
  exact_mod_cast hc

/-! ### The packed check -/

/-- One packed identity `a b + σ c d = e` with a digit margin identifies the polynomials. -/
theorem signedPolynomial_mul_add_mul_eq_of_packed {n₁ n₂ n₃ n₄ n₅ bits : ℕ}
    (a : CoefficientTree n₁) (b : CoefficientTree n₂) (c : CoefficientTree n₃)
    (d : CoefficientTree n₄) (e : CoefficientTree n₅) {σ : ℤ} (hσ : |σ| ≤ 1)
    (hmass : signedMass a * signedMass b + signedMass c * signedMass d + signedMass e <
      (2 : ℤ) ^ bits)
    (hpacked : packSignedBinary bits a * packSignedBinary bits b +
      σ * (packSignedBinary bits c * packSignedBinary bits d) = packSignedBinary bits e) :
    signedPolynomial a * signedPolynomial b + C σ * (signedPolynomial c * signedPolynomial d) =
      signedPolynomial e := by
  apply intPolynomial_eq_of_eval_eq (b := (2 : ℤ) ^ bits) (by positivity)
  · intro k
    rw [coeff_add, coeff_C_mul]
    have h₁ := abs_signedPolynomial_mul_coeff_le a (signedPolynomial b) (signedMass_nonneg b)
      (abs_signedPolynomial_coeff_le b) k
    have h₂ := abs_signedPolynomial_mul_coeff_le c (signedPolynomial d) (signedMass_nonneg d)
      (abs_signedPolynomial_coeff_le d) k
    have h₃ := abs_signedPolynomial_coeff_le e k
    have h₄ : |σ * (signedPolynomial c * signedPolynomial d).coeff k| ≤
        |(signedPolynomial c * signedPolynomial d).coeff k| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) hσ
    calc _ ≤ |(signedPolynomial a * signedPolynomial b).coeff k +
          σ * (signedPolynomial c * signedPolynomial d).coeff k| + |(signedPolynomial e).coeff k| :=
          abs_sub _ _
      _ ≤ |(signedPolynomial a * signedPolynomial b).coeff k| +
          |σ * (signedPolynomial c * signedPolynomial d).coeff k| +
            |(signedPolynomial e).coeff k| := by gcongr; exact abs_add_le _ _
      _ < _ := by linarith
  · simpa only [eval_add, eval_mul, eval_C, ← packSignedBinary_eq_eval] using hpacked

/-- The digit margin and the packed identity `a b + σ c d = e`, as one Boolean check. -/
def signedPairCheck {n₁ n₂ n₃ n₄ n₅ : ℕ} (bits : ℕ) (a : CoefficientTree n₁)
    (b : CoefficientTree n₂) (c : CoefficientTree n₃) (d : CoefficientTree n₄)
    (e : CoefficientTree n₅) (σ : ℤ) : Bool :=
  decide (signedMass a * signedMass b + signedMass c * signedMass d + signedMass e <
    (2 : ℤ) ^ bits) &&
  decide (packSignedBinary bits a * packSignedBinary bits b +
    σ * (packSignedBinary bits c * packSignedBinary bits d) = packSignedBinary bits e)

theorem signedPairCheck_sound {n₁ n₂ n₃ n₄ n₅ : ℕ} (bits : ℕ) (a : CoefficientTree n₁)
    (b : CoefficientTree n₂) (c : CoefficientTree n₃) (d : CoefficientTree n₄)
    (e : CoefficientTree n₅) {σ : ℤ} (hσ : |σ| ≤ 1)
    (h : signedPairCheck bits a b c d e σ = true) :
    signedPolynomial a * signedPolynomial b + C σ * (signedPolynomial c * signedPolynomial d) =
      signedPolynomial e := by
  simp only [signedPairCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact signedPolynomial_mul_add_mul_eq_of_packed a b c d e hσ h.1 h.2

/-- The Kronecker array of a two-index coefficient function on `[0, 2 ^ depth)`: entry `n` is
`g (n / S) (n % S)`. -/
def kroneckerTree (S depth : ℕ) (g : ℕ → ℕ → ℤ) : CoefficientTree depth :=
  CoefficientTree.ofFnBlock (fun n ↦ encodeSignedCoefficient (g (n / S) (n % S))) depth 0

theorem signedPolynomial_kroneckerTree {S d D depth : ℕ} {E : Polynomial (Polynomial ℤ)}
    {g : ℕ → ℕ → ℤ} (hg : ∀ a b, (E.coeff a).coeff b = g a b) (hE : InnerDegreeLE d E)
    (hD : ∀ a, D < a → E.coeff a = 0) (hdS : d < S) (hdepth : S * D + d < 2 ^ depth) :
    signedPolynomial (kroneckerTree S depth g) = kroneckerSubstitution S E := by
  ext n
  rw [signedPolynomial_coeff]
  split_ifs with hn
  · rw [kroneckerTree, CoefficientTree.lookup_ofFnBlock _ _ _ hn, signedCoefficient_encode,
      zero_add, ← hg, ← coeff_kroneckerSubstitution hE hdS _ (Nat.mod_lt _ (by omega)),
      Nat.div_add_mod]
  · exact (coeff_kroneckerSubstitution_eq_zero hE hD hdS (by omega)).symm

/-- The Kronecker array of `encRe` of a table. -/
def reTree (S depth : ℕ) {M L : ℕ} (c : TrigPoly2 M L ℤ) :
    CoefficientTree depth :=
  kroneckerTree S depth (encReCoeff M L (c.coeffN))

/-- The Kronecker array of `encIm` of a table. -/
def imTree (S depth : ℕ) {M L : ℕ} (c : TrigPoly2 M L ℤ) :
    CoefficientTree depth :=
  kroneckerTree S depth (encImCoeff M L (c.coeffN))

theorem signedPolynomial_reTree {S depth M L : ℕ}
    (c : TrigPoly2 M L ℤ) (hS : 2 * L < S)
    (hdepth : S * (2 * M) + 2 * L < 2 ^ depth) :
    signedPolynomial (reTree S depth c) = kroneckerSubstitution S (encRe M L (c.coeffN)) :=
  signedPolynomial_kroneckerTree (coeff_coeff_encRe M L _) (innerDegreeLE_encRe M L _)
    (fun _ ha ↦ coeff_encRe_eq_zero M L _ ha) hS hdepth

theorem signedPolynomial_imTree {S depth M L : ℕ}
    (c : TrigPoly2 M L ℤ) (hS : 2 * L < S)
    (hdepth : S * (2 * M) + 2 * L < 2 ^ depth) :
    signedPolynomial (imTree S depth c) = kroneckerSubstitution S (encIm M L (c.coeffN)) :=
  signedPolynomial_kroneckerTree (coeff_coeff_encIm M L _) (innerDegreeLE_encIm M L _)
    (fun _ ha ↦ coeff_encIm_eq_zero M L _ ha) hS hdepth

/-- The cells of `sin (0 · β)` and `sin (0 · θ)` of an integer table are zero. -/
def zeroModesCheck {M L : ℕ} (c : TrigPoly2 M L ℤ) : Bool :=
  decide (∀ j (l : Fin (L + 1)), c.coeff 1 j 0 l = 0) &&
    decide (∀ i (k : Fin (M + 1)), c.coeff i 1 k 0 = 0)

theorem zeroModesVanish_of_zeroModesCheck {M L : ℕ} {c : TrigPoly2 M L ℤ}
    (h : zeroModesCheck c = true) : c.ZeroModesVanish := by
  simp only [zeroModesCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  intro i j k l hc
  rcases hc with ⟨rfl, hk⟩ | ⟨rfl, hl⟩
  · rw [show k = 0 from Fin.ext (by simpa using hk)]
    exact h.1 j l
  · rw [show l = 0 from Fin.ext (by simpa using hl)]
    exact h.2 i k

/-- The product check of three integer tables: `cr` is four times the product of `cp` and `cq`,
certified by two packed identities of Kronecker arrays with stride `S` (one for `encRe`, one for
`encIm`), with the trees of depths `dp`, `dq`, `dr` and digits of `bits` bits. -/
def trigProductCheck {Mp Lp Mq Lq : ℕ} (S bits dp dq dr : ℕ)
    (cp : TrigPoly2 Mp Lp ℤ)
    (cq : TrigPoly2 Mq Lq ℤ)
    (cr : TrigPoly2 (Mp + Mq) (Lp + Lq) ℤ) : Bool :=
  Nat.blt (2 * (Lp + Lq)) S && Nat.blt (S * (2 * Mp) + 2 * Lp) (2 ^ dp) &&
    Nat.blt (S * (2 * Mq) + 2 * Lq) (2 ^ dq) &&
    Nat.blt (S * (2 * (Mp + Mq)) + 2 * (Lp + Lq)) (2 ^ dr) &&
    signedPairCheck bits (reTree S dp cp) (reTree S dq cq) (imTree S dp cp) (imTree S dq cq)
      (reTree S dr cr) (-1) &&
    signedPairCheck bits (reTree S dp cp) (imTree S dq cq) (imTree S dp cp) (reTree S dq cq)
      (imTree S dr cr) 1 &&
    zeroModesCheck cr

/-- A successful product check makes the value of `cr` four times the product of the values. -/
theorem trigTableValue_eq_of_trigProductCheck {Mp Lp Mq Lq : ℕ} {S bits dp dq dr : ℕ}
    {cp : TrigPoly2 Mp Lp ℤ}
    {cq : TrigPoly2 Mq Lq ℤ}
    {cr : TrigPoly2 (Mp + Mq) (Lp + Lq) ℤ}
    (h : trigProductCheck S bits dp dq dr cp cq cr = true) (β θ : ℝ) :
    trigTableValue (Mp + Mq) (Lp + Lq) (cr.coeffN) β θ =
      4 * (trigTableValue Mp Lp (cp.coeffN) β θ * trigTableValue Mq Lq (cq.coeffN) β θ) := by
  simp only [trigProductCheck, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hS, hp⟩, hq⟩, hr⟩, hRe⟩, hIm⟩, -⟩ := h
  have hSp : 2 * Lp < S := by omega
  have hSq : 2 * Lq < S := by omega
  have hRe' := signedPairCheck_sound bits _ _ _ _ _ (by norm_num) hRe
  have hIm' := signedPairCheck_sound bits _ _ _ _ _ (by norm_num) hIm
  rw [signedPolynomial_reTree cp hSp hp, signedPolynomial_reTree cq hSq hq,
    signedPolynomial_imTree cp hSp hp, signedPolynomial_imTree cq hSq hq,
    signedPolynomial_reTree cr hS hr, ← map_mul, ← map_mul, C_neg, C_1, neg_one_mul,
    ← map_neg, ← map_add, ← sub_eq_add_neg] at hRe'
  rw [signedPolynomial_reTree cp hSp hp, signedPolynomial_reTree cq hSq hq,
    signedPolynomial_imTree cp hSp hp, signedPolynomial_imTree cq hSq hq,
    signedPolynomial_imTree cr hS hr, ← map_mul, ← map_mul, C_1, one_mul, ← map_add] at hIm'
  refine trigTableValue_eq_of_enc _ _ _ ?_ ?_ β θ
  · refine (kroneckerSubstitution_injective (d := 2 * (Lp + Lq)) (innerDegreeLE_encRe _ _ _) ?_ hS
      hRe'.symm)
    rw [show 2 * (Lp + Lq) = 2 * Lp + 2 * Lq by ring]
    exact ((innerDegreeLE_encRe _ _ _).mul (innerDegreeLE_encRe _ _ _)).sub
      ((innerDegreeLE_encIm _ _ _).mul (innerDegreeLE_encIm _ _ _))
  · refine (kroneckerSubstitution_injective (d := 2 * (Lp + Lq)) (innerDegreeLE_encIm _ _ _) ?_ hS
      hIm'.symm)
    rw [show 2 * (Lp + Lq) = 2 * Lp + 2 * Lq by ring]
    exact ((innerDegreeLE_encRe _ _ _).mul (innerDegreeLE_encIm _ _ _)).add
      ((innerDegreeLE_encIm _ _ _).mul (innerDegreeLE_encRe _ _ _))

/-! ### Products of single-block tables -/

/-- The sign of a product of single blocks: `(-1)` for each variable in which both factors are
sines. -/
def blockProductSign (i j i' j' : Fin 2) : ℤ :=
  trigSumSign i i' * trigSumSign j j'

theorem blockWeight_mul_blockWeight (i j i' j' : Fin 2) :
    blockWeight i j * blockWeight i' j' * (blockProductSign i j i' j' : ℂ) =
      blockWeight (i + i') (j + j') := by
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp [blockWeight, blockProductSign, trigSumSign]

/-- The table with the block `c` at `(i, j)` and zeros elsewhere. -/
def blockInt {M L : ℕ} (i j : Fin 2) (c : Fin (M + 1) → Fin (L + 1) → ℤ) : TrigPoly2 M L ℤ :=
  ⟨fun i' j' k l ↦ if i' = i ∧ j' = j then c k l else 0⟩

theorem coeffN_blockInt {M L : ℕ} (i j : Fin 2) (c : Fin (M + 1) → Fin (L + 1) → ℤ)
    (i' j' : Fin 2) (k l : ℕ) : (blockInt i j c).coeffN i' j' k l =
      if i' = i ∧ j' = j then (blockInt i j c).coeffN i j k l else 0 := by
  unfold TrigPoly2.coeffN blockInt
  split_ifs <;> simp_all

theorem encPart_blockInt_of_ne {M L : ℕ} {i j i' j' : Fin 2}
    (c : Fin (M + 1) → Fin (L + 1) → ℤ) (h : ¬(i' = i ∧ j' = j)) :
    encPart M L ((blockInt i j c).coeffN) i' j' = 0 := by
  unfold encPart
  refine sum_eq_zero fun k _ ↦ sum_eq_zero fun l _ ↦ ?_
  rw [coeffN_blockInt, ite_eq_right h]
  simp

/-- A single block is `4 z^M w^L` times its value, up to its weight. -/
theorem blockWeight_mul_bivariateEval_encPart_blockInt {M L : ℕ} (i j : Fin 2)
    (c : Fin (M + 1) → Fin (L + 1) → ℤ) (β θ : ℝ) :
    blockWeight i j * bivariateEval (Complex.exp (β * Complex.I)) (Complex.exp (θ * Complex.I))
        (encPart M L ((blockInt i j c).coeffN) i j) =
      4 * Complex.exp (β * Complex.I) ^ M * Complex.exp (θ * Complex.I) ^ L *
        trigTableValue M L ((blockInt i j c).coeffN) β θ := by
  rw [← bivariateEval_encRe_add_I_mul, bivariateEval_encRe_add_I_mul_eq_sum, sum_eq_single i,
    sum_eq_single j]
  · intro j' _ hj'
    rw [encPart_blockInt_of_ne c fun h ↦ hj' h.2, map_zero, mul_zero]
  · simp
  · intro i' _ hi'
    exact sum_eq_zero fun j' _ ↦ by
      rw [encPart_blockInt_of_ne c fun h ↦ hi' h.1, map_zero, mul_zero]
  · simp

/-- Single blocks that multiply as exponential sums, with the sign `blockProductSign`, give
tables whose values multiply, with the factor `4`. -/
theorem trigTableValue_eq_of_encPart {Mp Lp Mq Lq : ℕ} (i j i' j' : Fin 2)
    (cp : Fin (Mp + 1) → Fin (Lp + 1) → ℤ) (cq : Fin (Mq + 1) → Fin (Lq + 1) → ℤ)
    (cr : Fin (Mp + Mq + 1) → Fin (Lp + Lq + 1) → ℤ)
    (h : encPart Mp Lp ((blockInt i j cp).coeffN) i j *
        encPart Mq Lq ((blockInt i' j' cq).coeffN) i' j' =
      C (C (blockProductSign i j i' j')) *
        encPart (Mp + Mq) (Lp + Lq) ((blockInt (i + i') (j + j') cr).coeffN) (i + i') (j + j'))
    (β θ : ℝ) :
    trigTableValue (Mp + Mq) (Lp + Lq) ((blockInt (i + i') (j + j') cr).coeffN) β θ =
      4 * (trigTableValue Mp Lp ((blockInt i j cp).coeffN) β θ *
        trigTableValue Mq Lq ((blockInt i' j' cq).coeffN) β θ) := by
  set z := Complex.exp (β * Complex.I)
  set w := Complex.exp (θ * Complex.I)
  have hp := blockWeight_mul_bivariateEval_encPart_blockInt i j cp β θ
  have hq := blockWeight_mul_bivariateEval_encPart_blockInt i' j' cq β θ
  have hr := blockWeight_mul_bivariateEval_encPart_blockInt (i + i') (j + j') cr β θ
  have he := congrArg (bivariateEval z w) h
  rw [map_mul, map_mul, bivariateEval_C_C] at he
  have h16 : 4 * z ^ (Mp + Mq) * w ^ (Lp + Lq) *
      trigTableValue (Mp + Mq) (Lp + Lq) ((blockInt (i + i') (j + j') cr).coeffN) β θ =
      (4 * z ^ Mp * w ^ Lp * trigTableValue Mp Lp ((blockInt i j cp).coeffN) β θ) *
        (4 * z ^ Mq * w ^ Lq * trigTableValue Mq Lq ((blockInt i' j' cq).coeffN) β θ) := by
    rw [← hr, ← hp, ← hq, ← blockWeight_mul_blockWeight i j i' j']
    linear_combination (blockWeight i j * blockWeight i' j') * he.symm
  have hne : 4 * z ^ (Mp + Mq) * w ^ (Lp + Lq) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (Complex.exp_ne_zero _)))
      (pow_ne_zero _ (Complex.exp_ne_zero _))
  have hc : (trigTableValue (Mp + Mq) (Lp + Lq) ((blockInt (i + i') (j + j') cr).coeffN) β θ : ℂ) =
      4 * (trigTableValue Mp Lp ((blockInt i j cp).coeffN) β θ *
        trigTableValue Mq Lq ((blockInt i' j' cq).coeffN) β θ) := by
    refine mul_left_cancel₀ hne ?_
    rw [h16, pow_add, pow_add]
    ring
  exact_mod_cast hc

/-- The Kronecker array of `σ` times the encoding of a single block. -/
def blockTree (S depth : ℕ) {M L : ℕ} (σ : ℤ) (i j : Fin 2)
    (c : Fin (M + 1) → Fin (L + 1) → ℤ) : CoefficientTree depth :=
  kroneckerTree S depth fun a b ↦ σ * modeCollapse M i a fun k ↦ modeCollapse L j b fun l ↦
    (blockInt i j c).coeffN i j k l

theorem signedPolynomial_blockTree {S depth M L : ℕ} (σ : ℤ) (i j : Fin 2)
    (c : Fin (M + 1) → Fin (L + 1) → ℤ) (hS : 2 * L < S)
    (hdepth : S * (2 * M) + 2 * L < 2 ^ depth) :
    signedPolynomial (blockTree S depth σ i j c) =
      kroneckerSubstitution S (C (C σ) * encPart M L ((blockInt i j c).coeffN) i j) := by
  refine signedPolynomial_kroneckerTree (fun a b ↦ ?_) (fun k ↦ ?_) (fun a ha ↦ ?_) hS hdepth
  · rw [coeff_C_mul, coeff_C_mul, coeff_coeff_encPart, encPartCoeff]
  · rw [coeff_C_mul]
    exact (natDegree_C_mul_le _ _).trans (innerDegreeLE_encPart M L _ i j k)
  · rw [coeff_C_mul, coeff_encPart_eq_zero M L _ i j ha, mul_zero]

/-- The product check of two single-block tables: `cr` in the block `(i + i', j + j')` is four
times the product of `cp` in `(i, j)` and `cq` in `(i', j')`, certified by one packed product
(`signedProductCheck`) of the Kronecker arrays. -/
def trigBlockProductCheck {Mp Lp Mq Lq : ℕ} (S bits dp dq dr : ℕ) (i j i' j' : Fin 2)
    (cp : Fin (Mp + 1) → Fin (Lp + 1) → ℤ) (cq : Fin (Mq + 1) → Fin (Lq + 1) → ℤ)
    (cr : Fin (Mp + Mq + 1) → Fin (Lp + Lq + 1) → ℤ) : Bool :=
  Nat.blt (2 * (Lp + Lq)) S && Nat.blt (S * (2 * Mp) + 2 * Lp) (2 ^ dp) &&
    Nat.blt (S * (2 * Mq) + 2 * Lq) (2 ^ dq) &&
    Nat.blt (S * (2 * (Mp + Mq)) + 2 * (Lp + Lq)) (2 ^ dr) &&
    signedProductCheck bits (blockTree S dp 1 i j cp) (blockTree S dq 1 i' j' cq)
      (blockTree S dr (blockProductSign i j i' j') (i + i') (j + j') cr) &&
    zeroModesCheck (blockInt (i + i') (j + j') cr)

theorem trigTableValue_eq_of_trigBlockProductCheck {Mp Lp Mq Lq : ℕ} {S bits dp dq dr : ℕ}
    {i j i' j' : Fin 2} {cp : Fin (Mp + 1) → Fin (Lp + 1) → ℤ}
    {cq : Fin (Mq + 1) → Fin (Lq + 1) → ℤ} {cr : Fin (Mp + Mq + 1) → Fin (Lp + Lq + 1) → ℤ}
    (h : trigBlockProductCheck S bits dp dq dr i j i' j' cp cq cr = true) (β θ : ℝ) :
    trigTableValue (Mp + Mq) (Lp + Lq) ((blockInt (i + i') (j + j') cr).coeffN) β θ =
      4 * (trigTableValue Mp Lp ((blockInt i j cp).coeffN) β θ *
        trigTableValue Mq Lq ((blockInt i' j' cq).coeffN) β θ) := by
  simp only [trigBlockProductCheck, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨hS, hp⟩, hq⟩, hr⟩, hprod⟩, -⟩ := h
  have h' := signedProductCheck_sound bits _ _ _ hprod
  rw [signedPolynomial_blockTree 1 i j cp (by omega) hp,
    signedPolynomial_blockTree 1 i' j' cq (by omega) hq,
    signedPolynomial_blockTree _ _ _ cr hS hr, map_one, map_one, one_mul, one_mul,
    ← map_mul] at h'
  refine trigTableValue_eq_of_encPart i j i' j' cp cq cr ?_ β θ
  refine kroneckerSubstitution_injective (d := 2 * (Lp + Lq)) ?_ ?_ hS h'
  · rw [show 2 * (Lp + Lq) = 2 * Lp + 2 * Lq by ring]
    exact (innerDegreeLE_encPart _ _ _ _ _).mul (innerDegreeLE_encPart _ _ _ _ _)
  · exact fun k ↦ by
      rw [coeff_C_mul]
      exact (natDegree_C_mul_le _ _).trans (innerDegreeLE_encPart _ _ _ _ _ k)

end CAS.Numerics

namespace PDE.Analysis.TrigPoly2

open Finset CAS.Numerics

variable {M L Mq Lq : ℕ}

/-- The rational table `c / d` of an integer table `c`. -/
def ofInt (c : TrigPoly2 M L ℤ) (d : ℚ) : TrigPoly2 M L :=
  ⟨fun i j k l ↦ (c.coeff i j k l : ℚ) / d⟩

theorem coeffN_ofInt (c : TrigPoly2 M L ℤ) (d : ℚ) (i j : Fin 2)
    (k l : ℕ) : (ofInt c d).coeffN i j k l = (c.coeffN i j k l : ℚ) / d := by
  unfold coeffN ofInt
  split_ifs <;> simp

theorem eval_ofInt (c : TrigPoly2 M L ℤ) (d : ℚ) (β θ : ℝ) :
    (ofInt c d).eval β θ = trigTableValue M L (c.coeffN) β θ / d := by
  simp only [eval_eq_sum_range, coeffN_ofInt, trigTableValue, sum_div]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦
    sum_congr rfl fun l _ ↦ ?_
  rw [map_div₀, eq_ratCast, eq_ratCast, Rat.cast_intCast]
  ring

/-- A successful product check: the table `cr / (4uv)` is the product of `cp / u` and
`cq / v`. -/
theorem eval_ofInt_eq_mul_of_trigProductCheck {S bits dp dq dr : ℕ}
    {cp : TrigPoly2 M L ℤ}
    {cq : TrigPoly2 Mq Lq ℤ}
    {cr : TrigPoly2 (M + Mq) (L + Lq) ℤ}
    (h : trigProductCheck S bits dp dq dr cp cq cr = true) (u v : ℚ) (β θ : ℝ) :
    (ofInt cr (4 * u * v)).eval β θ = (ofInt cp u).eval β θ * (ofInt cq v).eval β θ := by
  rw [eval_ofInt, eval_ofInt, eval_ofInt, trigTableValue_eq_of_trigProductCheck h, div_mul_div_comm]
  push_cast
  rw [mul_assoc 4 (u : ℝ), mul_div_mul_left _ _ four_ne_zero]

/-- A successful product check identifies `cr / (4uv)` with the product table. -/
theorem eval_ofInt_eq_eval_mul_of_trigProductCheck {S bits dp dq dr : ℕ}
    {cp : TrigPoly2 M L ℤ}
    {cq : TrigPoly2 Mq Lq ℤ}
    {cr : TrigPoly2 (M + Mq) (L + Lq) ℤ}
    (h : trigProductCheck S bits dp dq dr cp cq cr = true) (u v : ℚ) (β θ : ℝ) :
    (ofInt cr (4 * u * v)).eval β θ = ((ofInt cp u).mul (ofInt cq v)).eval β θ := by
  rw [eval_mul, eval_ofInt_eq_mul_of_trigProductCheck h]

/-- The rational table with the block `c / d` at `(i, j)` and zeros elsewhere. -/
def ofBlock (i j : Fin 2) (c : Fin (M + 1) → Fin (L + 1) → ℤ) (d : ℚ) : TrigPoly2 M L :=
  ofInt (blockInt i j c) d

/-- A successful single-block product check: the block `cr / (4uv)` at `(i + i', j + j')` is
the product of the blocks `cp / u` at `(i, j)` and `cq / v` at `(i', j')`. -/
theorem eval_ofBlock_eq_mul_of_trigBlockProductCheck {S bits dp dq dr : ℕ} {i j i' j' : Fin 2}
    {cp : Fin (M + 1) → Fin (L + 1) → ℤ} {cq : Fin (Mq + 1) → Fin (Lq + 1) → ℤ}
    {cr : Fin (M + Mq + 1) → Fin (L + Lq + 1) → ℤ}
    (h : trigBlockProductCheck S bits dp dq dr i j i' j' cp cq cr = true) (u v : ℚ) (β θ : ℝ) :
    (ofBlock (i + i') (j + j') cr (4 * u * v)).eval β θ =
      (ofBlock i j cp u).eval β θ * (ofBlock i' j' cq v).eval β θ := by
  rw [ofBlock, ofBlock, ofBlock, eval_ofInt, eval_ofInt, eval_ofInt,
    trigTableValue_eq_of_trigBlockProductCheck h, div_mul_div_comm]
  push_cast
  rw [mul_assoc 4 (u : ℝ), mul_div_mul_left _ _ four_ne_zero]

theorem zeroModesVanish_ofInt {c : TrigPoly2 M L ℤ} (hc : c.ZeroModesVanish) (d : ℚ) :
    (ofInt c d).ZeroModesVanish := fun i j k l h ↦ by
  simp [ofInt, hc i j k l h]

/-- The table certified by a successful product check has no `sin (0 · β)` or `sin (0 · θ)`
cells. -/
theorem zeroModesVanish_ofInt_of_trigProductCheck {S bits dp dq dr : ℕ}
    {cp : TrigPoly2 M L ℤ} {cq : TrigPoly2 Mq Lq ℤ} {cr : TrigPoly2 (M + Mq) (L + Lq) ℤ}
    (h : trigProductCheck S bits dp dq dr cp cq cr = true) (d : ℚ) :
    (ofInt cr d).ZeroModesVanish := by
  simp only [trigProductCheck, Bool.and_eq_true] at h
  exact zeroModesVanish_ofInt (zeroModesVanish_of_zeroModesCheck h.2) d

/-- The block certified by a successful single-block product check has no `sin (0 · β)` or
`sin (0 · θ)` cells. -/
theorem zeroModesVanish_ofBlock_of_trigBlockProductCheck {S bits dp dq dr : ℕ}
    {i j i' j' : Fin 2} {cp : Fin (M + 1) → Fin (L + 1) → ℤ}
    {cq : Fin (Mq + 1) → Fin (Lq + 1) → ℤ} {cr : Fin (M + Mq + 1) → Fin (L + Lq + 1) → ℤ}
    (h : trigBlockProductCheck S bits dp dq dr i j i' j' cp cq cr = true) (d : ℚ) :
    (ofBlock (i + i') (j + j') cr d).ZeroModesVanish := by
  simp only [trigBlockProductCheck, Bool.and_eq_true] at h
  exact zeroModesVanish_ofInt (zeroModesVanish_of_zeroModesCheck h.2) d

end PDE.Analysis.TrigPoly2
