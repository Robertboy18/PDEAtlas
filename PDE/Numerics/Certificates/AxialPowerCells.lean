/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Numerics.RootWitness
public import PDE.Analysis.Calculus.AxialPowerBounds
public import CAS.Continuum.Interval.Rational.RelativeHull

/-!
# Cell bounds of sums of axial-radial powers in the plane

A weight `w(x) = ∑ c_k |x₀|^{a_k} |x|^{b_k}` with rational data and `c_k ≥ 0` is a list of
`AxialTerm`s (`axialTermsValue`). On a rectangle `[x₀, x₁] × [y₀, y₁]` of the closed quadrant
(`PlaneCell`), for the points of the open quadrant in it (`PlaneCell.Mem`):

* `axialTermsLower` and `axialTermsUpper` bound `w` termwise: each factor is monotone in `|x₀|`
  and in `|x|²`, so its extreme values are powers of the endpoints, enclosed by `rpowBounds`
  (`axialTermsLower_le`, `le_axialTermsUpper`). The upper bound is `none` when a factor with a
  negative exponent has a zero endpoint (the axis or the origin): a caller multiplies the weight by
  `|x₀|^p |x|^q` first (`AxialTerm.shift`), which keeps it finite there.
* `polarMean ts f W R` is the mean of the statistic `f` of the terms with the masses
  `c_k W^{s_k} R^{u_k}`, where `W = x₀²/|x|²`, `R = |x|²`, and the exponents
  `s_k = (a_k - min a)/2`, `u_k = (a_k + b_k - min (a + b))/2` are normalized to be nonnegative.
  At a point of the open quadrant it is `∑ f_k c_k T_k(x) / w(x)` (`polarMean_eq`). When `f` is
  comonotone with `s` and `u` (`IsComonotone`), it is increasing in `W` and in `R`
  (`polarMean_mono`), by the cross-multiplied double sum
  `∑_{k,l} (f_k - f_l)(m'_k m_l - m_k m'_l) ≥ 0` (`sum_mul_sum_le_of_cross`).
  `polarMeanBounds` encloses it at a rational point.

The log-derivatives of `w` are such means: `x·∇w/w` is the mean of the degrees `a_k + b_k` (Euler's
identity), and `x₀ ∂₀w/w = (1 - W) B + W Γ`, `x₁ ∂₁w/w = (1 - W)(Γ - B)` with `Γ` the mean degree
and `B` the mean axial exponent (`mul_partialDeriv_zero_div`, `mul_partialDeriv_one_div`). For the
energy weights of Chen and Hou (Part I, Appendix C.1, (C.2)-(C.4)) the terms with the factor
`|x₀|^{-1/2}` are exactly those of the lowest degrees, so `Γ` and `B` are comonotone, and on a cell
they lie between their values at the polar corners `(W₋, R₋)` and `(W₊, R₊)`
(`axialTermsMean_mem`). The module `PDE.Numerics.Certificates.AxialWeight` packages such weights
and their cell rates.

## Main definitions

* `AxialTerm`: a term `c |x₀|^a |x|^b` with rational data; `axialTermsValue` sums a list of them.
* `PlaneCell`: a rectangle of the closed quadrant, with its points `PlaneCell.Mem` of the open
  quadrant.
* `axialTermsLower`, `axialTermsUpper`: termwise lower and upper bounds of a weight on a cell.
* `polarMean`: the mean of a statistic of the terms with the normalized polar masses at `(W, R)`.
* `polarMeanBounds`: rational bounds of the polar mean at a rational point.
* `axialTermsMeanBounds`: rational bounds of a comonotone mean on a cell, from its polar corners.
* `axialRateBounds`, `transverseRateBounds`: bounds of `x₀ ∂₀w/w` and `x₁ ∂₁w/w` from bounds of
  `B`, `Γ` and `W`.

## Main results

* `axialTermsLower_le`: a weight with nonnegative coefficients is at least `axialTermsLower` at
  every point of a valid cell.
* `le_axialTermsUpper`: such a weight is at most every value of `axialTermsUpper` on the cell.
* `polarMean_eq`: at a point of the open quadrant the polar mean is `∑ f_k c_k T_k(x) / w(x)`.
* `polarMean_mono`: for a comonotone statistic the polar mean increases in `W` and in `R`.
* `mul_partialDeriv_zero_div`: `x₀ ∂₀w/w = (1 - W) B + W Γ` with `W = x₀²/|x|²`.
* `mul_partialDeriv_one_div`: `x₁ ∂₁w/w = (1 - W)(Γ - B)`.
* `axialTermsMean_mem`: on a cell with positive polar masses, the mean of a comonotone statistic
  lies in `axialTermsMeanBounds`.
* `axialRateBounds_mem`, `transverseRateBounds_mem`: the two rate bounds are sound.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Appendix C.1,
  (C.2)-(C.4).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

namespace CAS.Numerics

open PDE.Analysis
open CAS.Continuum.RationalInterval (roundDownRel roundUpRel roundDownRel_le le_roundUpRel)

/-! ### Terms and cells -/

/-- A term `coeff |x₀|^axial |x|^radial` with rational data. -/
structure AxialTerm where
  /-- The coefficient. -/
  coeff : ℚ
  /-- The exponent of `|x₀|`. -/
  axial : ℚ
  /-- The exponent of `|x|`. -/
  radial : ℚ
deriving DecidableEq

/-- The degree `axial + radial` of a term. -/
def AxialTerm.degree (t : AxialTerm) : ℚ := t.axial + t.radial

/-- The value `coeff |x₀|^axial |x|^radial` of a term. -/
noncomputable def AxialTerm.value (t : AxialTerm) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (t.coeff : ℝ) * axialPower 0 t.axial t.radial x

/-- The weight `∑ coeff |x₀|^axial |x|^radial` of a list of terms. -/
noncomputable def axialTermsValue (ts : List AxialTerm) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (ts.map fun t ↦ t.value x).sum

/-- The weight of a list of terms as an `axialPowerSum` over the positions of the list. -/
theorem axialTermsValue_eq_axialPowerSum (ts : List AxialTerm) :
    axialTermsValue ts = axialPowerSum 0 (fun k : Fin ts.length ↦ (ts[k.1].coeff : ℝ))
      (fun k ↦ (ts[k.1].axial : ℝ)) (fun k ↦ (ts[k.1].radial : ℝ)) := by
  funext x
  rw [axialPowerSum, axialTermsValue]
  exact (Fin.sum_univ_fun_getElem ts (fun t ↦ t.value x)).symm

/-- The rectangle `[left, right] × [bottom, top]` of the closed quadrant. -/
structure PlaneCell where
  /-- The left end `x₀`. -/
  left : ℚ
  /-- The right end `x₁`. -/
  right : ℚ
  /-- The lower end `y₀`. -/
  bottom : ℚ
  /-- The upper end `y₁`. -/
  top : ℚ

/-- The points of the open quadrant in the cell. -/
def PlaneCell.Mem (C : PlaneCell) (x : EuclideanSpace ℝ (Fin 2)) : Prop :=
  0 < x 0 ∧ 0 < x 1 ∧ (C.left : ℝ) ≤ x 0 ∧ x 0 ≤ C.right ∧ (C.bottom : ℝ) ≤ x 1 ∧
    x 1 ≤ C.top

/-- The cell lies in the closed quadrant. -/
def PlaneCell.Valid (C : PlaneCell) : Prop :=
  0 ≤ C.left ∧ 0 ≤ C.bottom

/-- `C.Valid` is decidable. -/
instance (C : PlaneCell) : Decidable C.Valid := inferInstanceAs (Decidable (_ ∧ _))

/-- The lower bound `x₀² + y₀²` of `|x|²` on the cell, rounded down. -/
def PlaneCell.radiusLower (C : PlaneCell) (bits : ℕ) : ℚ :=
  roundDownRel bits (C.left ^ 2 + C.bottom ^ 2)

/-- The upper bound `x₁² + y₁²` of `|x|²` on the cell, rounded up. -/
def PlaneCell.radiusUpper (C : PlaneCell) (bits : ℕ) : ℚ :=
  roundUpRel bits (C.right ^ 2 + C.top ^ 2)

/-- At a point `x` of a valid cell, `|x|²` lies between the rounded corner bounds
`radiusLower ≥ 0` and `radiusUpper`. -/
theorem PlaneCell.radius_mem {C : PlaneCell} (hC : C.Valid) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : C.Mem x) (bits : ℕ) :
    0 ≤ C.radiusLower bits ∧ (C.radiusLower bits : ℝ) ≤ ‖x‖ ^ 2 ∧
      ‖x‖ ^ 2 ≤ C.radiusUpper bits := by
  obtain ⟨h0, h1, ha, hb, hc, hd⟩ := hx
  have ha0 : (0 : ℝ) ≤ C.left := by exact_mod_cast hC.1
  have hc0 : (0 : ℝ) ≤ C.bottom := by exact_mod_cast hC.2
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  refine ⟨div_nonneg (by exact_mod_cast Int.floor_nonneg.2 (by positivity)) (by positivity), ?_,
    ?_⟩
  · have h := (Rat.cast_le (K := ℝ)).2 (roundDownRel_le bits (C.left ^ 2 + C.bottom ^ 2))
    push_cast at h
    have : (C.left : ℝ) ^ 2 + C.bottom ^ 2 ≤ x 0 ^ 2 + x 1 ^ 2 := by nlinarith
    exact h.trans this
  · have h := (Rat.cast_le (K := ℝ)).2 (le_roundUpRel bits (C.right ^ 2 + C.top ^ 2))
    push_cast at h
    have : x 0 ^ 2 + x 1 ^ 2 ≤ (C.right : ℝ) ^ 2 + C.top ^ 2 := by nlinarith
    exact this.trans h

/-! ### Values -/

/-- A lower bound of `v ^ e` for `v ∈ [lo, hi]`, `0 ≤ lo`, `0 < v`. -/
def monoPowLower (lo hi e : ℚ) (bits : ℕ) : ℚ :=
  if 0 ≤ e then (rpowBounds lo e bits).1 else (rpowBounds hi e bits).1

/-- An upper bound of `v ^ e` for `v ∈ [lo, hi]`, `0 ≤ lo`, `0 < v`: `none` when `e < 0` and
`lo = 0`. -/
def monoPowUpper (lo hi e : ℚ) (bits : ℕ) : Option ℚ :=
  if 0 ≤ e then some (rpowBounds hi e bits).2
  else if 0 < lo then some (rpowBounds lo e bits).2 else none

/-- `monoPowLower lo hi e bits ≤ v ^ e` for `0 < v ∈ [lo, hi]` and `0 ≤ lo`. -/
theorem monoPowLower_le {lo hi : ℚ} (hlo : 0 ≤ lo) {v : ℝ} (hv : 0 < v) (hlv : (lo : ℝ) ≤ v)
    (hvh : v ≤ hi) (e : ℚ) (bits : ℕ) : (monoPowLower lo hi e bits : ℝ) ≤ v ^ (e : ℝ) := by
  unfold monoPowLower
  split_ifs with he
  · have he' : (0 : ℝ) ≤ e := by exact_mod_cast he
    exact (rpowBounds_mem hlo e bits).1.trans
      (Real.rpow_le_rpow (by exact_mod_cast hlo) hlv he')
  · have hhi : 0 ≤ hi := by exact_mod_cast hv.le.trans hvh
    have he' : (e : ℝ) ≤ 0 := by exact_mod_cast (not_le.1 he).le
    exact (rpowBounds_mem hhi e bits).1.trans (Real.rpow_le_rpow_of_nonpos hv hvh he')

/-- `v ^ e ≤ u` for `0 < v ∈ [lo, hi]`, `0 ≤ lo` and every value `u` of
`monoPowUpper lo hi e bits`. -/
theorem le_monoPowUpper {lo hi : ℚ} (hlo : 0 ≤ lo) {v : ℝ} (hv : 0 < v) (hlv : (lo : ℝ) ≤ v)
    (hvh : v ≤ hi) (e : ℚ) (bits : ℕ) {u : ℚ} (hu : monoPowUpper lo hi e bits = some u) :
    v ^ (e : ℝ) ≤ u := by
  unfold monoPowUpper at hu
  split_ifs at hu with he hl
  · cases hu
    have hhi : 0 ≤ hi := by exact_mod_cast hv.le.trans hvh
    have he' : (0 : ℝ) ≤ e := by exact_mod_cast he
    exact (Real.rpow_le_rpow hv.le hvh he').trans (rpowBounds_mem hhi e bits).2
  · cases hu
    have he' : (e : ℝ) ≤ 0 := by exact_mod_cast (not_le.1 he).le
    have hl' : (0 : ℝ) < lo := by exact_mod_cast hl
    exact (Real.rpow_le_rpow_of_nonpos hl' hlv he').trans (rpowBounds_mem hlo e bits).2

/-- The lower bound `monoPowLower lo hi e bits` is nonnegative. -/
theorem monoPowLower_nonneg (lo hi e : ℚ) (bits : ℕ) : 0 ≤ monoPowLower lo hi e bits := by
  unfold monoPowLower
  split_ifs <;> exact rpowBounds_fst_nonneg _ _ _

/-- `|x|^b = (|x|²)^(b/2)`. -/
theorem norm_rpow_eq_sq (x : EuclideanSpace ℝ (Fin 2)) (b : ℝ) :
    ‖x‖ ^ b = (‖x‖ ^ 2) ^ (b / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x)]
  congr 1
  push_cast
  ring

/-- The lower bound of a term on a cell. -/
def AxialTerm.lower (t : AxialTerm) (C : PlaneCell) (bits : ℕ) : ℚ :=
  t.coeff * monoPowLower C.left C.right t.axial bits *
    monoPowLower (C.radiusLower bits) (C.radiusUpper bits) (t.radial / 2) bits

/-- The upper bound of a term on a cell. -/
def AxialTerm.upper (t : AxialTerm) (C : PlaneCell) (bits : ℕ) : Option ℚ :=
  match monoPowUpper C.left C.right t.axial bits,
    monoPowUpper (C.radiusLower bits) (C.radiusUpper bits) (t.radial / 2) bits with
  | some u, some v => some (t.coeff * u * v)
  | _, _ => none

/-- The lower bound `∑ lower` of a weight on a cell. -/
def axialTermsLower (ts : List AxialTerm) (C : PlaneCell) (bits : ℕ) : ℚ :=
  (ts.map fun t ↦ t.lower C bits).sum

/-- The upper bound of a weight on a cell, `none` if one term has none. -/
def axialTermsUpper (ts : List AxialTerm) (C : PlaneCell) (bits : ℕ) : Option ℚ :=
  ts.foldr (fun t acc ↦ match t.upper C bits, acc with
    | some u, some v => some (u + v)
    | _, _ => none) (some 0)

/-- The terms have nonnegative coefficients. -/
def AxialTerm.NonnegCoeff (ts : List AxialTerm) : Prop := ∀ t ∈ ts, 0 ≤ t.coeff

/-- `AxialTerm.NonnegCoeff ts` is decidable. -/
instance (ts : List AxialTerm) : Decidable (AxialTerm.NonnegCoeff ts) :=
  inferInstanceAs (Decidable (∀ t ∈ ts, _))

/-- A term with a nonnegative coefficient is at least its lower bound `t.lower C bits` at every
point of a valid cell. -/
theorem AxialTerm.lower_le {t : AxialTerm} (ht : 0 ≤ t.coeff) {C : PlaneCell} (hC : C.Valid)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : C.Mem x) (bits : ℕ) :
    (t.lower C bits : ℝ) ≤ t.value x := by
  have hR := C.radius_mem hC hx bits
  have hn : 0 < ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]; nlinarith [hx.1, hx.2.1]
  have hA := monoPowLower_le hC.1 hx.1 hx.2.2.1 hx.2.2.2.1 t.axial bits
  have hB := monoPowLower_le hR.1 hn hR.2.1 hR.2.2 (t.radial / 2) bits
  have hB0 : (0 : ℝ) ≤
      monoPowLower (C.radiusLower bits) (C.radiusUpper bits) (t.radial / 2) bits := by
    exact_mod_cast monoPowLower_nonneg _ _ _ bits
  have hc : (0 : ℝ) ≤ t.coeff := by exact_mod_cast ht
  unfold AxialTerm.lower AxialTerm.value axialPower
  rw [abs_of_pos hx.1, norm_rpow_eq_sq]
  push_cast at hB ⊢
  have h1 := mul_le_mul hA hB hB0 (Real.rpow_nonneg hx.1.le _)
  calc (t.coeff : ℝ) * (monoPowLower C.left C.right t.axial bits : ℝ) *
        (monoPowLower (C.radiusLower bits) (C.radiusUpper bits) (t.radial / 2) bits : ℝ)
      = (t.coeff : ℝ) * ((monoPowLower C.left C.right t.axial bits : ℝ) *
        (monoPowLower (C.radiusLower bits) (C.radiusUpper bits) (t.radial / 2) bits : ℝ)) := by
        ring
    _ ≤ (t.coeff : ℝ) * (x 0 ^ (t.axial : ℝ) * (‖x‖ ^ 2) ^ ((t.radial : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left h1 hc
    _ = _ := by ring


/-- A term with a nonnegative coefficient is at most every value `u` of its upper bound
`t.upper C bits` at every point of a valid cell. -/
theorem AxialTerm.le_upper {t : AxialTerm} (ht : 0 ≤ t.coeff) {C : PlaneCell} (hC : C.Valid)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : C.Mem x) (bits : ℕ) {u : ℚ}
    (hu : t.upper C bits = some u) : t.value x ≤ u := by
  have hR := C.radius_mem hC hx bits
  have hn : 0 < ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]; nlinarith [hx.1, hx.2.1]
  unfold AxialTerm.upper at hu
  split at hu
  · rename_i a b ha hb
    cases hu
    have hA := le_monoPowUpper hC.1 hx.1 hx.2.2.1 hx.2.2.2.1 t.axial bits ha
    have hB := le_monoPowUpper hR.1 hn hR.2.1 hR.2.2 (t.radial / 2) bits hb
    have hc : (0 : ℝ) ≤ t.coeff := by exact_mod_cast ht
    unfold AxialTerm.value axialPower
    rw [abs_of_pos hx.1, norm_rpow_eq_sq]
    push_cast at hB ⊢
    have h1 := mul_le_mul hA hB (Real.rpow_nonneg hn.le _)
      ((Real.rpow_nonneg hx.1.le _).trans hA)
    calc (t.coeff : ℝ) * (x 0 ^ (t.axial : ℝ) * (‖x‖ ^ 2) ^ ((t.radial : ℝ) / 2))
        ≤ (t.coeff : ℝ) * ((a : ℝ) * b) := mul_le_mul_of_nonneg_left h1 hc
      _ = _ := by ring
  · cases hu

/-- A weight with nonnegative coefficients is at least `axialTermsLower ts C bits` at every point
of a valid cell. -/
theorem axialTermsLower_le {ts : List AxialTerm} (hts : AxialTerm.NonnegCoeff ts)
    {C : PlaneCell} (hC : C.Valid) {x : EuclideanSpace ℝ (Fin 2)} (hx : C.Mem x) (bits : ℕ) :
    (axialTermsLower ts C bits : ℝ) ≤ axialTermsValue ts x := by
  unfold axialTermsLower axialTermsValue
  push_cast
  rw [List.map_map]
  exact List.sum_le_sum fun t ht ↦ AxialTerm.lower_le (hts t ht) hC hx bits

/-- A weight with nonnegative coefficients is at most every value `u` of `axialTermsUpper ts C bits`
at every point of a valid cell. -/
theorem le_axialTermsUpper {ts : List AxialTerm} (hts : AxialTerm.NonnegCoeff ts)
    {C : PlaneCell} (hC : C.Valid) {x : EuclideanSpace ℝ (Fin 2)} (hx : C.Mem x) (bits : ℕ)
    {u : ℚ} (hu : axialTermsUpper ts C bits = some u) : axialTermsValue ts x ≤ u := by
  induction ts generalizing u with
  | nil =>
    simp only [axialTermsUpper, List.foldr_nil, Option.some.injEq] at hu
    simp [axialTermsValue, ← hu]
  | cons t ts ih =>
    simp only [axialTermsUpper, List.foldr_cons] at hu
    split at hu
    · rename_i a b ha hb
      cases hu
      have h1 := AxialTerm.le_upper (hts t List.mem_cons_self) hC hx bits ha
      have h2 := ih (fun t' ht' ↦ hts t' (List.mem_cons_of_mem _ ht')) hb
      simp only [axialTermsValue, List.map_cons, List.sum_cons] at h2 ⊢
      push_cast
      linarith
    · cases hu

/-- Multiplication of a weight by `|x₀|^p |x|^q`: the terms with shifted exponents. -/
def AxialTerm.shift (p q : ℚ) (ts : List AxialTerm) : List AxialTerm :=
  ts.map fun t ↦ ⟨t.coeff, t.axial + p, t.radial + q⟩

/-- For `x₀ > 0` the shifted weight `AxialTerm.shift p q ts` is `|x₀|^p |x|^q` times the weight. -/
theorem axialTermsValue_shift (p q : ℚ) (ts : List AxialTerm) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : 0 < x 0) :
    axialTermsValue (AxialTerm.shift p q ts) x =
      |x 0| ^ (p : ℝ) * ‖x‖ ^ (q : ℝ) * axialTermsValue ts x := by
  have hn : 0 < ‖x‖ := by
    rw [norm_pos_iff]; intro h; simp [h] at hx
  have ha : 0 < |x 0| := abs_pos.2 hx.ne'
  unfold axialTermsValue AxialTerm.shift
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun t _ ↦ ?_
  simp only [Function.comp, AxialTerm.value, axialPower]
  push_cast
  rw [Real.rpow_add ha, Real.rpow_add hn]
  ring

/-- Shifting the exponents keeps the coefficients nonnegative. -/
theorem AxialTerm.NonnegCoeff.shift {ts : List AxialTerm} (h : AxialTerm.NonnegCoeff ts)
    (p q : ℚ) : AxialTerm.NonnegCoeff (AxialTerm.shift p q ts) := by
  intro t ht
  simp only [AxialTerm.shift, List.mem_map] at ht
  obtain ⟨t', ht', rfl⟩ := ht
  exact h t' ht'

/-! ### Means with ordered likelihood ratios -/

/-- **Means under ordered ratios**: if the masses `m ≤ m'` satisfy `m_k m'_l ≤ m'_k m_l` whenever
`f_l < f_k`, the `m`-mean of `f` is at most its `m'`-mean (cross-multiplied form). -/
theorem sum_mul_sum_le_of_cross {ι : Type*} (s : Finset ι) (f m m' : ι → ℝ)
    (h : ∀ i ∈ s, ∀ j ∈ s, f j < f i → m i * m' j ≤ m' i * m j) :
    (∑ i ∈ s, f i * m i) * ∑ j ∈ s, m' j ≤ (∑ i ∈ s, f i * m' i) * ∑ j ∈ s, m j := by
  have key : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ (f i - f j) * (m' i * m j - m i * m' j) := by
    intro i hi j hj
    rcases lt_trichotomy (f j) (f i) with hlt | heq | hgt
    · exact mul_nonneg (by linarith) (by linarith [h i hi j hj hlt])
    · simp [heq]
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [h j hj i hi hgt])
  have hsum : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (f i - f j) * (m' i * m j - m i * m' j) :=
    Finset.sum_nonneg fun i hi ↦ Finset.sum_nonneg fun j hj ↦ key i hi j hj
  have hswap : ∑ i ∈ s, ∑ j ∈ s, (f j * (m i * m' j) - f j * (m' i * m j)) =
      ∑ i ∈ s, ∑ j ∈ s, (f i * m' i * m j - f i * m i * m' j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have hexp : ∑ i ∈ s, ∑ j ∈ s, (f i - f j) * (m' i * m j - m i * m' j) =
      2 * ((∑ i ∈ s, f i * m' i) * ∑ j ∈ s, m j - (∑ i ∈ s, f i * m i) * ∑ j ∈ s, m' j) := by
    have e : ∀ i j, (f i - f j) * (m' i * m j - m i * m' j) =
        (f i * m' i * m j - f i * m i * m' j) + (f j * (m i * m' j) - f j * (m' i * m j)) := by
      intro i j; ring
    simp only [e, Finset.sum_add_distrib, hswap, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    rw [← two_mul]
  nlinarith

/-- The mass `c W^{(a - A)/2} R^{(a + b - G)/2}` of a term at the polar point `(W, R)`, with
normalizing exponents `A ≤ a` and `G ≤ a + b`. -/
noncomputable def AxialTerm.polarMass (t : AxialTerm) (A G : ℚ) (W R : ℝ) : ℝ :=
  (t.coeff : ℝ) * W ^ (((t.axial - A) / 2 : ℚ) : ℝ) * R ^ (((t.degree - G) / 2 : ℚ) : ℝ)

/-- The mean `∑ f m / ∑ m` of the statistic `f` of the terms with the polar masses. -/
noncomputable def polarMean (ts : List AxialTerm) (f : AxialTerm → ℚ) (A G : ℚ) (W R : ℝ) : ℝ :=
  (ts.map fun t ↦ (f t : ℝ) * t.polarMass A G W R).sum / (ts.map fun t ↦ t.polarMass A G W R).sum

/-- The statistic `f` is comonotone with the axial exponents and the degrees of the terms. -/
def IsComonotone (ts : List AxialTerm) (f : AxialTerm → ℚ) : Prop :=
  ∀ t ∈ ts, ∀ l ∈ ts, f l < f t → l.axial ≤ t.axial ∧ l.degree ≤ t.degree

/-- `IsComonotone ts f` is decidable. -/
instance (ts : List AxialTerm) (f : AxialTerm → ℚ) : Decidable (IsComonotone ts f) :=
  inferInstanceAs (Decidable (∀ t ∈ ts, ∀ l ∈ ts, _))

/-- `W^a W'^b ≤ W'^a W^b` for `0 ≤ W ≤ W'` and `0 ≤ b ≤ a`. -/
theorem rpow_mul_rpow_le {W W' a b : ℝ} (hW : 0 ≤ W) (hWW : W ≤ W') (hb : 0 ≤ b) (hba : b ≤ a) :
    W ^ a * W' ^ b ≤ W' ^ a * W ^ b := by
  rcases hW.lt_or_eq with hWp | hW0
  · have hW'p : 0 < W' := hWp.trans_le hWW
    have e1 : W ^ a = W ^ (a - b) * W ^ b := by rw [← Real.rpow_add hWp, sub_add_cancel]
    have e2 : W' ^ a = W' ^ (a - b) * W' ^ b := by rw [← Real.rpow_add hW'p, sub_add_cancel]
    rw [e1, e2]
    have hm := Real.rpow_le_rpow hW hWW (sub_nonneg.2 hba)
    have h1 : 0 ≤ W ^ b := Real.rpow_nonneg hW _
    have h2 : 0 ≤ W' ^ b := Real.rpow_nonneg hW'p.le _
    nlinarith [mul_le_mul_of_nonneg_right hm (mul_nonneg h1 h2)]
  · subst hW0
    rcases hb.lt_or_eq with hbp | hb0
    · rw [Real.zero_rpow (by linarith), Real.zero_rpow hbp.ne']; simp
    · subst hb0
      rcases (show (0 : ℝ) ≤ a by linarith).lt_or_eq with hap | ha0
      · rw [Real.zero_rpow hap.ne']; simp only [Real.rpow_zero, mul_one]
        exact Real.rpow_nonneg (le_trans le_rfl hWW) _
      · subst ha0; simp

/-- The polar mass of a term with a nonnegative coefficient is nonnegative at `W, R ≥ 0`. -/
theorem polarMass_nonneg {t : AxialTerm} (ht : 0 ≤ t.coeff) (A G : ℚ) {W R : ℝ} (hW : 0 ≤ W)
    (hR : 0 ≤ R) : 0 ≤ t.polarMass A G W R := by
  unfold AxialTerm.polarMass
  have : (0 : ℝ) ≤ t.coeff := by exact_mod_cast ht
  have := Real.rpow_nonneg hW (((t.axial - A) / 2 : ℚ) : ℝ)
  have := Real.rpow_nonneg hR (((t.degree - G) / 2 : ℚ) : ℝ)
  positivity

/-- **Monotonicity of the polar means**: for a comonotone statistic and normalizing exponents
below every term, the mean increases from `(W, R)` to `(W', R') ≥ (W, R)`. -/
theorem polarMean_mono {ts : List AxialTerm} (hts : AxialTerm.NonnegCoeff ts)
    {f : AxialTerm → ℚ} (hf : IsComonotone ts f) {A G : ℚ}
    (hA : ∀ t ∈ ts, A ≤ t.axial) (hG : ∀ t ∈ ts, G ≤ t.degree) {W R W' R' : ℝ} (hW : 0 ≤ W)
    (hR : 0 ≤ R) (hWW : W ≤ W') (hRR : R ≤ R')
    (hD : 0 < (ts.map fun t ↦ t.polarMass A G W R).sum)
    (hD' : 0 < (ts.map fun t ↦ t.polarMass A G W' R').sum) :
    polarMean ts f A G W R ≤ polarMean ts f A G W' R' := by
  unfold polarMean
  rw [div_le_div_iff₀ hD hD']
  have hconv := fun (g : AxialTerm → ℝ) ↦ (Fin.sum_univ_fun_getElem ts g).symm
  rw [hconv (fun t ↦ (f t : ℝ) * t.polarMass A G W R), hconv (fun t ↦ t.polarMass A G W' R'),
    hconv (fun t ↦ (f t : ℝ) * t.polarMass A G W' R'), hconv (fun t ↦ t.polarMass A G W R)]
  refine sum_mul_sum_le_of_cross Finset.univ (fun k : Fin ts.length ↦ (f ts[k.1] : ℝ))
    (fun k ↦ ts[k.1].polarMass A G W R) (fun k ↦ ts[k.1].polarMass A G W' R') ?_
  intro i _ j _ hij
  have hmem : ∀ k : Fin ts.length, ts[k.1] ∈ ts := fun k ↦ List.getElem_mem _
  have hij' : f ts[j.1] < f ts[i.1] := by exact_mod_cast hij
  obtain ⟨hax, hdeg⟩ := hf _ (hmem i) _ (hmem j) hij'
  set ti := ts[i.1]
  set tj := ts[j.1]
  have hsi : (0 : ℝ) ≤ (((ti.axial - A) / 2 : ℚ) : ℝ) := by
    have := hA ti (hmem i); push_cast; linarith [(by exact_mod_cast this : (A : ℝ) ≤ ti.axial)]
  have hsj : (0 : ℝ) ≤ (((tj.axial - A) / 2 : ℚ) : ℝ) := by
    have := hA tj (hmem j); push_cast; linarith [(by exact_mod_cast this : (A : ℝ) ≤ tj.axial)]
  have hui : (0 : ℝ) ≤ (((ti.degree - G) / 2 : ℚ) : ℝ) := by
    have := hG ti (hmem i); push_cast; linarith [(by exact_mod_cast this : (G : ℝ) ≤ ti.degree)]
  have huj : (0 : ℝ) ≤ (((tj.degree - G) / 2 : ℚ) : ℝ) := by
    have := hG tj (hmem j); push_cast; linarith [(by exact_mod_cast this : (G : ℝ) ≤ tj.degree)]
  have hsij : (((tj.axial - A) / 2 : ℚ) : ℝ) ≤ (((ti.axial - A) / 2 : ℚ) : ℝ) := by
    push_cast; linarith [(by exact_mod_cast hax : (tj.axial : ℝ) ≤ ti.axial)]
  have huij : (((tj.degree - G) / 2 : ℚ) : ℝ) ≤ (((ti.degree - G) / 2 : ℚ) : ℝ) := by
    push_cast; linarith [(by exact_mod_cast hdeg : (tj.degree : ℝ) ≤ ti.degree)]
  have hW1 := rpow_mul_rpow_le hW hWW hsj hsij
  have hR1 := rpow_mul_rpow_le hR hRR huj huij
  have hci : (0 : ℝ) ≤ ti.coeff := by exact_mod_cast hts ti (hmem i)
  have hcj : (0 : ℝ) ≤ tj.coeff := by exact_mod_cast hts tj (hmem j)
  simp only [AxialTerm.polarMass]
  have hp1 := mul_le_mul hW1 hR1
    (mul_nonneg (Real.rpow_nonneg hR _) (Real.rpow_nonneg (hR.trans hRR) _))
    (mul_nonneg (Real.rpow_nonneg (hW.trans hWW) _) (Real.rpow_nonneg hW _))
  have hcc : (0 : ℝ) ≤ ti.coeff * tj.coeff := mul_nonneg hci hcj
  have := mul_le_mul_of_nonneg_left hp1 hcc
  calc (ti.coeff : ℝ) * W ^ (((ti.axial - A) / 2 : ℚ) : ℝ) *
        R ^ (((ti.degree - G) / 2 : ℚ) : ℝ) *
        ((tj.coeff : ℝ) * W' ^ (((tj.axial - A) / 2 : ℚ) : ℝ) *
          R' ^ (((tj.degree - G) / 2 : ℚ) : ℝ))
      = ti.coeff * tj.coeff * ((W ^ (((ti.axial - A) / 2 : ℚ) : ℝ) *
          W' ^ (((tj.axial - A) / 2 : ℚ) : ℝ)) * (R ^ (((ti.degree - G) / 2 : ℚ) : ℝ) *
          R' ^ (((tj.degree - G) / 2 : ℚ) : ℝ))) := by ring
    _ ≤ ti.coeff * tj.coeff * ((W' ^ (((ti.axial - A) / 2 : ℚ) : ℝ) *
          W ^ (((tj.axial - A) / 2 : ℚ) : ℝ)) * (R' ^ (((ti.degree - G) / 2 : ℚ) : ℝ) *
          R ^ (((tj.degree - G) / 2 : ℚ) : ℝ))) := this
    _ = _ := by ring

/-- At a point of the open quadrant the polar mass is the term times the common factor
`|x₀|^{-A} |x|^{A - G}`. -/
theorem polarMass_eq (t : AxialTerm) (A G : ℚ) {x : EuclideanSpace ℝ (Fin 2)} (hx : 0 < x 0) :
    t.polarMass A G (x 0 ^ 2 / ‖x‖ ^ 2) (‖x‖ ^ 2) =
      t.value x * (x 0 ^ (-(A : ℝ)) * ‖x‖ ^ ((A : ℝ) - G)) := by
  have hn : 0 < ‖x‖ := by rw [norm_pos_iff]; intro h; simp [h] at hx
  unfold AxialTerm.polarMass AxialTerm.value axialPower AxialTerm.degree
  rw [abs_of_pos hx, Real.div_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul hx.le 2,
    ← Real.rpow_natCast_mul hn.le 2, ← Real.rpow_natCast_mul hn.le 2]
  push_cast
  rw [div_eq_mul_inv, ← Real.rpow_neg hn.le]
  have e1 : x 0 ^ (2 * (((t.axial : ℝ) - A) / 2)) = x 0 ^ (t.axial : ℝ) * x 0 ^ (-(A : ℝ)) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have e2 : ‖x‖ ^ (-(2 * (((t.axial : ℝ) - A) / 2))) * ‖x‖ ^ (2 * (((t.axial : ℝ) +
      t.radial - G) / 2)) = ‖x‖ ^ (t.radial : ℝ) * ‖x‖ ^ ((A : ℝ) - G) := by
    rw [← Real.rpow_add hn, ← Real.rpow_add hn]; congr 1; ring
  rw [e1]
  calc (t.coeff : ℝ) * (x 0 ^ (t.axial : ℝ) * x 0 ^ (-(A : ℝ)) *
        ‖x‖ ^ (-(2 * (((t.axial : ℝ) - A) / 2)))) * ‖x‖ ^ (2 * (((t.axial : ℝ) + t.radial - G) / 2))
      = (t.coeff : ℝ) * x 0 ^ (t.axial : ℝ) * x 0 ^ (-(A : ℝ)) *
        (‖x‖ ^ (-(2 * (((t.axial : ℝ) - A) / 2))) *
          ‖x‖ ^ (2 * (((t.axial : ℝ) + t.radial - G) / 2))) := by ring
    _ = _ := by rw [e2]; ring

/-- **The polar mean at a point** is the mean of the statistic over the terms of the weight. -/
theorem polarMean_eq (ts : List AxialTerm) (f : AxialTerm → ℚ) (A G : ℚ)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : 0 < x 0) :
    polarMean ts f A G (x 0 ^ 2 / ‖x‖ ^ 2) (‖x‖ ^ 2) =
      (ts.map fun t ↦ (f t : ℝ) * t.value x).sum / axialTermsValue ts x := by
  have hn : 0 < ‖x‖ := by rw [norm_pos_iff]; intro h; simp [h] at hx
  have hK : 0 < x 0 ^ (-(A : ℝ)) * ‖x‖ ^ ((A : ℝ) - G) := by positivity
  set K := x 0 ^ (-(A : ℝ)) * ‖x‖ ^ ((A : ℝ) - G)
  have hN : (ts.map fun t ↦ (f t : ℝ) * t.polarMass A G (x 0 ^ 2 / ‖x‖ ^ 2) (‖x‖ ^ 2)).sum =
      (ts.map fun t ↦ (f t : ℝ) * t.value x).sum * K := by
    rw [← List.sum_map_mul_right]
    congr 1
    refine List.map_congr_left fun t _ ↦ ?_
    rw [polarMass_eq _ A G hx]; ring
  have hD : (ts.map fun t ↦ t.polarMass A G (x 0 ^ 2 / ‖x‖ ^ 2) (‖x‖ ^ 2)).sum =
      (ts.map fun t ↦ t.value x).sum * K := by
    rw [← List.sum_map_mul_right]
    congr 1
    refine List.map_congr_left fun t _ ↦ ?_
    rw [polarMass_eq _ A G hx]
  unfold polarMean axialTermsValue
  rw [hN, hD, mul_div_mul_right _ _ hK.ne']

/-- The polar masses are positive at an interior point once their sum is positive at some point. -/
theorem polarMass_sum_pos {ts : List AxialTerm} (hts : AxialTerm.NonnegCoeff ts) {A G : ℚ}
    {W R W' R' : ℝ} (hD : 0 < (ts.map fun t ↦ t.polarMass A G W R).sum) (hW' : 0 < W')
    (hR' : 0 < R') : 0 < (ts.map fun t ↦ t.polarMass A G W' R').sum := by
  obtain ⟨t, ht, hpos⟩ : ∃ t ∈ ts, t.polarMass A G W R ≠ 0 := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have : (ts.map fun t ↦ t.polarMass A G W R).sum = 0 :=
      List.sum_eq_zero fun y hy ↦ by
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hy
        exact h t ht
    linarith
  have hc : t.coeff ≠ 0 := by
    intro h0; apply hpos; simp [AxialTerm.polarMass, h0]
  have hc' : (0 : ℝ) < t.coeff := by exact_mod_cast lt_of_le_of_ne (hts t ht) (Ne.symm hc)
  have ht' : 0 < t.polarMass A G W' R' := by
    unfold AxialTerm.polarMass
    have := Real.rpow_pos_of_pos hW' (((t.axial - A) / 2 : ℚ) : ℝ)
    have := Real.rpow_pos_of_pos hR' (((t.degree - G) / 2 : ℚ) : ℝ)
    positivity
  refine lt_of_lt_of_le ht' ?_
  exact List.single_le_sum (fun y hy ↦ by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hy
    exact polarMass_nonneg (hts t ht) A G hW'.le hR'.le) _ (List.mem_map_of_mem ht)

/-! ### Enclosures of the means at rational points -/

/-- Lower and upper bounds of the mass of a term at the rational point `(W, R)`. -/
def AxialTerm.massBounds (t : AxialTerm) (A G W R : ℚ) (bits : ℕ) : ℚ × ℚ :=
  let a := rpowBounds W ((t.axial - A) / 2) bits
  let b := rpowBounds R ((t.degree - G) / 2) bits
  (t.coeff * a.1 * b.1, t.coeff * a.2 * b.2)

/-- The terms with the bounds of their masses at `(W, R)`, computed once for all statistics. -/
def massList (ts : List AxialTerm) (A G W R : ℚ) (bits : ℕ) : List (AxialTerm × ℚ × ℚ) :=
  ts.map fun t ↦ (t, t.massBounds A G W R bits)

/-- The lower bound of `∑ f m`, with the mass bound chosen by the sign of `f`. -/
def momentLower (ms : List (AxialTerm × ℚ × ℚ)) (f : AxialTerm → ℚ) : ℚ :=
  (ms.map fun p ↦ if 0 ≤ f p.1 then f p.1 * p.2.1 else f p.1 * p.2.2).sum

/-- The upper bound of `∑ f m`, with the mass bound chosen by the sign of `f`. -/
def momentUpper (ms : List (AxialTerm × ℚ × ℚ)) (f : AxialTerm → ℚ) : ℚ :=
  (ms.map fun p ↦ if 0 ≤ f p.1 then f p.1 * p.2.2 else f p.1 * p.2.1).sum

/-- The lower bound of the total mass. -/
def totalLower (ms : List (AxialTerm × ℚ × ℚ)) : ℚ := (ms.map fun p ↦ p.2.1).sum

/-- The upper bound of the total mass. -/
def totalUpper (ms : List (AxialTerm × ℚ × ℚ)) : ℚ := (ms.map fun p ↦ p.2.2).sum

/-- The bounds `N₋ / D` and `N₊ / D` of a mean from the mass bounds. -/
def meanBoundsOf (ms : List (AxialTerm × ℚ × ℚ)) (f : AxialTerm → ℚ) : ℚ × ℚ :=
  let Nlo := momentLower ms f
  let Nhi := momentUpper ms f
  let Dlo := totalLower ms
  let Dhi := totalUpper ms
  (Nlo / (if 0 ≤ Nlo then Dhi else Dlo), Nhi / (if 0 ≤ Nhi then Dlo else Dhi))

/-- The lower bound of the total mass at `(W, R)`. -/
def massTotalLower (ts : List AxialTerm) (A G W R : ℚ) (bits : ℕ) : ℚ :=
  totalLower (massList ts A G W R bits)

/-- The bounds of the polar mean at `(W, R)`, valid when the lower bound of the total mass is
positive. -/
def polarMeanBounds (ts : List AxialTerm) (f : AxialTerm → ℚ) (A G W R : ℚ) (bits : ℕ) :
    ℚ × ℚ :=
  meanBoundsOf (massList ts A G W R bits) f

/-- For `W, R ≥ 0` and a nonnegative coefficient, `t.massBounds A G W R bits` encloses the polar
mass `t.polarMass A G W R`. -/
theorem AxialTerm.mass_mem {t : AxialTerm} (ht : 0 ≤ t.coeff) {A G W R : ℚ} (hW : 0 ≤ W)
    (hR : 0 ≤ R) (bits : ℕ) :
    ((t.massBounds A G W R bits).1 : ℝ) ≤ t.polarMass A G W R ∧
      t.polarMass A G W R ≤ (t.massBounds A G W R bits).2 := by
  have h1 := rpowBounds_mem hW ((t.axial - A) / 2) bits
  have h2 := rpowBounds_mem hR ((t.degree - G) / 2) bits
  have h10 : (0 : ℝ) ≤ (rpowBounds W ((t.axial - A) / 2) bits).1 := by
    exact_mod_cast rpowBounds_fst_nonneg _ _ _
  have h20 : (0 : ℝ) ≤ (rpowBounds R ((t.degree - G) / 2) bits).1 := by
    exact_mod_cast rpowBounds_fst_nonneg _ _ _
  have hc : (0 : ℝ) ≤ t.coeff := by exact_mod_cast ht
  unfold AxialTerm.massBounds AxialTerm.polarMass
  simp only [Rat.cast_mul]
  constructor
  · rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1.1 h2.1 h20 (h10.trans h1.1)) hc
  · rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1.2 h2.2 (h20.trans h2.1)
      ((h10.trans h1.1).trans h1.2)) hc

/-- The enclosure of `R ^ 0` is exactly `(1, 1)`. -/
theorem rpowBounds_zero (R : ℚ) (bits : ℕ) : rpowBounds R 0 bits = (1, 1) := by
  simp [rpowBounds]

/-- The lower mass bound of a term with a nonnegative coefficient is nonnegative. -/
theorem AxialTerm.massBounds_fst_nonneg {t : AxialTerm} (ht : 0 ≤ t.coeff) (A G W R : ℚ)
    (bits : ℕ) : 0 ≤ (t.massBounds A G W R bits).1 := by
  unfold AxialTerm.massBounds
  exact mul_nonneg (mul_nonneg ht (rpowBounds_fst_nonneg _ _ _)) (rpowBounds_fst_nonneg _ _ _)

/-- The lower bound of the total mass is positive when a term with a positive coefficient attains
both normalizing exponents: its mass is its coefficient. -/
theorem totalLower_massList_pos {ts : List AxialTerm} (hts : AxialTerm.NonnegCoeff ts) {A G : ℚ}
    (hmin : ∃ t ∈ ts, 0 < t.coeff ∧ t.axial = A ∧ t.degree = G) (W R : ℚ) (bits : ℕ) :
    0 < totalLower (massList ts A G W R bits) := by
  obtain ⟨t, ht, hc, ha, hg⟩ := hmin
  have hval : (t.massBounds A G W R bits).1 = t.coeff := by
    simp [AxialTerm.massBounds, ha, hg, rpowBounds_zero]
  unfold totalLower massList
  rw [List.map_map]
  refine lt_of_lt_of_le (hval ▸ hc) ?_
  exact List.single_le_sum (fun y hy ↦ by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hy
    exact AxialTerm.massBounds_fst_nonneg (hts s hs) A G W R bits) _
    (List.mem_map_of_mem (f := fun s ↦ (s.massBounds A G W R bits).1) ht)

/-- Bounds of `N / D` from `N ∈ [Nlo, Nhi]` and `D ∈ [Dlo, Dhi]` with `Dlo > 0`: each end of `N` is
divided by the end of `D` that is extreme for its sign. -/
theorem div_mem_of_bounds {N D Nlo Nhi Dlo Dhi : ℝ} (hDlo : 0 < Dlo) (hN : Nlo ≤ N ∧ N ≤ Nhi)
    (hD : Dlo ≤ D ∧ D ≤ Dhi) :
    Nlo / (if 0 ≤ Nlo then Dhi else Dlo) ≤ N / D ∧
      N / D ≤ Nhi / (if 0 ≤ Nhi then Dlo else Dhi) := by
  have hDp : 0 < D := hDlo.trans_le hD.1
  have hDhi : 0 < Dhi := hDp.trans_le hD.2
  constructor
  · split_ifs with h
    · calc Nlo / Dhi ≤ Nlo / D := div_le_div_of_nonneg_left h hDp hD.2
        _ ≤ N / D := div_le_div_of_nonneg_right hN.1 hDp.le
    · calc Nlo / Dlo ≤ Nlo / D := by
            rw [div_le_div_iff₀ hDlo hDp]; nlinarith [hD.1, (not_le.1 h)]
        _ ≤ N / D := div_le_div_of_nonneg_right hN.1 hDp.le
  · split_ifs with h
    · calc N / D ≤ Nhi / D := div_le_div_of_nonneg_right hN.2 hDp.le
        _ ≤ Nhi / Dlo := div_le_div_of_nonneg_left h hDlo hD.1
    · calc N / D ≤ Nhi / D := div_le_div_of_nonneg_right hN.2 hDp.le
        _ ≤ Nhi / Dhi := by
            rw [div_le_div_iff₀ hDp hDhi]; nlinarith [hD.2, (not_le.1 h)]

/-- **Enclosure of a mean from mass bounds**: if every term `p.1` of the list carries bounds
`p.2.1 ≤ m(p.1) ≤ p.2.2` of a mass `m` and the lower bounds have a positive sum, the mean
`∑ f m / ∑ m` lies in `meanBoundsOf`. -/
theorem meanBoundsOf_mem {ms : List (AxialTerm × ℚ × ℚ)} (m : AxialTerm → ℝ)
    (hm : ∀ p ∈ ms, (p.2.1 : ℝ) ≤ m p.1 ∧ m p.1 ≤ p.2.2) (hD : 0 < totalLower ms)
    (f : AxialTerm → ℚ) :
    0 < (ms.map fun p ↦ m p.1).sum ∧
      ((meanBoundsOf ms f).1 : ℝ) ≤
        (ms.map fun p ↦ (f p.1 : ℝ) * m p.1).sum / (ms.map fun p ↦ m p.1).sum ∧
      (ms.map fun p ↦ (f p.1 : ℝ) * m p.1).sum / (ms.map fun p ↦ m p.1).sum ≤
        (meanBoundsOf ms f).2 := by
  have hDlo : (totalLower ms : ℝ) ≤ (ms.map fun p ↦ m p.1).sum := by
    unfold totalLower; push_cast; rw [List.map_map]
    exact List.sum_le_sum fun p hp ↦ (hm p hp).1
  have hDhi : (ms.map fun p ↦ m p.1).sum ≤ (totalUpper ms : ℝ) := by
    unfold totalUpper; push_cast; rw [List.map_map]
    exact List.sum_le_sum fun p hp ↦ (hm p hp).2
  have hNlo : (momentLower ms f : ℝ) ≤ (ms.map fun p ↦ (f p.1 : ℝ) * m p.1).sum := by
    unfold momentLower; push_cast; rw [List.map_map]
    refine List.sum_le_sum fun p hp ↦ ?_
    simp only [Function.comp]
    split_ifs with hf
    · push_cast; exact mul_le_mul_of_nonneg_left (hm p hp).1 (by exact_mod_cast hf)
    · push_cast
      exact mul_le_mul_of_nonpos_left (hm p hp).2 (by exact_mod_cast (not_le.1 hf).le)
  have hNhi : (ms.map fun p ↦ (f p.1 : ℝ) * m p.1).sum ≤ (momentUpper ms f : ℝ) := by
    unfold momentUpper; push_cast; rw [List.map_map]
    refine List.sum_le_sum fun p hp ↦ ?_
    simp only [Function.comp]
    split_ifs with hf
    · push_cast; exact mul_le_mul_of_nonneg_left (hm p hp).2 (by exact_mod_cast hf)
    · push_cast
      exact mul_le_mul_of_nonpos_left (hm p hp).1 (by exact_mod_cast (not_le.1 hf).le)
  have hD' : (0 : ℝ) < totalLower ms := by exact_mod_cast hD
  refine ⟨hD'.trans_le hDlo, ?_⟩
  have h := div_mem_of_bounds hD' ⟨hNlo, hNhi⟩ ⟨hDlo, hDhi⟩
  unfold meanBoundsOf
  simp only
  push_cast
  simpa [apply_ite (fun q : ℚ ↦ (q : ℝ)), Rat.cast_nonneg] using h

/-- **Enclosure of the polar mean** at a rational point with a positive lower mass bound. -/
theorem polarMeanBounds_mem {ts : List AxialTerm} (hts : AxialTerm.NonnegCoeff ts)
    (f : AxialTerm → ℚ) (A G : ℚ) {W R : ℚ} (hW : 0 ≤ W) (hR : 0 ≤ R) (bits : ℕ)
    (hD : 0 < massTotalLower ts A G W R bits) :
    0 < (ts.map fun t ↦ t.polarMass A G W R).sum ∧
      ((polarMeanBounds ts f A G W R bits).1 : ℝ) ≤ polarMean ts f A G W R ∧
      polarMean ts f A G W R ≤ (polarMeanBounds ts f A G W R bits).2 := by
  have h := meanBoundsOf_mem (ms := massList ts A G W R bits)
    (fun t ↦ t.polarMass A G (W : ℝ) (R : ℝ)) (by
      intro p hp
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hp
      exact AxialTerm.mass_mem (hts t ht) hW hR bits) hD f
  simp only [massList, List.map_map, Function.comp_def] at h
  exact h

/-! ### Log-derivatives -/

/-- The coordinate derivatives of a sum of axial-radial powers are the sums of the derivatives of
the terms. -/
theorem partialDeriv_axialPowerSum {ι : Type*} [Fintype ι] (c a b : ι → ℝ) (i : Fin 2)
    {x : EuclideanSpace ℝ (Fin 2)} (h0 : x 0 ≠ 0) :
    (∂[i] (axialPowerSum 0 c a b)) x = ∑ k, c k * (∂[i] (axialPower 0 (a k) (b k))) x := by
  change fderiv ℝ (axialPowerSum 0 c a b) x (EuclideanSpace.single i 1) = _
  rw [(hasFDerivAt_axialPowerSum 0 c a b h0).fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  rfl

/-- `x_i ∂_i w = ∑ c (a [i = 0] + b x_i²/|x|²) T` for a list of terms, at a point with `x₀ ≠ 0`. -/
theorem mul_partialDeriv_axialTermsValue (ts : List AxialTerm) (i : Fin 2)
    {x : EuclideanSpace ℝ (Fin 2)} (h0 : x 0 ≠ 0) :
    x i * (∂[i] (axialTermsValue ts)) x =
      (ts.map fun t ↦ ((if i = 0 then (t.axial : ℝ) else 0) +
        t.radial * (x i ^ 2 / ‖x‖ ^ 2)) * t.value x).sum := by
  rw [axialTermsValue_eq_axialPowerSum, partialDeriv_axialPowerSum _ _ _ i h0, Finset.mul_sum]
  rw [← Fin.sum_univ_fun_getElem ts (fun t ↦ ((if i = 0 then (t.axial : ℝ) else 0) +
    t.radial * (x i ^ 2 / ‖x‖ ^ 2)) * t.value x)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [mul_left_comm, mul_partialDeriv_axialPower 0 i _ _ h0]
  simp only [AxialTerm.value]
  by_cases hi : i = 0
  · subst hi; simp; ring
  · simp [hi]; ring

/-- The mean degree `Γ = x·∇w/w` and the mean axial exponent `B` of the terms at a point. -/
noncomputable def axialTermsMean (ts : List AxialTerm) (f : AxialTerm → ℚ)
    (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (ts.map fun t ↦ (f t : ℝ) * t.value x).sum / axialTermsValue ts x

/-- `|x|² > 0` when `x₀ > 0`. -/
theorem norm_sq_pos_of_pos {x : EuclideanSpace ℝ (Fin 2)} (hx : 0 < x 0) : 0 < ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]; nlinarith

/-- A list sum of a combination of two functions. -/
theorem list_sum_map_add_mul {ι : Type*} (l : List ι) (g h : ι → ℝ) (a b : ℝ) :
    (l.map fun i ↦ a * g i + b * h i).sum = a * (l.map g).sum + b * (l.map h).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- `x₀ ∂₀w/w = (1 - W) B + W Γ` with `W = x₀²/|x|²`. -/
theorem mul_partialDeriv_zero_div (ts : List AxialTerm) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : 0 < x 0) :
    x 0 * (∂[0] (axialTermsValue ts)) x / axialTermsValue ts x =
      (1 - x 0 ^ 2 / ‖x‖ ^ 2) * axialTermsMean ts AxialTerm.axial x +
        x 0 ^ 2 / ‖x‖ ^ 2 * axialTermsMean ts AxialTerm.degree x := by
  rw [mul_partialDeriv_axialTermsValue ts 0 hx.ne']
  unfold axialTermsMean
  set W := x 0 ^ 2 / ‖x‖ ^ 2
  have hnum : (ts.map fun t ↦ ((if (0 : Fin 2) = 0 then (t.axial : ℝ) else 0) +
      t.radial * W) * t.value x).sum = (1 - W) * (ts.map fun t ↦ (t.axial : ℝ) * t.value x).sum +
        W * (ts.map fun t ↦ ((t.degree : ℚ) : ℝ) * t.value x).sum := by
    rw [← list_sum_map_add_mul]
    congr 1
    refine List.map_congr_left fun t _ ↦ ?_
    simp only [↓reduceIte, AxialTerm.degree]
    push_cast
    ring
  rw [hnum]
  ring

/-- `x₁ ∂₁w/w = (1 - W)(Γ - B)` with `W = x₀²/|x|²`. -/
theorem mul_partialDeriv_one_div (ts : List AxialTerm) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : 0 < x 0) :
    x 1 * (∂[1] (axialTermsValue ts)) x / axialTermsValue ts x =
      (1 - x 0 ^ 2 / ‖x‖ ^ 2) *
        (axialTermsMean ts AxialTerm.degree x - axialTermsMean ts AxialTerm.axial x) := by
  have hn := norm_sq_pos_of_pos hx
  have hW : x 1 ^ 2 / ‖x‖ ^ 2 = 1 - x 0 ^ 2 / ‖x‖ ^ 2 := by
    rw [eq_sub_iff_add_eq, ← add_div, add_comm, ← Fin.sum_univ_two (fun i ↦ x i ^ 2),
      ← EuclideanSpace.real_norm_sq_eq, div_self hn.ne']
  rw [mul_partialDeriv_axialTermsValue ts 1 hx.ne', hW]
  unfold axialTermsMean
  set W := x 0 ^ 2 / ‖x‖ ^ 2
  have hnum : (ts.map fun t ↦ ((if (1 : Fin 2) = 0 then (t.axial : ℝ) else 0) +
      t.radial * (1 - W)) * t.value x).sum =
        (1 - W) * (ts.map fun t ↦ ((t.degree : ℚ) : ℝ) * t.value x).sum +
          (-(1 - W)) * (ts.map fun t ↦ (t.axial : ℝ) * t.value x).sum := by
    rw [← list_sum_map_add_mul]
    congr 1
    refine List.map_congr_left fun t _ ↦ ?_
    simp only [one_ne_zero, ↓reduceIte, AxialTerm.degree]
    push_cast
    ring
  rw [hnum]
  ring

/-- Euler's identity: `x·∇w/w = Γ`. -/
theorem mul_partialDeriv_add_div (ts : List AxialTerm) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : 0 < x 0) :
    (x 0 * (∂[0] (axialTermsValue ts)) x + x 1 * (∂[1] (axialTermsValue ts)) x) /
        axialTermsValue ts x = axialTermsMean ts AxialTerm.degree x := by
  rw [add_div, mul_partialDeriv_zero_div ts hx, mul_partialDeriv_one_div ts hx]
  ring


/-! ### Means and rates on cells -/

/-- The lower polar direction `W₋ = x₀²/(x₀² + y₁²)` of the cell. -/
def PlaneCell.directionLower (C : PlaneCell) : ℚ :=
  C.left ^ 2 / (C.left ^ 2 + C.top ^ 2)

/-- The upper polar direction `W₊ = x₁²/(x₁² + y₀²)` of the cell. -/
def PlaneCell.directionUpper (C : PlaneCell) : ℚ :=
  C.right ^ 2 / (C.right ^ 2 + C.bottom ^ 2)

/-- At a point of a valid cell the polar direction `W = x₀²/|x|²` lies between
`directionLower ≥ 0` and `directionUpper ≤ 1`. -/
theorem PlaneCell.direction_mem {C : PlaneCell} (hC : C.Valid) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : C.Mem x) :
    0 ≤ C.directionLower ∧ (C.directionLower : ℝ) ≤ x 0 ^ 2 / ‖x‖ ^ 2 ∧
      x 0 ^ 2 / ‖x‖ ^ 2 ≤ C.directionUpper ∧ C.directionUpper ≤ 1 := by
  obtain ⟨h0, h1, ha, hb, hc, hd⟩ := hx
  have ha0 : (0 : ℝ) ≤ C.left := by exact_mod_cast hC.1
  have hc0 : (0 : ℝ) ≤ C.bottom := by exact_mod_cast hC.2
  have hn : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hnp : 0 < x 0 ^ 2 + x 1 ^ 2 := by positivity
  have hb0 : (0 : ℝ) < C.right := h0.trans_le hb
  have hD : (0 : ℝ) < C.right ^ 2 + C.bottom ^ 2 := by positivity
  refine ⟨by unfold PlaneCell.directionLower; positivity, ?_, ?_, ?_⟩
  · unfold PlaneCell.directionLower
    push_cast
    rw [hn]
    rcases (show (0 : ℝ) ≤ C.left ^ 2 + C.top ^ 2 by positivity).lt_or_eq with hp | hz
    · rw [div_le_div_iff₀ hp hnp]
      have h1' : x 1 ^ 2 ≤ (C.top : ℝ) ^ 2 := pow_le_pow_left₀ h1.le hd 2
      have h0' : (C.left : ℝ) ^ 2 ≤ x 0 ^ 2 := pow_le_pow_left₀ ha0 ha 2
      nlinarith [mul_le_mul h0' h1' (sq_nonneg _) (sq_nonneg _)]
    · rw [← hz, div_zero]; positivity
  · unfold PlaneCell.directionUpper
    push_cast
    rw [hn, div_le_div_iff₀ hnp hD]
    have h1' : (C.bottom : ℝ) ^ 2 ≤ x 1 ^ 2 := pow_le_pow_left₀ hc0 hc 2
    have h0' : x 0 ^ 2 ≤ (C.right : ℝ) ^ 2 := pow_le_pow_left₀ h0.le hb 2
    nlinarith [mul_le_mul h0' h1' (sq_nonneg _) (sq_nonneg _)]
  · unfold PlaneCell.directionUpper
    have hbq : (0 : ℚ) < C.right := by exact_mod_cast hb0
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg C.bottom]

/-- The bounds of the mean of `f` on the cell: the lower bound at the polar corner `(W₋, R₋)` and
the upper bound at `(W₊, R₊)`. -/
def axialTermsMeanBounds (ts : List AxialTerm) (f : AxialTerm → ℚ) (A G : ℚ) (C : PlaneCell)
    (bits : ℕ) : ℚ × ℚ :=
  ((polarMeanBounds ts f A G C.directionLower (C.radiusLower bits) bits).1,
    (polarMeanBounds ts f A G C.directionUpper (C.radiusUpper bits) bits).2)

/-- The check that both corner masses are bounded below by a positive number. -/
def axialTermsMeanValid (ts : List AxialTerm) (A G : ℚ) (C : PlaneCell) (bits : ℕ) : Bool :=
  decide (0 < massTotalLower ts A G C.directionLower (C.radiusLower bits) bits) &&
    decide (0 < massTotalLower ts A G C.directionUpper (C.radiusUpper bits) bits)

/-- **The mean of a comonotone statistic on a cell** lies between its enclosures at the polar
corners. -/
theorem axialTermsMean_mem {ts : List AxialTerm} (hts : AxialTerm.NonnegCoeff ts)
    {f : AxialTerm → ℚ} (hf : IsComonotone ts f) {A G : ℚ} (hA : ∀ t ∈ ts, A ≤ t.axial)
    (hG : ∀ t ∈ ts, G ≤ t.degree) {C : PlaneCell} (hC : C.Valid) {bits : ℕ}
    (hv : axialTermsMeanValid ts A G C bits = true) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : C.Mem x) :
    ((axialTermsMeanBounds ts f A G C bits).1 : ℝ) ≤ axialTermsMean ts f x ∧
      axialTermsMean ts f x ≤ (axialTermsMeanBounds ts f A G C bits).2 := by
  simp only [axialTermsMeanValid, Bool.and_eq_true, decide_eq_true_eq] at hv
  have hR := C.radius_mem hC hx bits
  have hW := C.direction_mem hC hx
  have hRU : 0 ≤ C.radiusUpper bits := by
    have : (0 : ℝ) ≤ C.radiusUpper bits := (sq_nonneg _).trans hR.2.2
    exact_mod_cast this
  have hWU : 0 ≤ C.directionUpper := by
    have : (0 : ℝ) ≤ C.directionUpper := (div_nonneg (sq_nonneg _) (sq_nonneg _)).trans hW.2.2.1
    exact_mod_cast this
  have hlo := polarMeanBounds_mem hts f A G hW.1 hR.1 bits hv.1
  have hhi := polarMeanBounds_mem hts f A G hWU hRU bits hv.2
  have hxW : 0 < x 0 ^ 2 / ‖x‖ ^ 2 := div_pos (by nlinarith [hx.1]) (norm_sq_pos_of_pos hx.1)
  have hxR : 0 < ‖x‖ ^ 2 := norm_sq_pos_of_pos hx.1
  have hDx := polarMass_sum_pos hts hlo.1 hxW hxR
  rw [axialTermsMean, ← polarMean_eq ts f A G hx.1]
  constructor
  · refine hlo.2.1.trans (polarMean_mono hts hf hA hG (by exact_mod_cast hW.1)
      (by exact_mod_cast hR.1) hW.2.1 hR.2.1 hlo.1 hDx)
  · refine (polarMean_mono hts hf hA hG hxW.le hxR.le hW.2.2.1 hR.2.2 hDx hhi.1).trans hhi.2.2

/-- `min (f w₀) (f w₁) ≤ f w ≤ max (f w₀) (f w₁)` for an affine `f` and `w ∈ [w₀, w₁]`. -/
theorem affine_mem_minmax {p q w₀ w₁ w : ℝ} (h₀ : w₀ ≤ w) (h₁ : w ≤ w₁) :
    min (p + q * w₀) (p + q * w₁) ≤ p + q * w ∧ p + q * w ≤ max (p + q * w₀) (p + q * w₁) := by
  rcases le_total 0 q with hq | hq
  · exact ⟨(min_le_left _ _).trans (by nlinarith), le_trans (by nlinarith) (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (by nlinarith), le_trans (by nlinarith) (le_max_left _ _)⟩

/-- The bounds of `x₀ ∂₀w/w = (1 - W) B + W Γ` on a cell from the ranges `B ∈ [b₀, b₁]`,
`Γ ∈ [g₀, g₁]` and `W ∈ [w₀, w₁] ⊂ [0, 1]`. -/
def axialRateBounds (b g : ℚ × ℚ) (w₀ w₁ : ℚ) : ℚ × ℚ :=
  (min (b.1 + (g.1 - b.1) * w₀) (b.1 + (g.1 - b.1) * w₁),
    max (b.2 + (g.2 - b.2) * w₀) (b.2 + (g.2 - b.2) * w₁))

/-- The bounds of `x₁ ∂₁w/w = (1 - W)(Γ - B)` on a cell. -/
def transverseRateBounds (b g : ℚ × ℚ) (w₀ w₁ : ℚ) : ℚ × ℚ :=
  (min ((1 - w₀) * (g.1 - b.2)) ((1 - w₁) * (g.1 - b.2)),
    max ((1 - w₀) * (g.2 - b.1)) ((1 - w₁) * (g.2 - b.1)))

/-- `axialRateBounds b g w₀ w₁` encloses `(1 - W) B + W Γ` for `B ∈ [b₀, b₁]`, `Γ ∈ [g₀, g₁]` and
`W ∈ [w₀, w₁] ⊂ [0, 1]`. -/
theorem axialRateBounds_mem {b g : ℚ × ℚ} {w₀ w₁ : ℚ} {B Γ W : ℝ} (hB : (b.1 : ℝ) ≤ B ∧ B ≤ b.2)
    (hΓ : (g.1 : ℝ) ≤ Γ ∧ Γ ≤ g.2) (hW₀ : (w₀ : ℝ) ≤ W) (hW₁ : W ≤ w₁) (hW : 0 ≤ W)
    (hW1 : W ≤ 1) :
    ((axialRateBounds b g w₀ w₁).1 : ℝ) ≤ (1 - W) * B + W * Γ ∧
      (1 - W) * B + W * Γ ≤ (axialRateBounds b g w₀ w₁).2 := by
  have hl := (affine_mem_minmax (p := (b.1 : ℝ)) (q := (g.1 : ℝ) - b.1) hW₀ hW₁).1
  have hu := (affine_mem_minmax (p := (b.2 : ℝ)) (q := (g.2 : ℝ) - b.2) hW₀ hW₁).2
  unfold axialRateBounds
  push_cast
  constructor
  · refine hl.trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hB.1 (sub_nonneg.2 hW1), mul_le_mul_of_nonneg_left hΓ.1 hW]
  · refine le_trans ?_ hu
    nlinarith [mul_le_mul_of_nonneg_left hB.2 (sub_nonneg.2 hW1), mul_le_mul_of_nonneg_left hΓ.2 hW]

/-- `transverseRateBounds b g w₀ w₁` encloses `(1 - W)(Γ - B)` for `B ∈ [b₀, b₁]`, `Γ ∈ [g₀, g₁]`
and `w₀ ≤ W ≤ w₁`, `W ≤ 1`. -/
theorem transverseRateBounds_mem {b g : ℚ × ℚ} {w₀ w₁ : ℚ} {B Γ W : ℝ}
    (hB : (b.1 : ℝ) ≤ B ∧ B ≤ b.2) (hΓ : (g.1 : ℝ) ≤ Γ ∧ Γ ≤ g.2) (hW₀ : (w₀ : ℝ) ≤ W)
    (hW₁ : W ≤ w₁) (hW1 : W ≤ 1) :
    ((transverseRateBounds b g w₀ w₁).1 : ℝ) ≤ (1 - W) * (Γ - B) ∧
      (1 - W) * (Γ - B) ≤ (transverseRateBounds b g w₀ w₁).2 := by
  set d₀ : ℝ := (g.1 : ℝ) - b.2
  set d₁ : ℝ := (g.2 : ℝ) - b.1
  have hl := (affine_mem_minmax (p := d₀) (q := -d₀) hW₀ hW₁).1
  have hu := (affine_mem_minmax (p := d₁) (q := -d₁) hW₀ hW₁).2
  unfold transverseRateBounds
  push_cast
  constructor
  · calc min ((1 - (w₀ : ℝ)) * d₀) ((1 - (w₁ : ℝ)) * d₀)
        = min (d₀ + -d₀ * w₀) (d₀ + -d₀ * w₁) := by congr 1 <;> ring
      _ ≤ d₀ + -d₀ * W := hl
      _ = (1 - W) * d₀ := by ring
      _ ≤ (1 - W) * (Γ - B) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  · calc (1 - W) * (Γ - B) ≤ (1 - W) * d₁ :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = d₁ + -d₁ * W := by ring
      _ ≤ max (d₁ + -d₁ * w₀) (d₁ + -d₁ * w₁) := hu
      _ = max ((1 - (w₀ : ℝ)) * d₁) ((1 - (w₁ : ℝ)) * d₁) := by congr 1 <;> ring

end CAS.Numerics
