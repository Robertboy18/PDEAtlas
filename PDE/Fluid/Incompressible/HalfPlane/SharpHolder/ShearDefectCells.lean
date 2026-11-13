/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearResidualEnvelope

/-!
# Lower bounds of the line defect

The line defect `D_c(A) = ∫_{1/9}^{c} d(p) μ_A(p) dp` (`shearLineDefect`) is bounded below by a
walk over cells `(p₀, p₁]`. The weight `d` increases on `[0, 1]` and decreases on `[1, ∞)`, so
`d ≥ min(d(p₀), d(p₁))` on the cell (`min_shearLineWeight_le`), and
`G(p) = arctan((p - 1)/A) - arctan((p + 1)/A)` is a primitive of `μ_A ≥ 0`, so the cell contributes
at least `w (G(p₁) - G(p₀))` for `0 ≤ w ≤ d` (`ofReal_le_lintegral_shearLineDefect`). The walk
`shearDefectWalk` sums these values with rational bounds of `d` and `G`, and
`shearDefectLow c A` is a rational lower bound of `D_c(A)` (`ofReal_shearDefectLow_le`).

## Main definitions

* `shearMassPrimitive`: the primitive `G(p) = arctan((p - 1)/A) - arctan((p + 1)/A)` of `μ_A`.
* `shearLineWeightLow`, `shearMassCellLow`: rational lower bounds of `d(x)` and of
  `G(p₁) - G(p₀)`.
* `shearDefectWalk`: the walk over the cells from `p` to `c`.
* `shearDefectLow`: a rational lower bound of `D_c(A)`.

## Main results

* `shearLineWeight_eq`: `d(p) = (2p)^{1/2} + √2 - 2 |p - 1|^{1/2}`.
* `min_shearLineWeight_le`: `min(d(p₀), d(p₁)) ≤ d(p)` for `p₀ ≤ p ≤ p₁`.
* `hasDerivAt_shearMassPrimitive`: for `A > 0`, `G' = μ_A`.
* `ofReal_le_lintegral_shearLineDefect`: for `0 ≤ w ≤ d` on `(p₀, p₁]`,
  `w (G(p₁) - G(p₀)) ≤ ∫_{p₀}^{p₁} d μ_A`.
* `shearDefectWalk_spec`: if `wp ≤ d(p)` and the walk from `p ≥ 0` to `c` returns `N`, then
  `(N - acc)/2⁶⁴ ≤ ∫_{(p, c]} d μ_A`.
* `ofReal_shearDefectLow_le`: for `A > 0`, `shearDefectLow c A ≤ D_c(A)`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory PDE.Analysis
open scoped ENNReal

namespace IncompressibleFlow.SharpHolder

/-! ### The weight -/

/-- The weight in square roots: `d(p) = (2p)^{1/2} + √2 - 2 |p - 1|^{1/2}`. -/
theorem shearLineWeight_eq (p : ℝ) :
    shearLineWeight p = Real.sqrt (2 * p) + Real.sqrt 2 - 2 * Real.sqrt |p - 1| := by
  rw [shearLineWeight, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]

/-- `d` increases on `[0, 1]`. -/
theorem shearLineWeight_le_of_le_one {p q : ℝ} (hpq : p ≤ q) (hq : q ≤ 1) :
    shearLineWeight p ≤ shearLineWeight q := by
  rw [shearLineWeight_eq, shearLineWeight_eq, abs_of_nonpos (by linarith),
    abs_of_nonpos (by linarith)]
  have h₁ : Real.sqrt (2 * p) ≤ Real.sqrt (2 * q) := Real.sqrt_le_sqrt (by linarith)
  have h₂ : Real.sqrt (-(q - 1)) ≤ Real.sqrt (-(p - 1)) := Real.sqrt_le_sqrt (by linarith)
  linarith

/-- `d` decreases on `[1, ∞)`: `√(2q) - √(2p) ≤ 2 (√(q - 1) - √(p - 1))` for `1 ≤ p ≤ q`. -/
theorem shearLineWeight_le_of_one_le {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    shearLineWeight q ≤ shearLineWeight p := by
  rw [shearLineWeight_eq, shearLineWeight_eq, abs_of_nonneg (by linarith),
    abs_of_nonneg (by linarith)]
  set a := Real.sqrt (2 * p)
  set b := Real.sqrt (2 * q)
  set c := Real.sqrt (p - 1)
  set e := Real.sqrt (q - 1)
  have ha : a ^ 2 = 2 * p := Real.sq_sqrt (by linarith)
  have hb : b ^ 2 = 2 * q := Real.sq_sqrt (by linarith)
  have hc : c ^ 2 = p - 1 := Real.sq_sqrt (by linarith)
  have he : e ^ 2 = q - 1 := Real.sq_sqrt (by linarith)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have he0 : 0 ≤ e := Real.sqrt_nonneg _
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hce : c ≤ e := Real.sqrt_le_sqrt (by linarith)
  have hca : c ≤ a := Real.sqrt_le_sqrt (by linarith)
  have heb : e ≤ b := Real.sqrt_le_sqrt (by linarith)
  -- `(b - a)(b + a) = 2 (q - p) = 2 (e - c)(e + c)` and `e + c ≤ b + a`
  have hkey : (b - a) * (b + a) = 2 * ((e - c) * (e + c)) := by nlinarith
  have : b - a ≤ 2 * (e - c) := by
    rcases eq_or_lt_of_le (add_nonneg ha0 hb0) with h0 | h0
    · nlinarith
    · nlinarith [mul_le_mul_of_nonneg_left (add_le_add heb hca) (sub_nonneg.2 hce)]
  linarith

/-- `d` is unimodal: `min(d(p₀), d(p₁)) ≤ d(p)` for `p₀ ≤ p ≤ p₁`. -/
theorem min_shearLineWeight_le {p₀ p p₁ : ℝ} (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) :
    min (shearLineWeight p₀) (shearLineWeight p₁) ≤ shearLineWeight p := by
  rcases le_total p 1 with hp | hp
  · exact (min_le_left _ _).trans (shearLineWeight_le_of_le_one h₀ hp)
  · exact (min_le_right _ _).trans (shearLineWeight_le_of_one_le hp h₁)

/-- A rational lower bound of `d(x)`. -/
def shearLineWeightLow (x : ℚ) : ℚ :=
  sqrtLow (2 * x) + 1414213562373 / 10 ^ 12 - 2 * sqrtHigh |x - 1|

/-- For `x ≥ 0`, `shearLineWeightLow x ≤ d(x)`. -/
theorem shearLineWeightLow_le {x : ℚ} (hx : 0 ≤ x) :
    (shearLineWeightLow x : ℝ) ≤ shearLineWeight x := by
  rw [shearLineWeight_eq]
  have h₁ := sqrtLow_le_sqrt (q := 2 * x) (by linarith)
  have h₂ : (1414213562373 / 10 ^ 12 : ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have h₃ := sqrt_le_sqrtHigh (q := |x - 1|) (abs_nonneg _)
  unfold shearLineWeightLow
  push_cast at h₁ h₃ ⊢
  linarith

/-! ### The cells -/

/-- The primitive `G(p) = arctan((p - 1)/A) - arctan((p + 1)/A)` of `μ_A`. -/
def shearMassPrimitive (A p : ℝ) : ℝ := Real.arctan ((p - 1) / A) - Real.arctan ((p + 1) / A)

/-- For `A > 0`, `G' = μ_A`. -/
theorem hasDerivAt_shearMassPrimitive {A : ℝ} (hA : 0 < A) (p : ℝ) :
    HasDerivAt (shearMassPrimitive A) (shearMassDensity A p) p := by
  have h₁ := (((hasDerivAt_id' p).sub_const 1).div_const A).arctan
  have h₂ := (((hasDerivAt_id' p).add_const 1).div_const A).arctan
  refine (h₁.sub h₂).congr_deriv ?_
  unfold shearMassDensity
  have hA' := hA.ne'
  field_simp
  ring

/-- **A cell of the line defect**: for `0 ≤ w ≤ d` on `(p₀, p₁]`,
`w (G(p₁) - G(p₀)) ≤ ∫_{p₀}^{p₁} d μ_A`. -/
theorem ofReal_le_lintegral_shearLineDefect {A w p₀ p₁ : ℝ} (hA : 0 < A) (hp₀ : 0 ≤ p₀)
    (hp : p₀ ≤ p₁) (hw : 0 ≤ w) (hwd : ∀ p ∈ Ioc p₀ p₁, w ≤ shearLineWeight p) :
    ENNReal.ofReal (w * (shearMassPrimitive A p₁ - shearMassPrimitive A p₀)) ≤
      ∫⁻ p in Ioc p₀ p₁, ENNReal.ofReal (shearLineWeight p * shearMassDensity A p) := by
  rw [mul_sub, ← lintegral_Ioc_ofReal_deriv (g := fun p ↦ w * shearMassPrimitive A p)
    (g' := fun p ↦ w * shearMassDensity A p) hp
    (fun p _ ↦ ((hasDerivAt_shearMassPrimitive hA p).const_mul w).continuousAt.continuousWithinAt)
    (fun p _ ↦ (hasDerivAt_shearMassPrimitive hA p).const_mul w)
    (fun p hp' ↦ mul_nonneg hw (shearMassDensity_nonneg hA (hp₀.trans hp'.1.le)))]
  refine setLIntegral_mono' measurableSet_Ioc fun p hp' ↦ ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul_of_nonneg_right (hwd p hp') (shearMassDensity_nonneg hA (hp₀.trans hp'.1.le))

/-- Rational bounds `(lo, hi)` of `G(p)`. -/
def shearMassPrimitiveBounds (A p : ℚ) : ℚ × ℚ :=
  ((atanPair ((p - 1) / A)).1 - (atanPair ((p + 1) / A)).2,
    (atanPair ((p - 1) / A)).2 - (atanPair ((p + 1) / A)).1)

/-- The rational bounds enclose `G(p)`: `lo ≤ G(p) ≤ hi`. -/
theorem shearMassPrimitiveBounds_spec (A p : ℚ) :
    ((shearMassPrimitiveBounds A p).1 : ℝ) ≤ shearMassPrimitive A p ∧
      shearMassPrimitive A p ≤ (shearMassPrimitiveBounds A p).2 := by
  have h₁ := atanPair_fst_le ((p - 1) / A)
  have h₂ := le_atanPair_snd ((p - 1) / A)
  have h₃ := atanPair_fst_le ((p + 1) / A)
  have h₄ := le_atanPair_snd ((p + 1) / A)
  unfold shearMassPrimitiveBounds shearMassPrimitive
  push_cast at h₁ h₂ h₃ h₄ ⊢
  constructor <;> linarith

/-- `G(p₁) - G(p₀)` by the subtraction formula of the arctangent when `(p₀ - 1)(p₁ - 1) ≥ 0`. -/
theorem shearMassPrimitive_sub_eq {A p₀ p₁ : ℝ} (hA : 0 < A) (hp₀ : 0 ≤ p₀) (hp₁ : 0 ≤ p₁)
    (h : 0 ≤ (p₀ - 1) * (p₁ - 1)) :
    shearMassPrimitive A p₁ - shearMassPrimitive A p₀ =
      Real.arctan (A * (p₁ - p₀) / (A ^ 2 + (p₀ - 1) * (p₁ - 1))) -
        Real.arctan (A * (p₁ - p₀) / (A ^ 2 + (p₀ + 1) * (p₁ + 1))) := by
  have hA' := hA.ne'
  have h₁ : 0 ≤ (p₁ - 1) / A * ((p₀ - 1) / A) := by
    rw [div_mul_div_comm]
    exact div_nonneg (by linarith [mul_comm (p₀ - 1) (p₁ - 1)]) (by positivity)
  have h₂ : 0 ≤ (p₁ + 1) / A * ((p₀ + 1) / A) := by positivity
  have hd₁ : A ^ 2 + (p₀ - 1) * (p₁ - 1) ≠ 0 := by positivity
  have hd₂ : A ^ 2 + (p₀ + 1) * (p₁ + 1) ≠ 0 := by positivity
  unfold shearMassPrimitive
  have e₁ := arctan_sub_arctan h₁
  have e₂ := arctan_sub_arctan h₂
  have q₁ : ((p₁ - 1) / A - (p₀ - 1) / A) / (1 + (p₁ - 1) / A * ((p₀ - 1) / A)) =
      A * (p₁ - p₀) / (A ^ 2 + (p₀ - 1) * (p₁ - 1)) := by
    field_simp
    ring
  have q₂ : ((p₁ + 1) / A - (p₀ + 1) / A) / (1 + (p₁ + 1) / A * ((p₀ + 1) / A)) =
      A * (p₁ - p₀) / (A ^ 2 + (p₀ + 1) * (p₁ + 1)) := by
    field_simp
    ring
  rw [q₁] at e₁
  rw [q₂] at e₂
  linarith

/-- A rational lower bound of `G(p₁) - G(p₀)`. -/
def shearMassCellLow (A p₀ p₁ : ℚ) : ℚ :=
  if 0 ≤ (p₀ - 1) * (p₁ - 1) then
    (atanPair (A * (p₁ - p₀) / (A ^ 2 + (p₀ - 1) * (p₁ - 1)))).1 -
      (atanPair (A * (p₁ - p₀) / (A ^ 2 + (p₀ + 1) * (p₁ + 1)))).2
  else (shearMassPrimitiveBounds A p₁).1 - (shearMassPrimitiveBounds A p₀).2

/-- For `A > 0` and `p₀, p₁ ≥ 0`, `shearMassCellLow A p₀ p₁ ≤ G(p₁) - G(p₀)`. -/
theorem shearMassCellLow_le {A p₀ p₁ : ℚ} (hA : 0 < A) (hp₀ : 0 ≤ p₀) (hp₁ : 0 ≤ p₁) :
    (shearMassCellLow A p₀ p₁ : ℝ) ≤ shearMassPrimitive A p₁ - shearMassPrimitive A p₀ := by
  unfold shearMassCellLow
  split_ifs with h
  · have h' : (0 : ℝ) ≤ (p₀ - 1) * (p₁ - 1) := by exact_mod_cast h
    rw [shearMassPrimitive_sub_eq (by exact_mod_cast hA) (by exact_mod_cast hp₀)
      (by exact_mod_cast hp₁) h']
    have h₁ := atanPair_fst_le (A * (p₁ - p₀) / (A ^ 2 + (p₀ - 1) * (p₁ - 1)))
    have h₂ := le_atanPair_snd (A * (p₁ - p₀) / (A ^ 2 + (p₀ + 1) * (p₁ + 1)))
    push_cast at h₁ h₂ ⊢
    linarith
  · have h₁ := (shearMassPrimitiveBounds_spec A p₁).1
    have h₂ := (shearMassPrimitiveBounds_spec A p₀).2
    push_cast at h₁ h₂ ⊢
    linarith

/-- The walk over the cells from `p` to `c`, carrying a lower bound `wp` of `d(p)` and the sum
`acc` on the grid `2^-64`. -/
def shearDefectWalk (A : ℚ) (next : ℚ → ℚ) : ℕ → ℚ → ℚ → ℚ → ℤ → Option ℤ
  | 0, _, _, _, _ => none
  | fuel + 1, p, c, wp, acc =>
    if c ≤ p then some acc
    else
      let p' := min (next p) c
      if p < p' then
        let wp' := shearLineWeightLow p'
        shearDefectWalk A next fuel p' c wp'
          (acc + ⌊max 0 (min wp wp') * shearMassCellLow A p p' * 2 ^ 64⌋)
      else none

/-- **Soundness of the walk.** If `wp ≤ d(p)` and the walk from `p ≥ 0` to `c` returns `N`, then
`(N - acc)/2^64 ≤ ∫_{(p, c]} d μ_A`. -/
theorem shearDefectWalk_spec {A : ℚ} (hA : 0 < A) {next : ℚ → ℚ} {c : ℚ} (fuel : ℕ)
    {p wp : ℚ} {acc N : ℤ} (hp : 0 ≤ p) (hwp : (wp : ℝ) ≤ shearLineWeight p)
    (h : shearDefectWalk A next fuel p c wp acc = some N) :
    ENNReal.ofReal ((N - acc) / 2 ^ 64) ≤
      ∫⁻ x in Ioc (p : ℝ) c, ENNReal.ofReal (shearLineWeight x * shearMassDensity A x) := by
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  induction fuel generalizing p wp acc with
  | zero => simp [shearDefectWalk] at h
  | succ n ih =>
    simp only [shearDefectWalk] at h
    split_ifs at h with hcp hlt
    · simp only [Option.some.injEq] at h
      subst h
      simp
    · set p' := min (next p) c
      have hp' : 0 ≤ p' := hp.trans hlt.le
      have hwp' := shearLineWeightLow_le hp'
      have hrest := ih hp' hwp' h
      have hpp' : (p : ℝ) ≤ p' := by exact_mod_cast hlt.le
      have hp'c : (p' : ℝ) ≤ c := by exact_mod_cast min_le_right (next p) c
      -- the cell
      set w := max 0 (min wp (shearLineWeightLow p'))
      set g := shearMassCellLow A p p'
      have hg := shearMassCellLow_le hA hp hp'
      have hw0 : (0 : ℝ) ≤ w := by exact_mod_cast le_max_left _ _
      have hcell : ENNReal.ofReal ((⌊w * g * 2 ^ 64⌋ : ℝ) / 2 ^ 64) ≤
          ∫⁻ x in Ioc (p : ℝ) p', ENNReal.ofReal (shearLineWeight x * shearMassDensity A x) := by
        have hfl : ((⌊w * g * 2 ^ 64⌋ : ℤ) : ℝ) / 2 ^ 64 ≤
            (w : ℝ) * (shearMassPrimitive A p' - shearMassPrimitive A p) := by
          have h₁ : ((⌊w * g * 2 ^ 64⌋ : ℤ) : ℚ) ≤ w * g * 2 ^ 64 := Int.floor_le _
          have h₂ : ((⌊w * g * 2 ^ 64⌋ : ℤ) : ℝ) ≤ (w : ℝ) * g * 2 ^ 64 := by exact_mod_cast h₁
          rw [div_le_iff₀ (by positivity)]
          refine h₂.trans ?_
          have : (w : ℝ) * g ≤ w * (shearMassPrimitive A p' - shearMassPrimitive A p) :=
            mul_le_mul_of_nonneg_left hg hw0
          nlinarith
        refine (ENNReal.ofReal_le_ofReal hfl).trans ?_
        rcases eq_or_lt_of_le hw0 with hw | hw
        · rw [← hw, zero_mul, ENNReal.ofReal_zero]
          exact zero_le
        · refine ofReal_le_lintegral_shearLineDefect hA' (by exact_mod_cast hp) hpp' hw0
            fun x hx ↦ ?_
          have hw' : (0 : ℚ) < w := by exact_mod_cast hw
          have hmin : (w : ℝ) ≤ min (wp : ℝ) (shearLineWeightLow p') := by
            have : w = min wp (shearLineWeightLow p') := by
              simp only [w] at hw' ⊢
              exact max_eq_right (le_of_lt (lt_max_iff.1 hw' |>.resolve_left (lt_irrefl 0)))
            rw [this]
            push_cast
            exact le_rfl
          exact hmin.trans ((min_le_min hwp hwp').trans (min_shearLineWeight_le hx.1.le hx.2))
      calc ENNReal.ofReal ((N - acc) / 2 ^ 64)
          ≤ ENNReal.ofReal ((⌊w * g * 2 ^ 64⌋ : ℝ) / 2 ^ 64) +
              ENNReal.ofReal ((N - (acc + ⌊w * g * 2 ^ 64⌋)) / 2 ^ 64) := by
            refine le_trans (le_of_eq ?_) ENNReal.ofReal_add_le
            congr 1
            ring
        _ ≤ (∫⁻ x in Ioc (p : ℝ) p', ENNReal.ofReal (shearLineWeight x * shearMassDensity A x)) +
            ∫⁻ x in Ioc (p' : ℝ) c, ENNReal.ofReal (shearLineWeight x * shearMassDensity A x) := by
            gcongr
            simpa using hrest
        _ = ∫⁻ x in Ioc (p : ℝ) c, ENNReal.ofReal (shearLineWeight x * shearMassDensity A x) := by
            rw [← lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl),
              Ioc_union_Ioc_eq_Ioc hpp' hp'c]

/-- The cells of the line defect: ratio `1/4` in `|p - 1|` below and above `p = 1`, one cell across
`p = 1` ending at `1 + 2^-12`, and width `1/8` above `p = 2`. -/
def shearDefectNext (p : ℚ) : ℚ :=
  if p < 1 - 1 / 2 ^ 12 then roundUpRel (1 - (1 - p) * (3 / 4))
  else if p < 1 + 1 / 2 ^ 12 then 1 + 1 / 2 ^ 12
  else if p < 2 then roundUpRel (1 + (p - 1) * (5 / 4))
  else p + 1 / 8

/-- A rational lower bound of `D_c(A)`. -/
def shearDefectLow (c A : ℚ) : ℚ :=
  match shearDefectWalk A shearDefectNext 1000 (1 / 9) c (shearLineWeightLow (1 / 9)) 0 with
  | some N => N / 2 ^ 64
  | none => 0

/-- For `A > 0`, `shearDefectLow c A ≤ D_c(A)`. -/
theorem ofReal_shearDefectLow_le {c A : ℚ} (hA : 0 < A) :
    ENNReal.ofReal (shearDefectLow c A) ≤ shearLineDefect c A := by
  unfold shearDefectLow
  split
  · rename_i N hN
    have := shearDefectWalk_spec hA 1000 (by norm_num) (shearLineWeightLow_le (by norm_num)) hN
    push_cast at this ⊢
    simpa [shearLineDefect] using this
  · simp

end IncompressibleFlow.SharpHolder
