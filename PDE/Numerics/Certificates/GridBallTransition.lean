/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.GridBallPolynomial
public import CAS.Numerics.GridBallAtan
public import PDE.Analysis.Calculus.SmoothTransitionIteratedDerivatives

/-!
# Balls for the exponential transition and its derivatives

`σ = Real.smoothTransition` is `χ_e` of Chen and Hou, Part II, (D.1).

* `transitionPoint a order` encloses `σ(a)` at a rational `a`: `0` for `a ≤ 0`, `1` for `a ≥ 1`,
  `E / (1 + E)` with `E = exp (1 / (1 - a) - 1 / a)` on `(0, 1/2]` and
  `1 / (1 + exp (1/a - 1/(1-a)))` on `(1/2, 1)`, so that the exponential is never taken of a
  positive argument
  (`transitionPoint_sound`). `transitionRange I order` encloses `σ` on `I` by monotonicity.
* `transitionDerivRange k order p I` encloses `σ^(k+1)` on `I ⊂ (0, 1)` through the closed form
  `σ (1 - σ) H_k(σ, t) / (t (1 - t)) ^ (2k + 2)` of `iteratedDeriv_succ_smoothTransition`
  (`transitionDerivRange_sound`), and `transitionFlatRange k order δ` encloses it on `t ≤ δ` and
  on `t ≥ 1 - δ` for `(2k + 2) δ ≤ 1` by the flat-end bound (`transitionFlatRange_sound`).
* `transitionPointBall`, `IntervalBalls.transitionRangeBall`, `IntervalBalls.transitionDerivBall`
  and `IntervalBalls.transitionFlatBall` are the ball mirrors, sound in the form
  `S.Encloses P I → (op S).Encloses P (op I)`.

Near the endpoints the closed form divides by `(t (1 - t)) ^ (2k + 2)`; the balls carry an
absolute error of a few units of `2 ^ -P` in `σ`, so the rounding alone costs about
`(2k + 2) log₂ (1 / (t (1 - t)))` bits of the precision `P`. This is a rounding estimate: the
truncation of the exponential series and the dependence of the interval evaluation of `H_k` on
a wide interval come in addition. The flat-end bound covers the cells next to the endpoints.
At `P = 200` and order 40 a value of `σ` costs about 1.3 ms in the fast profile and 6 ms in the
kernel, and `σ^(5)` about 8.5 ms and 110 ms.

## Main results

* `transitionPoint_sound`: `transitionPoint a order` encloses `σ(a)` at every rational `a`.
* `transitionRange_sound`: `transitionRange I order` encloses `σ(x)` for every `x ∈ I`.
* `transitionDerivRange_sound`: for `0 < I.lo` and `I.hi < 1`, `transitionDerivRange k order p I`
  encloses `σ^(k+1)(x)` for every `x ∈ I`.
* `transitionFlatRange_sound`: for `δ > 0` with `(2k + 2) δ ≤ 1`, `transitionFlatRange k order δ`
  encloses `σ^(k+1)(x)` for `x ≤ δ` and `x ≥ 1 - δ`.
* `IntervalBalls.splitBalls_encloses`: balls of the four branches of a case split give balls of
  the function defined by the cases.
* `transitionPointBall_encloses`: a ball of `a` gives balls of `transitionPoint a order`.
* `IntervalBalls.transitionDerivBall_encloses`: balls of `I` give balls of
  `transitionDerivRange k order p I`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, (D.1).
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace CAS.Numerics

open CAS.Continuum CAS.Polynomial PDE.Analysis

/-! ### Values -/

/-- The enclosure `E / (1 + E)`, `E = exp ((1 - a)⁻¹ - a⁻¹)`, of `σ(a)` on `(0, 1/2]`. -/
def transitionLow (a : ℚ) (order : ℕ) : RationalInterval :=
  (RationalInterval.expRangeWith (RationalInterval.const ((1 - a)⁻¹ - a⁻¹)) order)
    |>.divPositiveOrZero ((RationalInterval.const 1).add
      (RationalInterval.expRangeWith (RationalInterval.const ((1 - a)⁻¹ - a⁻¹)) order))

/-- The enclosure `1 / (1 + exp (a⁻¹ - (1 - a)⁻¹))` of `σ(a)` on `(1/2, 1)`. -/
def transitionHigh (a : ℚ) (order : ℕ) : RationalInterval :=
  (RationalInterval.const 1).divPositiveOrZero ((RationalInterval.const 1).add
    (RationalInterval.expRangeWith (RationalInterval.const (a⁻¹ - (1 - a)⁻¹)) order))

/-- The enclosure of `σ(a)` at a rational point `a`. -/
def transitionPoint (a : ℚ) (order : ℕ) : RationalInterval :=
  if a ≤ 0 then RationalInterval.const 0
  else if 1 ≤ a then RationalInterval.const 1
  else if a ≤ 1 / 2 then transitionLow a order
  else transitionHigh a order

/-- The interval `1 + exp I` has a positive lower end. -/
theorem one_add_expRangeWith_lo_pos (I : RationalInterval) (order : ℕ) :
    0 < ((RationalInterval.const 1).add (RationalInterval.expRangeWith I order)).lo := by
  rw [RationalInterval.add_lo, RationalInterval.const_lo, expRangeWith_lo]
  have := le_max_left (0 : ℚ) (FloatLib.Numerics.Enclosure.exp I.lo (max order 1)).lo
  linarith

/-- For `0 < a < 1`, `transitionLow a order` encloses `σ(a)`. -/
theorem transitionLow_sound {a : ℚ} (ha : 0 < a) (ha₁ : a < 1) (order : ℕ) :
    (transitionLow a order).MemReal (Real.smoothTransition a) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have haR₁ : (a : ℝ) < 1 := by exact_mod_cast ha₁
  have hgap : (0 : ℝ) < 1 - a := by linarith
  set e : ℚ := (1 - a)⁻¹ - a⁻¹
  have hE := RationalInterval.expRangeWith_sound _ order (RationalInterval.memReal_const e)
  have hden := RationalInterval.add_sound (RationalInterval.memReal_const 1) hE
  have h := RationalInterval.divPositiveOrZero_sound (one_add_expRangeWith_lo_pos _ order) hE hden
  have heq : Real.exp (e : ℝ) / (((1 : ℚ) : ℝ) + Real.exp (e : ℝ)) =
      Real.smoothTransition a := by
    rw [smoothTransition_eq_inv_one_add_exp haR haR₁]
    have he : (e : ℝ) = -(1 / (a : ℝ) - 1 / (1 - a)) := by simp only [e]; push_cast; ring
    rw [he, Real.exp_neg]
    have hp := Real.exp_pos (1 / (a : ℝ) - 1 / (1 - a))
    field_simp
    ring
  rwa [heq] at h

/-- For `0 < a < 1`, `transitionHigh a order` encloses `σ(a)`. -/
theorem transitionHigh_sound {a : ℚ} (ha : 0 < a) (ha₁ : a < 1) (order : ℕ) :
    (transitionHigh a order).MemReal (Real.smoothTransition a) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have haR₁ : (a : ℝ) < 1 := by exact_mod_cast ha₁
  set e : ℚ := a⁻¹ - (1 - a)⁻¹
  have hE := RationalInterval.expRangeWith_sound _ order (RationalInterval.memReal_const e)
  have hden := RationalInterval.add_sound (RationalInterval.memReal_const 1) hE
  have h := RationalInterval.divPositiveOrZero_sound (one_add_expRangeWith_lo_pos _ order)
    (RationalInterval.memReal_const 1) hden
  have heq : ((1 : ℚ) : ℝ) / (((1 : ℚ) : ℝ) + Real.exp (e : ℝ)) = Real.smoothTransition a := by
    rw [smoothTransition_eq_inv_one_add_exp haR haR₁]
    have he : (e : ℝ) = 1 / (a : ℝ) - 1 / (1 - a) := by simp only [e]; push_cast; ring
    rw [he]; simp
  rwa [heq] at h

/-- `transitionPoint a order` encloses `σ(a)` at every rational `a`. -/
theorem transitionPoint_sound (a : ℚ) (order : ℕ) :
    (transitionPoint a order).MemReal (Real.smoothTransition a) := by
  unfold transitionPoint
  by_cases h0 : a ≤ 0
  · have : Real.smoothTransition a = 0 :=
      Real.smoothTransition.zero_of_nonpos (by exact_mod_cast h0)
    simpa [h0, this] using RationalInterval.memReal_const 0
  by_cases h1 : 1 ≤ a
  · have : Real.smoothTransition a = 1 :=
      Real.smoothTransition.one_of_one_le (by exact_mod_cast h1)
    simpa [h0, h1, this] using RationalInterval.memReal_const 1
  have ha := not_le.mp h0
  have ha₁ := not_le.mp h1
  simp only [h0, h1, ↓reduceIte]
  split_ifs
  · exact transitionLow_sound ha ha₁ order
  · exact transitionHigh_sound ha ha₁ order

/-- The enclosure of `σ` on `I` from the endpoint enclosures, by monotonicity. -/
def transitionRange (I : RationalInterval) (order : ℕ) : RationalInterval :=
  monotoneRange (fun a ↦ transitionPoint a order)
    (monotone_ends_of_sound Real.smoothTransition.monotone fun a ↦ transitionPoint_sound a order) I

/-- `transitionRange I order` encloses `σ(x)` for every `x ∈ I`. -/
theorem transitionRange_sound {I : RationalInterval} (order : ℕ) {x : ℝ} (hx : I.MemReal x) :
    (transitionRange I order).MemReal (Real.smoothTransition x) :=
  monotoneRange_sound Real.smoothTransition.monotone (fun a ↦ transitionPoint_sound a order) hx

/-! ### Derivatives -/

/-- The exponent `-(2k + 2)` of the closed form. -/
def transitionExponent (k : ℕ) : ℚ := -((2 * k + 2 : ℕ) : ℚ)

/-- The closed-form enclosure of `σ^(k+1)` on an interval inside `(0, 1)`. -/
def transitionDerivRange (k order : ℕ) (p : RationalInterval.PowerPrecision)
    (I : RationalInterval) : RationalInterval :=
  (((transitionRange I order).mul ((RationalInterval.const 1).sub (transitionRange I order))).mul
    (RationalInterval.nestedRange (transitionNumerator k) (transitionRange I order) I)).mul
      (RationalInterval.rpowRat (I.mul ((RationalInterval.const 1).sub I))
        (transitionExponent k) p)

/-- The product of two intervals with positive lower ends has a positive lower end. -/
theorem mul_lo_pos {I J : RationalInterval} (hI : 0 < I.lo) (hJ : 0 < J.lo) :
    0 < (I.mul J).lo := by
  have hIh : 0 < I.hi := hI.trans_le I.hle
  have hJh : 0 < J.hi := hJ.trans_le J.hle
  rw [RationalInterval.mul_lo]
  exact lt_min (lt_min (mul_pos hI hJ) (mul_pos hI hJh))
    (lt_min (mul_pos hIh hJ) (mul_pos hIh hJh))

/-- For `0 < I.lo` and `I.hi < 1`, `transitionDerivRange k order p I` encloses `σ^(k+1)(x)` for
every `x ∈ I`. -/
theorem transitionDerivRange_sound (k order : ℕ) (p : RationalInterval.PowerPrecision)
    {I : RationalInterval} (hlo : 0 < I.lo) (hhi : I.hi < 1) {x : ℝ} (hx : I.MemReal x) :
    (transitionDerivRange k order p I).MemReal
      (iteratedDeriv (k + 1) Real.smoothTransition x) := by
  have hloR : (0 : ℝ) < I.lo := by exact_mod_cast hlo
  have hhiR : (I.hi : ℝ) < 1 := by exact_mod_cast hhi
  have hx0 : 0 < x := hloR.trans_le hx.1
  have hx1 : x < 1 := hx.2.trans_lt hhiR
  have hw : 0 < x * (1 - x) := mul_pos hx0 (by linarith)
  rw [iteratedDeriv_succ_smoothTransition k]
  have hS := transitionRange_sound order hx
  have hone := RationalInterval.memReal_const 1
  have hσσ := RationalInterval.mul_sound hS (RationalInterval.sub_sound hone hS)
  have hH := RationalInterval.nestedRange_sound (transitionNumerator k) hS hx
  have hW := RationalInterval.mul_sound hx (RationalInterval.sub_sound hone hx)
  have hdom : RationalInterval.PowDomain (I.mul ((RationalInterval.const 1).sub I))
      (transitionExponent k) := by
    right
    refine mul_lo_pos hlo ?_
    rw [RationalInterval.sub_lo, RationalInterval.const_lo]
    linarith
  have hP := RationalInterval.rpowRat_sound hdom p hW
  have h := RationalInterval.mul_sound (RationalInterval.mul_sound hσσ hH) hP
  have hexp : (x * (1 - x)) ^ ((transitionExponent k : ℚ) : ℝ) =
      ((x * (1 - x)) ^ (2 * k + 2))⁻¹ := by
    rw [transitionExponent]
    push_cast
    rw [Real.rpow_neg hw.le]
    norm_cast
  rw [Rat.cast_one, hexp] at h
  rw [div_eq_mul_inv]
  exact h

/-- The flat-end enclosure `[-B, B]` of `σ^(k+1)` on `t ≤ δ` and `t ≥ 1 - δ`, where `B` is the
upper end of an enclosure of `‖H_k‖₁ e ^ (2 - 1/δ) (2/δ) ^ (2k + 2)`. -/
def transitionFlatBound (k order : ℕ) (δ : ℚ) : RationalInterval :=
  (RationalInterval.const (nestedNorm (transitionNumerator k))).mul
    ((RationalInterval.expRangeWith (RationalInterval.const (2 - 1 / δ)) order).mul
      (RationalInterval.const ((2 / δ) ^ (2 * k + 2))))

/-- `[-|B|, |B|]` for the upper end `B` of `transitionFlatBound`. -/
def transitionFlatRange (k order : ℕ) (δ : ℚ) : RationalInterval :=
  RationalInterval.ofBounds (-|(transitionFlatBound k order δ).hi|)
    |(transitionFlatBound k order δ).hi|
    (by linarith [abs_nonneg (transitionFlatBound k order δ).hi])

/-- For `δ > 0` with `(2k + 2) δ ≤ 1`, `transitionFlatRange k order δ` encloses `σ^(k+1)(x)` at
every `x ≤ δ` and every `x ≥ 1 - δ`. -/
theorem transitionFlatRange_sound {k order : ℕ} {δ : ℚ} (hδ : 0 < δ)
    (hk : (2 * k + 2) * δ ≤ 1) {x : ℝ} (hx : x ≤ δ ∨ 1 - δ ≤ x) :
    (transitionFlatRange k order δ).MemReal (iteratedDeriv (k + 1) Real.smoothTransition x) := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hkR : (2 * k + 2) * (δ : ℝ) ≤ 1 := by exact_mod_cast hk
  have hbound : |iteratedDeriv (k + 1) Real.smoothTransition x| ≤
      nestedNorm (transitionNumerator k) * (Real.exp (2 - 1 / δ) * (2 / δ) ^ (2 * k + 2)) := by
    rcases hx with hx | hx
    · exact abs_iteratedDeriv_succ_smoothTransition_le_of_le hδR hx hkR
    · exact abs_iteratedDeriv_succ_smoothTransition_le_of_one_sub_le hδR hx hkR
  have hB := RationalInterval.mul_sound
    (RationalInterval.memReal_const (nestedNorm (transitionNumerator k)))
    (RationalInterval.mul_sound (RationalInterval.expRangeWith_sound _ order
      (RationalInterval.memReal_const (2 - 1 / δ)))
      (RationalInterval.memReal_const ((2 / δ) ^ (2 * k + 2))))
  have hle : |iteratedDeriv (k + 1) Real.smoothTransition x| ≤
      ((|(transitionFlatBound k order δ).hi| : ℚ) : ℝ) := by
    refine hbound.trans ?_
    have h2 := hB.2
    push_cast at h2 ⊢
    exact h2.trans (le_abs_self _)
  have h1 := neg_abs_le (iteratedDeriv (k + 1) Real.smoothTransition x)
  have h2 := le_abs_self (iteratedDeriv (k + 1) Real.smoothTransition x)
  refine ⟨?_, ?_⟩
  · change (((-|(transitionFlatBound k order δ).hi|) : ℚ) : ℝ) ≤ _
    push_cast at hle ⊢
    linarith
  · change _ ≤ ((|(transitionFlatBound k order δ).hi| : ℚ) : ℝ)
    linarith

/-! ### Balls -/

namespace IntervalBalls

/-- Balls of a function of `a` defined by the cases `a ≤ 0`, `1 ≤ a`, `a ≤ c` and otherwise, from
the balls `Z`, `O`, `L`, `H` of the four branches and the decisions `b₀`, `b₁`, `bᵢ` (`0 < a < 1`),
`bₗ` (`a ≤ c`) and `bₕ` (`c < a`); the join of `L` and `H` when neither of the last two holds. -/
def splitBalls (b₀ b₁ bᵢ bₗ bₕ : Bool) (Z O L H : IntervalBalls) : IntervalBalls :=
  Bool.rec (Bool.rec (Bool.rec invalid (Bool.rec (Bool.rec (join L H) H bₕ) L bₗ) bᵢ) O b₁) Z b₀

/-- If each decision implies its case and `Z`, `O`, `L`, `H` enclose the four branches, then
`splitBalls` encloses the function defined by the cases `a ≤ 0`, `1 ≤ a`, `a ≤ c` and otherwise. -/
theorem splitBalls_encloses {P : ℕ} {b₀ b₁ bᵢ bₗ bₕ : Bool} {Z O L H : IntervalBalls}
    {a c : ℚ} {z o l h : RationalInterval} (h₀ : b₀ = true → a ≤ 0) (h₁ : b₁ = true → 1 ≤ a)
    (hᵢ : bᵢ = true → 0 < a ∧ a < 1) (hₗ : bₗ = true → a ≤ c) (hₕ : bₕ = true → c < a)
    (hZ : Z.Encloses P z) (hO : O.Encloses P o) (hL : L.Encloses P l) (hH : H.Encloses P h) :
    (splitBalls b₀ b₁ bᵢ bₗ bₕ Z O L H).Encloses P
      (if a ≤ 0 then z else if 1 ≤ a then o else if a ≤ c then l else h) := by
  unfold splitBalls
  cases e₀ : b₀
  · cases e₁ : b₁
    · cases eᵢ : bᵢ
      · exact invalid_encloses _
      · obtain ⟨ha, ha₁⟩ := hᵢ eᵢ
        have n₀ : ¬ a ≤ 0 := not_le.mpr ha
        have n₁ : ¬ 1 ≤ a := not_le.mpr ha₁
        simp only [n₀, n₁, ↓reduceIte]
        cases eₗ : bₗ
        · cases eₕ : bₕ
          · exact join_encloses_ite hL hH (a ≤ c)
          · simpa only [not_le.mpr (hₕ eₕ), ↓reduceIte] using hH
        · simpa only [hₗ eₗ, ↓reduceIte] using hL
    · have ha := h₁ e₁
      simpa only [show ¬ a ≤ 0 by linarith, ha, ↓reduceIte] using hO
  · simpa only [h₀ e₀, ↓reduceIte] using hZ

end IntervalBalls

/-- Balls of `transitionLow a order` from a ball `B` of `a`. -/
def transitionLowBall (P order : ℕ) (B : GridBall) : IntervalBalls :=
  IntervalBalls.divPositiveOrZero P
    (IntervalBalls.expRangeBall P order
      ⟨GridBall.sub (GridBall.inv P (GridBall.sub (GridBall.ofNat P 1) B)) (GridBall.inv P B),
        GridBall.sub (GridBall.inv P (GridBall.sub (GridBall.ofNat P 1) B)) (GridBall.inv P B)⟩)
    ((IntervalBalls.const P 1).add (IntervalBalls.expRangeBall P order
      ⟨GridBall.sub (GridBall.inv P (GridBall.sub (GridBall.ofNat P 1) B)) (GridBall.inv P B),
        GridBall.sub (GridBall.inv P (GridBall.sub (GridBall.ofNat P 1) B)) (GridBall.inv P B)⟩))

/-- Balls of `transitionHigh a order` from a ball `B` of `a`. -/
def transitionHighBall (P order : ℕ) (B : GridBall) : IntervalBalls :=
  IntervalBalls.divPositiveOrZero P (IntervalBalls.const P 1)
    ((IntervalBalls.const P 1).add (IntervalBalls.expRangeBall P order
      ⟨GridBall.sub (GridBall.inv P B) (GridBall.inv P (GridBall.sub (GridBall.ofNat P 1) B)),
        GridBall.sub (GridBall.inv P B) (GridBall.inv P (GridBall.sub (GridBall.ofNat P 1) B))⟩))

/-- A ball `B` of `a` gives balls of `transitionLow a order`. -/
theorem transitionLowBall_encloses {P order : ℕ} {B : GridBall} {a : ℚ} (hB : B.Encloses P a) :
    (transitionLowBall P order B).Encloses P (transitionLow a order) := by
  have hone := GridBall.ofNat_encloses P 1
  rw [Nat.cast_one] at hone
  have harg := GridBall.sub_encloses (GridBall.inv_encloses (GridBall.sub_encloses hone hB))
    (GridBall.inv_encloses hB)
  have hE := IntervalBalls.expRangeBall_encloses (order := order)
    (show IntervalBalls.Encloses P ⟨_, _⟩ (RationalInterval.const ((1 - a)⁻¹ - a⁻¹)) from
      ⟨harg, harg⟩)
  exact IntervalBalls.divPositiveOrZero_encloses hE
    (IntervalBalls.add_encloses (IntervalBalls.const_encloses 1) hE)

/-- A ball `B` of `a` gives balls of `transitionHigh a order`. -/
theorem transitionHighBall_encloses {P order : ℕ} {B : GridBall} {a : ℚ} (hB : B.Encloses P a) :
    (transitionHighBall P order B).Encloses P (transitionHigh a order) := by
  have hone := GridBall.ofNat_encloses P 1
  rw [Nat.cast_one] at hone
  have harg := GridBall.sub_encloses (GridBall.inv_encloses hB)
    (GridBall.inv_encloses (GridBall.sub_encloses hone hB))
  have hE := IntervalBalls.expRangeBall_encloses (order := order)
    (show IntervalBalls.Encloses P ⟨_, _⟩ (RationalInterval.const (a⁻¹ - (1 - a)⁻¹)) from
      ⟨harg, harg⟩)
  exact IntervalBalls.divPositiveOrZero_encloses (IntervalBalls.const_encloses 1)
    (IntervalBalls.add_encloses (IntervalBalls.const_encloses 1) hE)

/-- Balls of `transitionPoint a order` from a ball `B` of `a`. -/
def transitionPointBall (P order : ℕ) (B : GridBall) : IntervalBalls :=
  IntervalBalls.splitBalls (GridBall.nonposCertain B) (GridBall.leCertain (GridBall.ofNat P 1) B)
    (GridBall.posCertain B && GridBall.ltCertain B (GridBall.ofNat P 1))
    (GridBall.leCertain B (GridBall.ofFrac P false 1 2))
    (GridBall.ltCertain (GridBall.ofFrac P false 1 2) B)
    (IntervalBalls.const P 0) (IntervalBalls.const P 1) (transitionLowBall P order B)
    (transitionHighBall P order B)

/-- A ball `B` of `a` gives balls of `transitionPoint a order`. -/
theorem transitionPointBall_encloses {P order : ℕ} {B : GridBall} {a : ℚ}
    (hB : B.Encloses P a) :
    (transitionPointBall P order B).Encloses P (transitionPoint a order) := by
  have hone := GridBall.ofNat_encloses P 1
  rw [Nat.cast_one] at hone
  have hhalf := (GridBall.ofFrac_encloses P 1 2).1
  simp only [Nat.cast_one, Nat.cast_ofNat] at hhalf
  exact IntervalBalls.splitBalls_encloses (GridBall.nonpos_of_nonposCertain hB)
    (GridBall.le_of_leCertain hone hB)
    (fun h ↦ by
      simp only [Bool.and_eq_true] at h
      exact ⟨GridBall.pos_of_posCertain hB h.1, GridBall.lt_of_ltCertain hB hone h.2⟩)
    (GridBall.le_of_leCertain hB hhalf) (GridBall.lt_of_ltCertain hhalf hB)
    (IntervalBalls.const_encloses 0) (IntervalBalls.const_encloses 1)
    (transitionLowBall_encloses hB) (transitionHighBall_encloses hB)

namespace IntervalBalls

/-- Balls of `transitionRange I order` from balls `S` of `I`. -/
def transitionRangeBall (P order : ℕ) (S : IntervalBalls) : IntervalBalls :=
  ends (transitionPointBall P order) S

/-- Balls `S` of `I` give balls of `transitionRange I order`. -/
theorem transitionRangeBall_encloses {P order : ℕ} {S : IntervalBalls} {I : RationalInterval}
    (hS : S.Encloses P I) : (transitionRangeBall P order S).Encloses P (transitionRange I order) :=
  ends_encloses (fun hB ↦ transitionPointBall_encloses hB) hS

/-- Balls of `transitionDerivRange k order p I` from balls `S` of `I`. -/
def transitionDerivBall (P k order : ℕ) (p : RationalInterval.PowerPrecision)
    (S : IntervalBalls) : IntervalBalls :=
  mul P (mul P (mul P (transitionRangeBall P order S)
      ((const P 1).sub (transitionRangeBall P order S)))
    (nestedRangeBall P (transitionNumerator k) (transitionRangeBall P order S) S))
    (rpowRatBall P p (transitionExponent k) (mul P S ((const P 1).sub S)))

/-- Balls `S` of `I` give balls of `transitionDerivRange k order p I`. -/
theorem transitionDerivBall_encloses {P k order : ℕ} {p : RationalInterval.PowerPrecision}
    {S : IntervalBalls} {I : RationalInterval} (hS : S.Encloses P I) :
    (transitionDerivBall P k order p S).Encloses P (transitionDerivRange k order p I) := by
  have hT := transitionRangeBall_encloses (order := order) hS
  exact mul_encloses (mul_encloses (mul_encloses hT (sub_encloses (const_encloses 1) hT))
    (nestedRangeBall_encloses _ hT hS))
    (rpowRatBall_encloses (mul_encloses hS (sub_encloses (const_encloses 1) hS)))

/-- Balls of `transitionFlatRange k order δ`. -/
def transitionFlatBall (P k order : ℕ) (δ : ℚ) : IntervalBalls :=
  let B := (mul P (const P (nestedNorm (transitionNumerator k)))
    (mul P (expRangeBall P order (const P (2 - 1 / δ))) (const P ((2 / δ) ^ (2 * k + 2))))).hi
  ⟨B.abs.neg, B.abs⟩

/-- `transitionFlatBall P k order δ` encloses `transitionFlatRange k order δ`. -/
theorem transitionFlatBall_encloses (P k order : ℕ) (δ : ℚ) :
    (transitionFlatBall P k order δ).Encloses P (transitionFlatRange k order δ) := by
  have hB := (mul_encloses (const_encloses (P := P) (nestedNorm (transitionNumerator k)))
    (mul_encloses (expRangeBall_encloses (order := order) (const_encloses (P := P) (2 - 1 / δ)))
      (const_encloses (P := P) ((2 / δ) ^ (2 * k + 2))))).2
  exact ⟨GridBall.neg_encloses (GridBall.abs_encloses hB), GridBall.abs_encloses hB⟩

end IntervalBalls

end CAS.Numerics
