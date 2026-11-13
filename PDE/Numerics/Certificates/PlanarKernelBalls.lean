/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarKernelConstants
public import CAS.Numerics.GridBallAtan
public import CAS.Numerics.GridBallSqrt

/-!
# Balls of the closed-form integrals of the planar Biot–Savart kernels

Balls on the grid `2 ^ -P` of the closed forms of `PotentialTheory.Planar` on rectangles with
rational corners. Each evaluator mirrors an exact rational interval (`*Range`, never evaluated)
that contains the real closed form (`*_sound`), and its ball encloses that interval
(`*Ball_encloses`); from a successful `checkBoundsCertain` the real integral lies between the two
bounds (`integral_rectangle_*_mem` and the neighbouring `*_mem` theorems). An invalid or undecided
ball fails every check, so a `*_mem` theorem never applies to it.

Measured in the fast profile (`cega [fast]`) at `P = bits = 200`, one rectangle costs about
`0.3` to `0.7` ms for `K₁` and `K₁ₛ` (one logarithm), `0.8` ms for `K₂` on a small cell away from
the pole and `10` ms on a rectangle of size one crossing an axis, `3` ms for `K₂ₛ` on a small cell,
`15` to `35` ms for `|K₂|` across the diagonal and for `∂ᵢG`, whose arctangent arguments are of
order one.

## Main definitions

* `atanAt`, `logAt`: FloatLib's arctangent and logarithm enclosures at a rational point, with
  `logAt q = {0}` for `q ≤ 0`, sound for `q ≥ 0` (`Real.log 0 = 0`). The series degree is chosen
  from the size of the argument for an accuracy of about `2 ^ -bits` (`atanDegree`, `logDegree`),
  so that the small arguments of small cells far from the pole need few terms.
* `kernelOneRange`: `∫_Q K₁ = -(1/4) log R` with one logarithm of the rational cross ratio
  `R = (b² + d²)(a² + c²) / ((a² + d²)(b² + c²))` (`cornerSum_log_eq_neg_log_crossRatio`), and
  `symmetrizedKernelOneRange`: `∫_Q K₁ₛ(x, ·) = -(1/4) log (R₁ R₄ / (R₂ R₃))` with one logarithm
  (`symmetrizedCornerSum_log_eq_neg_log_symmetrizedCrossRatio`).
* `kernelTwoRange`: `∫_Q K₂` with at most two arctangents of the rationals
  `Z = (b-a)(d-c)(ab-cd) / ((d² + ab)(c² + ab) + (b-a)² cd)` of the pieces of `Q` reflected into the
  closed first quadrant (`cornerSum_arctan_eq_arctan_quadrantArg`); `kernelTwoCornerRange` is the
  four-arctangent form, `symmetrizedKernelTwoRange` the alternating sum over `x - Q`, `x - R₀ Q`,
  `x - R₁ Q`, `x + Q`.
* `absKernelTwoRange`: `∫_Q |K₂|` on rectangles of the first quadrant, one arctangent with the sign
  of `K₂` off the diagonal and the clamp formula (one logarithm, six arctangents) across it;
  `squareAbsKernelTwoRange`: `F_diag`; `gradientZeroBall`: `∫_Q ∂ᵢG` on every rectangle, also
  around the pole (four logarithms and four arctangents).
* `halfPowerAt`, `halfPowerRange`: `f_s` at a rational point and, by monotonicity, on an interval,
  with `√2` from `sqrtPointInterval`; the positivity of the logarithm arguments and of `4√2` is a
  separate ball test (`halfPowerAtOk`); `kernelTwoHalfPowerRange`: the corner integral
  `∫₀^b (∫₀^a |K₂|) y₂^{1/2} dy₂`; `kernelTwoLowRange`: `C_{K₂,low}`; `halfPowerLimitRange`:
  `f_s(∞) = π / (2√2)`.

## Main results

* `integral_rectangle_hessianKernel_zero_one_mem`: certified bounds of `∫_Q K₁` from a successful
  ball check.
* `integral_rectangle_hessianKernel_zero_zero_mem`: certified bounds of `∫_Q K₂`.
* `integral_rectangle_symmetrizedKernel_zero_one_mem`: certified bounds of `∫_Q K₁ₛ(x, ·)` at a
  rational point when `x - Q`, `x - R₀ Q`, `x - R₁ Q`, `x + Q` avoid the origin.
* `integral_rectangle_symmetrizedKernel_zero_zero_mem`: the same for `∫_Q K₂ₛ(x, ·)`.
* `integral_rectangle_abs_hessianKernel_zero_zero_mem`: certified bounds of `∫_Q |K₂|` on a
  rectangle of the first quadrant.
* `integral_rectangle_gradientKernel_zero_mem`: certified bounds of `∫_Q ∂₁G` on every closed
  rectangle, also one containing the pole.
* `kernelTwoLow_mem`: certified bounds of `C_{K₂,low} = (1/2) log 2 - f_s(1)`.
* `integral_integral_abs_hessianKernel_zero_zero_mul_sqrt_mem`: certified bounds of
  `∫₀^b (∫₀^a |K₂|) y₂^{1/2} dy₂`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, supplementary
  material II, Section 5.1, (5.5), (5.10)-(5.12).
  <https://arxiv.org/abs/2305.05660v3>
* R. J. George, W. Adkisson and A. Anandkumar, "FloatLib: Verified Floating-Point Arithmetic in
  Lean", arXiv:2609.19352, 2026.
  <https://arxiv.org/abs/2609.19352>
  <https://github.com/lean-dojo/FloatLib>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis PotentialTheory.Planar
open CAS.Continuum (RationalInterval)

namespace CAS.Numerics.PlanarKernel

/-! ### Points -/

/-- The degree of the arctangent series at `q` for an absolute accuracy of about `2 ^ -bits`:
for `|q| ≤ 2 ^ -m`, `m ≥ 2`, the remainder `|q| ^ (2d + 3)` needs `d ≥ bits / (2m)`; otherwise
FloatLib reduces the argument to `|t| ≤ 1/2` and `d = bits / 2 + 1` suffices. -/
def atanDegree (bits : ℕ) (q : ℚ) : ℕ :=
  let m := Nat.log2 (q.den / q.num.natAbs)
  if m ≤ 1 then bits / 2 + 1 else bits / (2 * m) + 1

/-- FloatLib's arctangent enclosure at the rational `q`, accurate to about `2 ^ -bits`. -/
def atanAt (bits : ℕ) (q : ℚ) : RationalInterval :=
  RationalInterval.atanRangeWith (RationalInterval.const q) (atanDegree bits q)

/-- `atanAt bits q` contains `arctan q`. -/
theorem atanAt_sound (bits : ℕ) (q : ℚ) : (atanAt bits q).MemReal (Real.arctan q) :=
  RationalInterval.atanRangeWith_sound _ _ (RationalInterval.memReal_const q)

/-- Balls of `atanAt bits q` at precision `P`. -/
def atanAtBall (P bits : ℕ) (q : ℚ) : IntervalBalls :=
  atanBall P (atanDegree bits q) (GridBall.ofRat P q)

/-- `atanAtBall P bits q` encloses `atanAt bits q`. -/
theorem atanAtBall_encloses (P bits : ℕ) (q : ℚ) :
    (atanAtBall P bits q).Encloses P (atanAt bits q) := by
  have h := atanBall_encloses (d := atanDegree bits q) (GridBall.ofRat_encloses P q)
  refine ⟨?_, ?_⟩
  · rw [atanAt, atanRangeWith_lo]; exact h.1
  · rw [atanAt, atanRangeWith_hi]; exact h.2

/-- The number of logarithm terms at `q` for an absolute accuracy of about `2 ^ -bits`: on
`(1/2, 2)` the series runs in `t = (q - 1)/(q + 1)`, and for `|t| ≤ 2 ^ -m`, `m ≥ 2`,
`bits / (2m) + 1` terms suffice; otherwise the reduced `|t| ≤ 1/3` needs `bits / 2 + 1`. -/
def logDegree (bits : ℕ) (q : ℚ) : ℕ :=
  let t := (q - 1) / (q + 1)
  let m := Nat.log2 (t.den / t.num.natAbs)
  if 1 / 2 < q ∧ q < 2 ∧ 2 ≤ m then bits / (2 * m) + 1 else bits / 2 + 1

/-- FloatLib's logarithm enclosure at the rational `q > 0`, accurate to about `2 ^ -bits`, and
`{0}` for `q ≤ 0`. -/
def logAt (bits : ℕ) (q : ℚ) : RationalInterval :=
  if h : 0 < q then RationalInterval.logPointIntervalWith (logDegree bits q) q h
  else RationalInterval.const 0

/-- `logAt bits q` contains `log q` for `q ≥ 0` (Mathlib's `log 0 = 0`). -/
theorem logAt_sound (bits : ℕ) {q : ℚ} (hq : 0 ≤ q) : (logAt bits q).MemReal (Real.log q) := by
  unfold logAt
  split_ifs with h
  · exact RationalInterval.logPointIntervalWith_sound _ q h
  · have : q = 0 := le_antisymm (not_lt.mp h) hq
    subst this
    simpa using RationalInterval.memReal_const 0

/-- Balls of `logAt bits q` at precision `P`. -/
def logAtBall (P bits : ℕ) (q : ℚ) : IntervalBalls :=
  if 0 < q then IntervalBalls.logPointBall P (logDegree bits q) (GridBall.ofRat P q)
  else IntervalBalls.const P 0

/-- `logAtBall P bits q` encloses `logAt bits q`. -/
theorem logAtBall_encloses (P bits : ℕ) (q : ℚ) :
    (logAtBall P bits q).Encloses P (logAt bits q) := by
  unfold logAtBall logAt
  split_ifs with h
  · exact IntervalBalls.logPointBall_encloses (GridBall.ofRat_encloses P q) h
  · exact IntervalBalls.const_encloses 0

/-! ### `K₁` on rectangles -/

/-- The enclosure of `∫_Q K₁ = -(1/4) log R` with one logarithm. -/
def kernelOneRange (bits : ℕ) (a b c d : ℚ) : RationalInterval :=
  (RationalInterval.const (-1 / 4)).mul (logAt bits (crossRatio a b c d))

/-- On a rectangle `[a, b] × [c, d]` avoiding the origin, `kernelOneRange bits a b c d` contains the
corner sum of `-log (u² + v²) / 4`. -/
theorem kernelOneRange_sound (bits : ℕ) {a b c d : ℚ} (hab : a ≤ b) (hcd : c ≤ d)
    (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) :
    (kernelOneRange bits a b c d).MemReal
      (cornerSum (fun u v ↦ -Real.log (u ^ 2 + v ^ 2) / 4) a b c d) := by
  have h0' : (0 : ℝ) < a ∨ (b : ℝ) < 0 ∨ (0 : ℝ) < c ∨ (d : ℝ) < 0 := by
    rcases h0 with h | h | h | h <;> [left; (right; left); (right; right; left);
      (right; right; right)] <;> exact_mod_cast h
  rw [cornerSum_log_eq_neg_log_crossRatio (by exact_mod_cast hab) (by exact_mod_cast hcd) h0',
    show -Real.log (crossRatio (a : ℝ) b c d) / 4 =
      ((-1 / 4 : ℚ) : ℝ) * Real.log (crossRatio (a : ℝ) b c d) by push_cast; ring,
    ← cast_crossRatio]
  exact RationalInterval.mul_sound (RationalInterval.memReal_const _)
    (logAt_sound bits (by unfold crossRatio; positivity))

/-- Balls of `kernelOneRange bits a b c d`. -/
def kernelOneBall (P bits : ℕ) (a b c d : ℚ) : IntervalBalls :=
  IntervalBalls.constMul (-1 / 4) (logAtBall P bits (crossRatio a b c d))

/-- `kernelOneBall P bits a b c d` encloses `kernelOneRange bits a b c d`. -/
theorem kernelOneBall_encloses (P bits : ℕ) (a b c d : ℚ) :
    (kernelOneBall P bits a b c d).Encloses P (kernelOneRange bits a b c d) :=
  IntervalBalls.constMul_encloses (logAtBall_encloses P bits _) _

/-- If `S` encloses `I`, `x ∈ I` and the ball check `checkBoundsCertain P (lo, hi) S` succeeds, then
`lo ≤ x ≤ hi`. -/
private theorem mem_of_check {P : ℕ} {S : IntervalBalls} {I : RationalInterval} {x : ℝ}
    (hS : S.Encloses P I) (hx : I.MemReal x) {lo hi : ℚ}
    (h : IntervalBalls.checkBoundsCertain P (lo, hi) S = true) : (lo : ℝ) ≤ x ∧ x ≤ hi := by
  have hb := IntervalBalls.checkBounds_of_certain hS h
  simp only [RationalInterval.checkBounds, Bool.and_eq_true, decide_eq_true_eq] at hb
  exact ⟨(Rat.cast_le.mpr hb.1).trans hx.1, hx.2.trans (Rat.cast_le.mpr hb.2)⟩

/-- **Certified bounds of `∫_Q K₁`** from a successful ball check. -/
theorem integral_rectangle_hessianKernel_zero_one_mem {a b c d : ℚ} (hab : a ≤ b) (hcd : c ≤ d)
    (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) {P bits : ℕ} {lo hi : ℚ}
    (h : IntervalBalls.checkBoundsCertain P (lo, hi) (kernelOneBall P bits a b c d) = true) :
    (lo : ℝ) ≤ ∫ y in coordinateRectangle a b c d, hessianKernel 0 1 y ∧
      ∫ y in coordinateRectangle a b c d, hessianKernel 0 1 y ≤ hi := by
  have h0' : (0 : ℝ) < a ∨ (b : ℝ) < 0 ∨ (0 : ℝ) < c ∨ (d : ℝ) < 0 := by
    rcases h0 with h | h | h | h <;> [left; (right; left); (right; right; left);
      (right; right; right)] <;> exact_mod_cast h
  rw [integral_rectangle_hessianKernel_zero_one_eq_cornerSum (by exact_mod_cast hab)
    (by exact_mod_cast hcd) h0']
  exact mem_of_check (kernelOneBall_encloses P bits a b c d)
    (kernelOneRange_sound bits hab hcd h0) h

/-! ### `K₂` on rectangles -/

/-- The enclosure of `∫_Q K₂ = (1/2) Σ ± arctan (u / v)` from the four corner arctangents. Its
arguments are of order one, so it needs the full series degree; `kernelTwoRange` uses at most two
arctangents of small arguments instead. -/
def kernelTwoCornerRange (bits : ℕ) (a b c d : ℚ) : RationalInterval :=
  (RationalInterval.const (1 / 2)).mul ((((atanAt bits (b / d)).sub (atanAt bits (a / d))).sub
    (atanAt bits (b / c))).add (atanAt bits (a / c)))

/-- `kernelTwoCornerRange bits a b c d` contains the corner sum of `arctan (u / v) / 2` over
`[a, b] × [c, d]`. -/
theorem kernelTwoCornerRange_sound (bits : ℕ) (a b c d : ℚ) :
    (kernelTwoCornerRange bits a b c d).MemReal
      (cornerSum (fun u v ↦ Real.arctan (u / v) / 2) a b c d) := by
  have h := RationalInterval.mul_sound (RationalInterval.memReal_const (1 / 2))
    (RationalInterval.add_sound (RationalInterval.sub_sound (RationalInterval.sub_sound
      (atanAt_sound bits (b / d)) (atanAt_sound bits (a / d))) (atanAt_sound bits (b / c)))
      (atanAt_sound bits (a / c)))
  have e : cornerSum (fun u v ↦ Real.arctan (u / v) / 2) a b c d =
      ((1 / 2 : ℚ) : ℝ) * (Real.arctan ((b / d : ℚ) : ℝ) - Real.arctan ((a / d : ℚ) : ℝ) -
        Real.arctan ((b / c : ℚ) : ℝ) + Real.arctan ((a / c : ℚ) : ℝ)) := by
    push_cast
    unfold cornerSum
    ring
  rw [e]
  exact h

/-- Balls of `kernelTwoCornerRange bits a b c d`. -/
def kernelTwoCornerBall (P bits : ℕ) (a b c d : ℚ) : IntervalBalls :=
  IntervalBalls.constMul (1 / 2) ((((atanAtBall P bits (b / d)).sub
    (atanAtBall P bits (a / d))).sub (atanAtBall P bits (b / c))).add
    (atanAtBall P bits (a / c)))

/-- `kernelTwoCornerBall P bits a b c d` encloses `kernelTwoCornerRange bits a b c d`. -/
theorem kernelTwoCornerBall_encloses (P bits : ℕ) (a b c d : ℚ) :
    (kernelTwoCornerBall P bits a b c d).Encloses P (kernelTwoCornerRange bits a b c d) :=
  IntervalBalls.constMul_encloses (IntervalBalls.add_encloses (IntervalBalls.sub_encloses
    (IntervalBalls.sub_encloses (atanAtBall_encloses P bits _) (atanAtBall_encloses P bits _))
    (atanAtBall_encloses P bits _)) (atanAtBall_encloses P bits _)) _

/-- The enclosure of `∫_Q K₂ = (1/2) arctan Z` on rectangles of the first quadrant. -/
def kernelTwoQuadrantRange (bits : ℕ) (a b c d : ℚ) : RationalInterval :=
  (RationalInterval.const (1 / 2)).mul (atanAt bits (quadrantArg a b c d))

/-- On a rectangle of the closed first quadrant with `0 < a` or `0 < c`, `kernelTwoQuadrantRange`
contains the corner sum of `arctan (u / v) / 2`. -/
theorem kernelTwoQuadrantRange_sound (bits : ℕ) {a b c d : ℚ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hc : 0 ≤ c) (hcd : c ≤ d) (h0 : 0 < a ∨ 0 < c) :
    (kernelTwoQuadrantRange bits a b c d).MemReal
      (cornerSum (fun u v ↦ Real.arctan (u / v) / 2) a b c d) := by
  have h0' : (0 : ℝ) < a ∨ (0 : ℝ) < c := by
    rcases h0 with h | h <;> [left; right] <;> exact_mod_cast h
  rw [cornerSum_arctan_eq_arctan_quadrantArg (by exact_mod_cast ha) (by exact_mod_cast hab)
    (by exact_mod_cast hc) (by exact_mod_cast hcd) h0', ← cast_quadrantArg,
    show Real.arctan ((quadrantArg a b c d : ℚ) : ℝ) / 2 =
      ((1 / 2 : ℚ) : ℝ) * Real.arctan ((quadrantArg a b c d : ℚ) : ℝ) by push_cast; ring]
  exact RationalInterval.mul_sound (RationalInterval.memReal_const _) (atanAt_sound bits _)

/-- Balls of `kernelTwoQuadrantRange bits a b c d`. -/
def kernelTwoQuadrantBall (P bits : ℕ) (a b c d : ℚ) : IntervalBalls :=
  IntervalBalls.constMul (1 / 2) (atanAtBall P bits (quadrantArg a b c d))

/-- `kernelTwoQuadrantBall P bits a b c d` encloses `kernelTwoQuadrantRange bits a b c d`. -/
theorem kernelTwoQuadrantBall_encloses (P bits : ℕ) (a b c d : ℚ) :
    (kernelTwoQuadrantBall P bits a b c d).Encloses P (kernelTwoQuadrantRange bits a b c d) :=
  IntervalBalls.constMul_encloses (atanAtBall_encloses P bits _) _

/-- The corner sum of `arctan (u / v) / 2` is unchanged when `[a, b]` is reflected to `[-b, -a]` in
the first variable. -/
private theorem cornerSum_arctan_neg_left (a b c d : ℝ) :
    cornerSum (fun u v ↦ Real.arctan (u / v) / 2) (-b) (-a) c d =
      cornerSum (fun u v ↦ Real.arctan (u / v) / 2) a b c d := by
  simp only [cornerSum, neg_div, Real.arctan_neg]; ring

/-- The corner sum of `arctan (u / v) / 2` is unchanged when `[c, d]` is reflected to `[-d, -c]` in
the second variable. -/
private theorem cornerSum_arctan_neg_right (a b c d : ℝ) :
    cornerSum (fun u v ↦ Real.arctan (u / v) / 2) a b (-d) (-c) =
      cornerSum (fun u v ↦ Real.arctan (u / v) / 2) a b c d := by
  simp only [cornerSum, div_neg, Real.arctan_neg]; ring

/-- The corner sum of `arctan (u / v) / 2` over `[a, b] × [0, -c]` equals the one over
`[a, b] × [c, 0]`. -/
private theorem cornerSum_arctan_zero_neg_right (a b c : ℝ) :
    cornerSum (fun u v ↦ Real.arctan (u / v) / 2) a b 0 (-c) =
      cornerSum (fun u v ↦ Real.arctan (u / v) / 2) a b c 0 := by
  simp only [cornerSum, div_neg, div_zero, Real.arctan_neg, Real.arctan_zero]; ring

/-- The corner sum of `arctan (u / v) / 2` over `[0, -a] × [c, d]` equals the one over
`[a, 0] × [c, d]`. -/
private theorem cornerSum_arctan_zero_neg_left (a c d : ℝ) :
    cornerSum (fun u v ↦ Real.arctan (u / v) / 2) 0 (-a) c d =
      cornerSum (fun u v ↦ Real.arctan (u / v) / 2) a 0 c d := by
  simp only [cornerSum, neg_div, zero_div, Real.arctan_neg, Real.arctan_zero]; ring

/-- Corner sums add up over the split of `[a, b]` into `[a, m]` and `[m, b]` in the first variable.
-/
private theorem cornerSum_split_left (H : ℝ → ℝ → ℝ) (a m b c d : ℝ) :
    cornerSum H a b c d = cornerSum H a m c d + cornerSum H m b c d := by
  unfold cornerSum; ring

/-- Corner sums add up over the split of `[c, d]` into `[c, m]` and `[m, d]` in the second variable.
-/
private theorem cornerSum_split_right (H : ℝ → ℝ → ℝ) (a b c m d : ℝ) :
    cornerSum H a b c d = cornerSum H a b c m + cornerSum H a b m d := by
  unfold cornerSum; ring

/-- The enclosure of `∫_Q K₂` on a rectangle avoiding the origin with at most two arctangents:
reflected across the axes (`K₂` is even in each coordinate) and split on an axis it crosses, `Q`
becomes at most two rectangles of the closed first quadrant, each with one arctangent of the
rational `quadrantArg`. -/
def kernelTwoRange (bits : ℕ) (a b c d : ℚ) : RationalInterval :=
  if 0 ≤ a then
    if 0 ≤ c then kernelTwoQuadrantRange bits a b c d
    else if d ≤ 0 then kernelTwoQuadrantRange bits a b (-d) (-c)
    else (kernelTwoQuadrantRange bits a b 0 (-c)).add (kernelTwoQuadrantRange bits a b 0 d)
  else if b ≤ 0 then
    if 0 ≤ c then kernelTwoQuadrantRange bits (-b) (-a) c d
    else if d ≤ 0 then kernelTwoQuadrantRange bits (-b) (-a) (-d) (-c)
    else (kernelTwoQuadrantRange bits (-b) (-a) 0 (-c)).add
      (kernelTwoQuadrantRange bits (-b) (-a) 0 d)
  else
    if 0 ≤ c then (kernelTwoQuadrantRange bits 0 (-a) c d).add (kernelTwoQuadrantRange bits 0 b c d)
    else if d ≤ 0 then (kernelTwoQuadrantRange bits 0 (-a) (-d) (-c)).add
      (kernelTwoQuadrantRange bits 0 b (-d) (-c))
    else kernelTwoCornerRange bits a b c d

/-- On a rectangle `[a, b] × [c, d]` avoiding the origin, `kernelTwoRange bits a b c d` contains the
corner sum of `arctan (u / v) / 2`. -/
theorem kernelTwoRange_sound (bits : ℕ) {a b c d : ℚ} (hab : a ≤ b) (hcd : c ≤ d)
    (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) :
    (kernelTwoRange bits a b c d).MemReal
      (cornerSum (fun u v ↦ Real.arctan (u / v) / 2) a b c d) := by
  have Qs : ∀ p q r s : ℚ, 0 ≤ p → p ≤ q → 0 ≤ r → r ≤ s → (0 < p ∨ 0 < r) →
      (kernelTwoQuadrantRange bits p q r s).MemReal
        (cornerSum (fun u v ↦ Real.arctan (u / v) / 2) p q r s) :=
    fun p q r s hp hpq hr hrs h ↦ kernelTwoQuadrantRange_sound bits hp hpq hr hrs h
  unfold kernelTwoRange
  split_ifs with ha hc hd hb hc hd hc hd
  · exact Qs a b c d ha hab hc hcd (by
      rcases lt_or_eq_of_le ha with h' | h'
      · exact Or.inl h'
      · right; rcases h0 with h | h | h | h <;> linarith)
  · have := Qs a b (-d) (-c) ha hab (by linarith) (by linarith) (by
      rcases lt_or_eq_of_le ha with h' | h'
      · exact Or.inl h'
      · right; rcases h0 with h | h | h | h <;> linarith)
    push_cast at this
    rwa [cornerSum_arctan_neg_right] at this
  · rw [cornerSum_split_right (fun u v ↦ Real.arctan (u / v) / 2) a b c 0 d]
    have ha' : 0 < a := by
      rcases h0 with h | h | h | h <;> linarith
    have h1 := Qs a b 0 (-c) ha hab le_rfl (by linarith) (Or.inl ha')
    have h2 := Qs a b 0 d ha hab le_rfl (by linarith) (Or.inl ha')
    push_cast at h1 h2
    rw [cornerSum_arctan_zero_neg_right] at h1
    exact RationalInterval.add_sound h1 h2
  · have := Qs (-b) (-a) c d (by linarith) (by linarith) hc hcd (by
      rcases lt_or_eq_of_le (neg_nonneg.mpr hb) with h' | h'
      · exact Or.inl h'
      · right; rcases h0 with h | h | h | h <;> linarith)
    push_cast at this
    rwa [cornerSum_arctan_neg_left] at this
  · have := Qs (-b) (-a) (-d) (-c) (by linarith) (by linarith) (by linarith) (by linarith) (by
      rcases lt_or_eq_of_le (neg_nonneg.mpr hb) with h' | h'
      · exact Or.inl h'
      · right; rcases h0 with h | h | h | h <;> linarith)
    push_cast at this
    rwa [cornerSum_arctan_neg_left, cornerSum_arctan_neg_right] at this
  · rw [cornerSum_split_right (fun u v ↦ Real.arctan (u / v) / 2) a b c 0 d]
    have hb' : b < 0 := by
      rcases h0 with h | h | h | h <;> linarith
    have h1 := Qs (-b) (-a) 0 (-c) (by linarith) (by linarith) le_rfl (by linarith)
      (Or.inl (by linarith))
    have h2 := Qs (-b) (-a) 0 d (by linarith) (by linarith) le_rfl (by linarith)
      (Or.inl (by linarith))
    push_cast at h1 h2
    rw [cornerSum_arctan_zero_neg_right, cornerSum_arctan_neg_left] at h1
    rw [cornerSum_arctan_neg_left] at h2
    exact RationalInterval.add_sound h1 h2
  · rw [cornerSum_split_left (fun u v ↦ Real.arctan (u / v) / 2) a 0 b c d]
    have hc' : 0 < c := by
      rcases h0 with h | h | h | h <;> linarith
    have h1 := Qs 0 (-a) c d le_rfl (by linarith) hc hcd (Or.inr hc')
    have h2 := Qs 0 b c d le_rfl (by linarith) hc hcd (Or.inr hc')
    push_cast at h1 h2
    rw [cornerSum_arctan_zero_neg_left] at h1
    exact RationalInterval.add_sound h1 h2
  · rw [cornerSum_split_left (fun u v ↦ Real.arctan (u / v) / 2) a 0 b c d]
    have hd' : d < 0 := by
      rcases h0 with h | h | h | h <;> linarith
    have h1 := Qs 0 (-a) (-d) (-c) le_rfl (by linarith) (by linarith) (by linarith)
      (Or.inr (by linarith))
    have h2 := Qs 0 b (-d) (-c) le_rfl (by linarith) (by linarith) (by linarith)
      (Or.inr (by linarith))
    push_cast at h1 h2
    rw [cornerSum_arctan_zero_neg_left, cornerSum_arctan_neg_right] at h1
    rw [cornerSum_arctan_neg_right] at h2
    exact RationalInterval.add_sound h1 h2
  · exact kernelTwoCornerRange_sound bits a b c d

/-- Balls of `kernelTwoRange bits a b c d`. -/
def kernelTwoBall (P bits : ℕ) (a b c d : ℚ) : IntervalBalls :=
  if 0 ≤ a then
    if 0 ≤ c then kernelTwoQuadrantBall P bits a b c d
    else if d ≤ 0 then kernelTwoQuadrantBall P bits a b (-d) (-c)
    else (kernelTwoQuadrantBall P bits a b 0 (-c)).add (kernelTwoQuadrantBall P bits a b 0 d)
  else if b ≤ 0 then
    if 0 ≤ c then kernelTwoQuadrantBall P bits (-b) (-a) c d
    else if d ≤ 0 then kernelTwoQuadrantBall P bits (-b) (-a) (-d) (-c)
    else (kernelTwoQuadrantBall P bits (-b) (-a) 0 (-c)).add
      (kernelTwoQuadrantBall P bits (-b) (-a) 0 d)
  else
    if 0 ≤ c then (kernelTwoQuadrantBall P bits 0 (-a) c d).add
      (kernelTwoQuadrantBall P bits 0 b c d)
    else if d ≤ 0 then (kernelTwoQuadrantBall P bits 0 (-a) (-d) (-c)).add
      (kernelTwoQuadrantBall P bits 0 b (-d) (-c))
    else kernelTwoCornerBall P bits a b c d

/-- `kernelTwoBall P bits a b c d` encloses `kernelTwoRange bits a b c d`. -/
theorem kernelTwoBall_encloses (P bits : ℕ) (a b c d : ℚ) :
    (kernelTwoBall P bits a b c d).Encloses P (kernelTwoRange bits a b c d) := by
  have Q := kernelTwoQuadrantBall_encloses P bits
  unfold kernelTwoBall kernelTwoRange
  split_ifs
  all_goals first
    | exact Q _ _ _ _
    | exact IntervalBalls.add_encloses (Q _ _ _ _) (Q _ _ _ _)
    | exact kernelTwoCornerBall_encloses P bits a b c d

/-- **Certified bounds of `∫_Q K₂`** from a successful ball check. -/
theorem integral_rectangle_hessianKernel_zero_zero_mem {a b c d : ℚ} (hab : a ≤ b)
    (hcd : c ≤ d) (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) {P bits : ℕ} {lo hi : ℚ}
    (h : IntervalBalls.checkBoundsCertain P (lo, hi) (kernelTwoBall P bits a b c d) = true) :
    (lo : ℝ) ≤ ∫ y in coordinateRectangle a b c d, hessianKernel 0 0 y ∧
      ∫ y in coordinateRectangle a b c d, hessianKernel 0 0 y ≤ hi := by
  have h0' : (0 : ℝ) < a ∨ (b : ℝ) < 0 ∨ (0 : ℝ) < c ∨ (d : ℝ) < 0 := by
    rcases h0 with h | h | h | h <;> [left; (right; left); (right; right; left);
      (right; right; right)] <;> exact_mod_cast h
  rw [integral_rectangle_hessianKernel_zero_zero_eq_cornerSum (by exact_mod_cast hab)
    (by exact_mod_cast hcd) h0']
  exact mem_of_check (kernelTwoBall_encloses P bits a b c d)
    (kernelTwoRange_sound bits hab hcd h0) h

/-! ### Symmetrized kernels -/

/-- The enclosure of `∫_Q K₁ₛ(x, ·) = -(1/4) log (R₁ R₄ / (R₂ R₃))` with one logarithm. -/
def symmetrizedKernelOneRange (bits : ℕ) (x₀ x₁ a b c d : ℚ) : RationalInterval :=
  (RationalInterval.const (-1 / 4)).mul (logAt bits (symmetrizedCrossRatio x₀ x₁ a b c d))

/-- Balls of `symmetrizedKernelOneRange bits x₀ x₁ a b c d`. -/
def symmetrizedKernelOneBall (P bits : ℕ) (x₀ x₁ a b c d : ℚ) : IntervalBalls :=
  IntervalBalls.constMul (-1 / 4) (logAtBall P bits (symmetrizedCrossRatio x₀ x₁ a b c d))

/-- `symmetrizedKernelOneBall P bits x₀ x₁ a b c d` encloses
`symmetrizedKernelOneRange bits x₀ x₁ a b c d`. -/
theorem symmetrizedKernelOneBall_encloses (P bits : ℕ) (x₀ x₁ a b c d : ℚ) :
    (symmetrizedKernelOneBall P bits x₀ x₁ a b c d).Encloses P
      (symmetrizedKernelOneRange bits x₀ x₁ a b c d) :=
  IntervalBalls.constMul_encloses (logAtBall_encloses P bits _) _

/-- The condition that `[a, b] × [c, d]` avoids the origin passes from `ℚ` to `ℝ`. -/
private theorem cast_avoids {a b c d : ℚ} (h : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) :
    (0 : ℝ) < a ∨ (b : ℝ) < 0 ∨ (0 : ℝ) < c ∨ (d : ℝ) < 0 := by
  rcases h with h | h | h | h <;> [left; (right; left); (right; right; left);
    (right; right; right)] <;> exact_mod_cast h

/-- **Certified bounds of `∫_Q K₁ₛ(x, ·)`** at a rational point `x = (x₀, x₁)` from a successful
ball check, when the four rectangles `x - Q`, `x - R₀ Q`, `x - R₁ Q`, `x + Q` avoid the origin. -/
theorem integral_rectangle_symmetrizedKernel_zero_one_mem {x₀ x₁ a b c d : ℚ} (hab : a ≤ b)
    (hcd : c ≤ d) (h₁ : 0 < x₀ - b ∨ x₀ - a < 0 ∨ 0 < x₁ - d ∨ x₁ - c < 0)
    (h₂ : 0 < x₀ + a ∨ x₀ + b < 0 ∨ 0 < x₁ - d ∨ x₁ - c < 0)
    (h₃ : 0 < x₀ - b ∨ x₀ - a < 0 ∨ 0 < x₁ + c ∨ x₁ + d < 0)
    (h₄ : 0 < x₀ + a ∨ x₀ + b < 0 ∨ 0 < x₁ + c ∨ x₁ + d < 0) {P bits : ℕ} {lo hi : ℚ}
    (h : IntervalBalls.checkBoundsCertain P (lo, hi)
      (symmetrizedKernelOneBall P bits x₀ x₁ a b c d) = true) :
    (lo : ℝ) ≤ ∫ y in coordinateRectangle a b c d,
        GreenFunction.symmetrizedKernel (hessianKernel 0 1) !₂[(x₀ : ℝ), x₁] y ∧
      ∫ y in coordinateRectangle a b c d,
        GreenFunction.symmetrizedKernel (hessianKernel 0 1) !₂[(x₀ : ℝ), x₁] y ≤ hi := by
  have c₁ := cast_avoids h₁; have c₂ := cast_avoids h₂
  have c₃ := cast_avoids h₃; have c₄ := cast_avoids h₄
  push_cast at c₁ c₂ c₃ c₄
  have hx0 : (!₂[(x₀ : ℝ), x₁] : ℝ^2) 0 = x₀ := by simp
  have hx1 : (!₂[(x₀ : ℝ), x₁] : ℝ^2) 1 = x₁ := by simp
  rw [integral_rectangle_symmetrizedKernel_zero_one _ (by exact_mod_cast hab)
    (by exact_mod_cast hcd) (by rw [hx0, hx1]; exact c₁) (by rw [hx0, hx1]; exact c₂)
    (by rw [hx0, hx1]; exact c₃) (by rw [hx0, hx1]; exact c₄),
    symmetrizedCornerSum_log_eq_neg_log_symmetrizedCrossRatio (by exact_mod_cast hab)
      (by exact_mod_cast hcd)
      (by rw [hx0, hx1]; exact c₁) (by rw [hx0, hx1]; exact c₂) (by rw [hx0, hx1]; exact c₃)
      (by rw [hx0, hx1]; exact c₄), hx0, hx1]
  have hcast : ((symmetrizedCrossRatio x₀ x₁ a b c d : ℚ) : ℝ) =
      symmetrizedCrossRatio (x₀ : ℝ) x₁ a b c d := by simp [symmetrizedCrossRatio, crossRatio]
  have hpos : 0 ≤ symmetrizedCrossRatio x₀ x₁ a b c d := by
    have := (show (0 : ℝ) < symmetrizedCrossRatio (x₀ : ℝ) x₁ a b c d by
      have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
      have hcd' : (c : ℝ) ≤ d := by exact_mod_cast hcd
      have e₁ : (x₀ : ℝ) - b ≤ x₀ - a := by linarith
      have e₂ : (x₁ : ℝ) - d ≤ x₁ - c := by linarith
      have e₃ : (x₀ : ℝ) + a ≤ x₀ + b := by linarith
      have e₄ : (x₁ : ℝ) + c ≤ x₁ + d := by linarith
      unfold symmetrizedCrossRatio
      have := crossRatio_pos e₁ e₂ c₁; have := crossRatio_pos e₃ e₂ c₂
      have := crossRatio_pos e₁ e₄ c₃; have := crossRatio_pos e₃ e₄ c₄
      positivity)
    rw [← hcast] at this
    exact_mod_cast this.le
  have hs : (symmetrizedKernelOneRange bits x₀ x₁ a b c d).MemReal
      (-Real.log (symmetrizedCrossRatio (x₀ : ℝ) x₁ a b c d) / 4) := by
    rw [show -Real.log (symmetrizedCrossRatio (x₀ : ℝ) x₁ a b c d) / 4 =
      ((-1 / 4 : ℚ) : ℝ) * Real.log ((symmetrizedCrossRatio x₀ x₁ a b c d : ℚ) : ℝ) by
        rw [hcast]; push_cast; ring]
    exact RationalInterval.mul_sound (RationalInterval.memReal_const _) (logAt_sound bits hpos)
  exact mem_of_check (symmetrizedKernelOneBall_encloses P bits x₀ x₁ a b c d) hs h

/-- The enclosure of `∫_Q K₂ₛ(x, ·)`: the alternating sum of the four rectangle enclosures. -/
def symmetrizedKernelTwoRange (bits : ℕ) (x₀ x₁ a b c d : ℚ) : RationalInterval :=
  (((kernelTwoRange bits (x₀ - b) (x₀ - a) (x₁ - d) (x₁ - c)).sub
    (kernelTwoRange bits (x₀ + a) (x₀ + b) (x₁ - d) (x₁ - c))).sub
    (kernelTwoRange bits (x₀ - b) (x₀ - a) (x₁ + c) (x₁ + d))).add
    (kernelTwoRange bits (x₀ + a) (x₀ + b) (x₁ + c) (x₁ + d))

/-- Balls of `symmetrizedKernelTwoRange bits x₀ x₁ a b c d`. -/
def symmetrizedKernelTwoBall (P bits : ℕ) (x₀ x₁ a b c d : ℚ) : IntervalBalls :=
  (((kernelTwoBall P bits (x₀ - b) (x₀ - a) (x₁ - d) (x₁ - c)).sub
    (kernelTwoBall P bits (x₀ + a) (x₀ + b) (x₁ - d) (x₁ - c))).sub
    (kernelTwoBall P bits (x₀ - b) (x₀ - a) (x₁ + c) (x₁ + d))).add
    (kernelTwoBall P bits (x₀ + a) (x₀ + b) (x₁ + c) (x₁ + d))

/-- `symmetrizedKernelTwoBall P bits x₀ x₁ a b c d` encloses
`symmetrizedKernelTwoRange bits x₀ x₁ a b c d`. -/
theorem symmetrizedKernelTwoBall_encloses (P bits : ℕ) (x₀ x₁ a b c d : ℚ) :
    (symmetrizedKernelTwoBall P bits x₀ x₁ a b c d).Encloses P
      (symmetrizedKernelTwoRange bits x₀ x₁ a b c d) :=
  IntervalBalls.add_encloses (IntervalBalls.sub_encloses (IntervalBalls.sub_encloses
    (kernelTwoBall_encloses _ _ _ _ _ _) (kernelTwoBall_encloses _ _ _ _ _ _))
    (kernelTwoBall_encloses _ _ _ _ _ _)) (kernelTwoBall_encloses _ _ _ _ _ _)

/-- When the four rectangles `x - Q`, `x - R₀ Q`, `x - R₁ Q`, `x + Q` avoid the origin,
`symmetrizedKernelTwoRange` contains the symmetrized corner sum of `arctan (u / v) / 2` at
`x = (x₀, x₁)`. -/
theorem symmetrizedKernelTwoRange_sound (bits : ℕ) {x₀ x₁ a b c d : ℚ} (hab : a ≤ b)
    (hcd : c ≤ d) (h₁ : 0 < x₀ - b ∨ x₀ - a < 0 ∨ 0 < x₁ - d ∨ x₁ - c < 0)
    (h₂ : 0 < x₀ + a ∨ x₀ + b < 0 ∨ 0 < x₁ - d ∨ x₁ - c < 0)
    (h₃ : 0 < x₀ - b ∨ x₀ - a < 0 ∨ 0 < x₁ + c ∨ x₁ + d < 0)
    (h₄ : 0 < x₀ + a ∨ x₀ + b < 0 ∨ 0 < x₁ + c ∨ x₁ + d < 0) :
    (symmetrizedKernelTwoRange bits x₀ x₁ a b c d).MemReal
      (symmetrizedCornerSum (fun u v ↦ Real.arctan (u / v) / 2) !₂[(x₀ : ℝ), x₁] a b c d) := by
  have h := RationalInterval.add_sound (RationalInterval.sub_sound (RationalInterval.sub_sound
    (kernelTwoRange_sound bits (by linarith) (by linarith) h₁)
    (kernelTwoRange_sound bits (by linarith) (by linarith) h₂))
    (kernelTwoRange_sound bits (by linarith) (by linarith) h₃))
    (kernelTwoRange_sound bits (by linarith) (by linarith) h₄)
  push_cast at h
  have hx0 : (!₂[(x₀ : ℝ), x₁] : ℝ^2) 0 = x₀ := by simp
  have hx1 : (!₂[(x₀ : ℝ), x₁] : ℝ^2) 1 = x₁ := by simp
  rw [symmetrizedCornerSum, hx0, hx1]
  exact h

/-- **Certified bounds of `∫_Q K₂ₛ(x, ·)`** at a rational point `x = (x₀, x₁)` from a successful
ball check, when the four rectangles `x - Q`, `x - R₀ Q`, `x - R₁ Q`, `x + Q` avoid the origin. -/
theorem integral_rectangle_symmetrizedKernel_zero_zero_mem {x₀ x₁ a b c d : ℚ} (hab : a ≤ b)
    (hcd : c ≤ d) (h₁ : 0 < x₀ - b ∨ x₀ - a < 0 ∨ 0 < x₁ - d ∨ x₁ - c < 0)
    (h₂ : 0 < x₀ + a ∨ x₀ + b < 0 ∨ 0 < x₁ - d ∨ x₁ - c < 0)
    (h₃ : 0 < x₀ - b ∨ x₀ - a < 0 ∨ 0 < x₁ + c ∨ x₁ + d < 0)
    (h₄ : 0 < x₀ + a ∨ x₀ + b < 0 ∨ 0 < x₁ + c ∨ x₁ + d < 0) {P bits : ℕ} {lo hi : ℚ}
    (h : IntervalBalls.checkBoundsCertain P (lo, hi)
      (symmetrizedKernelTwoBall P bits x₀ x₁ a b c d) = true) :
    (lo : ℝ) ≤ ∫ y in coordinateRectangle a b c d,
        GreenFunction.symmetrizedKernel (hessianKernel 0 0) !₂[(x₀ : ℝ), x₁] y ∧
      ∫ y in coordinateRectangle a b c d,
        GreenFunction.symmetrizedKernel (hessianKernel 0 0) !₂[(x₀ : ℝ), x₁] y ≤ hi := by
  have c₁ := cast_avoids h₁; have c₂ := cast_avoids h₂
  have c₃ := cast_avoids h₃; have c₄ := cast_avoids h₄
  push_cast at c₁ c₂ c₃ c₄
  have hx0 : (!₂[(x₀ : ℝ), x₁] : ℝ^2) 0 = x₀ := by simp
  have hx1 : (!₂[(x₀ : ℝ), x₁] : ℝ^2) 1 = x₁ := by simp
  rw [integral_rectangle_symmetrizedKernel_zero_zero _ (by exact_mod_cast hab)
    (by exact_mod_cast hcd) (by rw [hx0, hx1]; exact c₁) (by rw [hx0, hx1]; exact c₂)
    (by rw [hx0, hx1]; exact c₃) (by rw [hx0, hx1]; exact c₄)]
  exact mem_of_check (symmetrizedKernelTwoBall_encloses P bits x₀ x₁ a b c d)
    (symmetrizedKernelTwoRange_sound bits hab hcd h₁ h₂ h₃ h₄) h

/-! ### `|K₂|` on rectangles of the first quadrant -/

/-- The enclosure of the clamp formula for `∫_Q |K₂|` on a rectangle of the first quadrant
(`integral_rectangle_abs_hessianKernel_zero_zero`): one logarithm and six arctangents. -/
def absKernelTwoClampRange (bits : ℕ) (a b c d : ℚ) : RationalInterval :=
  let p := max a (min c b)
  let q := max a (min d b)
  (((((RationalInterval.const (1 / 2)).mul (logAt bits (q / p))).add (atanAt bits (p / c))).sub
    ((RationalInterval.const (1 / 2)).mul ((atanAt bits (a / c)).add (atanAt bits (b / c))))).add
    ((RationalInterval.const (1 / 2)).mul ((atanAt bits (a / d)).add (atanAt bits (b / d))))).sub
    (atanAt bits (q / d))

/-- Balls of `absKernelTwoClampRange bits a b c d`. -/
def absKernelTwoClampBall (P bits : ℕ) (a b c d : ℚ) : IntervalBalls :=
  let p := max a (min c b)
  let q := max a (min d b)
  ((((IntervalBalls.constMul (1 / 2) (logAtBall P bits (q / p))).add
    (atanAtBall P bits (p / c))).sub (IntervalBalls.constMul (1 / 2)
      ((atanAtBall P bits (a / c)).add (atanAtBall P bits (b / c))))).add
    (IntervalBalls.constMul (1 / 2) ((atanAtBall P bits (a / d)).add
      (atanAtBall P bits (b / d))))).sub (atanAtBall P bits (q / d))

/-- `absKernelTwoClampBall P bits a b c d` encloses `absKernelTwoClampRange bits a b c d`. -/
theorem absKernelTwoClampBall_encloses (P bits : ℕ) (a b c d : ℚ) :
    (absKernelTwoClampBall P bits a b c d).Encloses P (absKernelTwoClampRange bits a b c d) :=
  IntervalBalls.sub_encloses (IntervalBalls.add_encloses (IntervalBalls.sub_encloses
    (IntervalBalls.add_encloses (IntervalBalls.constMul_encloses (logAtBall_encloses P bits _) _)
      (atanAtBall_encloses P bits _)) (IntervalBalls.constMul_encloses
        (IntervalBalls.add_encloses (atanAtBall_encloses P bits _)
          (atanAtBall_encloses P bits _)) _))
    (IntervalBalls.constMul_encloses (IntervalBalls.add_encloses
      (atanAtBall_encloses P bits _) (atanAtBall_encloses P bits _)) _))
    (atanAtBall_encloses P bits _)

/-- For `0 ≤ a`, `absKernelTwoClampRange bits a b c d` contains the real clamp formula of
`integral_rectangle_abs_hessianKernel_zero_zero`, with the clamped ends `p = max a (min c b)` and
`q = max a (min d b)`. -/
private theorem absKernelTwoClampRange_sound (bits : ℕ) {a b c d : ℚ} (ha : 0 ≤ a) :
    (absKernelTwoClampRange bits a b c d).MemReal
      (Real.log (max (a : ℝ) (min (d : ℝ) b) / max (a : ℝ) (min (c : ℝ) b)) / 2 +
        Real.arctan (max (a : ℝ) (min (c : ℝ) b) / c) -
        (Real.arctan ((a : ℝ) / c) + Real.arctan ((b : ℝ) / c)) / 2 +
        (Real.arctan ((a : ℝ) / d) + Real.arctan ((b : ℝ) / d)) / 2 -
        Real.arctan (max (a : ℝ) (min (d : ℝ) b) / d)) := by
  have hpq : 0 ≤ max a (min d b) / max a (min c b) :=
    div_nonneg (ha.trans (le_max_left _ _)) (ha.trans (le_max_left _ _))
  have hs := RationalInterval.sub_sound (RationalInterval.add_sound (RationalInterval.sub_sound
    (RationalInterval.add_sound (RationalInterval.mul_sound (RationalInterval.memReal_const (1 / 2))
      (logAt_sound bits hpq)) (atanAt_sound bits (max a (min c b) / c)))
    (RationalInterval.mul_sound (RationalInterval.memReal_const (1 / 2))
      (RationalInterval.add_sound (atanAt_sound bits (a / c)) (atanAt_sound bits (b / c)))))
    (RationalInterval.mul_sound (RationalInterval.memReal_const (1 / 2))
      (RationalInterval.add_sound (atanAt_sound bits (a / d)) (atanAt_sound bits (b / d)))))
    (atanAt_sound bits (max a (min d b) / d))
  have e : Real.log (max (a : ℝ) (min (d : ℝ) b) / max (a : ℝ) (min (c : ℝ) b)) / 2 +
      Real.arctan (max (a : ℝ) (min (c : ℝ) b) / c) -
      (Real.arctan ((a : ℝ) / c) + Real.arctan ((b : ℝ) / c)) / 2 +
      (Real.arctan ((a : ℝ) / d) + Real.arctan ((b : ℝ) / d)) / 2 -
      Real.arctan (max (a : ℝ) (min (d : ℝ) b) / d) =
      ((1 / 2 : ℚ) : ℝ) * Real.log ((max a (min d b) / max a (min c b) : ℚ) : ℝ) +
        Real.arctan ((max a (min c b) / c : ℚ) : ℝ) -
        ((1 / 2 : ℚ) : ℝ) * (Real.arctan ((a / c : ℚ) : ℝ) + Real.arctan ((b / c : ℚ) : ℝ)) +
        ((1 / 2 : ℚ) : ℝ) * (Real.arctan ((a / d : ℚ) : ℝ) + Real.arctan ((b / d : ℚ) : ℝ)) -
        Real.arctan ((max a (min d b) / d : ℚ) : ℝ) := by
    push_cast; ring
  rw [e]
  exact hs

/-- The real `|K₂|` integral on a rectangle of the first quadrant off the diagonal: above it
(`b ≤ c`) `K₂ ≤ 0`, below it (`d ≤ a`) `K₂ ≥ 0`. -/
private theorem integral_integral_abs_kernelTwo_of_sign {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (h0 : 0 < a ∨ 0 < c) (s : ℝ)
    (hs : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d,
      |hessianKernel 0 0 !₂[x, y]| = s * hessianKernel 0 0 !₂[x, y]) :
    ∫ x in a..b, ∫ y in c..d, |hessianKernel 0 0 !₂[x, y]| =
      s * cornerSum (fun u v ↦ Real.arctan (u / v) / 2) a b c d := by
  rw [← integral_integral_hessianKernel_zero_zero hab hcd (by tauto),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x hx ↦ ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun y hy ↦ ?_
  rw [uIcc_of_le hab] at hx; rw [uIcc_of_le hcd] at hy
  exact hs x hx y hy

/-- The enclosure of `∫_Q |K₂|` on a rectangle of the first quadrant: one arctangent with the sign
of `K₂` off the diagonal (`b ≤ c` or `d ≤ a`), the clamp formula on rectangles crossing it. -/
def absKernelTwoRange (bits : ℕ) (a b c d : ℚ) : RationalInterval :=
  if b ≤ c then (RationalInterval.const (-1)).mul (kernelTwoQuadrantRange bits a b c d)
  else if d ≤ a then kernelTwoQuadrantRange bits a b c d
  else absKernelTwoClampRange bits a b c d

/-- Balls of `absKernelTwoRange bits a b c d`. -/
def absKernelTwoBall (P bits : ℕ) (a b c d : ℚ) : IntervalBalls :=
  if b ≤ c then IntervalBalls.constMul (-1) (kernelTwoQuadrantBall P bits a b c d)
  else if d ≤ a then kernelTwoQuadrantBall P bits a b c d
  else absKernelTwoClampBall P bits a b c d

/-- `absKernelTwoBall P bits a b c d` encloses `absKernelTwoRange bits a b c d`. -/
theorem absKernelTwoBall_encloses (P bits : ℕ) (a b c d : ℚ) :
    (absKernelTwoBall P bits a b c d).Encloses P (absKernelTwoRange bits a b c d) := by
  unfold absKernelTwoBall absKernelTwoRange
  split_ifs
  · exact IntervalBalls.constMul_encloses (kernelTwoQuadrantBall_encloses P bits a b c d) _
  · exact kernelTwoQuadrantBall_encloses P bits a b c d
  · exact absKernelTwoClampBall_encloses P bits a b c d

/-- **Certified bounds of `∫_Q |K₂|`** on a rectangle of the first quadrant from a successful ball
check. -/
theorem integral_rectangle_abs_hessianKernel_zero_zero_mem {a b c d : ℚ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hc : 0 ≤ c) (hcd : c ≤ d) (h0 : 0 < a ∨ 0 < c) {P bits : ℕ} {lo hi : ℚ}
    (h : IntervalBalls.checkBoundsCertain P (lo, hi) (absKernelTwoBall P bits a b c d) = true) :
    (lo : ℝ) ≤ ∫ y in coordinateRectangle a b c d, |hessianKernel 0 0 y| ∧
      ∫ y in coordinateRectangle a b c d, |hessianKernel 0 0 y| ≤ hi := by
  have h0' : (0 : ℝ) < a ∨ (0 : ℝ) < c := by
    rcases h0 with h | h <;> [left; right] <;> exact_mod_cast h
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hcd' : (c : ℝ) ≤ d := by exact_mod_cast hcd
  have h0'' : (0 : ℝ) < a ∨ (b : ℝ) < 0 ∨ (0 : ℝ) < c ∨ (d : ℝ) < 0 := by tauto
  rw [setIntegral_coordinateRectangle hab' hcd' (continuousOn_hessianKernel 0 0 h0'').abs]
  refine mem_of_check (absKernelTwoBall_encloses P bits a b c d) ?_ h
  unfold absKernelTwoRange
  split_ifs with hbc hda
  · have hbc' : (b : ℝ) ≤ c := by exact_mod_cast hbc
    rw [integral_integral_abs_kernelTwo_of_sign hab' hcd' h0' (-1) fun x hx y hy ↦ by
      rw [abs_of_nonpos (hessianKernel_zero_zero_toLp_nonpos (ha'.trans hx.1)
        ((hx.2.trans hbc').trans hy.1))]
      ring]
    have := RationalInterval.mul_sound (RationalInterval.memReal_const (-1))
      (kernelTwoQuadrantRange_sound bits ha hab hc hcd h0)
    push_cast at this
    exact this
  · have hda' : (d : ℝ) ≤ a := by exact_mod_cast hda
    rw [integral_integral_abs_kernelTwo_of_sign hab' hcd' h0' 1 fun x hx y hy ↦ by
      rw [abs_of_nonneg (hessianKernel_zero_zero_toLp_nonneg (hc'.trans hy.1)
        ((hy.2.trans hda').trans hx.1))]
      ring, one_mul]
    exact kernelTwoQuadrantRange_sound bits ha hab hc hcd h0
  · rw [integral_integral_abs_hessianKernel_zero_zero ha' hab' hc' hcd' h0']
    exact absKernelTwoClampRange_sound bits ha

/-- The enclosure of `F_diag(a, b) = (1/2) log (b/a) - (arctan 1 - arctan (a/b))`. -/
def squareAbsKernelTwoRange (bits : ℕ) (a b : ℚ) : RationalInterval :=
  ((RationalInterval.const (1 / 2)).mul (logAt bits (b / a))).sub
    ((atanAt bits 1).sub (atanAt bits (a / b)))

/-- Balls of `squareAbsKernelTwoRange bits a b`. -/
def squareAbsKernelTwoBall (P bits : ℕ) (a b : ℚ) : IntervalBalls :=
  (IntervalBalls.constMul (1 / 2) (logAtBall P bits (b / a))).sub
    ((atanAtBall P bits 1).sub (atanAtBall P bits (a / b)))

/-- **Certified bounds of `F_diag(a, b) = ∫_{[a, b]²} |K₂|`** from a successful ball check. -/
theorem integral_square_abs_hessianKernel_zero_zero_mem {a b : ℚ} (ha : 0 < a) (hab : a ≤ b)
    {P bits : ℕ} {lo hi : ℚ}
    (h : IntervalBalls.checkBoundsCertain P (lo, hi) (squareAbsKernelTwoBall P bits a b) = true) :
    (lo : ℝ) ≤ ∫ y in coordinateRectangle a b a b, |hessianKernel 0 0 y| ∧
      ∫ y in coordinateRectangle a b a b, |hessianKernel 0 0 y| ≤ hi := by
  rw [integral_square_abs_hessianKernel_zero_zero (by exact_mod_cast ha) (by exact_mod_cast hab)]
  have hS := IntervalBalls.sub_encloses
    (IntervalBalls.constMul_encloses (logAtBall_encloses P bits (b / a)) (1 / 2))
    (IntervalBalls.sub_encloses (atanAtBall_encloses P bits 1) (atanAtBall_encloses P bits (a / b)))
  have hs := RationalInterval.sub_sound (RationalInterval.mul_sound
    (RationalInterval.memReal_const (1 / 2))
      (logAt_sound bits (div_nonneg (ha.le.trans hab) ha.le)))
    (RationalInterval.sub_sound (atanAt_sound bits 1) (atanAt_sound bits (a / b)))
  have e : Real.log ((b : ℝ) / a) / 2 - (Real.pi / 4 - Real.arctan ((a : ℝ) / b)) =
      ((1 / 2 : ℚ) : ℝ) * Real.log ((b / a : ℚ) : ℝ) -
        (Real.arctan ((1 : ℚ) : ℝ) - Real.arctan ((a / b : ℚ) : ℝ)) := by
    push_cast; rw [Real.arctan_one]; ring
  rw [e]
  exact mem_of_check hS hs h

/-! ### The velocity kernels `∂ᵢG` on rectangles -/

/-- The enclosure of `-(2u arctan (v/u) + v log (u² + v²))/4` at a rational corner. -/
def gradientCornerRange (bits : ℕ) (u v : ℚ) : RationalInterval :=
  (RationalInterval.const (-1 / 4)).mul (((RationalInterval.const (2 * u)).mul
    (atanAt bits (v / u))).add ((RationalInterval.const v).mul (logAt bits (u ^ 2 + v ^ 2))))

/-- `gradientCornerRange bits u v` contains `-(2u arctan (v/u) + v log (u² + v²))/4`. -/
theorem gradientCornerRange_sound (bits : ℕ) (u v : ℚ) :
    (gradientCornerRange bits u v).MemReal
      (-(2 * ((u : ℝ) * Real.arctan (v / u)) + v * Real.log (u ^ 2 + v ^ 2)) / 4) := by
  have h := RationalInterval.mul_sound (RationalInterval.memReal_const (-1 / 4))
    (RationalInterval.add_sound (RationalInterval.mul_sound (RationalInterval.memReal_const (2 * u))
      (atanAt_sound bits (v / u))) (RationalInterval.mul_sound (RationalInterval.memReal_const v)
        (logAt_sound bits (by positivity : (0 : ℚ) ≤ u ^ 2 + v ^ 2))))
  have e : -(2 * ((u : ℝ) * Real.arctan (v / u)) + v * Real.log (u ^ 2 + v ^ 2)) / 4 =
      ((-1 / 4 : ℚ) : ℝ) * (((2 * u : ℚ) : ℝ) * Real.arctan ((v / u : ℚ) : ℝ) +
        (v : ℝ) * Real.log ((u ^ 2 + v ^ 2 : ℚ) : ℝ)) := by
    push_cast; ring
  rw [e]
  exact h

/-- Balls of `gradientCornerRange bits u v`. -/
def gradientCornerBall (P bits : ℕ) (u v : ℚ) : IntervalBalls :=
  IntervalBalls.constMul (-1 / 4) ((IntervalBalls.constMul (2 * u) (atanAtBall P bits (v / u))).add
    (IntervalBalls.constMul v (logAtBall P bits (u ^ 2 + v ^ 2))))

/-- `gradientCornerBall P bits u v` encloses `gradientCornerRange bits u v`. -/
theorem gradientCornerBall_encloses (P bits : ℕ) (u v : ℚ) :
    (gradientCornerBall P bits u v).Encloses P (gradientCornerRange bits u v) :=
  IntervalBalls.constMul_encloses (IntervalBalls.add_encloses
    (IntervalBalls.constMul_encloses (atanAtBall_encloses P bits _) _)
    (IntervalBalls.constMul_encloses (logAtBall_encloses P bits _) _)) _

/-- Balls of `∫_Q ∂₁G = π ∫_Q gradientKernel 0`, the corner sum of `gradientCornerBall`. -/
def gradientZeroBall (P bits : ℕ) (a b c d : ℚ) : IntervalBalls :=
  (((gradientCornerBall P bits b d).sub (gradientCornerBall P bits a d)).sub
    (gradientCornerBall P bits b c)).add (gradientCornerBall P bits a c)

/-- **Certified bounds of `π ∫_Q gradientKernel 0 = ∫_Q ∂₁G`** from a successful ball check, on
every closed rectangle, also one containing the pole. -/
theorem integral_rectangle_gradientKernel_zero_mem {a b c d : ℚ} (hab : a ≤ b) (hcd : c ≤ d)
    {P bits : ℕ} {lo hi : ℚ}
    (h : IntervalBalls.checkBoundsCertain P (lo, hi) (gradientZeroBall P bits a b c d) = true) :
    (lo : ℝ) ≤ Real.pi * ∫ y in coordinateRectangle a b c d, gradientKernel 0 y ∧
      Real.pi * ∫ y in coordinateRectangle a b c d, gradientKernel 0 y ≤ hi := by
  rw [integral_rectangle_gradientKernel_zero_eq_cornerSum (by exact_mod_cast hab)
    (by exact_mod_cast hcd)]
  have hS := IntervalBalls.add_encloses (IntervalBalls.sub_encloses (IntervalBalls.sub_encloses
    (gradientCornerBall_encloses P bits b d) (gradientCornerBall_encloses P bits a d))
    (gradientCornerBall_encloses P bits b c)) (gradientCornerBall_encloses P bits a c)
  exact mem_of_check hS (RationalInterval.add_sound (RationalInterval.sub_sound
    (RationalInterval.sub_sound (gradientCornerRange_sound bits b d)
      (gradientCornerRange_sound bits a d)) (gradientCornerRange_sound bits b c))
    (gradientCornerRange_sound bits a c)) h

/-- **Certified bounds of `π ∫_Q gradientKernel 1 = ∫_Q ∂₂G`** from a successful ball check, on
every closed rectangle: by the coordinate swap, the corners `(v, u)` of `gradientCornerBall`. -/
theorem integral_rectangle_gradientKernel_one_mem {a b c d : ℚ} (hab : a ≤ b) (hcd : c ≤ d)
    {P bits : ℕ} {lo hi : ℚ}
    (h : IntervalBalls.checkBoundsCertain P (lo, hi) (gradientZeroBall P bits c d a b) = true) :
    (lo : ℝ) ≤ Real.pi * ∫ y in coordinateRectangle a b c d, gradientKernel 1 y ∧
      Real.pi * ∫ y in coordinateRectangle a b c d, gradientKernel 1 y ≤ hi := by
  rw [integral_rectangle_gradientKernel_one_eq_cornerSum (by exact_mod_cast hab)
    (by exact_mod_cast hcd), ← cornerSum_swap]
  have e : (fun x y : ℝ ↦ -(2 * (x * Real.arctan (y / x)) + y * Real.log (y ^ 2 + x ^ 2)) / 4) =
      fun x y ↦ -(2 * (x * Real.arctan (y / x)) + y * Real.log (x ^ 2 + y ^ 2)) / 4 := by
    funext x y; rw [add_comm (y ^ 2)]
  rw [e]
  have hS := IntervalBalls.add_encloses (IntervalBalls.sub_encloses (IntervalBalls.sub_encloses
    (gradientCornerBall_encloses P bits d b) (gradientCornerBall_encloses P bits c b))
    (gradientCornerBall_encloses P bits d a)) (gradientCornerBall_encloses P bits c a)
  exact mem_of_check hS (RationalInterval.add_sound (RationalInterval.sub_sound
    (RationalInterval.sub_sound (gradientCornerRange_sound bits d b)
      (gradientCornerRange_sound bits c b)) (gradientCornerRange_sound bits d a))
    (gradientCornerRange_sound bits c a)) h

/-! ### `f_s` and the constants with a half power -/

/-- FloatLib's logarithm enclosure of an interval with positive lower endpoint, `{0}` otherwise. -/
def logRangeOr (terms : ℕ) (I : RationalInterval) : RationalInterval :=
  if h : 0 < I.lo then RationalInterval.logRangeWith I terms h else RationalInterval.const 0

/-- For `0 < I.lo`, `logRangeOr terms I` contains `log x` for every `x ∈ I`. -/
theorem logRangeOr_sound (terms : ℕ) {I : RationalInterval} (h : 0 < I.lo) {x : ℝ}
    (hx : I.MemReal x) : (logRangeOr terms I).MemReal (Real.log x) := by
  simp only [logRangeOr, h, ↓reduceDIte]
  exact RationalInterval.logRangeWith_sound I terms h hx

/-- Balls of `logRangeOr terms I`, invalid unless the ball decides `0 < I.lo`. -/
def logRangeOrBall (P terms : ℕ) (S : IntervalBalls) : IntervalBalls :=
  Bool.rec IntervalBalls.invalid (IntervalBalls.logRangeBall P terms S) (GridBall.posCertain S.lo)

/-- Balls `S` of `I` give balls of `logRangeOr terms I`. -/
theorem logRangeOrBall_encloses {P terms : ℕ} {S : IntervalBalls} {I : RationalInterval}
    (hS : S.Encloses P I) : (logRangeOrBall P terms S).Encloses P (logRangeOr terms I) := by
  unfold logRangeOrBall
  cases h : GridBall.posCertain S.lo
  · exact IntervalBalls.invalid_encloses _
  · have hI := IntervalBalls.lo_pos_of hS h
    simp only [logRangeOr, hI, ↓reduceDIte]
    exact IntervalBalls.logRangeBall_encloses hS hI

/-- The enclosure `sqrtPointInterval 2 steps` of `√2`. -/
def sqrtTwo (steps : ℕ) : RationalInterval := RationalInterval.sqrtPointInterval 2 steps

/-- `sqrtTwo steps` contains `√2`. -/
theorem sqrtTwo_sound (steps : ℕ) : (sqrtTwo steps).MemReal √2 := by
  have h := RationalInterval.sqrtPointInterval_sound 2 steps
  rw [show ((2 : ℚ) : ℝ) = 2 by norm_num] at h
  exact h

/-- Balls of `sqrtTwo steps`. -/
def sqrtTwoBall (P steps : ℕ) : IntervalBalls := sqrtPointBall P steps (GridBall.ofNat P 2)

/-- `sqrtTwoBall P steps` encloses `sqrtTwo steps`. -/
theorem sqrtTwoBall_encloses (P steps : ℕ) :
    (sqrtTwoBall P steps).Encloses P (sqrtTwo steps) := by
  have h := sqrtPointBall_encloses (steps := steps) (GridBall.ofNat_encloses P 2)
  rw [show ((2 : ℕ) : ℚ) = 2 by norm_num] at h
  exact h

/-- The enclosure of `t² - √2 t + 1`. -/
def halfPowerMinus (steps : ℕ) (t : ℚ) : RationalInterval :=
  (RationalInterval.const (t ^ 2 + 1)).sub ((RationalInterval.const t).mul (sqrtTwo steps))

/-- The enclosure of `t² + √2 t + 1`. -/
def halfPowerPlus (steps : ℕ) (t : ℚ) : RationalInterval :=
  (RationalInterval.const (t ^ 2 + 1)).add ((RationalInterval.const t).mul (sqrtTwo steps))

/-- The enclosure of `4√2`. -/
def halfPowerDen (steps : ℕ) : RationalInterval := (RationalInterval.const 4).mul (sqrtTwo steps)

/-- The enclosure of `f_s(t)` from its closed form (`halfPowerIntegral_eq`) at a rational `t`. -/
def halfPowerAt (terms steps : ℕ) (t : ℚ) : RationalInterval :=
  ((((logRangeOr terms (halfPowerMinus steps t)).sub (logRangeOr terms (halfPowerPlus steps t))).add
    ((RationalInterval.const 2).mul (RationalInterval.atanRangeWith
      (((RationalInterval.const t).mul (sqrtTwo steps)).add (RationalInterval.const 1)) terms))).add
    ((RationalInterval.const 2).mul (RationalInterval.atanRangeWith
      (((RationalInterval.const t).mul (sqrtTwo steps)).sub (RationalInterval.const 1))
        terms))).divPositiveOrZero (halfPowerDen steps)

/-- `halfPowerAt terms steps t` contains `f_s(t)` when the three positivity conditions hold. -/
theorem halfPowerAt_sound (terms steps : ℕ) {t : ℚ} (h₁ : 0 < (halfPowerMinus steps t).lo)
    (h₂ : 0 < (halfPowerPlus steps t).lo) (h₃ : 0 < (halfPowerDen steps).lo) :
    (halfPowerAt terms steps t).MemReal (halfPowerIntegral t) := by
  have hr := sqrtTwo_sound steps
  have hA : (halfPowerMinus steps t).MemReal ((t : ℝ) ^ 2 - √2 * t + 1) := by
    have := RationalInterval.sub_sound (RationalInterval.memReal_const (t ^ 2 + 1))
      (RationalInterval.mul_sound (RationalInterval.memReal_const t) hr)
    have e : (t : ℝ) ^ 2 - √2 * t + 1 = ((t ^ 2 + 1 : ℚ) : ℝ) - t * √2 := by push_cast; ring
    rw [e]; exact this
  have hB : (halfPowerPlus steps t).MemReal ((t : ℝ) ^ 2 + √2 * t + 1) := by
    have := RationalInterval.add_sound (RationalInterval.memReal_const (t ^ 2 + 1))
      (RationalInterval.mul_sound (RationalInterval.memReal_const t) hr)
    have e : (t : ℝ) ^ 2 + √2 * t + 1 = ((t ^ 2 + 1 : ℚ) : ℝ) + t * √2 := by push_cast; ring
    rw [e]; exact this
  have h₁' : (0 : ℝ) < (t : ℝ) ^ 2 - √2 * t + 1 := by
    nlinarith [sq_nonneg ((t : ℝ) - √2 / 2), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h₂' : (0 : ℝ) < (t : ℝ) ^ 2 + √2 * t + 1 := by
    nlinarith [sq_nonneg ((t : ℝ) + √2 / 2), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hD : (halfPowerDen steps).MemReal (4 * √2) := by
    have h := RationalInterval.mul_sound (RationalInterval.memReal_const 4) hr
    rw [show ((4 : ℚ) : ℝ) = 4 by norm_num] at h
    exact h
  have ha1 := RationalInterval.atanRangeWith_sound _ terms (RationalInterval.add_sound
    (RationalInterval.mul_sound (RationalInterval.memReal_const t) hr)
    (RationalInterval.memReal_const 1))
  have ha2 := RationalInterval.atanRangeWith_sound _ terms (RationalInterval.sub_sound
    (RationalInterval.mul_sound (RationalInterval.memReal_const t) hr)
    (RationalInterval.memReal_const 1))
  have hnum := RationalInterval.add_sound (RationalInterval.add_sound (RationalInterval.sub_sound
    (logRangeOr_sound terms h₁ hA) (logRangeOr_sound terms h₂ hB))
    (RationalInterval.mul_sound (RationalInterval.memReal_const 2) ha1))
    (RationalInterval.mul_sound (RationalInterval.memReal_const 2) ha2)
  have h := RationalInterval.divPositiveOrZero_sound h₃ hnum hD
  rw [halfPowerIntegral_eq, Real.log_div h₁'.ne' h₂'.ne']
  have e : (Real.log ((t : ℝ) ^ 2 - √2 * t + 1) - Real.log ((t : ℝ) ^ 2 + √2 * t + 1) +
      2 * Real.arctan (√2 * t + 1) + 2 * Real.arctan (√2 * t - 1)) / (4 * √2) =
      (Real.log ((t : ℝ) ^ 2 - √2 * t + 1) - Real.log ((t : ℝ) ^ 2 + √2 * t + 1) +
        ((2 : ℚ) : ℝ) * Real.arctan (t * √2 + ((1 : ℚ) : ℝ)) +
        ((2 : ℚ) : ℝ) * Real.arctan (t * √2 - ((1 : ℚ) : ℝ))) / (4 * √2) := by
    push_cast; ring_nf
  rw [e]
  exact h

/-- Balls of `halfPowerAt terms steps t`. -/
def halfPowerAtBall (P terms steps : ℕ) (t : ℚ) : IntervalBalls :=
  let tr := IntervalBalls.constMul t (sqrtTwoBall P steps)
  IntervalBalls.divPositiveOrZero P
    ((((logRangeOrBall P terms ((IntervalBalls.const P (t ^ 2 + 1)).sub tr)).sub
      (logRangeOrBall P terms ((IntervalBalls.const P (t ^ 2 + 1)).add tr))).add
      (IntervalBalls.constMul 2
        (IntervalBalls.atanRangeBall P terms (tr.add (IntervalBalls.const P 1))))).add
      (IntervalBalls.constMul 2
        (IntervalBalls.atanRangeBall P terms (tr.sub (IntervalBalls.const P 1)))))
    (IntervalBalls.constMul 4 (sqrtTwoBall P steps))

/-- `halfPowerAtBall P terms steps t` encloses `halfPowerAt terms steps t`. -/
theorem halfPowerAtBall_encloses (P terms steps : ℕ) (t : ℚ) :
    (halfPowerAtBall P terms steps t).Encloses P (halfPowerAt terms steps t) := by
  have hr := sqrtTwoBall_encloses P steps
  have htr := IntervalBalls.constMul_encloses hr t
  exact IntervalBalls.divPositiveOrZero_encloses (IntervalBalls.add_encloses
    (IntervalBalls.add_encloses (IntervalBalls.sub_encloses
      (logRangeOrBall_encloses (IntervalBalls.sub_encloses (IntervalBalls.const_encloses _) htr))
      (logRangeOrBall_encloses (IntervalBalls.add_encloses (IntervalBalls.const_encloses _) htr)))
      (IntervalBalls.constMul_encloses (IntervalBalls.atanRangeBall_encloses
        (IntervalBalls.add_encloses htr (IntervalBalls.const_encloses 1))) 2))
    (IntervalBalls.constMul_encloses (IntervalBalls.atanRangeBall_encloses
      (IntervalBalls.sub_encloses htr (IntervalBalls.const_encloses 1))) 2))
    (IntervalBalls.constMul_encloses hr 4)

/-- The ball test of the three positivity conditions of `halfPowerAt_sound`. -/
def halfPowerAtOk (P steps : ℕ) (t : ℚ) : Bool :=
  let tr := IntervalBalls.constMul t (sqrtTwoBall P steps)
  GridBall.posCertain ((IntervalBalls.const P (t ^ 2 + 1)).sub tr).lo &&
    GridBall.posCertain ((IntervalBalls.const P (t ^ 2 + 1)).add tr).lo &&
    GridBall.posCertain (IntervalBalls.constMul 4 (sqrtTwoBall P steps)).lo

/-- After a successful ball test `halfPowerAtOk P steps t`, `halfPowerAt terms steps t` contains
`f_s(t)`. -/
theorem halfPowerAt_sound_of_ok {P terms steps : ℕ} {t : ℚ} (h : halfPowerAtOk P steps t = true) :
    (halfPowerAt terms steps t).MemReal (halfPowerIntegral t) := by
  simp only [halfPowerAtOk, Bool.and_eq_true] at h
  have hr := sqrtTwoBall_encloses P steps
  have htr := IntervalBalls.constMul_encloses hr t
  exact halfPowerAt_sound terms steps
    (IntervalBalls.lo_pos_of (IntervalBalls.sub_encloses (IntervalBalls.const_encloses _) htr)
      h.1.1)
    (IntervalBalls.lo_pos_of (IntervalBalls.add_encloses (IntervalBalls.const_encloses _) htr)
      h.1.2)
    (IntervalBalls.lo_pos_of (IntervalBalls.constMul_encloses hr 4) h.2)

/-- **Certified bounds of `f_s(t)`** at a rational `t` from successful ball checks. -/
theorem halfPowerIntegral_mem {P terms steps : ℕ} {t lo hi : ℚ}
    (hok : halfPowerAtOk P steps t = true)
    (h : IntervalBalls.checkBoundsCertain P (lo, hi) (halfPowerAtBall P terms steps t) = true) :
    (lo : ℝ) ≤ halfPowerIntegral t ∧ halfPowerIntegral t ≤ hi :=
  mem_of_check (halfPowerAtBall_encloses P terms steps t) (halfPowerAt_sound_of_ok hok) h

/-- The enclosure of `f_s` on an interval `T`, by monotonicity from its two endpoints. -/
def halfPowerRange (terms steps : ℕ) (T : RationalInterval) : RationalInterval :=
  (halfPowerAt terms steps T.lo).hull (halfPowerAt terms steps T.hi)

/-- If the ball tests succeed at both ends of `T`, `halfPowerRange terms steps T` contains `f_s(x)`
for every `x ∈ T`. -/
theorem halfPowerRange_sound {P terms steps : ℕ} {T : RationalInterval}
    (hlo : halfPowerAtOk P steps T.lo = true) (hhi : halfPowerAtOk P steps T.hi = true) {x : ℝ}
    (hx : T.MemReal x) : (halfPowerRange terms steps T).MemReal (halfPowerIntegral x) := by
  have h1 := halfPowerAt_sound_of_ok (terms := terms) hlo
  have h2 := halfPowerAt_sound_of_ok (terms := terms) hhi
  change ((halfPowerRange terms steps T).lo : ℝ) ≤ _ ∧ _ ≤ ((halfPowerRange terms steps T).hi : ℝ)
  rw [halfPowerRange, RationalInterval.hull_lo, RationalInterval.hull_hi, Rat.cast_min,
    Rat.cast_max]
  exact ⟨(min_le_left _ _).trans (h1.1.trans (monotone_halfPowerIntegral hx.1)),
    ((monotone_halfPowerIntegral hx.2).trans h2.2).trans (le_max_right _ _)⟩

/-- Balls of `halfPowerRange terms steps T` at the exact endpoints of `T`. -/
def halfPowerRangeBall (P terms steps : ℕ) (T : RationalInterval) : IntervalBalls :=
  (halfPowerAtBall P terms steps T.lo).hull (halfPowerAtBall P terms steps T.hi)

/-- `halfPowerRangeBall P terms steps T` encloses `halfPowerRange terms steps T`. -/
theorem halfPowerRangeBall_encloses (P terms steps : ℕ) (T : RationalInterval) :
    (halfPowerRangeBall P terms steps T).Encloses P (halfPowerRange terms steps T) :=
  IntervalBalls.hull_encloses (halfPowerAtBall_encloses P terms steps _)
    (halfPowerAtBall_encloses P terms steps _)

/-- The enclosure of `C_{K₂,low} = (log 2 - 2 f_s(1)) / 2 = (1/2) log 2 - f_s(1)`. -/
def kernelTwoLowRange (terms steps : ℕ) : RationalInterval :=
  ((RationalInterval.const (1 / 2)).mul (logAt terms 2)).sub (halfPowerAt terms steps 1)

/-- Balls of `kernelTwoLowRange terms steps`. -/
def kernelTwoLowBall (P terms steps : ℕ) : IntervalBalls :=
  (IntervalBalls.constMul (1 / 2) (logAtBall P terms 2)).sub (halfPowerAtBall P terms steps 1)

/-- **Certified bounds of `C_{K₂,low}`** of Chen and Hou, Part II, supplementary material II,
(5.11)-(5.12), from successful ball checks. -/
theorem kernelTwoLow_mem {P terms steps : ℕ} {lo hi : ℚ} (hok : halfPowerAtOk P steps 1 = true)
    (h : IntervalBalls.checkBoundsCertain P (lo, hi) (kernelTwoLowBall P terms steps) = true) :
    (lo : ℝ) ≤ ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..x ^ 2, |hessianKernel 0 0 !₂[x, y]| * √y ∧
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..x ^ 2, |hessianKernel 0 0 !₂[x, y]| * √y ≤ hi := by
  rw [integral_integral_abs_hessianKernel_zero_zero_mul_sqrt_parabola]
  have hS := IntervalBalls.sub_encloses
    (IntervalBalls.constMul_encloses (logAtBall_encloses P terms 2) (1 / 2))
    (halfPowerAtBall_encloses P terms steps 1)
  have hs := RationalInterval.sub_sound (RationalInterval.mul_sound
    (RationalInterval.memReal_const (1 / 2)) (logAt_sound terms (by norm_num : (0 : ℚ) ≤ 2)))
    (halfPowerAt_sound_of_ok (terms := terms) hok)
  have e : (Real.log 2 - 2 * halfPowerIntegral 1) / 2 =
      ((1 / 2 : ℚ) : ℝ) * Real.log ((2 : ℚ) : ℝ) - halfPowerIntegral ((1 : ℚ) : ℝ) := by
    push_cast; ring
  rw [e]
  exact mem_of_check hS hs h

/-- The enclosure of `f_s(∞) = π / (2√2) = 4 arctan 1 / (2√2)`. -/
def halfPowerLimitRange (terms steps : ℕ) : RationalInterval :=
  ((RationalInterval.const 4).mul (atanAt terms 1)).divPositiveOrZero
    ((RationalInterval.const 2).mul (sqrtTwo steps))

/-- Balls of `halfPowerLimitRange terms steps`. -/
def halfPowerLimitBall (P terms steps : ℕ) : IntervalBalls :=
  IntervalBalls.divPositiveOrZero P (IntervalBalls.constMul 4 (atanAtBall P terms 1))
    (IntervalBalls.constMul 2 (sqrtTwoBall P steps))

/-- **Certified bounds of `∫₀^∞ s² / (1 + s⁴) ds = π / (2√2)`** from successful ball checks. -/
theorem integral_Ioi_sq_div_one_add_pow_four_mem {P terms steps : ℕ} {lo hi : ℚ}
    (hok : GridBall.posCertain (IntervalBalls.constMul 2 (sqrtTwoBall P steps)).lo = true)
    (h : IntervalBalls.checkBoundsCertain P (lo, hi) (halfPowerLimitBall P terms steps) = true) :
    (lo : ℝ) ≤ ∫ s in Ioi (0 : ℝ), s ^ 2 / (1 + s ^ 4) ∧
      ∫ s in Ioi (0 : ℝ), s ^ 2 / (1 + s ^ 4) ≤ (hi : ℝ) := by
  rw [integral_Ioi_sq_div_one_add_pow_four]
  have hden := IntervalBalls.constMul_encloses (sqrtTwoBall_encloses P steps) 2
  have hS := IntervalBalls.divPositiveOrZero_encloses
    (IntervalBalls.constMul_encloses (atanAtBall_encloses P terms 1) 4) hden
  have hs := RationalInterval.divPositiveOrZero_sound (IntervalBalls.lo_pos_of hden hok)
    (RationalInterval.mul_sound (RationalInterval.memReal_const 4) (atanAt_sound terms 1))
    (RationalInterval.mul_sound (RationalInterval.memReal_const 2) (sqrtTwo_sound steps))
  have e : Real.pi / (2 * √2) =
      ((4 : ℚ) : ℝ) * Real.arctan ((1 : ℚ) : ℝ) / (((2 : ℚ) : ℝ) * √2) := by
    push_cast; rw [Real.arctan_one]; ring
  rw [e]
  exact mem_of_check hS hs h

/-- The enclosure of `F(a, b) = ∫₀^b (∫₀^a |K₂|) y₂^{1/2} dy₂`
(`integral_integral_abs_hessianKernel_zero_zero_mul_sqrt`) for rationals `a, b > 0`. -/
def kernelTwoHalfPowerRange (terms steps : ℕ) (a b : ℚ) : RationalInterval :=
  if b ≤ a then
    (RationalInterval.sqrtPointInterval b steps).sub
      ((RationalInterval.sqrtPointInterval a steps).mul
        (halfPowerRange terms steps (RationalInterval.sqrtPointInterval (b / a) steps)))
  else
    (RationalInterval.sqrtPointInterval a steps).mul (((RationalInterval.const 1).sub
      ((RationalInterval.const 2).mul (halfPowerAt terms steps 1))).add
      (halfPowerRange terms steps (RationalInterval.sqrtPointInterval (b / a) steps)))

/-- Balls of `kernelTwoHalfPowerRange terms steps a b`. -/
def kernelTwoHalfPowerBall (P terms steps : ℕ) (a b : ℚ) : IntervalBalls :=
  if b ≤ a then
    (sqrtPointBall P steps (GridBall.ofRat P b)).sub (IntervalBalls.mul P
      (sqrtPointBall P steps (GridBall.ofRat P a))
      (halfPowerRangeBall P terms steps (RationalInterval.sqrtPointInterval (b / a) steps)))
  else
    IntervalBalls.mul P (sqrtPointBall P steps (GridBall.ofRat P a))
      (((IntervalBalls.const P 1).sub
        (IntervalBalls.constMul 2 (halfPowerAtBall P terms steps 1))).add
        (halfPowerRangeBall P terms steps (RationalInterval.sqrtPointInterval (b / a) steps)))

/-- `kernelTwoHalfPowerBall P terms steps a b` encloses `kernelTwoHalfPowerRange terms steps a b`.
-/
theorem kernelTwoHalfPowerBall_encloses (P terms steps : ℕ) (a b : ℚ) :
    (kernelTwoHalfPowerBall P terms steps a b).Encloses P
      (kernelTwoHalfPowerRange terms steps a b) := by
  unfold kernelTwoHalfPowerBall kernelTwoHalfPowerRange
  split_ifs
  · exact IntervalBalls.sub_encloses (sqrtPointBall_encloses (GridBall.ofRat_encloses P b))
      (IntervalBalls.mul_encloses (sqrtPointBall_encloses (GridBall.ofRat_encloses P a))
        (halfPowerRangeBall_encloses P terms steps _))
  · exact IntervalBalls.mul_encloses (sqrtPointBall_encloses (GridBall.ofRat_encloses P a))
      (IntervalBalls.add_encloses (IntervalBalls.sub_encloses (IntervalBalls.const_encloses 1)
        (IntervalBalls.constMul_encloses (halfPowerAtBall_encloses P terms steps 1) 2))
        (halfPowerRangeBall_encloses P terms steps _))

/-- The ball tests of the positivity conditions behind `kernelTwoHalfPowerRange`. -/
def kernelTwoHalfPowerOk (P steps : ℕ) (a b : ℚ) : Bool :=
  halfPowerAtOk P steps (RationalInterval.sqrtPointInterval (b / a) steps).lo &&
    halfPowerAtOk P steps (RationalInterval.sqrtPointInterval (b / a) steps).hi &&
    halfPowerAtOk P steps 1

/-- **Certified bounds of `∫₀^b (∫₀^a |K₂|) y₂^{1/2} dy₂`** from successful ball checks. -/
theorem integral_integral_abs_hessianKernel_zero_zero_mul_sqrt_mem {a b : ℚ} (ha : 0 < a)
    (hb : 0 < b) {P terms steps : ℕ} {lo hi : ℚ} (hok : kernelTwoHalfPowerOk P steps a b = true)
    (h : IntervalBalls.checkBoundsCertain P (lo, hi) (kernelTwoHalfPowerBall P terms steps a b) =
      true) :
    (lo : ℝ) ≤ ∫ y in (0 : ℝ)..b, (∫ x in (0 : ℝ)..a, |hessianKernel 0 0 !₂[x, y]|) * √y ∧
      ∫ y in (0 : ℝ)..b, (∫ x in (0 : ℝ)..a, |hessianKernel 0 0 !₂[x, y]|) * √y ≤ (hi : ℝ) := by
  simp only [kernelTwoHalfPowerOk, Bool.and_eq_true] at hok
  rw [integral_integral_abs_hessianKernel_zero_zero_mul_sqrt (by exact_mod_cast ha)
    (by exact_mod_cast hb)]
  have hT : (RationalInterval.sqrtPointInterval (b / a) steps).MemReal √((b : ℝ) / a) := by
    have := RationalInterval.sqrtPointInterval_sound (b / a) steps
    push_cast at this; exact this
  have hF := halfPowerRange_sound (terms := terms) hok.1.1 hok.1.2 hT
  refine mem_of_check (kernelTwoHalfPowerBall_encloses P terms steps a b) ?_ h
  unfold kernelTwoHalfPowerRange
  have hsa := RationalInterval.sqrtPointInterval_sound a steps
  have hsb := RationalInterval.sqrtPointInterval_sound b steps
  by_cases hba : b ≤ a
  · have hba' : (b : ℝ) ≤ a := by exact_mod_cast hba
    simp only [hba, hba', ↓reduceIte]
    exact RationalInterval.sub_sound hsb (RationalInterval.mul_sound hsa hF)
  · have hba' : ¬ (b : ℝ) ≤ a := by exact_mod_cast hba
    simp only [hba, hba', ↓reduceIte]
    have h1 := halfPowerAt_sound_of_ok (terms := terms) hok.2
    have := RationalInterval.mul_sound hsa (RationalInterval.add_sound (RationalInterval.sub_sound
      (RationalInterval.memReal_const 1) (RationalInterval.mul_sound
        (RationalInterval.memReal_const 2) h1)) hF)
    push_cast at this
    exact this

end CAS.Numerics.PlanarKernel
