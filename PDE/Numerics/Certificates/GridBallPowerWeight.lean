/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.GridBallPolynomial
public import PDE.Analysis.Calculus.RadialPowerDerivatives

/-!
# Balls for the derivatives of power weights on cells

`closedTermsRange cs p X Y` encloses `∑ c ∈ cs, N_c(x, y) x ^ a_c (x ^ 2 + y ^ 2) ^ s_c` on the cell
`X × Y` (`closedTermsRange_sound`), where every power is in the domain of `rpowRat` (on cells
with `X.lo > 0` by `closedTermsDomain_of_pos`, for radial terms away from the origin by
`closedTermsDomain_of_radiusSq_pos`); terms with `a_c = 0` carry no factor in `x`. With the
closed-form terms `powerWeightClosed ts i j` or `radialWeightClosed ts i j` it encloses the mixed
partial derivatives `∂_x ^ i ∂_y ^ j` of a power weight (`powerWeightDerivRange_sound`,
`radialWeightDerivRange_sound`). `closedTermsBall` is the ball mirror (`closedTermsBall_encloses`).

The closed-form terms are data: a certificate that evaluates them on many cells computes them
once, or replaces them by a literal list checked equal to them. At `P = 200` the mixed derivative
`∂_x ∂_y ψ_1` of the Hölder weight costs about 4.8 ms per cell in the fast profile and 32 ms in
the kernel.

The interval products and powers `RationalInterval.mul` and `RationalInterval.powNat` of SymLean
are computed and certified by FloatLib, and the two lemmas on `X ^ 2` unfold FloatLib's power
bounds.

## Main definitions

* `closedTermsRange`: the enclosure of a sum of closed-form terms on a cell `X × Y`.
* `ClosedTermsDomain`: the domain condition of `closedTermsRange` on `X × Y`.
* `IntervalBalls.closedTermsBall`: the balls of `closedTermsRange`.

## Main results

* `closedTermsRange_sound`: under the domain condition, `closedTermsRange cs p X Y` encloses the
  sum of the closed-form terms at every point of `X × Y`.
* `closedTermsDomain_of_pos`: on a cell with `X.lo > 0` every closed-form term lies in the domain.
* `closedTermsDomain_of_radiusSq_pos`: away from the origin every radial closed-form term lies in
  the domain.
* `powerWeightDerivRange_sound`: the enclosure of `∂_x ^ i ∂_y ^ j` of a power weight on `X × Y`
  with `X.lo > 0`.
* `radialWeightDerivRange_sound`: the enclosure of `∂_x ^ i ∂_y ^ j` of a radial weight on `X × Y`
  away from the origin.
* `IntervalBalls.closedTermsBall_encloses`: balls of `X`, `Y` give balls of
  `closedTermsRange cs p X Y`.

## References

* R. J. George, W. Adkisson and A. Anandkumar, "FloatLib: Verified Floating-Point Arithmetic in
  Lean", arXiv:2609.19352, 2026.
  <https://arxiv.org/abs/2609.19352>
  <https://github.com/lean-dojo/FloatLib>
-/

@[expose] public section

namespace CAS.Numerics

open CAS.Continuum CAS.Polynomial PDE.Analysis

/-- The sum of a list of intervals. -/
def listSumRange (L : List RationalInterval) : RationalInterval :=
  L.foldr RationalInterval.add (RationalInterval.const 0)

/-- If `F l` encloses `f l` for every `l ∈ L`, the sum of the intervals `F l` encloses
`∑ l ∈ L, f l`. -/
theorem listSumRange_sound {ι : Type*} (L : List ι) {F : ι → RationalInterval} {f : ι → ℝ}
    (h : ∀ l ∈ L, (F l).MemReal (f l)) : (listSumRange (L.map F)).MemReal (L.map f).sum := by
  induction L with
  | nil => simpa [listSumRange] using RationalInterval.memReal_const 0
  | cons l L ih =>
    simp only [listSumRange, List.map_cons, List.foldr_cons, List.sum_cons] at ih ⊢
    exact RationalInterval.add_sound (h l List.mem_cons_self)
      (ih fun l hl ↦ h l (List.mem_cons_of_mem _ hl))

/-- The enclosure `X ^ 2 + Y ^ 2` of `x ^ 2 + y ^ 2`. -/
def radiusSqRange (X Y : RationalInterval) : RationalInterval := (X.powNat 2).add (Y.powNat 2)

/-- `radiusSqRange X Y` encloses `x ^ 2 + y ^ 2` for `x ∈ X` and `y ∈ Y`. -/
theorem radiusSqRange_sound {X Y : RationalInterval} {x y : ℝ} (hx : X.MemReal x)
    (hy : Y.MemReal y) : (radiusSqRange X Y).MemReal (x ^ 2 + y ^ 2) :=
  RationalInterval.add_sound (RationalInterval.powNat_sound hx 2)
    (RationalInterval.powNat_sound hy 2)

/-- The enclosure of one closed-form term on `X × Y`; a term with `axial = 0` has no factor in
`x`. -/
def closedTermRange (c : ClosedTerm) (p : RationalInterval.PowerPrecision)
    (X Y : RationalInterval) : RationalInterval :=
  if c.axial = 0 then
    (RationalInterval.nestedRange c.numerator X Y).mul
      (RationalInterval.rpowRat (radiusSqRange X Y) c.radial p)
  else
    (RationalInterval.nestedRange c.numerator X Y).mul
      ((RationalInterval.rpowRat X c.axial p).mul
        (RationalInterval.rpowRat (radiusSqRange X Y) c.radial p))

/-- The enclosure of a sum of closed-form terms on `X × Y`. -/
def closedTermsRange (cs : List ClosedTerm) (p : RationalInterval.PowerPrecision)
    (X Y : RationalInterval) : RationalInterval :=
  listSumRange (cs.map fun c ↦ closedTermRange c p X Y)

/-- The domain condition of `closedTermsRange` on `X × Y`. -/
def ClosedTermsDomain (cs : List ClosedTerm) (X Y : RationalInterval) : Prop :=
  ∀ c ∈ cs, (c.axial = 0 ∨ RationalInterval.PowDomain X c.axial) ∧
    RationalInterval.PowDomain (radiusSqRange X Y) c.radial

/-- Under the domain condition, `closedTermsRange cs p X Y` encloses the sum of the closed-form
terms `cs` at every point of `X × Y`. -/
theorem closedTermsRange_sound {cs : List ClosedTerm} (p : RationalInterval.PowerPrecision)
    {X Y : RationalInterval} (hd : ClosedTermsDomain cs X Y) {x y : ℝ} (hx : X.MemReal x)
    (hy : Y.MemReal y) :
    (closedTermsRange cs p X Y).MemReal ((cs.map fun c ↦ c.eval x y).sum) := by
  refine listSumRange_sound cs fun c hc ↦ ?_
  have hN := RationalInterval.nestedRange_sound c.numerator hx hy
  have hS := RationalInterval.rpowRat_sound (hd c hc).2 p (radiusSqRange_sound hx hy)
  unfold closedTermRange
  split_ifs with h0
  · have h := RationalInterval.mul_sound hN hS
    simpa [ClosedTerm.eval, h0] using h
  · have hax : RationalInterval.PowDomain X c.axial := (hd c hc).1.resolve_left h0
    have h := RationalInterval.mul_sound hN
      (RationalInterval.mul_sound (RationalInterval.rpowRat_sound hax p hx) hS)
    rw [← mul_assoc] at h
    exact h

/-- The lower end of the square `X ^ 2` of an interval with `0 ≤ X.lo` is `X.lo ^ 2`. -/
theorem powNat_two_lo_of_nonneg {X : RationalInterval} (hX : 0 ≤ X.lo) :
    (X.powNat 2).lo = X.lo ^ 2 := by
  simp only [RationalInterval.powNat, RationalInterval.ofFloatLib,
    FloatLib.Numerics.Interval.powBounds, FloatLib.Numerics.Interval.absBounds]
  simp [hX, IntervalBalls.npowBinRec_eq_pow]

/-- The lower end of the square `X ^ 2` of an interval is nonnegative. -/
theorem powNat_two_lo_nonneg (X : RationalInterval) : 0 ≤ (X.powNat 2).lo := by
  simp only [RationalInterval.powNat, RationalInterval.ofFloatLib,
    FloatLib.Numerics.Interval.powBounds]
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  rw [IntervalBalls.npowBinRec_eq_pow]
  exact sq_nonneg _

/-- On a cell with `X.lo > 0` every closed-form term lies in the domain. -/
theorem closedTermsDomain_of_pos (cs : List ClosedTerm) {X : RationalInterval}
    (Y : RationalInterval) (hX : 0 < X.lo) : ClosedTermsDomain cs X Y := by
  have hS : 0 < (radiusSqRange X Y).lo := by
    rw [radiusSqRange, RationalInterval.add_lo, powNat_two_lo_of_nonneg hX.le]
    have := powNat_two_lo_nonneg Y
    positivity
  exact fun c _ ↦ ⟨Or.inr (Or.inr hX), Or.inr hS⟩

/-- Away from the origin every radial closed-form term lies in the domain. -/
theorem closedTermsDomain_of_radiusSq_pos {cs : List ClosedTerm} (hax : ∀ c ∈ cs, c.axial = 0)
    {X Y : RationalInterval} (hS : 0 < (radiusSqRange X Y).lo) : ClosedTermsDomain cs X Y :=
  fun c hc ↦ ⟨Or.inl (hax c hc), Or.inr hS⟩

/-- The closed-form terms of the derivatives of a radial weight carry no factor in `x`. -/
theorem radialWeightClosed_axial (ts : List PowerTerm) (i j : ℕ) :
    ∀ c ∈ radialWeightClosed ts i j, c.axial = 0 := by
  intro c hc
  simp only [radialWeightClosed, List.mem_map] at hc
  obtain ⟨t, _, rfl⟩ := hc
  rfl

/-- The enclosure of `∂_x ^ i ∂_y ^ j` of a power weight on `X × Y` with `X.lo > 0`. -/
theorem powerWeightDerivRange_sound (ts : List PowerTerm) (i j : ℕ)
    (p : RationalInterval.PowerPrecision) {X Y : RationalInterval}
    (hd : ClosedTermsDomain (powerWeightClosed ts i j) X Y) (hX : 0 < X.lo) {x y : ℝ}
    (hx : X.MemReal x) (hy : Y.MemReal y) :
    (closedTermsRange (powerWeightClosed ts i j) p X Y).MemReal
      (iteratedDeriv i (fun u ↦ iteratedDeriv j (fun v ↦ powerWeight ts u v) y) x) := by
  have hx0 : 0 < x := (show (0 : ℝ) < X.lo by exact_mod_cast hX).trans_le hx.1
  rw [iteratedDeriv_powerWeight ts i j hx0, powerWeightDeriv_eq_closed]
  exact closedTermsRange_sound p hd hx hy

/-- The enclosure of `∂_x ^ i ∂_y ^ j` of a radial weight on `X × Y` away from the origin. -/
theorem radialWeightDerivRange_sound (ts : List PowerTerm) (hts : ∀ t ∈ ts, t.axial = 0)
    (i j : ℕ) (p : RationalInterval.PowerPrecision) {X Y : RationalInterval}
    (hd : ClosedTermsDomain (radialWeightClosed ts i j) X Y) {x y : ℝ} (hS : 0 < x ^ 2 + y ^ 2)
    (hx : X.MemReal x) (hy : Y.MemReal y) :
    (closedTermsRange (radialWeightClosed ts i j) p X Y).MemReal
      (iteratedDeriv i (fun u ↦ iteratedDeriv j (fun v ↦ powerWeight ts u v) y) x) := by
  rw [iteratedDeriv_radialWeight ts hts i j hS, radialWeightDeriv_eq_closed]
  exact closedTermsRange_sound p hd hx hy

/-! ### Balls -/

namespace IntervalBalls

/-- The sum of a list of balls. -/
def listSumBall (P : ℕ) (L : List IntervalBalls) : IntervalBalls :=
  L.foldr add (const P 0)

/-- If `FB l` encloses `F l` for every `l ∈ L`, the sum of the balls encloses the sum of the
intervals. -/
theorem listSumBall_encloses {P : ℕ} {ι : Type*} (L : List ι) {FB : ι → IntervalBalls}
    {F : ι → RationalInterval} (h : ∀ l ∈ L, (FB l).Encloses P (F l)) :
    (listSumBall P (L.map FB)).Encloses P (listSumRange (L.map F)) := by
  induction L with
  | nil => exact const_encloses 0
  | cons l L ih =>
    simp only [listSumBall, listSumRange, List.map_cons, List.foldr_cons] at ih ⊢
    exact add_encloses (h l List.mem_cons_self) (ih fun l hl ↦ h l (List.mem_cons_of_mem _ hl))

/-- Balls of `radiusSqRange X Y`. -/
def radiusSqBall (P : ℕ) (SX SY : IntervalBalls) : IntervalBalls :=
  (powNat P SX 2).add (powNat P SY 2)

/-- Balls `SX`, `SY` of `X`, `Y` give balls of `radiusSqRange X Y`. -/
theorem radiusSqBall_encloses {P : ℕ} {SX SY : IntervalBalls} {X Y : RationalInterval}
    (hX : SX.Encloses P X) (hY : SY.Encloses P Y) :
    (radiusSqBall P SX SY).Encloses P (radiusSqRange X Y) :=
  add_encloses (powNat_encloses hX 2) (powNat_encloses hY 2)

/-- Balls of `closedTermRange c p X Y`. -/
def closedTermBall (P : ℕ) (c : ClosedTerm) (p : RationalInterval.PowerPrecision)
    (SX SY : IntervalBalls) : IntervalBalls :=
  Bool.rec
    (mul P (nestedRangeBall P c.numerator SX SY)
      (mul P (rpowRatBall P p c.axial SX) (rpowRatBall P p c.radial (radiusSqBall P SX SY))))
    (mul P (nestedRangeBall P c.numerator SX SY)
      (rpowRatBall P p c.radial (radiusSqBall P SX SY)))
    (decide (c.axial = 0))

/-- Balls `SX`, `SY` of `X`, `Y` give balls of the enclosure `closedTermRange c p X Y` of one term.
-/
theorem closedTermBall_encloses {P : ℕ} {c : ClosedTerm} {p : RationalInterval.PowerPrecision}
    {SX SY : IntervalBalls} {X Y : RationalInterval} (hX : SX.Encloses P X)
    (hY : SY.Encloses P Y) :
    (closedTermBall P c p SX SY).Encloses P (closedTermRange c p X Y) := by
  unfold closedTermBall closedTermRange
  by_cases h0 : c.axial = 0
  · simp only [h0, decide_true, ↓reduceIte]
    exact mul_encloses (nestedRangeBall_encloses c.numerator hX hY)
      (rpowRatBall_encloses (radiusSqBall_encloses hX hY))
  · simp only [h0, decide_false, ↓reduceIte]
    exact mul_encloses (nestedRangeBall_encloses c.numerator hX hY)
      (mul_encloses (rpowRatBall_encloses hX) (rpowRatBall_encloses (radiusSqBall_encloses hX hY)))

/-- Balls of `closedTermsRange cs p X Y`. -/
def closedTermsBall (P : ℕ) (cs : List ClosedTerm) (p : RationalInterval.PowerPrecision)
    (SX SY : IntervalBalls) : IntervalBalls :=
  listSumBall P (cs.map fun c ↦ closedTermBall P c p SX SY)

/-- Balls `SX`, `SY` of `X`, `Y` give balls of the enclosure `closedTermsRange cs p X Y` of a sum of
terms. -/
theorem closedTermsBall_encloses {P : ℕ} {cs : List ClosedTerm}
    {p : RationalInterval.PowerPrecision} {SX SY : IntervalBalls} {X Y : RationalInterval}
    (hX : SX.Encloses P X) (hY : SY.Encloses P Y) :
    (closedTermsBall P cs p SX SY).Encloses P (closedTermsRange cs p X Y) :=
  listSumBall_encloses cs fun _ _ ↦ closedTermBall_encloses hX hY

end IntervalBalls

end CAS.Numerics
