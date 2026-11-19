/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Numerics.GridBallRpow
public import CAS.Continuum.Interval.Rational.Polynomial
public import PDE.Analysis.Calculus.PolynomialPowerDerivatives

/-!
# Balls for polynomials, powers of polynomials and products of derivatives

* `coeffRangeBall P l S` and `nestedRangeBall P M SX SY` enclose the interval Horner evaluations
  `coeffRange l I` and `nestedRange M X Y` (`coeffRangeBall_encloses`, `nestedRangeBall_encloses`).
* `polyPowRangeOf N b p I DI = coeffRange N I · rpowRat DI b p` contains `N(x) D(x) ^ b` for
  `x ∈ I` when `DI` contains `D(x)` and lies in the domain of the power (`polyPowRangeOf_sound`);
  with the numerators `powerDerivNumerator N D a k` it contains the `k`-th derivative of
  `N D ^ a` (`iteratedDeriv_mem_polyPowRangeOf`). `polyPowRange` takes the Horner range of `D`;
  a sharper `DI`, such as `1 + I ^ 4` for `1 + x ^ 4`, keeps the domain condition on intervals
  around zero. `polyPowBallOf` and `polyPowBall` are the mirrors.
* `leibnizRange n F G = ∑ i ≤ n, (n choose i) F_i G_(n-i)` contains the `n`-th derivative of a
  product `f g` at `x` when `F_i ∋ f^(i)(x)` and `G_j ∋ g^(j)(x)` (`leibnizRange_sound`);
  `leibnizBall` is its mirror.
* `monotoneRange g h I` is the interval from the lower end of `g I.lo` to the upper end of
  `g I.hi`; it contains `f x` for `x ∈ I` when `f` is monotone and `g a ∋ f a` at every rational
  `a` (`monotoneRange_sound`). `IntervalBalls.ends f S` is its mirror (`ends_encloses`). The
  lemmas are proved once for abstract `g` and `f`, so that instances never compare the unfolded
  bodies of two endpoint enclosures.

## Main results

* `IntervalBalls.coeffRangeBall_encloses`: `coeffRangeBall P l S` encloses `coeffRange l I` when
  `S` encloses `I`.
* `IntervalBalls.nestedRangeBall_encloses`: `nestedRangeBall P M SX SY` encloses
  `nestedRange M X Y`.
* `polyPowRangeOf_sound`: `polyPowRangeOf N b p I DI` contains `N(x) D(x) ^ b` for `x ∈ I`.
* `iteratedDeriv_mem_polyPowRangeOf`: the `k`-th derivative of `N D ^ a` lies in
  `polyPowRangeOf` of the `k`-th numerator where `D > 0`.
* `IntervalBalls.polyPowBall_encloses`: `polyPowBall P N D b p S` encloses `polyPowRange N D b p I`.
* `leibnizRange_sound`: `leibnizRange n F G` contains `(f g)⁽ⁿ⁾(x)`.
* `monotoneRange_sound`: for a monotone `f`, `monotoneRange g h I` contains `f x` for `x ∈ I`.
* `IntervalBalls.ends_encloses`: `ends f S` encloses `monotoneRange g h I` when `S` encloses `I`.
-/

@[expose] public section

namespace CAS.Numerics

open CAS.Continuum CAS.Polynomial

namespace IntervalBalls

/-- Balls of `coeffRange l I` from balls `S` of `I`. -/
def coeffRangeBall (P : ℕ) (l : List ℚ) (S : IntervalBalls) : IntervalBalls :=
  l.foldr (fun c acc ↦ (const P c).add (mul P S acc)) (const P 0)

/-- `coeffRangeBall P l S` encloses the Horner range `coeffRange l I` when `S` encloses `I`. -/
theorem coeffRangeBall_encloses {P : ℕ} (l : List ℚ) {S : IntervalBalls} {I : RationalInterval}
    (hS : S.Encloses P I) :
    (coeffRangeBall P l S).Encloses P (RationalInterval.coeffRange l I) := by
  induction l with
  | nil => exact const_encloses 0
  | cons c l ih =>
    simpa [coeffRangeBall, RationalInterval.coeffRange] using
      add_encloses (const_encloses c) (mul_encloses hS ih)

/-- Balls of `nestedRange M X Y` from balls `SX` of `X` and `SY` of `Y`. -/
def nestedRangeBall (P : ℕ) (M : List (List ℚ)) (SX SY : IntervalBalls) : IntervalBalls :=
  M.foldr (fun m acc ↦ (coeffRangeBall P m SY).add (mul P SX acc)) (const P 0)

/-- `nestedRangeBall P M SX SY` encloses `nestedRange M X Y` when `SX` encloses `X` and `SY`
encloses `Y`. -/
theorem nestedRangeBall_encloses {P : ℕ} (M : List (List ℚ)) {SX SY : IntervalBalls}
    {X Y : RationalInterval} (hX : SX.Encloses P X) (hY : SY.Encloses P Y) :
    (nestedRangeBall P M SX SY).Encloses P (RationalInterval.nestedRange M X Y) := by
  induction M with
  | nil => exact const_encloses 0
  | cons m M ih =>
    simpa [nestedRangeBall, RationalInterval.nestedRange] using
      add_encloses (coeffRangeBall_encloses m hY) (mul_encloses hX ih)

end IntervalBalls

/-! ### A polynomial times a power of a polynomial -/

/-- The enclosure `coeffRange N I · rpowRat DI b p` of `N(x) D(x) ^ b`, from an enclosure `DI` of
the values of `D` on `I`. -/
def polyPowRangeOf (N : List ℚ) (b : ℚ) (p : RationalInterval.PowerPrecision)
    (I DI : RationalInterval) : RationalInterval :=
  (RationalInterval.coeffRange N I).mul (RationalInterval.rpowRat DI b p)

/-- `polyPowRangeOf N b p I DI` contains `N(x) D(x) ^ b` for `x ∈ I` when `DI` contains `D(x)` and
lies in the domain of the power `b`. -/
theorem polyPowRangeOf_sound (N D : List ℚ) (b : ℚ) (p : RationalInterval.PowerPrecision)
    {I DI : RationalInterval} (hD : RationalInterval.PowDomain DI b) {x : ℝ} (hx : I.MemReal x)
    (hDx : DI.MemReal (coeffEval D x)) :
    (polyPowRangeOf N b p I DI).MemReal (coeffEval N x * coeffEval D x ^ (b : ℝ)) :=
  RationalInterval.mul_sound (RationalInterval.coeffRange_sound N hx)
    (RationalInterval.rpowRat_sound hD p hDx)

/-- The enclosure of `N(x) D(x) ^ b` with the Horner range of `D`. -/
def polyPowRange (N D : List ℚ) (b : ℚ) (p : RationalInterval.PowerPrecision)
    (I : RationalInterval) : RationalInterval :=
  polyPowRangeOf N b p I (RationalInterval.coeffRange D I)

/-- `polyPowRange N D b p I` contains `N(x) D(x) ^ b` for `x ∈ I` when the Horner range of `D` on
`I` lies in the domain of the power `b`. -/
theorem polyPowRange_sound (N D : List ℚ) (b : ℚ) (p : RationalInterval.PowerPrecision)
    {I : RationalInterval} (hD : RationalInterval.PowDomain (RationalInterval.coeffRange D I) b)
    {x : ℝ} (hx : I.MemReal x) :
    (polyPowRange N D b p I).MemReal (coeffEval N x * coeffEval D x ^ (b : ℝ)) :=
  polyPowRangeOf_sound N D b p hD hx (RationalInterval.coeffRange_sound D hx)

/-- The `k`-th derivative of `N D ^ a` lies in `polyPowRangeOf` of the `k`-th numerator, at every
point of an open set where `D > 0`. -/
theorem iteratedDeriv_mem_polyPowRangeOf (N D : List ℚ) (a : ℚ) (k : ℕ)
    (p : RationalInterval.PowerPrecision) {U : Set ℝ} (hU : IsOpen U)
    (hDU : ∀ x ∈ U, 0 < coeffEval D x) {I DI : RationalInterval}
    (hD : RationalInterval.PowDomain DI (a - k)) {x : ℝ} (hxU : x ∈ U) (hx : I.MemReal x)
    (hDx : DI.MemReal (coeffEval D x)) :
    (polyPowRangeOf (PDE.Analysis.powerDerivNumerator N D a k) (a - k) p I DI).MemReal
      (iteratedDeriv k (fun y ↦ coeffEval N y * coeffEval D y ^ (a : ℝ)) x) := by
  rw [PDE.Analysis.iteratedDeriv_coeffEval_mul_rpow N D a hU hDU k hxU]
  have h := polyPowRangeOf_sound (PDE.Analysis.powerDerivNumerator N D a k) D (a - k) p hD hx hDx
  push_cast at h
  exact h

/-- `iteratedDeriv_mem_polyPowRangeOf` with the Horner range of `D`. -/
theorem iteratedDeriv_mem_polyPowRange (N D : List ℚ) (a : ℚ) (k : ℕ)
    (p : RationalInterval.PowerPrecision) {U : Set ℝ} (hU : IsOpen U)
    (hDU : ∀ x ∈ U, 0 < coeffEval D x) {I : RationalInterval}
    (hD : RationalInterval.PowDomain (RationalInterval.coeffRange D I) (a - k)) {x : ℝ}
    (hxU : x ∈ U) (hx : I.MemReal x) :
    (polyPowRange (PDE.Analysis.powerDerivNumerator N D a k) D (a - k) p I).MemReal
      (iteratedDeriv k (fun y ↦ coeffEval N y * coeffEval D y ^ (a : ℝ)) x) :=
  iteratedDeriv_mem_polyPowRangeOf N D a k p hU hDU hD hxU hx
    (RationalInterval.coeffRange_sound D hx)

namespace IntervalBalls

/-- Balls of `polyPowRangeOf N b p I DI` from balls `S` of `I` and `SD` of `DI`. -/
def polyPowBallOf (P : ℕ) (N : List ℚ) (b : ℚ) (p : RationalInterval.PowerPrecision)
    (S SD : IntervalBalls) : IntervalBalls :=
  mul P (coeffRangeBall P N S) (rpowRatBall P p b SD)

/-- `polyPowBallOf P N b p S SD` encloses `polyPowRangeOf N b p I DI` when `S` encloses `I` and
`SD` encloses `DI`. -/
theorem polyPowBallOf_encloses {P : ℕ} (N : List ℚ) (b : ℚ) (p : RationalInterval.PowerPrecision)
    {S SD : IntervalBalls} {I DI : RationalInterval} (hS : S.Encloses P I)
    (hSD : SD.Encloses P DI) :
    (polyPowBallOf P N b p S SD).Encloses P (polyPowRangeOf N b p I DI) :=
  mul_encloses (coeffRangeBall_encloses N hS) (rpowRatBall_encloses hSD)

/-- Balls of `polyPowRange N D b p I` from balls `S` of `I`. -/
def polyPowBall (P : ℕ) (N D : List ℚ) (b : ℚ) (p : RationalInterval.PowerPrecision)
    (S : IntervalBalls) : IntervalBalls :=
  polyPowBallOf P N b p S (coeffRangeBall P D S)

/-- `polyPowBall P N D b p S` encloses `polyPowRange N D b p I` when `S` encloses `I`. -/
theorem polyPowBall_encloses {P : ℕ} (N D : List ℚ) (b : ℚ) (p : RationalInterval.PowerPrecision)
    {S : IntervalBalls} {I : RationalInterval} (hS : S.Encloses P I) :
    (polyPowBall P N D b p S).Encloses P (polyPowRange N D b p I) :=
  polyPowBallOf_encloses N b p hS (coeffRangeBall_encloses D hS)

end IntervalBalls

/-! ### Monotone functions -/

/-- The interval from the lower end of `g I.lo` to the upper end of `g I.hi`. -/
def monotoneRange (g : ℚ → RationalInterval) (h : ∀ a b : ℚ, a ≤ b → (g a).lo ≤ (g b).hi)
    (I : RationalInterval) : RationalInterval :=
  RationalInterval.ofBounds (g I.lo).lo (g I.hi).hi (h _ _ I.hle)

/-- Point enclosures of a monotone function have ordered ends. -/
theorem monotone_ends_of_sound {g : ℚ → RationalInterval} {f : ℝ → ℝ} (hf : Monotone f)
    (hg : ∀ a : ℚ, (g a).MemReal (f a)) (a b : ℚ) (hab : a ≤ b) : (g a).lo ≤ (g b).hi := by
  have h := (hg a).1.trans ((hf (show (a : ℝ) ≤ b by exact_mod_cast hab)).trans (hg b).2)
  exact_mod_cast h

/-- For a monotone `f` with `g a ∋ f a` at every rational `a`, `monotoneRange g h I` contains `f x`
for every `x ∈ I`. -/
theorem monotoneRange_sound {g : ℚ → RationalInterval}
    {h : ∀ a b : ℚ, a ≤ b → (g a).lo ≤ (g b).hi} {f : ℝ → ℝ} (hf : Monotone f)
    (hg : ∀ a : ℚ, (g a).MemReal (f a)) {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    (monotoneRange g h I).MemReal (f x) :=
  ⟨(hg I.lo).1.trans (hf hx.1), (hf hx.2).trans (hg I.hi).2⟩

namespace IntervalBalls

/-- The lower ball of `f S.lo` and the upper ball of `f S.hi`. -/
def ends (f : GridBall → IntervalBalls) (S : IntervalBalls) : IntervalBalls :=
  ⟨(f S.lo).lo, (f S.hi).hi⟩

/-- `ends f S` encloses `monotoneRange g h I` when `S` encloses `I` and `f B` encloses `g a`
whenever `B` encloses `a`. -/
theorem ends_encloses {P : ℕ} {f : GridBall → IntervalBalls} {g : ℚ → RationalInterval}
    {h : ∀ a b : ℚ, a ≤ b → (g a).lo ≤ (g b).hi}
    (hf : ∀ {B : GridBall} {a : ℚ}, B.Encloses P a → (f B).Encloses P (g a))
    {S : IntervalBalls} {I : RationalInterval} (hS : S.Encloses P I) :
    (ends f S).Encloses P (monotoneRange g h I) :=
  ⟨(hf hS.1).1, (hf hS.2).2⟩

end IntervalBalls

/-! ### The Leibniz rule -/

/-- `∑ i ≤ n, (n choose i) F_i G_(n-i)`. -/
def leibnizRange (n : ℕ) (F G : ℕ → RationalInterval) : RationalInterval :=
  RationalInterval.sum (Finset.range (n + 1))
    (fun i ↦ (RationalInterval.const (n.choose i)).mul ((F i).mul (G (n - i))))

/-- **The Leibniz rule for enclosures.** For `f`, `g` of class `Cⁿ` at `x` with `F i ∋ f⁽ⁱ⁾(x)` and
`G j ∋ g⁽ʲ⁾(x)`, `leibnizRange n F G` contains `(f g)⁽ⁿ⁾(x)`. -/
theorem leibnizRange_sound {n : ℕ} {f g : ℝ → ℝ} {x : ℝ} (hf : ContDiffAt ℝ n f x)
    (hg : ContDiffAt ℝ n g x) {F G : ℕ → RationalInterval}
    (hF : ∀ i ≤ n, (F i).MemReal (iteratedDeriv i f x))
    (hG : ∀ j ≤ n, (G j).MemReal (iteratedDeriv j g x)) :
    (leibnizRange n F G).MemReal (iteratedDeriv n (fun y ↦ f y * g y) x) := by
  rw [iteratedDeriv_fun_mul hf hg]
  apply RationalInterval.sum_sound
  intro i hi
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h := RationalInterval.mul_sound (RationalInterval.memReal_const (n.choose i : ℚ))
    (RationalInterval.mul_sound (hF i hin) (hG (n - i) (Nat.sub_le n i)))
  push_cast at h
  rw [mul_assoc]
  exact h

namespace IntervalBalls

/-- Balls of `leibnizRange n F G` from balls `FB i` of `F i` and `GB j` of `G j`. -/
def leibnizBall (P n : ℕ) (FB GB : ℕ → IntervalBalls) : IntervalBalls :=
  sumNat P (n + 1) (fun i ↦ constMul (n.choose i) (mul P (FB i) (GB (n - i))))

/-- `leibnizBall P n FB GB` encloses `leibnizRange n F G` when `FB i` encloses `F i` and `GB j`
encloses `G j` for `i, j ≤ n`. -/
theorem leibnizBall_encloses {P n : ℕ} {FB GB : ℕ → IntervalBalls} {F G : ℕ → RationalInterval}
    (hF : ∀ i ≤ n, (FB i).Encloses P (F i)) (hG : ∀ j ≤ n, (GB j).Encloses P (G j)) :
    (leibnizBall P n FB GB).Encloses P (leibnizRange n F G) :=
  sumNat_encloses_range fun i hi ↦ constMul_encloses
    (mul_encloses (hF i (Nat.lt_succ_iff.mp hi)) (hG (n - i) (Nat.sub_le n i))) _

end IntervalBalls

end CAS.Numerics
