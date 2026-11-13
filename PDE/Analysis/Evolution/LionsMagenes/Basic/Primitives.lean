/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity.Finset

/-!
# Time primitives for Lions–Magenes theory

The Lions–Magenes time-regularity argument, and the energy-method uniqueness proofs for
parabolic and hyperbolic equations, repeatedly form indefinite Bochner integrals of
trajectories that are only known to lie in `L²(a, b; E)` or `L¹(a, b; V*)`. We collect
the elementary calculus of those primitives.

Three objects are involved. First, an `L²` class on `Ioc a b` is interval integrable on
`[a, b]`, so it has an ordinary interval integral. Second, the *backward* primitive
`backwardTimePrimitive u s t = ∫ₜˢ u(r) dr`, taken from a variable time `t` up to a fixed
terminal time `s`, is the auxiliary function `v(t) = ∫ₜˢ u(τ) dτ` of Evans's uniqueness
proof for second-order hyperbolic equations (§7.2.2, Theorem 4): it has derivative `-u`
and vanishes at `t = s`, and testing against it replaces the inadmissible test `uₜ`.
Third, the forward primitive `dualPrimitive g a t = ∫ₐᵗ g(s) ds` of a `V*`-valued
trajectory is the continuous function whose increments realise the fundamental theorem
of calculus in `V*` in the Lions–Magenes theorem.

## Main results

* `intervalIntegrable_coeFn_L2_restrict_Ioc`: an `L²(Ioc a b; E)` class is interval
  integrable on `[a, b]`.
* `backwardTimePrimitive` with `backwardTimePrimitive_terminal`, `_sub`, `_split`,
  `ContinuousLinearMap.map_backwardTimePrimitive`: the vanishing at the terminal time,
  linearity, additivity in the interval, and commutation with bounded linear maps.
* `backwardTimePrimitive_eq_forward_sub`, `norm_sq_backwardTimePrimitive_le_forward`:
  `∫ₜˢ u = w(s) - w(t)` for the forward primitive `w`, and the resulting bound
  `‖∫ₜˢ u‖² ≤ 2 ‖w(s)‖² + 2 ‖w(t)‖²`.
* `norm_backwardTimePrimitive_le`, `continuousOn_backwardTimePrimitive`: the variation
  bound and continuity on the whole compact interval.
* `dualPrimitive` with `continuousOn_dualPrimitive`, `dualPrimitive_sub`,
  `dualPrimitive_apply`, `norm_dualPrimitive_sub_le`: continuity, the increment formula,
  commutation of evaluation at `v ∈ V` with the integral, and the variation bound.

## Implementation notes

Interval integrals are used throughout (rather than set integrals over `Ioc`), so all
statements hold for either orientation of the interval; hypotheses are phrased with the
unordered interval `uIcc a b` wherever orientation is irrelevant. Integrability is always
an explicit hypothesis, since Mathlib's interval integral of a non-integrable function is
`0` and the identities would otherwise be vacuous.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, proof of Theorem 4 (the function `v(t) = ∫ₜˢ u(τ) dτ`
  and the bound after (41)). <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped InnerProductSpace Interval Topology

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

section LpInterval

/--
An `L²` Bochner class on `(a,b]` is integrable on the finite interval and
therefore has an ordinary interval integral.

This is needed whenever a weak solution, which lies in
`L²(a,b;E)`, is used to form a time primitive. The theorem is stated
for an arbitrary normed target space and does not choose a special
representative beyond Mathlib's canonical coercion from `Lp`.
-/
theorem intervalIntegrable_coeFn_L2_restrict_Ioc
    {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ}
    (u : Lp E 2 (volume.restrict (Set.Ioc a b)))
    (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ u t) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact (Lp.memLp u).integrable (by norm_num)

end LpInterval

section BackwardTimePrimitive

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/--
The backward time primitive used in Evans's hyperbolic uniqueness argument
(§7.2.2, proof of Theorem 4): `backwardTimePrimitive u s t = ∫ r in t..s, u r`.

For a fixed terminal time `s`, its time derivative is `-u`; in particular it
is the low-regularity substitute for testing the wave equation directly by
`uₜ`, which need not be an admissible energy-space test.
-/
def backwardTimePrimitive
    (u : ℝ → E) (s t : ℝ) : E :=
  ∫ r in t..s, u r

/-- The backward primitive vanishes at its terminal time: `∫ₛˢ u = 0`. -/
@[simp]
theorem backwardTimePrimitive_terminal
    (u : ℝ → E) (s : ℝ) :
    backwardTimePrimitive u s s = 0 := by
  simp [backwardTimePrimitive]

/-- Bounded linear maps commute with the backward time primitive. -/
theorem ContinuousLinearMap.map_backwardTimePrimitive
    [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℝ] F) {u : ℝ → E} {s t : ℝ}
    (hu : IntervalIntegrable u volume t s) :
    L (backwardTimePrimitive u s t) =
      backwardTimePrimitive (fun r ↦ L (u r)) s t := by
  simpa only [backwardTimePrimitive] using
    (L.intervalIntegral_comp_comm hu).symm

/-- The backward primitive is linear in its trajectory. -/
theorem backwardTimePrimitive_sub
    {u v : ℝ → E} {s t : ℝ}
    (hu : IntervalIntegrable u volume t s)
    (hv : IntervalIntegrable v volume t s) :
    backwardTimePrimitive (fun r ↦ u r - v r) s t =
      backwardTimePrimitive u s t - backwardTimePrimitive v s t := by
  exact intervalIntegral.integral_sub hu hv

/--
Splitting a backward primitive at an intermediate time.  The identity is
oriented as Evans uses it: the primitive from `t` to `s` is the sum of the
pieces from `t` to `r` and from `r` to `s`.
-/
theorem backwardTimePrimitive_split
    {u : ℝ → E} {t r s : ℝ}
    (htr : IntervalIntegrable u volume t r)
    (hrs : IntervalIntegrable u volume r s) :
    backwardTimePrimitive u s t =
      backwardTimePrimitive u r t + backwardTimePrimitive u s r := by
  simpa only [backwardTimePrimitive] using
    (intervalIntegral.integral_add_adjacent_intervals htr hrs).symm

/--
The backward primitive is the difference of two forward primitives.

If `w(t) = ∫ₐᵗ u(r) dr`, then

`∫ₜˢ u(r) dr = w(s) - w(t)`.

The endpoint assumptions only ensure that the two subinterval integrals
inherit integrability from `[a,b]`; no ordering between `t` and `s` is
required.
-/
theorem backwardTimePrimitive_eq_forward_sub
    {u : ℝ → E} {a b s t : ℝ}
    (hu : IntervalIntegrable u volume a b)
    (hs : s ∈ Set.uIcc a b)
    (ht : t ∈ Set.uIcc a b) :
    backwardTimePrimitive u s t =
      (∫ r in a..s, u r) - ∫ r in a..t, u r := by
  simpa only [backwardTimePrimitive] using
    (intervalIntegral.integral_interval_sub_left
      (hu.mono_set
        (Set.uIcc_subset_uIcc Set.left_mem_uIcc hs))
      (hu.mono_set
        (Set.uIcc_subset_uIcc Set.left_mem_uIcc ht))).symm

/--
Squared-norm estimate for the preceding forward/backward primitive identity:

`‖w(s)-w(t)‖² ≤ 2‖w(s)‖² + 2‖w(t)‖²`.

This is the abstract Banach-space inequality used after (41) in the proof of Evans
§7.2.2, Theorem 4, where the energy of the backward primitive `∫ₜˢ u` is bounded by
the energies of the two forward primitives. It is the elementary bound
`(x + y)² ≤ 2x² + 2y²` applied to the triangle inequality.
-/
theorem norm_sq_backwardTimePrimitive_le_forward
    {u : ℝ → E} {a b s t : ℝ}
    (hu : IntervalIntegrable u volume a b)
    (hs : s ∈ Set.uIcc a b)
    (ht : t ∈ Set.uIcc a b) :
    ‖backwardTimePrimitive u s t‖ ^ 2 ≤
      2 * ‖∫ r in a..s, u r‖ ^ 2 +
        2 * ‖∫ r in a..t, u r‖ ^ 2 := by
  rw [backwardTimePrimitive_eq_forward_sub hu hs ht]
  have htriangle :
      ‖(∫ r in a..s, u r) - ∫ r in a..t, u r‖ ≤
        ‖∫ r in a..s, u r‖ + ‖∫ r in a..t, u r‖ :=
    norm_sub_le _ _
  have htriangleSq :
      ‖(∫ r in a..s, u r) - ∫ r in a..t, u r‖ ^ 2 ≤
        (‖∫ r in a..s, u r‖ + ‖∫ r in a..t, u r‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 htriangle
  nlinarith [
    htriangleSq,
    sq_nonneg
      (‖∫ r in a..s, u r‖ - ‖∫ r in a..t, u r‖)]

/-- The standard variation estimate for a backward Bochner primitive. -/
theorem norm_backwardTimePrimitive_le
    {u : ℝ → E} {s t : ℝ}
    (hts : t ≤ s) :
    ‖backwardTimePrimitive u s t‖ ≤ ∫ r in t..s, ‖u r‖ := by
  exact intervalIntegral.norm_integral_le_integral_norm hts

/--
The backward primitive of an interval-integrable Banach-valued trajectory is
continuous on the whole compact time interval.

Writing

`∫ₜˢ u(r) dr = (∫ₐˢ u(r) dr) - (∫ₐᵗ u(r) dr)`

reduces the claim to continuity of the ordinary Bochner primitive.  The
terminal time `s` is allowed anywhere in the unordered interval `[[a,b]]`;
the resulting theorem therefore applies unchanged on forward or reversed
time intervals.
-/
theorem continuousOn_backwardTimePrimitive
    {u : ℝ → E} {a b s : ℝ}
    (hu : IntervalIntegrable u volume a b)
    (hs : s ∈ Set.uIcc a b) :
    ContinuousOn (backwardTimePrimitive u s) (Set.uIcc a b) := by
  have hprimitive :
      ContinuousOn (fun t ↦ ∫ r in a..t, u r) (Set.uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval'
      hu Set.left_mem_uIcc
  have hconstant :
      ContinuousOn (fun _ : ℝ ↦ ∫ r in a..s, u r) (Set.uIcc a b) :=
    continuousOn_const
  apply (hconstant.sub hprimitive).congr
  intro t ht
  rw [show backwardTimePrimitive u s t =
      (∫ r in a..s, u r) - ∫ r in a..t, u r by
    simpa only [backwardTimePrimitive] using
      (intervalIntegral.integral_interval_sub_left
        (hu.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc hs))
        (hu.mono_set
          (Set.uIcc_subset_uIcc Set.left_mem_uIcc ht))).symm]
  rfl

end BackwardTimePrimitive

section DualPrimitive

/-- The `V*`-valued primitive of an integrable dual trajectory. -/
def dualPrimitive (g : ℝ → StrongDual ℝ V) (a t : ℝ) :
    StrongDual ℝ V :=
  ∫ s in a..t, g s

/-- An interval-integrable `V*` trajectory has a continuous primitive on the
whole time interval. -/
theorem continuousOn_dualPrimitive
    {g : ℝ → StrongDual ℝ V} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) :
    ContinuousOn (dualPrimitive g a) (uIcc a b) := by
  exact intervalIntegral.continuousOn_primitive_interval'
    hg left_mem_uIcc

/-- Increment identity for the dual-valued primitive. -/
theorem dualPrimitive_sub
    {g : ℝ → StrongDual ℝ V} {a s t : ℝ}
    (has : IntervalIntegrable g volume a s)
    (hst : IntervalIntegrable g volume s t) :
    dualPrimitive g a t - dualPrimitive g a s = ∫ r in s..t, g r := by
  rw [dualPrimitive, dualPrimitive]
  rw [← intervalIntegral.integral_add_adjacent_intervals has hst]
  abel

/-- Evaluation of a dual-valued primitive commutes with integration. -/
theorem dualPrimitive_apply
    {g : ℝ → StrongDual ℝ V} {a t : ℝ}
    (hg : IntervalIntegrable g volume a t) (v : V) :
    dualPrimitive g a t v = ∫ s in a..t, g s v := by
  exact ContinuousLinearMap.intervalIntegral_apply hg v

/-- The standard variation bound for a `V*`-valued primitive. -/
theorem norm_dualPrimitive_sub_le
    {g : ℝ → StrongDual ℝ V} {a s t : ℝ}
    (has : IntervalIntegrable g volume a s)
    (hst : IntervalIntegrable g volume s t) (hstOrder : s ≤ t) :
    ‖dualPrimitive g a t - dualPrimitive g a s‖ ≤
      ∫ r in s..t, ‖g r‖ := by
  rw [dualPrimitive_sub has hst]
  exact intervalIntegral.norm_integral_le_integral_norm hstOrder

end DualPrimitive

end PDE.Analysis.Evolution
