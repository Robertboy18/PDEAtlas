/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Solution.Singularity.FiniteTime.Norm.Trajectory

/-!
# Continuation criteria and finite-time norm growth

A model-specific local well-posedness theorem usually says that a solution
extends beyond its maximal time whenever a controlling norm remains bounded.
We record the logical consequences of such a criterion, which do not depend
on the equation. The blow-up alternative for semilinear parabolic equations (Quittner and
Souplet) and the Beale–Kato–Majda criterion for the three-dimensional Euler equations (see also
Majda and Bertozzi, Chapter 3) are criteria of this kind.

Extendability is an arbitrary proposition here, since there is no single
notion of PDE continuation: each equation comes with its own solution class,
data space, and extension theorem.

Norm-unboundedness and norm blow-up remain distinct. A continuation criterion
alone yields only one-sided norm-unboundedness; an additional persistence
property, such as monotonicity of the norm, is needed to obtain norm blow-up.

Both lifespan directions are covered. The unqualified predicates approach a
right endpoint from below, while the `FromRight` predicates approach a left
endpoint through later times.

## Main results

* `normUnboundedAt_iff_not_eventually_norm_bounded` (and the `WithinAt`, `FromRight`
  variants): `NormUnboundedAt u T` is the negation of an eventual norm bound on the left
  neighbourhood filter of `T`.
* `normUnboundedAt_of_not_extendable`, `normUnboundedAtFromRight_of_not_extendable`: the
  blow-up alternative. If bounded norm near `T` would allow extension and the solution does
  not extend, the norm is unbounded near `T`.
* `exists_normUnboundedAt_mem_Ioc_of_not_extendable`: combined with an independent lifespan
  bound `T ≤ τ`, this places a norm-unbounded time in `(t₀, τ]`.
* `NormUnboundedAt.normBlowsUpAt_of_monotoneOn`,
  `normBlowsUpAt_of_not_extendable_of_monotoneOn`: with a monotone norm, unboundedness becomes
  `‖u t‖ → ∞` as `t → T⁻`.

## References

* P. Quittner and P. Souplet, *Superlinear Parabolic Problems*, Birkhäuser Advanced Texts,
  Birkhäuser, 2007, chapter "Model Parabolic Problems", pp. 75-250.
  <https://doi.org/10.1007/978-3-7643-8442-5_3>
* J. T. Beale, T. Kato and A. Majda, "Remarks on the breakdown of smooth solutions for the 3-D
  Euler equations", *Comm. Math. Phys.* 94 (1984), 61-66.
  <https://doi.org/10.1007/BF01212349>
* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in
  Applied Mathematics 27, Cambridge University Press, 2001, Chapter 3, "Energy Methods for the
  Euler and the Navier–Stokes Equations", pp. 86-135.
  <https://doi.org/10.1017/CBO9780511613203.004>
-/

@[expose] public section

namespace PDE.Solution.Singularity.FiniteTime

open Filter Topology

/-- Norm-unboundedness within a set is exactly the failure of every eventual
norm bound along the corresponding restricted neighborhood filter. -/
theorem normUnboundedWithinAt_iff_not_eventually_norm_bounded
    {E : Type*} [Norm E] {u : ℝ → E} {s : Set ℝ} {T : ℝ} :
    NormUnboundedWithinAt u s T ↔
      ¬ ∃ C : ℝ, ∀ᶠ t in nhdsWithin T s, ‖u t‖ ≤ C := by
  simp only [NormUnboundedWithinAt, not_exists, Filter.not_eventually, not_le]

/-- Norm-unboundedness from below is exactly the failure of every eventual
norm bound on a left neighborhood of the terminal time. -/
theorem normUnboundedAt_iff_not_eventually_norm_bounded
    {E : Type*} [Norm E] {u : ℝ → E} {T : ℝ} :
    NormUnboundedAt u T ↔
      ¬ ∃ C : ℝ,
        ∀ᶠ t in nhdsWithin T (Set.Iio T), ‖u t‖ ≤ C := by
  simpa only [NormUnboundedAt] using
    (normUnboundedWithinAt_iff_not_eventually_norm_bounded
      (u := u) (s := Set.Iio T) (T := T))

/-- Norm-unboundedness from the right is exactly the failure of every eventual
norm bound on a right neighborhood of the terminal time. -/
theorem normUnboundedAtFromRight_iff_not_eventually_norm_bounded
    {E : Type*} [Norm E] {u : ℝ → E} {T : ℝ} :
    NormUnboundedAtFromRight u T ↔
      ¬ ∃ C : ℝ,
        ∀ᶠ t in nhdsWithin T (Set.Ioi T), ‖u t‖ ≤ C := by
  simpa only [NormUnboundedAtFromRight] using
    (normUnboundedWithinAt_iff_not_eventually_norm_bounded
      (u := u) (s := Set.Ioi T) (T := T))

/-- Any continuation criterion based on eventual norm boundedness within `s`
gives the alternative: the norm is unbounded at the endpoint within `s`, or
the solution is extendable.

The proposition `extendable` is an arbitrary hypothesis. -/
theorem normUnboundedWithinAt_or_extendable
    {E : Type*} [Norm E] {u : ℝ → E} {s : Set ℝ} {T : ℝ}
    {extendable : Prop}
    (hcontinuation :
      (∃ C : ℝ,
        ∀ᶠ t in nhdsWithin T s, ‖u t‖ ≤ C) →
        extendable) :
    NormUnboundedWithinAt u s T ∨ extendable := by
  by_cases hbounded :
      ∃ C : ℝ,
        ∀ᶠ t in nhdsWithin T s, ‖u t‖ ≤ C
  · exact Or.inr (hcontinuation hbounded)
  · exact Or.inl <|
      normUnboundedWithinAt_iff_not_eventually_norm_bounded.mpr hbounded

/-- Any continuation criterion based on an eventual norm bound from below
gives the alternative that the norm is unbounded or the solution extends. -/
theorem normUnboundedAt_or_extendable
    {E : Type*} [Norm E] {u : ℝ → E} {T : ℝ}
    {extendable : Prop}
    (hcontinuation :
      (∃ C : ℝ,
        ∀ᶠ t in nhdsWithin T (Set.Iio T), ‖u t‖ ≤ C) →
        extendable) :
    NormUnboundedAt u T ∨ extendable :=
  normUnboundedWithinAt_or_extendable hcontinuation

/-- Any continuation criterion based on an eventual norm bound from the right
gives the alternative that the norm is unbounded or the solution extends. -/
theorem normUnboundedAtFromRight_or_extendable
    {E : Type*} [Norm E] {u : ℝ → E} {T : ℝ}
    {extendable : Prop}
    (hcontinuation :
      (∃ C : ℝ,
        ∀ᶠ t in nhdsWithin T (Set.Ioi T), ‖u t‖ ≤ C) →
        extendable) :
    NormUnboundedAtFromRight u T ∨ extendable :=
  normUnboundedWithinAt_or_extendable hcontinuation

/-- If a model-specific continuation criterion applies within `s` and the
solution is not extendable, then its controlling norm is unbounded along the
restricted neighborhood filter. -/
theorem normUnboundedWithinAt_of_not_extendable
    {E : Type*} [Norm E] {u : ℝ → E} {s : Set ℝ} {T : ℝ}
    {extendable : Prop}
    (hcontinuation :
      (∃ C : ℝ,
        ∀ᶠ t in nhdsWithin T s, ‖u t‖ ≤ C) →
        extendable)
    (hnotExtendable : ¬ extendable) :
    NormUnboundedWithinAt u s T :=
  (normUnboundedWithinAt_or_extendable hcontinuation).resolve_right
    hnotExtendable

/-- A nonextendable solution satisfying a forward continuation criterion has
an unbounded controlling norm arbitrarily close to its right endpoint. -/
theorem normUnboundedAt_of_not_extendable
    {E : Type*} [Norm E] {u : ℝ → E} {T : ℝ}
    {extendable : Prop}
    (hcontinuation :
      (∃ C : ℝ,
        ∀ᶠ t in nhdsWithin T (Set.Iio T), ‖u t‖ ≤ C) →
        extendable)
    (hnotExtendable : ¬ extendable) :
    NormUnboundedAt u T :=
  normUnboundedWithinAt_of_not_extendable hcontinuation hnotExtendable

/-- A nonextendable solution satisfying a backward continuation criterion has
an unbounded controlling norm arbitrarily close to its left endpoint. -/
theorem normUnboundedAtFromRight_of_not_extendable
    {E : Type*} [Norm E] {u : ℝ → E} {T : ℝ}
    {extendable : Prop}
    (hcontinuation :
      (∃ C : ℝ,
        ∀ᶠ t in nhdsWithin T (Set.Ioi T), ‖u t‖ ≤ C) →
        extendable)
    (hnotExtendable : ¬ extendable) :
    NormUnboundedAtFromRight u T :=
  normUnboundedWithinAt_of_not_extendable hcontinuation hnotExtendable

/-- A finite right endpoint satisfying a continuation criterion is a
norm-unbounded time inside any enclosing half-open lifespan bound.

The lifespan estimate is independent of the continuation criterion. A PDE
application can first prove `T ≤ τ` by an energy, virial, or comparison
argument and then combine it with this theorem. -/
theorem exists_normUnboundedAt_mem_Ioc_of_not_extendable
    {E : Type*} [Norm E] {u : ℝ → E} {t₀ T τ : ℝ}
    {extendable : Prop}
    (htime : t₀ < T)
    (hendpoint : T ≤ τ)
    (hcontinuation :
      (∃ C : ℝ,
        ∀ᶠ t in nhdsWithin T (Set.Iio T), ‖u t‖ ≤ C) →
        extendable)
    (hnotExtendable : ¬ extendable) :
    ∃ T' ∈ Set.Ioc t₀ τ, NormUnboundedAt u T' :=
  ⟨T, ⟨htime, hendpoint⟩,
    normUnboundedAt_of_not_extendable hcontinuation hnotExtendable⟩

/-- A finite left endpoint satisfying a backward continuation criterion is a
right-unbounded time inside any enclosing half-open lifespan bound.

Here `τ ≤ T` comes from a backward lifespan estimate for the model, and
`T < t₀` says that `T` is strictly to the left of the reference time. -/
theorem exists_normUnboundedAtFromRight_mem_Ico_of_not_extendable
    {E : Type*} [Norm E] {u : ℝ → E} {τ T t₀ : ℝ}
    {extendable : Prop}
    (hendpoint : τ ≤ T)
    (htime : T < t₀)
    (hcontinuation :
      (∃ C : ℝ,
        ∀ᶠ t in nhdsWithin T (Set.Ioi T), ‖u t‖ ≤ C) →
        extendable)
    (hnotExtendable : ¬ extendable) :
    ∃ T' ∈ Set.Ico τ t₀, NormUnboundedAtFromRight u T' :=
  ⟨T, ⟨hendpoint, htime⟩,
    normUnboundedAtFromRight_of_not_extendable
      hcontinuation hnotExtendable⟩

/-- For a norm that is nondecreasing before `T`, norm-unboundedness upgrades
to norm blow-up.

Without monotonicity or another persistence hypothesis, this implication is
false: an unbounded trajectory may repeatedly return to bounded norm. -/
theorem NormUnboundedAt.normBlowsUpAt_of_monotoneOn
    {E : Type*} [Norm E] {u : ℝ → E} {T : ℝ}
    (hunbounded : NormUnboundedAt u T)
    (hmono : MonotoneOn (fun t ↦ ‖u t‖) (Set.Iio T)) :
    NormBlowsUpAt u T := by
  rw [NormBlowsUpAt, NormBlowsUpWithinAt, tendsto_atTop]
  intro C
  obtain ⟨t, hCt, htT⟩ :=
    (hunbounded C).and_eventually self_mem_nhdsWithin |>.exists
  filter_upwards
    [nhdsWithin_le_nhds (Ioi_mem_nhds htT),
      self_mem_nhdsWithin] with s hts hsT
  exact hCt.le.trans (hmono htT hsT hts.le)

/-- For a norm that is nonincreasing after a left endpoint `T`,
right-unboundedness upgrades to norm blow-up from the right.

Without antitonicity or another persistence hypothesis, an unbounded
trajectory may repeatedly return to bounded norm. -/
theorem NormUnboundedAtFromRight.normBlowsUpAtFromRight_of_antitoneOn
    {E : Type*} [Norm E] {u : ℝ → E} {T : ℝ}
    (hunbounded : NormUnboundedAtFromRight u T)
    (hanti : AntitoneOn (fun t ↦ ‖u t‖) (Set.Ioi T)) :
    NormBlowsUpAtFromRight u T := by
  rw [NormBlowsUpAtFromRight, NormBlowsUpWithinAt, tendsto_atTop]
  intro C
  obtain ⟨t, hCt, hTt⟩ :=
    (hunbounded C).and_eventually self_mem_nhdsWithin |>.exists
  filter_upwards
    [nhdsWithin_le_nhds (Iio_mem_nhds hTt),
      self_mem_nhdsWithin] with s hst hTs
  exact hCt.le.trans (hanti hTs hTt hst.le)

/-- A nonextendable trajectory satisfying a norm-based continuation
criterion blows up when its norm is nondecreasing before the terminal time. -/
theorem normBlowsUpAt_of_not_extendable_of_monotoneOn
    {E : Type*} [Norm E] {u : ℝ → E} {T : ℝ}
    {extendable : Prop}
    (hcontinuation :
      (∃ C : ℝ,
        ∀ᶠ t in nhdsWithin T (Set.Iio T), ‖u t‖ ≤ C) →
        extendable)
    (hnotExtendable : ¬ extendable)
    (hmono : MonotoneOn (fun t ↦ ‖u t‖) (Set.Iio T)) :
    NormBlowsUpAt u T :=
  (normUnboundedAt_of_not_extendable
    hcontinuation hnotExtendable).normBlowsUpAt_of_monotoneOn hmono

/-- A nonextendable trajectory satisfying a backward norm-based continuation
criterion blows up from the right when its norm is nonincreasing after the
left endpoint. -/
theorem normBlowsUpAtFromRight_of_not_extendable_of_antitoneOn
    {E : Type*} [Norm E] {u : ℝ → E} {T : ℝ}
    {extendable : Prop}
    (hcontinuation :
      (∃ C : ℝ,
        ∀ᶠ t in nhdsWithin T (Set.Ioi T), ‖u t‖ ≤ C) →
        extendable)
    (hnotExtendable : ¬ extendable)
    (hanti : AntitoneOn (fun t ↦ ‖u t‖) (Set.Ioi T)) :
    NormBlowsUpAtFromRight u T :=
  (normUnboundedAtFromRight_of_not_extendable
    hcontinuation hnotExtendable).normBlowsUpAtFromRight_of_antitoneOn hanti

end PDE.Solution.Singularity.FiniteTime
