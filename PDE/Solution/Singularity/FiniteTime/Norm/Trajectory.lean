/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Finite-time norm blow-up of trajectories

Finite-time norm blow-up for an ordinary trajectory `u : ℝ → E`. The core
predicates need only a norm on `E`; algebraic and topological assumptions appear only in the
theorems that use them. In applications, `E` may be Euclidean, Banach, Sobolev, `Lᵖ`, or another
normed state space. No pointwise representative of an element of `E` is required.

The set-relative predicates support one-sided and domain-restricted limits.
The main specializations used throughout the finite-time theory are:

* `NormBlowsUpAt u T` says that `‖u t‖` tends to `+∞` as `t` approaches `T` from below.
* `NormUnboundedAt u T` says only that every threshold is exceeded arbitrarily close to `T`.
* The `FromRight` variants describe approach to a left endpoint through times `t > T`.

Everything here is a predicate or a transfer theorem, with no singularity structure, so a
continuation theorem can use them with whatever state space suits the model.

The amplitude-profile theorem applies to quotient-valued normed spaces: it needs only a lower
bound on the norm of the profile trajectory, not a dilation operator.

## Main declarations

* `NormBlowsUpWithinAt`, `NormUnboundedWithinAt`: the set-relative predicates, and their
  one-sided specialisations `NormBlowsUpAt`, `NormUnboundedAt`, `NormBlowsUpAtFromRight`,
  `NormUnboundedAtFromRight`.
* `NormBlowsUpAt.of_eventually_le`, `NormBlowsUpAt.of_smul`: blow-up from a divergent scalar
  lower bound, and for `amplitude t • profile t` when `‖amplitude t‖ → ∞` and the profile stays
  away from zero.
* `NormBlowsUpAt.comp_linearIsometry_iff`: invariance under linear isometric embeddings.
* `NormBlowsUpAt.not_eventually_norm_bounded`, `NormBlowsUpAt.not_continuousAt`,
  `NormBlowsUpAt.not_exists_continuousWithinAt_extension`: what blow-up rules out.
* `NormBlowsUpAt.iff_of_norm_sub_eventually_bounded`: stability under bounded perturbations.

The blow-up theorems of `PDE.Solution.Singularity.FiniteTime` state their conclusions with
these predicates.
-/

@[expose] public section

namespace PDE.Solution.Singularity.FiniteTime

open Filter Topology

/-- A trajectory blows up in norm at `T` within `s` if its norm tends to `+∞` along the
neighborhood filter of `T` restricted to `s`.

As for any `Tendsto` statement, this is vacuous when `nhdsWithin T s = ⊥`. Theorems that produce
nearby times therefore assume `NeBot (nhdsWithin T s)`; the one-sided specializations have that
instance automatically. -/
def NormBlowsUpWithinAt {E : Type*} [Norm E]
    (u : ℝ → E) (s : Set ℝ) (T : ℝ) : Prop :=
  Tendsto (fun t ↦ ‖u t‖) (nhdsWithin T s) atTop

/-- A trajectory is norm-unbounded at `T` within `s` if every norm threshold is exceeded
frequently along the neighborhood filter of `T` restricted to `s`. -/
def NormUnboundedWithinAt {E : Type*} [Norm E]
    (u : ℝ → E) (s : Set ℝ) (T : ℝ) : Prop :=
  ∀ C : ℝ, ∃ᶠ t in nhdsWithin T s, C < ‖u t‖

/-- A trajectory blows up in norm at `T` from below if its norm tends to `+∞` along `t < T`. -/
def NormBlowsUpAt {E : Type*} [Norm E]
    (u : ℝ → E) (T : ℝ) : Prop :=
  NormBlowsUpWithinAt u (Set.Iio T) T

/-- A trajectory is norm-unbounded at `T` from below if every norm threshold is exceeded
arbitrarily close to `T`.

Unlike `NormBlowsUpAt`, this predicate permits the norm to return below a threshold infinitely
often as `t` approaches `T`. -/
def NormUnboundedAt {E : Type*} [Norm E]
    (u : ℝ → E) (T : ℝ) : Prop :=
  NormUnboundedWithinAt u (Set.Iio T) T

/-- A trajectory blows up in norm at `T` from the right if its norm tends to `+∞` as
`t ↓ T` through times `t > T`. This is the natural convention at a left lifespan endpoint. -/
def NormBlowsUpAtFromRight {E : Type*} [Norm E]
    (u : ℝ → E) (T : ℝ) : Prop :=
  NormBlowsUpWithinAt u (Set.Ioi T) T

/-- A trajectory is norm-unbounded at `T` from the right if every norm threshold is exceeded
arbitrarily close to `T` through times `t > T`. -/
def NormUnboundedAtFromRight {E : Type*} [Norm E]
    (u : ℝ → E) (T : ℝ) : Prop :=
  NormUnboundedWithinAt u (Set.Ioi T) T

/-- A divergent scalar lower bound proves norm blow-up. -/
theorem NormBlowsUpAt.of_eventually_le
    {E : Type*} [Norm E] {u : ℝ → E} {T : ℝ}
    {observable : ℝ → ℝ}
    (hobservable :
      Tendsto observable (nhdsWithin T (Set.Iio T)) atTop)
    (hcontrol :
      observable ≤ᶠ[nhdsWithin T (Set.Iio T)] fun t ↦ ‖u t‖) :
    NormBlowsUpAt u T :=
  tendsto_atTop_mono' _ hcontrol hobservable

/-- A real-valued trajectory that itself tends to `+∞` also blows up in norm.

Scalar comparison theorems can then be stated with order limits and still conclude
`NormBlowsUpAt`. -/
theorem NormBlowsUpAt.of_tendsto_atTop
    {u : ℝ → ℝ} {T : ℝ}
    (h : Tendsto u (nhdsWithin T (Set.Iio T)) atTop) :
    NormBlowsUpAt u T :=
  NormBlowsUpAt.of_eventually_le h <|
    Eventually.of_forall fun t ↦ Real.le_norm_self (u t)

/-- A diverging scalar amplitude forces norm blow-up when the profile trajectory stays uniformly
away from zero in norm.

The scalar field and state space are arbitrary normed modules. In particular, `profile t` may
belong to a Sobolev or `Lᵖ` quotient space; any dilation used to define that trajectory has to
be constructed separately. -/
theorem NormBlowsUpAt.of_smul
    {𝕜 E : Type*} [NormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    {amplitude : ℝ → 𝕜} {profile : ℝ → E} {T c : ℝ}
    (hc : 0 < c)
    (hamplitude :
      Tendsto (fun t ↦ ‖amplitude t‖)
        (nhdsWithin T (Set.Iio T)) atTop)
    (hprofile :
      ∀ᶠ t in nhdsWithin T (Set.Iio T), c ≤ ‖profile t‖) :
    NormBlowsUpAt (fun t ↦ amplitude t • profile t) T := by
  apply NormBlowsUpAt.of_eventually_le
    (Filter.Tendsto.atTop_mul_const hc hamplitude)
  filter_upwards [hprofile] with t ht
  simpa only [norm_smul] using
    mul_le_mul_of_nonneg_left ht (norm_nonneg (amplitude t))

/-- A linear isometric embedding preserves and reflects norm blow-up of an abstract trajectory.

The source and target may themselves be Sobolev or `Lᵖ` spaces. The statement uses only their
norms and the isometry; it does not select pointwise representatives. -/
theorem NormBlowsUpAt.comp_linearIsometry_iff
    {𝕜 E F : Type*} [Semiring 𝕜]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [Module 𝕜 E] [Module 𝕜 F]
    {u : ℝ → E} {T : ℝ} (L : E →ₗᵢ[𝕜] F) :
    NormBlowsUpAt (L ∘ u) T ↔ NormBlowsUpAt u T := by
  simp only [NormBlowsUpAt, NormBlowsUpWithinAt, Function.comp_apply, L.norm_map]

/-- Norm blow-up implies frequent norm-unboundedness near the singular time.

The converse is false in general: an unbounded trajectory may oscillate back to bounded values
arbitrarily close to `T`. -/
theorem NormBlowsUpWithinAt.norm_unbounded_within_at
    {E : Type*} [Norm E] {u : ℝ → E} {s : Set ℝ} {T : ℝ}
    [NeBot (nhdsWithin T s)]
    (h : NormBlowsUpWithinAt u s T) :
    NormUnboundedWithinAt u s T := by
  intro C
  exact (h.eventually_gt_atTop C).frequently

/-- Norm blow-up from below implies frequent norm-unboundedness from below. -/
theorem NormBlowsUpAt.norm_unbounded_at
    {E : Type*} [Norm E] {u : ℝ → E} {T : ℝ}
    (h : NormBlowsUpAt u T) :
    NormUnboundedAt u T :=
  h.norm_unbounded_within_at

/-- Norm blow-up from the right implies frequent norm-unboundedness from the right. -/
theorem NormBlowsUpAtFromRight.norm_unbounded_at_from_right
    {E : Type*} [Norm E] {u : ℝ → E} {T : ℝ}
    (h : NormBlowsUpAtFromRight u T) :
    NormUnboundedAtFromRight u T :=
  h.norm_unbounded_within_at

/-- A norm-blowing-up trajectory cannot have an eventual uniform norm bound within the
approach set. -/
theorem NormBlowsUpWithinAt.not_eventually_norm_bounded
    {E : Type*} [Norm E] {u : ℝ → E} {s : Set ℝ} {T : ℝ}
    [NeBot (nhdsWithin T s)]
    (h : NormBlowsUpWithinAt u s T) :
    ¬ ∃ C : ℝ, ∀ᶠ t in nhdsWithin T s, ‖u t‖ ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨t, ht, hCt⟩ := (h.norm_unbounded_within_at C).and_eventually hC |>.exists
  exact (not_lt_of_ge hCt) ht

/-- A norm-blowing-up trajectory cannot have an eventual uniform norm bound before the
singular time.

This is the contradiction form used with continuation criteria: a fixed norm ball on a left
neighborhood of `T` rules out `NormBlowsUpAt u T`. -/
theorem NormBlowsUpAt.not_eventually_norm_bounded
    {E : Type*} [Norm E] {u : ℝ → E} {T : ℝ}
    (h : NormBlowsUpAt u T) :
    ¬ ∃ C : ℝ, ∀ᶠ t in nhdsWithin T (Set.Iio T), ‖u t‖ ≤ C :=
  NormBlowsUpWithinAt.not_eventually_norm_bounded h

/-- Norm blow-up from the right rules out an eventual norm bound to the right of the
singular time. -/
theorem NormBlowsUpAtFromRight.not_eventually_norm_bounded
    {E : Type*} [Norm E] {u : ℝ → E} {T : ℝ}
    (h : NormBlowsUpAtFromRight u T) :
    ¬ ∃ C : ℝ, ∀ᶠ t in nhdsWithin T (Set.Ioi T), ‖u t‖ ≤ C :=
  NormBlowsUpWithinAt.not_eventually_norm_bounded h

/-- A norm-blowing-up trajectory cannot converge from below to a finite state. -/
theorem NormBlowsUpAt.not_tendsto_nhds
    {E : Type*} [SeminormedAddGroup E] {u : ℝ → E} {T : ℝ}
    (h : NormBlowsUpAt u T) (x : E) :
    ¬ Tendsto u (nhdsWithin T (Set.Iio T)) (nhds x) := by
  intro hu
  exact (not_tendsto_nhds_of_tendsto_atTop h ‖x‖) hu.norm

/-- Norm blow-up rules out a trajectory continuous from the left through `T` that agrees with
the original trajectory at every earlier time.

Such an extension would give the original trajectory a finite left limit at `T`, contradicting
norm divergence. -/
theorem NormBlowsUpAt.not_exists_continuousWithinAt_extension
    {E : Type*} [SeminormedAddGroup E] {u : ℝ → E} {T : ℝ}
    (h : NormBlowsUpAt u T) :
    ¬ ∃ v : ℝ → E,
      ContinuousWithinAt v (Set.Iic T) T ∧ Set.EqOn v u (Set.Iio T) := by
  rintro ⟨v, hv, hvu⟩
  apply h.not_tendsto_nhds (v T)
  exact (hv.mono Set.Iio_subset_Iic_self).congr' hvu.eventuallyEq_nhdsWithin

/-- Norm blow-up at `T` obstructs continuity of the trajectory at `T`. -/
theorem NormBlowsUpAt.not_continuousAt
    {E : Type*} [SeminormedAddGroup E] {u : ℝ → E} {T : ℝ}
    (h : NormBlowsUpAt u T) :
    ¬ ContinuousAt u T := by
  intro hu
  exact h.not_tendsto_nhds (u T) (hu.tendsto.mono_left nhdsWithin_le_nhds)

/-- Norm blow-up is invariant under an eventually norm-bounded additive error.

Thus a singular leading trajectory and its uniformly controlled perturbation blow up together.
The bounded-difference hypothesis is symmetric because `‖u - v‖ = ‖v - u‖`. -/
theorem NormBlowsUpAt.iff_of_norm_sub_eventually_bounded
    {E : Type*} [SeminormedAddGroup E] {u v : ℝ → E} {T : ℝ}
    (herror :
      ∃ C : ℝ, ∀ᶠ t in nhdsWithin T (Set.Iio T), ‖u t - v t‖ ≤ C) :
    NormBlowsUpAt u T ↔ NormBlowsUpAt v T := by
  rcases herror with ⟨C, herror⟩
  have transfer :
      ∀ {a b : ℝ → E},
        NormBlowsUpAt a T →
        (∀ᶠ t in nhdsWithin T (Set.Iio T), ‖a t - b t‖ ≤ C) →
        NormBlowsUpAt b T := by
    intro a b ha hab
    rw [NormBlowsUpAt, NormBlowsUpWithinAt, tendsto_atTop] at ha ⊢
    intro threshold
    filter_upwards [ha (threshold + C), hab] with t ht herror_t
    have htriangle : ‖a t‖ ≤ ‖a t - b t‖ + ‖b t‖ := by
      calc
        ‖a t‖ = ‖(a t - b t) + b t‖ := by rw [sub_add_cancel]
        _ ≤ ‖a t - b t‖ + ‖b t‖ := norm_add_le _ _
    have hsum : threshold + C ≤ C + ‖b t‖ :=
      ht.trans (htriangle.trans (add_le_add herror_t le_rfl))
    exact (add_le_add_iff_left C).mp (by simpa [add_comm] using hsum)
  constructor
  · intro hu
    exact transfer hu herror
  · intro hv
    apply transfer hv
    filter_upwards [herror] with t ht
    calc
      ‖v t - u t‖ = ‖-(v t - u t)‖ := (norm_neg _).symm
      _ = ‖u t - v t‖ := by rw [neg_sub]
      _ ≤ C := ht

end PDE.Solution.Singularity.FiniteTime
