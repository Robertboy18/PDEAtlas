/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.RealLine.Continuation.Uniform

/-!
# The finite maximal-endpoint alternative

The solution class consists of C² waves before a positive finite endpoint,
with the prescribed initial data and bounded range on every proper closed
forward strip. Maximality means that no solution in the same class on a longer
whole-line strip agrees with it before the endpoint.

For a C¹ reaction, bounded C² initial displacement with bounded first derivative,
and bounded C¹ initial velocity, a finite maximal endpoint forces unbounded
solution range arbitrarily near that endpoint. The conclusion concerns the range over space and
time. No existence of a maximal solution is built into the definition.
-/

@[expose] public noncomputable section

open PDE.Common Set
open scoped BoundedContinuousFunction

namespace WaveEquation

/-- A classical wave on a positive forward interval, bounded on every
proper closed strip. Regularity is required only on the open half-space before
the endpoint. No bound on a solution derivative or terminal trace is included. -/
structure IsBoundedClassicalWaveBefore
    (f : ℝ → ℝ) (g h : ℝ →ᵇ ℝ) (T : ℝ) (u : ℝ^2 → ℝ) : Prop where
  time_pos : 0 < T
  regular : ContDiffOn ℝ 2 u {p | p 0 < T}
  equation : ∀ p : ℝ^2, p 0 ∈ Ico 0 T → waveOperator (n := 1) u p = -f (u p)
  position : ∀ x : ℝ^1, u (timeSpaceCons 0 x) = g (x 0)
  velocity : ∀ x : ℝ^1, (∂[0] u) (timeSpaceCons 0 x) = h (x 0)
  bounded : ∀ S ∈ Ico 0 T, ∃ R : ℝ, ∀ p : ℝ^2, p 0 ∈ Icc 0 S → |u p| ≤ R

/-- A finite endpoint is maximal if the wave cannot agree with a solution on
any longer whole-line strip in the same class. This is nonextendibility of the
PDE solution, not failure of a particular construction. -/
structure IsMaximalBoundedClassicalWaveBefore
    (f : ℝ → ℝ) (g h : ℝ →ᵇ ℝ) (T : ℝ) (u : ℝ^2 → ℝ) : Prop
    extends IsBoundedClassicalWaveBefore f g h T u where
  nonextendible : ∀ {S : ℝ} {v : ℝ^2 → ℝ}, T < S →
    IsBoundedClassicalWaveBefore f g h S v →
    (∀ p : ℝ^2, p 0 ∈ Ico 0 T → v p = u p) → False

/-- Two waves in this class with common initial data agree before their common
endpoint. -/
theorem IsBoundedClassicalWaveBefore.eq {f : ℝ → ℝ} (hf : LocallyLipschitz f) {g h : ℝ →ᵇ ℝ} {T : ℝ}
    {u v : ℝ^2 → ℝ} (hu : IsBoundedClassicalWaveBefore f g h T u)
    (hv : IsBoundedClassicalWaveBefore f g h T v) :
    ∀ p : ℝ^2, p 0 ∈ Ico 0 T → u p = v p :=
  eq_on_forward_open_strip_of_eq_cauchyData_locallyLipschitz hf hu.regular hv.regular
    hu.equation hv.equation (fun x ↦ (hu.position x).trans (hv.position x).symm)
    (fun x ↦ (hu.velocity x).trans (hv.velocity x).symm)

/-- Restriction to a shorter positive interval preserves the classical
bounded-strip solution class. -/
theorem IsBoundedClassicalWaveBefore.mono {f : ℝ → ℝ} {g h : ℝ →ᵇ ℝ} {S T : ℝ} {u : ℝ^2 → ℝ}
    (hu : IsBoundedClassicalWaveBefore f g h T u) (hS : 0 < S) (hST : S ≤ T) :
    IsBoundedClassicalWaveBefore f g h S u :=
  ⟨hS, hu.regular.mono (fun _ hp ↦ lt_of_lt_of_le hp hST),
    fun p hp ↦ hu.equation p ⟨hp.1, hp.2.trans_le hST⟩, hu.position, hu.velocity,
    fun A hA ↦ hu.bounded A ⟨hA.1, hA.2.trans_le hST⟩⟩

/-- PDE uniqueness identifies waves on the overlap of their forward
intervals, even when their endpoints differ. -/
theorem IsBoundedClassicalWaveBefore.eq_on_overlap {f : ℝ → ℝ} (hf : LocallyLipschitz f)
    {g h : ℝ →ᵇ ℝ} {S T : ℝ} {u v : ℝ^2 → ℝ} (hu : IsBoundedClassicalWaveBefore f g h S u)
    (hv : IsBoundedClassicalWaveBefore f g h T v) :
    ∀ p : ℝ^2, p 0 ∈ Ico 0 (min S T) → u p = v p :=
  (hu.mono (lt_min hu.time_pos hv.time_pos) (min_le_left S T)).eq hf
    (hv.mono (lt_min hu.time_pos hv.time_pos) (min_le_right S T))

/-- Finite maximal endpoints for the same Cauchy data coincide. -/
theorem IsMaximalBoundedClassicalWaveBefore.endpoint_eq {f : ℝ → ℝ} (hf : LocallyLipschitz f)
    {g h : ℝ →ᵇ ℝ} {S T : ℝ} {u v : ℝ^2 → ℝ} (hu : IsMaximalBoundedClassicalWaveBefore f g h S u)
    (hv : IsMaximalBoundedClassicalWaveBefore f g h T v) :
    S = T := by
  rcases lt_trichotomy S T with hlt | heq | hgt
  · apply (hu.nonextendible hlt hv.toIsBoundedClassicalWaveBefore ?_).elim
    intro p hp
    exact hv.toIsBoundedClassicalWaveBefore.eq_on_overlap hf
      hu.toIsBoundedClassicalWaveBefore p ⟨hp.1, lt_min (hp.2.trans hlt) hp.2⟩
  · exact heq
  · apply (hv.nonextendible hgt hu.toIsBoundedClassicalWaveBefore ?_).elim
    intro p hp
    exact hu.toIsBoundedClassicalWaveBefore.eq_on_overlap hf
      hv.toIsBoundedClassicalWaveBefore p ⟨hp.1, lt_min (hp.2.trans hgt) hp.2⟩

/-- A bound up to the finite endpoint yields an extension in the same
bounded-strip class. Its additional time is uniform over the whole line. -/
theorem IsBoundedClassicalWaveBefore.exists_extension_of_bounded_range {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) {g h : ℝ →ᵇ ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) {D : ℝ}
    (hD : ∀ x : ℝ, ‖deriv g x‖ ≤ D) {T R : ℝ} {u : ℝ^2 → ℝ}
    (hu : IsBoundedClassicalWaveBefore f g h T u) (hbound : ∀ p : ℝ^2, p 0 ∈ Ico 0 T → |u p| ≤ R) :
    ∃ S : ℝ, T < S ∧ ∃ v : ℝ^2 → ℝ, IsBoundedClassicalWaveBefore f g h S v ∧
      ∀ p : ℝ^2, p 0 ∈ Ico 0 T → v p = u p := by
  obtain ⟨δ, hδ, v, hv, heq, hpos, hvel, hwave, B, hB⟩ :=
    exists_classical_continuation_of_bounded_range hf hg hh hD hu.time_pos hu.regular
      hu.equation hu.position hu.velocity hbound
  refine ⟨T + δ, lt_add_of_pos_right T hδ, v, ?_, heq⟩
  exact ⟨add_pos hu.time_pos hδ, hv.contDiffOn, fun p hp ↦ hwave p ⟨hp.1, hp.2.le⟩,
    hpos, hvel, fun S hS ↦ ⟨B, fun p hp ↦ hB p ⟨hp.1, hp.2.trans hS.2.le⟩⟩⟩

/-- Before a finite endpoint, either a wave extends to a longer whole-line
strip or its space-time range on the original strip is unbounded. -/
theorem IsBoundedClassicalWaveBefore.continuation_or_unbounded {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {g h : ℝ →ᵇ ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) {D : ℝ}
    (hD : ∀ x : ℝ, ‖deriv g x‖ ≤ D) {T : ℝ} {u : ℝ^2 → ℝ}
    (hu : IsBoundedClassicalWaveBefore f g h T u) :
    (∃ S : ℝ, T < S ∧ ∃ v : ℝ^2 → ℝ, IsBoundedClassicalWaveBefore f g h S v ∧ ∀ p : ℝ^2, p 0 ∈
      Ico 0 T → v p = u p) ∨ ∀ R : ℝ, ∃ p : ℝ^2, p 0 ∈ Ico 0 T ∧ R < |u p| := by
  by_cases hb : ∃ R : ℝ, ∀ p : ℝ^2, p 0 ∈ Ico 0 T → |u p| ≤ R
  · obtain ⟨R, hR⟩ := hb
    exact Or.inl (hu.exists_extension_of_bounded_range hf hg hh hD hR)
  · right
    push Not at hb
    exact hb

/-- A finite nonextendible wave has unbounded space-time range before its
endpoint. Only C¹ regularity of the reaction is used for continuation. -/
theorem IsMaximalBoundedClassicalWaveBefore.unbounded_range {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {g h : ℝ →ᵇ ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) {D : ℝ}
    (hD : ∀ x : ℝ, ‖deriv g x‖ ≤ D) {T : ℝ} {u : ℝ^2 → ℝ}
    (hu : IsMaximalBoundedClassicalWaveBefore f g h T u) :
    ∀ R : ℝ, ∃ p : ℝ^2, p 0 ∈ Ico 0 T ∧ R < |u p| := by
  rcases hu.toIsBoundedClassicalWaveBefore.continuation_or_unbounded hf hg hh hD with
    ⟨S, hS, v, hv, heq⟩ | hb
  · exact (hu.nonextendible hS hv heq).elim
  · exact hb

/-- Unboundedness occurs arbitrarily near a finite maximal endpoint. The bound
on every proper closed strip excludes unbounded values confined to earlier times. -/
theorem IsMaximalBoundedClassicalWaveBefore.unbounded_range_near_endpoint {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) {g h : ℝ →ᵇ ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) {D : ℝ}
    (hD : ∀ x : ℝ, ‖deriv g x‖ ≤ D) {T : ℝ} {u : ℝ^2 → ℝ}
    (hu : IsMaximalBoundedClassicalWaveBefore f g h T u) :
    ∀ S ∈ Ico 0 T, ∀ R : ℝ, ∃ p : ℝ^2, p 0 ∈ Ioo S T ∧ R < |u p| := by
  intro S hS R
  obtain ⟨B, hB⟩ := hu.bounded S hS
  obtain ⟨p, hp, hlarge⟩ := hu.unbounded_range hf hg hh hD (max R B)
  have hSp : S < p 0 := by
    by_contra! hle
    exact (not_lt_of_ge ((hB p ⟨hp.1, hle⟩).trans (le_max_right R B))) hlarge
  exact ⟨p, ⟨hSp, hp.2⟩, (le_max_left R B).trans_lt hlarge⟩

end WaveEquation
