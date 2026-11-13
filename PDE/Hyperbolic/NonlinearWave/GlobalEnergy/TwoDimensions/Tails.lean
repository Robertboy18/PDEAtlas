/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.TwoDimensions.ShortTime
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Tails.Propagation

/-!
# Uniform spatial tails for planar waves

The planar short-time estimate `exists_pos_uniform_tail_of_compact_cauchy_two`
instantiates the propagation theorems for spatial tails. A planar wave whose
displacement slices have compact support therefore has uniformly small spatial tails,
and is uniformly bounded, on every finite forward time interval.
-/

@[expose] public noncomputable section

open Set PDE PDE.Common

namespace WaveEquation

/-- If every displacement slice at a nonnegative time has compact support, the spatial
tails are uniformly small on a neighborhood of each time `a ≥ 0`. The time-reflected
solution is used only at positive times, where the equation holds. -/
theorem exists_uniform_tail_near_of_compact_slices_two
    {u : ℝ^3 → ℝ} {f : ℝ → ℝ} (hu : ContDiff ℝ 4 u) (hf : Continuous f)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^2,
      waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^2 ↦ u (timeSpaceCons t x)))
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ δ > 0, ∃ R : ℝ, ∀ t ∈ Icc (max 0 (a - δ)) (a + δ), ∀ x : ℝ^2,
      R < ‖x‖ → ‖u (timeSpaceCons t x)‖ < ε := by
  exact exists_uniform_tail_near_of_compact_slices_of_short_time
    exists_pos_uniform_tail_of_compact_cauchy_two hu hf hwave hs ha hε

/-- The radius for a small spatial tail is uniform on every finite forward
band, although each displacement slice has its own compact support. -/
theorem exists_uniform_tail_on_Icc_of_compact_slices_two
    {u : ℝ^3 → ℝ} {f : ℝ → ℝ} (hu : ContDiff ℝ 4 u) (hf : Continuous f)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^2,
      waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^2 ↦ u (timeSpaceCons t x)))
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ t ∈ Icc 0 T, ∀ x : ℝ^2, R < ‖x‖ → ‖u (timeSpaceCons t x)‖ < ε := by
  exact exists_uniform_tail_on_Icc_of_compact_slices_of_short_time
    exists_pos_uniform_tail_of_compact_cauchy_two hu hf hwave hs T hε

/-- Uniform tails and compactness of the remaining cylinder give a spatial
amplitude bound on every finite forward time band. -/
theorem exists_uniform_amplitude_on_Icc_of_compact_slices_two {u : ℝ^3 → ℝ} {f : ℝ → ℝ}
    (hu : ContDiff ℝ 4 u) (hf : Continuous f)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^2,
      waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^2 ↦ u (timeSpaceCons t x))) (T : ℝ) :
    ∃ M ≥ 0, ∀ t ∈ Icc 0 T, ∀ x : ℝ^2, ‖u (timeSpaceCons t x)‖ ≤ M := by
  exact exists_uniform_amplitude_on_Icc_of_uniform_tails hu.continuous.continuousOn
    (fun ε hε ↦ exists_uniform_tail_on_Icc_of_compact_slices_two hu hf hwave hs T hε)

/-- Uniform spatial tails on `[0, T]` for a field that is `C⁴` on the closed forward
half-space and satisfies the equation at positive times. -/
theorem exists_uniform_tail_on_Icc_of_forward_compact_slices_two {u : ℝ^3 → ℝ} {f : ℝ → ℝ}
    (hu : ContDiffOn ℝ 4 u {p | 0 ≤ p 0}) (hf : Continuous f)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^2,
      waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^2 ↦ u (timeSpaceCons t x))) (T : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ R : ℝ, ∀ t ∈ Icc 0 T, ∀ x : ℝ^2, R < ‖x‖ → ‖u (timeSpaceCons t x)‖ < ε := by
  exact exists_uniform_tail_on_Icc_of_forward_compact_slices_of_short_time
    exists_pos_uniform_tail_of_compact_cauchy_two hu hf hwave hs T hε

/-- In dimension two, `C⁴` regularity on the closed forward half-space and compact
displacement slices bound the field uniformly on each finite time band. -/
theorem exists_uniform_amplitude_on_Icc_of_forward_compact_slices_two {u : ℝ^3 → ℝ} {f : ℝ → ℝ}
    (hu : ContDiffOn ℝ 4 u {p | 0 ≤ p 0}) (hf : Continuous f)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^2,
      waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^2 ↦ u (timeSpaceCons t x))) (T : ℝ) :
    ∃ M ≥ 0, ∀ t ∈ Icc 0 T, ∀ x : ℝ^2, ‖u (timeSpaceCons t x)‖ ≤ M := by
  exact exists_uniform_amplitude_on_Icc_of_uniform_tails hu.continuousOn
    (fun ε hε ↦ exists_uniform_tail_on_Icc_of_forward_compact_slices_two hu hf hwave hs T hε)

/-- A potential continuous at zero and vanishing there has uniformly small tails on
every finite forward planar band, with the non-strict threshold `B ≤ ‖x‖`. -/
theorem exists_uniform_potential_tail_on_Icc_of_forward_compact_slices_two {u : ℝ^3 → ℝ}
    {f V : ℝ → ℝ} (hu : ContDiffOn ℝ 4 u {p | 0 ≤ p 0}) (hf : Continuous f)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^2,
      waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^2 ↦ u (timeSpaceCons t x)))
    (hV : ContinuousAt V 0) (hV0 : V 0 = 0) {s t ε : ℝ} (hs0 : 0 ≤ s) (hε : 0 < ε) :
    ∃ B : ℝ, ∀ r ∈ Icc s t, ∀ x : ℝ^2, B ≤ ‖x‖ → |V (u (timeSpaceCons r x))| ≤ ε := by
  exact exists_uniform_potential_tail_on_Icc_of_uniform_tails
    (fun η hη ↦ exists_uniform_tail_on_Icc_of_forward_compact_slices_two
      hu hf hwave hs t hη) hV hV0 hs0 hε

end WaveEquation
