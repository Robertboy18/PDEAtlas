/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.ClassicalExtension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import CAS.ExactTactic

/-!
# Smooth extension across the initial edge of a time band

Finite-order regularity on a closed lower, open upper coordinate band yields a
smooth representative across the lower edge. A temporal cutoff and the checked
closed-halfspace extension give the representative; no regularity is needed at
the upper edge. The original field is preserved throughout the forward half-space.
-/

@[expose] public noncomputable section

open Filter Set PDE PDE.Common PDE.Analysis
open scoped Topology

namespace PDE.Analysis

/-- A scalar field smooth up to the lower edge of a half-open band extends smoothly
across that edge, without any regularity at the upper edge. -/
theorem exists_contDiffOn_extension_halfOpenBand {n k : ℕ} (i : Fin n)
    {u : ℝ^n → ℝ} {T : ℝ} (hT : 0 < T)
    (hu : ContDiffOn ℝ k u {p | 0 ≤ p i ∧ p i < T}) :
    ∃ v : ℝ^n → ℝ, ContDiffOn ℝ k v {p | p i < T} ∧ EqOn v u {p | 0 ≤ p i} := by
  let θ (p : ℝ^n) := Real.smoothTransition ((T / 2 - p i) / (T / 4))
  have hθ : ContDiff ℝ k θ := Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).contDiff).div_const (T / 4))
  have hone {p : ℝ^n} (hp : p i ≤ T / 4) : θ p = 1 :=
    Real.smoothTransition.one_of_one_le ((one_le_div (by positivity : 0 < T / 4)).mpr
      (by linarith))
  have hzero {p : ℝ^n} (hp : T / 2 ≤ p i) : θ p = 0 :=
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
  have hcut : ContDiffOn ℝ k (fun p ↦ θ p * u p) {p | 0 ≤ p i} := by
    intro p hp
    by_cases hpt : p i < T
    · have hup : ContDiffWithinAt ℝ k u {p | 0 ≤ p i} p :=
        (contDiffWithinAt_inter ((isOpen_lt (EuclideanSpace.proj i).continuous
          continuous_const).mem_nhds hpt)).mp (hu p ⟨hp, hpt⟩)
      exact hθ.contDiffAt.contDiffWithinAt.mul hup
    · apply ContDiffAt.contDiffWithinAt
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      have hp' : T / 2 < p i := by linarith
      filter_upwards [(isOpen_lt continuous_const (EuclideanSpace.proj i).continuous).mem_nhds hp']
        with q hq
      simp only [hzero hq.le, zero_mul]
  obtain ⟨g, hg, heq⟩ := exists_contDiff_extension_halfSpace i k hcut
  let v (p : ℝ^n) := g p + (1 - θ p) * u p
  have hv {p : ℝ^n} (hp : 0 ≤ p i) : v p = u p := by
    dsimp only [v]
    rw [heq hp]
    change θ p * u p + (1 - θ p) * u p = u p
    generalize θ p = a
    generalize u p = b
    cas
  refine ⟨v, ?_, fun p hp ↦ hv hp⟩
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  by_cases hpos : 0 < p i
  · have hmem : {q : ℝ^n | 0 ≤ q i ∧ q i < T} ∈ 𝓝 p :=
      Filter.mem_of_superset (((isOpen_lt continuous_const (EuclideanSpace.proj i).continuous).inter
        (isOpen_lt (EuclideanSpace.proj i).continuous continuous_const)).mem_nhds ⟨hpos, hp⟩)
          (fun _ hq ↦ ⟨hq.1.le, hq.2⟩)
    have hup := hu.contDiffAt hmem
    apply hup.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const (EuclideanSpace.proj i).continuous).mem_nhds hpos]
      with q hq
    exact hv hq.le
  · apply hg.contDiffAt.congr_of_eventuallyEq
    have hp' : p i < T / 4 := by linarith
    filter_upwards [(isOpen_lt (EuclideanSpace.proj i).continuous continuous_const).mem_nhds hp']
      with q hq
    simp only [v, hone hq.le, sub_self, zero_mul, add_zero]

end PDE.Analysis
