/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.OneDimension.LocalBounds
import PDE.Hyperbolic.Classical.ForwardLocalization
import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.ClassicalExtension

/-!
# Bounds for the closed-forward wave differential

A C3 extension from the closed forward halfspace transfers the local
characteristic bounds to the within differential, including time zero.
The equation is used only at positive times and support only slice by slice.
No smoothness or PDE at negative times is added to the hypotheses.
-/

@[expose] public noncomputable section

open PDE PDE.Common Set Filter
open scoped Topology

namespace WaveEquation

/-- Forward differentials are uniformly bounded in space near every time.
Only separate compact displacement slices and the forward equation are required. -/
theorem exists_uniform_forwardDifferential_bound_near_of_compact_slices {u : ℝ^2 → ℝ} {f : ℝ → ℝ}
    (hu : ContDiffOn ℝ 3 u {p | 0 ≤ p 0}) (hf : Continuous f)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^1,
      waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^1 ↦ u (timeSpaceCons t x))) {a : ℝ}
    (ha : 0 ≤ a) :
    ∃ δ > 0, ∃ L ≥ 0, ∀ t ∈ Icc (max 0 (a - δ)) (a + δ), ∀ x : ℝ^1, ∀ i : Fin 2,
      ‖PDE.Analysis.forwardDifferential u t x (EuclideanSpace.single i 1)‖ ≤ L := by
  obtain ⟨U, hU, heq⟩ := PDE.Analysis.exists_contDiff_extension_halfSpace 0 3 hu
  have hw (t : ℝ) (ht : 0 < t) (x : ℝ^1) :
      waveOperator U (timeSpaceCons t x) + f (U (timeSpaceCons t x)) = 0 := by
    have hgerm := eventuallyEq_of_eqOn_forward heq
      (show 0 < (timeSpaceCons t x) 0 by simpa using ht)
    rw [waveOperator_congr_nhds hgerm, hgerm.eq_of_nhds]
    exact hwave t ht x
  have hc (t : ℝ) (ht : 0 ≤ t) :
      HasCompactSupport (fun x : ℝ^1 ↦ U (timeSpaceCons t x)) := by
    have hslic : (fun x : ℝ^1 ↦ U (timeSpaceCons t x)) =
        (fun x : ℝ^1 ↦ u (timeSpaceCons t x)) := by
      funext x
      exact heq (show 0 ≤ (timeSpaceCons t x) 0 by simpa using ht)
    rw [hslic]
    exact hs t ht
  obtain ⟨δ, hδ, L, hL, hb⟩ := exists_uniform_partialDeriv_bound_near_of_compact_slices
    hU hf hw hc ha
  refine ⟨δ, hδ, L, hL, fun t ht x i ↦ ?_⟩
  rw [forwardDifferential_eq_fderiv_of_extension (hU.of_le (by norm_num)) heq
    ((le_max_left _ _).trans ht.1) x]
  exact hb (timeSpaceCons t x) (by simpa using ht) i

end WaveEquation
