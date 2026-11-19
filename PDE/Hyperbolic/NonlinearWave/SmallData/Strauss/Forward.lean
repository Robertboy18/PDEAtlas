/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.Nonexistence
import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.Solution
import PDE.Hyperbolic.NonlinearWave.FinitePropagation.ForwardUniqueness
import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.ClassicalExtension

/-!
# The Strauss obstruction with forward-time regularity

A solution posed for nonnegative time need not have derivatives at negative times.
Finite-order reflection supplies a smooth representative without changing the forward
PDE or either initial trace. Finite propagation and the signed-data mass estimate then
exclude a global solution throughout the strict three-dimensional Strauss range.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Analysis PDE.Common Set
open scoped Topology

namespace WaveEquation.SmallData

/-- The three-dimensional focusing wave has no global forward classical solution
in the strict Strauss range when both compact Cauchy data have positive integrals.
The displacement integral may even be zero; neither profile needs a pointwise sign. -/
theorem not_global_forward_solution_three_of_lt_strauss {g h : ℝ^3 → ℝ} {R p : ℝ}
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (hgs : ∀ x, R < ‖x‖ → g x = 0)
    (hhs : ∀ x, R < ‖x‖ → h x = 0) (hR : 0 < R) (hp : 1 < p) (hcrit : p < 1 + Real.sqrt 2)
    (hG : 0 ≤ ∫ x, g x) (hH : 0 < ∫ x, h x) {u : ℝ^4 → ℝ} (hu : ContDiffOn ℝ 2 u {z | 0 ≤ z 0})
    (hwave : ∀ t, 0 < t → ∀ x, waveOperator u (timeSpaceCons t x) = |u (timeSpaceCons t x)| ^ p)
    (hpos : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hvel : ∀ x, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = h x) :
    False := by
  have hs : HasForwardSupport u R :=
    hasForwardSupport_of_cauchyData (Classical.locallyLipschitz_neg_abs_rpow hp)
      (by simp [Real.zero_rpow (by linarith : p ≠ 0)])
      (hu.mono (fun z hz ↦ (show 0 < z 0 from hz).le)) (hu.of_le (by norm_num))
      (fun t ht x ↦ by simp [hwave t ht x]) hpos hvel hgs hhs
  obtain ⟨U, hU, heq⟩ := exists_contDiff_extension_halfSpace (0 : Fin 4) 2 hu
  have hslice (t : ℝ) (ht : 0 ≤ t) (x : ℝ^3) : U (timeSpaceCons t x) = u (timeSpaceCons t x) :=
    heq (by simpa using ht)
  have hlocal (t : ℝ) (ht : 0 < t) (x : ℝ^3) : U =ᶠ[𝓝 (timeSpaceCons t x)] u :=
    eventuallyEq_of_eqOn_forward heq (by simpa using ht)
  have hUs : HasForwardSupport U R := fun t ht x hx ↦ (hslice t ht x).trans (hs t ht x hx)
  have hUw (t : ℝ) (ht : 0 < t) (x : ℝ^3) :
      waveOperator U (timeSpaceCons t x) = |U (timeSpaceCons t x)| ^ p := by
    rw [waveOperator_congr_nhds (hlocal t ht x), hslice t ht.le x]
    exact hwave t ht x
  have hUv (x : ℝ^3) : (∂[0] U) (timeSpaceCons 0 x) = h x := by
    have hd := PDE.hasDerivAt_timeSpaceCons U 0 x (hU.differentiable (by norm_num) _)
    rw [← hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 0 (by simp))]
    rw [derivWithin_congr (s := Ici 0) (fun t ht ↦ hslice t ht x) (hslice 0 le_rfl x)]
    exact hvel x
  exact not_global_cauchy_solution_three_of_lt_strauss hU hUs hg hh hR hp hcrit
    hUw (fun x ↦ (hslice 0 le_rfl x).trans (hpos x)) hUv hG hH

end WaveEquation.SmallData
