/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.InitialValue
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Comparison

/-!
# Dynamic-programming representation for Hopf–Lax profiles

Three elementary consequences of the Hopf–Lax restart formula:

* one-sided restart bounds propagate order;
* exact restart identities preserve uniform-distance bounds;
* a profile with the prescribed initial trace and exact restart identity is
  the canonical Hopf–Lax profile.

The results apply to arbitrary spacetime profiles satisfying the stated
restart bounds; the comparison uses only these dynamic-programming hypotheses.

The restart formula is the functional identity (22) of Evans, §3.3.2(b), Lemma 1, here assumed
of a profile: `u(·, t)` is the Hopf–Lax formula applied for the time `t - s` to `u(·, s)`. With
`s = 0` it is the formula (21) of Theorem 4, which gives
`eqOn_hopfLaxEvolutionSpacetime_of_initial_trace_of_restart`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(b), Theorem 4, formula (21); Lemma 1,
  equation (22).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HamiltonJacobi1D

noncomputable section

open PDE.Common

/-- Opposite Hopf–Lax restart bounds propagate order from one time slice.

The lower profile is assumed to lie below the Hopf–Lax evolution of its
time-`s` slice, while the upper profile lies above the corresponding
evolution of its own slice. Pointwise order on the two slices then gives
order at every later spacetime point. -/
theorem le_of_hopfLaxEvolution_restart_bounds {H : ℝ → ℝ} {u v : ℝ^2 → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) {K : NNReal} {s : ℝ}
    (huSlice : LipschitzWith K (fun x ↦ u !₂[s, x])) {z : ℝ^2} (hsz : s ≤ z 0)
    (huRestart : u z ≤ HopfLax1D.hopfLaxEvolution H (fun x ↦ u !₂[s, x]) (z 0 - s) (z 1))
    (hvRestart : HopfLax1D.hopfLaxEvolution H (fun x ↦ v !₂[s, x]) (z 0 - s) (z 1) ≤ v z)
    (hslice : ∀ x, u !₂[s, x] ≤ v !₂[s, x]) :
    u z ≤ v z := by
  have htime : 0 ≤ z 0 - s := sub_nonneg.mpr hsz
  exact huRestart.trans <| (HopfLax1D.hopfLaxEvolution_mono_phi_of_lipschitz
      hFin huSlice htime hslice).trans hvRestart

/-- Exact Hopf–Lax restart identities preserve a pointwise uniform-distance
estimate from an earlier time slice. -/
theorem dist_le_of_hopfLaxEvolution_restart {H : ℝ → ℝ} {u v : ℝ^2 → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) {K : NNReal} {s : ℝ}
    (huSlice : LipschitzWith K (fun x ↦ u !₂[s, x])) {C : ℝ} {z : ℝ^2} (hsz : s ≤ z 0)
    (huRestart : u z = HopfLax1D.hopfLaxEvolution H (fun x ↦ u !₂[s, x]) (z 0 - s) (z 1))
    (hvRestart : v z = HopfLax1D.hopfLaxEvolution H (fun x ↦ v !₂[s, x]) (z 0 - s) (z 1))
    (hslice : ∀ x, dist (u !₂[s, x]) (v !₂[s, x]) ≤ C) :
    dist (u z) (v z) ≤ C := by
  rw [huRestart, hvRestart]
  exact HopfLax1D.dist_hopfLaxEvolution_le_of_lipschitz hFin huSlice (sub_nonneg.mpr hsz) hslice

/-- A profile with the prescribed initial trace and the zero-time Hopf–Lax
restart identity is the canonical closed-time Hopf–Lax profile.

Only the restart identity is used here. No viscosity hypothesis is needed. -/
theorem eqOn_hopfLaxEvolutionSpacetime_of_initial_trace_of_restart {H phi : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (htrace : ∀ x, u !₂[0, x] = phi x)
    (hrestart : ∀ z, 0 ≤ z 0 → u z =
      HopfLax1D.hopfLaxEvolution H (fun x ↦ u !₂[0, x]) (z 0) (z 1)) :
    Set.EqOn u (hopfLaxEvolutionSpacetime H phi) {z : ℝ^2 | 0 ≤ z 0} := by
  have hslice : (fun x ↦ u !₂[0, x]) = phi := funext htrace
  intro z hz
  rw [hrestart z hz, hslice]
  rfl

/-- Two profiles with the same initial trace and exact zero-time Hopf–Lax
restart identity agree throughout closed forward spacetime. -/
theorem eqOn_of_initial_trace_eq_of_hopfLaxEvolution_restart {H : ℝ → ℝ} {u v : ℝ^2 → ℝ}
    (htrace : ∀ x, u !₂[0, x] = v !₂[0, x])
    (huRestart : ∀ z, 0 ≤ z 0 → u z = HopfLax1D.hopfLaxEvolution H (fun x ↦ u !₂[0, x]) (z 0) (z 1))
    (hvRestart : ∀ z, 0 ≤ z 0 → v z =
      HopfLax1D.hopfLaxEvolution H (fun x ↦ v !₂[0, x]) (z 0) (z 1)) :
    Set.EqOn u v {z : ℝ^2 | 0 ≤ z 0} := by
  have hslice : (fun x ↦ u !₂[0, x]) = fun x ↦ v !₂[0, x] := funext htrace
  intro z hz
  rw [huRestart z hz, hvRestart z hz, hslice]

end

end HamiltonJacobi1D
