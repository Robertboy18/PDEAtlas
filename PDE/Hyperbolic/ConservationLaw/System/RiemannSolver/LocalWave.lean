/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.RiemannSolver.ElementaryWave
public import PDE.Hyperbolic.ConservationLaw.System.WaveCurve.Rarefaction
public import PDE.Hyperbolic.ConservationLaw.System.Rarefaction.Fan
import PDE.Hyperbolic.ConservationLaw.System.RiemannSolver.EntropyLocalWave

/-!
# Realization of local elementary wave transformations

A regular elementary transformation with characteristic tangent determines
a Lax shock on its negative genuinely nonlinear branch. On the
positive branch, inversion of the characteristic speed produces a fan whose
values agree with the entire local integral curve. A linearly degenerate
branch gives the planar contact determined by that same curve.

The neighborhood and norm bound are uniform in both strength and left state.

`eventually_exists_bounded_elementary_wave` states this realization for the weak equation
alone. The construction is `eventually_exists_bounded_elementary_wave_with_entropy` in
`RiemannSolver.EntropyLocalWave`, which also states when the waves satisfy the convex entropy
inequalities; the theorem here drops that conjunct.

The three cases are the waves that make up `T_k(z₀)` in Evans, §11.2.4: the `k`-shock wave
(36)-(37) of §11.2.3 on `S_k^-(z₀)`, the centered rarefaction wave of §11.2.2, Theorem 1, on
`R_k^+(z₀)`, and the contact discontinuity (33)-(34) of §11.2.3 when the pair is linearly
degenerate, where `R_k(z₀) = S_k(z₀)` by Theorem 3 there. The window `(lo, hi)` around
`λ_k(q₀)` outside which the wave is constant is the sector
`λ_k(z₀) - ε < x/t < λ_k(z₀) + ε` of step 4 of the proof of §11.2.4, Theorem 4.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.2, Theorem 1; §11.2.3, equations (33)-(37), Theorem 3
  and the definition of `S_k^-(z₀)`; §11.2.4, the definition of `T_k(z₀)` and step 4 of the
  proof of Theorem 4.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Metric Set
open scoped Topology

/-- Realize a local elementary transformation by bounded self-similar weak
waves, preserving the precise elementary witness. On a genuinely nonlinear
branch the transformation has the positively oriented characteristic tangent
and agrees with the supplied local flow for positive strengths. -/
theorem eventually_exists_bounded_elementary_wave {m : ℕ} {flux : ℝ^m → ℝ^m}
    (hflux : ContDiff ℝ 1 flux) (fields : Fin m → CharacteristicField flux) (k : Fin m) (gn : Prop)
    {R T : ℝ × ℝ^m → ℝ^m} {q₀ : ℝ^m} {lo hi : ℝ} (heig : ContDiffAt ℝ 1 (fields k).speed q₀)
    (hT : ContDiffAt ℝ 1 T (0, q₀)) (hR : ContDiffAt ℝ 1 R (0, q₀)) (hTzero : ∀ q, T (0, q) = q)
    (hRzero : ∀ᶠ q in 𝓝 q₀, R (0, q) = q)
    (htan : HasDerivAt (fun s ↦ T (s, q₀)) ((fields k).rightEigenvector q₀) 0)
    (helementary : ∀ p, IsElementaryConnection fields k p.2 (T p))
    (hbranch : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), (¬gn ∨ 0 < p.1) → T p = R p)
    (hflow : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀),
      HasDerivAt (fun t ↦ R (t, p.2)) ((fields k).rightEigenvector (R p)) p.1)
    (hpositive : gn → 0 < fderiv ℝ (fields k).speed q₀ ((fields k).rightEigenvector q₀))
    (hdegenerate : ¬gn → (fields k).IsLinearlyDegenerate)
    (hwindow : (fields k).speed q₀ ∈ Ioo lo hi) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), ∃ u : ℝ^2 → ℝ^m,
      IsElementaryWave fields k p.2 (T p) u ∧
      IsWeakSolution flux forwardHalfSpace u ∧ Measurable u ∧
      (∀ z : ℝ^2, 0 < z 0 → ‖u z‖ ≤ ‖q₀‖ + 1) ∧
      (∀ c : ℝ, 0 < c → ∀ z, u (c • z) = u z) ∧
      (∀ z : ℝ^2, 0 < z 0 → z 1 < lo * z 0 → u z = p.2) ∧
      (∀ z : ℝ^2, 0 < z 0 → hi * z 0 ≤ z 1 → u z = T p) := by
  filter_upwards [eventually_exists_bounded_elementary_wave_with_entropy hflux fields k gn heig hT
    hR hTzero hRzero htan helementary hbranch hflow hpositive hdegenerate hwindow] with p hp
  obtain ⟨u, helem, hu, hmu, hbu, hsu, hlu, hru, -⟩ := hp
  exact ⟨u, helem, hu, hmu, hbu, hsu, hlu, hru⟩

end PDE.Hyperbolic.ConservationLaw.System
