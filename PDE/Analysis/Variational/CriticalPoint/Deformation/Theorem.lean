/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.CriticalPoint.PalaisSmale.GradientBound
public import PDE.Analysis.Variational.CriticalPoint.Deformation.Energy
public import PDE.Analysis.Evolution.ODE.Autonomous.Bounded.Flow

/-!
# Deformation near a noncritical energy level

From a continuously differentiable functional, Lipschitz bounds for its gradient on balls,
and the raw Palais–Smale sequence condition, we construct a single continuous flow with the
four deformation properties. Every sufficiently small outer band is allowed. Its inner width
is fixed before the states or times.

This is the deformation theorem of Evans, §8.5.1, Theorem 1. His class `C` consists of the
functionals in `C¹(H; ℝ)` whose derivative is Lipschitz on bounded sets, his (2); these are
the hypotheses `hI` and `hG`, and `hc` is his hypothesis (3), `K_c = ∅`. We prove his
properties (i)-(iv) in a slightly stronger form: points with `ε ≤ |I x - c|` are fixed at all
times, and the energy is nonincreasing for all `t ≥ 0`.

The flow is defined at all real times, so joint continuity at time zero and the
unit-interval endpoints comes from the ODE construction. Its time slices
are homeomorphisms through Mathlib's `Flow.toHomeomorph`. The fixed region is the
complement of the symmetric outer energy band, including its endpoints.

## Main results

* `PalaisSmale.exists_deformation`: let `I` be `C¹` with gradient Lipschitz on balls, satisfy
  the Palais–Smale condition and have no critical point at the level `c`. Then every
  sufficiently small `ε > 0` has a `δ ∈ (0, ε)` and a flow `Φ` with `Φ 0 x = x`, `Φ t x = x`
  when `ε ≤ |I x - c|`, `I (Φ t x) ≤ I x` for `t ≥ 0`, and `I (Φ 1 x) ≤ c - δ` when
  `I x ≤ c + δ`.

## How it works

We follow Evans's proof. `PalaisSmale.exists_gradient_gap` is his step 1, the gradient gap
(4) on a closed band, and `δ = min (ε / 2) (σ² / 4)` satisfies his (7). His field (10) is
`descendingField`, built from the energy cutoff `energyBandCutoff` in place of his distance
quotient `g` and from the radial projection of the gradient, which is his `h(‖I'[u]‖) I'[u]`.
The field is bounded by one and Lipschitz on balls, so
`Evolution.exists_flow_hasDerivAt_of_bounded` solves the ODE (11) for all real times. As in
his steps 4 and 5, `antitone_energy_of_descendingField` gives (iii) and
`energy_drop_of_descendingField` gives (iv).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.5.1(a), the class `C`, the sets `A_c` and `K_c`,
  and Theorem 1 (Deformation Theorem) with its proof, (2)-(15), pp. 502-505.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Gradient

open Metric Set

namespace PDE.Analysis.Variational

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The raw deformation theorem in an arbitrary real Hilbert space. One jointly
continuous flow has the initial identity, fixes the outer band's complement, decreases
energy, and lowers the upper inner sublevel to the lower one at time one. -/
theorem PalaisSmale.exists_deformation {I : H → ℝ} (hPS : PalaisSmale I)
    (hI : ContDiff ℝ 1 I)
    (hG : ∀ R : ℝ, 0 < R →
      ∃ K : NNReal, LipschitzOnWith K (∇ I) (closedBall 0 R))
    {c : ℝ} (hc : ∀ x, I x = c → ∇ I x ≠ 0) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioo (0 : ℝ) ε₀,
      ∃ δ ∈ Ioo (0 : ℝ) ε, ∃ Φ : Flow ℝ H,
        (∀ x, Φ 0 x = x) ∧
        (∀ x t, ε ≤ |I x - c| → Φ t x = x) ∧
        (∀ x t, 0 ≤ t → I (Φ t x) ≤ I x) ∧
        (∀ x, I x ≤ c + δ → I (Φ 1 x) ≤ c - δ) := by
  obtain ⟨ε₀, hε₀, σ, hσ, hgap⟩ := hPS.exists_gradient_gap hI hc
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε
  let δ := min (ε / 2) (σ ^ 2 / 4)
  have hδ : 0 < δ := lt_min (div_pos hε.1 (by norm_num))
    (div_pos (sq_pos_of_pos hσ.1) (by norm_num))
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith [hε.1])
  have hwidth : 2 * δ < σ ^ 2 := by
    have hle := min_le_right (ε / 2) (σ ^ 2 / 4)
    have hsq : 0 < σ ^ 2 := sq_pos_of_pos hσ.1
    dsimp [δ]
    linarith
  have hdiff := hI.differentiable one_ne_zero
  have hF := descendingField_lipschitzOn_balls hdiff hG c δ ε
  obtain ⟨Φ, hΦ⟩ := Evolution.exists_flow_hasDerivAt_of_bounded
    (M := 1) (norm_descendingField_le I c δ ε) hF
  refine ⟨δ, ⟨hδ, hδε⟩, Φ, Φ.map_zero_apply, ?_, ?_, ?_⟩
  · intro x t hx
    have hz := descendingField_eq_zero hδε hx
    have heq : (fun s ↦ Φ s x) = fun _ ↦ x := by
      apply Evolution.eq_of_hasDerivAt_of_lipschitzOn_balls hF (t₀ := 0)
        (hΦ x) ?_ (Φ.map_zero_apply x)
      intro s
      simpa only [hz] using hasDerivAt_const s x
    exact congrFun heq t
  · intro x t ht
    have hm := antitone_energy_of_descendingField hdiff (hΦ x)
    simpa only [Function.comp_apply, Φ.map_zero_apply] using hm ht
  · intro x hx
    apply energy_drop_of_descendingField hdiff hδε hσ hwidth
      (fun y hy ↦ hgap y (hy.trans (hδε.trans hε.2).le)) (hΦ x)
    simpa only [Φ.map_zero_apply] using hx

end PDE.Analysis.Variational
