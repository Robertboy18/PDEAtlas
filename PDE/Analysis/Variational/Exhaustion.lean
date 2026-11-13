/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.CompactConvergence
public import PDE.Analysis.WeakConstraints

/-!
# Variational limits under exhaustion of the test domain

A bounded family of Hilbert-space approximants has a weakly convergent refinement.
For each test, a compact linear observation supplies the strong convergence needed
by a continuous nonlinear tested load. Vanishing tested residuals then identify a
solution. Separate mass and gradient radii and linear constraints pass to the same
limit. No compact embedding on the whole spatial domain is required.

For stationary fluid equations, integration by parts onto a compactly supported
test places the quadratic velocity term in a local strong topology. The test may
become admissible only after its support lies inside the approximating domain.
This is the passage to the limit `R → ∞` in the proof of Proposition 1 of Hou, Wang and Yang
(Section 4.3, "Taking weak limits"), where a divergence-free test `ϕ ∈ C_c^∞` is used once
`B_R(0)` contains its support and the quadratic term converges by Rellich–Kondrachov on that
support. The application must supply the actual tested equation, compact observation, and
radius estimates.

## Main results

* `norm_map_le_of_tendsto_weak`: a norm bound on a continuous linear image passes to a weak
  limit.
* `tested_equation_of_tendsto_weak`: a compact observation passes a continuous nonlinear tested
  load to a weak limit.
* `exists_solution_of_bounded_residuals`: vanishing tested residuals of a bounded family give an
  exact solution that keeps the image radii and the linear constraints.
* `exists_solution_of_eventually_eq`: the same when each test equation holds only eventually.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 4.3, proof of
  Proposition 1, p. 31. <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public section

namespace PDE.Analysis.Variational

open Filter Set
open scoped Topology

section WeakLimit

variable {H Y : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A norm bound on a continuous linear image passes to a weak limit. -/
theorem norm_map_le_of_tendsto_weak
    (A : H →L[ℝ] Y) {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → H} {uLimit : H} {radius : ℝ}
    (hu : Tendsto (fun i ↦ toWeakSpace ℝ H (u i)) l
      (𝓝 (toWeakSpace ℝ H uLimit)))
    (hbound : ∀ᶠ i in l, ‖A (u i)‖ ≤ radius) : ‖A uLimit‖ ≤ radius := by
  simpa only [LinearEquiv.symm_apply_apply] using
    WeakCompactness.norm_le_of_tendsto_of_norm_le (tendsto_weak_map A hu) hbound

/-- A compact observation permits a continuous nonlinear tested load in a weak limit. -/
theorem tested_equation_of_tendsto_weak
    (linear : StrongDual ℝ H) (observe : H →L[ℝ] Y)
    (hcompact : IsCompactOperator observe) (nonlinear : Y → ℝ)
    (hcontinuous : Continuous nonlinear) (forcing : ℝ)
    {ι : Type*} {l : Filter ι} [l.NeBot] {u : ι → H} {uLimit : H}
    (hbounded : Bornology.IsBounded (range u))
    (hu : Tendsto (fun i ↦ toWeakSpace ℝ H (u i)) l
      (𝓝 (toWeakSpace ℝ H uLimit)))
    (hresidual : Tendsto (fun i ↦ linear (u i) + nonlinear (observe (u i)) - forcing)
      l (𝓝 0)) : linear uLimit + nonlinear (observe uLimit) = forcing := by
  have hlinear : Tendsto (fun i ↦ linear (u i)) l (𝓝 (linear uLimit)) := by
    simpa only [LinearEquiv.symm_apply_apply] using
      WeakCompactness.tendsto_evaluation hu linear
  have hobserve := tendsto_compactOperator_of_tendsto_weak_of_bounded
    observe hcompact hbounded hu
  have hnonlinear := hcontinuous.continuousAt.tendsto.comp hobserve
  have hlimit := (hlinear.add hnonlinear).sub (tendsto_const_nhds (x := forcing))
  exact sub_eq_zero.mp (tendsto_nhds_unique hlimit hresidual)

end WeakLimit

section Existence

variable {H Y M D C T J ι : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup M] [NormedSpace ℝ M]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup C] [NormedSpace ℝ C]

/-- Vanishing tested residuals of a bounded approximating family yield an exact solution,
retaining separate image radii and every eventually satisfied linear constraint.
The compact observation is local to each test; the test index need not be countable. -/
theorem exists_solution_of_bounded_residuals
    (l : Filter ι) [l.NeBot] (u : ι → H)
    (hbounded : Bornology.IsBounded (range u))
    (mass : H →L[ℝ] M) (gradient : H →L[ℝ] D) (massRadius gradientRadius : ℝ)
    (hmass : ∀ᶠ i in l, ‖mass (u i)‖ ≤ massRadius)
    (hgradient : ∀ᶠ i in l, ‖gradient (u i)‖ ≤ gradientRadius)
    (constraints : J → H →L[ℝ] C)
    (hconstraints : ∀ᶠ i in l, ∀ j, constraints j (u i) = 0)
    (linear : T → StrongDual ℝ H) (observe : T → H →L[ℝ] Y)
    (hcompact : ∀ t, IsCompactOperator (observe t))
    (nonlinear : T → Y → ℝ) (hcontinuous : ∀ t, Continuous (nonlinear t))
    (forcing : T → ℝ)
    (hresidual : ∀ t, Tendsto
      (fun i ↦ linear t (u i) + nonlinear t (observe t (u i)) - forcing t) l (𝓝 0)) :
    ∃ uLimit : H, ‖mass uLimit‖ ≤ massRadius ∧ ‖gradient uLimit‖ ≤ gradientRadius ∧
      (∀ j, constraints j uLimit = 0) ∧
      ∀ t, linear t uLimit + nonlinear t (observe t uLimit) = forcing t := by
  obtain ⟨uLimit, refinement, hle, hu⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter l u hbounded
  refine ⟨uLimit, norm_map_le_of_tendsto_weak mass hu (hmass.filter_mono hle),
    norm_map_le_of_tendsto_weak gradient hu (hgradient.filter_mono hle),
    constraints_eq_zero_of_tendsto_weak constraints hu (hconstraints.filter_mono hle), ?_⟩
  intro t
  exact tested_equation_of_tendsto_weak (linear t) (observe t) (hcompact t)
    (nonlinear t) (hcontinuous t) (forcing t) hbounded hu ((hresidual t).mono_left hle)

/-- In an exhaustion, each test equation need only hold eventually, once its support
fits inside the approximating domain. The same limit satisfies all test equations. -/
theorem exists_solution_of_eventually_eq
    (l : Filter ι) [l.NeBot] (u : ι → H)
    (hbounded : Bornology.IsBounded (range u))
    (mass : H →L[ℝ] M) (gradient : H →L[ℝ] D) (massRadius gradientRadius : ℝ)
    (hmass : ∀ᶠ i in l, ‖mass (u i)‖ ≤ massRadius)
    (hgradient : ∀ᶠ i in l, ‖gradient (u i)‖ ≤ gradientRadius)
    (constraints : J → H →L[ℝ] C)
    (hconstraints : ∀ᶠ i in l, ∀ j, constraints j (u i) = 0)
    (linear : T → StrongDual ℝ H) (observe : T → H →L[ℝ] Y)
    (hcompact : ∀ t, IsCompactOperator (observe t))
    (nonlinear : T → Y → ℝ) (hcontinuous : ∀ t, Continuous (nonlinear t))
    (forcing : T → ℝ)
    (hequation : ∀ t, ∀ᶠ i in l,
      linear t (u i) + nonlinear t (observe t (u i)) = forcing t) :
    ∃ uLimit : H, ‖mass uLimit‖ ≤ massRadius ∧ ‖gradient uLimit‖ ≤ gradientRadius ∧
      (∀ j, constraints j uLimit = 0) ∧
      ∀ t, linear t uLimit + nonlinear t (observe t uLimit) = forcing t := by
  apply exists_solution_of_bounded_residuals l u hbounded mass gradient
    massRadius gradientRadius hmass hgradient constraints hconstraints
    linear observe hcompact nonlinear hcontinuous forcing
  intro t
  apply tendsto_const_nhds.congr'
  filter_upwards [hequation t] with i hi
  exact (sub_eq_zero.mpr hi).symm

end Existence

end PDE.Analysis.Variational
