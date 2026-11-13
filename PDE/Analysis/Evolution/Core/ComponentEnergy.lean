/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import PDE.Analysis.Evolution.Core.EnergyIdentity
import PDE.Analysis.Evolution.Core.Gronwall

/-!
# Energy estimates from finite systems of evolution equations

For finitely many trajectories `uᵢ : ℝ → V` in a real inner product space with
derivatives `duᵢ`, the weighted energy `E = ½ ∑ᵢ wᵢ ‖uᵢ‖²` has derivative
`∑ᵢ wᵢ ⟪duᵢ, uᵢ⟫`. The scalar Grönwall, dissipative and first-contact bounds
therefore hold for `E` under hypotheses on this inner-product expression alone.
The weights are constant in time and may have any sign. They are nonnegative
when `E` is used as an energy.

## Main results

* `finiteWeightedEnergy`, `finiteWeightedEnergyRate`: the energy
  `½ ∑ᵢ wᵢ ‖uᵢ‖²` and its derivative `∑ᵢ wᵢ ⟪uᵢ', uᵢ⟫`, with
  `hasDerivAt_finiteWeightedEnergy` and `hasDerivWithinAt_finiteWeightedEnergy`.
* `finiteWeightedEnergy_le_gronwallBound`: differential Grönwall for the
  component system, with the energy derivative derived from the component
  equations.
* `finiteWeightedEnergy_dissipative_bound`,
  `finiteWeightedEnergy_sublevel_invariant`: the dissipative bound and
  sublevel invariance under `rate + α energy ≤ β`.
* `finiteWeightedEnergy_strict_sublevel_invariant`: first-contact closure
  when the production is negative on the boundary `energy = R`.
-/

@[expose] public section

noncomputable section

open Set

namespace PDE.Analysis.Evolution

open scoped InnerProductSpace

variable {ι V : Type*} [Fintype ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Half the finite weighted sum of the squared component norms. -/
def finiteWeightedEnergy (weight : ι → ℝ) (u : ι → ℝ → V) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, weight i * ‖u i t‖ ^ 2

/-- The inner-product expression obtained by differentiating `finiteWeightedEnergy`. -/
def finiteWeightedEnergyRate
    (weight : ι → ℝ) (u du : ι → ℝ → V) (t : ℝ) : ℝ :=
  ∑ i, weight i * inner ℝ (du i t) (u i t)

omit [InnerProductSpace ℝ V] in
/-- A finite weighted energy is nonnegative when every weight is nonnegative. -/
theorem finiteWeightedEnergy_nonneg
    {weight : ι → ℝ} (hweight : ∀ i, 0 ≤ weight i)
    (u : ι → ℝ → V) (t : ℝ) :
    0 ≤ finiteWeightedEnergy weight u t := by
  unfold finiteWeightedEnergy
  exact mul_nonneg (by norm_num) <| Finset.sum_nonneg fun i _ ↦
    mul_nonneg (hweight i) (sq_nonneg _)

/-- Componentwise derivatives give the derivative of the finite weighted energy:
`d/dt (½ ∑ᵢ wᵢ ‖uᵢ‖²) = ∑ᵢ wᵢ ⟪uᵢ', uᵢ⟫`. -/
theorem hasDerivAt_finiteWeightedEnergy
    {weight : ι → ℝ} {u du : ι → ℝ → V} {t : ℝ}
    (hu : ∀ i, HasDerivAt (u i) (du i t) t) :
    HasDerivAt (finiteWeightedEnergy weight u)
      (finiteWeightedEnergyRate weight u du t) t := by
  have hsum :=
    HasDerivAt.sum (u := Finset.univ) fun i _ ↦
      (hasDerivAt_half_norm_sq (hu i)).const_mul (weight i)
  apply hsum.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun s ↦ by
    simp only [Finset.sum_apply]
    change
      (1 / 2 : ℝ) * ∑ i, weight i * ‖u i s‖ ^ 2 =
        ∑ i, weight i * ((1 / 2 : ℝ) * ‖u i s‖ ^ 2)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Componentwise differentiability implies differentiability of the finite
weighted energy. -/
theorem differentiableAt_finiteWeightedEnergy
    {weight : ι → ℝ} {u : ι → ℝ → V} {t : ℝ}
    (hu : ∀ i, DifferentiableAt ℝ (u i) t) :
    DifferentiableAt ℝ (finiteWeightedEnergy weight u) t := by
  let du : ι → ℝ → V := fun i _ ↦ deriv (u i) t
  exact
    (hasDerivAt_finiteWeightedEnergy (du := du) fun i ↦
      (hu i).hasDerivAt).differentiableAt

omit [InnerProductSpace ℝ V] in
/-- Componentwise continuity implies continuity of the finite weighted energy. -/
theorem continuousAt_finiteWeightedEnergy
    {weight : ι → ℝ} {u : ι → ℝ → V} {t : ℝ}
    (hu : ∀ i, ContinuousAt (u i) t) :
    ContinuousAt (finiteWeightedEnergy weight u) t := by
  unfold finiteWeightedEnergy
  fun_prop

/-- Componentwise derivative identities on a set make the finite weighted
energy continuous on that set. -/
theorem continuousOn_finiteWeightedEnergy_of_hasDerivAt
    {weight : ι → ℝ} {u du : ι → ℝ → V} {s : Set ℝ}
    (hu : ∀ t ∈ s, ∀ i, HasDerivAt (u i) (du i t) t) :
    ContinuousOn (finiteWeightedEnergy weight u) s := by
  intro t ht
  exact (hasDerivAt_finiteWeightedEnergy (hu t ht)).continuousAt.continuousWithinAt

/-- Relative derivative identity for component trajectories defined on a time set. -/
theorem hasDerivWithinAt_finiteWeightedEnergy
    {weight : ι → ℝ} {u du : ι → ℝ → V} {t : ℝ} {s : Set ℝ}
    (hu : ∀ i, HasDerivWithinAt (u i) (du i t) s t) :
    HasDerivWithinAt (finiteWeightedEnergy weight u)
      (finiteWeightedEnergyRate weight u du t) s t := by
  change HasDerivWithinAt
    (fun r ↦ (1 / 2 : ℝ) * ∑ i, weight i * ‖u i r‖ ^ 2)
    (∑ i, weight i * inner ℝ (du i t) (u i t)) s t
  have hsum :=
    HasDerivWithinAt.sum (u := Finset.univ) fun i _ ↦
      (hasDerivWithinAt_half_norm_sq (hu i)).const_mul (weight i)
  have hidentity (r : ℝ) :
      (1 / 2 : ℝ) * ∑ i, weight i * ‖u i r‖ ^ 2 =
        ∑ i, weight i * ((1 / 2 : ℝ) * ‖u i r‖ ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  apply hsum.congr_of_eventuallyEq
  · exact Filter.Eventually.of_forall fun r ↦ by
      simpa only [Finset.sum_apply] using hidentity r
  · simpa only [Finset.sum_apply] using hidentity t

/--
Differential Grönwall for a finite component system. If each `uᵢ` has
derivative `duᵢ` within `[a, b]`, `E(a) ≤ δ` and `∑ᵢ wᵢ ⟪duᵢ, uᵢ⟫ ≤ K E + ε`,
then `E(t) ≤ gronwallBound δ K ε (t - a)`.
-/
theorem finiteWeightedEnergy_le_gronwallBound
    {weight : ι → ℝ} {u du : ι → ℝ → V}
    {a b δ K ε : ℝ}
    (hu : ∀ t ∈ Icc a b, ∀ i,
      HasDerivWithinAt (u i) (du i t) (Icc a b) t)
    (ha : finiteWeightedEnergy weight u a ≤ δ)
    (hproduction : ∀ t ∈ Icc a b,
      finiteWeightedEnergyRate weight u du t ≤
        K * finiteWeightedEnergy weight u t + ε) :
    ∀ t ∈ Icc a b,
      finiteWeightedEnergy weight u t ≤ gronwallBound δ K ε (t - a) := by
  apply le_gronwallBound_of_hasDerivWithinAt_le
    (e := finiteWeightedEnergy weight u)
    (de := finiteWeightedEnergyRate weight u du)
  · intro t ht
    exact hasDerivWithinAt_finiteWeightedEnergy (hu t ht)
  · exact ha
  · exact hproduction

/--
Dissipative bound for a finite component system. If
`∑ᵢ wᵢ ⟪duᵢ, uᵢ⟫ + α E ≤ β` on `[a, b]` with `α > 0`, then
`E(t) ≤ E(a) e^{-α(t-a)} + (β/α)(1 - e^{-α(t-a)})`.
-/
theorem finiteWeightedEnergy_dissipative_bound
    {weight : ι → ℝ} {u du : ι → ℝ → V}
    {a b α β : ℝ}
    (hα : 0 < α)
    (hu : ∀ t ∈ Icc a b, ∀ i,
      HasDerivWithinAt (u i) (du i t) (Icc a b) t)
    (hproduction : ∀ t ∈ Icc a b,
      finiteWeightedEnergyRate weight u du t +
          α * finiteWeightedEnergy weight u t ≤ β) :
    ∀ t ∈ Icc a b,
      finiteWeightedEnergy weight u t ≤
        finiteWeightedEnergy weight u a * Real.exp (-α * (t - a)) +
          (β / α) * (1 - Real.exp (-α * (t - a))) := by
  apply dissipative_energy_bound
    (e := finiteWeightedEnergy weight u)
    (de := finiteWeightedEnergyRate weight u du) hα
  · intro t ht
    exact hasDerivWithinAt_finiteWeightedEnergy (hu t ht)
  · exact hproduction

/-- Under the hypotheses of `finiteWeightedEnergy_dissipative_bound`, the sublevel
`E ≤ R` is invariant whenever `β ≤ α R`. -/
theorem finiteWeightedEnergy_sublevel_invariant
    {weight : ι → ℝ} {u du : ι → ℝ → V}
    {a b α β R : ℝ}
    (hα : 0 < α)
    (hu : ∀ t ∈ Icc a b, ∀ i,
      HasDerivWithinAt (u i) (du i t) (Icc a b) t)
    (ha : finiteWeightedEnergy weight u a ≤ R)
    (hequilibrium : β ≤ α * R)
    (hproduction : ∀ t ∈ Icc a b,
      finiteWeightedEnergyRate weight u du t +
          α * finiteWeightedEnergy weight u t ≤ β) :
    ∀ t ∈ Icc a b, finiteWeightedEnergy weight u t ≤ R := by
  apply dissipative_energy_sublevel_invariant
    (e := finiteWeightedEnergy weight u)
    (de := finiteWeightedEnergyRate weight u du) hα
  · intro t ht
    exact hasDerivWithinAt_finiteWeightedEnergy (hu t ht)
  · exact ha
  · exact hequilibrium
  · exact hproduction

/--
First-contact closure for a finite component system. If each `uᵢ` is
differentiable on `[a, b]`, `E(a) < R`, and `∑ᵢ wᵢ ⟪duᵢ, uᵢ⟫ < 0` at every time
where `E = R`, then `E < R` on `[a, b]`.
-/
theorem finiteWeightedEnergy_strict_sublevel_invariant
    {weight : ι → ℝ} {u du : ι → ℝ → V}
    {a b R : ℝ}
    (hu : ∀ t ∈ Icc a b, ∀ i, HasDerivAt (u i) (du i t) t)
    (ha : finiteWeightedEnergy weight u a < R)
    (hboundary : ∀ t ∈ Icc a b,
      finiteWeightedEnergy weight u t = R →
        finiteWeightedEnergyRate weight u du t < 0) :
    ∀ t ∈ Icc a b, finiteWeightedEnergy weight u t < R := by
  have henergyDeriv (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (finiteWeightedEnergy weight u)
        (finiteWeightedEnergyRate weight u du t) t :=
    hasDerivAt_finiteWeightedEnergy (hu t ht)
  have henergyContinuous :
      ContinuousOn (finiteWeightedEnergy weight u) (Icc a b) := by
    intro t ht
    exact (henergyDeriv t ht).continuousAt.continuousWithinAt
  apply strict_sublevel_invariant_of_deriv_neg_on_boundary
    (e := finiteWeightedEnergy weight u) henergyContinuous ha
  intro t ht hboundaryValue
  rw [(henergyDeriv t ht).deriv]
  exact hboundary t ht hboundaryValue

end PDE.Analysis.Evolution
