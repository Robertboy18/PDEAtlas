/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.MaximumPrinciple
import Mathlib.Analysis.Calculus.Deriv.Add
import PDE.FDeriv.Calculus

/-!
# Parabolic comparison and uniqueness

Let `Ω` be a nonempty open set with compact closure. If `u` and `v` are continuous on the closed
cylinder, `C²` in space and differentiable in time for `0 < t ≤ T`, satisfy `uₜ - Δu ≤ vₜ - Δv`
there and `u ≤ v` on the parabolic boundary, then `u ≤ v` on the closed cylinder
(`heat_comparison_of_boundary_le`). Two such functions with the same heat residual and the same
parabolic boundary values agree (`heat_solution_unique`).

Comparison is the weak maximum principle of Evans's §7.1.4, Theorem 8, with `L = -Δ`, applied to
`u - v` (`heat_subsolution_le_of_boundary_le`, with `heatParabolicOperator_sub` for the difference).
Uniqueness, Evans's §2.3.3, Theorem 5, follows as in his proof, which applies the maximum principle
to `±(u - v)`: comparison is applied in both directions.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.3, Theorem 5 (Uniqueness on bounded domains), (22),
  p. 57; §7.1.4(a), Theorem 8 (Weak maximum principle), (62)-(64), pp. 389-390.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

noncomputable section

namespace HeatEquation

open ParabolicMaximum

open Set

/-- The classical heat operator respects subtraction at points
where both functions have the regularity needed to compute the derivatives. -/
theorem heatParabolicOperator_sub {n : ℕ}
    (u v : ℝ^n → ℝ → ℝ)
    (x : ℝ^n) (t : ℝ)
    (huspace : ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hvspace : ContDiffAt ℝ 2 (fun y ↦ v y t) x)
    (hutime : DifferentiableAt ℝ (u x) t)
    (hvtime : DifferentiableAt ℝ (v x) t) :
    heatParabolicOperator (fun y s ↦ u y s - v y s) x t =
      heatParabolicOperator u x t - heatParabolicOperator v x t := by
  have htime :
      deriv (fun s ↦ u x s - v x s) t =
        deriv (u x) t - deriv (v x) t :=
    (hutime.hasDerivAt.sub hvtime.hasDerivAt).deriv
  have hspace :
      laplacian (fun y ↦ u y t - v y t) x =
        laplacian (fun y ↦ u y t) x -
          laplacian (fun y ↦ v y t) x :=
    PDE.laplacian_sub
      (fun y ↦ u y t) (fun y ↦ v y t) x huspace hvspace
  rw [heatParabolicOperator, heatParabolicOperator,
    heatParabolicOperator, htime, hspace]
  ring

/-- Parabolic comparison principle.

If `uₜ-Δu ≤ vₜ-Δv` in the positive-time interior and `u ≤ v` on the
parabolic boundary, then `u ≤ v` throughout the closed cylinder. The proof
applies the weak maximum principle (Evans's §7.1.4, Theorem 8, with `L = -Δ`) to `u - v`. -/
theorem heat_comparison_of_boundary_le {n : ℕ}
    {Ω : Set (ℝ^n)} {T : ℝ}
    (hΩopen : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩcompact : IsCompact (closure Ω)) (hT : 0 < T)
    (u v : ℝ^n → ℝ → ℝ)
    (hucont :
      ContinuousOn (fun p ↦ u p.1 p.2) (closedCylinder Ω T))
    (hvcont :
      ContinuousOn (fun p ↦ v p.1 p.2) (closedCylinder Ω T))
    (huspace : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hvspace : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      ContDiffAt ℝ 2 (fun y ↦ v y t) x)
    (hutime : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      DifferentiableAt ℝ (u x) t)
    (hvtime : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      DifferentiableAt ℝ (v x) t)
    (hoperator : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      heatParabolicOperator u x t ≤ heatParabolicOperator v x t)
    (hboundary : ∀ p ∈ parabolicBoundary Ω T,
      u p.1 p.2 ≤ v p.1 p.2) :
    ∀ p ∈ closedCylinder Ω T, u p.1 p.2 ≤ v p.1 p.2 := by
  let w : ℝ^n → ℝ → ℝ :=
    fun x t ↦ u x t - v x t
  have hwcont :
      ContinuousOn (fun p ↦ w p.1 p.2) (closedCylinder Ω T) :=
    hucont.sub hvcont
  have hwspace : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      ContDiffAt ℝ 2 (fun y ↦ w y t) x := by
    intro x hx t ht
    exact (huspace x hx t ht).sub (hvspace x hx t ht)
  have hwtime : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      DifferentiableAt ℝ (w x) t := by
    intro x hx t ht
    exact (hutime x hx t ht).sub (hvtime x hx t ht)
  have hwsub : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      heatParabolicOperator w x t ≤ 0 := by
    intro x hx t ht
    rw [show w = (fun y s ↦ u y s - v y s) from rfl,
      heatParabolicOperator_sub u v x t
        (huspace x hx t ht) (hvspace x hx t ht)
        (hutime x hx t ht) (hvtime x hx t ht)]
    exact sub_nonpos.mpr (hoperator x hx t ht)
  have hwboundary : ∀ p ∈ parabolicBoundary Ω T,
      w p.1 p.2 ≤ 0 := by
    intro p hp
    exact sub_nonpos.mpr (hboundary p hp)
  have hw :=
    heat_subsolution_le_of_boundary_le
      hΩopen hΩne hΩcompact hT w hwcont
        (fun x hx t ht ↦ hwspace x hx t ⟨ht.1, ht.2.le⟩)
        (fun x hx t ht ↦ hwtime x hx t ⟨ht.1, ht.2.le⟩)
        (fun x hx t ht ↦ hwsub x hx t ⟨ht.1, ht.2.le⟩) hwboundary
  intro p hp
  exact sub_nonpos.mp (hw p hp)

/-- Classical heat solutions with the same parabolic boundary values and
the same heat residual agree throughout the closed cylinder. This is Evans's §2.3.3,
Theorem 5. -/
theorem heat_solution_unique {n : ℕ}
    {Ω : Set (ℝ^n)} {T : ℝ}
    (hΩopen : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩcompact : IsCompact (closure Ω)) (hT : 0 < T)
    (u v : ℝ^n → ℝ → ℝ)
    (hucont :
      ContinuousOn (fun p ↦ u p.1 p.2) (closedCylinder Ω T))
    (hvcont :
      ContinuousOn (fun p ↦ v p.1 p.2) (closedCylinder Ω T))
    (huspace : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hvspace : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      ContDiffAt ℝ 2 (fun y ↦ v y t) x)
    (hutime : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      DifferentiableAt ℝ (u x) t)
    (hvtime : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      DifferentiableAt ℝ (v x) t)
    (hoperator : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      heatParabolicOperator u x t = heatParabolicOperator v x t)
    (hboundary : ∀ p ∈ parabolicBoundary Ω T,
      u p.1 p.2 = v p.1 p.2) :
    ∀ p ∈ closedCylinder Ω T, u p.1 p.2 = v p.1 p.2 := by
  have huv :=
    heat_comparison_of_boundary_le hΩopen hΩne hΩcompact hT
      u v hucont hvcont huspace hvspace hutime hvtime
      (fun x hx t ht ↦ (hoperator x hx t ht).le)
      (fun p hp ↦ (hboundary p hp).le)
  have hvu :=
    heat_comparison_of_boundary_le hΩopen hΩne hΩcompact hT
      v u hvcont hucont hvspace huspace hvtime hutime
      (fun x hx t ht ↦ (hoperator x hx t ht).ge)
      (fun p hp ↦ (hboundary p hp).ge)
  intro p hp
  exact le_antisymm (huv p hp) (hvu p hp)

end HeatEquation
