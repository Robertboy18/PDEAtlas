/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.MaximumPrinciple.FactoredOperator
public import PDE.Parabolic.Heat.Equation
import PDE.FDeriv.Calculus
import CAS.ExactTactic

/-!
# Maximum principle for the heat equation

The weak maximum principle for the heat equation on a bounded cylinder: if `u` is continuous
on `closure Ω × [0, T]`, is `C²` in space and differentiable in time on `Ω × (0, T)`, and
satisfies `uₜ - Δu ≤ 0` there, then `u` is bounded above by its supremum over the parabolic
boundary `(∂Ω × [0, T]) ∪ (closure Ω × {0})`. Applying this to `-u` gives the minimum
principle for supersolutions. This is Evans's weak maximum principle for parabolic operators
with `c ≡ 0` (§7.1.4, Theorem 8) specialized to `uₜ - Δu`; for solutions of the heat equation
it is part (i) of §2.3.3, Theorem 4.

For a strict subsolution `uₜ - Δu < 0`, a maximum over the
closed cylinder that is not attained on the parabolic boundary sits at an interior point
`x ∈ Ω` and a time `t ∈ (0, T]`; there `Δu(x, t) ≤ 0` because `x` is a spatial local maximum
and `uₜ(x, t) ≥ 0` because `t` is a maximum of `s ↦ u(x, s)` on `[0, T]` (one-sided at
`t = T`), so `uₜ - Δu ≥ 0`, a contradiction. The non-strict case follows by perturbing to
`u - εt`, which lowers the residual by exactly `ε` and the boundary values by at most `εT`.

## Main results

* `heatParabolicOperator_eq_factoredParabolicOperator`: `uₜ - Δu` is the factored parabolic
  operator with coordinate directions and zero drift.
* `heatParabolicOperator_sub_time`, `heatParabolicOperator_neg`: how the operator responds to
  the perturbation `u - εt` and to negation.
* `strict_heat_subsolution_le_of_boundary_le`: the maximum principle for strict subsolutions.
* `heat_subsolution_le_of_boundary_le`: the weak maximum principle for subsolutions
  `uₜ - Δu ≤ 0`.
* `boundary_le_heat_supersolution`: the weak minimum principle for supersolutions
  `uₜ - Δu ≥ 0`.

## Implementation notes

The maximum and minimum principles specialize the factored operator to coordinate directions
and zero drift. The common extremum and perturbation proofs are in
`PDE.Parabolic.MaximumPrinciple.FactoredOperator`. The regularity hypotheses are pointwise
(`ContDiffAt ℝ 2` in space, `DifferentiableAt` in time). For the weak principles they
are imposed only on `Ω × (0, T)`: first apply the estimate on shorter cylinders,
then use continuity to reach the final time. No extension beyond `T` is required.
The strict auxiliary theorem retains its pointwise hypotheses at the terminal face.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.3(a), Theorem 4 (Strong maximum principle for the heat
  equation), p. 55; §7.1.4(a), Theorem 8 (Weak maximum principle), (62)-(64), and its proof,
  pp. 389-390.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

noncomputable section

namespace HeatEquation

open ParabolicMaximum

open Filter Function Set
open scoped Topology

/-- The heat operator is the factored parabolic operator with coordinate directions and
zero drift. Local spatial `C²` regularity identifies the line and coordinate second derivatives. -/
theorem heatParabolicOperator_eq_factoredParabolicOperator {n : ℕ}
    (u : ℝ^n → ℝ → ℝ) (x : ℝ^n) (t : ℝ)
    (hu : ContDiffAt ℝ 2 (fun y ↦ u y t) x) :
    heatParabolicOperator u x t =
      factoredParabolicOperator (fun _ _ i ↦ EuclideanSpace.single i 1)
        (fun _ _ ↦ 0) u x t := by
  have hsecond := (hu.fderiv_right (m := (1 : WithTop ℕ∞))
    (by norm_num)).differentiableAt (by norm_num)
  simp only [heatParabolicOperator, factoredParabolicOperator, factoredEllipticOperator,
    map_zero, add_zero, sub_eq_add_neg]
  congr 2
  apply Finset.sum_congr rfl
  intro i _hi
  rw [PDE.Analysis.secondDirectionalDerivative_eq_fderiv hu,
    PDE.secondPartialDeriv_eq_fderiv i i hsecond]

/-- Subtracting `εt` lowers the heat residual by exactly `ε`. -/
theorem heatParabolicOperator_sub_time {n : ℕ}
    (u : ℝ^n → ℝ → ℝ)
    (ε : ℝ) (x : ℝ^n) (t : ℝ)
    (hux : ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hut : DifferentiableAt ℝ (u x) t) :
    heatParabolicOperator (fun y s ↦ u y s - ε * s) x t =
      heatParabolicOperator u x t - ε := by
  have hlin : HasDerivAt (fun s : ℝ ↦ ε * s) ε t := by
    cas
  have htime :
      deriv (fun s ↦ u x s - ε * s) t = deriv (u x) t - ε :=
    (hut.hasDerivAt.sub hlin).deriv
  have hconst :
      ContDiffAt ℝ 2 (fun _y : ℝ^n ↦ ε * t) x :=
    contDiffAt_const
  have hspace :
      laplacian (fun y ↦ u y t - ε * t) x =
        laplacian (fun y ↦ u y t) x := by
    rw [PDE.laplacian_sub
      (fun y ↦ u y t) (fun _y : ℝ^n ↦ ε * t)
      x hux hconst]
    simp
  rw [heatParabolicOperator, heatParabolicOperator, htime, hspace]
  ring

/-- The heat operator commutes with negation. -/
theorem heatParabolicOperator_neg {n : ℕ}
    (u : ℝ^n → ℝ → ℝ)
    (x : ℝ^n) (t : ℝ) :
    heatParabolicOperator (fun y s ↦ -u y s) x t =
      -heatParabolicOperator u x t := by
  have htime : deriv (fun s ↦ -u x s) t = -deriv (u x) t := deriv.neg
  have hspace :
      laplacian (fun y ↦ -u y t) x =
        -laplacian (fun y ↦ u y t) x := by
    exact PDE.laplacian_neg (fun y ↦ u y t) x
  rw [heatParabolicOperator, heatParabolicOperator, htime, hspace]
  ring

/-- The strict case in the proof of Evans's §7.1.4, Theorem 8, for the heat operator.

At an interior spatial maximum `Δu ≤ 0`; at a positive-time maximum on
`[0,T]`, including the terminal face, `uₜ ≥ 0`. Hence `uₜ - Δu ≥ 0`,
contradicting the strict subsolution inequality. -/
theorem strict_heat_subsolution_le_of_boundary_le {n : ℕ}
    {Ω : Set (ℝ^n)} {T M : ℝ}
    (hΩopen : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩcompact : IsCompact (closure Ω)) (hT : 0 < T)
    (u : ℝ^n → ℝ → ℝ)
    (hucont :
      ContinuousOn (fun p ↦ u p.1 p.2) (closedCylinder Ω T))
    (huspace : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hutime : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      DifferentiableAt ℝ (u x) t)
    (hsub : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      heatParabolicOperator u x t < 0)
    (hboundary : ∀ p ∈ parabolicBoundary Ω T, u p.1 p.2 ≤ M) :
    ∀ p ∈ closedCylinder Ω T, u p.1 p.2 ≤ M := by
  apply strict_subsolution_le_of_boundary_le hΩopen hΩne hΩcompact hT
    (fun _ _ i ↦ EuclideanSpace.single i 1) (fun _ _ ↦ 0)
    u hucont huspace hutime ?_ hboundary
  intro x hx t ht
  rw [← heatParabolicOperator_eq_factoredParabolicOperator u x t (huspace x hx t ht)]
  exact hsub x hx t ht

/-- Evans's §7.1.4, Theorem 8, specialized to the heat equation.

An upper bound on the initial and lateral boundary controls every classical
subsolution of `uₜ - Δu ≤ 0` on the closed cylinder. The strict perturbation argument is
applied on shorter cylinders, and continuity then reaches the terminal face.
-/
theorem heat_subsolution_le_of_boundary_le {n : ℕ}
    {Ω : Set (ℝ^n)} {T M : ℝ}
    (hΩopen : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩcompact : IsCompact (closure Ω)) (hT : 0 < T)
    (u : ℝ^n → ℝ → ℝ)
    (hucont :
      ContinuousOn (fun p ↦ u p.1 p.2) (closedCylinder Ω T))
    (huspace : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T,
      ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hutime : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T,
      DifferentiableAt ℝ (u x) t)
    (hsub : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T,
      heatParabolicOperator u x t ≤ 0)
    (hboundary : ∀ p ∈ parabolicBoundary Ω T, u p.1 p.2 ≤ M) :
    ∀ p ∈ closedCylinder Ω T, u p.1 p.2 ≤ M := by
  have hinterior : ∀ p ∈ Ω ×ˢ Ioo 0 T, u p.1 p.2 ≤ M := by
    intro p hp
    have htime : Ioc 0 p.2 ⊆ Ioo 0 T :=
      fun _ ht ↦ ⟨ht.1, ht.2.trans_lt hp.2.2⟩
    have hclosed : closedCylinder Ω p.2 ⊆ closedCylinder Ω T :=
      Set.prod_mono Subset.rfl (Icc_subset_Icc le_rfl hp.2.2.le)
    have hbound : ∀ q ∈ parabolicBoundary Ω p.2, u q.1 q.2 ≤ M := by
      intro q hq
      apply hboundary q
      rcases hq with hq | hq
      · exact Or.inl ⟨hq.1, hq.2.1, hq.2.2.trans hp.2.2.le⟩
      · exact Or.inr hq
    apply subsolution_le_of_boundary_le hΩopen hΩne hΩcompact hp.2.1
      (fun _ _ i ↦ EuclideanSpace.single i 1) (fun _ _ ↦ 0)
      u (hucont.mono hclosed)
      (fun x hx t ht ↦ huspace x hx t (htime ht))
      (fun x hx t ht ↦ hutime x hx t (htime ht)) ?_ hbound p
      ⟨subset_closure hp.1, hp.2.1.le, le_rfl⟩
    intro x hx t ht
    rw [← heatParabolicOperator_eq_factoredParabolicOperator u x t
      (huspace x hx t (htime ht))]
    exact hsub x hx t (htime ht)
  have hclosure : closure (Ω ×ˢ Ioo 0 T) = closedCylinder Ω T := by
    rw [closure_prod_eq, closure_Ioo hT.ne]
    rfl
  intro p hp
  exact le_on_closure hinterior (hclosure ▸ hucont) continuousOn_const
    (hclosure.symm ▸ hp)

/-- The dual heat minimum principle, obtained by applying the maximum
principle to `-u`. -/
theorem boundary_le_heat_supersolution {n : ℕ}
    {Ω : Set (ℝ^n)} {T M : ℝ}
    (hΩopen : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩcompact : IsCompact (closure Ω)) (hT : 0 < T)
    (u : ℝ^n → ℝ → ℝ)
    (hucont :
      ContinuousOn (fun p ↦ u p.1 p.2) (closedCylinder Ω T))
    (huspace : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T,
      ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hutime : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T,
      DifferentiableAt ℝ (u x) t)
    (hsuper : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T,
      0 ≤ heatParabolicOperator u x t)
    (hboundary : ∀ p ∈ parabolicBoundary Ω T, M ≤ u p.1 p.2) :
    ∀ p ∈ closedCylinder Ω T, M ≤ u p.1 p.2 := by
  have hneg := heat_subsolution_le_of_boundary_le hΩopen hΩne hΩcompact hT
    (fun x t ↦ -u x t) hucont.neg
    (fun x hx t ht ↦ (huspace x hx t ht).neg)
    (fun x hx t ht ↦ (hutime x hx t ht).neg)
    (fun x hx t ht ↦ by
      rw [heatParabolicOperator_neg]
      exact neg_nonpos.mpr (hsuper x hx t ht))
    (M := -M) (fun p hp ↦ neg_le_neg (hboundary p hp))
  exact fun p hp ↦ neg_le_neg_iff.mp (hneg p hp)

end HeatEquation
