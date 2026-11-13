/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.NullLagrangian.SecondJet
public import PDE.CalculusOfVariations.FirstVariation.EulerLagrange
public import PDE.Spaces.Sobolev.Extension.C1.ClassicalHigherOrder.VectorValued

/-!
# Equal-boundary action invariance for null Lagrangians

The nullity hypothesis is the original property testing smooth maps. Second-jet
realization supplies the equation for the `C²` interpolation family, and the
first-variation identity makes its action constant.

The closure theorem takes classical derivatives of finite order and continuous
closure representatives on a bounded open `C²` graph domain. Ambient extensions
are constructed by finite-order reflection.

`IsNullLagrangianOn.lagrangianAction_eq_of_eqOn_frontier` is Evans, §8.1.4(b), Theorem 1,
for maps that are `C²` up to the boundary; Evans's proof also differentiates the action
along the segment between the two maps.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.1.4(b), Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Elementwise

namespace PDE.CalculusOfVariations

open Analysis SobolevSpace

variable {n m : ℕ} {Ω : Set (ℝ^n)}
  {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ} {u v : ℝ^n → ℝ^m}

/-- Equal boundary values give equal actions for ambient `C²` maps.
Only C¹ graph geometry is needed in this ambient formulation. -/
theorem IsNullLagrangianOn.lagrangianAction_eq_of_contDiff
    (hnull : IsNullLagrangianOn Ω L)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    (hL : ContinuousSecondJetOn
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      {a | a.2.2 ∈ Ω})
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hboundary : EqOn u v (frontier Ω)) :
    lagrangianAction Ω L u = lagrangianAction Ω L v := by
  let w : ℝ^n → ℝ^m := fun x ↦ v x - u x
  have hw : ContDiff ℝ 2 w := hv.sub hu
  have hz : ∀ x ∈ frontier Ω, w x = 0 := fun x hx ↦ sub_eq_zero.mpr (hboundary hx).symm
  have hd (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ lagrangianAction Ω L (fun x ↦ u x + s • w x)) 0 t := by
    apply (hasDerivAt_lagrangianAction_eulerLagrange
      hopen hbounded hgraph hL hu hw hz t).congr_deriv
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
    apply Finset.sum_eq_zero
    intro k _
    have ht : ContDiff ℝ 2 (fun y ↦ u y + t • w y) :=
      hu.add ((contDiff_const (c := t)).smul hw)
    have hzero := hnull.classicalEulerLagrange_eq_zero_of_contDiffOn
      hopen ht.contDiffOn hL.contDiffOn x hx k
    exact mul_eq_zero_of_left hzero _
  have hc := is_const_of_deriv_eq_zero (fun t ↦ (hd t).differentiableAt)
    (fun t ↦ (hd t).deriv) (0 : ℝ) 1
  simpa [w] using hc

variable [Fact (0 < n)]

/-- A general smooth null Lagrangian has the same integral on `C²` closure
maps with equal boundary values, on a bounded open `C²` graph domain.
Continuity on the closure binds the assigned boundary values to their interior limits. -/
theorem IsNullLagrangianOn.lagrangianAction_eq_of_eqOn_frontier
    (hnull : IsNullLagrangianOn Ω L)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
    (hL : ContinuousSecondJetOn
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      {a | a.2.2 ∈ Ω})
    (hu : ∀ k, ContDiffUpToBoundary 2 (fun x ↦ u x k) Ω)
    (hv : ∀ k, ContDiffUpToBoundary 2 (fun x ↦ v x k) Ω)
    (huc : ContinuousOn u (closure Ω)) (hvc : ContinuousOn v (closure Ω))
    (hboundary : EqOn u v (frontier Ω)) :
    lagrangianAction Ω L u = lagrangianAction Ω L v := by
  obtain ⟨U, hU, hUu⟩ := exists_contDiff_succ_extension_vector 1 hu huc hopen hbounded hgraph
  obtain ⟨V, hV, hVv⟩ := exists_contDiff_succ_extension_vector 1 hv hvc hopen hbounded hgraph
  have hUV : EqOn U V (frontier Ω) := by
    intro x hx
    rw [hUu (frontier_subset_closure hx), hVv (frontier_subset_closure hx), hboundary hx]
  calc
    lagrangianAction Ω L u = lagrangianAction Ω L U :=
      lagrangianAction_congr hopen (hUu.mono subset_closure).symm
    _ = lagrangianAction Ω L V :=
      hnull.lagrangianAction_eq_of_contDiff hopen hbounded
        (hgraph.hasC1GraphBoundary (by norm_num)) hL hU hV hUV
    _ = lagrangianAction Ω L v :=
      lagrangianAction_congr hopen (hVv.mono subset_closure)

end PDE.CalculusOfVariations
