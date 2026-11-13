/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MeanValue.MaximumPrinciple
public import PDE.Elliptic.Classical.MeanValue.PDEToMeanValue
import PDE.FDeriv.Calculus

/-!
# The sphere mean-value property implies harmonicity

A continuous function with the sphere mean-value property is harmonic. On a
small ball around each point, continuously extend the boundary trace and form
the ball Poisson solution. Their difference has the mean-value property,
vanishes on the boundary, and is therefore zero by the mean-value boundary
principle. Local equality with the Poisson solution supplies `C²` regularity
and a vanishing Laplacian.

This is the converse to the mean-value property in Evans, §2.2.2, Theorem 3, for continuous
rather than `C²` functions. Evans argues by contradiction from the formula
`φ'(r) = (r/n) ⨍_{B(x,r)} Δu` for the sphere average `φ`, which needs `C²` from the start; we
reuse LeanPDE's Poisson kernel and Mathlib's Tietze extension theorem instead.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.2, Theorem 3 (Converse to mean-value property) and its
  proof, p. 26.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

namespace LaplacianEquation

open MeasureTheory Set

/-- A continuous function with the sphere mean-value property on an open set
is harmonic in the classical PDE sense. -/
theorem HasSphereMeanValueProperty.isHarmonicPDE
    {n : ℕ} [Fact (0 < n)]
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : HasSphereMeanValueProperty n u U)
    (hU : IsOpen U) (hu_cont : ContinuousOn u U) :
    IsHarmonicPDE n u U := by
  classical
  have hlocal (x : ℝ^n) (hx : x ∈ U) : ContDiffAt ℝ 2 u x ∧ laplacian u x = 0 := by
    obtain ⟨r, hr, hclosed_x⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
    let v : ℝ^n → ℝ := fun z ↦ u (x + z)
    have htranslate : MapsTo (x + ·) (Metric.closedBall (0 : ℝ^n) r) (Metric.closedBall x r) :=
      fun z hz ↦ by simpa [dist_eq_norm] using hz
    have hv_cont : ContinuousOn v (Metric.closedBall (0 : ℝ^n) r) :=
      (hu_cont.mono hclosed_x).comp (by fun_prop) htranslate
    have hv_mean : HasSphereMeanValueProperty n v (Metric.ball (0 : ℝ^n) r) := by
      intro z hz ρ hρ hclosedρ
      have hclosedU : Metric.closedBall (x + z) ρ ⊆ U := fun y hy ↦ by
        have hyz : y - x ∈ Metric.closedBall z ρ := by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_sub, ← dist_eq_norm]
          exact hy
        exact hclosed_x (Metric.mem_closedBall.2
          ((dist_eq_norm y x).trans_le (mem_ball_zero_iff.1 (hclosedρ hyz)).le))
      calc v z = PDE.Analysis.sphereAverage n u (x + z) ρ :=
            hu.apply (hclosed_x (htranslate (Metric.ball_subset_closedBall hz))) hρ hclosedU
        _ = PDE.Analysis.sphereAverage n v z ρ := by
          rw [PDE.Analysis.sphereAverage_eq_unitSphereAverage v z ρ hρ,
            PDE.Analysis.sphereAverage_eq_unitSphereAverage u (x + z) ρ hρ]
          simp only [PDE.Analysis.unitSphereAverage, v, add_assoc]
    let vf : C(Metric.sphere (0 : ℝ^n) r, ℝ) :=
      ⟨fun z ↦ v z, continuousOn_iff_continuous_domRestrict.mp
        (hv_cont.mono Metric.sphere_subset_closedBall)⟩
    obtain ⟨g, hg_restrict⟩ := ContinuousMap.exists_restrict_eq Metric.isClosed_sphere vf
    let p : ℝ^n → ℝ := GreenFunction.poissonBallDirichletSolution (n := n) r g
    have hp_cont : ContinuousOn p (Metric.closedBall (0 : ℝ^n) r) :=
      GreenFunction.continuousOn_poissonBallDirichletSolution hr g.continuous.continuousOn
    have hp_harmonic : IsHarmonicPDE n p (Metric.ball (0 : ℝ^n) r) :=
      GreenFunction.poissonBallDirichletSolution_isHarmonicPDE hr g.continuous.continuousOn
    have hw_cont : ContinuousOn (v - p) (Metric.closedBall (0 : ℝ^n) r) := hv_cont.sub hp_cont
    have hw_mean := hv_mean.sub hp_harmonic.hasSphereMeanValueProperty
      (hv_cont.mono Metric.ball_subset_closedBall) (hp_cont.mono Metric.ball_subset_closedBall)
    have hw_boundary (z : ℝ^n) (hz : z ∈ Metric.sphere (0 : ℝ^n) r) : (v - p) z = 0 := by
      rw [Pi.sub_apply, sub_eq_zero,
        show v z = g z from (DFunLike.congr_fun hg_restrict ⟨z, hz⟩).symm]
      exact (GreenFunction.poissonBallDirichletSolution_eq_boundary g hz).symm
    have hv_eq_p : EqOn v p (Metric.closedBall (0 : ℝ^n) r) := fun z hz ↦ sub_eq_zero.1 <|
      le_antisymm (hw_mean.le_of_boundary_le hr hw_cont (fun z hz ↦ (hw_boundary z hz).le) z hz)
        (hw_mean.ge_of_boundary_ge hr hw_cont (fun z hz ↦ (hw_boundary z hz).ge) z hz)
    have h0 : (0 : ℝ^n) ∈ Metric.ball (0 : ℝ^n) r := Metric.mem_ball_self hr
    have heq : v =ᶠ[nhds (0 : ℝ^n)] p :=
      Filter.eventually_of_mem (Metric.closedBall_mem_nhds 0 hr) hv_eq_p
    have hv_reg : ContDiffAt ℝ 2 v (-x + x) := by
      simpa using (hp_harmonic.contDiffAt_of_isOpen Metric.isOpen_ball h0).congr_of_eventuallyEq heq
    have hu_reg : ContDiffAt ℝ 2 u x := by
      simpa [v, Function.comp_def] using
        hv_reg.comp x (by fun_prop : ContDiffAt ℝ 2 (fun y : ℝ^n ↦ -x + y) x)
    have hlap : laplacian v 0 = laplacian u x := by
      simpa [v] using PDE.laplacian_comp_add_left u x (0 : ℝ^n) (by simpa using hu_reg)
    exact ⟨hu_reg, hlap.symm.trans ((EuclideanLaplacian.laplacian_congr_nhds heq).trans
      (hp_harmonic.laplacian_eq_zero h0))⟩
  exact ⟨hU.contDiffOn_iff.mpr fun x hx ↦ (hlocal x hx).1, fun x hx ↦ (hlocal x hx).2⟩

end LaplacianEquation
