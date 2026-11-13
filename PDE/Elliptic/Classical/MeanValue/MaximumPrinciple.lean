/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MeanValue.Formulas
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Maximum principles from the sphere mean-value property

The maximum-principle argument uses only continuity and the sphere mean-value
property, not derivatives. If a continuous function bounded above by `M` has
spherical average `M`, positivity of Mathlib's sphere measure forces equality
on the whole sphere. The equality set of a function attaining a global
interior maximum is therefore open and closed in a connected domain.

The compact-ball boundary principle follows by applying this rigidity at a
maximizer. These results isolate the mean-value-theoretic part of Evans's proof of the strong
maximum principle (§2.2.3, Theorem 4).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.3, Theorem 4 (Strong maximum principle) and its proof,
  p. 27.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace LaplacianEquation

open MeasureTheory PDE.Analysis Set

/-- Rigidity of the spherical average at an upper bound. -/
theorem eqOn_sphere_of_sphereAverage_eq_of_le {n : ℕ} [Fact (0 < n)]
    {u : ℝ^n → ℝ} {x : ℝ^n}
    {r M : ℝ} (hr : 0 < r)
    (hu_cont : ContinuousOn u (Metric.sphere x r))
    (hu_le : ∀ y ∈ Metric.sphere x r, u y ≤ M)
    (havg : sphereAverage n u x r = M) :
    Set.EqOn u (fun _ ↦ M) (Metric.sphere x r) := by
  classical
  let μ : Measure (Metric.sphere (0 : ℝ^n) 1) := (volume : Measure (ℝ^n)).toSphere
  let p : Metric.sphere (0 : ℝ^n) 1 → ℝ^n := fun ω ↦ x + r • (ω : ℝ^n)
  have hp_sphere (ω : Metric.sphere (0 : ℝ^n) 1) : p ω ∈ Metric.sphere x r := by
    simp [p, norm_smul, abs_of_pos hr, mem_sphere_zero_iff_norm.mp ω.property]
  have hup_cont : Continuous fun ω ↦ u (p ω) := hu_cont.comp_continuous (by fun_prop) hp_sphere
  have hcs (f : Metric.sphere (0 : ℝ^n) 1 → ℝ) : HasCompactSupport f :=
    isCompact_univ.of_isClosed_subset isClosed_closure fun _ _ ↦ mem_univ _
  have hgap_integral : (∫ ω, M - u (p ω) ∂μ) = 0 := by
    rw [sphereAverage_eq_unitSphereAverage u x r hr] at havg
    have hup : (∫ ω, u (p ω) ∂μ) = M * unitSphereArea n :=
      (div_eq_iff unitSphereArea_pos.ne').mp (by simpa [unitSphereAverage, p, μ] using havg)
    rw [integral_sub (integrable_const M) (hup_cont.integrable_of_hasCompactSupport (hcs _)), hup]
    simp [μ, unitSphereArea, MeasureTheory.integral_const, MeasureTheory.measureReal_def,
      smul_eq_mul, mul_comm]
  intro y hy
  have hynorm : ‖y - x‖ = r := by simpa [dist_eq_norm] using hy
  let ω : Metric.sphere (0 : ℝ^n) 1 :=
    ⟨r⁻¹ • (y - x), by simp [norm_smul, hynorm, abs_of_pos hr, hr.ne']⟩
  have hpω : p ω = y := by simp only [p, ω, smul_smul, mul_inv_cancel₀ hr.ne', one_smul,
    add_sub_cancel]
  refine le_antisymm (hu_le y hy) (le_of_not_gt fun hlt ↦ ?_)
  have hpos : 0 < ∫ z, M - u (p z) ∂μ :=
    (continuous_const.sub hup_cont).integral_pos_of_hasCompactSupport_nonneg_nonzero (hcs _)
      (fun ω ↦ sub_nonneg.mpr (hu_le _ (hp_sphere ω))) (x := ω) (by rw [hpω]; linarith)
  exact hpos.ne' hgap_integral

/-- Strong maximum principle for a continuous function with the sphere mean-value property. -/
theorem HasSphereMeanValueProperty.eqOn_const_of_isPreconnected_of_forall_le
    {n : ℕ} [Fact (0 < n)]
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : HasSphereMeanValueProperty n u U)
    (hu_cont : ContinuousOn u U)
    (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    {x₀ : ℝ^n} (hx₀ : x₀ ∈ U)
    (hmax : ∀ y ∈ U, u y ≤ u x₀) :
    Set.EqOn u (fun _ ↦ u x₀) U := by
  classical
  let A : Set U := {z | u z = u x₀}
  have hA_open : IsOpen A := by
    refine isOpen_iff_mem_nhds.2 fun z hzA ↦ ?_
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds z.property)
    refine Filter.mem_of_superset (Metric.ball_mem_nhds z hε) fun y hy ↦ ?_
    change u y = u x₀
    rcases eq_or_ne (y : ℝ^n) z with hyz | hyz
    · rw [hyz]
      exact hzA
    have hρ : 0 < dist (z : ℝ^n) y := dist_pos.2 hyz.symm
    have hclosedρ : Metric.closedBall (z : ℝ^n) (dist (z : ℝ^n) y) ⊆ U :=
      (Metric.closedBall_subset_ball (by rw [dist_comm]; exact hy)).trans hεU
    exact eqOn_sphere_of_sphereAverage_eq_of_le hρ
      (hu_cont.mono (Metric.sphere_subset_closedBall.trans hclosedρ))
      (fun q hq ↦ hmax q (hclosedρ (Metric.sphere_subset_closedBall hq)))
      ((hu.apply z.property hρ hclosedρ).symm.trans hzA) (Metric.mem_sphere.2 (dist_comm _ _))
  have : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hUconn
  have hA_univ : A = univ := IsClopen.eq_univ ⟨isClosed_eq
    (continuousOn_iff_continuous_domRestrict.mp hu_cont) continuous_const, hA_open⟩ ⟨⟨x₀, hx₀⟩, rfl⟩
  exact fun y hy ↦ Set.eq_univ_iff_forall.1 hA_univ ⟨y, hy⟩

/-- Strong minimum principle for a continuous function with the sphere mean-value property. -/
theorem HasSphereMeanValueProperty.eqOn_const_of_isPreconnected_of_forall_ge
    {n : ℕ} [Fact (0 < n)]
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : HasSphereMeanValueProperty n u U)
    (hu_cont : ContinuousOn u U)
    (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    {x₀ : ℝ^n} (hx₀ : x₀ ∈ U)
    (hmin : ∀ y ∈ U, u x₀ ≤ u y) :
    Set.EqOn u (fun _ ↦ u x₀) U := by
  have hneg :=
    hu.neg.eqOn_const_of_isPreconnected_of_forall_le hu_cont.neg
      hUopen hUconn hx₀ (fun y hy ↦ neg_le_neg (hmin y hy))
  intro y hy
  have := hneg hy
  simpa using neg_injective this

/-- Boundary maximum principle on a Euclidean ball for a continuous function with the sphere
mean-value property. -/
theorem HasSphereMeanValueProperty.le_of_boundary_le {n : ℕ} [Fact (0 < n)]
    {u : ℝ^n → ℝ} {c : ℝ^n}
    {r M : ℝ}
    (hu : HasSphereMeanValueProperty n u (Metric.ball c r))
    (hr : 0 < r)
    (hu_cont : ContinuousOn u (Metric.closedBall c r))
    (hu_boundary : ∀ x ∈ Metric.sphere c r, u x ≤ M) :
    ∀ x ∈ Metric.closedBall c r, u x ≤ M := by
  classical
  intro x hx
  obtain ⟨z, hzclosed, hzmax⟩ :=
    (isCompact_closedBall c r).exists_isMaxOn ⟨c, Metric.mem_closedBall_self hr.le⟩ hu_cont
  refine (hzmax hx).trans ?_
  by_cases hzsphere : z ∈ Metric.sphere c r
  · exact hu_boundary z hzsphere
  have hconst := (hu.eqOn_const_of_isPreconnected_of_forall_le
    (hu_cont.mono Metric.ball_subset_closedBall) Metric.isOpen_ball Metric.isPreconnected_ball
    (Metric.mem_ball.2 (lt_of_le_of_ne hzclosed hzsphere))
    fun y hy ↦ hzmax (Metric.ball_subset_closedBall hy)).of_subset_closure hu_cont
      continuousOn_const Metric.ball_subset_closedBall (by rw [closure_ball c hr.ne'])
  have : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  obtain ⟨b, hb⟩ : (Metric.sphere c r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  exact (hconst (Metric.sphere_subset_closedBall hb)).symm.le.trans (hu_boundary b hb)

/-- Boundary minimum principle on a Euclidean ball for a continuous function with the sphere
mean-value property. -/
theorem HasSphereMeanValueProperty.ge_of_boundary_ge {n : ℕ} [Fact (0 < n)]
    {u : ℝ^n → ℝ} {c : ℝ^n}
    {r m : ℝ}
    (hu : HasSphereMeanValueProperty n u (Metric.ball c r))
    (hr : 0 < r)
    (hu_cont : ContinuousOn u (Metric.closedBall c r))
    (hu_boundary : ∀ x ∈ Metric.sphere c r, m ≤ u x) :
    ∀ x ∈ Metric.closedBall c r, m ≤ u x := by
  intro x hx
  have hneg :=
    hu.neg.le_of_boundary_le hr hu_cont.neg
      (fun y hy ↦ neg_le_neg (hu_boundary y hy)) x hx
  simpa using neg_le_neg hneg

end LaplacianEquation
