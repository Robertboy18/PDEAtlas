/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.SmoothTests
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Consistency at a differentiability point

A viscosity solution of `u_t + H(Dₓu, x) = 0` satisfies the equation at every
point where its joint derivative exists. Only differentiability at that point
is required. Nearby smooth contacts and continuity of the Hamiltonian supply
the two inequalities; the solution itself need not be an admissible smooth test.

This is Evans, §10.1.2, Theorem 1, on any open spacetime domain.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.1.2, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace HamiltonJacobi

open Set
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- An upper semicontinuous viscosity subsolution satisfies the classical
inequality at each point of joint differentiability. -/
theorem IsSpatialViscositySubsolution.le_zero_of_differentiableAt {H : E → E → ℝ} {U : Set (E × ℝ)}
    {u : E × ℝ → ℝ} {z : E × ℝ} (hsub : IsSpatialViscositySubsolution H U u)
    (hu : UpperSemicontinuousOn u U) (hH : Continuous (fun q : E × E ↦ H q.1 q.2)) (hz : z ∈ U)
    (hd : DifferentiableAt ℝ u z) :
    fderiv ℝ u z (0, 1) + H (∇ (fun x ↦ u (x, z.2)) z.1) z.1 ≤ 0 := by
  have hmax : IsLocalMaxOn (fun y ↦ u y - u y) U z := by
    simpa only [sub_self] using isLocalMaxOn_const (s := U) (a := z) (b := (0 : ℝ))
  have h := PDE.Analysis.le_zero_of_contDiff_upper_contacts
    (Q := quadraticSize (E := E)) contDiff_quadraticSize
    (by simp [quadraticSize]) norm_sq_le_quadraticSize
    (B := 4) norm_fderiv_quadraticSize_le hsub.1 hu hz
    hd.hasFDerivAt hmax (continuous_spatialJetOperator hH).continuousAt
    (fun y hy φ hφ hcontact ↦ by
      rw [spatialJetOperator_fderiv ((hφ.differentiable (by simp)) y)]
      exact hsub.2 y hy φ (hφ.contDiffAt.of_le (by simp)) hcontact)
  simpa only [spatialJetOperator_fderiv hd] using h

/-- A lower semicontinuous viscosity supersolution satisfies the classical
inequality at each point of joint differentiability. -/
theorem IsSpatialViscositySupersolution.zero_le_of_differentiableAt {H : E → E → ℝ}
    {U : Set (E × ℝ)} {u : E × ℝ → ℝ} {z : E × ℝ} (hsuper : IsSpatialViscositySupersolution H U u)
    (hu : LowerSemicontinuousOn u U) (hH : Continuous (fun q : E × E ↦ H q.1 q.2)) (hz : z ∈ U)
    (hd : DifferentiableAt ℝ u z) :
    0 ≤ fderiv ℝ u z (0, 1) + H (∇ (fun x ↦ u (x, z.2)) z.1) z.1 := by
  have hmin : IsLocalMinOn (fun y ↦ u y - u y) U z := by
    simpa only [sub_self] using isLocalMinOn_const (s := U) (a := z) (b := (0 : ℝ))
  have h := PDE.Analysis.zero_le_of_contDiff_lower_contacts
    (Q := quadraticSize (E := E)) contDiff_quadraticSize
    (by simp [quadraticSize]) norm_sq_le_quadraticSize
    (B := 4) norm_fderiv_quadraticSize_le hsuper.1 hu hz
    hd.hasFDerivAt hmin (continuous_spatialJetOperator hH).continuousAt
    (fun y hy φ hφ hcontact ↦ by
      rw [spatialJetOperator_fderiv ((hφ.differentiable (by simp)) y)]
      exact hsuper.2 y hy φ (hφ.contDiffAt.of_le (by simp)) hcontact)
  simpa only [spatialJetOperator_fderiv hd] using h

/-- At a joint differentiability point, a continuous viscosity solution
satisfies the PDE with its time derivative and spatial gradient. -/
theorem IsSpatialViscositySolution.eq_zero_of_differentiableAt {H : E → E → ℝ} {U : Set (E × ℝ)}
    {u : E × ℝ → ℝ} {z : E × ℝ} (hsol : IsSpatialViscositySolution H U u) (hu : ContinuousOn u U)
    (hH : Continuous (fun q : E × E ↦ H q.1 q.2)) (hz : z ∈ U) (hd : DifferentiableAt ℝ u z) :
    deriv (fun t ↦ u (z.1, t)) z.2 + H (∇ (fun x ↦ u (x, z.2)) z.1) z.1 = 0 := by
  have htime : HasDerivAt (fun t ↦ u (z.1, t)) (fderiv ℝ u z (0, 1)) z.2 :=
    hd.hasFDerivAt.comp_hasDerivAt z.2 ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
  rw [htime.deriv]
  exact le_antisymm (hsol.1.le_zero_of_differentiableAt hu.upperSemicontinuousOn hH hz hd)
    (hsol.2.zero_le_of_differentiableAt hu.lowerSemicontinuousOn hH hz hd)

/-- The smooth-test convention on the forward half-space gives pointwise
consistency under mere joint differentiability, as in Evans's definition. -/
theorem eq_zero_of_differentiableAt_of_smooth_tests {H : E → E → ℝ} {u : E × ℝ → ℝ} {z : E × ℝ}
    (hu : ContinuousOn u positiveTimeDomain) (hH : Continuous (fun q : E × E ↦ H q.1 q.2))
    (hsub : ∀ y ∈ positiveTimeDomain, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ positiveTimeDomain →
      IsLocalMaxOn (fun w ↦ u w - φ w) positiveTimeDomain y →
      fderiv ℝ φ y (0, 1) + H (∇ (fun x ↦ φ (x, y.2)) y.1) y.1 ≤ 0)
    (hsuper : ∀ y ∈ positiveTimeDomain, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ positiveTimeDomain →
      IsLocalMinOn (fun w ↦ u w - φ w) positiveTimeDomain y → 0 ≤
      fderiv ℝ φ y (0, 1) + H (∇ (fun x ↦ φ (x, y.2)) y.1) y.1)
    (hz : 0 < z.2) (hd : DifferentiableAt ℝ u z) :
    deriv (fun t ↦ u (z.1, t)) z.2 + H (∇ (fun x ↦ u (x, z.2)) z.1) z.1 = 0 := by
  have hsol : IsSpatialViscositySolution H positiveTimeDomain u :=
    ⟨(isSpatialViscositySubsolution_iff_smooth_tests isOpen_positiveTimeDomain
      hu.upperSemicontinuousOn hH).2 hsub,
      (isSpatialViscositySupersolution_iff_smooth_tests isOpen_positiveTimeDomain
        hu.lowerSemicontinuousOn hH).2 hsuper⟩
  exact hsol.eq_zero_of_differentiableAt hu hH hz hd

/-- The viscosity IVP class satisfies the classical PDE at every
positive-time point of joint differentiability. Continuity is derived from
the uniform continuity already required on finite closed slabs. -/
theorem IsViscosityInitialSolution.eq_zero_of_differentiableAt {H : E → E → ℝ} {g : E → ℝ}
    {u : E × ℝ → ℝ} {z : E × ℝ} (hsol : IsViscosityInitialSolution H g u)
    (hH : Continuous (fun q : E × E ↦ H q.1 q.2)) (hz : 0 < z.2) (hd : DifferentiableAt ℝ u z) :
    deriv (fun t ↦ u (z.1, t)) z.2 + H (∇ (fun x ↦ u (x, z.2)) z.1) z.1 = 0 := by
  have hu : ContinuousOn u positiveTimeDomain := by
    intro y hy
    have hlt : y.2 < y.2 + 1 := lt_add_one _
    have hT : 0 < y.2 + 1 := lt_trans hy hlt
    have hslab : closedTimeSlab (E := E) (y.2 + 1) ∈ 𝓝 y :=
      continuous_snd.continuousAt.preimage_mem_nhds (Icc_mem_nhds hy hlt)
    exact (((hsol.1 _ hT).2.continuousOn y ⟨hy.le, hlt.le⟩).continuousAt hslab).continuousWithinAt
  exact hsol.2.1.eq_zero_of_differentiableAt hu hH hz hd

end HamiltonJacobi
