/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.ContactStability
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.JetOperator
import PDE.Hyperbolic.HamiltonJacobi.Viscosity.QuadraticBarrier
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Locally uniform stability of Hamilton–Jacobi solutions

Let `H(p,x)` be continuous in momentum and position. A locally uniform limit
of upper semicontinuous subsolutions on an open spacetime domain is a
subsolution there. The analogous statement holds for lower semicontinuous
supersolutions. In particular, a locally uniform limit of continuous
solutions satisfies both of the local `C¹` touching-test inequalities.

The proof uses nearby contacts of the approximants, obtained by a
quadratic penalty and compact maximization. Finite dimensionality supplies
the compact balls.

The final theorem applies this argument to differentiable functions whose
classical PDE residuals tend uniformly to zero. It proves the viscosity
inequalities for their locally uniform limit.

The statement for solutions is Problem 2 of Evans, §10.4, with locally uniform convergence.
The nearby contacts are found as in (5)-(7) and (13) of the motivation in §10.1.1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.4, Problem 2; §10.1.1, (5)-(7) and (13).
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace HamiltonJacobi

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A locally uniform limit of upper semicontinuous subsolutions is a
subsolution for a Hamiltonian continuous in both momentum and position. -/
theorem isSpatialViscositySubsolution_of_tendstoLocallyUniformlyOn {H : E → E → ℝ} {U : Set (E × ℝ)}
    {v : ℕ → E × ℝ → ℝ} {u : E × ℝ → ℝ} (hH : Continuous (fun q : E × E ↦ H q.1 q.2))
    (hv : ∀ n, UpperSemicontinuousOn (v n) U) (hsub : ∀ n, IsSpatialViscositySubsolution H U (v n))
    (hvu : TendstoLocallyUniformlyOn v u atTop U) :
    IsSpatialViscositySubsolution H U u := by
  refine ⟨(hsub 0).1, fun z hz φ hφ hcontact ↦ ?_⟩
  have h := PDE.Analysis.le_zero_of_tendstoLocallyUniformlyOn_upper_contacts
    (Q := quadraticSize (E := E)) contDiff_quadraticSize
    (by simp [quadraticSize]) norm_sq_le_quadraticSize
    (hsub 0).1 hv hvu (ε := fun _ ↦ 0) tendsto_const_nhds hz hφ hcontact
    (continuous_spatialJetOperator hH).continuousAt
    (fun n y hy ψ hψ hmax ↦ by
      rw [spatialJetOperator_fderiv hψ.differentiableAt_one]
      exact (hsub n).2 y hy ψ hψ hmax)
  simpa only [spatialJetOperator_fderiv hφ.differentiableAt_one] using h

/-- A locally uniform limit of lower semicontinuous supersolutions is a
supersolution for a Hamiltonian continuous in both momentum and position. -/
theorem isSpatialViscositySupersolution_of_tendstoLocallyUniformlyOn {H : E → E → ℝ}
    {U : Set (E × ℝ)} {v : ℕ → E × ℝ → ℝ} {u : E × ℝ → ℝ}
    (hH : Continuous (fun q : E × E ↦ H q.1 q.2)) (hv : ∀ n, LowerSemicontinuousOn (v n) U)
    (hsuper : ∀ n, IsSpatialViscositySupersolution H U (v n))
    (hvu : TendstoLocallyUniformlyOn v u atTop U) :
    IsSpatialViscositySupersolution H U u := by
  refine ⟨(hsuper 0).1, fun z hz φ hφ hcontact ↦ ?_⟩
  have h := PDE.Analysis.zero_le_of_tendstoLocallyUniformlyOn_lower_contacts
    (Q := quadraticSize (E := E)) contDiff_quadraticSize
    (by simp [quadraticSize]) norm_sq_le_quadraticSize
    (hsuper 0).1 hv hvu (ε := fun _ ↦ 0) tendsto_const_nhds hz hφ hcontact
    (continuous_spatialJetOperator hH).continuousAt
    (fun n y hy ψ hψ hmin ↦ by
      rw [spatialJetOperator_fderiv hψ.differentiableAt_one]
      simpa only [neg_zero] using (hsuper n).2 y hy ψ hψ hmin)
  simpa only [spatialJetOperator_fderiv hφ.differentiableAt_one] using h

/-- A locally uniform limit of continuous spatial viscosity solutions
satisfies the same local `C¹` subsolution and supersolution predicates.
Continuity of the approximants supplies both semicontinuity hypotheses. -/
theorem isSpatialViscositySolution_of_tendstoLocallyUniformlyOn {H : E → E → ℝ} {U : Set (E × ℝ)}
    {v : ℕ → E × ℝ → ℝ} {u : E × ℝ → ℝ} (hH : Continuous (fun q : E × E ↦ H q.1 q.2))
    (hv : ∀ n, ContinuousOn (v n) U) (hsolution : ∀ n, IsSpatialViscositySolution H U (v n))
    (hvu : TendstoLocallyUniformlyOn v u atTop U) :
    IsSpatialViscositySolution H U u :=
  ⟨isSpatialViscositySubsolution_of_tendstoLocallyUniformlyOn hH
      (fun n ↦ (hv n).upperSemicontinuousOn) (fun n ↦ (hsolution n).1) hvu,
    isSpatialViscositySupersolution_of_tendstoLocallyUniformlyOn hH
      (fun n ↦ (hv n).lowerSemicontinuousOn) (fun n ↦ (hsolution n).2) hvu⟩

/-- Differentiable approximate solutions with residuals bounded by a scalar
sequence tending to zero have viscosity-solution locally uniform limits.
The residual uses the spacetime derivative and fixed-time spatial
gradient. Differentiability of the approximants on the open domain suffices. -/
theorem isSpatialViscositySolution_of_tendstoLocallyUniformlyOn_residual {H : E → E → ℝ}
    {U : Set (E × ℝ)} (hU : IsOpen U) {v : ℕ → E × ℝ → ℝ} {u : E × ℝ → ℝ} {ε : ℕ → ℝ}
    (hH : Continuous (fun q : E × E ↦ H q.1 q.2)) (hv : ∀ n, DifferentiableOn ℝ (v n) U)
    (hvu : TendstoLocallyUniformlyOn v u atTop U) (hε : Tendsto ε atTop (𝓝 0))
    (hresidual : ∀ n z, z ∈ U → |fderiv ℝ (v n) z (0, 1) + H (∇ (fun x ↦ v n (x, z.2)) z.1) z.1| ≤
      ε n) :
    IsSpatialViscositySolution H U u := by
  constructor
  · refine ⟨hU, fun z hz φ hφ hcontact ↦ ?_⟩
    have h := PDE.Analysis.le_zero_of_tendstoLocallyUniformlyOn_upper_contacts
      (Q := quadraticSize (E := E)) contDiff_quadraticSize
      (by simp [quadraticSize]) norm_sq_le_quadraticSize
      hU (fun n ↦ (hv n).continuousOn.upperSemicontinuousOn) hvu hε hz hφ hcontact
      (continuous_spatialJetOperator hH).continuousAt
      (fun n y hy ψ hψ hmax ↦ by
        have hdv := (hv n y hy).differentiableAt (hU.mem_nhds hy)
        have hzero := (hmax.isLocalMax (hU.mem_nhds hy)).hasFDerivAt_eq_zero
          (hdv.hasFDerivAt.sub hψ.differentiableAt_one.hasFDerivAt)
        have heq : fderiv ℝ (v n) y = fderiv ℝ ψ y := sub_eq_zero.mp hzero
        rw [← heq, spatialJetOperator_fderiv hdv]
        exact (abs_le.mp (hresidual n y hy)).2)
    simpa only [spatialJetOperator_fderiv hφ.differentiableAt_one] using h
  · refine ⟨hU, fun z hz φ hφ hcontact ↦ ?_⟩
    have h := PDE.Analysis.zero_le_of_tendstoLocallyUniformlyOn_lower_contacts
      (Q := quadraticSize (E := E)) contDiff_quadraticSize
      (by simp [quadraticSize]) norm_sq_le_quadraticSize
      hU (fun n ↦ (hv n).continuousOn.lowerSemicontinuousOn) hvu hε hz hφ hcontact
      (continuous_spatialJetOperator hH).continuousAt
      (fun n y hy ψ hψ hmin ↦ by
        have hdv := (hv n y hy).differentiableAt (hU.mem_nhds hy)
        have hzero := (hmin.isLocalMin (hU.mem_nhds hy)).hasFDerivAt_eq_zero
          (hdv.hasFDerivAt.sub hψ.differentiableAt_one.hasFDerivAt)
        have heq : fderiv ℝ (v n) y = fderiv ℝ ψ y := sub_eq_zero.mp hzero
        rw [← heq, spatialJetOperator_fderiv hdv]
        exact (abs_le.mp (hresidual n y hy)).1)
    simpa only [spatialJetOperator_fderiv hφ.differentiableAt_one] using h

end HamiltonJacobi

end
