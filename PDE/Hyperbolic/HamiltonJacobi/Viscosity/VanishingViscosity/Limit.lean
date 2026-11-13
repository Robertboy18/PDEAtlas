/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.ContactStability.VanishingPerturbation
public import PDE.Analysis.Calculus.Laplacian.Slices
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.VanishingViscosity.Classical
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.SmoothTests

/-!
# Vanishing viscosity for Hamilton–Jacobi equations

Let `uₙ` solve `∂ₜuₙ + H(∇uₙ, x) = εₙ Δuₙ`, where `εₙ ≥ 0` tends to zero.
A locally uniform limit is a viscosity solution of the first-order equation.
The Hamiltonian may depend on position and need only be continuous.

The key estimate differentiates a fixed smooth touching test, not the sequence
of solutions. Its Laplacian stays bounded near the contact, so multiplication
by `εₙ` removes the viscous term even when the solution derivatives grow.
Nearby smooth contacts then recover all locally `C¹` tests in our definition.
The approximants need a joint first derivative and `C²` spatial slices.

This is the argument (5)-(15) with which Evans motivates the definition of viscosity solution in
§10.1.1, for the regularized equation (2) of §10.1 and the locally uniform limit (3). Evans takes
`ε > 0` and smooth solutions of (2); we allow `εₙ ≥ 0` and less regular approximants.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.1, equations (2)-(3); §10.1.1, (5)-(15).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Gradient Laplacian ContDiff Topology

namespace HamiltonJacobi

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Locally uniform limits of classical viscous subsolutions satisfy the
first-order viscosity inequality. -/
theorem isSpatialViscositySubsolution_of_vanishing_viscosity {H : E → E → ℝ} {U : Set (E × ℝ)}
    (hU : IsOpen U) {v : ℕ → E × ℝ → ℝ} {u : E × ℝ → ℝ} {ε : ℕ → ℝ}
    (hH : Continuous (fun q : E × E ↦ H q.1 q.2)) (hv : ∀ n, DifferentiableOn ℝ (v n) U)
    (hspace : ∀ n z, z ∈ U → ContDiffAt ℝ 2 (fun x ↦ v n (x, z.2)) z.1)
    (hvu : TendstoLocallyUniformlyOn v u atTop U) (hεnonneg : ∀ n, 0 ≤ ε n)
    (hε : Tendsto ε atTop (𝓝 0))
    (hresidual : ∀ n z, z ∈ U → fderiv ℝ (v n) z (0, 1) + H (∇ (fun x ↦ v n (x, z.2)) z.1) z.1 ≤
      ε n * Δ (fun x ↦ v n (x, z.2)) z.1) :
    IsSpatialViscositySubsolution H U u := by
  have hu : ContinuousOn u U :=
    hvu.continuousOn (Frequently.of_forall (fun n ↦ (hv n).continuousOn))
  refine ⟨hU, fun z hz φ hφ hcontact ↦ ?_⟩
  have hd := hφ.differentiableAt_one
  have h := PDE.Analysis.le_zero_of_contDiff_upper_contacts
    (Q := quadraticSize (E := E)) contDiff_quadraticSize
    (by simp [quadraticSize]) norm_sq_le_quadraticSize
    (B := 4) norm_fderiv_quadraticSize_le
    hU hu.upperSemicontinuousOn hz hd.hasFDerivAt hcontact
    (continuous_spatialJetOperator hH).continuousAt
    (fun y hy ψ hψ hupper ↦ by
      apply PDE.Analysis.le_zero_of_vanishing_perturbation_at_upper_contacts
        (Q := quadraticSize (E := E)) contDiff_quadraticSize
        (by simp [quadraticSize]) norm_sq_le_quadraticSize hU
        (fun n ↦ (hv n).continuousOn.upperSemicontinuousOn) hvu hε hy hψ hupper
        (continuous_spatialJetOperator hH).continuousAt (G := fun θ w ↦ Δ (fun x ↦ θ (x, w.2)) w.1)
      · exact fun θ hθ ↦ (PDE.contDiff_laplacian_prod_firstSlice (m := 0)
          (hθ.of_le (by simp))).continuous
      · intro n w hw θ hθ hmax
        have hdv := (hv n w hw).differentiableAt (hU.mem_nhds hw)
        apply spatialJetOperator_le_mul_laplacian_of_upper_contact
          (hεnonneg n) hdv (hspace n w hw) (hθ.contDiffAt.of_le (by simp))
          (hmax.isLocalMax (hU.mem_nhds hw))
        simpa only [spatialJetOperator_fderiv hdv] using hresidual n w hw)
  simpa only [spatialJetOperator_fderiv hd] using h

/-- The corresponding limit theorem for classical viscous supersolutions. -/
theorem isSpatialViscositySupersolution_of_vanishing_viscosity {H : E → E → ℝ} {U : Set (E × ℝ)}
    (hU : IsOpen U) {v : ℕ → E × ℝ → ℝ} {u : E × ℝ → ℝ} {ε : ℕ → ℝ}
    (hH : Continuous (fun q : E × E ↦ H q.1 q.2)) (hv : ∀ n, DifferentiableOn ℝ (v n) U)
    (hspace : ∀ n z, z ∈ U → ContDiffAt ℝ 2 (fun x ↦ v n (x, z.2)) z.1)
    (hvu : TendstoLocallyUniformlyOn v u atTop U) (hεnonneg : ∀ n, 0 ≤ ε n)
    (hε : Tendsto ε atTop (𝓝 0))
    (hresidual : ∀ n z, z ∈ U → ε n * Δ (fun x ↦ v n (x, z.2)) z.1 ≤
      fderiv ℝ (v n) z (0, 1) + H (∇ (fun x ↦ v n (x, z.2)) z.1) z.1) :
    IsSpatialViscositySupersolution H U u := by
  have hu : ContinuousOn u U :=
    hvu.continuousOn (Frequently.of_forall (fun n ↦ (hv n).continuousOn))
  refine ⟨hU, fun z hz φ hφ hcontact ↦ ?_⟩
  have hd := hφ.differentiableAt_one
  have h := PDE.Analysis.zero_le_of_contDiff_lower_contacts
    (Q := quadraticSize (E := E)) contDiff_quadraticSize
    (by simp [quadraticSize]) norm_sq_le_quadraticSize
    (B := 4) norm_fderiv_quadraticSize_le
    hU hu.lowerSemicontinuousOn hz hd.hasFDerivAt hcontact
    (continuous_spatialJetOperator hH).continuousAt
    (fun y hy ψ hψ hlower ↦ by
      apply PDE.Analysis.zero_le_of_vanishing_perturbation_at_lower_contacts
        (Q := quadraticSize (E := E)) contDiff_quadraticSize
        (by simp [quadraticSize]) norm_sq_le_quadraticSize hU
        (fun n ↦ (hv n).continuousOn.lowerSemicontinuousOn) hvu hε hy hψ hlower
        (continuous_spatialJetOperator hH).continuousAt (G := fun θ w ↦ Δ (fun x ↦ θ (x, w.2)) w.1)
      · exact fun θ hθ ↦ (PDE.contDiff_laplacian_prod_firstSlice (m := 0)
          (hθ.of_le (by simp))).continuous
      · intro n w hw θ hθ hmin
        have hdv := (hv n w hw).differentiableAt (hU.mem_nhds hw)
        apply mul_laplacian_le_spatialJetOperator_of_lower_contact
          (hεnonneg n) hdv (hspace n w hw) (hθ.contDiffAt.of_le (by simp))
          (hmin.isLocalMin (hU.mem_nhds hw))
        simpa only [spatialJetOperator_fderiv hdv] using hresidual n w hw)
  simpa only [spatialJetOperator_fderiv hd] using h

/-- A locally uniform limit of classical solutions with vanishing nonnegative
viscosity solves `u_t + H(∇u, x) = 0` in the viscosity sense. The conclusion
uses all locally `C¹` tests, with no convexity or derivative-convergence hypothesis. -/
theorem isSpatialViscositySolution_of_vanishing_viscosity {H : E → E → ℝ} {U : Set (E × ℝ)}
    (hU : IsOpen U) {v : ℕ → E × ℝ → ℝ} {u : E × ℝ → ℝ} {ε : ℕ → ℝ}
    (hH : Continuous (fun q : E × E ↦ H q.1 q.2)) (hv : ∀ n, DifferentiableOn ℝ (v n) U)
    (hspace : ∀ n z, z ∈ U → ContDiffAt ℝ 2 (fun x ↦ v n (x, z.2)) z.1)
    (hvu : TendstoLocallyUniformlyOn v u atTop U) (hεnonneg : ∀ n, 0 ≤ ε n)
    (hε : Tendsto ε atTop (𝓝 0))
    (hresidual : ∀ n z, z ∈ U → fderiv ℝ (v n) z (0, 1) + H (∇ (fun x ↦ v n (x, z.2)) z.1) z.1 =
      ε n * Δ (fun x ↦ v n (x, z.2)) z.1) :
    IsSpatialViscositySolution H U u :=
  ⟨isSpatialViscositySubsolution_of_vanishing_viscosity hU hH hv hspace hvu hεnonneg hε
      (fun n z hz ↦ (hresidual n z hz).le),
    isSpatialViscositySupersolution_of_vanishing_viscosity hU hH hv hspace hvu hεnonneg hε
      (fun n z hz ↦ (hresidual n z hz).ge)⟩

end HamiltonJacobi
