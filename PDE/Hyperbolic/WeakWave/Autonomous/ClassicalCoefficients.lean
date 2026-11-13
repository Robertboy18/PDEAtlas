/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.Autonomous.SobolevCoefficients
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData

/-!
# Energy bounds from classical autonomous wave coefficients

Classical coefficient fields on the closure of a bounded open domain determine the
full divergence form, including drift and potential. Their Sobolev classes and all
bounds needed for existence, uniqueness and the energy estimate are derived here.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The full divergence form of classical autonomous coefficient fields. -/
def classicalAutonomousWaveForm
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    {A : ℝ^n → Fin n → Fin n → ℝ} {B : Fin n → ℝ^n → ℝ} {C : ℝ^n → ℝ}
    (hA : ∀ i j, ContDiffUpToBoundary 1 (fun x ↦ A x i j) Ω)
    (hB : ∀ i, ContDiffUpToBoundary 1 (B i) Ω) (hC : ContDiffUpToBoundary 0 C Ω) :
    H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
  fullDivergenceForm (multiplicationCoefficientOperator
    (fun i j ↦ (hA i j).toLp hΩ hbounded ∞))
    (fun i ↦ mulLpLeft ((hB i).toLp hΩ hbounded ∞))
    (mulLpLeft (hC.toLp hΩ hbounded ∞))

/-- Pointwise symmetry and uniform ellipticity pass to the canonical coefficient
classes; no representative identity is added as a hypothesis. -/
theorem classical_coefficients_ae_symmetric_elliptic (hΩ : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) {A : ℝ^n → Fin n → Fin n → ℝ}
    (hA : ∀ i j, ContDiffUpToBoundary 1 (fun x ↦ A x i j) Ω)
    (hsymm : ∀ x ∈ Ω, ∀ i j, A x i j = A x j i) {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ, alpha * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, A x i j * ξ j * ξ i) :
    AESymmetricCoefficient (fun i j ↦ (hA i j).toLp hΩ hbounded ∞) ∧
      AEUniformlyElliptic (fun i j ↦ (hA i j).toLp hΩ hbounded ∞) alpha := by
  have hrep : ∀ᵐ x ∂domainMeasure n Ω, ∀ i j, (hA i j).toLp hΩ hbounded ∞ x = A x i j :=
    ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦ (hA i j).toLp_coeFn hΩ hbounded ∞
  constructor
  · intro i j
    filter_upwards [hrep, ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
    rw [hx i j, hx j i]
    exact hsymm x hxΩ i j
  · refine ⟨halpha, ?_⟩
    filter_upwards [hrep, ae_restrict_mem hΩ.measurableSet] with x hx hxΩ ξ
    simpa only [hx] using hell x hxΩ ξ

/-- Every weak solution satisfies the full energy estimate for classical autonomous
coefficients on a bounded open domain. The constant is fixed before the forcing and
initial data; existence and both initial traces are included. -/
theorem exists_uniform_energy_bound_of_classical_autonomous_coefficients (hn : 0 < n)
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) {a b : ℝ} (hab : a < b)
    {A : ℝ^n → Fin n → Fin n → ℝ} {B : Fin n → ℝ^n → ℝ} {C : ℝ^n → ℝ}
    (hA : ∀ i j, ContDiffUpToBoundary 1 (fun x ↦ A x i j) Ω)
    (hB : ∀ i, ContDiffUpToBoundary 1 (B i) Ω) (hC : ContDiffUpToBoundary 0 C Ω)
    (hsymm : ∀ x ∈ Ω, ∀ i j, A x i j = A x j i) {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ, alpha * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, A x i j * ξ j * ξ i) :
    let T := h10L2GelfandTriple hΩ
    let F := classicalAutonomousWaveForm hΩ hbounded hA hB hC
    ∃ M : ℝ, 0 < M ∧
      ∀ (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
        (g : H¹₀(Ω)) (h : DerivLp n 2 Ω),
      (∃ u v w, Hyperbolic.Variational.IsGelfandWeakWaveSolution T (fun _ ↦ F)
        (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f) u v w g h) ∧
      ∀ u v w, Hyperbolic.Variational.IsGelfandWeakWaveSolution T (fun _ ↦ F)
        (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f) u v w g h →
        MemLp (fun t ↦ u t) ∞ (volume.restrict (Ioc a b)) ∧
        MemLp (fun t ↦ v t) ∞ (volume.restrict (Ioc a b)) ∧
        ∀ᵐ t ∂volume.restrict (Ioc a b),
          ‖u t‖ + ‖v t‖ ≤ M * (‖f‖ + ‖g‖ + ‖h‖) := by
  obtain ⟨hAs, hAe⟩ := classical_coefficients_ae_symmetric_elliptic hΩ hbounded hA hsymm halpha hell
  simpa only [classicalAutonomousWaveForm, ContDiffUpToBoundary.toWkpSpaceOn_base_eq_toLp] using
    exists_uniform_energy_bound_of_autonomous_sobolev_coefficients hn hΩ hbounded hab
      (fun i j ↦ (hA i j).toLp hΩ hbounded ∞)
      (fun i ↦ (hB i).toWkpSpaceOn hΩ hbounded ∞) (hC.toLp hΩ hbounded ∞) hAs hAe

/-- Classical autonomous coefficients give uniqueness in the original weak class,
without assuming any of the improved regularity conclusions. -/
theorem weakWave_eq_of_classical_autonomous_coefficients (hn : 0 < n) (hΩ : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) {a b : ℝ} {A : ℝ^n → Fin n → Fin n → ℝ} {B : Fin n → ℝ^n → ℝ}
    {C : ℝ^n → ℝ} (hA : ∀ i j, ContDiffUpToBoundary 1 (fun x ↦ A x i j) Ω)
    (hB : ∀ i, ContDiffUpToBoundary 1 (B i) Ω) (hC : ContDiffUpToBoundary 0 C Ω)
    (hsymm : ∀ x ∈ Ω, ∀ i j, A x i j = A x j i) {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ, alpha * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, A x i j * ξ j * ξ i)
    {ell : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))} {q₀ : H¹₀(Ω)}
    {p₀ : DerivLp n 2 Ω} {u₁ u₂ : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))}
    {v₁ v₂ : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))}
    {w₁ w₂ : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))}
    (h₁ : Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hΩ)
      (fun _ ↦ classicalAutonomousWaveForm hΩ hbounded hA hB hC) ell u₁ v₁ w₁ q₀ p₀)
    (h₂ : Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hΩ)
      (fun _ ↦ classicalAutonomousWaveForm hΩ hbounded hA hB hC) ell u₂ v₂ w₂ q₀ p₀) :
    u₁ = u₂ ∧ v₁ = v₂ ∧ w₁ = w₂ := by
  obtain ⟨hAs, hAe⟩ := classical_coefficients_ae_symmetric_elliptic hΩ hbounded hA hsymm halpha hell
  apply weakWave_eq_of_autonomous_sobolev_coefficients hn hΩ hbounded
    (fun i j ↦ (hA i j).toLp hΩ hbounded ∞) (fun i ↦ (hB i).toWkpSpaceOn hΩ hbounded ∞)
    (hC.toLp hΩ hbounded ∞) hAs hAe
  · simpa only [classicalAutonomousWaveForm,
      ContDiffUpToBoundary.toWkpSpaceOn_base_eq_toLp] using h₁
  · simpa only [classicalAutonomousWaveForm,
      ContDiffUpToBoundary.toWkpSpaceOn_base_eq_toLp] using h₂

end SobolevSpace.GraphSpace
