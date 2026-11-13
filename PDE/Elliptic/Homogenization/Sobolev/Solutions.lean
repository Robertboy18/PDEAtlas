/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Homogenization.Sobolev.FluxBridge
public import PDE.Elliptic.Homogenization.Uniqueness
public import PDE.Elliptic.Variational.DivergenceSolution

/-!
# The explicit homogenization solutions as canonical weak solutions

The oscillatory and harmonic-mean solutions define `H¹₀` fields with
identified weak derivatives. Their weak equations use the divergence
solution predicate `IsWeakDivergenceSolution`. Periodicity and positivity give a common
ellipticity constant,
and variational uniqueness identifies the explicit solution with the named solver.
Interval flux solutions with arbitrary exterior extensions represent the same weak solution.
-/

@[expose] public noncomputable section

open Set MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal Topology
open PDE.Analysis (primitive hasDerivAt_primitive)

namespace PDE.Elliptic.Homogenization

namespace PeriodicMedium

open PDE.Analysis.PeriodicAveraging

/-- The oscillatory coefficient as a one-by-one matrix of `L∞` classes. -/
def matrixCoefficient (a : PeriodicMedium) (ε : ℝ) :
    Fin 1 → Fin 1 → DerivLp 1 ∞ unitInterval :=
  fun _ _ ↦ continuousLiftLp (a.continuous.comp (continuous_id.div_const ε)) ∞

/-- The explicit oscillatory solution represents an `H¹₀` weak divergence solution. -/
theorem exists_solution_sobolev (a : PeriodicMedium) {f : ℝ → ℝ}
    (hf : Continuous f) (ε : ℝ) :
    ∃ U : H¹₀(unitInterval),
      (baseCoordCLM U : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 unitInterval]
        (fun x ↦ a.solution f ε (x 0)) ∧
      (∀ i, (derivCoordCLM i U : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 unitInterval]
        (fun x ↦ deriv (a.solution f ε) (x 0))) ∧
      IsWeakDivergenceSolution (a.matrixCoefficient ε) (continuousLiftLp hf 2) U :=
  exists_weakSolution_of_flux (a.continuous.comp (continuous_id.div_const ε)) hf
    (a.contDiff_solution hf ε) (a.solution_zero f ε) (a.solution_one f ε)
    (a.hasDerivAt_solution_flux hf ε)


/-- The constructed interval solution in the zero-trace Sobolev space. -/
def sobolevSolution (a : PeriodicMedium) {f : ℝ → ℝ} (hf : Continuous f) (ε : ℝ) :
    H¹₀(unitInterval) :=
  (a.exists_solution_sobolev hf ε).choose

/-- The Sobolev solution has the explicit classical solution as its value representative. -/
theorem sobolevSolution_base_ae (a : PeriodicMedium) {f : ℝ → ℝ}
    (hf : Continuous f) (ε : ℝ) :
    (baseCoordCLM (a.sobolevSolution hf ε) : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 unitInterval]
      fun x ↦ a.solution f ε (x 0) :=
  (a.exists_solution_sobolev hf ε).choose_spec.1

/-- The weak derivative is represented by the derivative of the explicit solution. -/
theorem sobolevSolution_deriv_ae (a : PeriodicMedium) {f : ℝ → ℝ}
    (hf : Continuous f) (ε : ℝ) (i : Fin 1) :
    (derivCoordCLM i (a.sobolevSolution hf ε) : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 unitInterval]
      fun x ↦ deriv (a.solution f ε) (x 0) :=
  (a.exists_solution_sobolev hf ε).choose_spec.2.1 i

/-- The constructed Sobolev field satisfies the canonical weak divergence equation. -/
theorem sobolevSolution_isWeakDivergenceSolution (a : PeriodicMedium) {f : ℝ → ℝ}
    (hf : Continuous f) (ε : ℝ) :
    IsWeakDivergenceSolution (a.matrixCoefficient ε) (continuousLiftLp hf 2)
      (a.sobolevSolution hf ε) :=
  (a.exists_solution_sobolev hf ε).choose_spec.2.2

/-- Every interval flux solution represents a canonical weak solution, regardless of its
exterior extension. Its weak derivative agrees with its ordinary derivative in the interior. -/
theorem exists_sobolev_of_isFluxDirichletSolution (a : PeriodicMedium) {f v : ℝ → ℝ}
    (hf : Continuous f) (ε : ℝ)
    (hv : IsFluxDirichletSolution (fun x ↦ a.coefficient (x / ε)) f v) :
    ∃ U : H¹₀(unitInterval),
      (baseCoordCLM U : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 unitInterval] (fun x ↦ v (x 0)) ∧
      (∀ i, (derivCoordCLM i U : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 unitInterval]
        (fun x ↦ deriv v (x 0))) ∧
      IsWeakDivergenceSolution (a.matrixCoefficient ε) (continuousLiftLp hf 2) U := by
  have he := a.solution_unique hf ε hv
  refine ⟨a.sobolevSolution hf ε, ?_, ?_,
    a.sobolevSolution_isWeakDivergenceSolution hf ε⟩
  · filter_upwards [a.sobolevSolution_base_ae hf ε,
      ae_restrict_mem isOpen_unitInterval.measurableSet] with x hx hxΩ
    exact hx.trans (he ⟨hxΩ.1.le, hxΩ.2.le⟩).symm
  · intro i
    filter_upwards [a.sobolevSolution_deriv_ae hf ε i,
      ae_restrict_mem isOpen_unitInterval.measurableSet] with x hx hxΩ
    have hlocal : v =ᶠ[𝓝 (x 0)] a.solution f ε :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hxΩ)
        (fun y hy ↦ he (Ioo_subset_Icc_self hy))
    exact hx.trans hlocal.deriv_eq.symm

/-- The positive periodic medium gives one ellipticity constant valid at every scale. -/
theorem exists_aeUniformlyElliptic_matrixCoefficient (a : PeriodicMedium) :
    ∃ α > 0, ∀ ε, AEUniformlyElliptic (a.matrixCoefficient ε) α := by
  obtain ⟨α, hα, β, _, hb⟩ := a.exists_ellipticity_bounds
  refine ⟨α, hα, fun ε ↦ ⟨hα, ?_⟩⟩
  filter_upwards [continuousLiftLp_ae
    (a.continuous.comp (continuous_id.div_const ε)) ∞] with x hx
  intro ξ
  simp only [Fin.sum_univ_one]
  change α * (ξ 0 * ξ 0) ≤ (continuousLiftLp _ ∞ : ℝ^1 → ℝ) x * ξ 0 * ξ 0
  rw [hx, mul_assoc]
  exact mul_le_mul_of_nonneg_right (hb (x 0 / ε)).1 (mul_self_nonneg _)

/-- Uniqueness identifies the explicit construction with the variational solver. -/
theorem sobolevSolution_eq_weakDivergenceSolve (a : PeriodicMedium) {f : ℝ → ℝ}
    (hf : Continuous f) (ε : ℝ) {α : ℝ}
    (ha : AEUniformlyElliptic (a.matrixCoefficient ε) α) :
    a.sobolevSolution hf ε = weakDivergenceSolve zero_lt_one isBounded_unitInterval
      (a.matrixCoefficient ε) ha (continuousLiftLp hf 2) :=
  (IsWeakDivergenceSolution.existsUnique_of_ae isOpen_unitInterval zero_lt_one
    isBounded_unitInterval (a.matrixCoefficient ε) ha (continuousLiftLp hf 2)).unique
      (a.sobolevSolution_isWeakDivergenceSolution hf ε)
      (weakDivergenceSolve_isWeakDivergenceSolution isOpen_unitInterval zero_lt_one
        isBounded_unitInterval (a.matrixCoefficient ε) ha (continuousLiftLp hf 2))

/-- The effective solution represents an `H¹₀` solution with the harmonic-mean coefficient. -/
theorem exists_homogenizedSolution_sobolev (a : PeriodicMedium) {f : ℝ → ℝ}
    (hf : Continuous f) :
    ∃ U : H¹₀(unitInterval),
      (baseCoordCLM U : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 unitInterval]
        (fun x ↦ a.homogenizedSolution f (x 0)) ∧
      (∀ i, (derivCoordCLM i U : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 unitInterval]
        (fun x ↦ deriv (a.homogenizedSolution f) (x 0))) ∧
      IsWeakDivergenceSolution
        (fun _ _ ↦ continuousLiftLp (g := fun _ ↦ a.effective) continuous_const ∞)
        (continuousLiftLp hf 2) U := by
  refine exists_weakSolution_of_flux continuous_const hf (a.contDiff_homogenizedSolution hf)
    (a.homogenizedSolution_zero f) (a.homogenizedSolution_one f) (fun x ↦ ?_)
  simp_rw [a.homogenizedSolution_flux hf]
  convert (hasDerivAt_primitive hf x).const_sub
    (primitive (primitive f) 1) using 1

/-- The harmonic-mean solution in the zero-trace Sobolev space. -/
def homogenizedSobolevSolution (a : PeriodicMedium) {f : ℝ → ℝ} (hf : Continuous f) :
    H¹₀(unitInterval) :=
  (a.exists_homogenizedSolution_sobolev hf).choose

/-- The effective Sobolev solution has the explicit effective value representative. -/
theorem homogenizedSobolevSolution_base_ae (a : PeriodicMedium) {f : ℝ → ℝ}
    (hf : Continuous f) :
    (baseCoordCLM (a.homogenizedSobolevSolution hf) : ℝ^1 → ℝ)
      =ᵐ[domainMeasure 1 unitInterval] fun x ↦ a.homogenizedSolution f (x 0) :=
  (a.exists_homogenizedSolution_sobolev hf).choose_spec.1

/-- The effective weak derivative has the explicit effective derivative representative. -/
theorem homogenizedSobolevSolution_deriv_ae (a : PeriodicMedium) {f : ℝ → ℝ}
    (hf : Continuous f) (i : Fin 1) :
    (derivCoordCLM i (a.homogenizedSobolevSolution hf) : ℝ^1 → ℝ)
      =ᵐ[domainMeasure 1 unitInterval] fun x ↦ deriv (a.homogenizedSolution f) (x 0) :=
  (a.exists_homogenizedSolution_sobolev hf).choose_spec.2.1 i

/-- The effective Sobolev field satisfies the canonical weak divergence equation. -/
theorem homogenizedSobolevSolution_isWeakDivergenceSolution (a : PeriodicMedium) {f : ℝ → ℝ}
    (hf : Continuous f) :
    IsWeakDivergenceSolution
      (fun _ _ ↦ continuousLiftLp (g := fun _ ↦ a.effective) continuous_const ∞)
      (continuousLiftLp hf 2) (a.homogenizedSobolevSolution hf) :=
  (a.exists_homogenizedSolution_sobolev hf).choose_spec.2.2

end PeriodicMedium
end PDE.Elliptic.Homogenization
