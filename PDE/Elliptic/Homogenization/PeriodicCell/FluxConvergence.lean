/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Homogenization.PeriodicCell.Convergence
public import PDE.Spaces.Sobolev.Periodic.FluxSeparation
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Weak convergence of the microscopic Dirichlet flux

For bounded measurable uniformly elliptic periodic coefficients on a bounded open
Euclidean domain, the microscopic Dirichlet flux converges weakly in L² to
the effective flux. Oscillating tests identify every weak flux limit, and weak
compactness gives convergence of the whole family. The named rescaling interface
uses periods in `(0, 1]`; no coefficient symmetry or boundary regularity is required.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology InnerProductSpace Sobolev

namespace PDE.Elliptic.Homogenization.PeriodicCell

variable {n : ℕ} (A : Lp ((ℝ^n) →L[ℝ] (ℝ^n)) ∞ (cellMeasure n))
    {α : ℝ} (hα : 0 < α)
    (hA : ∀ᵐ x ∂cellMeasure n, ∀ ξ : ℝ^n, α * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {Ω : Set (ℝ^n)} (hn : 0 < n) (hΩ : Bornology.IsBounded Ω) (hΩo : IsOpen Ω)
    (f : DerivLp n 2 Ω)

include hΩo in
/-- Every weak L² flux limit accompanying a strong solution-value limit is
identified by the derived effective operator. -/
theorem weak_flux_limit_eq_effectiveOperator
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (ε : ι → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε l (𝓝 0)) (U : H¹₀(Ω))
    (hu : Tendsto (fun j ↦ baseCoordCLM
      (rescaledDirichletSolution A hα hA hn hΩ (ε j) (hε j).ne' f)) l
      (𝓝 (baseCoordCLM U)))
    (P : Lp (ℝ^n) 2 (domainMeasure n Ω))
    (hp : Tendsto (fun j ↦ toWeakSpace ℝ (Lp (ℝ^n) 2 (domainMeasure n Ω))
      (rescaledDirichletFlux A hΩ hα hA hn f (ε j) (hε j) (hε1 j))) l
      (𝓝 (toWeakSpace ℝ (Lp (ℝ^n) 2 (domainMeasure n Ω)) P))) :
    P = (effectiveOperator A hα hA).compLp (gradientCLM U) := by
  let := isFiniteMeasure_domainMeasure_of_isBounded hΩ
  apply SobolevSpace.Periodic.eq_of_inner_weighted_const_eq hΩo
  intro i φ
  let g : Lp (ℝ^n) 2 (domainMeasure n Ω) := testFunctionLpTop (Ω := Ω) φ.1 •
    Lp.const 2 (volume.restrict Ω) (EuclideanSpace.single i (1 : ℝ))
  let p (j : ι) := rescaledDirichletFlux A hΩ hα hA hn f (ε j) (hε j) (hε1 j)
  have hP : Tendsto (fun j ↦ ⟪p j, g⟫_ℝ) l (𝓝 ⟪P, g⟫_ℝ) := by
    have h := PDE.Analysis.WeakCompactness.tendsto_evaluation hp (innerSL ℝ g)
    change Tendsto (fun j ↦ ⟪g, p j⟫_ℝ) l (𝓝 ⟪g, P⟫_ℝ) at h
    have he : (fun j ↦ ⟪p j, g⟫_ℝ) = (fun j ↦ ⟪g, p j⟫_ℝ) :=
      funext (fun j ↦ (real_inner_comm (p j) g).symm)
    rw [he, ← real_inner_comm P g]
    exact h
  have hQ := tendsto_inner_dirichletFlux_weighted_const A hα hA hΩ hn hΩo f
    ε hε hε1 ht U hu (EuclideanSpace.single i (1 : ℝ)) φ.1 φ.property
  rw [SobolevSpace.Periodic.inner_const_adjoint_weighted] at hQ
  exact tendsto_nhds_unique hP hQ

include hΩo in
/-- The microscopic Dirichlet flux converges weakly in L² to the
flux of the constructed effective Dirichlet solution. -/
theorem tendsto_weak_rescaledDirichletFlux
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (ε : ι → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε l (𝓝 0)) :
    Tendsto (fun j ↦ toWeakSpace ℝ (Lp (ℝ^n) 2 (domainMeasure n Ω))
      (rescaledDirichletFlux A hΩ hα hA hn f (ε j) (hε j) (hε1 j))) l
      (𝓝 (toWeakSpace ℝ (Lp (ℝ^n) 2 (domainMeasure n Ω))
        ((effectiveOperator A hα hA).compLp
          (gradientCLM (effectiveDirichletSolution A hα hA hn hΩ f))))) := by
  let := isFiniteMeasure_domainMeasure_of_isBounded hΩ
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp (ℝ^n) 2 (domainMeasure n Ω)) :=
    Lp.SecondCountableTopology
  let p (j : ι) := rescaledDirichletFlux A hΩ hα hA hn f (ε j) (hε j) (hε1 j)
  let U := effectiveDirichletSolution A hα hA hn hΩ f
  let Q := (effectiveOperator A hα hA).compLp (gradientCLM U)
  have hu := (tendsto_rescaledDirichletSolution A hα hA hn hΩ hΩo f ε hε ht).2
  obtain ⟨R, hR⟩ := exists_rescaledDirichletFlux_norm_bound A hΩ hα hA hn hΩo f
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hb : Bornology.IsBounded (range (fun j ↦ p (ns j))) := by
    apply isBounded_iff_forall_norm_le.mpr
    exact ⟨R, fun _ ⟨j, hj⟩ ↦ hj ▸ hR (ε (ns j)) (hε (ns j)) (hε1 (ns j))⟩
  obtain ⟨P, ms, hms, hw⟩ :=
    PDE.Analysis.WeakCompactness.exists_subseq_tendsto_weak_of_isBounded
      (PDE.Analysis.inclusionInDoubleDual_surjective (H := Lp (ℝ^n) 2 (domainMeasure n Ω)))
      (fun j ↦ p (ns j)) hb
  have he : P = Q := weak_flux_limit_eq_effectiveOperator A hα hA hn hΩ hΩo f
    (fun j ↦ ε (ns (ms j))) (fun j ↦ hε (ns (ms j)))
    (fun j ↦ hε1 (ns (ms j))) ((ht.comp hns).comp hms.tendsto_atTop) U
    ((hu.comp hns).comp hms.tendsto_atTop) P hw
  rw [he] at hw
  exact ⟨ms, hw⟩

end PDE.Elliptic.Homogenization.PeriodicCell
