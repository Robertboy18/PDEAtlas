/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Homogenization.PeriodicCell.LimitEquation

/-!
# Periodic homogenization of the multidimensional Dirichlet problem

For a bounded open domain and a bounded measurable uniformly elliptic periodic
coefficient, the canonical microscopic Dirichlet solutions converge weakly in
H¹₀ and strongly in L² to the canonical solution with the derived effective matrix.
The compactness limit is identified by the oscillating-test argument;
uniqueness gives convergence of the whole family. No symmetry or boundary
regularity beyond boundedness and openness is imposed.
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

include hΩo

/-- Every vanishing-period sequence has a subsequence converging to the
constructed effective solution, weakly in H¹₀ and strongly in L². -/
theorem exists_subseq_tendsto_effectiveDirichletSolution
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      Tendsto (fun j ↦ toWeakSpace ℝ (H¹₀(Ω))
        (rescaledDirichletSolution A hα hA hn hΩ (ε (ns j)) (hε (ns j)).ne' f)) atTop
        (𝓝 (toWeakSpace ℝ (H¹₀(Ω)) (effectiveDirichletSolution A hα hA hn hΩ f))) ∧
      Tendsto (fun j ↦ baseCoordCLM
        (rescaledDirichletSolution A hα hA hn hΩ (ε (ns j)) (hε (ns j)).ne' f)) atTop
        (𝓝 (baseCoordCLM (effectiveDirichletSolution A hα hA hn hΩ f))) := by
  obtain ⟨V, ns, hns, hw, hv⟩ := exists_subseq_rescaledDirichletSolution A hα hA
    hn hΩ hΩo f ε (fun j ↦ (hε j).ne')
  have he := strong_limit_eq_effectiveDirichletSolution A hα hA hn hΩ hΩo f
    (fun j ↦ ε (ns j)) (fun j ↦ hε (ns j)) (fun j ↦ hε1 (ns j))
    (ht.comp hns.tendsto_atTop) V hv
  exact ⟨ns, hns, he ▸ hw, he ▸ hv⟩

/-- Compactness and oscillating-test uniqueness give weak H¹₀ and strong L²
convergence of the entire microscopic Dirichlet family. -/
theorem tendsto_rescaledDirichletSolution_of_le_one
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (ε : ι → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε l (𝓝 0)) :
    Tendsto (fun j ↦ toWeakSpace ℝ (H¹₀(Ω))
      (rescaledDirichletSolution A hα hA hn hΩ (ε j) (hε j).ne' f)) l
      (𝓝 (toWeakSpace ℝ (H¹₀(Ω)) (effectiveDirichletSolution A hα hA hn hΩ f))) ∧
    Tendsto (fun j ↦ baseCoordCLM
      (rescaledDirichletSolution A hα hA hn hΩ (ε j) (hε j).ne' f)) l
      (𝓝 (baseCoordCLM (effectiveDirichletSolution A hα hA hn hΩ f))) := by
  constructor
  · apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨ms, _hms, hw, _hv⟩ := exists_subseq_tendsto_effectiveDirichletSolution
      A hα hA hn hΩ hΩo f (fun j ↦ ε (ns j))
      (fun j ↦ hε (ns j)) (fun j ↦ hε1 (ns j)) (ht.comp hns)
    exact ⟨ms, hw⟩
  · apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨ms, _hms, _hw, hv⟩ := exists_subseq_tendsto_effectiveDirichletSolution
      A hα hA hn hΩ hΩo f (fun j ↦ ε (ns j))
      (fun j ↦ hε (ns j)) (fun j ↦ hε1 (ns j)) (ht.comp hns)
    exact ⟨ms, hv⟩

/-- Periodic homogenization of the canonical Dirichlet BVP on every bounded open
domain, for bounded measurable uniformly elliptic, possibly nonsymmetric coefficients.
Only positivity and convergence to zero are required of the periods. -/
theorem tendsto_rescaledDirichletSolution
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (ε : ι → ℝ) (hε : ∀ j, 0 < ε j) (ht : Tendsto ε l (𝓝 0)) :
    Tendsto (fun j ↦ toWeakSpace ℝ (H¹₀(Ω))
      (rescaledDirichletSolution A hα hA hn hΩ (ε j) (hε j).ne' f)) l
      (𝓝 (toWeakSpace ℝ (H¹₀(Ω)) (effectiveDirichletSolution A hα hA hn hΩ f))) ∧
    Tendsto (fun j ↦ baseCoordCLM
      (rescaledDirichletSolution A hα hA hn hΩ (ε j) (hε j).ne' f)) l
      (𝓝 (baseCoordCLM (effectiveDirichletSolution A hα hA hn hΩ f))) := by
  let δ (j : ι) := min (ε j) 1
  have hδ (j : ι) : 0 < δ j := lt_min (hε j) zero_lt_one
  have htδ : Tendsto δ l (𝓝 0) := by
    simpa only [min_eq_left zero_le_one] using ht.min (tendsto_const_nhds (x := (1 : ℝ)))
  have he : ∀ᶠ j in l, δ j = ε j :=
    (ht.eventually (eventually_le_nhds zero_lt_one)).mono (fun _ hj ↦ min_eq_left hj)
  obtain ⟨hw, hv⟩ := tendsto_rescaledDirichletSolution_of_le_one A hα hA hn hΩ hΩo f
    δ hδ (fun j ↦ min_le_right (ε j) 1) htδ
  constructor
  · exact hw.congr' (he.mono (fun j hj ↦ by simp only [hj]))
  · exact hv.congr' (he.mono (fun j hj ↦ by simp only [hj]))

end PDE.Elliptic.Homogenization.PeriodicCell
