/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Variational.Semigroup.Generation
public import PDE.Elliptic.Regularity.SolutionOperator.DirichletDomain
public import PDE.Elliptic.Variational.NonnegativePotential

/-!
# The classical Dirichlet wave generator

`C²` boundary geometry and classical `C¹` principal coefficients identify the
wave generator domain with `(H² ∩ H¹₀) × H¹₀`. The action is `(v,-Lu)`, including
the potential. Elliptic regularity proves one graph inclusion; integration by
parts proves the other.

Symmetry, ellipticity, and nonnegativity of the original potential construct the
energy Hilbert space and its contraction semigroup. The result,
`exists_contractionSemigroup_h2_generator`, is Theorem 6 of Evans, §7.4.3, with the energy norm
(36) and the domain `[H² ∩ H¹₀] × H¹₀`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.4.3, Theorem 6, equations (34)-(37).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace Hyperbolic.Variational

open MeasureTheory PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity
open scoped ENNReal

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
  (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
  (a : ℝ^n → Fin n → Fin n → ℝ)
  (ha : ∀ i j, ContDiffUpToBoundary 1 (fun x ↦ a x i j) Ω)
  (c : DerivLp n ∞ Ω) (α : ℝ) (hα : 0 < α)
  (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) α)

local notation "B" => fullDivergenceForm (n := n) (Ω := Ω)
  (multiplicationCoefficientOperator (n := n) (Ω := Ω)
    (fun i j ↦ ContDiffUpToBoundary.toLp (ha i j) hopen hbounded ∞))
  (multiplicationFirstOrderOperator 0) (multiplicationZeroOrderOperator c)
local notation "T" => h10L2GelfandTriple (n := n) (Ω := Ω) hopen
local notation "L" => fullStrongLoad (n := n) (Ω := Ω)
  (fun i j ↦ ContDiffUpToBoundary.toWkpSpaceOn (ha i j) hopen hbounded ∞) 0 c

include hgraph hα hell in
/-- The energy-space wave graph has exactly the classical domain and action `(v,-Lu)`. -/
theorem mem_waveOperator_graph_iff_h2 :
    let B₀ := B
    ∀ (hB : IsCoercive B₀) (hsymm : ∀ u v, B₀ u v = B₀ v u)
      (x y : WaveEnergySpace (H := DerivLp n 2 Ω) B₀ hB hsymm),
    let C₀ := WaveEnergySpace.coordinates (H := DerivLp n 2 Ω) B₀ hB hsymm
    (x, y) ∈ (waveOperator T B₀ hB hsymm).graph ↔
      baseCoordCLM (C₀ y).1 = (C₀ x).2 ∧
        ∃ G : W^{2,2}(Ω),
          wkpBaseCoordinateCLM G = baseCoordCLM (C₀ x).1 ∧ (C₀ y).2 = -L G := by
  intro B₀ hB hsymm x y C₀
  rw [mem_waveOperator_graph_iff]
  change baseCoordCLM (C₀ y).1 = (C₀ x).2 ∧ B₀ (C₀ x).1 = -(T).pivotToDual (C₀ y).2 ↔ _
  refine and_congr_right fun _ ↦ ?_
  have hbridge := fullDivergenceForm_eq_pivotToDual_iff_h2
    hopen hbounded hgraph a ha 0 c α hα hell (C₀ x).1 (-(C₀ y).2)
  rw [map_neg] at hbridge
  rw [hbridge]
  refine exists_congr fun G ↦ ?_
  refine and_congr_right fun _ ↦ ?_
  constructor <;> intro h <;> simpa only [neg_neg] using congrArg Neg.neg h.symm

include hgraph hα hell in
/-- The wave operator domain is precisely `(H² ∩ H¹₀) × H¹₀` inside the energy space. -/
theorem mem_waveOperator_domain_iff_h2 :
    let B₀ := B
    ∀ (hB : IsCoercive B₀) (hsymm : ∀ u v, B₀ u v = B₀ v u)
      (x : WaveEnergySpace (H := DerivLp n 2 Ω) B₀ hB hsymm),
    let C₀ := WaveEnergySpace.coordinates (H := DerivLp n 2 Ω) B₀ hB hsymm
    x ∈ (waveOperator T B₀ hB hsymm).domain ↔
      (∃ G : W^{2,2}(Ω), wkpBaseCoordinateCLM G = baseCoordCLM (C₀ x).1) ∧
        ∃ v : H¹₀(Ω), baseCoordCLM v = (C₀ x).2 := by
  intro B₀ hB hsymm x C₀
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨hv, G, hG, _⟩ :=
      (mem_waveOperator_graph_iff_h2 hopen hbounded hgraph a ha c α hα hell hB hsymm x y).mp hy
    exact ⟨⟨G, hG⟩, ⟨(C₀ y).1, hv⟩⟩
  · rintro ⟨⟨G, hG⟩, ⟨v, hv⟩⟩
    refine ⟨C₀.symm (v, -L G), ?_⟩
    apply (mem_waveOperator_graph_iff_h2 hopen hbounded hgraph a ha c α hα hell hB hsymm x _).mpr
    change baseCoordCLM (C₀ (C₀.symm (v, -L G))).1 = (C₀ x).2 ∧
      ∃ G' : W^{2,2}(Ω), wkpBaseCoordinateCLM G' = baseCoordCLM (C₀ x).1 ∧
        (C₀ (C₀.symm (v, -L G))).2 = -L G'
    rw [C₀.apply_symm_apply]
    exact ⟨hv, G, hG, rfl⟩

include hgraph hα hell in
omit c in
/-- Symmetric elliptic coefficients and a nonnegative potential construct a contraction
semigroup in the full energy norm. Its whole generator has the classical domain
`(H² ∩ H¹₀) × H¹₀` and the exact action `(v,-Lu)`, with no nonempty-domain hypothesis. -/
theorem exists_contractionSemigroup_h2_generator (c : ℝ^n → ℝ) (hc : ContDiffUpToBoundary 0 c Ω)
    (hc_nonneg : ∀ x ∈ Ω, 0 ≤ c x) (ha_symm : ∀ x ∈ Ω, ∀ i j, a x i j = a x j i) :
    let a₀ := fun i j ↦ (ha i j).toLp hopen hbounded ∞
    let c₀ := hc.toLp hopen hbounded ∞
    let B₀ := fullDivergenceForm (multiplicationCoefficientOperator a₀)
      (multiplicationFirstOrderOperator 0) (multiplicationZeroOrderOperator c₀)
    let L₀ := fullStrongLoad (fun i j ↦ (ha i j).toWkpSpaceOn hopen hbounded ∞) 0 c₀
    ∃ (hcoercive : IsCoercive B₀) (hsymmetric : ∀ u v, B₀ u v = B₀ v u)
      (S : StronglyContinuousSemigroup
        (WaveEnergySpace (H := DerivLp n 2 Ω) B₀ hcoercive hsymmetric)),
      let C₀ := WaveEnergySpace.coordinates (H := DerivLp n 2 Ω) B₀ hcoercive hsymmetric
      S.IsContraction ∧
      (∀ x, ‖x‖ ^ 2 = B₀ (C₀ x).1 (C₀ x).1 + ‖(C₀ x).2‖ ^ 2) ∧
      S.generatorPMap = waveOperator T B₀ hcoercive hsymmetric ∧
      (∀ x, x ∈ S.generatorPMap.domain ↔
        (∃ G : W^{2,2}(Ω), wkpBaseCoordinateCLM G = baseCoordCLM (C₀ x).1) ∧
          ∃ v : H¹₀(Ω), baseCoordCLM v = (C₀ x).2) ∧
      (∀ x y, S.HasGeneratorAt x y ↔
        baseCoordCLM (C₀ y).1 = (C₀ x).2 ∧
          ∃ G : W^{2,2}(Ω),
            wkpBaseCoordinateCLM G = baseCoordCLM (C₀ x).1 ∧ (C₀ y).2 = -L₀ G) := by
  let A : Fin n → Fin n → W^{1,∞}(Ω) := fun i j ↦ (ha i j).toWkpSpaceOn hopen hbounded ∞
  have hcoeff : coefficientBase A = fun i j ↦ (ha i j).toLp hopen hbounded ∞ := by
    funext i j
    exact (ha i j).toWkpSpaceOn_base_eq_toLp hopen hbounded ∞
  have hell' := coefficientBase_aeUniformlyElliptic hopen.measurableSet A a
    (fun i j ↦ (ha i j).toWkpSpaceOn_base_ae hopen hbounded ∞) α hα hell
  have hsymm' := coefficientBase_aeSymmetric hopen.measurableSet A a
    (fun i j ↦ (ha i j).toWkpSpaceOn_base_ae hopen hbounded ∞) ha_symm
  rw [hcoeff] at hell' hsymm'
  have hc' : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ hc.toLp hopen hbounded ∞ x := by
    filter_upwards [hc.toLp_coeFn hopen hbounded ∞, ae_restrict_mem hopen.measurableSet]
      with x hx hxΩ
    rw [hx]
    exact hc_nonneg x hxΩ
  let B₀ := fullDivergenceForm
    (multiplicationCoefficientOperator (fun i j ↦ (ha i j).toLp hopen hbounded ∞))
    (multiplicationFirstOrderOperator 0)
    (multiplicationZeroOrderOperator (hc.toLp hopen hbounded ∞))
  have hcoercive : IsCoercive B₀ :=
    fullDivergenceForm_zero_drift_isCoercive (Fact.out : 0 < n) hbounded _
      (integratedElliptic_multiplication_of_ae _ hell') _ hc'
  have hsymmetric : ∀ u v, B₀ u v = B₀ v u := fullDivergenceForm_zero_drift_symm
      (symmetricCoefficientOperator_multiplication_of_ae _ hsymm') _
  refine ⟨hcoercive, hsymmetric, waveContractionSemigroup T B₀ hcoercive hsymmetric,
    waveContractionSemigroup_isContraction T B₀ hcoercive hsymmetric,
    WaveEnergySpace.norm_sq_eq B₀ hcoercive hsymmetric,
    generatorPMap_waveContractionSemigroup T B₀ hcoercive hsymmetric, ?_, ?_⟩
  · intro x
    rw [generatorPMap_waveContractionSemigroup]
    exact mem_waveOperator_domain_iff_h2 hopen hbounded hgraph a ha _ α hα hell
      hcoercive hsymmetric x
  · intro x y
    rw [StronglyContinuousSemigroup.hasGeneratorAt_iff_mem_generatorPMap_graph,
      generatorPMap_waveContractionSemigroup]
    exact mem_waveOperator_graph_iff_h2 hopen hbounded hgraph a ha _ α hα hell
      hcoercive hsymmetric x y

end Hyperbolic.Variational
