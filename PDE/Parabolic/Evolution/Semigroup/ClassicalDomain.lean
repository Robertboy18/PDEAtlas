/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.DirichletDomain
public import PDE.Parabolic.Evolution.Semigroup.DivergenceForm

/-!
# The classical Dirichlet domain of the parabolic generator

On a bounded open set with `C²` graph boundary, for principal coefficients that are `C¹` up to the
boundary and drift and potential coefficients that are continuous up to the boundary, the generator
domain of the divergence-form semigroup is `H² ∩ H¹₀` and the generator acts as `-L`
(`exists_semigroup_h2_generator`). The hypotheses are stated on the coefficient functions and the
boundary graph themselves: no extension of the coefficients and no boundary atlas is assumed.

This is Evans's §7.4.3(a), (25)-(26) and Theorem 5, which assume smooth coefficients and a smooth
boundary.

## How it works

Evans defines `D(A) = H¹₀(U) ∩ H²(U)`, (25), so he must prove that `A` is closed, with the `H²`
estimate of §6.3.2, Theorem 4 (step 2 of his proof), and that `λ - A` maps `D(A)` onto `L²`, with
elliptic regularity (step 3). We start from the semigroup of
`PDE.Parabolic.Evolution.Semigroup.DivergenceForm`, whose generator is the weak Dirichlet operator
on its natural domain, and identify the domain afterwards
(`mem_negativeDirichletOperator_domain_iff_h2`). Elliptic boundary regularity puts every element of
the weak domain in `H²`. Conversely, for `u ∈ H¹₀` with an `H²` representative `G`, the weak Leibniz
rule turns the form into the strong load `fullStrongLoad G`, so the generator acts as `-L`
(`mem_negativeDirichletOperator_graph_fullStrongLoad`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 4 (Boundary H²-regularity), (38)-(42),
  p. 334; §7.4.3(a), (24)-(32) and Theorem 5 (Second-order parabolic PDE as semigroups) and its
  proof, pp. 441-443.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace HeatEquation.Semigroup.Divergence

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity
open scoped ENNReal

variable {n : ℕ} {Ω : Set (ℝ^n)}

variable [Fact (0 < n)]
variable (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
  (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
  (a : ℝ^n → Fin n → Fin n → ℝ)
  (ha : ∀ i j, ContDiffUpToBoundary 1 (fun x ↦ a x i j) Ω)
  (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
  (α : ℝ) (hα : 0 < α)
  (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) α)

include hgraph hα hell

omit b c in
/-- `C¹` principal coefficients and continuous lower-order coefficients on a bounded domain with
`C²` graph boundary give an exponentially bounded `L²` semigroup whose generator has domain
`H² ∩ H¹₀` and acts as the negative full divergence operator. The `L^∞` coefficient classes and the
Gårding shift are computed from the given functions. -/
theorem exists_semigroup_h2_generator
    (b : Fin n → ℝ^n → ℝ) (c : ℝ^n → ℝ)
    (hb : ∀ i, ContDiffUpToBoundary 0 (b i) Ω) (hc : ContDiffUpToBoundary 0 c Ω) :
    let a₀ := fun i j ↦ (ha i j).toLp hopen hbounded ∞
    let b₀ := fun i ↦ (hb i).toLp hopen hbounded ∞
    let c₀ := hc.toLp hopen hbounded ∞
    let γ := coerciveShift (n := n) α (∑ i, ‖b₀ i‖) ‖c₀‖
    ∃ S : StronglyContinuousSemigroup (DerivLp n 2 Ω),
      0 ≤ γ ∧ (∀ t : NNReal, ‖S t‖ ≤ Real.exp (γ * (t : ℝ))) ∧
      S.generatorPMap = negativeDirichletOperator hopen a₀ b₀ c₀ ∧
      (∀ x, x ∈ S.generatorPMap.domain ↔
        (∃ u : H¹₀(Ω), baseCoordCLM u = x) ∧
          ∃ G : W^{2,2}(Ω), wkpBaseCoordinateCLM G = x) ∧
      (∀ (u : H¹₀(Ω)) (G : W^{2,2}(Ω)),
        wkpBaseCoordinateCLM G = baseCoordCLM u →
        S.HasGeneratorAt (baseCoordCLM u)
          (-fullStrongLoad (fun i j ↦ (ha i j).toWkpSpaceOn hopen hbounded ∞) b₀ c₀ G)) := by
  let A : Fin n → Fin n → W^{1,∞}(Ω) :=
    fun i j ↦ (ha i j).toWkpSpaceOn hopen hbounded ∞
  have hcoeff : coefficientBase A = fun i j ↦ (ha i j).toLp hopen hbounded ∞ := by
    funext i j
    exact (ha i j).toWkpSpaceOn_base_eq_toLp hopen hbounded ∞
  have hell' := coefficientBase_aeUniformlyElliptic hopen.measurableSet A a
    (fun i j ↦ (ha i j).toWkpSpaceOn_base_ae hopen hbounded ∞) α hα hell
  rw [hcoeff] at hell'
  let b₀ := fun i ↦ (hb i).toLp hopen hbounded ∞
  let c₀ := hc.toLp hopen hbounded ∞
  refine ⟨semigroup hopen _ b₀ c₀ hell', coerciveShift_nonneg b₀ c₀ hα,
    norm_semigroup_le hopen _ b₀ c₀ hell', generatorPMap_semigroup hopen _ b₀ c₀ hell',
    ?_, ?_⟩
  · intro x
    rw [generatorPMap_semigroup]
    exact mem_negativeDirichletOperator_domain_iff_h2 hopen hbounded hgraph a ha b₀ c₀ α hα hell x
  · intro u G hbase
    rw [StronglyContinuousSemigroup.hasGeneratorAt_iff_mem_generatorPMap_graph,
      generatorPMap_semigroup]
    have h := mem_negativeDirichletOperator_graph_fullStrongLoad hopen A b₀ c₀ G u hbase
    rwa [hcoeff] at h

end HeatEquation.Semigroup.Divergence
