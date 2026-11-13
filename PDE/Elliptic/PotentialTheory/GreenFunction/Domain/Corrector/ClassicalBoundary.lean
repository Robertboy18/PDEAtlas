/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Corrector.Existence
public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Corrector.Regularization
public import PDE.Elliptic.Variational.Harmonic.HigherOrder
import PDE.Elliptic.Regularity.Global.SmoothBoundary
import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.ClassicalBoundary
import PDE.Spaces.Sobolev.GraphSpace.Topology.OrderDensity

/-!
# Classical boundary jets of the constructed corrector

A smooth regularized pole gives an affine lifting of every finite Sobolev order.
On a Cⁿ⁺³ graph domain, unshifted Poisson regularity puts the harmonic corrector in
Hⁿ⁺³. Sobolev exponent improvement and Morrey's theorem then give its
classical derivatives through order two, uniformly continuous on the domain.

The finite boundary order is a sufficient hypothesis. Under C¹ geometry alone,
`Corrector.Existence` gives a corrector continuous on the closure.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace PotentialTheory.GreenFunction.Domain

open MeasureTheory Metric Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Boundary SobolevSpace.Approximation.UpToBoundary
open SobolevSpace.GraphSpace.BoundaryRegularity
open scoped ENNReal InnerProductSpace

/-- A continuous weak harmonic corrector has uniformly continuous
second-order boundary jets under the explicit sufficient Cⁿ⁺³ graph hypothesis. -/
theorem corrector_contDiffUpToBoundary_of_higher_graph
    {m : ℕ} {Ω : Set ℝ^(m + 1)}
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasContDiffGraphBoundary (m + 1 + 3) Ω)
    {x : ℝ^(m + 1)} (hx : x ∈ Ω)
    (U : H¹(Ω)) {φ : ℝ^(m + 1) → ℝ}
    (hU : baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] φ)
    (hφ : ContinuousOn φ (closure Ω))
    (hb : EqOn φ (fun y ↦ fundamentalSolution (m + 1) (y - x)) (frontier Ω))
    (hw : ∀ t : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) U)
        (derivCoordCLM i t)) = 0) :
    ContDiffUpToBoundary 2 φ Ω := by
  have hC1 := hgraph.hasC1GraphBoundary
    (by exact_mod_cast (by omega : 1 ≤ m + 1 + 3))
  let := hC1.c1ExtensionAtlas hΩ hbounded
  obtain ⟨P⟩ := exists_inwardPartition hΩ hbounded (hasC1Boundary_of_local_graph hC1)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  obtain ⟨A, hA, hAc, w, hweq, _, _⟩ :=
    exists_regularized_corrector P hbounded hr hball U hφ hU hb
  let G : W^{m + 1 + 1 + 2,2}(Ω) :=
    mkWkpSpaceOnOfContDiff A hA hAc
  have hG : lowerOrderCLM (by omega : 1 ≤ m + 1 + 1 + 2) G =
      mkWkpSpaceOnOfContDiff (k := 1) (p := 2) (Ω := Ω) A hA hAc :=
    lowerOrderCLM_mkWkpSpaceOnOfContDiff _ A hA hAc
  have hsum : lowerOrderCLM (by omega : 1 ≤ m + 1 + 1 + 2) G +
      (w : H¹(Ω)) = U := by
    rw [hG, hweq]
    abel
  obtain ⟨V, hV⟩ := exists_higherOrder_of_affine_dirichlet_eq_zero
    (m + 1 + 1) hΩ hbounded
    (hgraph.of_le (by exact_mod_cast (by omega : m + 1 + 1 + 2 ≤ m + 1 + 3)))
    G w (by simpa only [hsum] using hw)
  rw [hsum] at hV
  have hVae : baseRepresentative V =ᵐ[domainMeasure (m + 1) Ω] φ := by
    change (wkpBaseCoordinateCLM V : ℝ^(m + 1) → ℝ) =ᵐ[domainMeasure (m + 1) Ω] φ
    rw [hV]
    exact hU
  obtain ⟨atlas, _, _⟩ := hgraph.exists_c2BoundaryAtlas
    (by exact_mod_cast (by omega : 2 ≤ m + 1 + 3)) hΩ hbounded
  let : C1ExtensionAtlas (m + 1) Ω := atlas.toC1ExtensionAtlas
  let : Fact (1 ≤ (((2 * (m + 1) : ℕ) : NNReal) : ℝ≥0∞)) :=
    ⟨by exact_mod_cast (by omega : 1 ≤ 2 * (m + 1))⟩
  let V' := lowerOrderCLM (by omega : 2 + (m + 1) + 1 ≤ m + 1 + 1 + 2) V
  obtain ⟨jet, hjet⟩ := exists_supercriticalSobolevJet atlas 2 V'
  obtain ⟨v, hv, _, hvae⟩ := exists_contDiffUpToBoundary_representative_of_dimension_lt
    (by exact_mod_cast (by omega : 1 < 2 * (m + 1)))
    (by exact_mod_cast (by omega : m + 1 < 2 * (m + 1)))
    (by rfl : 2 + 1 ≤ 2 + 1) jet
  have hjet' : baseRepresentative jet =ᵐ[domainMeasure (m + 1) Ω] φ := by
    apply hjet.trans
    simpa only [V', baseRepresentative_lowerOrderCLM] using hVae
  have heq : EqOn φ v Ω := Measure.eqOn_open_of_ae_eq
    (hvae.trans hjet').symm hΩ (hφ.mono subset_closure) hv.contDiffOn.continuousOn
  exact hv.congr hΩ heq

/-- The corrector and its second-order classical boundary jets are constructed
from bounded open Cⁿ⁺³ graph geometry. -/
theorem exists_classical_harmonic_corrector_of_higher_graph
    {m : ℕ} {Ω : Set ℝ^(m + 1)} (hn : 2 ≤ m + 1)
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasContDiffGraphBoundary (m + 1 + 3) Ω)
    {x : ℝ^(m + 1)} (hx : x ∈ Ω) :
    ∃ φ : ℝ^(m + 1) → ℝ, ContDiffUpToBoundary 2 φ Ω ∧
      ContinuousOn φ (closure Ω) ∧ LaplacianEquation.IsHarmonicPDE (m + 1) φ Ω ∧
      EqOn φ (fun y ↦ fundamentalSolution (m + 1) (y - x)) (frontier Ω) := by
  obtain ⟨U, φ, hU, hh, hc, hb, hw⟩ := exists_harmonic_corrector_of_local_graph
    hn hΩ hbounded
    (hgraph.hasC1GraphBoundary (by exact_mod_cast (by omega : 1 ≤ m + 1 + 3))) hx
  exact ⟨φ, corrector_contDiffUpToBoundary_of_higher_graph hΩ hbounded hgraph
    hx U hU hc hb hw, hc, hh, hb⟩

end PotentialTheory.GreenFunction.Domain
