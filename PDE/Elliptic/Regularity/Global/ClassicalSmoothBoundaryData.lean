/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Global.ClassicalHigherBoundaryData
public import PDE.Elliptic.Regularity.Global.SmoothBoundary
import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.ClassicalBoundary

/-!
# Smooth boundary regularity from order-by-order classical data

The boundary and coefficient hypotheses are given separately at each finite order. This matches
Evans's definitions: `C^∞(Ū)` is the intersection of the spaces `C^k(Ū)`, and a boundary is `C^∞` if
it is `C^k` for every `k`. Each finite elliptic estimate constructs its own atlas and principal
extension. The Sobolev representatives all belong to the same weak solution, so the Morrey and
continuity assembly gives one representative smooth on the closure. Drift and potential terms remain
in the equation.

At shift zero this is Evans's §6.3.2, Theorem 6 (Infinite differentiability up to the boundary).

## Main results

* `exists_allOrderSobolevRepresentatives_of_contDiffUpToBoundary`: `W^{k,2}` representatives of the
  same weak solution at every order, the first step of Evans's proof.
* `exists_smoothRepresentativeOnClosure_of_contDiffUpToBoundary`: one representative that is smooth
  on the closure and `C^k` up to the boundary for every `k`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 6 (Infinite differentiability up to the
  boundary) and its proof, p. 343; Appendix A.3, Function spaces (i)-(ii), p. 702; Appendix C.1, the
  definition of a `C^k` boundary, p. 710.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- Smooth closure data give compatible Sobolev representatives at every order for the
full shifted divergence operator. Each finite-order graph description may be different. -/
theorem exists_allOrderSobolevRepresentatives_of_contDiffUpToBoundary
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    (a : ℝ^n → Fin n → Fin n → ℝ) (b : Fin n → ℝ^n → ℝ) (c f : ℝ^n → ℝ)
    (ha : ∀ k i j, ContDiffUpToBoundary k (fun x ↦ a x i j) Ω)
    (hb : ∀ k i, ContDiffUpToBoundary k (b i) Ω)
    (hc : ∀ k, ContDiffUpToBoundary k c Ω)
    (hf : ∀ k, ContDiffUpToBoundary k f Ω)
    (lambda alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha)
    (u : H¹₀(Ω))
    (hu : IsWeakShiftedFullDivergenceSolution
      (fun i j ↦ (ha 0 i j).toLp hopen hbounded ∞)
      (fun i ↦ (hb 0 i).toLp hopen hbounded ∞) ((hc 0).toLp hopen hbounded ∞)
      lambda ((hf 0).toLp hopen hbounded 2) 0 u) :
    ∀ k, ∃ W : W^{k,2}(Ω),
      baseRepresentative W =ᵐ[domainMeasure n Ω] weakSolutionBase u := by
  intro k
  obtain ⟨_, _, hreg⟩ :=
    exists_global_higherOrder_estimate_of_contDiffUpToBoundary k hopen hbounded
      (hgraph (k + 2)) a b c (ha (k + 1)) (hb (k + 1)) (hc (k + 1))
      lambda alpha halpha hElliptic
  obtain ⟨W, hW, _⟩ := hreg ((hf k).toWkpSpaceOn hopen hbounded 2) u (by
    simpa only [ContDiffUpToBoundary.toWkpSpaceOn_base_eq_toLp,
      ContDiffUpToBoundary.toLp] using hu)
  refine ⟨lowerOrderCLM (by omega : k ≤ k + 2) W, ?_⟩
  rw [baseRepresentative_lowerOrderCLM]
  change (wkpBaseCoordinateCLM W : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
    (baseCoordCLM u : ℝ^n → ℝ)
  rw [hW]

/-- The full divergence equation has a single representative smooth on the closure, with
every interior derivative uniformly continuous there. The boundary and coefficient data
are given separately at each finite order, without a common smooth atlas or extension. -/
theorem exists_smoothRepresentativeOnClosure_of_contDiffUpToBoundary
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    (a : ℝ^n → Fin n → Fin n → ℝ) (b : Fin n → ℝ^n → ℝ) (c f : ℝ^n → ℝ)
    (ha : ∀ k i j, ContDiffUpToBoundary k (fun x ↦ a x i j) Ω)
    (hb : ∀ k i, ContDiffUpToBoundary k (b i) Ω)
    (hc : ∀ k, ContDiffUpToBoundary k c Ω)
    (hf : ∀ k, ContDiffUpToBoundary k f Ω)
    (lambda alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha)
    (u : H¹₀(Ω))
    (hu : IsWeakShiftedFullDivergenceSolution
      (fun i j ↦ (ha 0 i j).toLp hopen hbounded ∞)
      (fun i ↦ (hb 0 i).toLp hopen hbounded ∞) ((hc 0).toLp hopen hbounded ∞)
      lambda ((hf 0).toLp hopen hbounded 2) 0 u) :
    ∃ v : ℝ^n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) v (closure Ω) ∧
      (∀ k, ContDiffUpToBoundary k v Ω) ∧
      v =ᵐ[domainMeasure n Ω] weakSolutionBase u := by
  obtain ⟨atlas, _, _⟩ := (hgraph 2).exists_c2BoundaryAtlas (by norm_num) hopen hbounded
  have hall := exists_allOrderSobolevRepresentatives_of_contDiffUpToBoundary hopen hbounded
    hgraph a b c f ha hb hc hf lambda alpha halpha hElliptic u hu
  obtain ⟨v, hv, hvae⟩ :=
    exists_smoothRepresentativeOnClosure_of_all_orders hopen (weakSolutionBase u) hall
    (hasClassicalRepresentativesOnClosure atlas)
  refine ⟨v, hv, ?_, hvae⟩
  intro k
  let : Boundary.C1ExtensionAtlas n Ω := atlas.toC1ExtensionAtlas
  have hn : 0 < n := Fact.out
  let : Fact (1 ≤ (((2 * n : ℕ) : NNReal) : ℝ≥0∞)) :=
    ⟨by exact_mod_cast (by omega : 1 ≤ 2 * n)⟩
  obtain ⟨W, hW⟩ := hall (k + n + 1)
  obtain ⟨jet, hjet⟩ := exists_supercriticalSobolevJet atlas k W
  obtain ⟨w, hw, _, hwae⟩ := exists_contDiffUpToBoundary_representative_of_dimension_lt
    (by exact_mod_cast (by omega : 1 < 2 * n))
    (by exact_mod_cast (by omega : n < 2 * n)) (by rfl : k + 1 ≤ k + 1) jet
  have heq : EqOn v w Ω :=
    Measure.eqOn_open_of_ae_eq (hvae.trans (hwae.trans (hjet.trans hW)).symm) hopen
      (hv.continuousOn.mono subset_closure) hw.contDiffOn.continuousOn
  exact hw.congr hopen heq

end SobolevSpace.GraphSpace.BoundaryRegularity
