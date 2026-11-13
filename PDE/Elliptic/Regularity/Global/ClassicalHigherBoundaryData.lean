/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.GeometricAtlas
public import PDE.Elliptic.Regularity.Global.ShiftedDivergenceHigherEstimate
public import PDE.Spaces.Sobolev.Extension.C1.ClassicalHigherOrder

/-!
# Global higher elliptic regularity from classical closure data

Finite classical regularity of the coefficients up to a bounded graph boundary supplies both their
Sobolev bundles and compact ambient principal representatives. Applying the global estimate then
gives the full divergence operator, including its drift and potential, with a constant chosen
independently of the forcing and weak solution
(`exists_global_higherOrder_estimate_of_contDiffUpToBoundary`).

At shift zero this is Evans's §6.3.2, Theorem 5 (Higher boundary regularity), with the hypotheses
(72) and (75) and the estimate (77). The coefficient and graph extensions are conclusions of the
construction, not hypotheses.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 5 (Higher boundary regularity), (72)-(77),
  pp. 340-341.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- `C^{m+1}` coefficients and a `C^{m+2}` graph boundary imply the full global
`H^{m+2}` estimate. The constant may depend on the fixed domain, order, coefficients,
ellipticity, and shift, but is fixed before the forcing and solution are chosen. -/
theorem exists_global_higherOrder_estimate_of_contDiffUpToBoundary (m : ℕ)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary (m + 2) Ω)
    (a : ℝ^n → Fin n → Fin n → ℝ) (b : Fin n → ℝ^n → ℝ) (c : ℝ^n → ℝ)
    (ha : ∀ i j, ContDiffUpToBoundary (m + 1) (fun x ↦ a x i j) Ω)
    (hb : ∀ i, ContDiffUpToBoundary (m + 1) (b i) Ω)
    (hc : ContDiffUpToBoundary (m + 1) c Ω)
    (lambda alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha) :
    ∃ K : ℝ, 0 < K ∧ ∀ (F : W^{m,2}(Ω)) (u : H¹₀(Ω)),
      IsWeakShiftedFullDivergenceSolution
        (fun i j ↦ (ha i j).toLp hopen hbounded ∞)
        (fun i ↦ (hb i).toLp hopen hbounded ∞) (hc.toLp hopen hbounded ∞)
        lambda (wkpBaseCoordinateCLM F) 0 u →
      ∃ W : W^{m + 2,2}(Ω),
        wkpBaseCoordinateCLM W = baseCoordCLM u ∧
        ‖W‖ ≤ K * (‖F‖ + ‖baseCoordCLM u‖) := by
  classical
  obtain ⟨atlas, hchart, hinv⟩ := hgraph.exists_higherOrderBoundaryAtlas m hopen hbounded
  have hgraph' : Boundary.HasContDiffGraphBoundary (m + 1) Ω :=
    hgraph.of_le (by norm_cast; omega)
  choose g hg _ hga using fun i j ↦
    (ha i j).exists_contDiff_succ_extension m hopen hbounded hgraph'
  let A : Fin n → Fin n → W^{m + 1,∞}(Ω) :=
    fun i j ↦ (ha i j).toWkpSpaceOn hopen hbounded ∞
  let B : Fin n → W^{m,∞}(Ω) :=
    fun i ↦ ((hb i).of_le (Nat.le_succ m)).toWkpSpaceOn hopen hbounded ∞
  let C : W^{m,∞}(Ω) :=
    (hc.of_le (Nat.le_succ m)).toWkpSpaceOn hopen hbounded ∞
  let aext : ℝ^n → Fin n → Fin n → ℝ := fun x i j ↦ g i j x
  have hrep (i j : Fin n) :
      (wkpBaseCoordinateCLM (A i j) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ aext x i j := by
    filter_upwards [(ha i j).toWkpSpaceOn_base_ae hopen hbounded ∞,
      ae_restrict_mem hopen.measurableSet] with x hx hxΩ
    exact hx.trans (hga i j hxΩ).symm
  have hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (aext x) alpha := by
    intro x hx
    have heq : aext x = a x := by
      funext i j
      exact hga i j hx
    rw [heq]
    exact hElliptic x hx
  obtain ⟨K, hK, hreg⟩ :=
    exists_global_higherOrder_estimate_of_weak_shifted_full_divergence_solution
      m atlas hchart hinv A aext hrep hg B C lambda alpha halpha hell
  refine ⟨K, hK, fun F u hu ↦ hreg F u ?_⟩
  simpa only [A, B, C, ContDiffUpToBoundary.toWkpSpaceOn_base_eq_toLp,
    ContDiffUpToBoundary.toLp] using hu

end SobolevSpace.GraphSpace.BoundaryRegularity
