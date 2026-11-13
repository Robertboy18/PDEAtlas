/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.GeometricAtlas
public import PDE.Elliptic.Regularity.Global.ShiftedDivergenceHigherEstimate
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData
import PDE.Spaces.Sobolev.Extension.C1.Classical
public import PDE.Spaces.Sobolev.GraphSpace.Operators.ZeroOrder

/-!
# Boundary regularity from classical coefficient data

For a bounded open set with `C²` graph boundary, principal coefficients that are `C¹` up to the
boundary give the full divergence-form `H²` estimate
(`exists_global_h2_estimate_of_contDiffUpToBoundary`). The lower-order coefficients need only belong
to `L^∞`. The boundary atlas, the Sobolev coefficient bundles and their ambient `C¹` representatives
are all constructed from the original data.

The conclusion includes the `L²` remainder and fixes its constant before the forcing and weak
solution are chosen. At shift zero this is Evans's §6.3.2, Theorem 4 (Boundary `H²`-regularity),
with the hypotheses (38) and (41) and the estimate (42).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 4 (Boundary H²-regularity), (38)-(42),
  p. 334.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- The full shifted divergence operator has the global `H²` estimate under `C²`
boundary geometry and classical `C¹` principal data up to the boundary. The drift and
potential are arbitrary `L^∞` classes, and the constant is independent of the forcing
and solution. No coefficient extension or Sobolev bundle is assumed. -/
theorem exists_global_h2_estimate_of_contDiffUpToBoundary
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (ha : ∀ i j, ContDiffUpToBoundary 1 (fun x ↦ a x i j) Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    (lambda alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : DerivLp n 2 Ω) (u : H¹₀(Ω)),
      IsWeakShiftedFullDivergenceSolution
        (fun i j ↦ (ha i j).toLp hopen hbounded ∞) b c lambda f 0 u →
      ∃ W : W^{2,2}(Ω),
        wkpBaseCoordinateCLM W = baseCoordCLM u ∧
        ‖W‖ ≤ K * (‖f‖ + ‖baseCoordCLM u‖) := by
  classical
  obtain ⟨atlas, hchart, _⟩ := hgraph.exists_c2BoundaryAtlas le_rfl hopen hbounded
  have hC1 : Boundary.HasC1GraphBoundary Ω := hgraph.hasC1GraphBoundary (by norm_num)
  choose g hg _ hga using fun i j ↦
    (ha i j).exists_contDiff_one_extension hopen hbounded hC1
  let A : Fin n → Fin n → W^{1,∞}(Ω) :=
    fun i j ↦ (ha i j).toWkpSpaceOn hopen hbounded ∞
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
      0 atlas (by simpa using hchart)
      (fun i ↦ atlas.toC1ExtensionAtlas.chart_symm_contDiff i)
      A aext hrep hg (fun i ↦ lpToZeroOrder (b i)) (lpToZeroOrder c)
      lambda alpha halpha hell
  refine ⟨K, hK, ?_⟩
  intro f u hu
  obtain ⟨W, hW, hbound⟩ := hreg (lpToZeroOrder f) u (by
    simpa only [A, ContDiffUpToBoundary.toWkpSpaceOn_base_eq_toLp,
      wkpBaseCoordinateCLM_lpToZeroOrder] using hu)
  exact ⟨W, hW, by simpa only [norm_lpToZeroOrder] using hbound⟩

end SobolevSpace.GraphSpace.BoundaryRegularity
