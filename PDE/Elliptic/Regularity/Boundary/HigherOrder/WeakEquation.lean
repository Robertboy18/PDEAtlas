/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.ChartWeakEquation
public import PDE.Elliptic.Regularity.Boundary.Domain
public import PDE.Elliptic.Variational.DivergenceForm
import PDE.Elliptic.Regularity.Boundary.HalfSpaceWeakEquation
import PDE.Elliptic.Regularity.Boundary.HigherOrder.ForcingTransport
import PDE.Elliptic.Regularity.Localization.HigherOrderCutoffEquation
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Arbitrary-order flattened boundary equation

The boundary step of the higher-order regularity bootstrap. Let
`U ∈ W^{k+1,2}(Ω)` have zero trace and solve `-∂ᵢ(aᵢⱼ ∂ⱼ U) = F` weakly with
`aᵢⱼ ∈ W^{k+1,∞}(Ω)` and `F ∈ W^{k,2}(Ω)`. Multiplying by the boundary
cutoff of a chart gives a localized zero-trace solution whose commutator
forcing is again in `W^{k,2}(Ω)` and is supported near that chart.
Transporting the forcing through the chart gives a `W^{k,2}` forcing on the
upper half-space, and the flattened localized field satisfies the flattened
weak equation with that forcing and the extended principal coefficient.

## Main results

* `exists_flattenedLocalized_equation_on_upper`: for every `k > 0`, the
  flattened localized field satisfies a weak divergence-form equation on `Ω⁺`
  with a `W^{k,2}(Ω⁺)` forcing. The case `k = 1` is the forcing used in the
  first boundary successor step.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, step 5 of the proof of Theorem 5 (the general case,
  by straightening the boundary as in the proof of Theorem 4), p. 343.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} [Fact (0 < n)]

/--
For every positive `k`, boundary localization and flattening produce a
`W^{k,2}` forcing on the upper half-space satisfying the flattened weak
equation. The case `k = 1` is the forcing construction used in the first
boundary successor step.
-/
theorem exists_flattenedLocalized_equation_on_upper
    (k : ℕ) (hk : 0 < k)
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (i : Fin hOmega.toC1ExtensionAtlas.N)
    (hChartSymm : ContDiff ℝ (k + 1)
      (fun y ↦ (hOmega.toC1ExtensionAtlas.chart i).symm y))
    (A : Fin n → Fin n → W^{k + 1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ r s,
      ((((A r s : WkpAmbientOn n (k + 1) ∞ Omega)
        (baseIndex n (k + 1)) : DerivLp n ∞ Omega) : ℝ^n → ℝ)) =ᵐ[domainMeasure n
          Omega] fun x ↦ a x r s)
    (F : W^{k,2}(Omega))
    (U : W^{k + 1,2}(Omega))
    (htrace0 :
      lowerOrderCLM
          (n := n) (p := 2) (Ω := Omega) (by omega) U ∈
        (h10SubmoduleOn (n := n) (Ω := Omega)).toSubmodule)
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (fun r s ↦ ((A r s : WkpAmbientOn n (k + 1) ∞ Omega)
        (baseIndex n (k + 1)) : DerivLp n ∞ Omega))
      ((F : WkpAmbientOn n k 2 Omega) (baseIndex n k) :
        DerivLp n 2 Omega)
      ⟨lowerOrderCLM
          (n := n) (p := 2) (Ω := Omega) (by omega) U,
        htrace0⟩)
    (beta : ℝ) :
    ∃ upperForcing : W^{k,2}(HalfSpace.upper n),
      ∀ phi : TestFunctionOn n (HalfSpace.upper n),
        (∫ y,
            principalPairing
              (extendedFlattenedPrincipalCoefficientAt (n := n)
                hOmega.toC1ExtensionAtlas i beta a y)
              (fun j ↦ flattenedChartGradient hOmega.toC1ExtensionAtlas i
                (lowerOrderCLM
                  (n := n) (p := 2) (Ω := Omega) (by omega) U) j y)
              (fun j ↦ (∂[j] phi.1.toFun) y)
          ∂domainMeasure n (HalfSpace.upper n)) =
          ∫ y,
            (((upperForcing : WkpAmbientOn n k 2 (HalfSpace.upper n))
              (baseIndex n k) : DerivLp n 2 (HalfSpace.upper n)) :
              ℝ^n → ℝ) y * phi.1.toFun y
            ∂domainMeasure n (HalfSpace.upper n) := by
  classical
  let hC1 := hOmega.toC1ExtensionAtlas
  obtain ⟨w, hwBase, G, hGSupport, hGw⟩ := exists_localized_weakDivergenceSolution_higher
    k hk hC1.isOpen A F U htrace0 hu (hC1.boundaryCutoff i)
  let g : DerivLp n 2 Omega := (G : WkpAmbientOn n k 2 Omega) (baseIndex n k)
  have hwEq : (w : H¹(Omega)) = cutoffCLM (n := n) (p := 2) (Ω := Omega) (hC1.boundaryCutoff i)
      (lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (by omega) U) := by
    apply WkpSpaceOn.ext_of_base_ae hC1.isOpen
    exact hwBase.trans (by simpa using (cutoffCLM_base_apply_ae (n := n) (p := 2) (Ω := Omega)
      (hC1.boundaryCutoff i) (lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (by omega) U)).symm)
  obtain ⟨upperForcing, hUpperForcing⟩ :=
    exists_flattenedForcing k hk hOmega i hChartSymm G hGSupport
  refine ⟨upperForcing, fun phi ↦ ?_⟩
  have hupper := (LocalizedChartEquationData.of_localized_weak_divergence_solution hC1 i _ a
    haRep _ w g hwEq hGSupport hGw).weakEquation_on_upper beta phi
  calc _ = ∫ y, (Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Omega) i).target.indicator
          (flattenedForcing (n := n) (Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n)
            (Ω := Omega) i) (g : ℝ^n → ℝ)) y * phi.1.toFun y
          ∂domainMeasure n (HalfSpace.upper n) := by simpa [hC1] using hupper
    _ = _ := integral_congr_ae (hUpperForcing.mono fun y hy ↦ congrArg (· * phi.1.toFun y) hy.symm)

end SobolevSpace.GraphSpace.BoundaryRegularity
