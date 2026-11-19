/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.Domain
public import PDE.Elliptic.Regularity.Boundary.ZeroTracePullback
import PDE.Spaces.Sobolev.Extension.C1.Assembly.BoundaryPiece.Agreement
import PDE.Spaces.Sobolev.Extension.Pullback.HigherOrder

/-!
# Higher-order boundary chart pullback

In the boundary regularity bootstrap, a Dirichlet solution `u ∈ H¹₀(Ω)` is
localized by the boundary cutoff `ζᵢ` of a chart, flattened through the chart
to the half-space `Ω⁺`, and shown there to have a `W^{k,2}(Ω⁺)`
representative `U`. We perform the return trip: `U` is pulled back
through the chart and shown to be a `W^{k,2}(Ω)` representative of the
localized piece `ζᵢ u`.

## Main results

* `exists_boundaryChart_pullback_localized_piece`: if `U ∈ W^{k,2}(Ω⁺)`
  represents the flattened localized field, then `ζᵢ u` has a `W^{k,2}(Ω)`
  representative. Only the selected forward chart needs `C^k` regularity; the
  inverse chart is used with the `C¹` regularity carried by the atlas.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, step 10 of the proof of Theorem 4, (71), p. 340, and
  step 5 of the proof of Theorem 5, p. 343.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open SobolevSpace.CompactSupportLocalization
open scoped ENNReal

variable {n : ℕ} [Fact (0 < n)]

/-- A flattened `W^{k,2}` representative of a localized Dirichlet field gives
the corresponding physical partition piece in `W^{k,2}(Omega)`.

Only the selected forward chart requires `C^k` regularity. The inverse chart
uses the `C^1` regularity already included in the domain data. -/
theorem exists_boundaryChart_pullback_localized_piece
    (k : ℕ) (hk : 0 < k)
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (i : Fin hOmega.toC1ExtensionAtlas.N)
    (hChart : ContDiff ℝ k
      (fun x ↦ hOmega.toC1ExtensionAtlas.chart i x))
    (u : H¹₀(Omega))
    (U : W^{k,2}(HalfSpace.upper n))
    (hU :
      ⇑((U : WkpAmbientOn n k 2 (HalfSpace.upper n))
          (baseIndex n k) : DerivLp n 2 (HalfSpace.upper n))
        =ᵐ[domainMeasure n (HalfSpace.upper n)]
            ⇑((((Extension.C1.BoundaryPiece.flattenH10
              hOmega.toC1ExtensionAtlas i u :
                H¹₀(HalfSpace.upper n)) :
              H¹(HalfSpace.upper n)) :
                WkpAmbientOn n 1 2 (HalfSpace.upper n))
              (baseIndex n 1) : DerivLp n 2 (HalfSpace.upper n))) :
    ∃ W : W^{k,2}(Omega),
      ⇑((W : WkpAmbientOn n k 2 Omega)
          (baseIndex n k) : DerivLp n 2 Omega)
        =ᵐ[domainMeasure n Omega]
          fun x ↦ (hOmega.toC1ExtensionAtlas.boundaryCutoff i).toFun x *
            ⇑(((u : H¹(Omega)) : WkpAmbientOn n 1 2 Omega)
              (baseIndex n 1) : DerivLp n 2 Omega) x := by
  classical
  let hC1 := hOmega.toC1ExtensionAtlas
  let E := hC1.chart i
  let EOmega := Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Omega) i
  let cutoffBase : ℝ^n → ℝ := baseRepresentative
    (cutoffCLM (n := n) (p := 2) (Ω := Omega) (hC1.boundaryCutoff i) (u : H¹(Omega)))
  let localizedBase : ℝ^n → ℝ :=
    fun x ↦ (hC1.boundaryCutoff i).toFun x * baseRepresentative (u : H¹(Omega)) x
  have htargetUpper : EOmega.target ⊆ HalfSpace.upper n :=
    Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_subset_upper i
  let UT : W^{k,2}(EOmega.target) :=
    restrictCLM (n := n) (k := k) (p := 2) EOmega.open_target.measurableSet htargetUpper U
  have hEOmegaK : ContDiff ℝ k (fun x ↦ EOmega x) := hChart
  have hEOmegaSymm : ContDiff ℝ 1 (fun y ↦ EOmega.symm y) := hC1.chart_symm_contDiff i
  have hsourceSub : EOmega.source ⊆ Omega := fun _ hx ↦ hx.2
  obtain ⟨P, hP⟩ := SobolevSpace.WeakChangeOfVariables.exists_WkTwo_pullback_on_bounded_chart k hk
    (SobolevSpace.Approximation.standardMollifier n) hEOmegaK hEOmegaSymm
    (hC1.bounded.subset hsourceSub) ((hC1.chart_target_bounded i).subset fun _ hy ↦ hy.1) UT
  have hPloc : baseRepresentative P =ᵐ[domainMeasure n EOmega.source] localizedBase := by
    refine hP.trans (Filter.EventuallyEq.trans ?_ ((cutoffCLM_base_apply_ae
      (hC1.boundaryCutoff i) (u : H¹(Omega))).filter_mono (ae_mono (domainMeasure_le hsourceSub))))
    filter_upwards [(SobolevSpace.WeakChangeOfVariables.quasiMeasurePreserving_partialHomeomorph
      (E := EOmega) (hEOmegaK.of_le (by exact_mod_cast hk)) hEOmegaSymm).ae_eq_comp
        ((restrictCLM_apply_ae (p := 2) EOmega.open_target.measurableSet htargetUpper U
          (baseIndex n k)).trans ((hU.filter_mono (ae_mono (domainMeasure_le htargetUpper))).trans
            (Extension.C1.BoundaryPiece.flattenCLM_base_agree_ae (p := 2) i (u : H¹(Omega))))),
      ae_restrict_mem EOmega.open_source.measurableSet] with x hx hxSource
    exact hx.trans (congrArg cutoffBase (E.left_inv hxSource.1))
  obtain ⟨chi, hchiSource, hchiOne, -, -⟩ := TestFunction.exists_eq_one_on_compact E.open_source
    (Boundary.C1ExtensionAtlas.DerivedCutoffs.isCompact_boundarySupport (n := n) (Ω := Omega) i)
    (Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupport_subset_source (n := n) (Ω := Omega) i)
  have hchi (x : ℝ^n) : chi.toFun x * localizedBase x = localizedBase x := by
    by_cases hpsi : (hC1.boundaryCutoff i).toFun x = 0
    · simp only [localizedBase, hpsi, zero_mul, mul_zero]
    · rw [hchiOne x (subset_tsupport _ hpsi), one_mul]
  refine ⟨HigherOrderLocalizedCutoff.interCutoff (n := n) (k := k) (p := 2) E.open_source
    hC1.isOpen chi hchiSource P, (HigherOrderLocalizedCutoff.interCutoff_base_ae _ _ _ _ _).trans
      (ae_of_ae_restrict_of_ae_restrict_compl E.source ?_ ?_)⟩
  · rw [show (domainMeasure n Omega).restrict E.source = domainMeasure n EOmega.source from
      Measure.restrict_restrict E.open_source.measurableSet]
    filter_upwards [hPloc] with x hx
    exact (congrArg (chi.toFun x * ·) hx).trans (hchi x)
  · filter_upwards [ae_restrict_mem E.open_source.measurableSet.compl] with x hx
    rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hchiSource h), zero_mul,
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (hC1.boundaryCutoff_support i h), zero_mul]

end SobolevSpace.GraphSpace.BoundaryRegularity
