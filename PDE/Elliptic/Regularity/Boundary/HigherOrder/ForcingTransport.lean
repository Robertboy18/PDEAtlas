/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.ChartCoefficients
public import PDE.Elliptic.Regularity.Boundary.Domain
public import PDE.Spaces.Sobolev.GraphSpace.Model.Notation
import Mathlib.Analysis.Calculus.Deriv.Abs
import PDE.Elliptic.Regularity.Boundary.ChartCoefficientRegularity
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.Integrability
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.LocalizedPullback
import PDE.Spaces.Sobolev.Extension.Pullback.HigherOrder
import PDE.Spaces.Sobolev.Localization.Cutoff.HigherOrderExtension

/-!
# Arbitrary-order transport of boundary forcing

When a divergence-form equation is flattened through a boundary chart `Φ`,
a forcing `G` on `Ω` becomes the Jacobian-weighted pullback
`y ↦ |det D(Φ⁻¹)(y)| · G(Φ⁻¹(y))` on the chart target, extended by zero to
the whole upper half-space `Ω⁺`. We show that the transported forcing
keeps the Sobolev regularity of `G`: a `W^{k,2}(Ω)` forcing supported in the
boundary support of the chart yields a `W^{k,2}(Ω⁺)` forcing, provided the
inverse chart is `C^{k+1}`.

## Main results

* `exists_flattenedForcing`: existence of the transported
  `W^{k,2}(Ω⁺)` forcing and its almost-everywhere identification with the
  weighted pullback `flattenedForcing` extended by zero from the chart
  target.

## Implementation notes

One more derivative is required of the inverse chart than of the forcing
because the Jacobian weight is itself differentiated `k` times. The support
hypothesis `hGPhysical` is what makes the zero extension from the chart
target harmless.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, step 8 of the proof of Theorem 4 (the transformed
  equation), (61)-(68), pp. 338-339, and step 5 of the proof of Theorem 5, p. 343.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set Function ENNReal
open SobolevSpace.Boundary.C1ExtensionAtlas.DerivedCutoffs
open SobolevSpace.CompactSupportLocalization
open scoped Topology Sobolev

variable {n : ℕ} [Fact (0 < n)]

/-- A physically supported `W^{k,2}` forcing pulls forward to a `W^{k,2}`
forcing on the upper half-space after multiplication by the inverse-chart
Jacobian and extension by zero from the chart target. -/
theorem exists_flattenedForcing
    (k : ℕ) (hk : 0 < k)
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (i : Fin hOmega.toC1ExtensionAtlas.N)
    (hChartSymm : ContDiff ℝ (k + 1)
      (fun y ↦ (hOmega.toC1ExtensionAtlas.chart i).symm y))
    (G : W^{k,2}(Omega))
    (hGPhysical :
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupport
        (hΩ := hOmega.toC1ExtensionAtlas) i).indicator
          ((((G : WkpAmbientOn n k 2 Omega) (baseIndex n k) :
            DerivLp n 2 Omega) : ℝ^n → ℝ)) =ᵐ[domainMeasure n Omega]
          (((G : WkpAmbientOn n k 2 Omega) (baseIndex n k) :
            DerivLp n 2 Omega) : ℝ^n → ℝ)) :
    ∃ F : W^{k,2}(SobolevSpace.HalfSpace.upper n),
      baseRepresentative F
        =ᵐ[domainMeasure n (SobolevSpace.HalfSpace.upper n)]
        (let E := Boundary.C1ExtensionAtlas.Charts.chartOnΩ
          (hΩ := hOmega.toC1ExtensionAtlas) i
         E.target.indicator
          (flattenedForcing (n := n) E
            (((G : WkpAmbientOn n k 2 Omega) (baseIndex n k) :
              DerivLp n 2 Omega) : ℝ^n → ℝ))) := by
  classical
  let hC1 := hOmega.toC1ExtensionAtlas
  let upper := SobolevSpace.HalfSpace.upper n
  let EFull := hC1.chart i
  let E := Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Omega) i
  let eta := targetSupportCutoff (n := n) (Ω := Omega) i
  let K := boundarySupport (n := n) (Ω := Omega) i
  let KT := boundarySupportInTarget (n := n) (Ω := Omega) i
  let g : ℝ^n → ℝ := baseRepresentative G
  have hTargetEq : E.target = EFull.target ∩ upper :=
    Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_eq_target_inter_upper i
  have hTargetSubFull : E.target ⊆ EFull.target := hTargetEq ▸ inter_subset_left
  have hSourceSub : E.source ⊆ Omega := fun _ hx ↦ hx.2
  have hTargetBounded : Bornology.IsBounded E.target :=
    (hC1.chart_target_bounded i).subset hTargetSubFull
  have hEOne : ContDiff ℝ 1 (fun x ↦ E x) := (hOmega.chart_contDiff_two i).of_le (by norm_num)
  have hEsymmSucc : ContDiff ℝ (k + 1) (fun y ↦ E.symm y) := hChartSymm
  have hqmp := SobolevSpace.WeakChangeOfVariables.quasiMeasurePreserving_partialHomeomorph
    (E := E.symm) (hEsymmSucc.of_le (by simp)) hEOne
  let GSource : W^{k,2}(E.source) :=
    restrictCLM (n := n) (k := k) (p := 2) E.open_source.measurableSet hSourceSub G
  obtain ⟨P, hPBase⟩ : ∃ P : W^{k,2}(E.target),
      baseRepresentative P =ᵐ[domainMeasure n E.target] fun y ↦ g (E.symm y) :=
    let ⟨P, hP⟩ := SobolevSpace.WeakChangeOfVariables.exists_WkTwo_pullback_on_bounded_chart k hk
      (SobolevSpace.Approximation.standardMollifier n) (E := E.symm) (hEsymmSucc.of_le (by simp))
      hEOne hTargetBounded (hC1.bounded.subset hSourceSub) GSource
    ⟨P, hP.trans (hqmp.ae_eq_comp (restrictCLM_apply_ae (p := 2) E.open_source.measurableSet
      hSourceSub G (baseIndex n k)))⟩
  have hTargetSupport : KT.indicator (fun y ↦ g (E.symm y)) =ᵐ[domainMeasure n E.target]
      fun y ↦ g (E.symm y) := by
    filter_upwards [hqmp.ae_eq_comp (hGPhysical.filter_mono (ae_mono (domainMeasure_le
      hSourceSub))), ae_restrict_mem E.open_target.measurableSet] with y hySupport hyTarget
    have hyK : E.symm y ∈ K ↔ y ∈ KT := by
      refine ⟨fun hxK ↦ ⟨EFull.symm y, hxK, EFull.right_inv (hTargetSubFull hyTarget)⟩, ?_⟩
      rintro ⟨x, hxK, rfl⟩
      rwa [show E.symm (EFull x) = x from EFull.left_inv
        (boundarySupport_subset_source (n := n) (Ω := Omega) i hxK)]
    by_cases hxK : E.symm y ∈ K
    · rw [Set.indicator_of_mem (hyK.1 hxK)]
    · rw [Set.indicator_of_notMem (fun hy ↦ hxK (hyK.2 hy))]
      exact (Set.indicator_of_notMem hxK _).symm.trans hySupport
  let jLocalized : ℝ^n → ℝ := fun y ↦ eta.toFun y * inverseChartJacobianWeight (n := n) EFull y
  have hEtaSupport : tsupport eta.toFun ⊆ EFull.target :=
    tsupport_targetSupportCutoff_subset_target (n := n) (Ω := Omega) i
  have hJOn : ContDiffOn ℝ k (inverseChartJacobianWeight (n := n) EFull) EFull.target :=
    (contDiff_det_fderiv (m := k) (fun y ↦ EFull.symm y) hChartSymm).contDiffOn.abs fun y hy ↦
      abs_pos.mp (inverseChartJacobianWeight_pos_on_target EFull hEOne
        (hChartSymm.of_le (by simp)) hy)
  have hJLocalized : ContDiff ℝ k jLocalized := contDiff_iff_contDiffAt.2 fun y ↦ by
    by_cases hy : y ∈ EFull.target
    · exact (eta.contDiff.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.mul
        (hJOn.contDiffAt (EFull.open_target.mem_nhds hy))
    · refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hy (hEtaSupport h)] with z hz
      simp only [jLocalized, hz, Pi.zero_apply, zero_mul]
  have hJMem (a : DerivIndex n k) : MemLp (fun y ↦ iteratedPartialDeriv (n := n) a.toList
      jLocalized y) ∞ (domainMeasure n E.target) :=
    SobolevSpace.WeakChangeOfVariables.memLp_top_on_bounded_of_continuous hTargetBounded
      (PDE.contDiff_iteratedPartialDeriv_of_le hJLocalized a.toList
        (by exact_mod_cast a.toList_length_le)).continuous
  let J : W^{k,∞}(E.target) := mkWkpSpaceOnOfContDiffMemLpFinite
    (n := n) (k := k) (p := ∞) (Ω := E.target) (f := jLocalized) hJLocalized hJMem
  have hJBase : baseRepresentative J =ᵐ[domainMeasure n E.target] jLocalized := by
    simpa [J, baseRepresentative, baseIndex_toList, iteratedPartialDeriv] using
      mkWkpSpaceOnOfContDiffMemLpFinite_apply_ae (Ω := E.target) jLocalized hJLocalized hJMem
        (baseIndex n k)
  let Q : W^{k,2}(E.target) := wkTopProduct (n := n) (Ω := E.target) hk E.open_target J P
  have hEtaForcing : (fun y ↦ eta.toFun y * flattenedForcing (n := n) E g y)
      =ᵐ[domainMeasure n E.target] flattenedForcing (n := n) E g := by
    filter_upwards [hTargetSupport] with y hySupport
    by_cases hyKT : y ∈ KT
    · rw [targetSupportCutoff_eq_one_on_boundarySupportInTarget i y hyKT, one_mul]
    · rw [Set.indicator_of_notMem hyKT] at hySupport
      simp [flattenedForcing, ← hySupport]
  have hQBase : baseRepresentative Q =ᵐ[domainMeasure n E.target] flattenedForcing (n := n) E g :=
    (Filter.EventuallyEq.trans (by
      filter_upwards [wkTopProduct_base_ae hk E.open_target J P, hJBase, hPBase]
        with y hyQ hyJ hyP
      rw [hyQ, hyJ, hyP]
      exact mul_assoc _ _ _) hEtaForcing)
  have hTargetInterOpen : IsOpen (EFull.target ∩ upper) :=
    EFull.open_target.inter (SobolevSpace.HalfSpace.isOpen_upper (n := n))
  have hTargetInterSub : EFull.target ∩ upper ⊆ E.target := hTargetEq.ge
  let Q' : W^{k,2}(EFull.target ∩ upper) := restrictCLM (n := n) (k := k) (p := 2)
    hTargetInterOpen.measurableSet hTargetInterSub Q
  have hμ : domainMeasure n (EFull.target ∩ upper) = domainMeasure n E.target := by
    rw [hTargetEq]
  have hQ' : baseRepresentative Q' =ᵐ[domainMeasure n E.target] flattenedForcing (n := n) E g := by
    rw [← hμ]
    exact (restrictCLM_apply_ae (p := 2) hTargetInterOpen.measurableSet hTargetInterSub Q
      (baseIndex n k)).trans (hQBase.filter_mono (ae_mono hμ.le))
  refine ⟨HigherOrderLocalizedCutoff.interCutoff (n := n) (k := k) (p := 2) EFull.open_target
    (SobolevSpace.HalfSpace.isOpen_upper (n := n)) eta hEtaSupport Q', ?_⟩
  refine (HigherOrderLocalizedCutoff.interCutoff_base_ae _ _ _ _ _).trans
    (ae_of_ae_restrict_of_ae_restrict_compl EFull.target ?_ ?_)
  · rw [show (domainMeasure n upper).restrict EFull.target = domainMeasure n E.target by
      rw [← hμ, domainMeasure, Measure.restrict_restrict EFull.open_target.measurableSet]]
    filter_upwards [hQ', hEtaForcing, ae_restrict_mem E.open_target.measurableSet]
      with y hyQ hyEta hyTarget
    rw [hyQ, hyEta, Set.indicator_of_mem hyTarget]
    rfl
  · filter_upwards [ae_restrict_mem EFull.open_target.measurableSet.compl] with y hy
    rw [image_eq_zero_of_notMem_tsupport fun h ↦ hy (hEtaSupport h), zero_mul,
      Set.indicator_of_notMem fun h ↦ hy (hTargetSubFull h)]

end SobolevSpace.GraphSpace.BoundaryRegularity
