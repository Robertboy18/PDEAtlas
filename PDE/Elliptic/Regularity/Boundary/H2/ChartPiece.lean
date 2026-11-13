/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.H2.ReflectedPullback
public import PDE.Elliptic.Regularity.Boundary.CoefficientGeometry
public import PDE.Elliptic.Regularity.Boundary.Domain
public import PDE.Elliptic.Regularity.Boundary.ZeroTracePullback
import PDE.Elliptic.Regularity.Boundary.H2.FlattenedEstimate
import PDE.Spaces.Sobolev.Calculus.Pullback.SupportBuffer
import PDE.Spaces.Sobolev.Extension.C1.Assembly.BoundaryPiece.Agreement
import PDE.Spaces.Sobolev.Extension.C1.Assembly.BoundaryPiece.Coordinates
public import PDE.Elliptic.Variational.DivergenceForm

/-!
# Boundary `H²` chart piece

A zero-trace localized solution that has gained `H²` regularity in flattened upper-half-space
coordinates is reflected oddly, relocalized inside the full chart target, pulled back through the
`C²` chart, and restricted to the physical domain.

## Main results

* `exists_boundaryChart_h2_localized_piece_of_flattened`: a flattened `H²` representative of the
  localized Dirichlet field gives an `H²(Ω)` representative of the partition piece `ψᵢ u`.
* `exists_boundaryChart_h2_localized_piece`: for a `C²` domain and `C¹` principal coefficients,
  every boundary partition piece of a weak Dirichlet solution belongs to `H²(Ω)`.

## How it works

Evans flattens the boundary on a half-ball `U'` inside the chart image, proves `u' ∈ H²(V')` on the
smaller half-ball `V'`, and changes variables back to obtain (71) on `V = Ψ(V')` (steps 7 and 10 of
the proof of §6.3.2, Theorem 4). Our flattened piece is `H²` on the whole upper half-space
(`exists_flattenedBoundary_h2_of_c2_boundary_atlas`). A pullback applied directly on compact subsets
of `chart.target ∩ upper` would stay away from the flat boundary and so lose the physical boundary.
We therefore first reflect the piece oddly across the flat boundary with
`oddReflectionH2OfBaseAEEqH10`, which is valid because the flattened Dirichlet field belongs to
`H¹₀`. A cutoff localizes the reflected field inside the chart target, the buffered `C²` pullback
`targetSubsetBufferedH2PullbackExtension` carries it to physical coordinates, and restriction gives
a field on the domain.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, steps 6-7 and 10 of the proof of Theorem 4, (57)-(60)
  and (71), pp. 337-340.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open SobolevSpace.Boundary.C1ExtensionAtlas.DerivedCutoffs
open scoped ENNReal

variable {n : ℕ} [Fact (0 < n)]

/-- A flattened `H²` representative of the localized Dirichlet field yields
an `H²(Ω)` representative of the corresponding partition-of-unity
piece `ψᵢ u`.

All support cutoffs are constructed from the `C²` domain structure. -/
theorem exists_boundaryChart_h2_localized_piece_of_flattened
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (i : Fin hOmega.toC1ExtensionAtlas.N)
    (u : H¹₀(Omega))
    (U : W^{2,2}(HalfSpace.upper n))
    (hU :
      ⇑((U : WkpAmbientOn n 2 2 (HalfSpace.upper n))
          (baseIndex n 2) : DerivLp n 2 (HalfSpace.upper n))
        =ᵐ[domainMeasure n (HalfSpace.upper n)]
          ⇑((((Extension.C1.BoundaryPiece.flattenH10
              hOmega.toC1ExtensionAtlas i u :
                H¹₀(HalfSpace.upper n)) :
              H¹(HalfSpace.upper n)) :
                WkpAmbientOn n 1 2 (HalfSpace.upper n))
              (baseIndex n 1) : DerivLp n 2 (HalfSpace.upper n))) :
    ∃ W : W^{2,2}(Omega),
      baseRepresentative W =ᵐ[domainMeasure n Omega]
        (fun x ↦ (hOmega.toC1ExtensionAtlas.boundaryCutoff i).toFun x *
          ⇑(((u : H¹(Omega)) : WkpAmbientOn n 1 2 Omega)
            (baseIndex n 1) : DerivLp n 2 Omega) x) := by
  classical
  let hC1 := hOmega.toC1ExtensionAtlas
  let upper := HalfSpace.upper n
  let uFlat : H¹₀(upper) := Extension.C1.BoundaryPiece.flattenH10 hC1 i u
  let eta := targetSupportCutoff (n := n) (Ω := Omega) i
  let E := hC1.chart i
  let EOmega := Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Omega) i
  let K0 := targetCutoffSupport (n := n) (Ω := Omega) i
  let R := oddReflectionH2OfBaseAEEqH10 U uFlat hU
  obtain ⟨T, hT⟩ : ∃ T : W^{2,2}((Set.univ : Set (ℝ^n))), baseRepresentative T
      =ᵐ[domainMeasure n Set.univ] fun x ↦ eta.toFun x * baseRepresentative R x :=
    ⟨_, CompactSupportLocalization.HigherOrderLocalizedCutoff.extendByCutoff_base_ae
      isOpen_univ (subset_refl _) eta (subset_univ _) R⟩
  obtain ⟨bufferTarget, bufferSource, bufferCutoff, hbTc, hbTs, hbSo, hbSp, hbSs, hbCs, hbOne, -⟩ :=
    SobolevSpace.WeakChangeOfVariables.exists_pullback_support_buffer E
      (hOmega.chart_symm_contDiff_two i).continuous (K₀ := K0)
      (isCompact_targetCutoffSupport (n := n) (Ω := Omega) i)
      (targetCutoffSupport_subset_target (n := n) (Ω := Omega) i)
  obtain ⟨G, hG⟩ : ∃ G : W^{2,2}((Set.univ : Set (ℝ^n))), baseRepresentative G
      =ᵐ[domainMeasure n Set.univ] fun x ↦ bufferCutoff.toFun x * baseRepresentative T (E x) :=
    ⟨_, targetSubsetBufferedH2PullbackExtension_base_ae
      (SobolevSpace.Approximation.standardMollifier n) (E := E) (hOmega.chart_contDiff_two i)
      ((hOmega.chart_symm_contDiff_two i).of_le (by norm_num)) (TargetBig := Set.univ)
      (Omega := Set.univ) (subset_univ _) hbTc hbTs hbSo hbSp (hbSs.trans (subset_univ _))
      bufferCutoff hbCs T⟩
  refine ⟨restrictCLM (n := n) (k := 2) (p := 2) hC1.isOpen.measurableSet (subset_univ Omega) G,
    ?_⟩
  let flatBase : ℝ^n → ℝ := baseRepresentative (uFlat : H¹(upper))
  let localizedBase : ℝ^n → ℝ :=
    fun x ↦ (hC1.boundaryCutoff i).toFun x * baseRepresentative (u : H¹(Omega)) x
  let cutoffBase : ℝ^n → ℝ := baseRepresentative
    (cutoffCLM (n := n) (p := 2) (Ω := Omega) (hC1.boundaryCutoff i) (u : H¹(Omega)))
  have hEtaFlat : (fun y ↦ eta.toFun y * flatBase y) =ᵐ[domainMeasure n upper] flatBase := by
    filter_upwards [Extension.C1.BoundaryPiece.flattenCLM_base_boundarySupportInTarget_indicator_ae
      (p := 2) i (u : H¹(Omega))] with y hy
    by_cases hyKT : y ∈ boundarySupportInTarget (n := n) (Ω := Omega) i
    · rw [targetSupportCutoff_eq_one_on_boundarySupportInTarget i y hyKT, one_mul]
    · rw [Set.indicator_of_notMem hyKT] at hy
      rw [show flatBase y = 0 from hy.symm, mul_zero]
  have hTupper : baseRepresentative T =ᵐ[domainMeasure n upper] flatBase := by
    filter_upwards [hT.filter_mono (ae_mono (domainMeasure_le (subset_univ upper))),
      (oddReflectionH2OfBaseAEEqH10_base_ae_upper U uFlat hU).trans hU, hEtaFlat]
      with y hyT hyR hyEta
    rw [hyT, show baseRepresentative R y = flatBase y from hyR, hyEta]
  have hSourceValues : (fun x ↦ baseRepresentative T (E x)) =ᵐ[domainMeasure n EOmega.source]
      cutoffBase := by
    filter_upwards [(SobolevSpace.WeakChangeOfVariables.quasiMeasurePreserving_partialHomeomorph
      (E := EOmega) ((hOmega.chart_contDiff_two i).of_le (by norm_num))
      ((hOmega.chart_symm_contDiff_two i).of_le (by norm_num))).ae_eq_comp
        ((hTupper.filter_mono (ae_mono (domainMeasure_le
          (Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_subset_upper i)))).trans
        (Extension.C1.BoundaryPiece.flattenCLM_base_agree_ae (p := 2) i (u : H¹(Omega)))),
      ae_restrict_mem EOmega.open_source.measurableSet] with x hx hxSource
    exact hx.trans (congrArg cutoffBase (E.left_inv hxSource.1))
  have hcutoff : cutoffBase =ᵐ[domainMeasure n Omega] localizedBase :=
    cutoffCLM_base_apply_ae (hC1.boundaryCutoff i) (u : H¹(Omega))
  have hbuf (x : ℝ^n) : bufferCutoff.toFun x * localizedBase x = localizedBase x := by
    by_cases hpsi : (hC1.boundaryCutoff i).toFun x = 0
    · simp only [localizedBase, hpsi, zero_mul, mul_zero]
    · have hxK : x ∈ boundarySupport (n := n) (Ω := Omega) i := subset_tsupport _ hpsi
      have hηx : eta.toFun (E x) ≠ 0 := by
        rw [targetSupportCutoff_eq_one_on_boundarySupportInTarget i (E x) ⟨x, hxK, rfl⟩]
        exact one_ne_zero
      rw [hbOne x ⟨E x, subset_tsupport _ hηx, E.left_inv (hC1.boundaryCutoff_support i hxK)⟩,
        one_mul]
  have hW := restrictCLM_apply_ae (p := 2) hC1.isOpen.measurableSet (subset_univ Omega) G
    (baseIndex n 2)
  have hGO := hG.filter_mono (ae_mono (domainMeasure_le (subset_univ Omega)))
  have hle := ae_mono (domainMeasure_le (n := n) (show EOmega.source ⊆ Omega from fun _ hx ↦ hx.2))
  refine ae_of_ae_restrict_of_ae_restrict_compl E.source ?_ ?_
  · rw [show (domainMeasure n Omega).restrict E.source = domainMeasure n EOmega.source from
      Measure.restrict_restrict E.open_source.measurableSet]
    filter_upwards [hW.filter_mono hle, hGO.filter_mono hle, hSourceValues,
      hcutoff.filter_mono hle] with x hxW hxG hxS hxC
    refine hxW.trans (hxG.trans ?_)
    rw [hxS, hxC]
    exact hbuf x
  · filter_upwards [ae_restrict_mem E.open_source.measurableSet.compl, ae_restrict_of_ae hW,
      ae_restrict_of_ae hGO] with x hx hxW hxG
    refine hxW.trans (hxG.trans ?_)
    rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hbSs (hbCs h)), zero_mul,
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (hC1.boundaryCutoff_support i h), zero_mul]

/-- Local boundary regularity in physical coordinates, our counterpart of (71)
in step 10 of Evans's proof of §6.3.2, Theorem 4.

For a bounded domain equipped with `C2BoundaryAtlas`, uniformly elliptic
principal coefficients admitting global `C¹` representatives, and an `L²`
forcing term, every boundary partition piece of a weak Dirichlet solution
belongs to `H²(Ω)`.  The flattened equation, geometric ellipticity constants,
odd reflection, and chart pullback are all discharged internally. -/
theorem exists_boundaryChart_h2_localized_piece
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (i : Fin hOmega.toC1ExtensionAtlas.N)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ r s,
      ⇑((A r s : WkpAmbientOn n 1 ∞ Omega)
          (baseIndex n 1) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x r s)
    (haC1 : ∀ r s, ContDiff ℝ 1 (fun x ↦ a x r s))
    (f : DerivLp n 2 Omega)
    (u : H¹₀(Omega))
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (fun r s ↦ ((A r s : WkpAmbientOn n 1 ∞ Omega)
        (baseIndex n 1) : DerivLp n ∞ Omega)) f u)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hPhysical : ∀ x ∈ Omega,
      MatrixEllipticLowerBound (a x) alpha) :
    ∃ W : W^{2,2}(Omega),
      baseRepresentative W =ᵐ[domainMeasure n Omega]
        (fun x ↦ (hOmega.toC1ExtensionAtlas.boundaryCutoff i).toFun x *
          ⇑(((u : H¹(Omega)) : WkpAmbientOn n 1 2 Omega)
            (baseIndex n 1) : DerivLp n 2 Omega) x) := by
  obtain ⟨U, hU⟩ :=
    exists_flattenedBoundary_h2_of_c2_boundary_atlas
      hOmega i A a haRep haC1 f u hu alpha halpha hPhysical
  exact exists_boundaryChart_h2_localized_piece_of_flattened
    hOmega i u U hU

end SobolevSpace.GraphSpace.BoundaryRegularity
