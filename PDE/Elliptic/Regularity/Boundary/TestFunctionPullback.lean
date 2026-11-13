/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions
public import PDE.Spaces.Sobolev.Variational.Spaces.H1
import PDE.DistributionTheory.TestFunction.CompactCutoff
import PDE.Spaces.Sobolev.Boundary.ZeroTrace.CompactSupport
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.ChangeOfVariables
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.Integrability
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.LocalizedPullback
import PDE.Spaces.Sobolev.Localization.Cutoff.CompactSupport

/-!
# Pulling test functions through boundary charts

To compare the flattened weak equation on the half-space with the original
equation on `Ω`, a test function `φ` compactly supported in the target of a
boundary chart `Φ` must be pulled back to an admissible `H¹₀(Ω)` test. The
pullback `φ ∘ Φ` is only defined on the chart source, so it is extended by
zero; the indicator is essential, and every identity below holds almost
everywhere on `Ω`.

## Main results

* `pullbackBase`, `pullbackDerivative`: the zero-extended pullback and the
  zero-extended chain-rule representatives
  `∑ⱼ (∂ⱼ φ)(Φ x) · (DΦ(x) eₖ)ⱼ` of its first derivatives.
* `exists_chartTest_pullback`: the pullback is an element of `H¹₀(Ω)` whose
  base coordinate is `pullbackBase` and whose derivative coordinates are
  `pullbackDerivative`, almost everywhere.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, steps 6-8 of the proof of Theorem 4 (straightening
  the boundary), (57)-(68), pp. 337-339.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace PDE.Elliptic.Regularity.Boundary.TestFunctionPullback

open MeasureTheory Set Function ENNReal
open scoped Topology BigOperators
open SobolevSpace
open SobolevSpace.GraphSpace

variable {n : ℕ} {Omega : Set (ℝ^n)}

variable [Fact (0 < n)]

/-- The literal zero extension of a target test function pulled back through a
boundary chart.  The indicator is essential: a boundary chart is only
invertible on its open source. -/
def pullbackBase
    (hOmega : Boundary.C1ExtensionAtlas n Omega) (i : Fin hOmega.N)
    (phi : TestFunctionOn n
      (Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Omega) i).target) :
    ℝ^n → ℝ :=
  let E := Boundary.C1ExtensionAtlas.Charts.chartOnΩ
    (n := n) (Ω := Omega) i
  E.source.indicator (fun x ↦ phi.1.toFun (E x))

/-- The zero-extended first-derivative representative given by the C¹
chain rule for `pullbackBase`. -/
def pullbackDerivative
    (hOmega : Boundary.C1ExtensionAtlas n Omega) (i : Fin hOmega.N)
    (phi : TestFunctionOn n
      (Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Omega) i).target)
    (k : Fin n) : ℝ^n → ℝ :=
  let E := Boundary.C1ExtensionAtlas.Charts.chartOnΩ
    (n := n) (Ω := Omega) i
  E.source.indicator fun x ↦
    ∑ j : Fin n, (∂[j] phi.1.toFun) (E x) *
      ((fderiv ℝ (fun z ↦ E z) x)
        (EuclideanSpace.single k (1 : ℝ))) j

/-- A compactly supported target test function can be pulled back through a
C¹ boundary chart and used as an `H¹₀(Omega)` test.  The returned Sobolev
coordinates are the literal zero extension and the first-order chain
rule representatives, almost everywhere.

This chart-test pullback is required in the boundary regularity argument of
Evans, *Partial Differential Equations*, 2nd ed., §6.3.2. -/
theorem exists_chartTest_pullback
    (hOmega : Boundary.C1ExtensionAtlas n Omega) (i : Fin hOmega.N)
    (phi : TestFunctionOn n
      (Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Omega) i).target) :
    ∃ Phi : H¹₀(Omega),
      (((((Phi.1 : WkpAmbientOn n 1 2 Omega) (baseIndex n 1) :
          DerivLp n 2 Omega) : ℝ^n → ℝ)) =ᵐ[domainMeasure n Omega]
            pullbackBase hOmega i phi) ∧
      ∀ k : Fin n,
        (((((Phi.1 : WkpAmbientOn n 1 2 Omega)
            (singleDerivIndex (n := n) k) : DerivLp n 2 Omega) : ℝ^n → ℝ))
          =ᵐ[domainMeasure n Omega] pullbackDerivative hOmega i phi k) := by
  classical
  let E := Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Omega) i
  let K : Set (ℝ^n) := tsupport phi.1.toFun
  let L : Set (ℝ^n) := E.symm '' K
  let b : ℝ^n → ℝ := pullbackBase hOmega i phi
  let db : Fin n → ℝ^n → ℝ := fun k ↦ pullbackDerivative hOmega i phi k
  have hE : ContDiff ℝ 1 (fun x ↦ E x) := hOmega.chart_contDiff i
  have hKcompact : IsCompact K := phi.1.hasCompactSupport
  have hKtarget : K ⊆ E.target := phi.2
  have hLcompact : IsCompact L := hKcompact.image (hOmega.chart_symm_contDiff i).continuous
  have hLsource : L ⊆ E.source := by
    rintro x ⟨y, hyK, rfl⟩
    exact E.map_target (hKtarget hyK)
  have hdphiCont (j : Fin n) : Continuous fun y ↦ (∂[j] phi.1.toFun) y :=
    (phi.1.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdphiSupport (j : Fin n) : Function.support (fun y ↦ (∂[j] phi.1.toFun) y) ⊆ K :=
    (subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single j (1 : ℝ)))
  have hLpTarget {f : ℝ^n → ℝ} (hf : Continuous f) (hsupp : Function.support f ⊆ K) :
      MemLp f 2 (domainMeasure n E.target) :=
    hf.memLp_of_hasCompactSupport (HasCompactSupport.of_support_subset_isCompact hKcompact hsupp)
  have hvolTarget : volume E.target ≠ ∞ :=
    ((hOmega.chart_target_bounded i).subset (by
      rw [Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_eq_target_inter_upper]
      exact inter_subset_left)).measure_lt_top.ne
  have hweakSource :=
    SobolevSpace.WeakChangeOfVariables.hasWeakDerivativeOn_comp_partialHomeomorph_W1_of_memLp
      (p := 2) (SobolevSpace.Approximation.standardMollifier n) hE (hOmega.chart_symm_contDiff i)
      hvolTarget (hLpTarget phi.1.contDiff.continuous (subset_tsupport _))
      (fun j ↦ hLpTarget (hdphiCont j) (hdphiSupport j))
      fun j ↦ SobolevSpace.WeakChangeOfVariables.hasWeakDerivativeOn_of_contDiff_one
        (n := n) (Ω := E.target) (phi.1.contDiff.of_le (by simp))
  have hsupp {f : ℝ^n → ℝ} (hf : ∀ x, f x ≠ 0 → E x ∈ K) :
      Function.support (E.source.indicator f) ⊆ L := fun x hx ↦ by
    rw [support_indicator] at hx
    exact ⟨E x, hf x hx.2, E.left_inv hx.1⟩
  have hbSupport : Function.support b ⊆ L := hsupp fun _ hx ↦ subset_tsupport _ hx
  have hdbSupport (k : Fin n) : Function.support (db k) ⊆ L := hsupp fun x hx ↦ by
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    exact hdphiSupport j (left_ne_zero_of_mul hj)
  obtain ⟨chi, hchiSource, -, hchiNhd, -⟩ :=
    TestFunction.exists_eq_one_on_compact E.open_source hLcompact hLsource
  have hbWeakGlobal (k : Fin n) : HasWeakDerivativeOn (n := n) Set.univ [k] b (db k) :=
    CompactSupportLocalization.hasWeakDerivativeOn_univ_of_support_subset_of_cutoff_one_nhds
      E.open_source hLsource hbSupport (hdbSupport k) chi hchiSource hchiNhd
      ((hweakSource k).congr_ae
        (indicator_ae_eq_restrict E.open_source.measurableSet.nullMeasurableSet).symm
        (indicator_ae_eq_restrict E.open_source.measurableSet.nullMeasurableSet).symm)
  have hLpUniv {f : ℝ^n → ℝ} (hf : Continuous f)
      (hsupp : Function.support (E.source.indicator f) ⊆ L) :
      MemLp (E.source.indicator f) 2 (domainMeasure n Set.univ) :=
    CompactSupportLocalization.memLp_of_support_subset_of_subset hLcompact.measurableSet
      (subset_univ L) hsupp ((memLp_congr_ae (ae_restrict_of_forall_mem hLcompact.measurableSet
        fun x hx ↦ indicator_of_mem (hLsource hx) f)).2
          (SobolevSpace.WeakChangeOfVariables.memLp_on_compact_of_continuous hLcompact hf))
  have hbLp : MemLp b 2 (domainMeasure n Set.univ) :=
    hLpUniv (phi.1.contDiff.continuous.comp hE.continuous) hbSupport
  have hdbLp (k : Fin n) : MemLp (db k) 2 (domainMeasure n Set.univ) :=
    hLpUniv (continuous_finsetSum _ fun j _ ↦ ((hdphiCont j).comp hE.continuous).mul
      ((EuclideanSpace.proj j).continuous.comp
          ((hE.continuous_fderiv (by simp)).clm_apply continuous_const))) (hdbSupport k)
  let q : DerivIndex n 1 → ℝ^n → ℝ := firstOrderRows b db
  have hqbase : q (baseIndex n 1) = b := by simp [q]
  have hqLp (a : DerivIndex n 1) : MemLp (q a) 2 (domainMeasure n Set.univ) := by
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨k, rfl⟩
    · simpa [q] using hbLp
    · simpa [q] using hdbLp k
  have hqweak (a : DerivIndex n 1) :
      HasWeakDerivativeOn (n := n) Set.univ a.toList b (q a) := by
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨k, rfl⟩
    · simpa [q] using hasWeakDerivativeOn_nil (memLp_locallyIntegrableOn_domain hbLp (by norm_num))
    · simpa [q] using hbWeakGlobal k
  let W : W^{1,2}((Set.univ : Set (ℝ^n))) := mkWkpSpaceOnOfWeakDerivatives
    (n := n) (k := 1) (p := 2) (Ω := Set.univ) b q hqbase hqLp hqweak
  have hW := mkWkpSpaceOnOfWeakDerivatives_apply_ae (n := n) (k := 1) (p := 2) (Ω := Set.univ)
    b q hqbase hqLp hqweak
  let V : H¹(Omega) :=
    restrictCLM (n := n) (k := 1) (p := 2) hOmega.isOpen.measurableSet (subset_univ Omega) W
  have hVmem : V ∈ (h10SubmoduleOn (n := n) (Ω := Omega)).toSubmodule :=
    restrict_mem_H10_of_tsupport_subset hOmega.isOpen W b
      (by simpa [domainMeasure, q] using hW (baseIndex n 1))
      (HasCompactSupport.of_support_subset_isCompact hLcompact hbSupport)
      ((closure_minimal hbSupport hLcompact.isClosed).trans (hLsource.trans fun _ hx ↦ hx.2))
  have hV (a : DerivIndex n 1) : ((V : WkpAmbientOn n 1 2 Omega) a : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Omega] q a :=
    (restrictCLM_apply_ae (p := 2) hOmega.isOpen.measurableSet (subset_univ Omega) W a).trans
      ((hW a).filter_mono (ae_mono (domainMeasure_le (subset_univ Omega))))
  exact ⟨⟨V, hVmem⟩, by simpa [q] using hV (baseIndex n 1),
    fun k ↦ by simpa [q] using hV (singleDerivIndex (n := n) k)⟩

end PDE.Elliptic.Regularity.Boundary.TestFunctionPullback
