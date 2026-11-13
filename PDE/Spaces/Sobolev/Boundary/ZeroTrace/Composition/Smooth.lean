/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.WkpExtensionByZero
public import PDE.Spaces.Sobolev.Calculus.Composition.Smooth
import PDE.Analysis.MeasureTheory.DominatedLp
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.GraphSpace.Topology.Convergence

/-!
# Smooth composition in the zero-boundary Sobolev space

A smooth scalar function fixing zero and with bounded slope preserves the
supported `W^{1,p}` closure. The argument uses strong approximation and
almost-everywhere convergence of a subsequence, so it includes `p = 1` and
requires neither finite measure nor a boundary atlas.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.GraphSpace

open Filter Function MeasureTheory Set
open scoped ENNReal Topology Sobolev
open ZeroTrace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A bounded continuous scalar slope preserves strong Sobolev convergence
along a sequence whose base coordinates also converge almost everywhere. -/
private theorem tendsto_smoothComposition_of_base_ae
    (hp : p ≠ ∞) {F F' : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (hF' : Continuous F')
    (hderiv : ∀ x, HasDerivAt F (F' x) x)
    (hzero : F 0 = 0) (hLip : LipschitzWith 1 F)
    (hbound : ∀ x, |F' x| ≤ 1)
    {U : ℕ → W^{1,p}(ℝ^n)} {V : W^{1,p}(ℝ^n)}
    (hU : Tendsto U atTop (𝓝 V))
    (hbase : ∀ᵐ x ∂domainMeasure n Set.univ,
      Tendsto (fun j ↦ (wkpCoordinateCLM (baseIndex n 1) (U j) : ℝ^n → ℝ) x)
        atTop (𝓝 ((wkpCoordinateCLM (baseIndex n 1) V : ℝ^n → ℝ) x))) :
    Tendsto (fun j ↦ smoothComposition hF hderiv hzero hbound (U j))
      atTop (𝓝 (smoothComposition hF hderiv hzero hbound V)) := by
  let b : W^{1,p}(ℝ^n) → DerivLp n p Set.univ :=
    wkpCoordinateCLM (baseIndex n 1)
  have hcoord (a : DerivIndex n 1) :
      Tendsto (fun j ↦ eLpNorm
        ((wkpCoordinateCLM a (U j) : ℝ^n → ℝ) -
          (wkpCoordinateCLM a V : ℝ^n → ℝ)) p (domainMeasure n Set.univ))
        atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
      (fun j ↦ wkpCoordinateCLM a (U j)) (wkpCoordinateCLM a V)).1
        (((wkpCoordinateCLM a).continuous.tendsto V).comp hU)
  apply tendsto_wkp_of_coordinate_eLpNorm
  intro a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds (hcoord (baseIndex n 1)) (fun _ ↦ bot_le)
    intro j
    apply eLpNorm_mono_ae
      ((Lp.aestronglyMeasurable
        (b (smoothComposition hF hderiv hzero hbound (U j)))).sub
        (Lp.aestronglyMeasurable
          (b (smoothComposition hF hderiv hzero hbound V))))
    filter_upwards
      [smoothComposition_base_ae hF hderiv hzero hbound (U j),
       smoothComposition_base_ae hF hderiv hzero hbound V] with x hx hy
    change ‖(_ : ℝ) - (_ : ℝ)‖ ≤ ‖(_ : ℝ) - (_ : ℝ)‖
    simp only [b, wkpCoordinateCLM_apply]
    rw [hx, hy]
    simpa only [b, wkpCoordinateCLM_apply, Real.norm_eq_abs, Real.dist_eq,
      NNReal.coe_one, one_mul] using
      hLip.dist_le_mul ((b (U j) : ℝ^n → ℝ) x) ((b V : ℝ^n → ℝ) x)
  · subst a
    let d : W^{1,p}(ℝ^n) → DerivLp n p Set.univ :=
      wkpCoordinateCLM (singleDerivIndex n i)
    have hmul :
        Tendsto (fun j ↦ eLpNorm (fun x ↦
          F' ((b (U j) : ℝ^n → ℝ) x) * (d (U j) : ℝ^n → ℝ) x -
          F' ((b V : ℝ^n → ℝ) x) * (d V : ℝ^n → ℝ) x)
          p (domainMeasure n Set.univ)) atTop (𝓝 0) := by
      apply tendsto_eLpNorm_mul_of_tendsto_ae_of_tendsto_eLpNorm
        (p := p) Fact.out hp
        (fun j ↦ hF'.comp_aestronglyMeasurable (Lp.memLp (b (U j))).aestronglyMeasurable)
        (hF'.comp_aestronglyMeasurable (Lp.memLp (b V)).aestronglyMeasurable)
        (fun j ↦ Lp.memLp (d (U j))) (Lp.memLp (d V))
      · exact fun _ ↦ Eventually.of_forall fun _ ↦ hbound _
      · exact Eventually.of_forall fun _ ↦ hbound _
      · filter_upwards [hbase] with x hx
        exact (hF'.tendsto _).comp hx
      · exact hcoord (singleDerivIndex n i)
    apply hmul.congr'
    filter_upwards with j
    apply eLpNorm_congr_ae
    filter_upwards
      [smoothComposition_derivative_ae hF hderiv hzero hbound (U j) i,
       smoothComposition_derivative_ae hF hderiv hzero hbound V i]
        with x hx hy
    exact (congrArg₂ (· - ·) hx hy).symm

/-- Smooth composition fixing zero preserves the supported smooth core.
The global weak derivative bundle is identified by its base coordinate. -/
private theorem restrict_smoothComposition_testFunction_mem
    {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω)
    {F F' : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hderiv : ∀ x, HasDerivAt F (F' x) x)
    (hzero : F 0 = 0)
    (hbound : ∀ x, |F' x| ≤ 1) (φ : TestFunctionOn n Ω) :
    restrictCLM hΩ (subset_univ Ω)
      (smoothComposition (hF.of_le (by simp)) hderiv hzero hbound
        (zeroExtendWkp0 hΩ (testFunctionToWkp0 (p := p) (k := 1) φ))) ∈
      (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := Ω)).toSubmodule := by
  let ψ : TestFunctionOn n Ω :=
    ⟨_root_.TestFunction.mk (F ∘ φ.1.toFun) (hF.comp φ.1.contDiff)
      (φ.1.hasCompactSupport.comp_left hzero) (subset_univ _),
      (tsupport_comp_subset hzero φ.1.toFun).trans φ.2⟩
  let φg : TestFunctionOn n Set.univ := ⟨φ.1, subset_univ _⟩
  let ψg : TestFunctionOn n Set.univ := ⟨ψ.1, subset_univ _⟩
  have hext :
      zeroExtendWkp0 hΩ (testFunctionToWkp0 (p := p) (k := 1) φ) =
        testFunctionToWkp (p := p) (k := 1) φg :=
    Subtype.ext (zeroExtendAmbient_testFunction_eq hΩ φ)
  have hglobal :
      smoothComposition (hF.of_le (by simp)) hderiv hzero hbound
        (zeroExtendWkp0 hΩ (testFunctionToWkp0 (p := p) (k := 1) φ)) =
          testFunctionToWkp (p := p) (k := 1) ψg := by
    rw [hext]
    apply WkpSpaceOn.ext_of_base_ae isOpen_univ
    filter_upwards
      [smoothComposition_base_ae (hF.of_le (by simp)) hderiv hzero
        hbound (testFunctionToWkp (p := p) (k := 1) φg),
       testFunctionToWkp_coordinate_ae (p := p) φg (baseIndex n 1),
       testFunctionToWkp_coordinate_ae (p := p) ψg (baseIndex n 1)] with x hx hφ hψ
    simp only [baseIndex_toList, iteratedPartialDeriv] at hφ hψ
    change _ = F (φ.1.toFun x) at hψ
    exact (hx.trans (congrArg F hφ)).trans hψ.symm
  rw [hglobal]
  have hrestrict :
      restrictCLM hΩ (subset_univ Ω) (testFunctionToWkp (p := p) (k := 1) ψg) =
        testFunctionToWkp (p := p) (k := 1) ψ := by
    apply Subtype.ext
    apply PiLp.ext
    intro a
    apply Lp.ext
    have hglobalΩ := ae_mono (domainMeasure_le (subset_univ Ω))
      (testFunctionToWkp_coordinate_ae (p := p) ψg a)
    filter_upwards
      [restrictCLM_apply_ae hΩ (subset_univ Ω)
        (testFunctionToWkp (p := p) (k := 1) ψg) a,
       hglobalΩ, testFunctionToWkp_coordinate_ae (p := p) ψ a] with x hx hy hz
    exact hx.trans (hy.trans hz.symm)
  rw [hrestrict]
  exact testFunctionToWkp_mem_Wkp0 ψ

/-- A smooth zero-preserving scalar map with slope bounded by one preserves
the supported `W^{1,p}` closure, including `p = 1`. -/
theorem restrict_smoothComposition_zeroExtendWkp0_mem
    {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω) (hp : p ≠ ∞)
    {F F' : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hF' : Continuous F')
    (hderiv : ∀ x, HasDerivAt F (F' x) x)
    (hzero : F 0 = 0) (hLip : LipschitzWith 1 F)
    (hbound : ∀ x, |F' x| ≤ 1) (u : W₀^{1,p}(Ω)) :
    restrictCLM hΩ (subset_univ Ω)
      (smoothComposition (hF.of_le (by simp)) hderiv hzero hbound
        (zeroExtendWkp0 hΩ u)) ∈
      (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := Ω)).toSubmodule := by
  obtain ⟨s, hs, hsu⟩ := mem_closure_iff_seq_limit.mp
    (denseRange_testFunctionToWkp0Linear (n := n) (k := 1) (p := p) (Ω := Ω) u)
  choose φ hφ using hs
  have hφu : Tendsto (fun j ↦ testFunctionToWkp0 (φ j)) atTop (𝓝 u) := by
    have hφeq : (fun j ↦ testFunctionToWkp0 (φ j)) = s := funext hφ
    rw [hφeq]
    exact hsu
  let U : ℕ → W^{1,p}(ℝ^n) := fun j ↦ zeroExtendWkp0 hΩ (testFunctionToWkp0 (φ j))
  let V : W^{1,p}(ℝ^n) := zeroExtendWkp0 hΩ u
  have hU : Tendsto U atTop (𝓝 V) :=
    ((zeroExtendWkp0 hΩ).continuous.tendsto u).comp hφu
  have hbaseLp := ((wkpCoordinateCLM (baseIndex n 1)).continuous.tendsto V).comp hU
  obtain ⟨ns, hns, hbaseAE⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hbaseLp).exists_seq_tendsto_ae
  have hcomp := tendsto_smoothComposition_of_base_ae hp (hF.of_le (by simp))
    hF' hderiv hzero hLip hbound (hU.comp hns.tendsto_atTop) hbaseAE
  apply (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := Ω)).isClosed'.mem_of_tendsto
    (((restrictCLM hΩ (subset_univ Ω)).continuous.tendsto _).comp hcomp)
  exact Eventually.of_forall fun j ↦
    restrict_smoothComposition_testFunction_mem hΩ hF hderiv hzero hbound
      (φ (ns j))

/-- Smooth composition fixing zero, as an element of the supported
Sobolev closure. -/
def smoothCompositionWkp0
    {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω) (hp : p ≠ ∞)
    {F F' : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hF' : Continuous F')
    (hderiv : ∀ x, HasDerivAt F (F' x) x)
    (hzero : F 0 = 0) (hLip : LipschitzWith 1 F)
    (hbound : ∀ x, |F' x| ≤ 1) (u : W₀^{1,p}(Ω)) :
    W₀^{1,p}(Ω) :=
  ⟨restrictCLM hΩ (subset_univ Ω)
    (smoothComposition (hF.of_le (by simp)) hderiv hzero hbound
      (zeroExtendWkp0 hΩ u)),
    restrict_smoothComposition_zeroExtendWkp0_mem hΩ hp hF hF'
      hderiv hzero hLip hbound u⟩

/-- The base coordinate of zero-boundary composition is the scalar composition. -/
theorem smoothCompositionWkp0_base_ae
    {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω) (hp : p ≠ ∞)
    {F F' : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hF' : Continuous F')
    (hderiv : ∀ x, HasDerivAt F (F' x) x)
    (hzero : F 0 = 0) (hLip : LipschitzWith 1 F)
    (hbound : ∀ x, |F' x| ≤ 1) (u : W₀^{1,p}(Ω)) :
    (wkpCoordinateCLM (baseIndex n 1)
      (smoothCompositionWkp0 hΩ hp hF hF' hderiv hzero hLip hbound u :
        W^{1,p}(Ω)) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ F (wkpCoordinateCLM (baseIndex n 1) (u : W^{1,p}(Ω)) x) := by
  have hglobal := ae_mono (domainMeasure_le (subset_univ Ω))
    (smoothComposition_base_ae (hF.of_le (by simp)) hderiv hzero hbound
      (zeroExtendWkp0 hΩ u))
  filter_upwards
    [restrictCLM_apply_ae hΩ (subset_univ Ω)
      (smoothComposition (hF.of_le (by simp)) hderiv hzero hbound
        (zeroExtendWkp0 hΩ u)) (baseIndex n 1),
     hglobal, zeroExtendWkp0_coordinate_ae_on hΩ u (baseIndex n 1)] with x hx hy hz
  exact hx.trans (hy.trans (congrArg F hz))

/-- Each weak derivative of zero-boundary smooth composition satisfies the
scalar chain rule almost everywhere. -/
theorem smoothCompositionWkp0_derivative_ae
    {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω) (hp : p ≠ ∞)
    {F F' : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hF' : Continuous F')
    (hderiv : ∀ x, HasDerivAt F (F' x) x)
    (hzero : F 0 = 0) (hLip : LipschitzWith 1 F)
    (hbound : ∀ x, |F' x| ≤ 1) (u : W₀^{1,p}(Ω)) (i : Fin n) :
    (wkpCoordinateCLM (singleDerivIndex n i)
      (smoothCompositionWkp0 hΩ hp hF hF' hderiv hzero hLip hbound u :
        W^{1,p}(Ω)) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ F' (wkpCoordinateCLM (baseIndex n 1) (u : W^{1,p}(Ω)) x) *
        wkpCoordinateCLM (singleDerivIndex n i) (u : W^{1,p}(Ω)) x := by
  have hglobal := ae_mono (domainMeasure_le (subset_univ Ω))
    (smoothComposition_derivative_ae (hF.of_le (by simp)) hderiv hzero hbound
      (zeroExtendWkp0 hΩ u) i)
  filter_upwards
    [restrictCLM_apply_ae hΩ (subset_univ Ω)
      (smoothComposition (hF.of_le (by simp)) hderiv hzero hbound
        (zeroExtendWkp0 hΩ u)) (singleDerivIndex n i),
     hglobal, zeroExtendWkp0_coordinate_ae_on hΩ u (baseIndex n 1),
     zeroExtendWkp0_coordinate_ae_on hΩ u (singleDerivIndex n i)] with x hx hy hb hd
  exact hx.trans (hy.trans (congrArg₂ (fun s t : ℝ ↦ F' s * t) hb hd))

end SobolevSpace.GraphSpace
