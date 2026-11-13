/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.ACL
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import PDE.Analysis.Calculus.LipschitzChainRule
import PDE.DistributionTheory.TestFunction.CompactCutoff
import PDE.Spaces.Sobolev.Calculus.Slicing.ACLConverse
import PDE.Spaces.Sobolev.Localization.Cutoff.ExponentRestriction
public import PDE.Spaces.Sobolev.Approximation.Density.Constructors

/-!
# Lipschitz composition in `W^{1,p}`

We prove the real scalar Lipschitz Nemytskii theorem on global `W^{1,p}` for every
`1 ≤ p ≤ ∞`. If `F` is Lipschitz and fixes zero, then `F ∘ u` remains in `W^{1,p}` and

`∂ᵢ(F ∘ u) = deriv F u * ∂ᵢu`

almost everywhere.

For finite `p`, fixing zero is necessary for a composition operation on the
whole global space: applying it to zero produces the constant `F(0)`, which
belongs to `L^p(ℝ^n)` only if it vanishes when `n > 0`. At `p = ∞`, nonzero
constants are allowed. The theorem here keeps `F(0) = 0` uniformly across
exponents.

## Main results

* `hasWeakDerivativeOn_comp_lipschitz`: for `F` Lipschitz with `F 0 = 0`, `U ∈ W^{1,p}(ℝ^n)` and
  `1 ≤ p ≤ ∞`, the function `deriv F u * ∂ᵢu` is the weak `i`th derivative of `F ∘ u` on `ℝ^n`,
  where `u` and `∂ᵢu` are the base and derivative coordinates of `U`.
* `lipschitzComposition`: the composition as an operation on `W^{1,p}(ℝ^n)`, with
  `lipschitzComposition_base_ae` and `lipschitzComposition_derivative_ae` identifying its base
  function and its weak derivatives almost everywhere.

## How it works

We use the ACL characterization in both directions. On almost every coordinate line the canonical
Sobolev representative is absolutely continuous; Rademacher's theorem on the line (Mathlib's
`LipschitzWith.ae_differentiableAt_real`), together with the null-preimage principle, gives the
scalar Lipschitz chain rule there (`PDE.Analysis.Calculus.LipschitzWith.ae_hasDerivAt_comp`), and
coordinate Fubini reconstructs the global weak derivative
(`Slices.hasWeakDerivativeOn_of_ae_coordinate_acl`). We first prove the chain rule in `W^{1,1}`. For
general `p`, a smooth cutoff equal to one near the support of the test function localizes the data
to `W^{1,1}` (`cutoffToW11`), and the distributional identity follows from the `W^{1,1}` case. The
main proof is `hasWeakDerivativeOn_comp_lipschitz`.

## References

* M. Marcus and V. J. Mizel, "Absolute continuity on tracks and mappings of Sobolev spaces",
  *Arch. Rational Mech. Anal.* 45 (1972), no. 4, 294-320, for the action of Lipschitz maps on
  Sobolev spaces.
  <https://doi.org/10.1007/BF00251378>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace.GraphSpace

open ENNReal Filter Function MeasureTheory Set
open scoped NNReal Topology Sobolev

private theorem continuous_coordinateACLRepresentative
    {n : ℕ} (i : Fin (n + 1)) (U : W^{1,1}(ℝ^(n + 1)))
    (y : ℝ^n)
    (hderiv : Integrable
      (Slices.coordinateWeakDerivativeSlice i U y) volume) :
    Continuous (Slices.coordinateACLRepresentative i U y) :=
  continuous_iff_continuousAt.2 fun t ↦ by
    have h := (Slices.absolutelyContinuousOnInterval_lineRepresentative
      (u := Slices.coordinateBaseSlice i U y) hderiv (t - 1) (t + 1)).continuousOn
    rw [Set.uIcc_of_le (by linarith)] at h
    exact h.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/-- The chain-rule candidate `deriv F (u x) * du x` of a Lipschitz `F` lies in `Lᵖ` whenever
`du` does. -/
private theorem memLp_deriv_comp_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} {F : ℝ → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F) {u du : α → ℝ}
    (hu : AEStronglyMeasurable u μ) (hdu : MemLp du p μ) :
    MemLp (fun x ↦ deriv F (u x) * du x) p μ :=
  hdu.of_le_mul (c := C)
    (((measurable_deriv F).comp_aemeasurable hu.aemeasurable).aestronglyMeasurable.mul
      hdu.aestronglyMeasurable)
    (.of_forall fun x ↦ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_deriv_le_of_lipschitz hF) (norm_nonneg _))

private theorem hasWeakDerivativeOn_comp_lipschitz_succ
    {n : ℕ} {F : ℝ → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hFzero : F 0 = 0)
    (U : W^{1,1}(ℝ^(n + 1))) (i : Fin (n + 1)) :
    let u : ℝ^(n + 1) → ℝ :=
      (wkpBaseCoordinateCLM
        (n := n + 1) (m := 1) (p := 1) (Ω := Set.univ) U :
          ℝ^(n + 1) → ℝ)
    let du : ℝ^(n + 1) → ℝ :=
      (wkpCoordinateCLM
        (n := n + 1) (p := 1) (Ω := Set.univ)
        (singleDerivIndex (n + 1) i) U : ℝ^(n + 1) → ℝ)
    HasWeakDerivativeOn (n := n + 1) Set.univ [i]
      (F ∘ u) (fun x ↦ deriv F (u x) * du x) := by
  intro u du
  have huMem : MemLp u 1 volume := by
    simpa [u, domainMeasure] using Lp.memLp
      (wkpBaseCoordinateCLM (n := n + 1) (m := 1) (p := 1) (Ω := Set.univ) U)
  have hduMem : MemLp du 1 volume := by
    simpa [du, domainMeasure] using Lp.memLp
      (wkpCoordinateCLM (n := n + 1) (p := 1) (Ω := Set.univ) (singleDerivIndex (n + 1) i) U)
  refine Slices.hasWeakDerivativeOn_of_ae_coordinate_acl i
    (memLp_one_iff_integrable.mp (hF.comp_memLp hFzero huMem))
    (memLp_one_iff_integrable.mp (memLp_deriv_comp_mul hF huMem.aestronglyMeasurable hduMem))
    (r := fun y ↦ F ∘ Slices.coordinateACLRepresentative i U y) ?_
    (Slices.ae_forall_absolutelyContinuousOnInterval_coordinateACLRepresentative i U |>.mono
      fun y hy a b ↦ hF.comp_absolutelyContinuousOnInterval (hy a b)) ?_
  · filter_upwards [Slices.ae_coordinateACLRepresentative_eq i U] with y hy
    filter_upwards [hy] with t ht
    simpa [Slices.coordinateBaseSlice, Slices.coordinateSlice, u,
      Function.comp_def] using congrArg F ht
  · filter_upwards [Slices.ae_coordinateSlice_acl i U,
      Slices.ae_hasDerivAt_coordinateACLRepresentative i U] with y hy hrepDeriv
    have hcomp := PDE.Analysis.Calculus.LipschitzWith.ae_hasDerivAt_comp hF
      (continuous_coordinateACLRepresentative i U y hy.2.1).measurable
      (hrepDeriv.mono fun _ ht ↦ ht.differentiableAt)
    filter_upwards [hy.2.2, hrepDeriv, hcomp] with t hrep hderiv hchain
    rw [hderiv.deriv] at hchain
    simpa [u, du, Slices.coordinateBaseSlice, Slices.coordinateWeakDerivativeSlice,
      Slices.coordinateSlice, Function.comp_def, hrep] using hchain

private theorem hasWeakDerivativeOn_comp_lipschitz_one
    {n : ℕ} [Fact (0 < n)] {F : ℝ → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hFzero : F 0 = 0)
    (U : W^{1,1}(ℝ^n)) (i : Fin n) :
    let u : ℝ^n → ℝ :=
      (wkpBaseCoordinateCLM
        (n := n) (m := 1) (p := 1) (Ω := Set.univ) U :
          ℝ^n → ℝ)
    let du : ℝ^n → ℝ :=
      (wkpCoordinateCLM
        (n := n) (p := 1) (Ω := Set.univ)
        (singleDerivIndex n i) U : ℝ^n → ℝ)
    HasWeakDerivativeOn (n := n) Set.univ [i]
      (F ∘ u) (fun x ↦ deriv F (u x) * du x) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Fact.out : 0 < n).ne'
  exact hasWeakDerivativeOn_comp_lipschitz_succ hF hFzero U i

/-- A zero-preserving Lipschitz scalar map obeys the weak chain rule on
global real-valued `W^{1,p}` for every exponent `1 ≤ p ≤ ∞`. -/
theorem hasWeakDerivativeOn_comp_lipschitz
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {F : ℝ → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hFzero : F 0 = 0)
    (U : W^{1,p}(ℝ^n)) (i : Fin n) :
    let u : ℝ^n → ℝ :=
      (wkpBaseCoordinateCLM
        (n := n) (m := 1) (p := p) (Ω := Set.univ) U :
          ℝ^n → ℝ)
    let du : ℝ^n → ℝ :=
      (wkpCoordinateCLM
        (n := n) (p := p) (Ω := Set.univ)
        (singleDerivIndex n i) U : ℝ^n → ℝ)
    HasWeakDerivativeOn (n := n) Set.univ [i]
      (F ∘ u) (fun x ↦ deriv F (u x) * du x) := by
  intro u du
  have : Fact (0 < n) := ⟨i.pos⟩
  have huMem : MemLp u p (domainMeasure n Set.univ) :=
    Lp.memLp (wkpBaseCoordinateCLM (n := n) (m := 1) (p := p) (Ω := Set.univ) U)
  have hduMem : MemLp du p (domainMeasure n Set.univ) :=
    Lp.memLp (wkpCoordinateCLM (n := n) (p := p) (Ω := Set.univ) (singleDerivIndex n i) U)
  refine ⟨memLp_locallyIntegrableOn_domain (hF.comp_memLp hFzero huMem) Fact.out,
    memLp_locallyIntegrableOn_domain
      (memLp_deriv_comp_mul hF huMem.aestronglyMeasurable hduMem) Fact.out, fun φ _ ↦ ?_⟩
  -- localize `U` to `W^{1,1}` by a cutoff equal to one near the support of `φ`
  let K : Set (ℝ^n) := tsupport φ.toFun
  obtain ⟨ψ, -, hψone, hψoneNhds, -⟩ := TestFunction.exists_eq_one_on_compact
    (n := n) isOpen_univ φ.hasCompactSupport.isCompact (subset_univ K)
  let V : W^{1,1}(ℝ^n) := cutoffToW11 ψ U
  let v : ℝ^n → ℝ :=
    (wkpBaseCoordinateCLM (n := n) (m := 1) (p := 1) (Ω := Set.univ) V : ℝ^n → ℝ)
  let dv : ℝ^n → ℝ :=
    (wkpCoordinateCLM (n := n) (p := 1) (Ω := Set.univ) (singleDerivIndex n i) V : ℝ^n → ℝ)
  have hlocal : HasWeakDerivativeOn (n := n) Set.univ [i]
      (F ∘ v) (fun x ↦ deriv F (v x) * dv x) :=
    hasWeakDerivativeOn_comp_lipschitz_one hF hFzero V i
  have hv : v =ᵐ[domainMeasure n Set.univ] fun x ↦ ψ.toFun x * u x := by
    simpa [v, V, u] using
      (cutoffToW11_apply_ae ψ U (baseIndex n 1)).trans (cutoffCLM_base_apply_ae ψ U)
  have hdv : dv =ᵐ[domainMeasure n Set.univ] fun x ↦
      ψ.toFun x * du x + iteratedPartialDeriv (n := n) [i] ψ.toFun x * u x := by
    simpa [dv, V, u, du] using (cutoffToW11_apply_ae ψ U (singleDerivIndex n i)).trans
      (cutoffCLM_singleDeriv_apply_ae ψ U i)
  have hleft : (∫ x, (F ∘ u) x * iteratedPartialDeriv (n := n) [i] φ.toFun x
        ∂ domainMeasure n Set.univ) =
      ∫ x, (F ∘ v) x * iteratedPartialDeriv (n := n) [i] φ.toFun x
        ∂ domainMeasure n Set.univ := by
    refine integral_congr_ae ?_
    filter_upwards [hv] with x hv
    by_cases hxK : x ∈ K
    · simp [hv, hψone x hxK]
    · have hdφ : iteratedPartialDeriv (n := n) [i] φ.toFun x = 0 :=
        image_eq_zero_of_notMem_tsupport fun hx ↦ hxK
          (tsupport_iteratedPartialDeriv_subset_tsupport (n := n) [i] φ.toFun hx)
      simp only [hdφ, mul_zero]
  have hright : (∫ x, (deriv F (v x) * dv x) * φ.toFun x ∂ domainMeasure n Set.univ) =
      ∫ x, (deriv F (u x) * du x) * φ.toFun x ∂ domainMeasure n Set.univ := by
    refine integral_congr_ae ?_
    filter_upwards [hv, hdv] with x hv hdv
    by_cases hxK : x ∈ K
    · have hdψ : iteratedPartialDeriv (n := n) [i] ψ.toFun x = 0 := by
        change (fderiv ℝ ψ.toFun x) (EuclideanSpace.single i 1) = 0
        rw [(hψoneNhds x hxK).fderiv_eq]
        simp
      rw [hv, hdv, hψone x hxK, hdψ]
      simp
    · simp [image_eq_zero_of_notMem_tsupport hxK]
  rw [hleft, hlocal φ (subset_univ K), hright]

/-- The base function of a composition `F ∘ U`: `F` applied to the base coordinate
representative of `U`. -/
abbrev compositionBase
    {n : ℕ} {p : ℝ≥0∞}
    (F : ℝ → ℝ) (U : W^{1,p}(ℝ^n)) :
    ℝ^n → ℝ :=
  F ∘
    ((U : WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : ℝ^n → ℝ)

/-- The coordinate rows of the Lipschitz composition: the base row is `F ∘ u`
and the `i`th derivative row is the chain-rule candidate. -/
def lipschitzCompositionRows
    {n : ℕ} {p : ℝ≥0∞}
    (F : ℝ → ℝ) (U : W^{1,p}(ℝ^n))
    (a : DerivIndex n 1) :
    ℝ^n → ℝ :=
  firstOrderRows (compositionBase F U)
    (fun i x ↦
      deriv F
        (((U : WkpAmbientOn n 1 p Set.univ)
          (baseIndex n 1) : ℝ^n → ℝ) x) *
        ((U : WkpAmbientOn n 1 p Set.univ) (singleDerivIndex n i) :
          ℝ^n → ℝ) x)
    a

/-- The base row of `lipschitzCompositionRows` is `compositionBase`. -/
theorem lipschitzCompositionRows_base
    {n : ℕ} {p : ℝ≥0∞}
    (F : ℝ → ℝ) (U : W^{1,p}(ℝ^n)) :
    lipschitzCompositionRows F U (baseIndex n 1) =
      compositionBase F U := by
  simp [lipschitzCompositionRows]

/-- Every row of `lipschitzCompositionRows` lies in `Lp` when `F` is Lipschitz
and fixes zero. -/
theorem lipschitzCompositionRows_memLp
    {n : ℕ} {p : ℝ≥0∞}
    {F : ℝ → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hFzero : F 0 = 0)
    (U : W^{1,p}(ℝ^n)) (a : DerivIndex n 1) :
    MemLp (lipschitzCompositionRows F U a) p
      (domainMeasure n Set.univ) := by
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨j, rfl⟩
  · simpa [lipschitzCompositionRows] using
      hF.comp_memLp hFzero (Lp.memLp ((U : WkpAmbientOn n 1 p Set.univ) (baseIndex n 1)))
  · rw [lipschitzCompositionRows, firstOrderRows_singleDerivIndex]
    exact memLp_deriv_comp_mul hF (Lp.memLp _).aestronglyMeasurable (Lp.memLp _)

/-- Each row of `lipschitzCompositionRows` is the corresponding weak derivative
of `compositionBase` on the whole space. -/
theorem lipschitzCompositionRows_weak
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {F : ℝ → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hFzero : F 0 = 0)
    (U : W^{1,p}(ℝ^n)) (a : DerivIndex n 1) :
    HasWeakDerivativeOn (n := n) Set.univ a.toList
      (compositionBase F U)
      (lipschitzCompositionRows F U a) := by
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    have hloc :=
      memLp_locallyIntegrableOn_domain
        (lipschitzCompositionRows_memLp hF hFzero U
          (baseIndex n 1))
        (Fact.out : (1 : ℝ≥0∞) ≤ p)
    have hloc' :
        LocallyIntegrableOn (compositionBase F U) Set.univ
          (volume : Measure (ℝ^n)) := by
      simpa [lipschitzCompositionRows] using hloc
    simpa [lipschitzCompositionRows, iteratedPartialDeriv] using
      (show HasWeakDerivativeOn (n := n) Set.univ []
          (compositionBase F U)
          (compositionBase F U) from
        hasWeakDerivativeOn_nil hloc')
  · subst a
    simpa [lipschitzCompositionRows, compositionBase,
      Function.comp_def] using
      hasWeakDerivativeOn_comp_lipschitz hF hFzero U i

/-- Composition by a zero-preserving Lipschitz scalar map as an operation on
global real-valued `W^{1,p}` for every `1 ≤ p ≤ ∞`. -/
noncomputable def lipschitzComposition
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {F : ℝ → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hFzero : F 0 = 0)
    (U : W^{1,p}(ℝ^n)) :
    W^{1,p}(ℝ^n) :=
  mkWkpSpaceOnOfWeakDerivatives
    (n := n) (k := 1) (p := p) (Ω := Set.univ)
    (compositionBase F U)
    (lipschitzCompositionRows F U)
    (lipschitzCompositionRows_base F U)
    (lipschitzCompositionRows_memLp hF hFzero U)
    (lipschitzCompositionRows_weak hF hFzero U)

/-- The base coordinate of `lipschitzComposition hF hFzero U` is `F ∘ u`
almost everywhere. -/
theorem lipschitzComposition_base_ae
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {F : ℝ → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hFzero : F 0 = 0)
    (U : W^{1,p}(ℝ^n)) :
    (((lipschitzComposition hF hFzero U :
        WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : DerivLp n p Set.univ) :
        ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ]
        F ∘
          ((U : WkpAmbientOn n 1 p Set.univ)
            (baseIndex n 1) : ℝ^n → ℝ) := by
  simpa [lipschitzComposition, lipschitzCompositionRows_base] using
    mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (n := n) (k := 1) (p := p) (Ω := Set.univ)
      (compositionBase F U)
      (lipschitzCompositionRows F U)
      (lipschitzCompositionRows_base F U)
      (lipschitzCompositionRows_memLp hF hFzero U)
      (lipschitzCompositionRows_weak hF hFzero U)
      (baseIndex n 1)

/-- The `i`th weak derivative of `lipschitzComposition hF hFzero U` is
`deriv F u * ∂ᵢu` almost everywhere. -/
theorem lipschitzComposition_derivative_ae
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {F : ℝ → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hFzero : F 0 = 0)
    (U : W^{1,p}(ℝ^n)) (i : Fin n) :
    (((lipschitzComposition hF hFzero U :
        WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) :
        DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ]
        fun x ↦
          deriv F
            (((U : WkpAmbientOn n 1 p Set.univ)
              (baseIndex n 1) : ℝ^n → ℝ) x) *
            ((U : WkpAmbientOn n 1 p Set.univ)
              (singleDerivIndex n i) : ℝ^n → ℝ) x := by
  simpa [lipschitzComposition, lipschitzCompositionRows] using
    mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (n := n) (k := 1) (p := p) (Ω := Set.univ)
      (compositionBase F U)
      (lipschitzCompositionRows F U)
      (lipschitzCompositionRows_base F U)
      (lipschitzCompositionRows_memLp hF hFzero U)
      (lipschitzCompositionRows_weak hF hFzero U)
      (singleDerivIndex n i)

end SobolevSpace.GraphSpace
