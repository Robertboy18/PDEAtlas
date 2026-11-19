/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Pullback.SecondOrder.Operator
public import PDE.Spaces.Sobolev.Localization.Cutoff.HigherOrderExtension
public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.OddSecondOrder
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Boundary `H²` pullback with a support buffer

The second-order weak chain rule `WeakChangeOfVariables.localizedH2Pullback` constructs an `H²`
pullback through a boundary chart on the compact set `E.symm '' K`. Such a Sobolev value cannot in
general be extended directly from that compact set: the set need not be open, and membership in
`W^{2,2}(E.symm '' K)` alone gives no trace compatibility across its boundary.

We therefore keep a support buffer. The pullback is restricted to an open set inside `E.symm '' K`
(`bufferedLocalizedH2Pullback`), multiplied by a smooth cutoff supported in that open set, and
extended to the physical domain (`bufferedLocalizedH2PullbackExtension`,
`targetSubsetBufferedH2PullbackExtension`). The second-order chain rules all come from
`WeakChangeOfVariables.localizedH2Pullback`; the new work is the restriction, the support
localization, and the almost-everywhere bookkeeping. We also define the odd reflection
`oddReflectionH2OfBaseAEEqH10` of a flattened `H²` field with zero trace and prove its norm
identities.

This is the change of variables back to physical coordinates, (71) in step 10 of Evans's proof of
§6.3.2, Theorem 4, where Evans states it directly for `V = Ψ(V')`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, step 10 of the proof of Theorem 4, (71), p. 340.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open CompactSupportLocalization.HigherOrderLocalizedCutoff
open scoped ENNReal

variable {n : ℕ}

/-- An `H²` representative whose base coordinate agrees with an `H¹₀`
function has zero trace after restriction to `H¹`. This is the
compatibility condition needed for odd reflection across the flat boundary. -/
theorem lowerOrderCLM_mem_H10_of_base_ae
    [Fact (0 < n)]
    (U : W^{2,2}(HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (hbase :
      ⇑((U : WkpAmbientOn n 2 2 (HalfSpace.upper n))
          (baseIndex n 2) : DerivLp n 2 (HalfSpace.upper n))
        =ᵐ[domainMeasure n (HalfSpace.upper n)]
          ⇑(((u : H¹(HalfSpace.upper n)) :
            WkpAmbientOn n 1 2 (HalfSpace.upper n))
              (baseIndex n 1) : DerivLp n 2 (HalfSpace.upper n))) :
    lowerOrderCLM
        (n := n) (k := 1) (m := 2) (p := 2) (Ω := HalfSpace.upper n)
        (by omega) U ∈
      (h10SubmoduleOn (n := n) (Ω := HalfSpace.upper n)).toSubmodule := by
  have heq : lowerOrderCLM (n := n) (k := 1) (m := 2) (p := 2) (Ω := HalfSpace.upper n)
      (by omega) U = (u : H¹(HalfSpace.upper n)) := by
    apply WkpSpaceOn.ext_of_base_ae (HalfSpace.isOpen_upper (n := n))
    simpa [lowerOrderCLM_apply] using hbase
  exact heq ▸ u.property

/-- The global `H²` odd reflection of a half-space representative whose base
coordinate agrees almost everywhere with an `H¹₀` function. -/
noncomputable def oddReflectionH2OfBaseAEEqH10
    [Fact (0 < n)]
    (U : W^{2,2}(HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (hbase :
      ⇑((U : WkpAmbientOn n 2 2 (HalfSpace.upper n))
          (baseIndex n 2) : DerivLp n 2 (HalfSpace.upper n))
        =ᵐ[domainMeasure n (HalfSpace.upper n)]
          ⇑(((u : H¹(HalfSpace.upper n)) :
            WkpAmbientOn n 1 2 (HalfSpace.upper n))
              (baseIndex n 1) : DerivLp n 2 (HalfSpace.upper n))) :
    W^{2,2}((Set.univ : Set (ℝ^n))) :=
  HigherOrderReflection.oddReflectionH2 (n := n)
    ⟨U, lowerOrderCLM_mem_H10_of_base_ae U u hbase⟩

/-- The odd reflection `oddReflectionH2OfBaseAEEqH10` has the coordinatewise ambient odd
reflection as its underlying Sobolev bundle. -/
@[simp] theorem oddReflectionH2OfBaseAEEqH10_coe
    [Fact (0 < n)]
    (U : W^{2,2}(HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (hbase :
      ⇑((U : WkpAmbientOn n 2 2 (HalfSpace.upper n))
          (baseIndex n 2) : DerivLp n 2 (HalfSpace.upper n))
        =ᵐ[domainMeasure n (HalfSpace.upper n)]
          ⇑(((u : H¹(HalfSpace.upper n)) :
            WkpAmbientOn n 1 2 (HalfSpace.upper n))
              (baseIndex n 1) : DerivLp n 2 (HalfSpace.upper n))) :
    (oddReflectionH2OfBaseAEEqH10 U u hbase :
        WkpAmbientOn n 2 2 Set.univ) =
      HigherOrderReflection.oddReflectAmbient (n := n) (m := 2)
        (U : WkpAmbientOn n 2 2 (HalfSpace.upper n)) := by
  rfl

/-- Restricting the odd reflection `oddReflectionH2OfBaseAEEqH10` to the upper half-space
recovers the original `H²` field. -/
@[simp] theorem restrict_oddReflectionH2OfBaseAEEqH10
    [Fact (0 < n)]
    (U : W^{2,2}(HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (hbase :
      ⇑((U : WkpAmbientOn n 2 2 (HalfSpace.upper n))
          (baseIndex n 2) : DerivLp n 2 (HalfSpace.upper n))
        =ᵐ[domainMeasure n (HalfSpace.upper n)]
          ⇑(((u : H¹(HalfSpace.upper n)) :
            WkpAmbientOn n 1 2 (HalfSpace.upper n))
              (baseIndex n 1) : DerivLp n 2 (HalfSpace.upper n))) :
    restrictCLM
        (n := n) (k := 2) (p := 2)
        (HalfSpace.measurableSet_upper (n := n))
        (subset_univ (HalfSpace.upper n))
        (oddReflectionH2OfBaseAEEqH10 U u hbase) =
      U := by
  exact HigherOrderReflection.restrict_oddReflectionH2
    (n := n)
    (⟨U, lowerOrderCLM_mem_H10_of_base_ae U u hbase⟩ :
      HigherOrderReflection.OddReflectionH2Space n)

/-- The odd reflection `oddReflectionH2OfBaseAEEqH10` multiplies the squared `H²` norm by
exactly two. -/
theorem norm_oddReflectionH2OfBaseAEEqH10_sq
    [Fact (0 < n)]
    (U : W^{2,2}(HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (hbase :
      ⇑((U : WkpAmbientOn n 2 2 (HalfSpace.upper n))
          (baseIndex n 2) : DerivLp n 2 (HalfSpace.upper n))
        =ᵐ[domainMeasure n (HalfSpace.upper n)]
          ⇑(((u : H¹(HalfSpace.upper n)) :
            WkpAmbientOn n 1 2 (HalfSpace.upper n))
              (baseIndex n 1) : DerivLp n 2 (HalfSpace.upper n))) :
    ‖oddReflectionH2OfBaseAEEqH10 U u hbase‖ ^ 2 = 2 * ‖U‖ ^ 2 := by
  exact HigherOrderReflection.norm_oddReflectionH2_sq
    (n := n)
    (⟨U, lowerOrderCLM_mem_H10_of_base_ae U u hbase⟩ :
      HigherOrderReflection.OddReflectionH2Space n)

/-- The odd reflection `oddReflectionH2OfBaseAEEqH10` multiplies the `H²` norm by `√2`. -/
theorem norm_oddReflectionH2OfBaseAEEqH10
    [Fact (0 < n)]
    (U : W^{2,2}(HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (hbase :
      ⇑((U : WkpAmbientOn n 2 2 (HalfSpace.upper n))
          (baseIndex n 2) : DerivLp n 2 (HalfSpace.upper n))
        =ᵐ[domainMeasure n (HalfSpace.upper n)]
          ⇑(((u : H¹(HalfSpace.upper n)) :
            WkpAmbientOn n 1 2 (HalfSpace.upper n))
              (baseIndex n 1) : DerivLp n 2 (HalfSpace.upper n))) :
    ‖oddReflectionH2OfBaseAEEqH10 U u hbase‖ =
      Real.sqrt 2 * ‖U‖ := by
  exact HigherOrderReflection.norm_oddReflectionH2
    (n := n)
    (⟨U, lowerOrderCLM_mem_H10_of_base_ae U u hbase⟩ :
      HigherOrderReflection.OddReflectionH2Space n)

/-- The base coordinate of the odd reflection `oddReflectionH2OfBaseAEEqH10` agrees almost
everywhere with the original half-space `H²` field. -/
theorem oddReflectionH2OfBaseAEEqH10_base_ae_upper
    [Fact (0 < n)]
    (U : W^{2,2}(HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (hbase :
      ⇑((U : WkpAmbientOn n 2 2 (HalfSpace.upper n))
          (baseIndex n 2) : DerivLp n 2 (HalfSpace.upper n))
        =ᵐ[domainMeasure n (HalfSpace.upper n)]
          ⇑(((u : H¹(HalfSpace.upper n)) :
            WkpAmbientOn n 1 2 (HalfSpace.upper n))
              (baseIndex n 1) : DerivLp n 2 (HalfSpace.upper n))) :
    ⇑((oddReflectionH2OfBaseAEEqH10 U u hbase :
        WkpAmbientOn n 2 2 Set.univ)
          (baseIndex n 2) : DerivLp n 2 Set.univ)
      =ᵐ[domainMeasure n (HalfSpace.upper n)]
        ⇑((U : WkpAmbientOn n 2 2 (HalfSpace.upper n))
          (baseIndex n 2) : DerivLp n 2 (HalfSpace.upper n)) := by
  have h := restrictCLM_apply_ae (HalfSpace.measurableSet_upper (n := n)) (subset_univ _)
    (oddReflectionH2OfBaseAEEqH10 U u hbase) (baseIndex n 2)
  rw [restrict_oddReflectionH2OfBaseAEEqH10] at h
  exact h.symm

/-- The pullback field restricted to the open buffer on which multiplication
by the physical cutoff is performed. -/
noncomputable def bufferedLocalizedH2Pullback
    (mu : SobolevSpace.Approximation.Mollifier n)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    {K V : Set (ℝ^n)}
    (hK : IsCompact K) (hKTarget : K ⊆ E.target)
    (hV : IsOpen V)
    (hVPatch : V ⊆
      SobolevSpace.WeakChangeOfVariables.compactPullbackSource
        (n := n) E K)
    (U : W^{2,2}(E.target)) : W^{2,2}(V) :=
  restrictCLM (n := n) (k := 2) (p := (2 : ENNReal))
    hV.measurableSet hVPatch
    (SobolevSpace.WeakChangeOfVariables.localizedH2Pullback
      (n := n) mu hE hEsymm hK hKTarget U)

/-- The base row of the buffered pullback is the chart pullback `U ∘ E`
on the open buffer. -/
theorem bufferedLocalizedH2Pullback_base_ae
    (mu : SobolevSpace.Approximation.Mollifier n)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    {K V : Set (ℝ^n)}
    (hK : IsCompact K) (hKTarget : K ⊆ E.target)
    (hV : IsOpen V)
    (hVPatch : V ⊆
      SobolevSpace.WeakChangeOfVariables.compactPullbackSource
        (n := n) E K)
    (U : W^{2,2}(E.target)) :
    ((((bufferedLocalizedH2Pullback
        (n := n) mu hE hEsymm hK hKTarget hV hVPatch U :
      WkpAmbientOn n 2 2 V) (baseIndex n 2) :
      DerivLp n 2 V) : ℝ^n → ℝ))
      =ᵐ[domainMeasure n V]
        fun x ↦
          ((((U : WkpAmbientOn n 2 2 E.target) (baseIndex n 2) :
            DerivLp n 2 E.target) : ℝ^n → ℝ) (E x)) := by
  have hPbase := (WeakChangeOfVariables.localizedH2Pullback_apply_ae mu hE hEsymm hK hKTarget U
    (baseIndex n 2)).trans (by
      simpa [WeakChangeOfVariables.localizedH2PullbackRow] using
        WeakChangeOfVariables.localizedSobolevPullbackBase_apply_ae (hE.of_le (by norm_num))
          hEsymm hK hKTarget U)
  exact (restrictCLM_apply_ae hV.measurableSet hVPatch _ (baseIndex n 2)).trans
    (hPbase.filter_mono (ae_mono (domainMeasure_le hVPatch)))

/-- Explicit finite Leibniz bound for one derivative row of a cutoff chart
pullback.  It consists only of `L∞` norms of cutoff derivatives and `L²`
norms of the corresponding restricted pullback rows. -/
noncomputable def bufferedLocalizedH2PullbackRowBound
    (mu : SobolevSpace.Approximation.Mollifier n)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    {K V : Set (ℝ^n)}
    (hK : IsCompact K) (hKTarget : K ⊆ E.target)
    (hV : IsOpen V)
    (hVPatch : V ⊆
      SobolevSpace.WeakChangeOfVariables.compactPullbackSource
        (n := n) E K)
    (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (U : W^{2,2}(E.target)) (a : DerivIndex n 2) : ℝ :=
  (SobolevSpace.CompactSupportLocalization.HigherOrderLocalizedCutoff.cutoffLeibnizENormBound
      (bufferedLocalizedH2Pullback
        (n := n) mu hE hEsymm hK hKTarget hV hVPatch U)
      psi a.toList.reverse).toReal

/-- Canonical compactly supported extension of a buffered chart pullback. -/
noncomputable def bufferedLocalizedH2PullbackExtension
    (mu : SobolevSpace.Approximation.Mollifier n)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    {K V Omega : Set (ℝ^n)}
    (hK : IsCompact K) (hKTarget : K ⊆ E.target)
    (hV : IsOpen V)
    (hVPatch : V ⊆
      SobolevSpace.WeakChangeOfVariables.compactPullbackSource
        (n := n) E K)
    (hVOmega : V ⊆ Omega)
    (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hpsiV : tsupport psi.toFun ⊆ V)
    (U : W^{2,2}(E.target)) :
    W^{2,2}(Omega) :=
  extendByCutoff
    (n := n) (k := 2) (p := (2 : ENNReal))
    hV hVOmega psi hpsiV
    (bufferedLocalizedH2Pullback
      (n := n) mu hE hEsymm hK hKTarget hV hVPatch U)

/-- Multiplying by a cutoff supported in the open set `V ⊆ Omega` turns an almost-everywhere
identity on `V` into one on `Omega`. -/
private theorem cutoff_mul_ae_eq_of_ae_eq {V Omega : Set (ℝ^n)} (hV : IsOpen V)
    (hVOmega : V ⊆ Omega) (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hpsiV : tsupport psi.toFun ⊆ V)
    {f g : ℝ^n → ℝ} (h : f =ᵐ[domainMeasure n V] g) :
    (fun x ↦ psi.toFun x * f x) =ᵐ[domainMeasure n Omega] fun x ↦ psi.toFun x * g x := by
  refine ae_of_ae_restrict_of_ae_restrict_compl V ?_ ?_
  · rw [domainMeasure, Measure.restrict_restrict_of_subset hVOmega]
    filter_upwards [h] with x hx
    rw [hx]
  · filter_upwards [ae_restrict_mem hV.measurableSet.compl] with x hx
    simp [image_eq_zero_of_notMem_tsupport fun hxt ↦ hx (hpsiV hxt)]

/-- The canonical extension represents the pointwise product
`ψ · (U ∘ E)` almost everywhere. -/
theorem bufferedLocalizedH2PullbackExtension_base_ae
    (mu : SobolevSpace.Approximation.Mollifier n)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    {K V Omega : Set (ℝ^n)}
    (hK : IsCompact K) (hKTarget : K ⊆ E.target)
    (hV : IsOpen V)
    (hVPatch : V ⊆
      SobolevSpace.WeakChangeOfVariables.compactPullbackSource
        (n := n) E K)
    (hVOmega : V ⊆ Omega)
    (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hpsiV : tsupport psi.toFun ⊆ V)
    (U : W^{2,2}(E.target)) :
    ((((bufferedLocalizedH2PullbackExtension
        (n := n) mu hE hEsymm hK hKTarget hV hVPatch hVOmega psi hpsiV U :
      WkpAmbientOn n 2 2 Omega) (baseIndex n 2) :
      DerivLp n 2 Omega) : ℝ^n → ℝ))
      =ᵐ[domainMeasure n Omega]
        fun x ↦ psi.toFun x *
          ((((U : WkpAmbientOn n 2 2 E.target) (baseIndex n 2) :
            DerivLp n 2 E.target) : ℝ^n → ℝ) (E x)) := by
  exact (extendByCutoff_base_ae hV hVOmega psi hpsiV _).trans (cutoff_mul_ae_eq_of_ae_eq hV hVOmega
    psi hpsiV (bufferedLocalizedH2Pullback_base_ae mu hE hEsymm hK hKTarget hV hVPatch U))

/-- Every row of the canonical extension satisfies the explicit finite
Leibniz bound. -/
theorem norm_bufferedLocalizedH2PullbackExtension_coordinate_le
    (mu : SobolevSpace.Approximation.Mollifier n)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    {K V Omega : Set (ℝ^n)}
    (hK : IsCompact K) (hKTarget : K ⊆ E.target)
    (hV : IsOpen V)
    (hVPatch : V ⊆
      SobolevSpace.WeakChangeOfVariables.compactPullbackSource
        (n := n) E K)
    (hVOmega : V ⊆ Omega)
    (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hpsiV : tsupport psi.toFun ⊆ V)
    (U : W^{2,2}(E.target)) (a : DerivIndex n 2) :
    ‖((bufferedLocalizedH2PullbackExtension
        (n := n) mu hE hEsymm hK hKTarget hV hVPatch hVOmega psi hpsiV U :
      WkpAmbientOn n 2 2 Omega) a : DerivLp n 2 Omega)‖ ≤
        bufferedLocalizedH2PullbackRowBound
          (n := n) mu hE hEsymm hK hKTarget hV hVPatch psi U a := by
  simpa [bufferedLocalizedH2PullbackExtension,
    bufferedLocalizedH2PullbackRowBound] using
    norm_extendByCutoff_coordinate_le
      (n := n) (k := 2) (p := (2 : ENNReal))
      hV hVOmega psi hpsiV
      (bufferedLocalizedH2Pullback
        (n := n) mu hE hEsymm hK hKTarget hV hVPatch U) a

/-- Row bound for a buffered pullback when the Sobolev field is first
restricted from a larger target domain to the chart target. -/
noncomputable def targetSubsetBufferedPullbackRowBound
    (mu : SobolevSpace.Approximation.Mollifier n)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    {TargetBig K V : Set (ℝ^n)}
    (hTarget : E.target ⊆ TargetBig)
    (hK : IsCompact K) (hKTarget : K ⊆ E.target)
    (hV : IsOpen V)
    (hVPatch : V ⊆
      SobolevSpace.WeakChangeOfVariables.compactPullbackSource
        (n := n) E K)
    (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (U : W^{2,2}(TargetBig)) (a : DerivIndex n 2) : ℝ :=
  bufferedLocalizedH2PullbackRowBound
    (n := n) mu hE hEsymm hK hKTarget hV hVPatch psi
    (restrictCLM (n := n) (k := 2) (p := (2 : ENNReal))
      E.open_target.measurableSet hTarget U) a

/-- Canonical buffered pullback extension for a field defined on a larger
target domain. -/
noncomputable def targetSubsetBufferedH2PullbackExtension
    (mu : SobolevSpace.Approximation.Mollifier n)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    {TargetBig K V Omega : Set (ℝ^n)}
    (hTarget : E.target ⊆ TargetBig)
    (hK : IsCompact K) (hKTarget : K ⊆ E.target)
    (hV : IsOpen V)
    (hVPatch : V ⊆
      SobolevSpace.WeakChangeOfVariables.compactPullbackSource
        (n := n) E K)
    (hVOmega : V ⊆ Omega)
    (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hpsiV : tsupport psi.toFun ⊆ V)
    (U : W^{2,2}(TargetBig)) :
    W^{2,2}(Omega) :=
  bufferedLocalizedH2PullbackExtension
    (n := n) mu hE hEsymm hK hKTarget hV hVPatch hVOmega psi hpsiV
    (restrictCLM (n := n) (k := 2) (p := (2 : ENNReal))
      E.open_target.measurableSet hTarget U)

/-- The target-subset construction represents `ψ · (U ∘ E)` almost
everywhere on the ambient domain. -/
theorem targetSubsetBufferedH2PullbackExtension_base_ae
    (mu : SobolevSpace.Approximation.Mollifier n)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    {TargetBig K V Omega : Set (ℝ^n)}
    (hTarget : E.target ⊆ TargetBig)
    (hK : IsCompact K) (hKTarget : K ⊆ E.target)
    (hV : IsOpen V)
    (hVPatch : V ⊆
      SobolevSpace.WeakChangeOfVariables.compactPullbackSource
        (n := n) E K)
    (hVOmega : V ⊆ Omega)
    (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hpsiV : tsupport psi.toFun ⊆ V)
    (U : W^{2,2}(TargetBig)) :
    ((((targetSubsetBufferedH2PullbackExtension
        (n := n) mu hE hEsymm hTarget hK hKTarget hV hVPatch hVOmega
          psi hpsiV U :
      WkpAmbientOn n 2 2 Omega) (baseIndex n 2) :
      DerivLp n 2 Omega) : ℝ^n → ℝ))
      =ᵐ[domainMeasure n Omega]
        fun x ↦ psi.toFun x *
          ((((U : WkpAmbientOn n 2 2 TargetBig) (baseIndex n 2) :
            DerivLp n 2 TargetBig) : ℝ^n → ℝ) (E x)) := by
  refine (bufferedLocalizedH2PullbackExtension_base_ae mu hE hEsymm hK hKTarget hV hVPatch hVOmega
    psi hpsiV _).trans (cutoff_mul_ae_eq_of_ae_eq hV hVOmega psi hpsiV ?_)
  have hVSource : V ⊆ E.source := fun x hx ↦ by
    obtain ⟨y, hyK, rfl⟩ := hVPatch hx
    exact E.map_target (hKTarget hyK)
  exact ((WeakChangeOfVariables.quasiMeasurePreserving_partialHomeomorph
    (hE.of_le (by norm_num)) hEsymm).ae_eq_comp (restrictCLM_apply_ae E.open_target.measurableSet
      hTarget U (baseIndex n 2))).filter_mono (ae_mono (domainMeasure_le hVSource))

/-- Componentwise row bound for the target-subset construction. -/
theorem norm_targetSubsetBufferedH2PullbackExtension_coordinate_le
    (mu : SobolevSpace.Approximation.Mollifier n)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    {TargetBig K V Omega : Set (ℝ^n)}
    (hTarget : E.target ⊆ TargetBig)
    (hK : IsCompact K) (hKTarget : K ⊆ E.target)
    (hV : IsOpen V)
    (hVPatch : V ⊆
      SobolevSpace.WeakChangeOfVariables.compactPullbackSource
        (n := n) E K)
    (hVOmega : V ⊆ Omega)
    (psi : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hpsiV : tsupport psi.toFun ⊆ V)
    (U : W^{2,2}(TargetBig)) (a : DerivIndex n 2) :
    ‖((targetSubsetBufferedH2PullbackExtension
        (n := n) mu hE hEsymm hTarget hK hKTarget hV hVPatch hVOmega
          psi hpsiV U :
      WkpAmbientOn n 2 2 Omega) a : DerivLp n 2 Omega)‖ ≤
        targetSubsetBufferedPullbackRowBound
          (n := n) mu hE hEsymm hTarget hK hKTarget hV hVPatch psi U a := by
  simpa [targetSubsetBufferedH2PullbackExtension,
    targetSubsetBufferedPullbackRowBound] using
    norm_bufferedLocalizedH2PullbackExtension_coordinate_le
      (n := n) mu hE hEsymm hK hKTarget hV hVPatch hVOmega psi hpsiV
      (restrictCLM (n := n) (k := 2) (p := (2 : ENNReal))
        E.open_target.measurableSet hTarget U) a

end SobolevSpace.GraphSpace.BoundaryRegularity
