/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Localization.Cutoff.HigherOrderExtension
public import PDE.Spaces.Sobolev.Extension.Lp.ZeroExtension

/-!
# Compatibility of cutoff extension with `Lᵖ`

Cutoff extension acts on the function coordinate by the same bounded `Lᵖ` map at
every Sobolev order. This compatibility permits the use of a single spatial operator
on trajectories and on their weaker time derivatives.
-/

@[expose] public section

open scoped Sobolev

namespace SobolevSpace.CompactSupportLocalization

open MeasureTheory Set GraphSpace TopologicalSpace
open scoped Distributions ENNReal

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {S T : Set ℝ^n}

/-- Extend by zero, restrict to the target domain, and multiply by a smooth cutoff. -/
noncomputable def cutoffExtendLp (hS : MeasurableSet S)
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) :
    DerivLp n p S →L[ℝ] DerivLp n p T :=
  (mulLpLeft (testFunctionLpTop ψ)).comp
    ((restrictDerivLp (subset_univ T)).comp (Extension.Lp.zeroExtendLp hS))

/-- When the cutoff vanishes on the target outside the source, cutoff extension is
represented by the ordinary product on the whole target. -/
theorem cutoffExtendLp_apply_ae (hS : MeasurableSet S) (hT : MeasurableSet T)
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ∩ T ⊆ S)
    (u : DerivLp n p S) :
    ⇑(cutoffExtendLp (T := T) hS ψ u) =ᵐ[domainMeasure n T] fun x ↦ ψ x * u x := by
  let z := Extension.Lp.zeroExtendLp hS u
  let r := restrictDerivLp (subset_univ T) z
  have hz : ⇑z =ᵐ[domainMeasure n T] S.indicator (fun x ↦ u x) :=
    (Extension.Lp.zeroExtendLp_apply_ae hS u).filter_mono
      (ae_mono (Measure.restrict_mono (subset_univ T) le_rfl))
  filter_upwards [mulLpLeft_apply_ae (testFunctionLpTop ψ) r,
    testFunctionLpTop_apply_ae (Ω := T) ψ,
    restrictDerivLp_apply_ae (subset_univ T) z, hz, ae_restrict_mem hT]
    with x hmul hcut hr hz hxT
  change (mulLpLeft (testFunctionLpTop ψ) r) x = ψ x * u x
  rw [hmul, hcut, hr, hz]
  by_cases hxS : x ∈ S
  · rw [indicator_of_mem hxS]
    rfl
  · have hzero : ψ x = 0 := by
      by_contra hne
      exact hxS (hψ ⟨subset_tsupport ψ.toFun hne, hxT⟩)
    simp [hzero]

/-- Higher-order multiplication by a cutoff agrees with the usual `L²` multiplier. -/
theorem higherOrderCutoffCLM_base (hk : 0 < k) (hS : IsOpen S)
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (U : W^{k,2}(S)) :
    wkpBaseCoordinateCLM (higherOrderCutoffCLM hk hS ψ U) =
      mulLpLeft (testFunctionLpTop ψ) (wkpBaseCoordinateCLM U) := by
  apply Lp.ext
  filter_upwards [higherOrderCutoffCLM_base_ae hk hS ψ U,
    mulLpLeft_apply_ae (testFunctionLpTop ψ) (wkpBaseCoordinateCLM U),
    testFunctionLpTop_apply_ae (Ω := S) ψ] with x hleft hright hψ
  exact hleft.trans (by rw [hright, hψ]; rfl)

namespace HigherOrderLocalizedCutoff

/-- Compactly supported Sobolev extension and `L²` cutoff extension have the same base. -/
theorem extendByCutoffCLM_base (hk : 0 < k)
    (hS : IsOpen S) (hT : IsOpen T) (hST : S ⊆ T)
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ S)
    (U : W^{k,2}(S)) :
    wkpBaseCoordinateCLM (extendByCutoffCLM hk hS hT hST ψ hψ U) =
      cutoffExtendLp (T := T) hS.measurableSet ψ (wkpBaseCoordinateCLM U) := by
  apply Lp.ext
  exact (extendByCutoff_base_ae hS hST ψ hψ U).trans
    (cutoffExtendLp_apply_ae hS.measurableSet hT.measurableSet ψ
      (fun _ hx ↦ hψ hx.1) _).symm

/-- The relative cutoff extension also agrees with the same bounded `L²` map. -/
theorem interCutoffCLM_base (hk : 0 < k) (hS : IsOpen S) (hT : IsOpen T)
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ S)
    (U : W^{k,2}((S ∩ T))) :
    wkpBaseCoordinateCLM (interCutoffCLM hk hS hT ψ hψ U) =
      cutoffExtendLp (T := T) (hS.inter hT).measurableSet ψ
        (wkpBaseCoordinateCLM U) := by
  apply Lp.ext
  exact (interCutoff_base_ae hS hT ψ hψ U).trans
    (cutoffExtendLp_apply_ae (hS.inter hT).measurableSet hT.measurableSet ψ
      (fun _ hx ↦ ⟨hψ hx.1, hx.2⟩) _).symm

end HigherOrderLocalizedCutoff

end SobolevSpace.CompactSupportLocalization
