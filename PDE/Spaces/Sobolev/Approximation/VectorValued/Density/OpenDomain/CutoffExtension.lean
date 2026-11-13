/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.VectorValued.Density.OpenDomain.CompactExtension
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.SmoothMultiplier

/-!
# Whole-space extension after an interior cutoff

The multiplier's finite Leibniz rows are supported in the cutoff's closed support.
For a test function supported in the open domain, the compact-family extension therefore
produces a whole-space Sobolev element with base representative equal to the localized input.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Function MeasureTheory TopologicalSpace
open scoped Distributions ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Interior cutoff multiplication followed by whole-space extension, using the
finite Leibniz representatives at every derivative coordinate. -/
def extendByCutoff (χ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hχ : tsupport χ.toFun ⊆ Ω)
    (U : W^{k,p}(Ω; F)) : W^{k,p}((⊤ : Opens ℝ^n); F) :=
  let hbound (β : List (Fin n)) (_ : β.length ≤ k) :
      MemLp (iteratedPartialDeriv β χ.toFun) ⊤ (domainMeasure n Ω) :=
    (PDE.contDiff_top_iteratedPartialDeriv χ.contDiff β).continuous.memLp_top_of_hasCompactSupport
      (hasCompactSupport_iteratedPartialDeriv χ.hasCompactSupport β) _
  extendCompactFamily (fun a ↦ smoothLeibnizRepresentative χ.toFun U a.toList)
    (fun a ↦ memLp_smoothLeibnizRepresentative χ.toFun hbound
      U a.toList a.toList_length_le)
    (fun a ↦ by
      simpa only [baseIndex_toList, smoothLeibnizRepresentative_nil] using
        WkpSpaceOn.hasWeakDerivativeOn_smul_smooth U χ.toFun χ.contDiff hbound
          a.toList a.toList_length_le)
    χ.hasCompactSupport hχ
    (fun a ↦ (subset_tsupport _).trans
      (tsupport_smoothLeibnizRepresentative_subset χ.toFun U a.toList))

/-- The extended base representative equals the cutoff times the original representative
almost everywhere in the whole space. -/
theorem extendByCutoff_base_ae (χ : 𝓓((⊤ : Opens ℝ^n), ℝ))
    (hχ : tsupport χ.toFun ⊆ Ω) (U : W^{k,p}(Ω; F)) :
    ((extendByCutoff χ hχ U).val (baseIndex n k) : ℝ^n → F) =ᵐ[volume]
      fun x ↦ χ.toFun x • U.val (baseIndex n k) x := by
  simpa only [extendByCutoff, baseIndex_toList, smoothLeibnizRepresentative_nil] using
    extendCompactFamily_apply_ae
      (fun a ↦ smoothLeibnizRepresentative χ.toFun U a.toList) _ _ χ.hasCompactSupport hχ
      _ (baseIndex n k)

end SobolevSpace.VectorValued
