/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.VectorValued.Duality
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Notation
import PDE.DistributionTheory.TestFunction.CompactCutoff
import PDE.Spaces.Sobolev.Localization.Cutoff.CompactSupport

/-!
# Extension of interior compactly supported Banach-valued derivative families

If the base and every derivative representative are supported in one compact subset of
an open domain, their weak identities extend to the whole space. A cutoff equal to one
near that compact set transfers the scalar identities, and the continuous dual recovers
the Bochner identities. This applies to localized derivative families.
-/

@[expose] public noncomputable section

open Function MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Sobolev Topology

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- An `Lp` representative supported in the domain belongs to whole-space `Lp`. -/
theorem memLp_univ_of_support_subset {f : ℝ^n → F}
    (hf : MemLp f p (domainMeasure n Ω)) (hsupp : support f ⊆ Ω) :
    MemLp f p volume := by
  have h := (memLp_indicator_iff_restrict Ω.isOpen.measurableSet.nullMeasurableSet).mpr hf
  rwa [indicator_eq_self.mpr hsupp] at h

/-- A weak derivative whose two representatives have common compact support in the
interior extends to a whole-space weak derivative, at every finite order. -/
theorem HasWeakDerivativeOn.extend_compact {α : List (Fin n)} {f g : ℝ^n → F}
    (h : HasWeakDerivativeOn Ω α f g) {C : Set ℝ^n} (hC : IsCompact C)
    (hCΩ : C ⊆ Ω) (hf : support f ⊆ C) (hg : support g ⊆ C) :
    HasWeakDerivativeOn ⊤ α f g := by
  have hfint : Integrable f volume :=
    (integrableOn_iff_integrable_of_support_subset hf).mp
      (h.locallyIntegrable_f.integrableOn_compact_subset hCΩ hC)
  have hgint : Integrable g volume :=
    (integrableOn_iff_integrable_of_support_subset hg).mp
      (h.locallyIntegrable_g.integrableOn_compact_subset hCΩ hC)
  obtain ⟨χ, hχΩ, _, hχone, _⟩ :=
    TestFunction.exists_eq_one_on_compact Ω.isOpen hC hCΩ
  apply (hasWeakDerivativeOn_iff_forall_dual
    (hfint.locallyIntegrable.locallyIntegrableOn _)
    (hgint.locallyIntegrable.locallyIntegrableOn _)).mpr
  intro L
  apply CompactSupportLocalization.hasWeakDerivativeOn_word_of_support_subset_of_cutoff_one_nhds
    Ω.isOpen (subset_univ _) hCΩ α _ _ χ hχΩ hχone
    (hasWeakDerivativeOn_real_iff.mp (h.map L))
  · intro x hx
    apply hf
    intro hfx
    exact hx (by simp [Function.comp_apply, hfx])
  · intro x hx
    apply hg
    intro hgx
    exact hx (by simp [Function.comp_apply, hgx])

/-- Package an interior compactly supported derivative family as a whole-space Sobolev
element. The functions themselves are retained as almost-everywhere representatives. -/
def extendCompactFamily (d : DerivIndex n k → ℝ^n → F)
    (hmem : ∀ a, MemLp (d a) p (domainMeasure n Ω))
    (hweak : ∀ a, HasWeakDerivativeOn Ω a.toList (d (baseIndex n k)) (d a))
    {C : Set ℝ^n} (hC : IsCompact C) (hCΩ : C ⊆ Ω)
    (hsupp : ∀ a, support (d a) ⊆ C) : W^{k,p}((⊤ : Opens ℝ^n); F) :=
  ofWeakDerivatives d
    (fun a ↦ by
      simpa [domainMeasure] using
        memLp_univ_of_support_subset (hmem a) ((hsupp a).trans hCΩ))
    (fun a ↦ (hweak a).extend_compact hC hCΩ (hsupp (baseIndex n k)) (hsupp a))

/-- Whole-space extension retains each compactly supported derivative representative. -/
theorem extendCompactFamily_apply_ae (d : DerivIndex n k → ℝ^n → F)
    (hmem : ∀ a, MemLp (d a) p (domainMeasure n Ω))
    (hweak : ∀ a, HasWeakDerivativeOn Ω a.toList (d (baseIndex n k)) (d a))
    {C : Set ℝ^n} (hC : IsCompact C) (hCΩ : C ⊆ Ω)
    (hsupp : ∀ a, support (d a) ⊆ C) (a : DerivIndex n k) :
    ((extendCompactFamily d hmem hweak hC hCΩ hsupp).val a : ℝ^n → F) =ᵐ[volume]
      d a := by
  simpa only [extendCompactFamily, domainMeasure, Opens.coe_top, Measure.restrict_univ] using
    ofWeakDerivatives_apply_ae (Ω := ⊤) (p := p) d _ _ a

end SobolevSpace.VectorValued
