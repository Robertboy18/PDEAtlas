/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.ZeroExtension.Norm
public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.ZeroExtension.Supported

/-!
# Bounded zero extension on a supported Gagliardo submodule

For measurable A ⊆ B, functions supported a.e. in S extend by zero whenever A ∩ S
has a positive gap from B ∖ A. The operator acts on the Gagliardo graph
spaces. Its physical value is the indicator of A times the original representative,
independently of all representative and gap choices. The construction uses neither
cutoff multiplication nor completeness of the codomain.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FractionalSobolev

namespace SobolevSpace.Fractional.GagliardoSpace.ZeroExtension

variable {n : ℕ} {s δ : ℝ} {A B S : Set (ℝ^n)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (hp : p ≠ ∞) (hs : 0 < s) (hδ : 0 < δ)
  (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B)
  (hgap : ∀ x ∈ A ∩ S, ∀ y ∈ B \ A, δ ≤ dist x y)

/-- Extend the supported representative by zero to the larger measurable domain. -/
def extend (u : supportedSubmodule n s A S (p := p) (F := F)) :
    W^{s,p}(B; F) :=
  ofFunction (A.indicator (representative u))
    (Localization.memGagliardo_indicator_of_gap hs hδ hA hB hAB
      (fun x hx hu ↦ hgap x ⟨hx, mem_of_representative_ne_zero u hu⟩)
      (memGagliardo_representative u)
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp)

/-- The extension has the original Lᵖ representative on A and is zero on B ∖ A. -/
theorem toLp_extend_apply_ae (u : supportedSubmodule n s A S (p := p) (F := F)) :
    (toLp n s B (extend hp hs hδ hA hB hAB hgap u) : ℝ^n → F)
      =ᵐ[volume.restrict B] A.indicator (toLp n s A u.val) := by
  have hind : A.indicator (representative u) =ᵐ[volume.restrict B]
      A.indicator (toLp n s A u.val) :=
    ae_mono Measure.restrict_le_self
      ((ae_eq_restrict_iff_indicator_ae_eq hA).mp (representative_ae u).symm)
  exact (toLp_ofFunction_apply_ae _ _).trans hind

/-- The uniform support gap gives the explicit finite-p graph norm bound. -/
theorem norm_extend_le (u : supportedSubmodule n s A S (p := p) (F := F)) :
    ‖extend hp hs hδ hA hB hAB hgap u‖ ≤ normBound n s δ p * ‖u‖ :=
  norm_le_of_indicator_ae hp hs hδ hA hB hAB
    (fun x hx hu ↦ hgap x ⟨hx, mem_of_representative_ne_zero u hu⟩)
    u.val (extend hp hs hδ hA hB hAB hgap u) (representative_ae u)
    (toLp_ofFunction_apply_ae _ _)

/-- Zero extension is additive on the supported submodule. -/
theorem extend_add (u v : supportedSubmodule n s A S (p := p) (F := F)) :
    extend hp hs hδ hA hB hAB hgap (u + v) =
      extend hp hs hδ hA hB hAB hgap u + extend hp hs hδ hA hB hAB hgap v := by
  classical
  apply toLp_injective
  apply Lp.ext
  have hin := Lp.coeFn_add (toLp n s A u.val) (toLp n s A v.val)
  have hi := ae_mono (μ := volume.restrict B) Measure.restrict_le_self
    ((ae_restrict_iff' hA).mp hin)
  have hout := Lp.coeFn_add
    (toLp n s B (extend hp hs hδ hA hB hAB hgap u))
    (toLp n s B (extend hp hs hδ hA hB hAB hgap v))
  simp only [map_add]
  filter_upwards [toLp_extend_apply_ae hp hs hδ hA hB hAB hgap (u + v),
    toLp_extend_apply_ae hp hs hδ hA hB hAB hgap u,
    toLp_extend_apply_ae hp hs hδ hA hB hAB hgap v, hi, hout]
    with x hsum hu hv hi ho
  rw [hsum, ho]
  simp only [Pi.add_apply, hu, hv, Submodule.coe_add, map_add]
  by_cases hx : x ∈ A
  · simp only [indicator_of_mem hx, hi hx, Pi.add_apply]
  · simp only [indicator_of_notMem hx, add_zero]

/-- Zero extension commutes with real scalar multiplication. -/
theorem extend_smul (c : ℝ) (u : supportedSubmodule n s A S (p := p) (F := F)) :
    extend hp hs hδ hA hB hAB hgap (c • u) =
      c • extend hp hs hδ hA hB hAB hgap u := by
  classical
  apply toLp_injective
  apply Lp.ext
  have hin := Lp.coeFn_smul c (toLp n s A u.val)
  have hi := ae_mono (μ := volume.restrict B) Measure.restrict_le_self
    ((ae_restrict_iff' hA).mp hin)
  have hout := Lp.coeFn_smul c (toLp n s B (extend hp hs hδ hA hB hAB hgap u))
  simp only [map_smul]
  filter_upwards [toLp_extend_apply_ae hp hs hδ hA hB hAB hgap (c • u),
    toLp_extend_apply_ae hp hs hδ hA hB hAB hgap u, hi, hout]
    with x hcu hu hi ho
  rw [hcu, ho]
  simp only [Pi.smul_apply, hu, Submodule.coe_smul, map_smul]
  by_cases hx : x ∈ A
  · simp only [indicator_of_mem hx, hi hx, Pi.smul_apply]
  · simp only [indicator_of_notMem hx, smul_zero]

/-- The bounded linear relative zero-extension operator on the supported graph submodule. -/
def extendL :
    supportedSubmodule n s A S (p := p) (F := F) →L[ℝ]
      W^{s,p}(B; F) :=
  LinearMap.mkContinuous
    { toFun := extend hp hs hδ hA hB hAB hgap
      map_add' := extend_add hp hs hδ hA hB hAB hgap
      map_smul' := extend_smul hp hs hδ hA hB hAB hgap }
    (normBound n s δ p) (norm_extend_le hp hs hδ hA hB hAB hgap)

/-- The bundled map is the zero extension of the underlying Lᵖ representative. -/
theorem toLp_extendL_apply_ae
    (u : supportedSubmodule n s A S (p := p) (F := F)) :
    (toLp n s B (extendL hp hs hδ hA hB hAB hgap u) : ℝ^n → F)
      =ᵐ[volume.restrict B] A.indicator (toLp n s A u.val) :=
  toLp_extend_apply_ae hp hs hδ hA hB hAB hgap u

/-- The operator norm is controlled by the explicit support-gap constant. -/
theorem norm_extendL_le :
    ‖extendL (F := F) hp hs hδ hA hB hAB hgap‖ ≤ normBound n s δ p := by
  -- Fix the inherited seminormed structures before unifying the bundled map.
  exact @ContinuousLinearMap.opNorm_le_bound ℝ ℝ
    (supportedSubmodule n s A S (p := p) (F := F))
    (W^{s,p}(B; F))
    (inferInstance) (inferInstance) (inferInstance) (inferInstance)
    (inferInstance) (inferInstance) (RingHom.id ℝ)
    (extendL hp hs hδ hA hB hAB hgap) _
    (normBound_nonneg n s hδ p) (norm_extend_le hp hs hδ hA hB hAB hgap)

/-- Any physical representative can be used in the zero-extension formula. -/
theorem toLp_extendL_of_ae
    (u : supportedSubmodule n s A S (p := p) (F := F)) {f : ℝ^n → F}
    (hf : (toLp n s A u.val : ℝ^n → F) =ᵐ[volume.restrict A] f) :
    (toLp n s B (extendL hp hs hδ hA hB hAB hgap u) : ℝ^n → F)
      =ᵐ[volume.restrict B] A.indicator f :=
  (toLp_extendL_apply_ae hp hs hδ hA hB hAB hgap u).trans
    (ae_mono Measure.restrict_le_self ((ae_eq_restrict_iff_indicator_ae_eq hA).mp hf))

include hp hs hδ hA hB hAB hgap in
/-- An a.e. support condition suffices for intrinsic membership of the extended function. -/
theorem memGagliardo_indicator_of_ae_support {f : ℝ^n → F}
    (hf : MemGagliardo n s A f (p := p))
    (hS : ∀ᵐ x ∂volume.restrict A, x ∉ S → f x = 0) :
    MemGagliardo n s B (A.indicator f) (p := p) :=
  (memGagliardo_iff_exists_gagliardoSpace _).2
    ⟨extendL hp hs hδ hA hB hAB hgap (supportedOfFunction f hf hS),
      toLp_extendL_of_ae hp hs hδ hA hB hAB hgap _
        (toLp_ofFunction_apply_ae f hf)⟩

/-- Applying the operator to a physical function agrees with the ordinary graph constructor. -/
theorem extendL_ofFunction {f : ℝ^n → F}
    (hf : MemGagliardo n s A f (p := p))
    (hS : ∀ᵐ x ∂volume.restrict A, x ∉ S → f x = 0) :
    extendL hp hs hδ hA hB hAB hgap (supportedOfFunction f hf hS) =
      ofFunction (A.indicator f)
        (memGagliardo_indicator_of_ae_support hp hs hδ hA hB hAB hgap hf hS) := by
  apply toLp_injective
  apply Lp.ext
  have hsource := toLp_ofFunction_apply_ae f hf
  have hext := toLp_extendL_of_ae hp hs hδ hA hB hAB hgap
    (supportedOfFunction f hf hS) hsource
  exact hext.trans (toLp_ofFunction_apply_ae _ _).symm

/-- The gap radius controls the bound but does not change the operator. -/
theorem extendL_eq {δ' : ℝ} (hδ' : 0 < δ')
    (hgap' : ∀ x ∈ A ∩ S, ∀ y ∈ B \ A, δ' ≤ dist x y) :
    extendL (F := F) hp hs hδ hA hB hAB hgap =
      extendL hp hs hδ' hA hB hAB hgap' := by
  apply ContinuousLinearMap.ext
  intro u
  apply toLp_injective
  apply Lp.ext
  exact (toLp_extendL_apply_ae hp hs hδ hA hB hAB hgap u).trans
    (toLp_extendL_apply_ae hp hs hδ' hA hB hAB hgap' u).symm

end SobolevSpace.Fractional.GagliardoSpace.ZeroExtension
