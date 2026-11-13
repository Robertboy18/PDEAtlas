/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Restriction
public import PDE.Analysis.Operator.KernelQuotient
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.WeakDerivative
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Conjugation

/-!
# Fractional Sobolev spaces on a domain by restriction

`H^s(Ω)` is the space of restrictions to `Ω` of whole-space `H^s(ℝ^n)` functions. This
construction covers every `s ≥ 0`, whereas the intrinsic Gagliardo space of
`Fractional.Domain.Slobodeckij` describes fractional regularity only for `0 < s < 1`.

Both constructions are stated for real-valued functions so that they can be compared. The
whole-space extension is stored directly in the canonical real space `HsSpaceReal`, rather than as a
complex `H^s` element accompanied by a duplicate realness proof.

The primary construction is the Hilbert quotient

`HsSpaceReal n s / ker(hsRestrictionCLM n s hs Ω)`.

It carries the usual quotient norm, embeds injectively into `L²(Ω)`, and every class has a canonical
norm-minimizing whole-space extension orthogonal to the kernel. The raw-function predicate
`MemHsRestriction` is a representative-level interface and is proved equivalent to having an `L²(Ω)`
value in the completed quotient.

Restriction is measured against `volume.restrict Ω`, so values off `Ω` are irrelevant. No
measurability assumption on `Ω` is needed for this measure-space construction.

The definition of `H^s(Ω)` as restrictions of `H^s(ℝ^n)` functions with the quotient norm
`‖u‖ = inf {‖U‖ : U|_Ω = u}` is the one used, for instance, by McLean. The quotient construction
makes the infimum a norm and identifies the minimiser as the orthogonal projection onto the
kernel's complement.

## Main definitions

* `SobolevSpace.Fractional.hsRestrictionCLM`: continuous restriction into
  `L²(Ω)`.
* `SobolevSpace.Fractional.HsRestrictionSpace`: the complete Hilbert quotient.
* `SobolevSpace.Fractional.HsRestrictionSpace.minimalExtension`: the canonical
  least-norm whole-space extension.
* `SobolevSpace.Fractional.HsRestrictionSpace.restrictCLM`: contractive
  restriction between quotient spaces on nested domains.
* `SobolevSpace.Fractional.MemHsRestriction`: membership in the restriction space.
* `SobolevSpace.Fractional.hsRestrictionSubmodule`: the corresponding real
  submodule of raw functions.

## Comparison with the Slobodeckij space

For `0 < s < 1` the comparison needs an extension operator. It is proved on the
upper half-space in `Gagliardo.HalfSpace` and on domains with a
`SobolevSpace.Boundary.C1ExtensionAtlas` in `Gagliardo.C1`.

## References

* W. McLean, *Strongly Elliptic Systems and Boundary Integral Equations*, Cambridge University
  Press, 2000, for `H^s(Ω)` as the space of restrictions of `H^s(ℝ^n)` with the quotient norm.
-/

@[expose] public section

open MeasureTheory
open scoped BesselPotentialSpace ENNReal SchwartzMap

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)}

open BesselPotentialSpace


/-- Restricting Lebesgue measure is monotone in the set. -/
theorem restrictedVolume_mono {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂) :
    (volume : Measure (ℝ^n)).restrict Ω₁ ≤
      (volume : Measure (ℝ^n)).restrict Ω₂ :=
  Measure.restrict_mono hΩ le_rfl

/-- Restrict a real `L²(ℝ^n)` class to `L²(Ω)`. -/
noncomputable def restrictL2 (n : ℕ) (Ω : Set (ℝ^n)) :
    Lp ℝ 2 (volume : Measure (ℝ^n)) →L[ℝ]
      Lp ℝ 2 ((volume : Measure (ℝ^n)).restrict Ω) :=
  MeasureTheory.Lp.restrictionCLMOfLE
    Measure.restrict_le_self

private theorem restrictL2_apply_ae (f : Lp ℝ 2 (volume : Measure (ℝ^n))) :
    (restrictL2 n Ω f : ℝ^n → ℝ)
      =ᵐ[(volume : Measure (ℝ^n)).restrict Ω] (f : ℝ^n → ℝ) :=
  MeasureTheory.Lp.restrictionCLMOfLE_apply_ae
    Measure.restrict_le_self f

/-- Restrict a real `L²` class from a larger domain to a subdomain. -/
noncomputable def restrictDomainL2 {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂) :
    Lp ℝ 2 ((volume : Measure (ℝ^n)).restrict Ω₂) →L[ℝ]
      Lp ℝ 2 ((volume : Measure (ℝ^n)).restrict Ω₁) :=
  MeasureTheory.Lp.restrictionCLMOfLE
    (restrictedVolume_mono (n := n) hΩ)

/-- Restriction between domain `L²` spaces is contractive. -/
theorem norm_restrictDomainL2_apply_le
    {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂)
    (f : Lp ℝ 2 ((volume : Measure (ℝ^n)).restrict Ω₂)) :
    ‖restrictDomainL2 hΩ f‖ ≤ ‖f‖ :=
  MeasureTheory.Lp.norm_restrictionCLMOfLE_apply_le
    (restrictedVolume_mono (n := n) hΩ) f

/-- The restricted domain `L²` class represents the same function almost
everywhere on the subdomain. -/
theorem restrictDomainL2_apply_ae
    {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂)
    (f : Lp ℝ 2 ((volume : Measure (ℝ^n)).restrict Ω₂)) :
    (restrictDomainL2 hΩ f : ℝ^n → ℝ)
      =ᵐ[(volume : Measure (ℝ^n)).restrict Ω₁] (f : ℝ^n → ℝ) :=
  MeasureTheory.Lp.restrictionCLMOfLE_apply_ae
    (restrictedVolume_mono (n := n) hΩ) f

/-- Restricting a domain `L²` class to the same domain is the identity. -/
theorem restrictDomainL2_self (Ω : Set (ℝ^n)) :
    restrictDomainL2 (n := n) (Set.Subset.rfl : Ω ⊆ Ω) =
      ContinuousLinearMap.id ℝ
        (Lp ℝ 2 ((volume : Measure (ℝ^n)).restrict Ω)) := by
  simpa only [restrictDomainL2] using
    (MeasureTheory.Lp.restrictionCLMOfLE_refl
      (E := ℝ) (p := (2 : ℝ≥0∞))
      (μ := (volume : Measure (ℝ^n)).restrict Ω))

/-- Domain `L²` restriction is functorial under nested inclusions. -/
theorem restrictDomainL2_comp
    {Ω₁ Ω₂ Ω₃ : Set (ℝ^n)}
    (h₁₂ : Ω₁ ⊆ Ω₂) (h₂₃ : Ω₂ ⊆ Ω₃) :
    (restrictDomainL2 (n := n) h₁₂).comp
        (restrictDomainL2 (n := n) h₂₃) =
      restrictDomainL2 (n := n) (h₁₂.trans h₂₃) := by
  simpa only [restrictDomainL2] using
    (MeasureTheory.Lp.restrictionCLMOfLE_trans
      (E := ℝ) (p := (2 : ℝ≥0∞))
      (restrictedVolume_mono (n := n) h₁₂)
      (restrictedVolume_mono (n := n) h₂₃))

/-- Restrict a real whole-space `H^s` function to its `L²(Ω)` class. -/
noncomputable def hsRestrictionCLM (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (Ω : Set (ℝ^n)) :
    HsSpaceReal n s →L[ℝ]
      Lp ℝ 2 ((volume : Measure (ℝ^n)).restrict Ω) :=
  (restrictL2 n Ω).comp (HsSpaceReal.toL2FunCLM n hs)

/-- The continuous restriction map agrees almost everywhere with the real part
of the physical `L²` representative. -/
theorem hsRestrictionCLM_apply_ae (hs : 0 ≤ s) (u : HsSpaceReal n s) :
    (hsRestrictionCLM n s hs Ω u : ℝ^n → ℝ)
      =ᵐ[(volume : Measure (ℝ^n)).restrict Ω]
        reOfL2 (toL2Fun hs u.1) := by
  have hphysical :=
    ae_restrict_of_ae
      (s := Ω) (HsSpaceReal.toL2FunCLM_apply_ae hs u)
  filter_upwards [restrictL2_apply_ae
    (n := n) (Ω := Ω) (HsSpaceReal.toL2FunCLM n hs u),
    hphysical] with x hrestrict hreal
  simpa [hsRestrictionCLM, reOfL2] using hrestrict.trans hreal

/-- Restricting the `L²` realization of a whole-space function to a subdomain
agrees with direct restriction to that subdomain. -/
theorem restrictDomainL2_hsRestrictionCLM
    (hs : 0 ≤ s) {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂)
    (u : HsSpaceReal n s) :
    restrictDomainL2 hΩ (hsRestrictionCLM n s hs Ω₂ u) =
      hsRestrictionCLM n s hs Ω₁ u := by
  apply Lp.ext
  have hbig :
      (hsRestrictionCLM n s hs Ω₂ u : ℝ^n → ℝ)
        =ᵐ[(volume : Measure (ℝ^n)).restrict Ω₁]
          reOfL2 (toL2Fun hs u.1) :=
    ae_mono (Measure.restrict_mono hΩ le_rfl)
      (hsRestrictionCLM_apply_ae hs u)
  exact
    (restrictDomainL2_apply_ae hΩ (hsRestrictionCLM n s hs Ω₂ u)).trans
      (hbig.trans (hsRestrictionCLM_apply_ae hs u).symm)

/-- The closed subspace of whole-space functions vanishing almost everywhere
on `Ω`. -/
noncomputable def hsRestrictionKernel (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (Ω : Set (ℝ^n)) : ClosedSubmodule ℝ (HsSpaceReal n s) :=
  ContinuousLinearMap.KernelQuotient.closedKernel
    (hsRestrictionCLM n s hs Ω)

/-- The restriction definition of `H^s(Ω)`, with its canonical quotient Hilbert
norm.  Two whole-space extensions define the same element exactly when they
agree almost everywhere on `Ω`. -/
noncomputable abbrev HsRestrictionSpace (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (Ω : Set (ℝ^n)) : Type :=
  HsSpaceReal n s ⧸ (hsRestrictionCLM n s hs Ω).ker

namespace HsRestrictionSpace

/-- Send a whole-space function to its restriction class. -/
noncomputable def ofWholeSpace (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (Ω : Set (ℝ^n)) :
    HsSpaceReal n s →L[ℝ] HsRestrictionSpace n s hs Ω :=
  (hsRestrictionCLM n s hs Ω).ker.mkQL

/-- Every restriction class has a whole-space representative. -/
theorem ofWholeSpace_surjective (hs : 0 ≤ s) :
    Function.Surjective
      (ofWholeSpace n s hs Ω) :=
  (ContinuousLinearMap.KernelQuotient.closedKernel
    (hsRestrictionCLM n s hs Ω)).toSubmodule.mkQ_surjective

/-- Realize a restriction class as its `L²(Ω)` value. -/
noncomputable def toLp (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (Ω : Set (ℝ^n)) :
    HsRestrictionSpace n s hs Ω →L[ℝ]
      Lp ℝ 2 ((volume : Measure (ℝ^n)).restrict Ω) :=
  (hsRestrictionCLM n s hs Ω).ker.liftQL (hsRestrictionCLM n s hs Ω) le_rfl

/-- `L²(Ω)` realization factors restriction through the quotient class. -/
@[simp] theorem toLp_ofWholeSpace (hs : 0 ≤ s) (u : HsSpaceReal n s) :
    toLp n s hs Ω (ofWholeSpace n s hs Ω u) =
      hsRestrictionCLM n s hs Ω u :=
  rfl

/-- Distinct restriction classes have distinct `L²(Ω)` values. -/
theorem toLp_injective (hs : 0 ≤ s) :
    Function.Injective (toLp n s hs Ω) :=
  LinearMap.ker_eq_bot.mp
    (Submodule.ker_liftQ_eq_bot (hsRestrictionCLM n s hs Ω).ker
      (hsRestrictionCLM n s hs Ω).toLinearMap le_rfl le_rfl)

/-- The canonical norm-minimizing whole-space extension of a restriction
class. -/
noncomputable def minimalExtension (n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (Ω : Set (ℝ^n)) :
    HsRestrictionSpace n s hs Ω →L[ℝ] HsSpaceReal n s :=
  ContinuousLinearMap.KernelQuotient.representative
    (hsRestrictionCLM n s hs Ω)

/-- Taking the restriction class of the canonical extension is the identity. -/
@[simp] theorem ofWholeSpace_minimalExtension (hs : 0 ≤ s)
    (q : HsRestrictionSpace n s hs Ω) :
    ofWholeSpace n s hs Ω (minimalExtension n s hs Ω q) = q :=
  ContinuousLinearMap.KernelQuotient.mk_representative
    (hsRestrictionCLM n s hs Ω) q

/-- The canonical extension preserves the quotient norm. -/
theorem norm_minimalExtension (hs : 0 ≤ s)
    (q : HsRestrictionSpace n s hs Ω) :
    ‖minimalExtension n s hs Ω q‖ = ‖q‖ :=
  ContinuousLinearMap.KernelQuotient.norm_representative
    (hsRestrictionCLM n s hs Ω) q

/-- The canonical extension realizes the represented `L²(Ω)` value. -/
theorem toLp_minimalExtension (hs : 0 ≤ s)
    (q : HsRestrictionSpace n s hs Ω) :
    hsRestrictionCLM n s hs Ω (minimalExtension n s hs Ω q) =
      toLp n s hs Ω q :=
  ContinuousLinearMap.KernelQuotient.apply_representative
    (hsRestrictionCLM n s hs Ω) q

/-- The canonical extension is orthogonal to every whole-space function
vanishing on `Ω`. -/
theorem minimalExtension_mem_orthogonal (hs : 0 ≤ s)
    (q : HsRestrictionSpace n s hs Ω) :
    minimalExtension n s hs Ω q ∈
      (hsRestrictionKernel n s hs Ω).toSubmodule.orthogonal :=
  ContinuousLinearMap.KernelQuotient.representative_mem_orthogonal
    (hsRestrictionCLM n s hs Ω) q

/-- The canonical extension has minimal norm among all extensions with the same
`L²(Ω)` value. -/
theorem norm_minimalExtension_le_of_toLp_eq (hs : 0 ≤ s)
    (q : HsRestrictionSpace n s hs Ω) (u : HsSpaceReal n s)
    (hu : hsRestrictionCLM n s hs Ω u = toLp n s hs Ω q) :
    ‖minimalExtension n s hs Ω q‖ ≤ ‖u‖ :=
  ContinuousLinearMap.KernelQuotient.norm_representative_le_of_apply_eq
    (hsRestrictionCLM n s hs Ω) q u hu

/-- The canonical extension is the unique extension orthogonal to the
restriction kernel. -/
theorem minimalExtension_eq_of_mem_orthogonal (hs : 0 ≤ s)
    (q : HsRestrictionSpace n s hs Ω) (u : HsSpaceReal n s)
    (hu : u ∈ (hsRestrictionKernel n s hs Ω).toSubmodule.orthogonal)
    (hrestrict : hsRestrictionCLM n s hs Ω u = toLp n s hs Ω q) :
    minimalExtension n s hs Ω q = u :=
  ContinuousLinearMap.KernelQuotient.representative_eq_of_mem_orthogonal
    (hsRestrictionCLM n s hs Ω) q u hu hrestrict

/-! ## Restriction to a subdomain -/

private theorem hsRestrictionCLM_eq_zero_mono
    (hs : 0 ≤ s) {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂)
    (u : HsSpaceReal n s) (hu : hsRestrictionCLM n s hs Ω₂ u = 0) :
    hsRestrictionCLM n s hs Ω₁ u = 0 := by
  rw [← restrictDomainL2_hsRestrictionCLM hs hΩ u, hu, map_zero]

/-- Continuous restriction of a quotient restriction-space element from a
larger domain to a subdomain. -/
noncomputable def restrictCLM
    (hs : 0 ≤ s) {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂) :
    HsRestrictionSpace n s hs Ω₂ →L[ℝ]
      HsRestrictionSpace n s hs Ω₁ :=
  ContinuousLinearMap.KernelQuotient.map
    (hsRestrictionCLM n s hs Ω₂)
    (hsRestrictionCLM n s hs Ω₁)
    (ContinuousLinearMap.id ℝ (HsSpaceReal n s))
    (by
      intro u hu
      simpa using hsRestrictionCLM_eq_zero_mono hs hΩ u hu)

/-- Restriction sends a whole-space representative to its class on the
subdomain. -/
@[simp]
theorem restrictCLM_ofWholeSpace
    (hs : 0 ≤ s) {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂)
    (u : HsSpaceReal n s) :
    restrictCLM hs hΩ (ofWholeSpace n s hs Ω₂ u) =
      ofWholeSpace n s hs Ω₁ u :=
  ContinuousLinearMap.KernelQuotient.map_mk
    (hsRestrictionCLM n s hs Ω₂)
    (hsRestrictionCLM n s hs Ω₁)
    (ContinuousLinearMap.id ℝ (HsSpaceReal n s))
    (by
      intro v hv
      simpa using hsRestrictionCLM_eq_zero_mono hs hΩ v hv)
    u

/-- The `L²` realization of quotient restriction is the canonical restriction
of the original realization. -/
theorem toLp_restrictCLM
    (hs : 0 ≤ s) {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂)
    (q : HsRestrictionSpace n s hs Ω₂) :
    toLp n s hs Ω₁ (restrictCLM hs hΩ q) =
      restrictDomainL2 hΩ (toLp n s hs Ω₂ q) := by
  obtain ⟨u, rfl⟩ := ofWholeSpace_surjective (n := n) (s := s) (Ω := Ω₂) hs q
  rw [restrictCLM_ofWholeSpace, toLp_ofWholeSpace, toLp_ofWholeSpace]
  exact (restrictDomainL2_hsRestrictionCLM hs hΩ u).symm

/-- Quotient restriction preserves representatives almost everywhere on the
subdomain. -/
theorem toLp_restrictCLM_apply_ae
    (hs : 0 ≤ s) {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂)
    (q : HsRestrictionSpace n s hs Ω₂) :
    (toLp n s hs Ω₁ (restrictCLM hs hΩ q) : ℝ^n → ℝ)
      =ᵐ[(volume : Measure (ℝ^n)).restrict Ω₁]
        (toLp n s hs Ω₂ q : ℝ^n → ℝ) := by
  rw [toLp_restrictCLM]
  exact restrictDomainL2_apply_ae hΩ (toLp n s hs Ω₂ q)

/-- Restriction between quotient restriction spaces is contractive. -/
theorem norm_restrictCLM_apply_le
    (hs : 0 ≤ s) {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂)
    (q : HsRestrictionSpace n s hs Ω₂) :
    ‖restrictCLM hs hΩ q‖ ≤ ‖q‖ := by
  unfold restrictCLM
  simpa using
    ContinuousLinearMap.KernelQuotient.norm_map_apply_le
      (hsRestrictionCLM n s hs Ω₂)
      (hsRestrictionCLM n s hs Ω₁)
      (ContinuousLinearMap.id ℝ (HsSpaceReal n s))
      (by
        intro u hu
        simpa using hsRestrictionCLM_eq_zero_mono hs hΩ u hu)
      (C := 1) (fun u ↦ by simp) q

/-- The operator norm of quotient restriction is at most one. -/
theorem norm_restrictCLM_le_one
    (hs : 0 ≤ s) {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂) :
    ‖restrictCLM (n := n) (s := s) hs hΩ‖ ≤ 1 :=
  (restrictCLM (n := n) (s := s) hs hΩ).opNorm_le_bound zero_le_one
    (fun q ↦ by simpa using norm_restrictCLM_apply_le hs hΩ q)

/-- Restriction to a subdomain is surjective: every smaller-domain class is
represented by the same whole-space function on the larger domain. -/
theorem restrictCLM_surjective
    (hs : 0 ≤ s) {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂) :
    Function.Surjective
      (restrictCLM (n := n) (s := s) hs hΩ) := by
  intro q
  refine ⟨ofWholeSpace n s hs Ω₂ (minimalExtension n s hs Ω₁ q), ?_⟩
  rw [restrictCLM_ofWholeSpace, ofWholeSpace_minimalExtension]

/-- Restricting to the same domain is the identity. -/
theorem restrictCLM_self (hs : 0 ≤ s) (Ω : Set (ℝ^n)) :
    restrictCLM (n := n) (s := s) hs
        (Set.Subset.rfl : Ω ⊆ Ω) =
      ContinuousLinearMap.id ℝ (HsRestrictionSpace n s hs Ω) := by
  apply ContinuousLinearMap.ext
  intro q
  obtain ⟨u, rfl⟩ := ofWholeSpace_surjective (n := n) (s := s) (Ω := Ω) hs q
  simp

/-- Quotient restriction is functorial under a chain of domain inclusions. -/
theorem restrictCLM_comp
    (hs : 0 ≤ s) {Ω₁ Ω₂ Ω₃ : Set (ℝ^n)}
    (h₁₂ : Ω₁ ⊆ Ω₂) (h₂₃ : Ω₂ ⊆ Ω₃) :
    (restrictCLM (n := n) (s := s) hs h₁₂).comp
        (restrictCLM (n := n) (s := s) hs h₂₃) =
      restrictCLM (n := n) (s := s) hs (h₁₂.trans h₂₃) := by
  apply ContinuousLinearMap.ext
  intro q
  obtain ⟨u, rfl⟩ := ofWholeSpace_surjective (n := n) (s := s) (Ω := Ω₃) hs q
  simp

/-- The least-norm extension of a restricted quotient class has no larger
norm than the original class. -/
theorem norm_minimalExtension_restrictCLM_le
    (hs : 0 ≤ s) {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂)
    (q : HsRestrictionSpace n s hs Ω₂) :
    ‖minimalExtension n s hs Ω₁ (restrictCLM hs hΩ q)‖ ≤ ‖q‖ := by
  rw [norm_minimalExtension]
  exact norm_restrictCLM_apply_le hs hΩ q

end HsRestrictionSpace

/-- `f` is the restriction to `Ω` of a real whole-space `H^s` function. -/
def MemHsRestriction (n : ℕ) (s : ℝ) (hs : 0 ≤ s) (Ω : Set (ℝ^n))
    (f : ℝ^n → ℝ) : Prop :=
  ∃ U : HsSpaceReal n s,
    reOfL2 (toL2Fun hs U.1) =ᵐ[(volume : Measure (ℝ^n)).restrict Ω] f

/-- The zero function is the restriction of the zero whole-space function. -/
theorem memHsRestriction_zero (hs : 0 ≤ s) :
    MemHsRestriction n s hs Ω (0 : ℝ^n → ℝ) := by
  refine ⟨0, ?_⟩
  have h : toL2Fun hs (0 : H^{s}(ℝ^n)) = 0 := by simp [toL2Fun, map_zero]
  filter_upwards [] with x
  simp [reOfL2, h]

/-- Restrictions are closed under addition: add the whole-space representatives. -/
theorem MemHsRestriction.add (hs : 0 ≤ s) {f g : ℝ^n → ℝ}
    (hf : MemHsRestriction n s hs Ω f) (hg : MemHsRestriction n s hs Ω g) :
    MemHsRestriction n s hs Ω (f + g) := by
  obtain ⟨U, hUf⟩ := hf
  obtain ⟨V, hVg⟩ := hg
  refine ⟨U + V, ?_⟩
  have hsum : reOfL2 (toL2Fun hs (U.1 + V.1))
      =ᵐ[(volume : Measure (ℝ^n))]
        reOfL2 (toL2Fun hs U.1) + reOfL2 (toL2Fun hs V.1) := by
    rw [toL2Fun_add]
    exact reOfL2_add_ae _ _
  have hsum' := ae_restrict_of_ae (μ := (volume : Measure (ℝ^n))) (s := Ω) hsum
  filter_upwards [hsum', hUf, hVg] with x hx hxU hxV
  simp [hx, hxU, hxV]

/-- Restrictions are closed under real scalar multiplication; the real scalar acts on the
complex whole-space representative through the coercion `ℝ → ℂ`. -/
theorem MemHsRestriction.smul (hs : 0 ≤ s) (c : ℝ) {f : ℝ^n → ℝ}
    (hf : MemHsRestriction n s hs Ω f) :
    MemHsRestriction n s hs Ω (c • f) := by
  obtain ⟨U, hUf⟩ := hf
  refine ⟨c • U, ?_⟩
  change reOfL2 (toL2Fun hs ((c : ℂ) • U.1))
      =ᵐ[volume.restrict Ω] c • f
  have hsm : reOfL2 (toL2Fun hs ((c : ℂ) • U.1))
      =ᵐ[(volume : Measure (ℝ^n))] c • reOfL2 (toL2Fun hs U.1) := by
    rw [toL2Fun_smul]
    exact reOfL2_smul_ae c _
  have hsm' := ae_restrict_of_ae (μ := (volume : Measure (ℝ^n))) (s := Ω) hsm
  filter_upwards [hsm', hUf] with x hx hxU
  rw [hx]
  simp [hxU]

/-- The restriction space `H^s(Ω)` as a real submodule of the function space. -/
def hsRestrictionSubmodule (n : ℕ) (s : ℝ) (hs : 0 ≤ s) (Ω : Set (ℝ^n)) :
    Submodule ℝ (ℝ^n → ℝ) where
  carrier := {f | MemHsRestriction n s hs Ω f}
  zero_mem' := memHsRestriction_zero hs
  add_mem' := MemHsRestriction.add hs
  smul_mem' c _ h := h.smul hs c

/-- Membership in `hsRestrictionSubmodule` unfolds to the raw predicate `MemHsRestriction`. -/
@[simp] theorem mem_hsRestrictionSubmodule_iff (hs : 0 ≤ s) {f : ℝ^n → ℝ} :
    f ∈ hsRestrictionSubmodule n s hs Ω ↔ MemHsRestriction n s hs Ω f := Iff.rfl

/-- Raw-function membership is exactly realization by an element of the
completed Hilbert restriction space. -/
theorem memHsRestriction_iff_exists_toLp (hs : 0 ≤ s) (f : ℝ^n → ℝ) :
    MemHsRestriction n s hs Ω f ↔
      ∃ q : HsRestrictionSpace n s hs Ω,
        (HsRestrictionSpace.toLp n s hs Ω q : ℝ^n → ℝ)
          =ᵐ[(volume : Measure (ℝ^n)).restrict Ω] f := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨HsRestrictionSpace.ofWholeSpace n s hs Ω u, ?_⟩
    rw [HsRestrictionSpace.toLp_ofWholeSpace]
    exact (hsRestrictionCLM_apply_ae hs u).trans hu
  · rintro ⟨q, hq⟩
    refine ⟨HsRestrictionSpace.minimalExtension n s hs Ω q, ?_⟩
    have hphysical :=
      hsRestrictionCLM_apply_ae (Ω := Ω) hs
        (HsRestrictionSpace.minimalExtension n s hs Ω q)
    rw [HsRestrictionSpace.toLp_minimalExtension] at hphysical
    exact hphysical.symm.trans hq

/-- Restriction is monotone in the domain: a function that is a restriction from
a larger set is one from a smaller set. -/
theorem MemHsRestriction.mono (hs : 0 ≤ s) {Ω₁ Ω₂ : Set (ℝ^n)} (h : Ω₁ ⊆ Ω₂)
    {f : ℝ^n → ℝ} (hf : MemHsRestriction n s hs Ω₂ f) :
    MemHsRestriction n s hs Ω₁ f := by
  obtain ⟨U, hUf⟩ := hf
  refine ⟨U, ?_⟩
  exact hUf.filter_mono (ae_mono (Measure.restrict_mono h le_rfl))

/-! ## Concrete inhabitants

Real Schwartz functions give elements of the restriction space. -/

/-- The real part of a real-valued Schwartz function, restricted to `Ω`, lies in
the restriction space, for every `s ≥ 0` and every `Ω`. -/
theorem memHsRestriction_reOfSchwartz (hs : 0 ≤ s) (Ω : Set (ℝ^n))
    (φ : 𝓢(ℝ^n, ℂ)) (hφ : ∀ x, (φ x).im = 0) :
    MemHsRestriction n s hs Ω (fun x ↦ (φ x).re) := by
  refine
    ⟨HsSpaceReal.ofPhysical hs (SchwartzMap.memSobolev φ).toBesselPotentialSpace
      (isRealL2_ofSchwartz hs φ hφ), ?_⟩
  have hae : reOfL2 (toL2Fun hs ((SchwartzMap.memSobolev (s := s) φ).toBesselPotentialSpace))
      =ᵐ[(volume : Measure (ℝ^n))] fun x ↦ (φ x).re := by
    rw [toL2Fun_ofSchwartz]
    filter_upwards [φ.coeFn_toLp 2 (volume : Measure (ℝ^n))] with x hx
    simp [reOfL2, hx]
  exact ae_restrict_of_ae hae

end SobolevSpace.Fractional
