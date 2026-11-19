/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Gagliardo.ExtensionEquivalence
public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.AtlasGluing

/-!
# Fractional Sobolev spaces on domains with a C¹ extension atlas

For `0 < s < 1` in positive dimension, `Boundary.C1ExtensionAtlas` supplies a
bounded intrinsic extension through `Extension.c1AtlasExtensionCLM`. The atlas
specifies finitely many flattening charts with globally C¹ representatives and
inverses, bounded targets, and a smooth partition of unity on the bounded open
domain. These data are stronger than a bare C¹ boundary hypothesis.

The extension sums the localized interior zero extension and the reflected
boundary pieces transported through the charts. Composing this extension with
the whole-space comparison makes the canonical map from the real restriction
Hilbert space to the intrinsic Gagliardo space an equivalence.

Both directions preserve the physical `L²(Ω)` class. The norm bounds separate the
whole-space Fourier constant from the norm of the constructed atlas extension.
`memHsRestriction_iff_memGagliardo_c1Atlas` identifies the two raw-function membership
predicates.
-/

@[expose] public section

noncomputable section

open scoped FractionalSobolev

namespace SobolevSpace.Fractional

variable {n : ℕ} [Fact (0 < n)] {s : ℝ} {Ω : Set (ℝ^n)}
variable [Boundary.C1ExtensionAtlas n Ω]

namespace HsRestrictionSpace

/-- The canonical comparison is an equivalence on a domain with a C¹ extension
atlas, using finite gluing of the intrinsic local extensions. -/
def c1EquivGagliardo (hs0 : 0 < s) (hs1 : s < 1) :
    HsRestrictionSpace n s hs0.le Ω ≃L[ℝ] W^{s,2}(Ω) :=
  equivGagliardoOfExtension hs0 hs1 (Extension.c1AtlasExtensionCLM (p := 2) (F := ℝ) hs0 hs1)
    (Extension.restrictCLM_comp_c1AtlasExtensionCLM (p := 2) (F := ℝ) hs0 hs1)

variable (hs0 : 0 < s) (hs1 : s < 1)

/-- The C¹ equivalence has the canonical comparison as its forward map. -/
@[simp]
theorem c1EquivGagliardo_toContinuousLinearMap :
    (c1EquivGagliardo (Ω := Ω) hs0 hs1).toContinuousLinearMap =
      toGagliardoCLM hs0 hs1 Ω :=
  rfl

/-- Its inverse is the atlas extension followed by the real whole-space comparison
and the restriction quotient. -/
@[simp]
theorem c1EquivGagliardo_symm_toContinuousLinearMap :
    (c1EquivGagliardo (Ω := Ω) hs0 hs1).symm.toContinuousLinearMap =
      (ofWholeSpace n s hs0.le Ω).comp
        ((GagliardoSpace.equivHsSpaceReal hs0 hs1).toContinuousLinearMap.comp
          (Extension.c1AtlasExtensionCLM (p := 2) (F := ℝ) hs0 hs1)) :=
  rfl

/-- The canonical comparison on the C1 domain preserves the physical `L²` class. -/
@[simp]
theorem toLp_c1EquivGagliardo (q : HsRestrictionSpace n s hs0.le Ω) :
    GagliardoSpace.toLp n s Ω (c1EquivGagliardo hs0 hs1 q) =
      toLp n s hs0.le Ω q :=
  toLp_toGagliardoCLM hs0 hs1 q

/-- Passing back to the restriction quotient preserves the intrinsic physical
`L²` class. -/
@[simp]
theorem toLp_c1EquivGagliardo_symm (u : W^{s,2}(Ω)) :
    toLp n s hs0.le Ω ((c1EquivGagliardo hs0 hs1).symm u) =
      GagliardoSpace.toLp n s Ω u :=
  GagliardoSpace.toLp_toHsRestrictionCLMOfExtension hs0 hs1
    (Extension.c1AtlasExtensionCLM (p := 2) (F := ℝ) hs0 hs1)
    (Extension.restrictCLM_comp_c1AtlasExtensionCLM (p := 2) (F := ℝ) hs0 hs1) u

/-- The C1 forward bound has the same constant as the canonical comparison on any
domain. -/
theorem norm_c1EquivGagliardo_le :
    ‖(c1EquivGagliardo (Ω := Ω) hs0 hs1).toContinuousLinearMap‖ ≤
      1 + √(gagliardoFourierConstant n s (Fact.out : 0 < n)) :=
  norm_toGagliardoCLM_le (Fact.out : 0 < n) hs0 hs1

/-- The inverse norm is bounded by the real whole-space comparison factor times
the norm of the constructed atlas extension. -/
theorem norm_c1EquivGagliardo_symm_le :
    ‖(c1EquivGagliardo (Ω := Ω) hs0 hs1).symm.toContinuousLinearMap‖ ≤
      (1 + (√(gagliardoFourierConstant n s (Fact.out : 0 < n)))⁻¹) *
        ‖Extension.c1AtlasExtensionCLM (p := 2) (F := ℝ) (Ω := Ω) hs0 hs1‖ :=
  GagliardoSpace.norm_toHsRestrictionCLMOfExtension_le (Fact.out : 0 < n) hs0 hs1
    (Extension.c1AtlasExtensionCLM (p := 2) (F := ℝ) hs0 hs1)

end HsRestrictionSpace

/-- On a domain with a C¹ extension atlas, intrinsic Gagliardo regularity of a real
function is equivalent to admitting a real whole-space Hilbert extension. -/
theorem memHsRestriction_iff_memGagliardo_c1Atlas (hs0 : 0 < s) (hs1 : s < 1)
    (f : ℝ^n → ℝ) :
    MemHsRestriction n s hs0.le Ω f ↔ MemGagliardo n s Ω f := by
  rw [memHsRestriction_iff_exists_toLp,
    GagliardoSpace.memGagliardo_iff_exists_gagliardoSpace]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨HsRestrictionSpace.c1EquivGagliardo hs0 hs1 q, ?_⟩
    simpa only [HsRestrictionSpace.toLp_c1EquivGagliardo] using hq
  · rintro ⟨u, hu⟩
    refine ⟨(HsRestrictionSpace.c1EquivGagliardo hs0 hs1).symm u, ?_⟩
    simpa only [HsRestrictionSpace.toLp_c1EquivGagliardo_symm] using hu

end SobolevSpace.Fractional
