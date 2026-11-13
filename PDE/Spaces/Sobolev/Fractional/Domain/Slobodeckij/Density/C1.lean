/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.AtlasGluing
public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Density.Extension

/-!
# Smooth approximation on domains with a C1 extension atlas

The atlas gives a bounded extension to the whole space. Smoothing that extension
and restricting back gives approximation by functions smooth across the boundary.
This avoids asking a C1 coordinate change to preserve higher derivatives.

The approximants have compact support in the ambient space, with no vanishing
condition at the domain boundary. The geometric assumptions are those of
`C1ExtensionAtlas`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FractionalSobolev Topology

namespace SobolevSpace.Fractional.GagliardoSpace

variable {n : ℕ} [Fact (0 < n)] {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {Ω : Set (ℝ^n)} [Boundary.C1ExtensionAtlas n Ω]

/-- On an atlas domain, every fractional Sobolev element admits approximants
that are smooth across the boundary and compactly supported in the ambient space. -/
theorem exists_global_smooth_approximation_c1Atlas
    (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (u : W^{s,p}(Ω; F)) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : W^{s,p}(Ω; F), ∃ f : ℝ^n → F,
      ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      (toLp n s Ω v : ℝ^n → F) =ᵐ[volume.restrict Ω] f ∧ ‖v - u‖ < ε := by
  obtain ⟨U, hU⟩ :=
    Extension.surjective_restrictCLM_c1Atlas (Ω := Ω) hs0 hs1 p F hp u
  exact exists_global_smooth_approximation_of_extension hs0 hs1 hp u U hU hε

/-- Restrictions of globally smooth, compactly supported functions are dense
in the intrinsic fractional Sobolev space of an atlas domain. -/
theorem dense_global_smooth_c1Atlas (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞) :
    Dense {u : W^{s,p}(Ω; F) |
      ∃ f : ℝ^n → F, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
        (toLp n s Ω u : ℝ^n → F) =ᵐ[volume.restrict Ω] f} :=
  dense_global_smooth_of_surjective_restrict hs0 hs1 hp
    (Extension.surjective_restrictCLM_c1Atlas hs0 hs1 p F hp)

end SobolevSpace.Fractional.GagliardoSpace
