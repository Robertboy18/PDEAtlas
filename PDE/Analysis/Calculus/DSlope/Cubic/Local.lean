/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.DSlope.Cubic

import PDE.Analysis.Calculus.Jet.Localization

/-!
# Joint local cubic factorization near a compact parameter set

The production divided-slope owner supplies the cubic identity and joint
smoothness for globally smooth maps. Compact localization gives a global
representative of a map smooth only on an open domain. The tube lemma then
retains one product neighborhood of the entire prescribed compact zero section.

Zero ordinary scalar jets transfer to the representative on that neighborhood.
They are not required away from it. The resulting factor is jointly smooth,
including at zero and for both signs of the scalar parameter.
-/

@[expose] public noncomputable section

open Filter Function Set
open scoped ContDiff Topology

namespace PDE.Analysis

universe u v

variable {P : Type u} {E : Type (max u v)}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A jointly smooth map on an open domain, with zero scalar jets through order
two along its zero section, has a jointly smooth cubic factor on one product
neighborhood of any prescribed compact subset of that section.

The factor has a global smooth extension; the factorization is asserted only
on the returned product neighborhood. No regularity of the original map outside
`Ω`, and no zero-jet condition outside its zero section, is required. -/
theorem exists_local_contDiff_cubic_factor_joint
    {F : P × ℝ → E} {Ω : Set (P × ℝ)} {K : Set P}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ×ˢ {(0 : ℝ)} ⊆ Ω)
    (hF : ContDiffOn ℝ ∞ F Ω)
    (hzero : ∀ p, (p, (0 : ℝ)) ∈ Ω → F (p, 0) = 0)
    (hfirst : ∀ p, (p, (0 : ℝ)) ∈ Ω → deriv (fun μ ↦ F (p, μ)) 0 = 0)
    (hsecond : ∀ p, (p, (0 : ℝ)) ∈ Ω →
      deriv (deriv (fun μ ↦ F (p, μ))) 0 = 0) :
    ∃ (V : Set P) (J : Set ℝ) (A : P × ℝ → E),
      IsOpen V ∧ K ⊆ V ∧ IsOpen J ∧ (0 : ℝ) ∈ J ∧ V ×ˢ J ⊆ Ω ∧
      ContDiff ℝ ∞ A ∧ ∀ p ∈ V, ∀ μ ∈ J, F (p, μ) = μ ^ 3 • A (p, μ) := by
  classical
  obtain ⟨χ, O, _, _, _, _, hO, hKO, hOΩ, _, hrep⟩ :=
    exists_smooth_cutoff_localization hF hΩ (hK.prod isCompact_singleton) hKΩ
  let F₁ : P × ℝ → E := Ω.indicator (fun q ↦ χ q • F q)
  have hF₁ : ContDiff ℝ ∞ F₁ := hrep.1
  have heq : EqOn F₁ F O := hrep.2.2.2
  obtain ⟨V, J, hV, hJ, hKV, hzeroJ, hVJ⟩ :=
    generalized_tube_lemma hK isCompact_singleton hO hKO
  have h0J : (0 : ℝ) ∈ J := hzeroJ (by simp)
  let A : P × ℝ → E := fun q ↦
    (Function.swap dslope 0)^[3] (fun μ ↦ F₁ (q.1, μ)) q.2
  have hA : ContDiff ℝ ∞ A := contDiff_iterate_dslope_snd hF₁ 0 3
  refine ⟨V, J, A, hV, hKV, hJ, h0J, hVJ.trans hOΩ, hA, ?_⟩
  intro p hp μ hμ
  have hnear : (fun ν ↦ F₁ (p, ν)) =ᶠ[𝓝 (0 : ℝ)] (fun ν ↦ F (p, ν)) := by
    filter_upwards [hJ.mem_nhds h0J] with ν hν
    exact heq (hVJ ⟨hp, hν⟩)
  have hpΩ : (p, (0 : ℝ)) ∈ Ω := hOΩ (hVJ ⟨hp, h0J⟩)
  have hz : F₁ (p, 0) = 0 := hnear.self_of_nhds.trans (hzero p hpΩ)
  have h₁ : deriv (fun ν ↦ F₁ (p, ν)) 0 = 0 :=
    hnear.deriv_eq.trans (hfirst p hpΩ)
  have h₂ : deriv (deriv (fun ν ↦ F₁ (p, ν))) 0 = 0 :=
    hnear.deriv.deriv_eq.trans (hsecond p hpΩ)
  have hslice : ContDiff ℝ 2 (fun ν ↦ F₁ (p, ν)) :=
    (hF₁.of_le (by simp)).comp (contDiff_const.prodMk contDiff_id)
  calc
    F (p, μ) = F₁ (p, μ) := (heq (hVJ ⟨hp, hμ⟩)).symm
    _ = μ ^ 3 • A (p, μ) :=
      eq_cube_smul_iterate_dslope_of_zero hslice hz h₁ h₂ μ

end PDE.Analysis
