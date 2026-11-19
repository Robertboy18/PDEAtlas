/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.BoundaryOperator

/-!
# Intrinsic fractional extension by the finite C1 atlas

The interior zero extension and the boundary-piece operators are added as
continuous linear maps. Their physical restrictions sum to the original
function by the atlas partition of unity. Both act on the
intrinsic Gagliardo space of each domain.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal FractionalSobolev

namespace SobolevSpace.Fractional.Extension

open SobolevSpace.Boundary GagliardoSpace

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The physical representative of a finite sum of extension operators. -/
private theorem toLp_add_sum_apply_ae {ι : Type*} [Fintype ι]
    {A B : Set (ℝ^n)} (hAB : A ⊆ B)
    (T₀ : W^{s,p}(A; F) →L[ℝ] W^{s,p}(B; F))
    (Tᵢ : ι → W^{s,p}(A; F) →L[ℝ] W^{s,p}(B; F))
    (u : W^{s,p}(A; F)) :
    (toLp n s B ((T₀ + ∑ i, Tᵢ i) u) : ℝ^n → F) =ᵐ[volume.restrict A]
      fun x ↦ toLp n s B (T₀ u) x + ∑ i, toLp n s B (Tᵢ i u) x := by
  classical
  have hadd : (toLp n s B ((T₀ + ∑ i, Tᵢ i) u) : ℝ^n → F)
      =ᵐ[volume.restrict A]
        fun x ↦ toLp n s B (T₀ u) x + toLp n s B (∑ i, Tᵢ i u) x := by
    have h := Lp.coeFn_add (toLp n s B (T₀ u)) (toLp n s B (∑ i, Tᵢ i u))
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hAB h] with x hx
    simpa only [add_apply, sum_apply, map_add, Pi.add_apply] using hx
  have hsum : (toLp n s B (∑ i, Tᵢ i u) : ℝ^n → F)
      =ᵐ[volume.restrict A] fun x ↦ ∑ i, toLp n s B (Tᵢ i u) x := by
    have h := Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦ toLp n s B (Tᵢ i u))
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hAB h] with x hx
    simpa only [map_sum] using hx
  filter_upwards [hadd, hsum] with x ha hs
  exact ha.trans (congrArg (toLp n s B (T₀ u) x + ·) hs)

variable [Fact (0 < n)] [hΩ : C1ExtensionAtlas n Ω]

/-- Summing the local extensions gives a bounded intrinsic extension
whose physical restriction is the original element. -/
theorem exists_c1AtlasExtensionCLM (hs0 : 0 < s) (hs1 : s < 1)
    (p : ℝ≥0∞ := 2) (F : Type* := by exact ℝ)
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fact (1 ≤ p)]
    (hp : p ≠ ∞ := by norm_num) :
    ∃ T : W^{s,p}(Ω; F) →L[ℝ] W^{s,p}(ℝ^n; F),
      ∀ u, (toLp n s Set.univ (T u) : ℝ^n → F)
        =ᵐ[volume.restrict Ω] (toLp n s Ω u : ℝ^n → F) := by
  classical
  obtain ⟨T₀, hT₀⟩ := Localization.exists_interiorCutoffCLM (Ω := Ω) hs0 hs1 p F hp
  choose Tᵢ hTᵢ using fun i ↦ Localization.exists_boundaryPieceCLM (Ω := Ω) hs0 hs1 i p F hp
  let T := T₀ + ∑ i, Tᵢ i
  refine ⟨T, fun u ↦ ?_⟩
  have h₀vol : (toLp n s Set.univ (T₀ u) : ℝ^n → F) =ᵐ[volume]
      Ω.indicator (fun x ↦ hΩ.interiorCutoff.toFun x • toLp n s Ω u x) := by
    simpa only [Measure.restrict_univ] using hT₀ u
  have hsum := toLp_add_sum_apply_ae (subset_univ Ω) T₀ Tᵢ u
  have hi : ∀ᵐ x ∂volume.restrict Ω, ∀ i : Fin hΩ.N,
      toLp n s Set.univ (Tᵢ i u) x = (hΩ.boundaryCutoff i).toFun x • toLp n s Ω u x :=
    ae_all_iff.mpr (fun i ↦ hTᵢ i u)
  filter_upwards [hsum, ae_restrict_of_ae h₀vol, hi,
    ae_restrict_mem hΩ.isOpen.measurableSet] with x hsumx h₀ hx hxΩ
  rw [hsumx, h₀, indicator_of_mem hxΩ]
  simp_rw [hx]
  rw [← Finset.sum_smul, ← add_smul, hΩ.cutoff_sum_eq_one x hxΩ, one_smul]

/-- Intrinsic fractional extension obtained by finite atlas gluing. -/
def c1AtlasExtensionCLM (hs0 : 0 < s) (hs1 : s < 1)
    (p : ℝ≥0∞ := 2) (F : Type* := by exact ℝ)
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fact (1 ≤ p)]
    (hp : p ≠ ∞ := by norm_num) :
    W^{s,p}(Ω; F) →L[ℝ] W^{s,p}(ℝ^n; F) :=
  (exists_c1AtlasExtensionCLM hs0 hs1 p F hp).choose

/-- The constructed map preserves the physical representative on the domain. -/
theorem toLp_c1AtlasExtensionCLM_apply_ae (hs0 : 0 < s) (hs1 : s < 1)
    (u : W^{s,p}(Ω; F)) (hp : p ≠ ∞ := by norm_num) :
    (toLp n s Set.univ (c1AtlasExtensionCLM hs0 hs1 p F hp u) : ℝ^n → F)
      =ᵐ[volume.restrict Ω] (toLp n s Ω u : ℝ^n → F) :=
  (exists_c1AtlasExtensionCLM hs0 hs1 p F hp).choose_spec u

/-- Intrinsic restriction has the bounded atlas extension as a right inverse. -/
theorem restrictCLM_comp_c1AtlasExtensionCLM (hs0 : 0 < s) (hs1 : s < 1)
    (p : ℝ≥0∞ := 2) (F : Type* := by exact ℝ)
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fact (1 ≤ p)]
    (hp : p ≠ ∞ := by norm_num) :
    (restrictCLM (subset_univ Ω)).comp (c1AtlasExtensionCLM hs0 hs1 p F hp) =
      ContinuousLinearMap.id ℝ (W^{s,p}(Ω; F)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply toLp_injective
  apply Lp.ext
  exact (toLp_restrictCLM_apply_ae (subset_univ Ω) (c1AtlasExtensionCLM hs0 hs1 p F hp u)).trans
    (toLp_c1AtlasExtensionCLM_apply_ae hs0 hs1 u hp)

/-- Every intrinsic element on the atlas domain is a whole-space restriction. -/
theorem surjective_restrictCLM_c1Atlas (hs0 : 0 < s) (hs1 : s < 1)
    (p : ℝ≥0∞ := 2) (F : Type* := by exact ℝ)
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fact (1 ≤ p)]
    (hp : p ≠ ∞ := by norm_num) :
    Function.Surjective (restrictCLM (n := n) (s := s) (p := p) (F := F)
      (subset_univ Ω)) := by
  intro u
  refine ⟨c1AtlasExtensionCLM hs0 hs1 p F hp u, ?_⟩
  exact congrArg
    (fun T : W^{s,p}(Ω; F) →L[ℝ] W^{s,p}(Ω; F) ↦ T u)
    (restrictCLM_comp_c1AtlasExtensionCLM hs0 hs1 p F hp)

end SobolevSpace.Fractional.Extension
