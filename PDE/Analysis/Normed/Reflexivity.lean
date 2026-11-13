/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Reflexivity under equivalence, finite products, and closed subspaces

Reflexivity is expressed as surjectivity of Mathlib's canonical map into the continuous
double dual. Finite products are treated by coordinate projections and injections.
For a closed subspace, a bidual functional is first represented in the ambient space;
Hahn–Banach separation forces that representative into the subspace, and Hahn–Banach
extension identifies its values on the entire subspace dual.
-/

@[expose] public section

open Set
open scoped BigOperators ENNReal

namespace NormedSpace

section GeneralScalar

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Surjectivity of the canonical bidual inclusion is preserved by a continuous linear
equivalence of seminormed spaces. -/
theorem surjective_inclusionInDoubleDual_of_equiv (e : E ≃L[𝕜] F)
    (hE : Function.Surjective (inclusionInDoubleDual 𝕜 E)) :
    Function.Surjective (inclusionInDoubleDual 𝕜 F) := by
  let R : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 F :=
    (ContinuousLinearMap.compL 𝕜 F E 𝕜).flip e.symm.toContinuousLinearMap
  intro H
  obtain ⟨x, hx⟩ := hE (H.comp R)
  refine ⟨e x, ?_⟩
  ext φ
  have hR : R (φ.comp e.toContinuousLinearMap) = φ := by
    ext y
    simp [R]
  have hh := congrArg
    (fun T : StrongDual 𝕜 (StrongDual 𝕜 E) ↦ T (φ.comp e.toContinuousLinearMap)) hx
  change φ (e x) = H (R (φ.comp e.toContinuousLinearMap)) at hh
  rw [hR] at hh
  exact hh

/-- A finite product of seminormed spaces with surjective bidual inclusions also has a
surjective bidual inclusion. -/
theorem surjective_inclusionInDoubleDual_pi {ι : Type*} [Fintype ι]
    (G : ι → Type*) [∀ i, SeminormedAddCommGroup (G i)] [∀ i, NormedSpace 𝕜 (G i)]
    (hG : ∀ i, Function.Surjective (inclusionInDoubleDual 𝕜 (G i))) :
    Function.Surjective (inclusionInDoubleDual 𝕜 (∀ i, G i)) := by
  classical
  let P (i : ι) : (∀ j, G j) →L[𝕜] G i := ContinuousLinearMap.proj i
  let J (i : ι) : G i →L[𝕜] (∀ j, G j) := ContinuousLinearMap.single 𝕜 G i
  let R (i : ι) : StrongDual 𝕜 (G i) →L[𝕜] StrongDual 𝕜 (∀ j, G j) :=
    (ContinuousLinearMap.compL 𝕜 (∀ j, G j) (G i) 𝕜).flip (P i)
  intro H
  choose x hx using fun i ↦ hG i (H.comp (R i))
  refine ⟨x, ?_⟩
  ext φ
  have hsum : (∑ i, (φ.comp (J i)).comp (P i)) = φ := by
    ext y
    simpa only [sum_apply, ContinuousLinearMap.comp_apply, P, J,
      ContinuousLinearMap.proj_apply] using ContinuousLinearMap.sum_comp_single 𝕜 G φ y
  have hcoord (i : ι) : H ((φ.comp (J i)).comp (P i)) = φ.comp (J i) (x i) := by
    have hh := congrArg
      (fun T : StrongDual 𝕜 (StrongDual 𝕜 (G i)) ↦ T (φ.comp (J i))) (hx i)
    exact hh.symm
  change φ x = H φ
  calc
    φ x = ∑ i, φ.comp (J i) (x i) :=
      (ContinuousLinearMap.sum_comp_single 𝕜 G φ x).symm
    _ = ∑ i, H ((φ.comp (J i)).comp (P i)) :=
      Finset.sum_congr rfl fun i _ ↦ (hcoord i).symm
    _ = H (∑ i, (φ.comp (J i)).comp (P i)) := (map_sum H _ _).symm
    _ = H φ := congrArg H hsum

/-- A finite `PiLp` product is reflexive whenever its coordinate spaces are reflexive.
The proof transports the finite-product result through Mathlib's continuous linear
equivalence, so it applies to the `PiLp` norm. -/
theorem surjective_inclusionInDoubleDual_piLp {ι : Type*} [Fintype ι]
    (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (G : ι → Type*) [∀ i, SeminormedAddCommGroup (G i)] [∀ i, NormedSpace 𝕜 (G i)]
    (hG : ∀ i, Function.Surjective (inclusionInDoubleDual 𝕜 (G i))) :
    Function.Surjective (inclusionInDoubleDual 𝕜 (PiLp r G)) :=
  surjective_inclusionInDoubleDual_of_equiv (PiLp.continuousLinearEquiv r 𝕜 G).symm
    (surjective_inclusionInDoubleDual_pi G hG)

end GeneralScalar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every closed subspace of a reflexive real normed space is reflexive. Separation proves
that the ambient representative lies in the subspace; extension handles all of its dual. -/
theorem surjective_inclusionInDoubleDual_submodule (S : Submodule ℝ E)
    (hS : IsClosed (S : Set E))
    (hE : Function.Surjective (inclusionInDoubleDual ℝ E)) :
    Function.Surjective (inclusionInDoubleDual ℝ S) := by
  let R : StrongDual ℝ E →L[ℝ] StrongDual ℝ S :=
    (ContinuousLinearMap.compL ℝ S E ℝ).flip S.subtypeL
  intro H
  obtain ⟨x, hx⟩ := hE (H.comp R)
  have hxS : x ∈ S := by
    by_contra hnot
    obtain ⟨φ, c, hφS, hφx⟩ := geometric_hahn_banach_closed_point S.convex hS hnot
    have hzero (y : S) : φ (y : E) = 0 := by
      by_contra hy
      have hlt := hφS (((c + 1) / φ (y : E)) • (y : E))
        (S.smul_mem _ y.property)
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hy] at hlt
      exact (lt_add_one c).asymm hlt
    have hR : R φ = 0 := by
      ext y
      exact hzero y
    have hxzero := congrArg (fun T : StrongDual ℝ (StrongDual ℝ E) ↦ T φ) hx
    change φ x = H (R φ) at hxzero
    rw [hR, map_zero] at hxzero
    have hc := hφS 0 S.zero_mem
    rw [map_zero] at hc
    rw [hxzero] at hφx
    exact (hc.trans hφx).false
  refine ⟨⟨x, hxS⟩, ?_⟩
  ext ψ
  obtain ⟨φ, hφ, _⟩ := exists_extension_norm_eq S ψ
  have hR : R φ = ψ := by
    ext y
    exact hφ y
  have hh := congrArg (fun T : StrongDual ℝ (StrongDual ℝ E) ↦ T φ) hx
  change φ x = H (R φ) at hh
  rw [hR] at hh
  change ψ ⟨x, hxS⟩ = H ψ
  exact (hφ ⟨x, hxS⟩).symm.trans hh

end NormedSpace
