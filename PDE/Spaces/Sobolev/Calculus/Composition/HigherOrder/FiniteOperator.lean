/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.HigherOrder.FiniteWholeSpace

/-!
# Composition operators for finite Sobolev families

The quantitative composition theorem determines a unique Sobolev graph. Reindexing
allows any finite family, including families indexed by a product of finite types.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev

namespace SobolevSpace.Composition

open GraphSpace

variable {n k : ℕ} [NeZero n] {ι : Type*} [Fintype ι]

/-- Reindexing the quantitative estimate gives a bound for any finite index type. -/
theorem exists_composition_bound (hk : (n : ℝ) < 2 * (k : ℝ))
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) :
    ∃ Φ : (ι → ℝ) → ℝ, Continuous Φ ∧ Monotone Φ ∧
      ∀ U : ι → W^{k,2}(ℝ^n), ∃ W : W^{k,2}(ℝ^n),
        baseRepresentative W =ᵐ[volume] (fun x ↦ f (fun i ↦ baseRepresentative (U i) x)) ∧
        ‖W‖ ≤ Φ (fun i ↦ ‖U i‖) := by
  classical
  let e := Fintype.equivFin ι
  let g : (Fin (Fintype.card ι) → ℝ) → ℝ := fun y ↦ f (fun i ↦ y (e i))
  have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
    hf.comp (contDiff_pi.mpr fun i ↦ contDiff_apply ℝ (fun _ ↦ ℝ) (e i))
  obtain ⟨Φ, hΦ, hmono, hbound⟩ := exists_finite_composition_bound hk hg hf0
  refine ⟨fun t ↦ Φ (fun j ↦ t (e.symm j)),
    hΦ.comp (continuous_pi fun j ↦ continuous_apply (e.symm j)),
    fun t s hts ↦ hmono (fun j ↦ hts (e.symm j)), ?_⟩
  intro U
  obtain ⟨W, hW, hnorm⟩ := hbound (fun j ↦ U (e.symm j))
  refine ⟨W, ?_, hnorm⟩
  simpa only [g, Equiv.symm_apply_apply] using hW

/-- The graph of a smooth zero-preserving reaction applied to a finite Sobolev family. -/
def finiteComposition (hk : (n : ℝ) < 2 * (k : ℝ))
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (U : ι → W^{k,2}(ℝ^n)) : W^{k,2}(ℝ^n) :=
  ((exists_composition_bound hk hf hf0).choose_spec.2.2 U).choose

/-- The selected graph represents the actual pointwise composition almost everywhere. -/
theorem finiteComposition_ae (hk : (n : ℝ) < 2 * (k : ℝ))
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (U : ι → W^{k,2}(ℝ^n)) :
    baseRepresentative (finiteComposition hk hf hf0 U) =ᵐ[volume]
      (fun x ↦ f (fun i ↦ baseRepresentative (U i) x)) :=
  ((exists_composition_bound hk hf hf0).choose_spec.2.2 U).choose_spec.1

/-- A base-coordinate identity identifies a finite composition graph uniquely. -/
theorem eq_finiteComposition_of_ae (hk : (n : ℝ) < 2 * (k : ℝ))
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (U : ι → W^{k,2}(ℝ^n)) {W : W^{k,2}(ℝ^n)}
    (hW : baseRepresentative W =ᵐ[volume]
      (fun x ↦ f (fun i ↦ baseRepresentative (U i) x))) :
    W = finiteComposition hk hf hf0 U := by
  apply WkpSpaceOn.ext_of_base_ae isOpen_univ
  simpa only [baseRepresentative, domainMeasure, Measure.restrict_univ] using
    hW.trans (finiteComposition_ae hk hf hf0 U).symm

/-- Finite composition is bounded on each ball in the product Sobolev norm. -/
theorem exists_norm_finiteComposition_bound (hk : (n : ℝ) < 2 * (k : ℝ))
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : ι → W^{k,2}(ℝ^n), ‖U‖ ≤ R →
      ‖finiteComposition hk hf hf0 U‖ ≤ C := by
  classical
  obtain ⟨Φ, _, hmono, hbound⟩ := exists_composition_bound hk hf hf0
  refine ⟨max (Φ (fun _ ↦ R)) 0, le_max_right _ _, ?_⟩
  intro U hU
  obtain ⟨W, hW, hnorm⟩ := hbound U
  rw [eq_finiteComposition_of_ae hk hf hf0 U hW] at hnorm
  exact hnorm.trans ((hmono (fun i ↦ (norm_le_pi_norm U i).trans hU)).trans
    (le_max_left _ _))

end SobolevSpace.Composition
