/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.RelativeNorm

/-!
# Bounded relative extension after cutoff multiplication

A fixed bounded Lipschitz cutoff, separated from the added part of a domain,
defines a bounded map between the intrinsic Gagliardo spaces.
Its representative is the ordinary cutoff product followed by an indicator.
The norm bound is the product of the cutoff bound and the artificial-edge bound.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.Fractional.GagliardoSpace

variable {n : ℕ} {s δ : ℝ} {A B : Set (ℝ^n)} {φ : ℝ^n → ℝ} {L M : NNReal}

variable (hs0 : 0 < s) (hs1 : s < 1) (hδ : 0 < δ)
  (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B)
  (hL : LipschitzWith L φ) (hM : ∀ x, ‖φ x‖ ≤ M)
  (hgap : ∀ x ∈ A, φ x ≠ 0 → ∀ y ∈ B \ A, δ ≤ dist x y)

/-- Multiply by the fixed cutoff and extend its physical representative by zero. -/
def relativeCutoff (u : GagliardoSpace n s A (F := ℝ)) : GagliardoSpace n s B (F := ℝ) :=
  ofFunction (A.indicator (fun x ↦ φ x * toLp n s A u x))
    (Localization.memGagliardo_indicator_of_gap hs0 hδ hA hB hAB
      (fun x hx hprod ↦ hgap x hx (mul_ne_zero_iff.mp hprod).1)
      (Localization.memGagliardo_mul_cutoff hs0 hs1 hL hM
        ⟨Lp.memLp _, toLp_mem_domain u⟩))

theorem toLp_relativeCutoff_apply_ae (u : GagliardoSpace n s A (F := ℝ)) :
    (toLp n s B (relativeCutoff hs0 hs1 hδ hA hB hAB hL hM hgap u) : ℝ^n → ℝ)
      =ᵐ[volume.restrict B] A.indicator (fun x ↦ φ x * toLp n s A u x) :=
  toLp_ofFunction_apply_ae _ _

/-- The graph-norm cost is the cutoff cost followed by the support-gap cost. -/
theorem norm_relativeCutoff_le (u : GagliardoSpace n s A (F := ℝ)) :
    ‖relativeCutoff hs0 hs1 hδ hA hB hAB hL hM hgap u‖ ≤
      (Real.sqrt (1 + 2 * (1 + δ⁻¹) ^ ((n : ℝ) + 2 * s) *
        (Localization.edgeMass n s).toReal) *
      Real.sqrt (3 * (M : ℝ) ^ 2 + 2 * ((L : ℝ) ^ 2 + 4 * (M : ℝ) ^ 2) *
        (Localization.cutoffMass n s).toReal)) * ‖u‖ := by
  calc
    _ ≤ Real.sqrt (1 + 2 * (1 + δ⁻¹) ^ ((n : ℝ) + 2 * s) *
          (Localization.edgeMass n s).toReal) * ‖mulCutoff hs0 hs1 hL hM u‖ :=
      norm_le_of_indicator_ae hs0 hδ hA hB hAB
        (fun x hx hprod ↦ hgap x hx (mul_ne_zero_iff.mp hprod).1)
        _ _ (toLp_mulCutoff_apply_ae hs0 hs1 hL hM u)
        (toLp_relativeCutoff_apply_ae hs0 hs1 hδ hA hB hAB hL hM hgap u)
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (norm_mulCutoff_le hs0 hs1 hL hM u) (Real.sqrt_nonneg
          (1 + 2 * (1 + δ⁻¹) ^ ((n : ℝ) + 2 * s) * (Localization.edgeMass n s).toReal))

/-- Relative extension of a cutoff product respects addition of Sobolev functions. -/
theorem relativeCutoff_add (u v : GagliardoSpace n s A (F := ℝ)) :
    relativeCutoff hs0 hs1 hδ hA hB hAB hL hM hgap (u + v) =
      relativeCutoff hs0 hs1 hδ hA hB hAB hL hM hgap u +
        relativeCutoff hs0 hs1 hδ hA hB hAB hL hM hgap v := by
  classical
  apply toLp_injective
  apply Lp.ext
  have hin := Lp.coeFn_add (toLp n s A u) (toLp n s A v)
  have hi := ae_mono (μ := volume.restrict B) Measure.restrict_le_self
    ((ae_restrict_iff' hA).mp hin)
  have hout := Lp.coeFn_add
    (toLp n s B (relativeCutoff hs0 hs1 hδ hA hB hAB hL hM hgap u))
    (toLp n s B (relativeCutoff hs0 hs1 hδ hA hB hAB hL hM hgap v))
  simp only [map_add]
  filter_upwards [toLp_relativeCutoff_apply_ae hs0 hs1 hδ hA hB hAB hL hM hgap (u + v),
    toLp_relativeCutoff_apply_ae hs0 hs1 hδ hA hB hAB hL hM hgap u,
    toLp_relativeCutoff_apply_ae hs0 hs1 hδ hA hB hAB hL hM hgap v, hi, hout]
      with x hsum hu hv hi ho
  simp only [map_add] at hsum
  rw [hsum, ho]
  simp only [Pi.add_apply]
  rw [hu, hv]
  by_cases hx : x ∈ A
  · simp only [indicator_of_mem hx, hi hx, Pi.add_apply, mul_add]
  · simp only [indicator_of_notMem hx, add_zero]

/-- Relative extension of a cutoff product respects real scalar multiplication. -/
theorem relativeCutoff_smul (c : ℝ) (u : GagliardoSpace n s A (F := ℝ)) :
    relativeCutoff hs0 hs1 hδ hA hB hAB hL hM hgap (c • u) =
      c • relativeCutoff hs0 hs1 hδ hA hB hAB hL hM hgap u := by
  classical
  apply toLp_injective
  apply Lp.ext
  have hin := Lp.coeFn_smul c (toLp n s A u)
  have hi := ae_mono (μ := volume.restrict B) Measure.restrict_le_self
    ((ae_restrict_iff' hA).mp hin)
  have hout := Lp.coeFn_smul c
    (toLp n s B (relativeCutoff hs0 hs1 hδ hA hB hAB hL hM hgap u))
  simp only [map_smul]
  filter_upwards [toLp_relativeCutoff_apply_ae hs0 hs1 hδ hA hB hAB hL hM hgap (c • u),
    toLp_relativeCutoff_apply_ae hs0 hs1 hδ hA hB hAB hL hM hgap u, hi, hout]
      with x hcu hu hi ho
  simp only [map_smul] at hcu
  rw [hcu, ho]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hu]
  by_cases hx : x ∈ A
  · simp only [indicator_of_mem hx, hi hx, Pi.smul_apply, smul_eq_mul]
    exact mul_left_comm _ _ _
  · simp only [indicator_of_notMem hx, mul_zero]

/-- Bounded cutoff multiplication followed by relative zero extension. -/
def relativeCutoffCLM :
    GagliardoSpace n s A (F := ℝ) →L[ℝ] GagliardoSpace n s B (F := ℝ) :=
  LinearMap.mkContinuous
    { toFun := relativeCutoff hs0 hs1 hδ hA hB hAB hL hM hgap
      map_add' := relativeCutoff_add hs0 hs1 hδ hA hB hAB hL hM hgap
      map_smul' := relativeCutoff_smul hs0 hs1 hδ hA hB hAB hL hM hgap }
    _ (norm_relativeCutoff_le hs0 hs1 hδ hA hB hAB hL hM hgap)

/-- The bounded map has the stated physical representative throughout the larger domain. -/
theorem toLp_relativeCutoffCLM_apply_ae (u : GagliardoSpace n s A (F := ℝ)) :
    (toLp n s B (relativeCutoffCLM hs0 hs1 hδ hA hB hAB hL hM hgap u) : ℝ^n → ℝ)
      =ᵐ[volume.restrict B] A.indicator (fun x ↦ φ x * toLp n s A u x) :=
  toLp_relativeCutoff_apply_ae hs0 hs1 hδ hA hB hAB hL hM hgap u

/-- The numerical norm bound follows from the two independently proved integral estimates. -/
theorem norm_relativeCutoffCLM_le :
    ‖relativeCutoffCLM hs0 hs1 hδ hA hB hAB hL hM hgap‖ ≤
      Real.sqrt (1 + 2 * (1 + δ⁻¹) ^ ((n : ℝ) + 2 * s) *
        (Localization.edgeMass n s).toReal) *
      Real.sqrt (3 * (M : ℝ) ^ 2 + 2 * ((L : ℝ) ^ 2 + 4 * (M : ℝ) ^ 2) *
        (Localization.cutoffMass n s).toReal) :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (norm_relativeCutoff_le hs0 hs1 hδ hA hB hAB hL hM hgap)

/-- The operator agrees with cutoff and zero extension of every intrinsic function,
independently of the representative selected by the L2 quotient. -/
theorem relativeCutoffCLM_ofFunction {f : ℝ^n → ℝ} (hf : MemGagliardo n s A f) :
    relativeCutoffCLM hs0 hs1 hδ hA hB hAB hL hM hgap (ofFunction f hf) =
      ofFunction (A.indicator (fun x ↦ φ x * f x))
        (Localization.memGagliardo_indicator_of_gap hs0 hδ hA hB hAB
          (fun x hx hprod ↦ hgap x hx (mul_ne_zero_iff.mp hprod).1)
          (Localization.memGagliardo_mul_cutoff hs0 hs1 hL hM hf)) := by
  apply toLp_injective
  apply Lp.ext
  have hi : (fun x ↦ φ x * toLp n s A (ofFunction f hf) x)
      =ᵐ[volume.restrict A] fun x ↦ φ x * f x := by
    filter_upwards [toLp_ofFunction_apply_ae f hf] with x hx
    rw [hx]
  have hzero : A.indicator (fun x ↦ φ x * toLp n s A (ofFunction f hf) x)
      =ᵐ[volume.restrict B] A.indicator (fun x ↦ φ x * f x) :=
    ae_mono Measure.restrict_le_self ((ae_eq_restrict_iff_indicator_ae_eq hA).mp hi)
  exact (toLp_relativeCutoffCLM_apply_ae hs0 hs1 hδ hA hB hAB hL hM hgap
    (ofFunction f hf)).trans (hzero.trans (toLp_ofFunction_apply_ae _ _).symm)

/-- Auxiliary bounds and a choice of gap radius do not change the physical operator. -/
theorem relativeCutoffCLM_eq {δ' : ℝ} {L' M' : NNReal}
    (hδ' : 0 < δ') (hL' : LipschitzWith L' φ) (hM' : ∀ x, ‖φ x‖ ≤ M')
    (hgap' : ∀ x ∈ A, φ x ≠ 0 → ∀ y ∈ B \ A, δ' ≤ dist x y) :
    relativeCutoffCLM hs0 hs1 hδ hA hB hAB hL hM hgap =
      relativeCutoffCLM hs0 hs1 hδ' hA hB hAB hL' hM' hgap' := by
  apply ContinuousLinearMap.ext
  intro u
  apply toLp_injective
  apply Lp.ext
  exact (toLp_relativeCutoffCLM_apply_ae hs0 hs1 hδ hA hB hAB hL hM hgap u).trans
    (toLp_relativeCutoffCLM_apply_ae hs0 hs1 hδ' hA hB hAB hL' hM' hgap' u).symm

end SobolevSpace.Fractional.GagliardoSpace
