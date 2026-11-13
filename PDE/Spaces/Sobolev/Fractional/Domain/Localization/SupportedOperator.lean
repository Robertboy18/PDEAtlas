/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.RelativeNorm

/-!
# Relative zero extension of a localized bounded map

A bounded map into the intrinsic space on `A` can be
extended to `B` when its physical representatives have a uniform support gap.
The representatives need not form a pointwise linear family: their almost
everywhere agreement with the input map supplies linearity after zero extension.

The norm bound follows from the artificial-edge estimate. No continuity
or intrinsic membership of the extended functions is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace SobolevSpace.Fractional.GagliardoSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {n : ℕ} {s δ : ℝ} {A B : Set (ℝ^n)}

variable (hs : 0 < s) (hδ : 0 < δ)
  (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B)
  (T : X →L[ℝ] GagliardoSpace n s A) (f : X → ℝ^n → ℝ)
  (hTf : ∀ u, (toLp n s A (T u) : ℝ^n → ℝ) =ᵐ[volume.restrict A] f u)
  (hgap : ∀ u, ∀ x ∈ A, f u x ≠ 0 → ∀ y ∈ B \ A, δ ≤ dist x y)

/-- Extend the physical representatives of a localized bounded map by zero. -/
def relativeZeroExtension (u : X) : GagliardoSpace n s B :=
  ofFunction (A.indicator (f u))
    (Localization.memGagliardo_indicator_of_gap hs hδ hA hB hAB (hgap u)
      ⟨(memLp_congr_ae (hTf u)).mp (Lp.memLp (toLp n s A (T u))),
        (memLp_congr_ae (diffQuot_congr_ae (s := s) (hTf u))).mp
          (toLp_mem_domain (T u))⟩)

/-- Relative extension retains the specified physical representative. -/
theorem toLp_relativeZeroExtension_apply_ae (u : X) :
    (toLp n s B (relativeZeroExtension hs hδ hA hB hAB T f hTf hgap u) : ℝ^n → ℝ)
      =ᵐ[volume.restrict B] A.indicator (f u) :=
  toLp_ofFunction_apply_ae _ _

/-- The support gap costs only the explicit radial-tail factor. -/
theorem norm_relativeZeroExtension_le (u : X) :
    ‖relativeZeroExtension hs hδ hA hB hAB T f hTf hgap u‖ ≤
      Real.sqrt (1 + 2 * (1 + δ⁻¹) ^ ((n : ℝ) + 2 * s) *
        (Localization.edgeMass n s).toReal) * ‖T u‖ :=
  norm_le_of_indicator_ae hs hδ hA hB hAB (hgap u) (T u)
    (relativeZeroExtension hs hδ hA hB hAB T f hTf hgap u) (hTf u)
    (toLp_relativeZeroExtension_apply_ae hs hδ hA hB hAB T f hTf hgap u)

/-- Postcompose a localized bounded map with relative zero extension.
The support gap and the original map determine a finite operator bound. -/
def relativeZeroExtensionCLM : X →L[ℝ] GagliardoSpace n s B :=
  LinearMap.mkContinuous
    { toFun := relativeZeroExtension hs hδ hA hB hAB T f hTf hgap
      map_add' := fun u v ↦ by
        classical
        apply toLp_injective
        apply Lp.ext
        have hin : f (u + v) =ᵐ[volume.restrict A] fun x ↦ f u x + f v x := by
          have hadd := Lp.coeFn_add (toLp n s A (T u)) (toLp n s A (T v))
          filter_upwards [hTf (u + v), hTf u, hTf v, hadd] with x hsum hu hv ha
          simp only [map_add] at hsum
          exact hsum.symm.trans (ha.trans (congrArg₂ (· + ·) hu hv))
        have hi := ae_mono (μ := volume.restrict B) Measure.restrict_le_self
          ((ae_restrict_iff' hA).mp hin)
        have hout := Lp.coeFn_add
          (toLp n s B (relativeZeroExtension hs hδ hA hB hAB T f hTf hgap u))
          (toLp n s B (relativeZeroExtension hs hδ hA hB hAB T f hTf hgap v))
        simp only [map_add]
        filter_upwards [
          toLp_relativeZeroExtension_apply_ae hs hδ hA hB hAB T f hTf hgap (u + v),
          toLp_relativeZeroExtension_apply_ae hs hδ hA hB hAB T f hTf hgap u,
          toLp_relativeZeroExtension_apply_ae hs hδ hA hB hAB T f hTf hgap v, hi, hout]
            with x hsum hu hv hi ho
        rw [hsum, ho]
        simp only [Pi.add_apply]
        rw [hu, hv]
        by_cases hx : x ∈ A
        · simp only [indicator_of_mem hx, hi hx]
        · simp only [indicator_of_notMem hx, add_zero]
      map_smul' := fun c u ↦ by
        classical
        apply toLp_injective
        apply Lp.ext
        have hin : f (c • u) =ᵐ[volume.restrict A] fun x ↦ c * f u x := by
          have hsmul := Lp.coeFn_smul c (toLp n s A (T u))
          filter_upwards [hTf (c • u), hTf u, hsmul] with x hcu hu hc
          simp only [map_smul] at hcu
          simpa only [Pi.smul_apply, smul_eq_mul] using
            hcu.symm.trans (hc.trans (congrArg (c • ·) hu))
        have hi := ae_mono (μ := volume.restrict B) Measure.restrict_le_self
          ((ae_restrict_iff' hA).mp hin)
        have hout := Lp.coeFn_smul c
          (toLp n s B (relativeZeroExtension hs hδ hA hB hAB T f hTf hgap u))
        simp only [map_smul, RingHom.id_apply]
        filter_upwards [
          toLp_relativeZeroExtension_apply_ae hs hδ hA hB hAB T f hTf hgap (c • u),
          toLp_relativeZeroExtension_apply_ae hs hδ hA hB hAB T f hTf hgap u, hi, hout]
            with x hcu hu hi ho
        rw [hcu, ho]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hu]
        by_cases hx : x ∈ A
        · simp only [indicator_of_mem hx, hi hx]
        · simp only [indicator_of_notMem hx, mul_zero] }
    (Real.sqrt (1 + 2 * (1 + δ⁻¹) ^ ((n : ℝ) + 2 * s) *
      (Localization.edgeMass n s).toReal) * ‖T‖)
    (fun u ↦ (norm_relativeZeroExtension_le hs hδ hA hB hAB T f hTf hgap u).trans
      (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (T.le_opNorm u) (Real.sqrt_nonneg _)))

/-- The resulting bounded map is the relative zero extension. -/
theorem toLp_relativeZeroExtensionCLM_apply_ae (u : X) :
    (toLp n s B (relativeZeroExtensionCLM hs hδ hA hB hAB T f hTf hgap u) : ℝ^n → ℝ)
      =ᵐ[volume.restrict B] A.indicator (f u) :=
  toLp_relativeZeroExtension_apply_ae hs hδ hA hB hAB T f hTf hgap u

/-- The operator norm uses the original map norm and the edge factor. -/
theorem norm_relativeZeroExtensionCLM_le :
    ‖relativeZeroExtensionCLM hs hδ hA hB hAB T f hTf hgap‖ ≤
      Real.sqrt (1 + 2 * (1 + δ⁻¹) ^ ((n : ℝ) + 2 * s) *
        (Localization.edgeMass n s).toReal) * ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦
    (norm_relativeZeroExtension_le hs hδ hA hB hAB T f hTf hgap u).trans
      (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (T.le_opNorm u) (Real.sqrt_nonneg _))

/-- A different physical representative and gap witness give the same map. -/
theorem relativeZeroExtensionCLM_eq
    {δ' : ℝ} (hδ' : 0 < δ') (g : X → ℝ^n → ℝ)
    (hTg : ∀ u, (toLp n s A (T u) : ℝ^n → ℝ) =ᵐ[volume.restrict A] g u)
    (hgap' : ∀ u, ∀ x ∈ A, g u x ≠ 0 → ∀ y ∈ B \ A, δ' ≤ dist x y) :
    relativeZeroExtensionCLM hs hδ hA hB hAB T f hTf hgap =
      relativeZeroExtensionCLM hs hδ' hA hB hAB T g hTg hgap' := by
  apply ContinuousLinearMap.ext
  intro u
  apply toLp_injective
  apply Lp.ext
  have hfg : f u =ᵐ[volume.restrict A] g u := (hTf u).symm.trans (hTg u)
  have hind : A.indicator (f u) =ᵐ[volume.restrict B] A.indicator (g u) :=
    ae_mono Measure.restrict_le_self ((ae_eq_restrict_iff_indicator_ae_eq hA).mp hfg)
  exact (toLp_relativeZeroExtensionCLM_apply_ae hs hδ hA hB hAB T f hTf hgap u).trans
    (hind.trans
      (toLp_relativeZeroExtensionCLM_apply_ae hs hδ' hA hB hAB T g hTg hgap' u).symm)

end SobolevSpace.Fractional.GagliardoSpace
