/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.CompactCutoff
public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.RelativeExtension
public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Density.WholeSpace

/-!
# Fractional approximation near an interior compact set

An interior cutoff lets us extend a Sobolev function by zero and smooth it on the
whole space. A second, fixed cutoff confines the approximation error to the
original compact set. Bounded multiplication and restriction then make that
error small in the intrinsic fractional norm.

Only openness of the domain is needed. The argument works for Banach-valued
functions, orders strictly between zero and one, and every finite exponent
at least one.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal FractionalSobolev NNReal
open SobolevSpace.Approximation

namespace SobolevSpace.Fractional.GagliardoSpace

private theorem norm_apply_lt_of_norm_lt_div {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : E →L[ℝ] G) (v : E) {δ : ℝ} (h : ‖v‖ < δ / (‖A‖ + 1)) :
    ‖A v‖ < δ := by
  have herr := (lt_div_iff₀ (by positivity : 0 < ‖A‖ + 1)).mp h
  have hbound := A.le_opNorm v
  nlinarith [norm_nonneg v]

variable {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
private theorem localized_error_apply_ae {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω)
    (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    {φ χ : ℝ^n → ℝ} {L M : ℝ≥0}
    (hL : LipschitzWith L φ) (hM : ∀ x, ‖φ x‖ ≤ M)
    (hχ : ∀ x, φ x ≠ 0 → χ x = 1)
    (u : W^{s,p}(Ω; F)) (V w : W^{s,p}(ℝ^n; F)) (v : ℝ^n → F)
    (hV : (toLp n s univ V : ℝ^n → F) =ᵐ[volume] v)
    (hw : (toLp n s univ w : ℝ^n → F) =ᵐ[volume.restrict univ]
      Ω.indicator (fun x ↦ χ x • toLp n s Ω u x)) :
    (toLp n s Ω (restrictCLM (subset_univ Ω)
      (smulCutoffL hs0 hs1 hp hL hM (V - w))) : ℝ^n → F) =ᵐ[volume.restrict Ω]
      fun x ↦ φ x • (v x - toLp n s Ω u x) := by
  have hrestrict := toLp_restrictCLM_apply_ae (subset_univ Ω)
    (smulCutoffL hs0 hs1 hp hL hM (V - w))
  have hprod := toLp_smulCutoffL_apply_ae hs0 hs1 hp hL hM (V - w)
  have hle : (volume : Measure (ℝ^n)).restrict Ω ≤ volume.restrict univ :=
    Measure.restrict_mono (subset_univ Ω) le_rfl
  filter_upwards [hrestrict, hprod.filter_mono (ae_mono hle),
    (toLp_sub_apply_ae V w).filter_mono (ae_mono hle),
    hV.filter_mono (ae_mono Measure.restrict_le_self),
    hw.filter_mono (ae_mono hle), ae_restrict_mem hΩ] with x hr hprod hsub hvx hwx hx
  rw [hr, hprod, hsub, hvx, hwx, indicator_of_mem hx]
  by_cases hzero : φ x = 0
  · simp only [hzero, zero_smul]
  · rw [hχ x hzero, one_smul]

/-- After multiplication by a prescribed interior test function, the error of
a globally smooth approximation can be made arbitrarily small in the full
fractional norm. The approximating function itself need not vanish at the boundary. -/
theorem exists_localized_smooth_error {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω)
    (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (u : W^{s,p}(Ω; F))
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψ : tsupport ψ.toFun ⊆ Ω)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ v : ℝ^n → F, ContDiff ℝ (⊤ : ℕ∞) v ∧
      ∃ e : W^{s,p}(Ω; F),
        (toLp n s Ω e : ℝ^n → F) =ᵐ[volume.restrict Ω]
          (fun x ↦ ψ.toFun x • (v x - toLp n s Ω u x)) ∧ ‖e‖ < δ := by
  obtain ⟨χ, hχ, hχone, _, _⟩ :=
    TestFunction.exists_eq_one_on_compact hΩ ψ.hasCompactSupport' hψ
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have hw : MemGagliardo n s univ
      (Ω.indicator (fun x ↦ χ.toFun x • toLp n s Ω u x)) (p := p) := by
    simpa only [inter_univ] using
      Localization.memGagliardo_indicator_smul_of_contDiff
      hs0 hs1 hΩ MeasurableSet.univ (χ.contDiff'.of_le (by simp)) χ.hasCompactSupport'
      hχ (by simpa only [inter_univ] using memGagliardo_toLp u) hp0 hp
  let w : W^{s,p}(ℝ^n; F) := ofFunction _ hw
  obtain ⟨L, M, hL, hM⟩ := Localization.exists_cutoff_bounds_of_contDiff
    (ψ.contDiff'.of_le (by simp)) ψ.hasCompactSupport'
  let A : W^{s,p}(ℝ^n; F) →L[ℝ] W^{s,p}(Ω; F) :=
    (restrictCLM (subset_univ Ω)).comp (smulCutoffL hs0 hs1 hp hL hM)
  have hC : 0 < ‖A‖ + 1 := by positivity
  obtain ⟨V, v, hv, hVbase, hnorm⟩ :=
    exists_smooth_approximation (standardMollifier n) hp w (div_pos hδ hC)
  refine ⟨v, hv, A (V - w), ?_, ?_⟩
  · exact localized_error_apply_ae hΩ.measurableSet hs0 hs1 hp hL hM
      (fun x hx ↦ hχone x (subset_tsupport ψ.toFun hx)) u V w v hVbase
      (toLp_ofFunction_apply_ae _ hw)
  · exact @norm_apply_lt_of_norm_lt_div (W^{s,p}(ℝ^n; F)) (W^{s,p}(Ω; F))
      inferInstance inferInstance inferInstance inferInstance A (V - w) δ hnorm

end SobolevSpace.Fractional.GagliardoSpace
