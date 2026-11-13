/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.HigherRegularity
public import PDE.Spaces.Holder.Evolution.SpaceTime
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.General

/-!
# Joint classical representatives from finite Sobolev time regularity

The spatial budget `k + floor(n/2) + 1` embeds in `C^{k,1/2}`. A finite family
of integrable Sobolev curves linked by weak time derivatives first acquires
continuous representatives in that common Sobolev space. The bounded spatial
embedding preserves their classical time derivatives, including both endpoints.

The resulting scalar field has classical joint derivatives and is `Cᵏ` up to
the closed cylinder boundary. The input is neither a chosen spatial approximation
nor a classical representative.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Common
open scoped ENNReal Sobolev

namespace HolderSpace.CKGammaOn

variable {n k : ℕ} {Ω : Set (ℝ^n)} {γ : Exponent} {a b : ℝ}

/-- The mixed fields satisfy the classical closure regularity predicate. -/
theorem contDiffUpToBoundary_spaceTimeField
    {R : Fin (k + 1) → ℝ → CKGammaOn n k Ω γ} (hΩ : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hcontinuous : ∀ j, ContinuousOn (R j) (Icc a b))
    (hderiv : ∀ j : Fin k, ∀ t ∈ Icc a b,
      HasDerivWithinAt (R j.castSucc) (R j.succ t) (Icc a b) t)
    (m : ℕ) (j : Fin (k + 1)) (α : MultiIndex n k)
    (hm : j.val + α.order + m ≤ k) :
    SobolevSpace.ContDiffUpToBoundary m (spaceTimeField R j α)
      (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)) :=
  ⟨contDiffOn_spaceTimeField hΩ hcontinuous hderiv m j α hm,
    fun w hw ↦ uniformContinuousOn_iteratedPartialDeriv_spaceTimeField
      hΩ hbounded hcontinuous hderiv w j α (by omega)⟩

end HolderSpace.CKGammaOn

namespace SobolevSpace.Evolution

open GraphSpace HolderSpace PDE.Analysis.Evolution

variable {n k : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Raw C¹ geometry supplies a bounded spatial representative map at the exact
Hilbert-to-Hölder derivative budget. -/
theorem exists_hilbertHolder_embedding {γ : Exponent} (hγ : (γ : ℝ) = 1 / 2)
    (hn : 0 < n) (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) :
    ∃ E : W^{k + n / 2 + 1,2}(Ω) →L[ℝ] CKGammaOn n k Ω γ,
      ∀ U, (E U).interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U := by
  have := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  have hrep := Inequalities.exists_halfHolder_representative_of_hasC1GraphBoundary
    (k := k) hγ hn hopen hbounded hgraph
  exact ⟨Inequalities.holderEmbeddingCLMOfExists hopen hrep,
    Inequalities.holderRepresentativeOfExists_ae hrep⟩

/-- Integrable adjacent weak derivatives construct classical fields with a
constant fixed before the family. The final integrable time level needs no
further derivative or endpoint trace. -/
theorem exists_finite_classical_representatives {γ : Exponent} (hγ : (γ : ℝ) = 1 / 2)
    (hn : 0 < n) (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ y : Fin (k + 2) → ℝ → W^{k + n / 2 + 1,2}(Ω),
        (∀ j, IntegrableOn (y j) (Ioo a b)) →
        (∀ j : Fin (k + 1),
          HasWeakTimeDerivativeOn (Ioo a b) (y j.castSucc) (y j.succ)) →
      ∃ R : Fin (k + 1) → ℝ → CKGammaOn n k Ω γ,
        (∀ j, Continuous (R j)) ∧
        (∀ j, ∀ᵐ t ∂volume.restrict (Ioo a b),
          (R j t).interiorDerivative 0 =ᵐ[domainMeasure n Ω]
            baseRepresentative (y j.castSucc t)) ∧
        (∀ j : Fin k, HasWeakTimeDerivativeOn (Ioo a b) (R j.castSucc) (R j.succ)) ∧
        (∀ j : Fin k, ∀ t ∈ Icc a b,
          HasDerivWithinAt (R j.castSucc) (R j.succ t) (Icc a b) t) ∧
        ContDiffUpToBoundary k (CKGammaOn.spaceTimeField R 0 0)
          (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)) ∧
        ContinuousOn (CKGammaOn.spaceTimeField R 0 0)
          (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)) ∧
        ∀ j, ∀ t ∈ Icc a b, ‖R j t‖ ≤ C *
          ((b - a)⁻¹ * (∫ r in Ioo a b, ‖y j.castSucc r‖) +
            ∫ r in Ioo a b, ‖y j.succ r‖) := by
  obtain ⟨E, hE⟩ := exists_hilbertHolder_embedding (k := k) hγ hn hopen hbounded hgraph
  refine ⟨‖E‖ + 1, by positivity, fun y hy hweak ↦ ?_⟩
  obtain ⟨S, hS, hae, _, hSweak, hSderiv, hbound⟩ :=
    exists_finite_continuous_representatives_Icc hab y hy hweak
  let R : Fin (k + 1) → ℝ → CKGammaOn n k Ω γ := fun j t ↦ E (S j t)
  have hR (j : Fin (k + 1)) : Continuous (R j) := E.continuous.comp (hS j)
  have hd (j : Fin k) (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt (R j.castSucc) (R j.succ t) (Icc a b) t :=
    E.hasFDerivAt.comp_hasDerivWithinAt t (hSderiv j t ht)
  refine ⟨R, hR, ?_, fun j ↦ (hSweak j).map E, hd, ?_, ?_, ?_⟩
  · intro j
    filter_upwards [hae j] with t ht
    simpa only [ht] using hE (S j t)
  · exact CKGammaOn.contDiffUpToBoundary_spaceTimeField hopen hbounded
      (fun j ↦ (hR j).continuousOn) hd k 0 0 (by simp)
  · exact CKGammaOn.continuousOn_spaceTimeField (fun j ↦ (hR j).continuousOn) 0 0
  · intro j t ht
    have hnonneg : 0 ≤ (b - a)⁻¹ * (∫ r in Ioo a b, ‖y j.castSucc r‖) +
        ∫ r in Ioo a b, ‖y j.succ r‖ :=
      add_nonneg (mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
        (integral_nonneg fun _ ↦ norm_nonneg _)) (integral_nonneg fun _ ↦ norm_nonneg _)
    exact (E.le_opNorm (S j t)).trans
      ((mul_le_mul_of_nonneg_left (hbound j t ht) (norm_nonneg E)).trans
        (mul_le_mul_of_nonneg_right (by linarith : ‖E‖ ≤ ‖E‖ + 1) hnonneg))

end SobolevSpace.Evolution
