/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Classical.Uniqueness
public import PDE.Spaces.Sobolev.Evolution.Classical.Representative

/-!
# One smooth representative from arbitrary finite Sobolev regularity

Every finite derivative budget gives a classical representative of the same
measurable time slices. Continuity identifies all these representatives on the
closed cylinder. Thus one function has every finite order of joint regularity,
including the uniformly continuous extensions of all its mixed derivatives.

The finite Sobolev families need not be chosen coherently across orders.
Their agreement with the original measurable function supplies that coherence.
-/

@[expose] public section

open PDE (SpaceTime)

noncomputable section

open MeasureTheory Set PDE.Common
open scoped Sobolev

namespace SobolevSpace.Evolution

open GraphSpace HolderSpace PDE.Analysis.Evolution

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Arbitrary finite Sobolev time regularity determines one jointly smooth
representative, uniquely on the entire closed cylinder. -/
theorem exists_joint_smooth_representative
    (hn : 0 < n) (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b)
    (u : ℝ → ℝ^n → ℝ)
    (hregular : ∀ k : ℕ,
      ∃ y : Fin (k + 2) → ℝ → W^{k + n / 2 + 1,2}(Ω),
        (∀ j, IntegrableOn (y j) (Ioo a b)) ∧
        (∀ j : Fin (k + 1),
          HasWeakTimeDerivativeOn (Ioo a b) (y j.castSucc) (y j.succ)) ∧
        ∀ᵐ t ∂volume.restrict (Ioo a b),
          baseRepresentative (y 0 t) =ᵐ[domainMeasure n Ω] u t) :
    ∃ U : SpaceTime n → ℝ,
      ContinuousOn U (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)) ∧
      (∀ k : ℕ, ContDiffUpToBoundary k U (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b))) ∧
      (∀ᵐ t ∂volume.restrict (Ioo a b),
        (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω] u t) ∧
      ∀ V : SpaceTime n → ℝ,
        ContinuousOn V (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)) →
        (∀ᵐ t ∂volume.restrict (Ioo a b),
          (fun x ↦ V (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω] u t) →
        EqOn V U (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)) := by
  let γ : Exponent := ⟨1 / 2, by norm_num, by norm_num⟩
  have hfinite (k : ℕ) : ∃ F : SpaceTime n → ℝ,
      ContinuousOn F (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)) ∧
      ContDiffUpToBoundary k F (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)) ∧
      ∀ᵐ t ∂volume.restrict (Ioo a b),
        (fun x ↦ F (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω] u t := by
    obtain ⟨y, hy, hweak, hyu⟩ := hregular k
    obtain ⟨_, _, hrep⟩ := exists_finite_classical_representatives
      (γ := γ) rfl hn hopen hbounded hgraph hab k
    obtain ⟨R, _, hae, _, _, hreg, hcont, _⟩ := hrep y hy hweak
    refine ⟨CKGammaOn.spaceTimeField R 0 0, hcont, hreg, ?_⟩
    filter_upwards [hae 0, hyu] with t ht htu
    simpa [CKGammaOn.spaceTimeField, CKGammaOn.mixedField] using ht.trans htu
  choose F hcont hreg hae using hfinite
  have heq (k : ℕ) :
      EqOn (F 0) (F k) (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)) := by
    apply eqOn_closed_spaceTime_cylinder_of_ae_eq hopen hab (hcont 0) (hcont k)
    filter_upwards [hae 0, hae k] with t ht hk
    exact ht.trans hk.symm
  refine ⟨F 0, hcont 0, ?_, hae 0, ?_⟩
  · intro k
    apply (hreg k).congr
      ((hopen.prod isOpen_Ioo).preimage (spaceTimeContinuousLinearEquiv n).continuous)
    intro z hz
    exact heq k ⟨subset_closure hz.1, Ioo_subset_Icc_self hz.2⟩
  · intro V hV hVu
    apply eqOn_closed_spaceTime_cylinder_of_ae_eq hopen hab hV (hcont 0)
    filter_upwards [hVu, hae 0] with t ht h0
    exact ht.trans h0.symm

end SobolevSpace.Evolution
