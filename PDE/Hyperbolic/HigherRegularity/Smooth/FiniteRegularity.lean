/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Data.SobolevTimeJet
public import PDE.Spaces.Sobolev.Evolution.Classical.Smooth

/-!
# Finite classical budgets in a wave Sobolev time jet

Restricting a finite initial segment of the wave jet to a common
Sobolev space preserves every weak time link. A jet of spatial order
`2*k + floor(n/2) + 2` supplies the common spatial budget
`k + floor(n/2) + 1` through time derivative `k+1`. The representative
theorem can therefore recover joint classical regularity.
-/

@[expose] public section

open PDE (SpaceTime)

open scoped Sobolev

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.HigherRegularity.SobolevTimeJet

open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- An initial segment of a decreasing Sobolev jet is a finite weak
derivative family in any common lower Sobolev space. -/
theorem exists_commonSpace_family (s d : ℕ)
    (U : SobolevTimeJet n (s + d) Ω a b) :
    ∃ y : Fin (d + 1) → ℝ → W^{s,2}(Ω),
      (∀ j, IntegrableOn (y j) (Ioo a b)) ∧
      (∀ j : Fin d, HasWeakTimeDerivativeOn (Ioo a b) (y j.castSucc) (y j.succ)) ∧
      ∀ t, y 0 t = lowerOrderCLM (Nat.le_add_right s d) (U.head t) := by
  induction d with
  | zero =>
      refine ⟨fun _ t ↦ U.head t, ?_, fun j ↦ Fin.elim0 j, ?_⟩
      · exact fun j ↦ ((Lp.memLp U.head).integrable (by norm_num)).mono_measure
          (volume.restrict_mono_set Ioo_subset_Ioc_self)
      · intro t
        simp
  | succ d ih =>
      obtain ⟨z, hz, hd, hzero⟩ := ih U.timeDerivative
      let E : W^{(s + d + 1),2}(Ω) →L[ℝ] W^{s,2}(Ω) :=
        lowerOrderCLM (by omega)
      let y : Fin (d + 1 + 1) → ℝ → W^{s,2}(Ω) := Fin.cons (fun t ↦ E (U.head t)) z
      refine ⟨y, ?_, ?_, fun _ ↦ rfl⟩
      · intro j
        refine Fin.cases ?_ (fun i ↦ hz i) j
        exact E.integrable_comp
          (((Lp.memLp U.head).integrable (by norm_num)).mono_measure
            (volume.restrict_mono_set Ioo_subset_Ioc_self))
      · intro j
        refine Fin.cases ?_ (fun i ↦ ?_) j
        · change HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ E (U.head t)) (z 0)
          have h := U.hasWeakTimeDerivative_timeDerivative.map
            (lowerOrderCLM (Nat.le_add_right s d))
          simpa only [Function.comp_def, lowerOrderCLM_trans_apply, E, ← hzero] using h
        · change HasWeakTimeDerivativeOn (Ioo a b) (z i.castSucc) (z i.succ)
          exact hd i

end Hyperbolic.HigherRegularity.SobolevTimeJet

namespace Hyperbolic.HigherRegularity

open SobolevSpace SobolevSpace.GraphSpace PDE.Common

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Arbitrary finite wave jets of the same original displacement give one
jointly smooth representative. This is the analytic step after constructing
the jets from the compatible wave data. -/
theorem exists_joint_smooth_representative_of_wave_jets
    (hn : 0 < n) (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b)
    (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
    (hjets : ∀ m : ℕ, ∃ U : SobolevTimeJet n (m + 1) Ω a b,
      ∀ᵐ t ∂volume.restrict (Ioc a b),
        lowerOrderCLM (by omega : 1 ≤ m + 1) (U.head t) = h10SubtypeL (u t)) :
    ∃ U : SpaceTime n → ℝ,
      ContinuousOn U (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)) ∧
      (∀ k : ℕ, ContDiffUpToBoundary k U (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b))) ∧
      ∀ᵐ t ∂volume.restrict (Ioo a b),
        (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
          baseRepresentative (h10SubtypeL (u t)) := by
  refine (SobolevSpace.Evolution.exists_joint_smooth_representative
    hn hopen hbounded hgraph hab (fun t ↦ baseRepresentative (h10SubtypeL (u t))) ?_).imp ?_
  · intro k
    obtain ⟨V, hV⟩ := hjets ((k + n / 2 + 1) + k)
    obtain ⟨y, hy, hd, hzero⟩ := V.exists_commonSpace_family (k + n / 2 + 1) (k + 1)
    refine ⟨y, hy, hd, ?_⟩
    filter_upwards [hV.filter_mono (ae_mono
      (volume.restrict_mono_set Ioo_subset_Ioc_self))] with t ht
    have heq := congrArg baseRepresentative ht
    rw [baseRepresentative_lowerOrderCLM] at heq
    rw [hzero, baseRepresentative_lowerOrderCLM, heq]
  · exact fun U hU ↦ ⟨hU.1, hU.2.1, hU.2.2.1⟩

end Hyperbolic.HigherRegularity
