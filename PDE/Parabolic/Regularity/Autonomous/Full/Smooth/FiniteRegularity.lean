/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.HigherOrder.Forcing
public import PDE.Spaces.Sobolev.Evolution.Classical.Smooth
public import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates

/-!
# Finite parabolic Sobolev estimates give one smooth representative

The decreasing spatial orders in the parabolic estimate contain any required
finite family of time derivatives in a common Sobolev space. Spatial restriction
preserves the weak time derivatives between entries. The classical
representative theorem then identifies all finite choices on the entire closed
cylinder.
-/

@[expose] public noncomputable section

open scoped Sobolev

open MeasureTheory Set

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder.ForcingJet

open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- A finite initial segment lies in one common Sobolev space and keeps its
weak time derivatives there. -/
theorem exists_commonSpace_family (s d : ℕ) (F : ForcingJet n Ω a b (s + d))
    (hF : F.HasWeakDerivatives) :
    ∃ y : Fin (d + 1) → ℝ → W^{s,2}(Ω),
      (∀ j, IntegrableOn (y j) (Ioo a b)) ∧
      (∀ j : Fin d, HasWeakTimeDerivativeOn (Ioo a b) (y j.castSucc) (y j.succ)) ∧
      ∀ t, y 0 t = lowerOrderCLM (show s ≤ 2 * (s + d) by omega) (F.head t) := by
  induction d with
  | zero =>
    let E : W^{(2 * s),2}(Ω) →L[ℝ] W^{s,2}(Ω) :=
      lowerOrderCLM (by omega)
    refine ⟨fun _ t ↦ E (F.head t), ?_, fun j ↦ Fin.elim0 j, fun _ ↦ rfl⟩
    intro j
    exact E.integrable_comp (((Lp.memLp F.head).integrable (by norm_num)).mono_measure
      (volume.restrict_mono_set Ioo_subset_Ioc_self))
  | succ d ih =>
    obtain ⟨z, hz, hd, hzero⟩ := ih F.2 hF.2
    let E : W^{(2 * (s + (d + 1))),2}(Ω) →L[ℝ] W^{s,2}(Ω) :=
      lowerOrderCLM (by omega)
    let y : Fin (d + 1 + 1) → ℝ → W^{s,2}(Ω) :=
      Fin.cons (fun t ↦ E (F.1 t)) z
    refine ⟨y, ?_, ?_, fun _ ↦ rfl⟩
    · intro j
      refine Fin.cases ?_ (fun i ↦ hz i) j
      exact E.integrable_comp (((Lp.memLp F.1).integrable (by norm_num)).mono_measure
        (volume.restrict_mono_set Ioo_subset_Ioc_self))
    · intro j
      refine Fin.cases ?_ (fun i ↦ ?_) j
      · change HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ E (F.1 t)) (z 0)
        have h := hF.1.map (lowerOrderCLM (show s ≤ 2 * (s + d) by omega))
        simpa only [Function.comp_def, lowerOrderCLM_trans_apply, E, ← hzero] using h
      · change HasWeakTimeDerivativeOn (Ioo a b) (z i.castSucc) (z i.succ)
        exact hd i

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder.ForcingJet

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth

open SobolevSpace SobolevSpace.GraphSpace PDE.Common HigherOrder

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Arbitrary finite parabolic regularity of the same original weak solution
constructs one smooth function on the entire closed cylinder. -/
theorem exists_joint_smooth_representative_of_finite_regularity
    (hn : 0 < n) (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b)
    (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
    (hregular : ∀ m : ℕ, ∃ F : ForcingJet n Ω a b (m + 1),
      F.HasWeakDerivatives ∧
      ∀ᵐ t ∂volume.restrict (Ioc a b),
        wkpBaseCoordinateCLM (F.head t) = baseCoordCLM (u t)) :
    ∃ U : SpaceTime n → ℝ,
      ContinuousOn U (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)) ∧
      (∀ k : ℕ, ContDiffUpToBoundary k U (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b))) ∧
      (∀ᵐ t ∂volume.restrict (Ioo a b),
        (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
          baseRepresentative (h10SubtypeL (u t))) ∧
      ∀ V : SpaceTime n → ℝ,
        ContinuousOn V (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)) →
        (∀ᵐ t ∂volume.restrict (Ioo a b),
          (fun x ↦ V (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
            baseRepresentative (h10SubtypeL (u t))) →
        EqOn V U (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)) := by
  apply SobolevSpace.Evolution.exists_joint_smooth_representative
    hn hopen hbounded hgraph hab (fun t ↦ baseRepresentative (h10SubtypeL (u t)))
  intro k
  obtain ⟨F, hF, hbase⟩ := hregular ((k + n / 2 + 1) + k)
  obtain ⟨y, hy, hd, hzero⟩ := F.exists_commonSpace_family (k + n / 2 + 1) (k + 1) hF
  refine ⟨y, hy, hd, ?_⟩
  filter_upwards [hbase.filter_mono
    (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))] with t ht
  rw [hzero, baseRepresentative_lowerOrderCLM]
  exact Filter.Eventually.of_forall
    (congrFun (congrArg (fun z : DerivLp n 2 Ω ↦ (z : ℝ^n → ℝ)) ht))

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth
