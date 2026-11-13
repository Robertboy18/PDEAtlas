/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.DistributionalDerivatives
public import PDE.Spaces.Sobolev.Evolution.Classical.Representative.Identification
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.H10L2

/-!
# Identifying a smooth representative with the original weak wave

Once a joint smooth displacement has been constructed, uniqueness of
Banach-valued weak derivatives identifies its canonical velocity and
acceleration with the original weak fields. The integrated initial identities
then identify the continuous endpoint slices.
-/

@[expose] public noncomputable section

open PDE (SpaceTime)

open scoped Sobolev

namespace Hyperbolic.HigherRegularity.SmoothWave

open Filter MeasureTheory Set PDE.Common SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution SobolevSpace.Evolution.Classical

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
  {U : SpaceTime n → ℝ}
  (hU : ∀ k, ContDiffUpToBoundary k U (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)))
  (hcont : ContinuousOn U (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)))
  {B : ℝ → H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω))}
  {ell : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))}
  {u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))}
  {v : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))}
  {w : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))}
  {q₀ : H¹₀(Ω)} {p₀ : DerivLp n 2 Ω}
  (hweak : Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hopen)
    B ell u v w q₀ p₀)
  (hae : ∀ᵐ t ∂volume.restrict (Ioo a b),
    (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
      baseRepresentative (h10SubtypeL (u t)))

include hcont hweak hae

/-- The canonical first time derivative represents the original weak velocity. -/
theorem velocity_ae :
    (fun t ↦ wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 1 1 t))
      =ᵐ[volume.restrict (Ioc a b)] fun t ↦ v t := by
  have hq := sobolevCurve_ae_of_representative hopen hbounded hab hU hcont hae
  have hd := (hasWeakTimeDerivativeOn_sobolevCurve hopen hbounded hab hU 1 0).map
    wkpBaseCoordinateCLM
  have hd' : HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ (h10L2GelfandTriple hopen).inclusion (u t))
      (fun t ↦ wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 1 1 t)) := by
    apply hd.congr_ae_restrict measurableSet_Ioo ?_ Filter.EventuallyEq.rfl
    filter_upwards [hq.filter_mono
      (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))] with t ht
    dsimp only [Function.comp_apply]
    rw [ht]
    rfl
  exact (ae_restrict_congr_set Ioo_ae_eq_Ioc).mp
    (hd'.ae_eq isOpen_Ioo hweak.displacement_hasWeakTimeDerivativeOn)

/-- The canonical second time derivative represents the original weak
acceleration in the Dirichlet dual. -/
theorem acceleration_ae :
    (fun t ↦ (h10L2GelfandTriple hopen).pivotToDual (wkpBaseCoordinateCLM
      (sobolevCurve hopen hbounded hab hU 1 2 t))) =ᵐ[volume.restrict (Ioc a b)] fun t ↦ w t := by
  have hv := velocity_ae hopen hbounded hab hU hcont hweak hae
  have hd := ((hasWeakTimeDerivativeOn_sobolevCurve hopen hbounded hab hU 1 1).map
    wkpBaseCoordinateCLM).map (h10L2GelfandTriple hopen).pivotToDual
  have hd' : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ (h10L2GelfandTriple hopen).pivotToDual (v t))
      (fun t ↦ (h10L2GelfandTriple hopen).pivotToDual
        (wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 1 2 t))) := by
    apply hd.congr_ae_restrict measurableSet_Ioo ?_ Filter.EventuallyEq.rfl
    filter_upwards [hv.filter_mono
      (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))] with t ht
    dsimp only [Function.comp_apply]
    rw [ht]
  exact (ae_restrict_congr_set Ioo_ae_eq_Ioc).mp
    (hd'.ae_eq isOpen_Ioo hweak.velocity_hasWeakTimeDerivativeOn)

/-- The canonical displacement has the initial value from the integrated
weak solution, as an endpoint equality in the pivot space. -/
theorem initial_displacement_eq :
    wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 1 0 a) = baseCoordCLM q₀ := by
  apply hweak.continuousDisplacement_eq_initial (wkpBaseCoordinateCLM.continuous.comp_continuousOn
      (continuousOn_sobolevCurve hopen hbounded hab hU 1 0))
  filter_upwards [sobolevCurve_ae_of_representative hopen hbounded hab hU hcont hae] with t ht
  dsimp only [Function.comp_apply]
  rw [ht]
  rfl

/-- The canonical velocity has the initial value from the original integrated
velocity identity. -/
theorem initial_velocity_eq :
    wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hU 1 1 a) = p₀ :=
  hweak.continuousVelocity_eq_initial (wkpBaseCoordinateCLM.continuous.comp_continuousOn
      (continuousOn_sobolevCurve hopen hbounded hab hU 1 1))
    (velocity_ae hopen hbounded hab hU hcont hweak hae)

end Hyperbolic.HigherRegularity.SmoothWave
