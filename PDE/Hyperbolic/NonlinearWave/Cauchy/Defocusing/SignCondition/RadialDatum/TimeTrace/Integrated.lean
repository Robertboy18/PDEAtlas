/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.Displacement.BoundedVelocity
public import PDE.Analysis.MeasureTheory.Integral.Reaction.PowerGrowth
public import PDE.Analysis.MeasureTheory.Lp.JointRepresentative
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.RadialDatum.Superlevel
public import PDE.Spaces.Sobolev.Evolution.WholeSpaceL2Triple

/-!
# The radial obstruction from local integrated displacement data

On the unit ball, use the ambient H¹ space, with no zero boundary condition.
The original integrated displacement identity and an L∞ velocity supply the
initial trace. Joint representatives are constructed from Bochner L², and the
reaction is the negative seventh power of the same displacement sections.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped ENNReal NNReal Sobolev

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- The signed source reaction fails local Bochner L² for any ambient-H¹
integrated displacement with the radial trace and essentially bounded velocity. -/
theorem not_memLp_signed_reaction_of_local_integrated_displacement {T : ℝ}
    {q : Lp (W^{1,2}(Metric.ball (0 : ℝ^3) 1)) 2 (volume.restrict (Ioc 0 T))}
    {v : Lp (DerivLp 3 2 (Metric.ball (0 : ℝ^3) 1)) 2 (volume.restrict (Ioc 0 T))}
    {q₀ : DerivLp 3 2 (Metric.ball (0 : ℝ^3) 1)} {R : ℝ → DerivLp 3 2 (Metric.ball (0 : ℝ^3) 1)}
    (hq : IsGelfandIntegratedWeakSolution (hOneLTwoGelfandTriple Metric.isOpen_ball) (fun _ ↦ 0)
      (fun t ↦ (hOneLTwoGelfandTriple Metric.isOpen_ball).pivotToDual (v t)) q q₀)
    (hv : MemLp (fun t ↦ v t) ∞ (volume.restrict (Ioc 0 T)))
    (hg : (q₀ : ℝ^3 → ℝ) =ᵐ[volume.restrict (Metric.ball 0 1)] singularRadialDatum)
    (hreact : ∀ᵐ t ∂volume.restrict (Ioc 0 T), (fun x ↦ -(wkpBaseCoordinateCLM (q t) x) ^ 7)
      =ᵐ[volume.restrict (Metric.ball (0 : ℝ^3) 1)] (R t : ℝ^3 → ℝ)) :
    ¬ MemLp R 2 (volume.restrict (Ioc 0 T)) := by
  intro hR
  let ν : Measure (ℝ^3) := volume.restrict (Metric.ball (0 : ℝ^3) 1)
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let J := hOneLTwoGelfandTriple (Metric.isOpen_ball (x := (0 : ℝ^3)) (ε := 1))
  let : MeasurableSpace (W^{1,2}(Metric.ball (0 : ℝ^3) 1)) := borel _
  let : BorelSpace (W^{1,2}(Metric.ball (0 : ℝ^3) 1)) := ⟨rfl⟩
  let : MeasurableSpace (StrongDual ℝ (W^{1,2}(Metric.ball (0 : ℝ^3) 1))) := borel _
  let : BorelSpace (StrongDual ℝ (W^{1,2}(Metric.ball (0 : ℝ^3) 1))) := ⟨rfl⟩
  obtain ⟨Q, K, hLip, hinit, hQ, hweak, hbound⟩ := hq.exists_lipschitz_displacement hv
  obtain ⟨u, hu, _, hsection⟩ := (J.inclusion.comp_memLp q).exists_jointRepresentative
  have hsectionQ : ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      (Q t : ℝ^3 → ℝ) =ᵐ[ν] fun x ↦ u (t, x) := by
    filter_upwards [hQ, hsection] with t ht hs
    rw [ht]
    exact hs.symm
  have hRsection : ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      (fun x ↦ -(u (t, x) ^ 7)) =ᵐ[ν] (R t : ℝ^3 → ℝ) := by
    filter_upwards [hsection, hreact] with t hs hr using (hs.fun_comp fun z : ℝ ↦ -(z ^ 7)).trans hr
  have hpot : MemLp (fun z ↦ -(u z ^ 7)) 2 ((volume.restrict (Ioc 0 T)).prod ν) :=
    memLp_prod_of_ae_eq_L2_sections hR (hu.pow 7).neg.aestronglyMeasurable hRsection
  have hfourteen : Integrable (fun z ↦ u z ^ 14)
      ((volume.restrict (Ioc 0 T)).prod ν) := by
    have h := hpot.integrable_norm_pow (p := 2) (by decide)
    simpa only [norm_neg, Real.norm_eq_abs, sq_abs, ← pow_mul] using h
  have hgmeas : AEStronglyMeasurable (fun z : ℝ × (ℝ^3) ↦ singularRadialDatum z.2)
      ((volume.restrict (Ioc 0 T)).prod ν) :=
    (memLp_singularRadialDatum_eight.aestronglyMeasurable.aemeasurable.mono_measure
      (show ν ≤ volume from Measure.restrict_le_self)).comp_snd.aestronglyMeasurable
  apply not_integrable_pow_fourteen_of_bounded_weak_derivative
    (μ := ν) (ν := ν) (U := Q) (V := fun t ↦ v t) (u := u) (g := singularRadialDatum)
    (K := K) (δ := 1 / 2) (c := volume.real (Metric.ball (0 : ℝ^3) 1))
    le_rfl hq.interval_nonempty (by norm_num) volume_real_unitBall_pos
    (fun s ↦ Metric.ball 0 (s ^ 6)) ?_ hweak ?_ hbound ?_
    (hu.aestronglyMeasurable.sub hgmeas) hsectionQ ?_ hfourteen
  · exact fun s hs ↦ (volume_real_restrict_unitBall_ball_pow_six hs.1.le
      (hs.2.trans (by norm_num))).ge
  · exact fun ell ↦ ell.continuous.comp_continuousOn hLip.continuousOn
  · exact fun s hs ↦ ae_one_div_sq_add_one_le_singularRadialDatum hs.1 hs.2
  · rwa [hinit]

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
