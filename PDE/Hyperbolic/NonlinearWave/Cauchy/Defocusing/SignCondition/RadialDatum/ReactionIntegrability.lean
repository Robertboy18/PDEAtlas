/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.Reaction.PowerGrowth
public import PDE.Analysis.MeasureTheory.Lp.Fubini
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.RadialDatum.Superlevel

/-!
# Initial-time reaction integrability for a singular finite-energy datum

The radial H¹ datum has integrable seventh-power potential, but any weak time trajectory with
bounded L² velocity and its initial trace fails the initial-time `L²(0,T; L²(B₁))` reaction
requirement. The Bochner reaction curve and displacement representative are identified explicitly by
AE sections.

The same H¹ witness supplies the zero-velocity finite-energy pair and the obstruction for every
positive lifetime.

The example concerns the reaction class `f(u) ∈ L²(0,T; L²_loc(ℝⁿ))` in the definition of a weak
solution at the start of Evans, §12.2, for trajectories with the bounded velocity
`u' ∈ L^∞((0,∞); L²(ℝⁿ))` of §12.3.1, Theorem 1. The reaction `z^7` satisfies the sign condition (2)
of that theorem, and the proof of the theorem identifies the reaction only as a local L¹ limit,
in (9). The example does not exclude the weaker local L¹ reaction class or reaction integrability
only locally away from the initial time.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.2, definition of a weak solution; §12.3.1, Theorem 1 and
  its proof, equation (9).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped NNReal Sobolev
open PDE.Analysis (primitive)

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- The radial datum cannot have a bounded-velocity weak time trajectory
whose seventh-power reaction is in `L²(0,T; L²(B₁))`. No wave-equation hypothesis
is needed for this stronger kinematic obstruction. -/
theorem not_memLp_seventh_power_reaction_of_singularRadialDatum
    {U V : ℝ → Lp ℝ 2 (volume : Measure (ℝ^3))} {u : ℝ × (ℝ^3) → ℝ}
    {R : ℝ → Lp ℝ 2 (volume.restrict (Metric.ball (0 : ℝ^3) 1))} {T : ℝ} {K : ℝ≥0} (hT : 0 < T)
    (hweak : HasWeakTimeDerivativeOn (Ioo 0 T) U V)
    (hu : ∀ ell : StrongDual ℝ (Lp ℝ 2 (volume : Measure (ℝ^3))),
      ContinuousOn (fun t ↦ ell (U t)) (Icc 0 T))
    (hbound : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ‖V t‖ ≤ K)
    (hmeas : AEStronglyMeasurable u
      ((volume.restrict (Ioo 0 T)).prod (volume.restrict (Metric.ball (0 : ℝ^3) 1))))
    (hsection : ∀ᵐ t ∂volume.restrict (Ioo 0 T), (U t : ℝ^3 → ℝ) =ᵐ[volume] fun x ↦ u (t, x))
    (hg : (U 0 : ℝ^3 → ℝ) =ᵐ[volume] singularRadialDatum)
    (hreact : ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      (fun x ↦ u (t, x) ^ 7) =ᵐ[volume.restrict (Metric.ball (0 : ℝ^3) 1)] (R t : ℝ^3 → ℝ)) :
    ¬ MemLp R 2 (volume.restrict (Ioo 0 T)) := by
  intro hR
  let ν : Measure (ℝ^3) := volume.restrict (Metric.ball (0 : ℝ^3) 1)
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hpot : MemLp (fun z ↦ u z ^ 7) 2 ((volume.restrict (Ioo 0 T)).prod ν) :=
    memLp_prod_of_ae_eq_L2_sections hR (hmeas.pow 7) hreact
  have hfourteen : Integrable (fun z ↦ u z ^ 14)
      ((volume.restrict (Ioc 0 T)).prod ν) := by
    have h := hpot.integrable_norm_pow (p := 2) (by decide)
    simpa only [Real.norm_eq_abs, sq_abs, ← pow_mul, restrict_Ioo_eq_restrict_Ioc] using h
  have hgmeas : AEStronglyMeasurable (fun z : ℝ × (ℝ^3) ↦ singularRadialDatum z.2)
      ((volume.restrict (Ioo 0 T)).prod ν) :=
    (memLp_singularRadialDatum_eight.aestronglyMeasurable.aemeasurable.mono_measure
      (show ν ≤ volume from Measure.restrict_le_self)).comp_snd.aestronglyMeasurable
  apply not_integrable_pow_fourteen_of_bounded_weak_derivative
    (μ := volume) (ν := ν) (U := U) (V := V) (u := u) (g := singularRadialDatum)
    (K := K) (δ := 1 / 2) (c := volume.real (Metric.ball (0 : ℝ^3) 1))
    Measure.restrict_le_self hT (by norm_num) volume_real_unitBall_pos
    (fun s ↦ Metric.ball 0 (s ^ 6)) ?_ hweak hu hbound ?_ ?_ ?_ hg hfourteen
  · exact fun s hs ↦ (volume_real_restrict_unitBall_ball_pow_six hs.1.le
      (hs.2.trans (by norm_num))).ge
  · exact fun s hs ↦ ae_one_div_sq_add_one_le_singularRadialDatum hs.1 hs.2
  · simpa only [Pi.sub_def, restrict_Ioo_eq_restrict_Ioc] using hmeas.sub hgmeas
  · simpa only [restrict_Ioo_eq_restrict_Ioc] using hsection

/-- A finite-energy initial pair with reaction `z^7` admits no trajectory
in the initial-time L² reaction class with bounded velocity and its given traces.
The same H¹ witness supplies both the integrable potential and the obstruction. -/
theorem exists_energyDatum_no_seventh_power_trajectory :
    ∃ X : H¹(ℝ^3) × DerivLp 3 2 univ,
      ((energyTriple 3).inclusion X.1 : ℝ^3 → ℝ) =ᵐ[volume] singularRadialDatum ∧
      X.2 = 0 ∧
      Integrable (fun x ↦ primitive (fun z ↦ z ^ 7) ((energyTriple 3).inclusion X.1 x))
        (domainMeasure 3 univ) ∧
      ∀ T : ℝ, 0 < T → ¬ ∃ (U V : ℝ → Lp ℝ 2 (volume : Measure (ℝ^3)))
          (u : ℝ × (ℝ^3) → ℝ)
          (R : ℝ → Lp ℝ 2 (volume.restrict (Metric.ball (0 : ℝ^3) 1))) (K : ℝ≥0),
        HasWeakTimeDerivativeOn (Ioo 0 T) U V ∧
        (∀ ell : StrongDual ℝ (Lp ℝ 2 (volume : Measure (ℝ^3))),
          ContinuousOn (fun t ↦ ell (U t)) (Icc 0 T)) ∧
        (∀ᵐ t ∂volume.restrict (Ioo 0 T), ‖V t‖ ≤ K) ∧
        AEStronglyMeasurable u ((volume.restrict (Ioo 0 T)).prod
          (volume.restrict (Metric.ball (0 : ℝ^3) 1))) ∧
        (∀ᵐ t ∂volume.restrict (Ioo 0 T),
          (U t : ℝ^3 → ℝ) =ᵐ[volume] fun x ↦ u (t, x)) ∧
        ((U 0 : ℝ^3 → ℝ) =ᵐ[volume] (energyTriple 3).inclusion X.1) ∧
        ((V 0 : ℝ^3 → ℝ) =ᵐ[volume] (X.2 : ℝ^3 → ℝ)) ∧
        MemLp R 2 (volume.restrict (Ioo 0 T)) ∧
        (∀ᵐ t ∂volume.restrict (Ioo 0 T),
          (fun x ↦ u (t, x) ^ 7) =ᵐ[volume.restrict (Metric.ball (0 : ℝ^3) 1)]
            (R t : ℝ^3 → ℝ)) := by
  obtain ⟨G, hG, hpotential⟩ := exists_energyDatum_singularRadialDatum
  refine ⟨(G, 0), hG, rfl, hpotential, fun T hT htrajectory ↦ ?_⟩
  obtain ⟨U, V, u, R, K, hweak, hu, hbound, hmeas, hsection, hg, _, hR, hreact⟩ := htrajectory
  exact not_memLp_seventh_power_reaction_of_singularRadialDatum hT hweak hu hbound
    hmeas hsection (hg.trans hG) hreact hR

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
