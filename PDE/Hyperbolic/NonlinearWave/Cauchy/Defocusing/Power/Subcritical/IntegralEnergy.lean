/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PowerPotential.Classical
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.EnergyRepresentation
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.IntegralSupportData
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.LipschitzEnergy
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FiniteInterval

/-!
# Conserved energy of the integral lifespan field

On each bounded prefix, a sign-preserving Lipschitz truncation agrees with the signed power
throughout the attained amplitude range. The tested PDE supplies energy-space primitives.
Finite-interval uniqueness identifies this trajectory with the Lipschitz energy solution and
transfers its conservation law. The cutoff potential agrees exactly with the signed-power potential.

Arbitrary compact C³ displacement and C² velocity construct a C¹ lifespan field with conserved
energy on every proper closed prefix, for every real exponent at least one. Global existence for
subcritical powers additionally needs cone estimates. The energy is the energy of (18) in Evans,
§12.3.3, and its conservation extends Theorem 1 of §12.1.1 to these C¹ fields.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.1, Theorem 1; §12.3.3, equation (18) and its energy.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution Hyperbolic.Variational
open scoped Topology Sobolev SobolevSpace.WholeSpaceHilbert Interval Laplacian
open PDE.Analysis (primitive)

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- The normalized potential agrees wherever a truncated reaction agrees with
the signed power on the interval from zero to the argument. -/
private theorem potential_eq_signedPowerPotential_on_ball {r R : ℝ} (hr : 1 ≤ r) {f : ℝ → ℝ}
    (hf : EqOn f (Real.signedPower r) (Metric.closedBall 0 R)) {z : ℝ} (hz : |z| ≤ R) :
    primitive f z = Real.signedPowerPotential r z := by
  have heq : (∫ s in 0..z, f s) = ∫ s in 0..z, Real.signedPower r s :=
    intervalIntegral.integral_congr fun s hs ↦ hf <| by
      simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using
        (show |s| ≤ |z| by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hs).trans hz
  rw [primitive, heq, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ ↦ Real.hasDerivAt_signedPowerPotential hr s)
      ((Real.continuous_signedPower (zero_lt_one.trans_le hr)).intervalIntegrable 0 z),
    Real.signedPowerPotential_zero hr, sub_zero]

/-- The signed-power energy is conserved on every bounded finite
energy trajectory. Conservation is transferred from the checked Lipschitz
Cauchy constructor by finite-interval uniqueness. -/
theorem signedPower_energy_eq_of_bounded_energy_primitives {r S M : ℝ} (hr : 1 ≤ r) (hS : 0 ≤ S)
    (hM : 0 ≤ M) {q : ℝ → H¹(ℝ^3)} {v F : ℝ → DerivLp 3 2 univ} (hq : Continuous q)
    (hv : Continuous v) {u : ℝ × ℝ^3 → ℝ} (hB : ∀ t ∈ Icc 0 S, ∀ x : ℝ^3, |u (t, x)| ≤ M)
    (hqae : ∀ t ∈ Icc 0 S, ((energyTriple 3).inclusion (q t) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ] fun
      x ↦ u (t, x))
    (hFae : ∀ t ∈ Icc 0 S, (F t : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ] fun x ↦
      -Real.signedPower r (u (t, x)))
    (hi : ∀ t ∈ Icc 0 S, (∫ s in 0..t, v s) = (energyTriple 3).inclusion (q t) -
      (energyTriple 3).inclusion (q 0) ∧ (∫ s in 0..t, (energyTriple 3).pivotToDual (F s) -
      gradientForm 3 (q s)) = (energyTriple 3).pivotToDual (v t) -
      (energyTriple 3).pivotToDual (v 0)) :
    ∀ t ∈ Icc 0 S, (1 / 2 : ℝ) * (gradientForm 3 (q t) (q t) + ‖v t‖ ^ 2) +
      (∫ x, Real.signedPowerPotential r (u (t, x))) = (1 / 2 : ℝ) *
      (gradientForm 3 (q 0) (q 0) + ‖v 0‖ ^ 2) + (∫ x, Real.signedPowerPotential r (u (0, x))) := by
  have hs (z : ℝ) : 0 ≤ z * Real.signedPower r z := by
    rw [Real.mul_signedPower_eq_abs_rpow hr]
    exact Real.rpow_nonneg (abs_nonneg _) _
  obtain ⟨g, K, _, _, hgLip, hmatch, hsign, _⟩ :=
    SignCondition.exists_sign_preserving_lipschitz_reaction
      (m := 1) (Real.contDiff_one_signedPower hr) one_ne_zero hs
      (show 0 < M + 1 by linarith)
  have hg0 := SignCondition.reaction_zero hgLip.continuous hsign
  let f : (ℝ^3 × ℝ × ℝ) → ℝ := fun z ↦ g z.2.2
  have hf : LipschitzWith K f := by
    simpa only [mul_one, Function.comp_def, f] using hgLip.comp
      (LipschitzWith.prod_snd.comp (LipschitzWith.prod_snd (α := ℝ^3)))
  have hf0 : f 0 = 0 := hg0
  have hreact (z : H¹(ℝ^3) × DerivLp 3 2 univ) :
      FirstJet.reaction hf hf0 z = hgLip.compLp hg0 ((energyTriple 3).inclusion z.1) := by
    apply Lp.ext
    filter_upwards [FirstJet.reaction_apply_ae hf hf0 z,
      hgLip.coeFn_compLp hg0 ((energyTriple 3).inclusion z.1)] with x hx hy
    exact hx.trans hy.symm
  have hreactF (t : ℝ) (ht : t ∈ Icc 0 S) :
      FirstJet.reaction hf hf0 (q t, v t) = -F t := by
    rw [hreact]
    apply Lp.ext
    filter_upwards [hgLip.coeFn_compLp hg0 ((energyTriple 3).inclusion (q t)),
      hqae t ht, hFae t ht, Lp.coeFn_neg (F t)] with x hx hqx hFx hneg
    rw [hx, hneg]
    change g ((energyTriple 3).inclusion (q t) x) = -(F t x)
    rw [hqx, hFx, neg_neg]
    exact hmatch (by simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      using (hB t ht x).trans (le_add_of_nonneg_right zero_le_one))
  have hacc (t : ℝ) (ht : t ∈ Icc 0 S) : FirstJet.acceleration hf hf0 (q t, v t) =
        (energyTriple 3).pivotToDual (F t) - gradientForm 3 (q t) := by
    simp only [FirstJet.acceleration, hreactF t ht, map_neg, neg_neg]
  have huOn : FirstJet.IsEnergySolutionOn hf hf0 (q 0, v 0) ⟨S, hS⟩
      (fun t ↦ (q t, v t)) := by
    refine ⟨(hq.prodMk hv).continuousOn, rfl, fun t ht ↦ (hi t ht).1, fun t ht ↦
      (intervalIntegral.integral_congr fun s hs ↦ ?_).trans (hi t ht).2⟩
    rw [uIcc_of_le ht.1] at hs
    exact hacc s ⟨hs.1, hs.2.trans ht.2⟩
  obtain ⟨w, hw, _, he, _⟩ :=
    SignCondition.exists_energySolution_of_lipschitz hgLip hsign (q 0, v 0)
  have hw' : FirstJet.IsEnergySolution hf hf0 (q 0, v 0) w :=
    ⟨hw.continuous, hw.initial, hw.displacement, fun t ht ↦ by
      simpa only [FirstJet.acceleration, hreact, Cauchy.acceleration] using hw.velocity t ht⟩
  have heq := huOn.eqOn (hw'.on ⟨S, hS⟩)
  have hpot (t : ℝ) (ht : t ∈ Icc 0 S) : SignCondition.physicalEnergy g (q t, v t) =
        (1 / 2 : ℝ) * (gradientForm 3 (q t) (q t) + ‖v t‖ ^ 2) +
          ∫ x, Real.signedPowerPotential r (u (t, x)) := by
    unfold SignCondition.physicalEnergy
    congr 1
    simp only [domainMeasure, Measure.restrict_univ] at hqae ⊢
    apply integral_congr_ae
    filter_upwards [hqae t ht] with x hx
    rw [hx]
    exact potential_eq_signedPowerPotential_on_ball hr hmatch
      ((hB t ht x).trans (le_add_of_nonneg_right zero_le_one))
  intro t ht
  rw [← hpot t ht, ← hpot 0 ⟨le_rfl, hS⟩]
  exact (congrArg (SignCondition.physicalEnergy g) (heq ht)).trans (he t ht.1)

/-- Continuous energy representatives with identified spatial derivatives
and velocity, and conserved signed-power energy on the closed prefix. -/
def HasConservedEnergyOn (r S : ℝ) (u : ℝ × ℝ^3 → ℝ) : Prop :=
  ∃ (q : ℝ → H¹(ℝ^3)) (v : ℝ → DerivLp 3 2 univ),
    Continuous q ∧ Continuous v ∧
    (∀ t ∈ Icc 0 S,
      ((energyTriple 3).inclusion (q t) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ]
        (fun x ↦ u (t, x)) ∧
      (∀ j : Fin 3, (wkpCoordinateCLM (singleDerivIndex 3 j) (q t) : ℝ^3 → ℝ)
        =ᵐ[domainMeasure 3 univ] ∂[j] (fun x ↦ u (t, x))) ∧
      (v t : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ]
        (fun x ↦ fderiv ℝ u (t, x) (1, 0))) ∧
    ∀ t ∈ Icc 0 S,
      (1 / 2 : ℝ) * (gradientForm 3 (q t) (q t) + ‖v t‖ ^ 2) +
        (∫ x, Real.signedPowerPotential r (u (t, x))) =
      (1 / 2 : ℝ) * (gradientForm 3 (q 0) (q 0) + ‖v 0‖ ^ 2) +
        (∫ x, Real.signedPowerPotential r (u (0, x)))

/-- A trajectory vanishing outside the cone `‖x‖ ≤ R + t` has compactly supported initial
position: at time zero it equals the free field, whose initial position is `g`. -/
theorem IsIntegralTrajectoryBefore.hasCompactSupport_initial_position {r b L R : ℝ}
    {g h : ℝ^3 → ℝ} {u : ℝ × ℝ^3 → ℝ}
    (hu : IsIntegralTrajectoryBefore r b (cauchyFreeField g h) L u)
    (hsupp : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → R + p.1 < ‖p.2‖ → u p = 0) :
    HasCompactSupport g := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ^3) R) fun x hx ↦ ?_
  have h0 : (0 : ℝ) ∈ Ico 0 L := ⟨le_rfl, hu.time_pos⟩
  have heq := hu.equation (0, x) h0
  dsimp only at heq
  rw [cauchyFreeField_initial_position, WaveEquation.oddDuhamelSolution_initial 0,
    add_zero] at heq
  rw [← heq]
  exact hsupp (0, x) h0 (by simpa [Metric.mem_closedBall, dist_zero_right] using hx)

/-- A trajectory vanishing outside the cone `‖x‖ ≤ R + t` has compactly supported initial
velocity: outside `closedBall 0 R` it vanishes on a time interval `[0, δ)`. -/
theorem IsIntegralTrajectoryBefore.hasCompactSupport_initial_velocity {r b L R : ℝ}
    {H : ℝ × ℝ^3 → ℝ} {h : ℝ^3 → ℝ} {u : ℝ × ℝ^3 → ℝ}
    (hu : IsIntegralTrajectoryBefore r b H L u)
    (hvel : ∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0)
    (hsupp : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → R + p.1 < ‖p.2‖ → u p = 0) :
    HasCompactSupport h := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ^3) R) fun x hx ↦ ?_
  have hR : R < ‖x‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have hzero : (fun t ↦ u (t, x)) =ᶠ[𝓝[Ici 0] 0] fun _ ↦ 0 := by
    filter_upwards [Ico_mem_nhdsGE (lt_min hu.time_pos (sub_pos.mpr hR))] with t ht
    exact hsupp (t, x) ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
      (by have := ht.2.trans_le (min_le_right _ _); dsimp only; linarith)
  have h1 : HasDerivWithinAt (fun _ : ℝ ↦ (0 : ℝ)) (h x) (Ici 0) 0 :=
    (hvel x).hasDerivWithinAt.congr_of_eventuallyEq hzero.symm
      (hsupp (0, x) ⟨le_rfl, hu.time_pos⟩ (by dsimp only; linarith)).symm
  exact (uniqueDiffWithinAt_Ici 0).eq_deriv _ h1 (hasDerivWithinAt_const _ _ _)

/-- The tested equation and finite-speed support yield conserved energy
on every proper closed prefix of the C¹ integral trajectory. -/
theorem IsIntegralTrajectoryBefore.hasConservedEnergyOn_of_support {r b L R : ℝ} (hr : 1 ≤ r)
    (hb : 0 < b) {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    {u : ℝ × ℝ^3 → ℝ}
    (hu : IsIntegralTrajectoryBefore r b (cauchyFreeField g h) L u)
    (hvel : ∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0)
    (hsupp : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → R + p.1 < ‖p.2‖ → u p = 0) {S : ℝ} (hS : 0 < S)
    (hSL : S < L) :
    HasConservedEnergyOn r S u := by
  have hhs : HasCompactSupport h := hu.hasCompactSupport_initial_velocity hvel hsupp
  obtain ⟨q, v, F, hq, hv, _, hae, hi, _⟩ :=
    exists_energy_representation_of_signedPower_tested_equation hr hb hS hSL
      hu.regular hhs hvel hsupp (fun ψ hψ hψs t ht ↦ hu.tested_equation hr hb hg hh hψ hψs ht)
  obtain ⟨T, hST, hTL⟩ := exists_between hSL
  obtain ⟨M, hM, hbound⟩ := hu.bounded_before T (hS.trans hST) hTL
  exact ⟨q, v, hq, hv, fun t ht ↦ ⟨(hae t ht).1, (hae t ht).2.1, (hae t ht).2.2.1⟩,
    signedPower_energy_eq_of_bounded_energy_primitives hr hS.le hM hq hv
      (fun t ht x ↦ hbound (t, x) ⟨ht.1, ht.2.trans_lt hST⟩)
      (fun t ht ↦ (hae t ht).1) (fun t ht ↦ (hae t ht).2.2.2) hi⟩

/-- Every real power at least one and arbitrary compact Cauchy data construct
a lifespan with conserved physical energy on all proper closed prefixes. -/
theorem exists_lifespan_with_conserved_energy_of_compact_data {r : ℝ} (hr : 1 ≤ r) {g h : ℝ^3 → ℝ}
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (hgs : HasCompactSupport g)
    (hhs : HasCompactSupport h) :
    ∃ b : ℝ, 0 < b ∧ ∃ u : ℝ × ℝ^3 → ℝ,
      (∀ x : ℝ^3, u (0, x) = g x) ∧
      (∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0) ∧
      ((IsGlobalIntegralTrajectory r b (cauchyFreeField g h) u ∧
        ∀ S : ℝ, 0 < S → HasConservedEnergyOn r S u) ∨
      ∃ L : ℝ, IsIntegralTrajectoryBefore r b (cauchyFreeField g h) L u ∧
        (∀ S : ℝ, 0 < S → S < L → HasConservedEnergyOn r S u) ∧
        ∀ A < L, ∀ M : ℝ, ∃ p : ℝ × ℝ^3,
          p.1 ∈ Ico 0 L ∧ A ≤ p.1 ∧ M < |u p|) := by
  obtain ⟨b, R, hb, _, hglobal | hfinite⟩ :=
    exists_supported_tested_lifespan_of_compact_data hr hg hh hgs hhs
  · obtain ⟨u, hu, hpos, hvel, hsupp, _⟩ := hglobal
    refine ⟨b, hb, u, hpos, hvel, Or.inl ⟨hu, ?_⟩⟩
    intro S hS
    have hbefore : IsIntegralTrajectoryBefore r b (cauchyFreeField g h) (S + 1) u :=
      ⟨by linarith, hu.regular.mono (fun _ hp ↦ hp.1),
        fun T _ _ ↦ hu.bounded_before T, fun p hp ↦ hu.equation p hp.1⟩
    exact hbefore.hasConservedEnergyOn_of_support hr hb hg hh hvel
      (fun p hp ↦ hsupp p hp.1) hS (by linarith)
  · obtain ⟨L, u, hu, hpos, hvel, hsupp, _, hblow⟩ := hfinite
    exact ⟨b, hb, u, hpos, hvel, Or.inr ⟨L, hu,
      fun _ hS hSL ↦ hu.hasConservedEnergyOn_of_support hr hb hg hh hvel hsupp hS hSL, hblow⟩⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
