/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.IntegralLifespanData
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.ClassicalPrefix

/-!
# C² regularity throughout the integral lifespan

Compact C³/C² data supply the finite-slab bound for the free field. Each
proper subinterval of the C¹ lifespan supplies its amplitude bound,
so finite C² persistence applies without a bound at the terminal time.
The scalar exponent is above two.
-/

@[expose] public noncomputable section

open Set PDE.Common WaveEquation
open WaveEquation.SmallData.Classical
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

/-- A finite integral lifespan for compact C³/C² data has C² regularity
at every positive time when the real power exceeds two. The amplitude may
be unbounded at its terminal time. -/
theorem contDiffOn_two_integralTrajectoryBefore {r b L : ℝ} (hr : 2 < r) (hb : 0 < b)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hgs : HasCompactSupport g) (hhs : HasCompactSupport h) {u : ℝ × ℝ^3 → ℝ}
    (hu : IsIntegralTrajectoryBefore r b (cauchyFreeField g h) L u) :
    ContDiffOn ℝ 2 u {p | 0 < p.1 ∧ p.1 < L} := by
  intro p hp
  obtain ⟨S, hpS, hSL⟩ := exists_between hp.2
  have hS : 0 < S := hp.1.trans hpS
  obtain ⟨M, -, huM⟩ := hu.bounded_before S hS hSL
  obtain ⟨B, -, hHB⟩ := exists_bound_cauchyFreeField_of_compact_data
    (hg.of_le (by norm_num)) (hh.of_le (by norm_num)) hgs hhs (S + 1)
  have hH : ContDiff ℝ 2 (cauchyFreeField g h) :=
    (contDiff_two_kirchhoffFormula hg hh).comp (contDiff_timeSpaceCons_uncurry 3)
  have hreg := (exists_c2_extension_of_bounded_signedPower_integral_eq hr hb hS
    (hu.regular.mono (fun _ hq ↦ ⟨hq.1, hq.2.trans hSL⟩)) hH hHB huM
    (fun q hq ↦ hu.equation q ⟨hq.1, hq.2.trans hSL⟩)).2
  exact (hreg.contDiffAt (((isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_fst continuous_const)).mem_nhds ⟨hp.1, hpS⟩)).contDiffWithinAt

/-- A global integral trajectory for compact C³/C² data is C² at all
positive times for every real power above two. Only its finite-slab
amplitude bounds enter the persistence proof. -/
theorem contDiffOn_two_globalIntegralTrajectory {r b : ℝ} (hr : 2 < r) (hb : 0 < b)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hgs : HasCompactSupport g) (hhs : HasCompactSupport h) {u : ℝ × ℝ^3 → ℝ}
    (hu : IsGlobalIntegralTrajectory r b (cauchyFreeField g h) u) :
    ContDiffOn ℝ 2 u {p | 0 < p.1} := by
  intro p hp
  change 0 < p.1 at hp
  have hbnd := hu.before (T := p.1 + 1) (by linarith)
  obtain ⟨B, -, hHB⟩ := exists_bound_cauchyFreeField_of_compact_data
    (hg.of_le (by norm_num)) (hh.of_le (by norm_num)) hgs hhs (p.1 + 1 + 1)
  obtain ⟨M, -, huM⟩ := hbnd.bounded
  have hH : ContDiff ℝ 2 (cauchyFreeField g h) :=
    (contDiff_two_kirchhoffFormula hg hh).comp (contDiff_timeSpaceCons_uncurry 3)
  have hreg := (exists_c2_extension_of_bounded_signedPower_integral_eq hr hb hbnd.time_pos
    hbnd.regular hH hHB huM hbnd.equation).2
  exact (hreg.contDiffAt (((isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_fst continuous_const)).mem_nhds
      ⟨hp, show p.1 < p.1 + 1 by linarith⟩)).contDiffWithinAt

/-- Every proper closed prefix of a finite integral lifespan has a C²
classical representative agreeing with that same trajectory, including time zero. -/
theorem exists_classical_representative_on_integral_prefix {r b L T : ℝ} (hr : 2 < r) (hb : 0 < b)
    (hT : 0 < T) (hTL : T < L) {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hgs : HasCompactSupport g) (hhs : HasCompactSupport h) {u : ℝ × ℝ^3 → ℝ}
    (hu : IsIntegralTrajectoryBefore r b (cauchyFreeField g h) L u) :
    ∃ v : ℝ^4 → ℝ, ContDiff ℝ 2 v ∧ IsSolutionBefore (Real.signedPower r) g h T v ∧ ∀ p : ℝ × ℝ^3,
      p.1 ∈ Icc 0 T → v (timeSpaceCons p.1 p.2) = u p := by
  obtain ⟨S, hTS, hSL⟩ := exists_between hTL
  have hbefore := hu.before (hT.trans hTS) hSL
  obtain ⟨M, -, huM⟩ := hbefore.bounded
  obtain ⟨B, -, hHB⟩ := exists_bound_cauchyFreeField_of_compact_data
    (hg.of_le (by norm_num)) (hh.of_le (by norm_num)) hgs hhs (S + 1)
  exact exists_classical_representative_on_bounded_integral_prefix hr hb hT hTS
    hg hh hbefore.regular hHB huM hbefore.equation

/-- Every finite closed prefix of a global integral trajectory has a C²
classical representative with the nonlinear equation and initial data. -/
theorem exists_classical_representative_on_global_integral_prefix {r b T : ℝ} (hr : 2 < r)
    (hb : 0 < b) (hT : 0 < T) {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hgs : HasCompactSupport g) (hhs : HasCompactSupport h) {u : ℝ × ℝ^3 → ℝ}
    (hu : IsGlobalIntegralTrajectory r b (cauchyFreeField g h) u) :
    ∃ v : ℝ^4 → ℝ, ContDiff ℝ 2 v ∧ IsSolutionBefore (Real.signedPower r) g h T v ∧ ∀ p : ℝ × ℝ^3,
      p.1 ∈ Icc 0 T → v (timeSpaceCons p.1 p.2) = u p := by
  have hbefore := hu.before (T := T + 1) (by linarith)
  obtain ⟨M, -, huM⟩ := hbefore.bounded
  obtain ⟨B, -, hHB⟩ := exists_bound_cauchyFreeField_of_compact_data
    (hg.of_le (by norm_num)) (hh.of_le (by norm_num)) hgs hhs (T + 1 + 1)
  exact exists_classical_representative_on_bounded_integral_prefix hr hb hT
    (by linarith) hg hh hbefore.regular hHB huM hbefore.equation

/-- Arbitrary compact C³/C² data construct an integral lifespan with
C² positive-time regularity for every real exponent above two. Its finite
branch retains the amplitude alternative, rather than assuming global existence. -/
theorem exists_c2_integral_lifespan_of_compact_data {r : ℝ} (hr : 2 < r)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hgs : HasCompactSupport g) (hhs : HasCompactSupport h) :
    ∃ b : ℝ, 0 < b ∧
      ((∃ u : ℝ × ℝ^3 → ℝ, IsGlobalIntegralTrajectory r b (cauchyFreeField g h) u ∧
        ContDiffOn ℝ 2 u {p | 0 < p.1} ∧
        (∀ x : ℝ^3, u (0, x) = g x) ∧
        ∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0) ∨
      ∃ L : ℝ, ∃ u : ℝ × ℝ^3 → ℝ,
        IsIntegralTrajectoryBefore r b (cauchyFreeField g h) L u ∧
        ContDiffOn ℝ 2 u {p | 0 < p.1 ∧ p.1 < L} ∧
        (∀ x : ℝ^3, u (0, x) = g x) ∧
        (∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0) ∧
        ∀ A < L, ∀ M : ℝ, ∃ p : ℝ × ℝ^3,
          p.1 ∈ Ico 0 L ∧ A ≤ p.1 ∧ M < |u p|) := by
  obtain ⟨b, hb, halt⟩ := exists_tested_lifespan_alternative_of_compact_data
    (by linarith : 1 ≤ r) hg hh hgs hhs
  refine ⟨b, hb, ?_⟩
  rcases halt with ⟨u, hu, hug, huh, _⟩ | ⟨L, u, hu, hug, huh, _, hblow⟩
  · exact Or.inl ⟨u, hu, contDiffOn_two_globalIntegralTrajectory hr hb hg hh hgs hhs hu, hug, huh⟩
  · exact Or.inr ⟨L, u, hu, contDiffOn_two_integralTrajectoryBefore hr hb hg hh hgs hhs hu,
      hug, huh, hblow⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower
