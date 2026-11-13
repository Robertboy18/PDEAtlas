/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Lifespan
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.Lifespan
import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.CompactData

/-!
# Global finite classical existence for powers between two and five

Finite C² persistence supplies classical representatives of every proper prefix
of the integral lifespan. The subcritical amplitude estimate,
with one fixed finite horizon, excludes the finite endpoint alternative.
Classical overlap gluing then constructs a global C² field from the arbitrary
compact C³/C² data.
-/

@[expose] public noncomputable section

open Set PDE.Common WaveEquation
open WaveEquation.SmallData.Classical
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

/-- Between powers two and five, compact C³/C² data construct a global integral
trajectory whose original field is C² at positive times. The finite branch is
excluded using the data-dependent classical amplitude bound on its prefixes. -/
theorem exists_global_c2_integral_trajectory_of_compact_data {r : ℝ} (hr : 2 < r) (hr5 : r < 5)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (hgs : HasCompactSupport g)
    (hhs : HasCompactSupport h) :
    ∃ b : ℝ, 0 < b ∧ ∃ u : ℝ × ℝ^3 → ℝ, IsGlobalIntegralTrajectory r b (cauchyFreeField g h) u ∧
      ContDiffOn ℝ 2 u {p | 0 < p.1} ∧ (∀ x : ℝ^3, u (0, x) = g x) ∧ ∀ x : ℝ^3,
      HasDerivAt (fun t ↦ u (t, x)) (h x) 0 := by
  obtain ⟨b, hb, halt⟩ := exists_c2_integral_lifespan_of_compact_data hr hg hh hgs hhs
  rcases halt with hglobal | ⟨L, u, hu, _, _, _, hblow⟩
  · exact ⟨b, hb, hglobal⟩
  exfalso
  obtain ⟨B, _, hbound⟩ := exists_uniform_amplitude_bound_of_compact_data
    (by linarith : 1 < r) hr5 L hg hh hgs hhs
  obtain ⟨p, hp, hpA, hpB⟩ := hblow (L / 2) (by linarith [hu.time_pos]) B
  have hp0 : 0 < p.1 := by linarith [hu.time_pos]
  obtain ⟨S, hpS, hSL⟩ := exists_between hp.2
  have hS : 0 < S := hp0.trans hpS
  obtain ⟨v, hv, hsol, heq⟩ := exists_classical_representative_on_integral_prefix
    hr hb hS hSL hg hh hgs hhs hu
  have hPDE (t : ℝ) (ht : t ∈ Ioo 0 S) (x : ℝ^3) : waveOperator v (timeSpaceCons t x) +
        Real.signedPower r (v (timeSpaceCons t x)) = 0 := by
    have he := hsol.equation (timeSpaceCons t x)
      (by simpa only [timeSpaceCons_zero, Set.mem_Ico] using And.intro ht.1.le ht.2)
    linarith
  have hvB := hbound S v hS hSL.le hv hsol.position hsol.velocity hPDE p.1 ⟨hp0, hpS.le⟩ p.2
  rw [heq p ⟨hp.1, hpS.le⟩] at hvB
  exact (not_lt_of_ge hvB) hpB

/-- Every real power strictly between two and five admits a global C² classical
solution from arbitrary compact C³ displacement and C² velocity. -/
theorem exists_global_classical_signedPower_of_compact_data {r : ℝ} (hr : 2 < r) (hr5 : r < 5)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (hgs : HasCompactSupport g)
    (hhs : HasCompactSupport h) :
    ∃ u : ℝ^4 → ℝ, IsGlobalSolution (Real.signedPower r) g h u := by
  obtain ⟨b, hb, u, hu, _, _, _⟩ :=
    exists_global_c2_integral_trajectory_of_compact_data hr hr5 hg hh hgs hhs
  apply exists_globalSolution_of_unbounded
    ((Real.contDiff_one_signedPower (by linarith : 1 ≤ r)).locallyLipschitz)
  rw [not_bddAbove_iff]
  intro S
  let T := max S 0 + 1
  have hT : 0 < T := by dsimp only [T]; linarith [le_max_right S 0]
  have hST : S < T := by dsimp only [T]; linarith [le_max_left S 0]
  obtain ⟨v, _, hsol, _⟩ := exists_classical_representative_on_global_integral_prefix
    hr hb hT hg hh hgs hhs hu
  exact ⟨T, ⟨v, hsol⟩, hST⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower
