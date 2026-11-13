/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.Amplitude
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.NormBlowup.Classical.Amplitude
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.NormBlowup.Terminal

/-!
# Comparing classical and higher Sobolev wave durations

A C² competitor lasting longer than the constructed higher lifetime
would bound its amplitude up to that lifetime. Classical uniqueness transfers
this bound to the higher trajectory. Tame composition and Grönwall then extend
the higher trajectory, contradicting its proved maximality.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Common Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Hyperbolic.NonlinearWave.Cauchy
open scoped ENNReal NNReal Sobolev

namespace WaveEquation.SmallData.Classical.NormBlowup

/-- Every C² quadratic-wave competitor with the same compact data ends
no later than the constructed higher Sobolev lifetime. -/
theorem classical_duration_le_quadratic_terminalTime
    (H : W^{5,2}(ℝ^3)) {R : ℝ}
    (hs : ∀ x, R < ‖x‖ → classicalRepresentativeCLM (by norm_num) H x = 0)
    (hR : 0 < R)
    (hpositive : 0 < ∫ x, classicalRepresentativeCLM (by norm_num) H x)
    {S : ℝ} {v : ℝ^4 → ℝ}
    (hv : IsSolutionBefore (fun z ↦ -(z ^ 2)) (fun _ ↦ 0)
      (classicalRepresentativeCLM (by norm_num) H) S v) :
    S ≤ (quadraticLifespan H).toReal := by
  by_contra hS
  have hTS : (quadraticLifespan H).toReal < S := lt_of_not_ge hS
  have hf1 : ContDiff ℝ 1 (fun z : ℝ ↦ -(z ^ 2)) :=
    contDiff_neg_sq.of_le (by simp)
  have hf := hf1.locallyLipschitz
  obtain ⟨B, -, hbound⟩ := hv.exists_norm_le_before_of_compact_data hf (by simp)
    (fun _ _ ↦ rfl) hs hTS
  obtain ⟨u, hu, hrep⟩ := exists_classical_quadratic_terminal H hs hpositive
  have hamp : ∀ t ∈ Ico 0 (quadraticLifespan H).toReal, ∀ x,
      ‖classicalRepresentativeCLM (by norm_num) (quadraticTrajectory H t).1 x‖ ≤ B := by
    intro t ht x
    have he := hu.eq_on_overlap hf hv (timeSpaceCons t x)
      (by simpa using And.intro ht.1 (lt_min ht.2 (ht.2.trans hTS)))
    rw [← (hrep t ht x).1, he]
    exact hbound t ⟨ht.1, ht.2.le⟩ x
  have hmild := isMildSolutionBefore_quadraticTrajectory H
    (quadraticLifespan_ne_top H hs hR hpositive)
  obtain ⟨ρ, hρ, V, hV, _⟩ := exists_higherSmooth_extension_of_amplitude
    (by norm_num : (3 : ℝ) < 2 * ((4 : ℝ) - 1)) (by norm_num)
    contDiff_neg_sq (by simp) hmild (quadratic_terminalTime_pos H hs hR hpositive) hamp
  exact not_exists_quadratic_mild_at_terminal H hs hR hpositive ⟨ρ, hρ.le, V, hV⟩

end WaveEquation.SmallData.Classical.NormBlowup
