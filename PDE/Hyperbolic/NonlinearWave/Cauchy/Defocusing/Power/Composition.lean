/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.IntermediateExponent
public import PDE.Analysis.MeasureTheory.Lp.SignedPower
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Spaces
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.ContinuousEmbedding
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Global

/-!
# Real power sources on the three-dimensional energy space

For `1 < p ≤ 3`, intermediate Lebesgue membership and the completed H¹ → L⁶
embedding construct the source `|u|^(p-1)u` in L². The closed graph
theorem bounds the inclusion into L^(2p), and the signed-power
difference estimate gives a Lipschitz constant on every H¹ ball.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power

variable {p : ℝ} (hp : 1 < p) (hp3 : p ≤ 3)

include hp hp3

/-- Every H¹ datum belongs to the exact input space for its real-power source. -/
theorem memLp_twice_power (u : H¹(ℝ^3)) :
    MemLp (baseRepresentative u) (ENNReal.ofReal (2 * p)) (domainMeasure 3 univ) := by
  apply MemLp.of_exponent_between (p := 2) (q := 6) (by norm_num)
    (by linarith) (by linarith)
  · simpa only [ENNReal.ofReal_ofNat, baseRepresentative] using Lp.memLp (u.val (baseIndex 3 1))
  · have h := Inequalities.memLp_of_inv_eq (n := 3) (k := 1) (p := 2) (q := 6)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) u
    simpa [baseRepresentative, domainMeasure] using h

/-- The bounded inclusion into L^(2p) retains the Sobolev representative. -/
def powerEmbedding [Fact (1 ≤ ENNReal.ofReal (2 * p))] :
    H¹(ℝ^3) →L[ℝ] DerivLp 3 (ENNReal.ofReal (2 * p)) univ :=
  Inequalities.embeddingCLMOfMemLp (memLp_twice_power hp hp3)

/-- The real defocusing power as an L² element for every energy displacement. -/
def source (u : H¹(ℝ^3)) : DerivLp 3 2 univ := by
  have : Fact (1 ≤ ENNReal.ofReal (2 * p)) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  exact Lp.signedPower hp.le (powerEmbedding hp hp3 u)

/-- The constructed source has exactly the required pointwise power almost everywhere. -/
theorem source_ae (u : H¹(ℝ^3)) :
    source hp hp3 u =ᵐ[domainMeasure 3 univ]
      fun x ↦ Real.signedPower p ((energyTriple 3).inclusion u x) := by
  have : Fact (1 ≤ ENNReal.ofReal (2 * p)) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  exact Lp.coeFn_signedPower hp.le (powerEmbedding hp hp3 u)

/-- Hölder's difference estimate and the bounded inclusion control every energy ball. -/
theorem source_lipschitzOn_closedBall (R : ℝ) (hR : 0 ≤ R) :
    ∃ L : NNReal, LipschitzOnWith L (source hp hp3) (Metric.closedBall 0 R) := by
  have : Fact (1 ≤ ENNReal.ofReal (2 * p)) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  let J := powerEmbedding hp hp3
  let K : ℝ := (2 * p) * (2 * (‖J‖ * R)) ^ (p - 1) * ‖J‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨⟨K, hK⟩, LipschitzOnWith.of_dist_le_mul fun u hu v hv ↦ ?_⟩
  simp only [Metric.mem_closedBall, dist_zero_right] at hu hv
  simp only [dist_eq_norm]
  have huJ : ‖J u‖ ≤ ‖J‖ * R := (J.le_opNorm u).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _))
  have hvJ : ‖J v‖ ≤ ‖J‖ * R := (J.le_opNorm v).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
  have hsum : ‖J u‖ + ‖J v‖ ≤ 2 * (‖J‖ * R) := by linarith
  have hdiff : ‖J u - J v‖ ≤ ‖J‖ * ‖u - v‖ := by
    simpa only [map_sub] using J.le_opNorm (u - v)
  calc
    ‖source hp hp3 u - source hp hp3 v‖ ≤ (2 * p) * (‖J u‖ + ‖J v‖) ^ (p - 1) * ‖J u - J v‖ :=
      Lp.norm_signedPower_sub_le hp (J u) (J v)
    _ ≤ (2 * p) * (2 * (‖J‖ * R)) ^ (p - 1) * (‖J‖ * ‖u - v‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hsum (by linarith)) (by positivity))
        hdiff (norm_nonneg _) (by positivity)
    _ = K * ‖u - v‖ := by dsimp [K]; ring

/-- The power source is locally Lipschitz on the entire energy displacement space. -/
theorem locallyLipschitz_source : LocallyLipschitz (source hp hp3) := by
  intro u
  obtain ⟨L, hL⟩ := source_lipschitzOn_closedBall hp hp3 (‖u‖ + 1) (by positivity)
  refine ⟨L, Metric.closedBall 0 (‖u‖ + 1), ?_, hL⟩
  apply Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds ?_) Metric.ball_subset_closedBall
  simpa only [Metric.mem_ball, dist_zero_right] using lt_add_one ‖u‖

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power
