/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Generation.Approximation
public import PDE.Analysis.Evolution.Semigroup.Generation.Exponential

/-!
# The strong limit of the Yosida semigroups

The resolvent hypotheses construct bounded Yosida generators and their exponential
contraction semigroups. The comparison estimate and density prove that their orbits
are uniformly Cauchy on bounded time intervals, for every initial vector.

These are steps 4 and 5 of the proof of Evans §7.4.2, Theorem 4, up to the limit (21).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.4.2, proof of Theorem 4, steps 4-5, (21), p. 440.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Set Topology

namespace PDE.Analysis.Evolution.HasContractionResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {A : E →ₗ.[ℝ] E} (hA : HasContractionResolvent A)
  {lambda mu : ℝ}

/-- The exponential semigroup of the bounded Yosida approximation. -/
def yosidaSemigroup (hlambda : 0 < lambda) : StronglyContinuousSemigroup E :=
  StronglyContinuousSemigroup.exponential (hA.yosidaApproximation hlambda)

/-- The constructed Yosida semigroups are contractions. -/
theorem yosidaSemigroup_isContraction (hlambda : 0 < lambda) :
    (hA.yosidaSemigroup hlambda).IsContraction :=
  StronglyContinuousSemigroup.exponential_isContraction_of_norm_le_one
    (lambda • hA.resolvent hlambda) (hA.norm_smul_resolvent_le hlambda) hlambda.le

/-- The difference of two approximate orbits is bounded by the difference of their generators,
`‖S_λ(t)x - S_μ(t)x‖ ≤ t ‖A_λx - A_μx‖`. -/
theorem norm_yosidaSemigroup_sub_le (hlambda : 0 < lambda) (hmu : 0 < mu)
    (t : NNReal) (x : E) :
    ‖hA.yosidaSemigroup hlambda t x - hA.yosidaSemigroup hmu t x‖ ≤
      (t : ℝ) * ‖hA.yosidaApproximation hlambda x - hA.yosidaApproximation hmu x‖ :=
  StronglyContinuousSemigroup.norm_exponential_sub_le _ _
    (hA.yosidaApproximation_commute hlambda hmu)
    (hA.yosidaSemigroup_isContraction hlambda)
    (hA.yosidaSemigroup_isContraction hmu) t x

/-- Approximate orbits starting in the operator domain are uniformly Cauchy on bounded times. -/
theorem uniformCauchySeqOn_yosidaSemigroup_domain (hdense : Dense (A.domain : Set E))
    (x : A.domain) (T : NNReal) :
    UniformCauchySeqOn (fun lambda : Ioi (0 : ℝ) ↦
      fun t : NNReal ↦ hA.yosidaSemigroup lambda.property t x) atTop (Icc 0 T) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp
    (hA.tendsto_yosidaApproximation hdense x).cauchySeq
    (ε / ((T : ℝ) + 1)) (div_pos hε (by positivity))
  refine ⟨N, fun lambda hlambda mu hmu t ht ↦ ?_⟩
  rw [dist_eq_norm]
  calc
    ‖hA.yosidaSemigroup lambda.property t x - hA.yosidaSemigroup mu.property t x‖ ≤
        (t : ℝ) * ‖hA.yosidaApproximation lambda.property x -
          hA.yosidaApproximation mu.property x‖ :=
      hA.norm_yosidaSemigroup_sub_le lambda.property mu.property t x
    _ ≤ (T : ℝ) * ‖hA.yosidaApproximation lambda.property x -
          hA.yosidaApproximation mu.property x‖ :=
      mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr ht.2) (norm_nonneg _)
    _ < ε := by
      have h := hN lambda hlambda mu hmu
      rw [dist_eq_norm, lt_div_iff₀ (show 0 < (T : ℝ) + 1 by positivity)] at h
      nlinarith [norm_nonneg (hA.yosidaApproximation lambda.property x -
        hA.yosidaApproximation mu.property x)]

/-- Density extends the uniformly Cauchy estimate to every initial vector. -/
theorem uniformCauchySeqOn_yosidaSemigroup (hdense : Dense (A.domain : Set E))
    (x : E) (T : NNReal) :
    UniformCauchySeqOn (fun lambda : Ioi (0 : ℝ) ↦
      fun t : NNReal ↦ hA.yosidaSemigroup lambda.property t x) atTop (Icc 0 T) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := hdense.exists_dist_lt x (show 0 < ε / 3 by positivity)
  obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp
    (hA.uniformCauchySeqOn_yosidaSemigroup_domain hdense ⟨y, hy⟩ T)
    (ε / 3) (by positivity)
  refine ⟨N, fun lambda hlambda mu hmu t ht ↦ ?_⟩
  have hleft := (hA.yosidaSemigroup_isContraction lambda.property).dist_apply_le t x y
  have hright := (hA.yosidaSemigroup_isContraction mu.property).dist_apply_le t y x
  have hmiddle := hN lambda hlambda mu hmu t ht
  have htriangle := dist_triangle4
    (hA.yosidaSemigroup lambda.property t x) (hA.yosidaSemigroup lambda.property t y)
    (hA.yosidaSemigroup mu.property t y) (hA.yosidaSemigroup mu.property t x)
  rw [dist_comm y x] at hright
  linarith

/-- The strong orbit limit, constructed from the Yosida semigroups. -/
def limitOrbit (x : E) (t : NNReal) : E :=
  atTop.limUnder (fun lambda : Ioi (0 : ℝ) ↦ hA.yosidaSemigroup lambda.property t x)

/-- Every Yosida orbit converges strongly to the constructed limit. -/
theorem tendsto_yosidaSemigroup (hdense : Dense (A.domain : Set E)) (x : E) (t : NNReal) :
    Tendsto (fun lambda : Ioi (0 : ℝ) ↦ hA.yosidaSemigroup lambda.property t x)
      atTop (𝓝 (hA.limitOrbit x t)) :=
  ((hA.uniformCauchySeqOn_yosidaSemigroup hdense x t).cauchySeq
    ⟨zero_le, le_rfl⟩).tendsto_limUnder

/-- The convergence to the constructed orbit is uniform on every bounded time interval. -/
theorem tendstoUniformlyOn_yosidaSemigroup (hdense : Dense (A.domain : Set E))
    (x : E) (T : NNReal) :
    TendstoUniformlyOn (fun lambda : Ioi (0 : ℝ) ↦
      fun t : NNReal ↦ hA.yosidaSemigroup lambda.property t x)
      (hA.limitOrbit x) atTop (Icc 0 T) :=
  (hA.uniformCauchySeqOn_yosidaSemigroup hdense x T).tendstoUniformlyOn_of_tendsto
    (fun t _ ↦ hA.tendsto_yosidaSemigroup hdense x t)

end PDE.Analysis.Evolution.HasContractionResolvent
