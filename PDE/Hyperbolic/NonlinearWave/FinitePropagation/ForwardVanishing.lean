/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.QuadraticLowerBound
import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.ClassicalExtension
import PDE.Hyperbolic.Classical.ForwardLocalization

/-!
# Forward finite propagation for a nonnegative C¹ potential

A C² extension from the closed forward half-space transfers the energy-based
vanishing theorem to the original field. The potential needs only C¹ regularity. The Cauchy data are
prescribed on the open base ball using the right velocity, and the conclusion includes the lateral
boundary and vertex.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.2, Theorem 2(ii).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set PDE.Common PDE.Analysis

namespace WaveEquation

variable {n : ℕ}

/-- Evans, §12.1.2, Theorem 2(ii), for a C¹ nonnegative potential and a
field that is C² on the closed forward half-space. Zero open-ball Cauchy data
force vanishing on the closed cone, with velocity given by the right derivative. -/
theorem eq_zero_on_closed_cone_of_contDiffOn_forward_semilinear [Fact (0 < n)] {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hV : ContDiff ℝ 1 V) (hVnonneg : ∀ z, 0 ≤ V z) (hVzero : V 0 = 0)
    (hu : ContDiffOn ℝ 2 u {p | 0 ≤ p 0}) (c : ℝ^n) {T : ℝ} (hT : 0 < T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t),
      semilinearWaveOperator V u (timeSpaceCons t x) = 0)
    (hpos : ∀ x ∈ Metric.ball c T, u (timeSpaceCons 0 x) = 0)
    (hvel : ∀ x ∈ Metric.ball c T, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = 0) :
    ∀ t ∈ Icc 0 T, ∀ x ∈ Metric.closedBall c (T - t), u (timeSpaceCons t x) = 0 := by
  obtain ⟨U, hU, heq⟩ := exists_contDiff_extension_halfSpace 0 2 hu
  have hwaveU (t : ℝ) (ht : t ∈ Ioo 0 T) (x : ℝ^n) (hx : x ∈ Metric.ball c (T - t)) :
      semilinearWaveOperator V U (timeSpaceCons t x) = 0 := by
    have hgerm := eventuallyEq_of_eqOn_forward heq
      (show 0 < (timeSpaceCons t x) 0 by simpa only [timeSpaceCons_zero] using ht.1)
    unfold semilinearWaveOperator
    rw [waveOperator_congr_nhds hgerm, hgerm.eq_of_nhds]
    exact hwave t ht x hx
  have hwaveClosed (t : ℝ) (ht : t ∈ Ico 0 T) (x : ℝ^n) (hx : x ∈ Metric.ball c (T - t)) :
      semilinearWaveOperator V U (timeSpaceCons t x) = 0 := by
    have hx' : dist x c < T - t := Metric.mem_ball.mp hx
    have hε : 0 < T - dist x c := by linarith [ht.1]
    exact waveOperator_add_eq_zero_of_mem_Icc hV.continuous_deriv_one hU hε
      (fun r hr ↦ hwaveU r ⟨hr.1, by linarith [hr.2, dist_nonneg (x := x) (y := c)]⟩ x
        (Metric.mem_ball.mpr (by linarith [hr.2]))) ⟨ht.1, by linarith⟩
  have hposU (x : ℝ^n) (hx : x ∈ Metric.ball c (T - 0)) :
      U (timeSpaceCons 0 x) = 0 := by
    rw [heq (by simp)]
    exact hpos x (by simpa using hx)
  have hvelU (x : ℝ^n) (hx : x ∈ Metric.ball c (T - 0)) :
      (∂[0] U) (timeSpaceCons 0 x) = 0 := by
    have hd := forwardDifferential_initial_eq_zero (hu.of_le (by norm_num))
      Metric.isOpen_ball hpos hvel (by simpa using hx)
    rw [forwardDifferential_eq_fderiv_of_extension hU heq le_rfl] at hd
    change fderiv ℝ U (timeSpaceCons 0 x) (EuclideanSpace.single 0 1) = 0
    rw [hd]
    rfl
  have hvanish := eq_zero_on_closed_backwardCone_semilinear_of_open_ball
    hV hVnonneg hVzero hU c hT hwaveClosed hposU hvelU
  intro t ht x hx
  rw [← heq (by simpa only [Set.mem_ofPred_eq, timeSpaceCons_zero] using ht.1)]
  exact hvanish t ht x hx

end WaveEquation
