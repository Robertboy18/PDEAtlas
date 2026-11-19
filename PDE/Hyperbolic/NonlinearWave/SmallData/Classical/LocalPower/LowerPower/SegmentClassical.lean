/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import
  PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.LowerPower.SegmentSolution
public import
  PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.LowerPower.SegmentFormula
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# A constructed classical solution of the weighted one-dimensional equation

The C¹ cone solution supplies a C¹ source. The characteristic integral gains
the missing derivative in one space dimension, so the solution is C²
and satisfies the pointwise equation. No second derivative of the scalar
reaction is required, including at its zeros.
-/

@[expose] public noncomputable section

open Set MeasureTheory BoundedContinuousFunction PDE.Common
open PDE (partialDeriv)
open scoped unitInterval

namespace WaveEquation.SmallData.Classical.LocalPower.LowerPower

/-- Bounded C¹ coefficient and velocity construct a jointly C² solution of
`w_tt - w_rr = a(r) f(w)` on a positive time interval. Both ordinary Cauchy
traces and finite propagation are conclusions of the construction. -/
theorem exists_classical_weighted_segment {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0)
    (h a : ℝ →ᵇ ℝ) (hh : ContDiff ℝ 1 h) (ha : ContDiff ℝ 1 a) :
    ∃ T : ℝ, 0 < T ∧ ∃ w : ℝ^2 → ℝ,
      ContDiff ℝ 2 w ∧
      (∀ q : ℝ^2, q 0 ∈ Ico 0 T →
        waveOperator w q = a (q 1) * f (w q)) ∧
      (∀ r : ℝ, w (timeSpaceCons 0 (EuclideanSpace.single (0 : Fin 1) r)) = 0) ∧
      (∀ r : ℝ, HasDerivAt
        (fun t ↦ w (timeSpaceCons t (EuclideanSpace.single (0 : Fin 1) r))) (h r) 0) ∧
      ∀ q : ℝ^2, q 0 ∈ Ico 0 T →
        (∀ y : ℝ, |y - q 1| ≤ q 0 → h y = 0) → w q = 0 := by
  obtain ⟨T, hT, v, hv, heq, hzero⟩ := exists_segment_solution hf hf0 h a hh ha
  let b : ContDiffBump (0 : ℝ) := ⟨T / 4, T / 2, by positivity, by linarith⟩
  let c : ℝ → ℝ := fun t ↦ t * b t
  have hc : ContDiff ℝ 1 c := contDiff_id.mul b.contDiff
  have hbound (t : ℝ) : |c t| < T := by
    by_cases ht : |t| < T / 2
    · rw [show c t = t * b t from rfl, abs_mul, abs_of_nonneg b.nonneg]
      linarith [mul_le_of_le_one_right (abs_nonneg t) (b.le_one (x := t))]
    · have hb : b t = 0 := b.zero_of_le_dist (by
        simpa only [b, dist_zero_right, Real.norm_eq_abs] using le_of_not_gt ht)
      simpa only [c, hb, mul_zero, abs_zero] using hT
  let V : ℝ × ℝ → ℝ := fun p ↦ v (c p.1, p.2)
  have hV : ContDiff ℝ 1 V :=
    hv.comp_contDiff ((hc.comp contDiff_fst).prodMk contDiff_snd) (fun p ↦ hbound p.1)
  have hVe {p : ℝ × ℝ} (hp : |p.1| < T / 4) : V p = v p := by
    have hb : b p.1 = 1 := b.one_of_mem_closedBall (by
      simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, b] using hp.le)
    simp only [V, c, hb, mul_one]
  let F : ℝ^2 → ℝ := fun q ↦ a (q 1) * f (V (q 0, q 1))
  have hF : ContDiff ℝ 1 F := (ha.comp (EuclideanSpace.proj (1 : Fin 2)).contDiff).mul
      (hf.comp (hV.comp ((EuclideanSpace.proj (0 : Fin 2)).contDiff.prodMk
        (EuclideanSpace.proj (1 : Fin 2)).contDiff)))
  let H := dAlembertSolution1D (fun _ ↦ 0) (fun x : ℝ^1 ↦ h (x 0))
  have hH : ContDiff ℝ 2 H :=
    contDiff_two_dAlembertSolution1D _ _ contDiff_const (by simpa using hh)
  let w : ℝ^2 → ℝ := fun q ↦ H q + dAlembertDuhamelSolution F q
  have hD := contDiff_two_dAlembertDuhamelSolution hF.contDiffOn
  have hw : ContDiff ℝ 2 w := hH.add hD
  have hwv {q : ℝ^2} (hq : q 0 ∈ Ico 0 (T / 4)) :
      w q = v (q 0, q 1) := by
    have ht : |q 0| < T := by rw [abs_of_nonneg hq.1]; linarith [hq.2]
    rw [heq (q 0, q 1) ht]
    change H q + dAlembertDuhamelSolution F q = _
    have hfree : H q =
        q 0 * ∫ b : I, h (q 1 + q 0 * (2 * (b : ℝ) - 1)) := by
      simpa [H, dAlembertSolution1D] using dAlembertFormula_zero_eq_segment h (q 1) (q 0)
    rw [hfree, dAlembertDuhamelSolution_eq_segment F hq.1]
    congr 3 with s
    congr 2 with z
    have hs0 := mul_nonneg hq.1 s.2.1
    have hsle : q 0 * (s : ℝ) ≤ q 0 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left s.2.2 hq.1
    have hs : q 0 * (s : ℝ) < T / 4 := hsle.trans_lt hq.2
    change a (q 1 + q 0 * ((1 - (s : ℝ)) * (2 * (z : ℝ) - 1))) *
      f (V (q 0 * (s : ℝ), q 1 + q 0 * ((1 - (s : ℝ)) * (2 * (z : ℝ) - 1)))) = _
    rw [hVe (by simpa only [abs_of_nonneg hs0] using hs)]
  refine ⟨T / 4, by positivity, w, hw, ?_, ?_, ?_, ?_⟩
  · intro q hq
    rw [waveOperator_add hH.contDiffAt hD.contDiffAt]
    have hhom : waveOperator H q = 0 :=
      waveOperator_dAlembertFormula _ _ contDiff_const (by simpa using hh) q
    rw [hhom, zero_add, waveOperator_dAlembertDuhamelSolution hF.contDiffOn hq.1]
    change a (q 1) * f (V (q 0, q 1)) = _
    rw [hVe (by simpa only [abs_of_nonneg hq.1] using hq.2), hwv hq]
  · intro r
    change H _ + dAlembertDuhamelSolution F _ = 0
    rw [dAlembertDuhamelSolution_initial, add_zero]
    exact dAlembert_satisfies_initial_pos _ _ _
  · intro r
    let x : ℝ^1 := EuclideanSpace.single 0 r
    have ht : ContDiff ℝ 2 (fun t ↦ w (timeSpaceCons t x)) :=
      hw.comp ((contDiff_timeSpaceCons_uncurry 1).comp (contDiff_id.prodMk contDiff_const))
    have hd := (ht.differentiable (by norm_num) 0).hasDerivAt
    have hv0 : deriv (fun t ↦ w (timeSpaceCons t x)) 0 = h r := by
      rw [← PDE.partialDeriv_timeSpaceCons_eq_deriv w x 0 (hw.differentiable (by norm_num) _)]
      change (∂[0] (fun q ↦ H q + dAlembertDuhamelSolution F q)) _ = _
      rw [PDE.partialDeriv_add (hH.differentiable (by norm_num) _)
        (hD.differentiable (by norm_num) _),
        partialDeriv_dAlembertDuhamelSolution_initial hF.contDiffOn, add_zero]
      exact dAlembert_satisfies_initial_vel _ _ contDiff_const (by simpa using hh) x
    rwa [hv0] at hd
  · intro q hq hz
    rw [hwv hq]
    exact hzero (q 0, q 1) (by rw [abs_of_nonneg hq.1]; linarith [hq.2])
      (by simpa only [abs_of_nonneg hq.1] using hz)

end WaveEquation.SmallData.Classical.LocalPower.LowerPower
