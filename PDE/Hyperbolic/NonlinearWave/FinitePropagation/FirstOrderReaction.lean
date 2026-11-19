/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.ForwardQuadraticEnergy
import PDE.Analysis.Calculus.SpaceTime.ForwardDerivative
import CAS.ExactTactic

/-!
# Finite propagation for reactions depending on first derivatives

For `uₜₜ - Δu + f(Dₓu, uₜ, u) = 0`, the quadratic cone energy controls all
arguments of `f`. On a fixed cone these arguments range over a compact set,
so a locally Lipschitz reaction has a uniform Lipschitz bound there. The
residual estimate and Grönwall then propagate zero Cauchy data.

The equation is imposed only inside the cone. The initial velocity is the
right derivative, and the conclusion includes the cone boundary and vertex.
This is Theorem 3 of Evans, §12.1.2, with a locally Lipschitz reaction in place of a smooth one;
the uniform Lipschitz bound on the cone replaces Evans's bound
`|f(Du, uₜ, u)| ≤ C (|Du| + |uₜ| + |u|)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.2, Theorem 3 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory PDE.Analysis PDE.Common Set
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- A linear bound in the field and its first derivatives controls the quadratic energy residual. -/
theorem quadraticEnergyBalanceResidual_le_of_waveOperator_bound {u : ℝ^(n + 1) → ℝ} {p : ℝ^(n + 1)}
    {K : ℝ} (hu : ContDiffAt ℝ 2 u p) (hK : 0 ≤ K)
    (hbound : |waveOperator u p| ≤
      K * (|(∂[0] u) p| + ‖classicalWaveSpatialGradient u p‖ + |u p|)) :
    semilinearWaveEnergyBalanceResidual (fun z : ℝ ↦ z ^ 2 / 2) u p ≤
      (1 + 4 * K) * semilinearWaveEnergyDensity (fun z : ℝ ↦ z ^ 2 / 2) u p := by
  have hV : ContDiff ℝ 1 (fun z : ℝ ↦ z ^ 2 / 2) := by fun_prop
  have hd (x : ℝ) : deriv (fun z : ℝ ↦ z ^ 2 / 2) x = x := by cas
  rw [semilinearWaveEnergyBalanceResidual_eq_mul_operator hV hu]
  simp only [semilinearWaveOperator, hd]
  let a := (∂[0] u) p
  let b := ‖classicalWaveSpatialGradient u p‖
  let c := u p
  have hprod : |a| * (|a| + b + |c|) ≤ 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    nlinarith [sq_nonneg (|a| - b), sq_nonneg (|a| - |c|), sq_abs a, sq_abs c,
      sq_nonneg b, sq_nonneg c]
  have hac : |a| * |c| ≤ (a ^ 2 + c ^ 2) / 2 := by
    nlinarith [sq_nonneg (|a| - |c|), sq_abs a, sq_abs c]
  change a * (waveOperator u p + c) ≤ _
  calc
    a * (waveOperator u p + c) ≤ |a * (waveOperator u p + c)| := le_abs_self _
    _ = |a| * |waveOperator u p + c| := abs_mul _ _
    _ ≤ |a| * (|waveOperator u p| + |c|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg a)
    _ ≤ |a| * (K * (|a| + b + |c|) + |c|) :=
      mul_le_mul_of_nonneg_left (by dsimp [a, b, c]; linarith [hbound]) (abs_nonneg a)
    _ = K * (|a| * (|a| + b + |c|)) + |a| * |c| := by ring
    _ ≤ K * (2 * (a ^ 2 + b ^ 2 + c ^ 2)) + (a ^ 2 + c ^ 2) / 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hprod hK) hac
    _ ≤ (1 + 4 * K) * semilinearWaveEnergyDensity (fun z : ℝ ↦ z ^ 2 / 2) u p := by
      unfold semilinearWaveEnergyDensity classicalWaveEnergyDensity
      change K * (2 * (a ^ 2 + b ^ 2 + c ^ 2)) + (a ^ 2 + c ^ 2) / 2 ≤
        (1 + 4 * K) * ((1 / 2 : ℝ) * (a ^ 2 + b ^ 2) + c ^ 2 / 2)
      nlinarith [sq_nonneg b]

/-- A locally Lipschitz first-derivative reaction vanishing at zero preserves zero
Cauchy data throughout the closed backward cone. -/
theorem eq_zero_on_closed_backwardCone_firstOrderReaction [Fact (0 < n)] {f : ℝ^n × ℝ × ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hf : LocallyLipschitz f) (hf0 : f (0, 0, 0) = 0)
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0}) (hu₀ : ContDiffOn ℝ 1 u {p | 0 ≤ p 0}) (c : ℝ^n) {T : ℝ}
    (hT : 0 < T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t), let p := timeSpaceCons t x; waveOperator u
      p + f (classicalWaveSpatialGradient u p, (∂[0] u) p, u p) = 0)
    (hpos : ∀ x ∈ Metric.ball c T, u (timeSpaceCons 0 x) = 0)
    (hvel : ∀ x ∈ Metric.ball c T, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = 0) :
    ∀ t ∈ Icc 0 T, ∀ x ∈ Metric.closedBall c (T - t), u (timeSpaceCons t x) = 0 := by
  let J : ℝ × ℝ^n → ℝ^n × ℝ × ℝ := fun q ↦
    (WithLp.toLp 2 (fun i : Fin n ↦ forwardDifferential u q.1 q.2 (EuclideanSpace.single i.succ 1)),
      forwardDifferential u q.1 q.2 (EuclideanSpace.single 0 1), u (timeSpaceCons (max 0 q.1) q.2))
  have hJ : Continuous J := by
    apply Continuous.prodMk
    · apply (PiLp.continuous_toLp 2 _).comp
      refine continuous_pi fun i ↦ ?_
      exact (continuous_forwardDifferential hu₀).clm_apply continuous_const
    · apply Continuous.prodMk
      · exact (continuous_forwardDifferential hu₀).clm_apply continuous_const
      · apply hu₀.continuousOn.comp_continuous
          ((contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
            ((continuous_const.max continuous_fst).prodMk continuous_snd))
        intro q
        exact le_max_left 0 q.1
  have hJeq (t : ℝ) (ht : 0 < t) (x : ℝ^n) :
      J (t, x) = (classicalWaveSpatialGradient u (timeSpaceCons t x),
        (∂[0] u) (timeSpaceCons t x), u (timeSpaceCons t x)) := by
    dsimp only [J]
    rw [forwardDifferential_eq_fderiv u ht x, max_eq_right ht.le]
    rfl
  let S := insert (0 : ℝ^n × ℝ × ℝ) (J '' (Icc 0 T ×ˢ Metric.closedBall c T))
  have hS : IsCompact S := ((isCompact_Icc.prod (isCompact_closedBall c T)).image hJ).insert _
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hS hf.locallyLipschitzOn
  have hbound (t : ℝ) (ht : t ∈ Ioo 0 T) (x : ℝ^n) (hx : x ∈ Metric.ball c (T - t)) :
      semilinearWaveEnergyBalanceResidual (fun z : ℝ ↦ z ^ 2 / 2) u (timeSpaceCons t x) ≤
        (1 + 4 * (K : ℝ)) * semilinearWaveEnergyDensity (fun z : ℝ ↦ z ^ 2 / 2) u
          (timeSpaceCons t x) := by
    let p := timeSpaceCons t x
    have hp : ContDiffAt ℝ 2 u p :=
      hu.contDiffAt ((isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).mem_nhds
        (show (0 : ℝ) < p 0 by simpa [p] using ht.1))
    apply quadraticEnergyBalanceResidual_le_of_waveOperator_bound hp K.coe_nonneg
    have hx' : x ∈ Metric.closedBall c T := Metric.mem_closedBall.mpr
      ((Metric.mem_ball.mp hx).le.trans (sub_le_self T ht.1.le))
    have hmem : J (t, x) ∈ S := mem_insert_of_mem _
      (mem_image_of_mem J ⟨Ioo_subset_Icc_self ht, hx'⟩)
    have hzero : (0 : ℝ^n × ℝ × ℝ) ∈ S := mem_insert _ _
    have hnorm := hK.dist_le_mul _ hmem _ hzero
    simp only [show f (0 : ℝ^n × ℝ × ℝ) = 0 from hf0,
      dist_zero_right, Real.norm_eq_abs, hJeq t ht.1 x] at hnorm
    have hnormSum : ‖(classicalWaveSpatialGradient u p, (∂[0] u) p, u p)‖ ≤
        |(∂[0] u) p| + ‖classicalWaveSpatialGradient u p‖ + |u p| := by
      simp only [Prod.norm_def, Real.norm_eq_abs]
      have ha := abs_nonneg ((∂[0] u) p)
      have hb := norm_nonneg (classicalWaveSpatialGradient u p)
      have hc := abs_nonneg (u p)
      exact max_le (by linarith) (max_le (by linarith) (by linarith))
    have hsource : |f (classicalWaveSpatialGradient u p, (∂[0] u) p, u p)| ≤
        (K : ℝ) * (|(∂[0] u) p| + ‖classicalWaveSpatialGradient u p‖ + |u p|) :=
      hnorm.trans (mul_le_mul_of_nonneg_left hnormSum K.coe_nonneg)
    have hpde := hwave t ht x hx
    change waveOperator u p + f (classicalWaveSpatialGradient u p, (∂[0] u) p, u p) = 0 at hpde
    rw [eq_neg_of_add_eq_zero_left hpde, abs_neg]
    exact hsource
  refine eq_zero_on_closed_backwardCone_of_energy_eq_zero_forward hu hu₀ c hT hpos fun t ht ↦ ?_
  have he := quadraticConeEnergy_eq_zero_forward hu hu₀ c hT hbound hpos hvel ht
  have hnonneg : 0 ≤ ballIntegral n (fun x ↦ u (timeSpaceCons t x) ^ 2 / 2) c (T - t) :=
    setIntegral_nonneg measurableSet_ball (fun x _ ↦ by positivity)
  unfold semilinearBackwardConeEnergy at he
  have hclassical := backwardConeEnergy_nonneg u c T t
  linarith

end WaveEquation
