/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Critical.DerivativeLinearEstimate
import PDE.Hyperbolic.NonlinearWave.Critical.ForwardEnergy
import PDE.Analysis.Calculus.SpaceTime.SchwartzData

/-!
# Uniform cone derivative estimates for the quintic Cauchy problem

Compact initial data and the PDE give finite propagation. Each positive restart then has Schwartz
data for every first derivative. Cone Sobolev control yields the derivative estimate with one
coefficient before all centers, directions and starts.

The estimate is the L⁶ part of the estimate (4) of Evans, §12.4, Theorem 1, on backward cones, for
the derivatives `v = u_{x_k}` and `v = u_t`, which satisfy `□v + 5u⁴v = 0`. Step 4 of the proof
of Theorem 3 uses it, through the method of step 2, to control the solution near a possible
singularity.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 1, equation (4), and step 1 of its proof;
  Theorem 3, steps 2 and 4 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform Filter Set Metric PDE PDE.Common
open scoped ENNReal SchwartzMap

open PDE.Analysis
open scoped ContDiff

namespace WaveEquation.Critical

/-- Smooth compact Cauchy data supply the cone derivative input with one
coefficient before all centers, coordinate directions and positive starts. -/
theorem exists_uniform_cone_derivative_estimate_of_quintic_cauchy {u : ℝ^4 → ℝ} {T : ℝ} (hT : 0 < T)
    (g h : ℝ^3 → ℝ) (hu : ContDiffOn ℝ ∞ u {p | 0 ≤ p 0 ∧ p 0 < T}) (hgc : HasCompactSupport g)
    (hhc : HasCompactSupport h)
    (hwave : ∀ q ∈ Ioo 0 T, ∀ x : ℝ^3,
      waveOperator u (timeSpaceCons q x) + u (timeSpaceCons q x) ^ 5 = 0)
    (hpos : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hvel : ∀ x, HasDerivWithinAt (fun t ↦ u (timeSpaceCons t x)) (h x) (Ici 0) 0) :
    ∃ L : ℝ, 0 ≤ L ∧
    ∀ c : ℝ^3, ∀ i : Fin 4, ∀ s ∈ Ioo 0 T, ∃ A : ℝ, ∀ r ∈ Ico s T,
      lpNorm (fun x ↦ (∂[i] u) (timeSpaceCons r x)) 6
        (volume.restrict (ball c (T - r))) ≤
      A + L * ∫ q in Icc s r,
        lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 4 * (∂[i] u) (timeSpaceCons q x)) 2
          (volume.restrict (ball c (T - q))) := by
  obtain ⟨R, _, hsupport, _⟩ := exists_support_and_uniform_energy_of_quintic_cauchy
    hT g h (hu.of_le (by simp)) hgc hhc hwave hpos hvel
  have hui : ContDiffOn ℝ ∞ u {p | 0 < p 0 ∧ p 0 < T} := hu.mono fun _ hp ↦ ⟨hp.1.le, hp.2⟩
  have hsupp : ∀ q ∈ Ioo 0 T, ∀ x : ℝ^3, R + q < ‖x‖ → u (timeSpaceCons q x) = 0 :=
    fun q hq ↦ hsupport q ⟨hq.1.le, hq.2⟩
  let S : ℝ := (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^3)) 2 : ℝ) * 3
  refine ⟨S * 5, by positivity, fun c i s hs ↦ ?_⟩
  obtain ⟨gₛ, hₛ, hgs, hhs⟩ :=
    exists_schwartz_partialDeriv_cauchyData_of_forward_support hui hsupp hs i
  refine ⟨S * (‖(Strichartz.initialEnergyDatum (gₛ.postcompCLM Complex.ofRealCLM)
    (hₛ.postcompCLM Complex.ofRealCLM)).fst‖ +
    ‖(Strichartz.initialEnergyDatum (gₛ.postcompCLM Complex.ofRealCLM)
      (hₛ.postcompCLM Complex.ofRealCLM)).snd‖), ?_⟩
  intro r hr
  have he := lpNorm_partialDeriv_cone_le_of_forward_support hui hsupp hwave
    hs hr (A := T) le_rfl c i gₛ hₛ hgs hhs
  simpa only [S, mul_add, mul_assoc] using he

end WaveEquation.Critical
