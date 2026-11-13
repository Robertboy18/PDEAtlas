/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.GeometricOptics.Residual

/-!
# The squared-eikonal limit of exact wave packets

At a fixed space-time point, an eventually classical family of exact complex wave
solutions satisfies the real amplitude-phase balance. If the amplitude tends to a
nonzero value, the first phase derivatives converge to those of a limiting phase,
and the amplitude wave residual vanishes after scaling by ε², this balance gives
the squared eikonal equation.

The passage is the one from (29) to (31) under the limits (30) in Evans, §4.5.3(a), Example 3,
and the squared equation `p_t² = |Dp|²` is equivalent to (31), `p_t ± |Dp| = 0`. Evans calls
the calculation a formal demonstration; the explicit derivative convergence and scaled
residual hypotheses justify the limit passage.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.5.3(a), Example 3, equations (29)-(31).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE Filter
open scoped Topology

namespace WaveEquation.GeometricOptics

variable {n : ℕ}

/-- Exact complex wave families force the squared eikonal relation in the limit.

The limiting phase has the stated classical derivative. Convergence of the amplitude,
first phase derivatives and the scaled amplitude wave residual are separate hypotheses. -/
theorem squared_eikonal_of_wavePacket_family {a p : ℝ → ℝ^(n + 1) → ℝ} {p₀ : ℝ^(n + 1) → ℝ}
    {z : ℝ^(n + 1)} {a₀ : ℝ} {L : ℝ^(n + 1) →L[ℝ] ℝ} (hp₀ : HasFDerivAt p₀ L z)
    (hregular : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ContDiffAt ℝ 2 (a ε) z ∧ ContDiffAt ℝ 2 (p ε) z)
    (hsolution : ∀ᶠ ε in 𝓝[>] (0 : ℝ), waveOperator (wavePacket ε (a ε) (p ε)) z = 0)
    (ha : Tendsto (fun ε ↦ a ε z) (𝓝[>] (0 : ℝ)) (𝓝 a₀)) (ha₀ : a₀ ≠ 0)
    (hp : ∀ i : Fin (n + 1),
      Tendsto (fun ε ↦ (∂[i] (p ε)) z) (𝓝[>] (0 : ℝ)) (𝓝 (L (EuclideanSpace.single i 1))))
    (hsmall : Tendsto (fun ε ↦ ε ^ 2 * waveOperator (a ε) z) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    (∂[0] p₀) z ^ 2 = ∑ i : Fin n, (∂[i.succ] p₀) z ^ 2 := by
  have hpositive : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hbalance : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      a ε z * eikonalDefect (p ε) z = ε ^ 2 * waveOperator (a ε) z := by
    filter_upwards [hregular, hsolution, hpositive] with ε hreg hsol hpos
    exact ((waveOperator_wavePacket_eq_zero_iff hreg.1 hreg.2 (ne_of_gt hpos)).mp hsol).1
  have hcoordinates (i : Fin (n + 1)) :
      Tendsto (fun ε ↦ (∂[i] (p ε)) z) (𝓝[>] (0 : ℝ)) (𝓝 ((∂[i] p₀) z)) := by
    simpa only [partialDeriv, hp₀.fderiv] using hp i
  have hsum := tendsto_finsetSum (s := Finset.univ)
    (fun (i : Fin n) _ ↦ (hcoordinates i.succ).pow 2)
  have he : Tendsto (fun ε ↦ eikonalDefect (p ε) z) (𝓝[>] (0 : ℝ))
      (𝓝 (eikonalDefect p₀ z)) := by
    simpa only [eikonalDefect] using ((hcoordinates 0).pow 2).sub hsum
  have hzero : Tendsto (fun ε ↦ a ε z * eikonalDefect (p ε) z)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := hsmall.congr' (hbalance.mono fun _ h ↦ h.symm)
  have hcancel : a₀ * eikonalDefect p₀ z = 0 := tendsto_nhds_unique (ha.mul he) hzero
  exact sub_eq_zero.mp ((mul_eq_zero.mp hcancel).resolve_left ha₀)

end WaveEquation.GeometricOptics
