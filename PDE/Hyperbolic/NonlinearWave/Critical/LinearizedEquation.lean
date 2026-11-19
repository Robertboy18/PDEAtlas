/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Calculus.SpaceTime
import PDE.Analysis.Calculus.LocalExtension.TimeBand
import PDE.Hyperbolic.Classical.ForwardLocalization
import PDE.FDeriv.Calculus

/-!
# The differentiated quintic wave equation on an open time band

Each first derivative of a C³ quintic wave satisfies its linearized equation. A local representative
permits commutation of the derivatives without regularity at either endpoint of the time band.

This is the equation `□v + 5u⁴v = 0` for `v = u_{x_k}`, derived in step 2 of the proof of Evans,
§12.4, Theorem 3, and used again in step 4 for `v = u_{x_k}` and `v = u_t`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 3, steps 2 and 4 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter PDE PDE.Common
open scoped ENNReal Topology

namespace WaveEquation.Critical

/-- Each coordinate derivative satisfies the linearized quintic equation
on an open time band. -/
theorem waveOperator_partialDeriv_quintic_on_band {u : ℝ^4 → ℝ} {s₀ T : ℝ}
    (hu : ContDiffOn ℝ 3 u {p | s₀ < p 0 ∧ p 0 < T})
    (hw : ∀ p, s₀ < p 0 → p 0 < T → waveOperator u p + u p ^ 5 = 0) (i : Fin 4) {p : ℝ^4}
    (hp : s₀ < p 0 ∧ p 0 < T) :
    waveOperator (∂[i] u) p = -(5 * u p ^ 4 * (∂[i] u) p) := by
  obtain ⟨g, hg, heq⟩ := ContDiffOn.exists_contDiff_eventuallyEq_on_band
    (k := 3) (f := u) (s := p 0) (τ := p 0)
    (EuclideanSpace.proj 0 : ℝ^4 →L[ℝ] ℝ) (by simpa using hu) hp.1 hp.2
  have he : u =ᶠ[𝓝 p] g := heq p (by simp)
  have hopen : IsOpen {q : ℝ^4 | s₀ < q 0 ∧ q 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hres : waveOperator g =ᶠ[𝓝 p] fun q ↦ -(g q ^ 5) := by
    filter_upwards [he.eventuallyEq_nhds, hopen.mem_nhds hp] with q hq hband
    have hwq := hw q hband.1 hband.2
    rw [waveOperator_congr_nhds hq, hq.eq_of_nhds] at hwq
    exact eq_neg_of_add_eq_zero_left hwq
  rw [waveOperator_congr_nhds (he.partialDeriv i),
    waveOperator_partialDeriv (by simpa using hg), partialDeriv_congr_nhds i hres]
  have hd : DifferentiableAt ℝ g p := hg.differentiable (by norm_num) p
  have hpow : (∂[i] (fun q ↦ -(g q ^ 5))) p =
      -(5 * g p ^ 4 * (∂[i] g) p) := by
    unfold partialDeriv
    rw [fderiv_fun_neg, fderiv_fun_pow 5 hd]
    simp [smul_eq_mul, mul_assoc]
  rw [hpow, he.eq_of_nhds, partialDeriv_congr_nhds i he]

end WaveEquation.Critical
