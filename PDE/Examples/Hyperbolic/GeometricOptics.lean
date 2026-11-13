/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.GeometricOptics.Limit
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Wave packets and the geometric-optics limit

At `ε = 0` the wave packet `wavePacket ε a p` is the amplitude `a`. Affine null phases
`t + s x` with `s² = 1` and constant amplitude give exact solutions of the wave equation
for every `ε ≠ 0` (`constant_amplitude_null_phase`), and they satisfy the hypotheses of
the limit theorem `squared_eikonal_of_wavePacket_family`. With the transverse quadratic
amplitude `y²` and phase `t - x`, the eikonal and transport terms vanish, but the wave
residual has norm `2` for every `ε` (`transverse_quadratic_residual`).
-/

@[expose] public noncomputable section

open PDE WaveEquation WaveEquation.GeometricOptics Filter
open scoped Topology

namespace PDE.Examples.GeometricOptics

variable {n : ℕ} {a p : ℝ^(n + 1) → ℝ} {z : ℝ^(n + 1)}

/-- At parameter zero the packet is the real amplitude included in the complex numbers. -/
example : wavePacket 0 a p = fun y ↦ (a y : ℂ) := by
  funext y
  simp [wavePacket, PDE.Analysis.osc]

/-- For `s² = 1` and `ε ≠ 0`, the packet with amplitude `1` and phase `t + s x` solves the
wave equation. -/
theorem constant_amplitude_null_phase (s : ℝ) (hs : s ^ 2 = 1)
    {ε : ℝ} (hε : ε ≠ 0) (z : ℝ^2) :
    waveOperator (wavePacket ε (fun _ ↦ 1) (fun y : ℝ^2 ↦ y 0 + s * y 1)) z = 0 := by
  have hp : ContDiff ℝ 2 (fun y : ℝ^2 ↦ y 0 + s * y 1) := by fun_prop
  have ht (y : ℝ^2) : (∂[0] (fun x : ℝ^2 ↦ x 0 + s * x 1)) y = 1 := by
    cas
  have hx (y : ℝ^2) : (∂[1] (fun x : ℝ^2 ↦ x 0 + s * x 1)) y = s := by
    cas
  have htt (y : ℝ^2) :
      (∂[0] (fun x ↦ (∂[0] (fun v : ℝ^2 ↦ v 0 + s * v 1)) x)) y = 0 := by
    cas
  have hxx (y : ℝ^2) :
      (∂[1] (fun x ↦ (∂[1] (fun v : ℝ^2 ↦ v 0 + s * v 1)) x)) y = 0 := by
    cas
  have he : eikonalDefect (fun y : ℝ^2 ↦ y 0 + s * y 1) z = 0 := by
    simp [eikonalDefect, ht, hx, hs]
  have hw : waveOperator (fun y : ℝ^2 ↦ y 0 + s * y 1) z = 0 := by
    simp [waveOperator, htt, hxx]
  apply (waveOperator_wavePacket_eq_zero_iff contDiffAt_const hp.contDiffAt hε).mpr
  constructor
  · simp [he]
  · simp [transportTerm, hw]

/-- The limit theorem recovers the eikonal equation for the affine null phase. -/
example (s : ℝ) (hs : s ^ 2 = 1) (z : ℝ^2) :
    (∂[0] (fun y : ℝ^2 ↦ y 0 + s * y 1)) z ^ 2 =
      ∑ i : Fin 1, (∂[i.succ] (fun y : ℝ^2 ↦ y 0 + s * y 1)) z ^ 2 := by
  have hp : ContDiff ℝ 2 (fun y : ℝ^2 ↦ y 0 + s * y 1) := by fun_prop
  have hp₀ := (hp.differentiable (by norm_num) z).hasFDerivAt
  apply squared_eikonal_of_wavePacket_family
    (a := fun _ _ ↦ 1) (p := fun _ y ↦ y 0 + s * y 1) hp₀
  · exact Eventually.of_forall fun _ ↦ ⟨contDiffAt_const, hp.contDiffAt⟩
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact constant_amplitude_null_phase s hs (ne_of_gt hε) z
  · exact tendsto_const_nhds
  · norm_num
  · intro i
    exact tendsto_const_nhds
  · simp

/-- With amplitude `y²` and phase `t - x`, the wave residual is `-2 osc ε⁻¹ (t - x)`. -/
theorem transverse_quadratic_residual (ε : ℝ) (z : ℝ^3) :
    waveOperator (wavePacket ε (fun y : ℝ^3 ↦ y 2 ^ 2)
      (fun y : ℝ^3 ↦ y 0 - y 1)) z =
        -2 * PDE.Analysis.osc ε⁻¹ (z 0 - z 1) := by
  have ha : ContDiff ℝ 2 (fun y : ℝ^3 ↦ y 2 ^ 2) := by fun_prop
  have hp : ContDiff ℝ 2 (fun y : ℝ^3 ↦ y 0 - y 1) := by fun_prop
  have pt (y : ℝ^3) : (∂[0] (fun x : ℝ^3 ↦ x 0 - x 1)) y = 1 := by cas
  have px (y : ℝ^3) : (∂[1] (fun x : ℝ^3 ↦ x 0 - x 1)) y = -1 := by cas
  have py (y : ℝ^3) : (∂[2] (fun x : ℝ^3 ↦ x 0 - x 1)) y = 0 := by cas
  have hat (y : ℝ^3) : (∂[0] (fun x : ℝ^3 ↦ x 2 ^ 2)) y = 0 := by cas
  have ax (y : ℝ^3) : (∂[1] (fun x : ℝ^3 ↦ x 2 ^ 2)) y = 0 := by cas
  have ptt (y : ℝ^3) :
      (∂[0] (fun x ↦ (∂[0] (fun v : ℝ^3 ↦ v 0 - v 1)) x)) y = 0 := by cas
  have pxx (y : ℝ^3) :
      (∂[1] (fun x ↦ (∂[1] (fun v : ℝ^3 ↦ v 0 - v 1)) x)) y = 0 := by cas
  have pyy (y : ℝ^3) :
      (∂[2] (fun x ↦ (∂[2] (fun v : ℝ^3 ↦ v 0 - v 1)) x)) y = 0 := by cas
  have att (y : ℝ^3) :
      (∂[0] (fun x ↦ (∂[0] (fun v : ℝ^3 ↦ v 2 ^ 2)) x)) y = 0 := by cas
  have axx (y : ℝ^3) :
      (∂[1] (fun x ↦ (∂[1] (fun v : ℝ^3 ↦ v 2 ^ 2)) x)) y = 0 := by cas
  have ayy (y : ℝ^3) :
      (∂[2] (fun x ↦ (∂[2] (fun v : ℝ^3 ↦ v 2 ^ 2)) x)) y = 2 := by cas
  have he : eikonalDefect (fun y : ℝ^3 ↦ y 0 - y 1) z = 0 := by
    simp [eikonalDefect, Fin.sum_univ_two, pt, px, py]
  have hwp : waveOperator (fun y : ℝ^3 ↦ y 0 - y 1) z = 0 := by
    simp [waveOperator, Fin.sum_univ_two, ptt, pxx, pyy]
  have hwa : waveOperator (fun y : ℝ^3 ↦ y 2 ^ 2) z = -2 := by
    simp [waveOperator, Fin.sum_univ_two, att, axx, ayy]
  have htransport : transportTerm (fun y : ℝ^3 ↦ y 2 ^ 2)
      (fun y : ℝ^3 ↦ y 0 - y 1) z = 0 := by
    simp [transportTerm, Fin.sum_univ_two, hwp, pt, px, py, hat, ax]
  rw [waveOperator_wavePacket_frequency ha.contDiffAt hp.contDiffAt, he, htransport, hwa]
  simp [mul_comm]

/-- The residual has norm `2` at every point. -/
theorem norm_transverse_quadratic_residual (ε : ℝ) (z : ℝ^3) :
    ‖waveOperator (wavePacket ε (fun y : ℝ^3 ↦ y 2 ^ 2)
      (fun y : ℝ^3 ↦ y 0 - y 1)) z‖ = 2 := by
  rw [transverse_quadratic_residual, norm_mul, PDE.Analysis.norm_osc_eq_one]
  norm_num

/-- The residual does not tend to zero as `ε → 0⁺`. -/
theorem transverse_quadratic_residual_not_tendsto_zero (z : ℝ^3) :
    ¬ Tendsto (fun ε ↦ waveOperator (wavePacket ε (fun y : ℝ^3 ↦ y 2 ^ 2)
      (fun y : ℝ^3 ↦ y 0 - y 1)) z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  intro h
  have hnorm : Tendsto (fun _ : ℝ ↦ (2 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [norm_transverse_quadratic_residual, norm_zero] using h.norm
  have hfalse : (2 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hnorm
  norm_num at hfalse

/-- `ε² □a` tends to zero as `ε → 0⁺`. -/
theorem tendsto_scaled_transverse_quadratic_amplitude_residual (z : ℝ^3) :
    Tendsto (fun ε ↦ ε ^ 2 * waveOperator (fun y : ℝ^3 ↦ y 2 ^ 2) z)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hε : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  simpa using (hε.pow 2).mul_const (waveOperator (fun y : ℝ^3 ↦ y 2 ^ 2) z)

/-- The transverse unit point has amplitude one and residual negative two for every ε. -/
example (ε : ℝ) :
    (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) 2 ^ 2 = 1 ∧
      waveOperator (wavePacket ε (fun y : ℝ^3 ↦ y 2 ^ 2)
        (fun y : ℝ^3 ↦ y 0 - y 1)) (EuclideanSpace.single 2 1) = -2 := by
  constructor
  · norm_num
  · simpa [PDE.Analysis.osc] using
      transverse_quadratic_residual ε (EuclideanSpace.single 2 1)

end PDE.Examples.GeometricOptics
