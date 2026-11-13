/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.ReactionDiffusion.Turing.Spectrum
public import PDE.FDeriv.Calculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Classical cosine modes of the linear reaction-diffusion PDE

Time is coordinate `0` and space is coordinate `1`. An eigenvector `v` of `A - k² D` with eigenvalue
`λ` gives a classical solution `X(t,x) = α exp(λt) cos(kx) v` of the system `IsSolution`
(`cosineMode_isSolution`). The time and spatial derivatives are Fréchet coordinate derivatives;
SymLean's `cas` tactic computes them for `cosineMode` and checks the two equations. We also prove
the initial uniform bound (`cosineMode_initial_abs_le`), growth at the origin
(`cosineMode_abs_tendsto_atTop`), and homogeneous Neumann conditions on the interval `[0, π/k]` when
`k ≠ 0` (`cosineMode_neumann`).

These are solutions of the linear system; for a nonlinear reaction term they are solutions of its
linearization. The mode is the analogue of one term `s_j(t) w_j(x)` of Evans's expansion (23) in
§4.1.2, with `cos(kx)` and `k²` in place of a Dirichlet eigenfunction `w_j` and its eigenvalue, so
that `s_j(t) = α exp(λt) v` solves (24)-(25).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.1.2 (Application: Turing instability), (22)-(25),
  pp. 172-173.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace ReactionDiffusion.Turing

open Filter
open scoped Topology ContDiff

/-- A classical solution of the two-species linear reaction-diffusion system. -/
structure IsSolution (C : Coefficients) (u v : ℝ^2 → ℝ) : Prop where
  regularity₁ : ContDiff ℝ 2 u
  regularity₂ : ContDiff ℝ 2 v
  equation₁ : ∀ p, (∂[(0 : Fin 2)] u) p =
    C.diffusion₁ * (∂[(1 : Fin 2)] (∂[(1 : Fin 2)] u)) p + C.a * u p + C.b * v p
  equation₂ : ∀ p, (∂[(0 : Fin 2)] v) p =
    C.diffusion₂ * (∂[(1 : Fin 2)] (∂[(1 : Fin 2)] v)) p + C.c * u p + C.d * v p

/-- One scalar component of a real Fourier mode. -/
def cosineMode (rate frequency amplitude : ℝ) (p : ℝ^2) : ℝ :=
  amplitude * Real.exp (rate * p 0) * Real.cos (frequency * p 1)

/-- The explicit mode is jointly smooth in space and time. -/
theorem contDiff_cosineMode (rate frequency amplitude : ℝ) :
    ContDiff ℝ ∞ (cosineMode rate frequency amplitude) := by
  unfold cosineMode
  fun_prop

/-- Time derivative of the cosine mode. -/
theorem cosineMode_time_derivative (rate frequency amplitude : ℝ) (p : ℝ^2) :
    (∂[(0 : Fin 2)] (cosineMode rate frequency amplitude)) p =
      rate * cosineMode rate frequency amplitude p := by
  unfold cosineMode
  cas

/-- Spatial derivative of the cosine mode. -/
theorem cosineMode_space_derivative (rate frequency amplitude : ℝ) (p : ℝ^2) :
    (∂[(1 : Fin 2)] (cosineMode rate frequency amplitude)) p =
      -(frequency * amplitude * Real.exp (rate * p 0) * Real.sin (frequency * p 1)) := by
  unfold cosineMode
  cas

/-- Spatial Laplacian in one dimension. -/
theorem cosineMode_second_space_derivative (rate frequency amplitude : ℝ) (p : ℝ^2) :
    (∂[(1 : Fin 2)] (∂[(1 : Fin 2)] (cosineMode rate frequency amplitude))) p =
      -(frequency ^ 2) * cosineMode rate frequency amplitude p := by
  rw [show (∂[(1 : Fin 2)] (cosineMode rate frequency amplitude)) =
      (fun q ↦ -(frequency * amplitude * Real.exp (rate * q 0) *
        Real.sin (frequency * q 1))) from funext (cosineMode_space_derivative _ _ _)]
  unfold cosineMode
  cas

/-- A mode eigenvector gives a classical PDE solution at every amplitude scale. -/
theorem cosineMode_isSolution (C : Coefficients) (rate frequency scale : ℝ)
    {vector : Fin 2 → ℝ}
    (hvector : Module.End.HasEigenvector (C.modeMatrix (frequency ^ 2)).toLin' rate vector) :
    IsSolution C (cosineMode rate frequency (scale * vector 0))
      (cosineMode rate frequency (scale * vector 1)) := by
  have h₀ := congrFun hvector.apply_eq_smul 0
  have h₁ := congrFun hvector.apply_eq_smul 1
  simp only [Matrix.toLin'_apply, Coefficients.modeMatrix, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at h₀ h₁
  change (C.a - C.diffusion₁ * frequency ^ 2) * vector 0 + C.b * vector 1 =
    rate * vector 0 at h₀
  change C.c * vector 0 + (C.d - C.diffusion₂ * frequency ^ 2) * vector 1 =
    rate * vector 1 at h₁
  refine ⟨(contDiff_cosineMode _ _ _).of_le (by norm_num),
    (contDiff_cosineMode _ _ _).of_le (by norm_num), ?_, ?_⟩
  · intro p
    rw [cosineMode_time_derivative, cosineMode_second_space_derivative]
    unfold cosineMode
    cas using h₀
  · intro p
    rw [cosineMode_time_derivative, cosineMode_second_space_derivative]
    unfold cosineMode
    cas using h₁

/-- The initial scalar mode is uniformly bounded by its amplitude. -/
theorem cosineMode_initial_abs_le (rate frequency amplitude x : ℝ) :
    |cosineMode rate frequency amplitude !₂[0, x]| ≤ |amplitude| := by
  simpa [cosineMode, abs_mul] using
    mul_le_of_le_one_right (abs_nonneg amplitude) (Real.abs_cos_le_one (frequency * x))

/-- A positive rate and a nonzero amplitude give unbounded growth at the origin. -/
theorem cosineMode_abs_tendsto_atTop {rate amplitude : ℝ}
    (hrate : 0 < rate) (hamplitude : amplitude ≠ 0) (frequency : ℝ) :
    Tendsto (fun t ↦ |cosineMode rate frequency amplitude !₂[t, 0]|) atTop atTop := by
  have hexp := Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hrate)
  simpa [cosineMode, abs_mul, abs_of_pos (Real.exp_pos _)] using
    hexp.const_mul_atTop (abs_pos.mpr hamplitude)

/-- A nonzero wave number gives zero normal derivatives at both ends of a
Neumann interval of length `π/k`. Positivity of `k` makes this length positive. -/
theorem cosineMode_neumann {frequency : ℝ} (hfrequency : frequency ≠ 0)
    (rate amplitude t : ℝ) :
    (∂[(1 : Fin 2)] (cosineMode rate frequency amplitude)) !₂[t, 0] = 0 ∧
      (∂[(1 : Fin 2)] (cosineMode rate frequency amplitude))
        !₂[t, Real.pi / frequency] = 0 := by
  have hphase : frequency * (Real.pi / frequency) = Real.pi := mul_div_cancel₀ _ hfrequency
  simp [cosineMode_space_derivative, hphase]

/-- A nonzero frequency and amplitude produce a spatially nonconstant initial state. -/
theorem cosineMode_initial_nonconstant {frequency amplitude : ℝ}
    (hfrequency : frequency ≠ 0) (hamplitude : amplitude ≠ 0) (rate : ℝ) :
    cosineMode rate frequency amplitude !₂[0, 0] ≠
      cosineMode rate frequency amplitude !₂[0, Real.pi / frequency] := by
  have hphase : frequency * (Real.pi / frequency) = Real.pi := mul_div_cancel₀ _ hfrequency
  have hne : amplitude ≠ -amplitude := fun h ↦ hamplitude (by linarith)
  simpa [cosineMode, hphase] using hne

end ReactionDiffusion.Turing
