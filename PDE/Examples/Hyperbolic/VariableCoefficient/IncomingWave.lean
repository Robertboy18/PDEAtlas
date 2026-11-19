/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Hyperbolic.VariableCoefficient.IncomingData
public import PDE.Examples.Hyperbolic.VariableCoefficient.OpticalRadius
public import PDE.Hyperbolic.Classical.VariableCoefficient.OpticalConjugation
public import PDE.Hyperbolic.Models.Wave.Kirchhoff.CoordinateLine
public import PDE.Hyperbolic.Models.Wave.Kirchhoff.ExponentialData
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A wave entering from spatial infinity

The coefficient `(1 + x²)²` puts infinity at finite optical distance. Pulling
back a Kirchhoff potential through `arctan` gives a smooth wave with zero
initial displacement and velocity which becomes positive at the origin.

The wave satisfies the smooth nondivergence equation `u_tt = (1 + x²)² u_xx`, whose
coefficient is at least one. The closed optical sublevel at `π / 2` is all of `ℝ`, and
the wave shows that finite propagation fails among smooth classical solutions on an
unbounded domain without compact optical sublevels
(`not_finite_propagation_of_lower_ellipticity`).
-/

@[expose] public noncomputable section

open PDE PDE.Analysis PDE.Common WaveEquation
open scoped ContDiff

namespace PDE.Examples.VariableCoefficient

/-- The incoming wave in physical space, with time first. -/
def incomingWave (t x : ℝ) : ℝ :=
  Real.sqrt (1 + x ^ 2) * kirchhoffLine incomingData 0 0 t (Real.arctan x)

/-- The explicit wave is smooth jointly in physical space and time. -/
theorem contDiff_incomingWave :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ incomingWave p.1 p.2) := by
  apply contDiff_infty.mpr
  intro k
  have hs : ContDiff ℝ k (fun p : ℝ × ℝ ↦ Real.sqrt (1 + p.2 ^ 2)) := by
    exact (contDiff_const.add (contDiff_snd.pow 2)).sqrt (by intro p; positivity)
  have hl := contDiff_kirchhoffLine (k := k) contDiff_incomingData 0 0
  exact hs.mul (hl.comp (contDiff_fst.prodMk (Real.contDiff_arctan.comp contDiff_snd)))

/-- `Δ incomingData = ∂₀² incomingData + incomingData`, the Klein–Gordon term removed by
the optical conjugation. -/
theorem laplacian_incomingData (x : ℝ^3) :
    laplacian incomingData x = (∂[0] (∂[0] incomingData)) x + incomingData x := by
  have hh : ContDiff ℝ 1 (fun s : ℝ ↦ expNegInvGlue (s - 2)) :=
    expNegInvGlue.contDiff.comp (contDiff_id.sub contDiff_const)
  exact congrFun (laplacian_exp_mul_comp_zero (hh.differentiable one_ne_zero)) x

/-- The wave satisfies `u_tt = (1 + x²)² u_xx` at every positive time. -/
theorem incomingWave_equation {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (deriv (fun s ↦ incomingWave s x)) t -
        OpticalRadius.coefficient x * deriv (deriv (incomingWave t)) x = 0 := by
  have hl : ContDiff ℝ 2 (kirchhoffLine incomingData 0 0 t) :=
    (contDiff_kirchhoffLine (k := 2) contDiff_incomingData 0 0).comp
      (contDiff_const.prodMk contDiff_id)
  exact OpticalConjugation.wave_residual_sqrt_comp_arctan_eq_zero
    (kirchhoffLine incomingData 0 0) t x (hl.differentiable (by norm_num))
    (hl.deriv'.differentiable one_ne_zero _) (kleinGordon_kirchhoffLine
      contDiff_incomingData 0 laplacian_incomingData 0 (Real.arctan x) ht)

/-- Every physical point has zero initial displacement. -/
@[simp]
theorem incomingWave_initial (x : ℝ) : incomingWave 0 x = 0 := by
  simp [incomingWave]

/-- Every physical point also has zero initial velocity: the optical interval
lies entirely inside the zero region of the prescribed data. -/
theorem deriv_incomingWave_initial (x : ℝ) :
    deriv (fun t ↦ incomingWave t x) 0 = 0 := by
  unfold incomingWave
  rw [deriv_const_mul_field, deriv_kirchhoffLine_initial contDiff_incomingData]
  have hx : Real.arctan x ≤ 2 := by
    have h := Real.arctan_lt_pi_div_two x
    linarith [Real.pi_lt_four]
  rw [incomingData_eq_zero (by simpa using hx), mul_zero]

/-- At time three, the incoming wave is strictly positive at the origin. -/
theorem incomingWave_pos : 0 < incomingWave 3 0 := by
  simpa [incomingWave, kirchhoffLine, coordinateLine] using
    kirchhoffPotential_incomingData_pos

/-- There is a smooth nonzero solution of `u_tt = (1 + x²)² u_xx` with zero initial data,
so smoothness and the lower ellipticity bound do not give uniqueness. -/
theorem exists_nonzero_smooth_wave_with_zero_initial_data :
    ∃ u : ℝ × ℝ → ℝ,
      ContDiff ℝ ∞ u ∧
      (∀ t, 0 < t → ∀ x,
        deriv (deriv (fun s ↦ u (s, x))) t -
          OpticalRadius.coefficient x * deriv (deriv (fun y ↦ u (t, y))) x = 0) ∧
      (∀ x, u (0, x) = 0 ∧ deriv (fun t ↦ u (t, x)) 0 = 0) ∧
      0 < u (3, 0) :=
  ⟨fun p ↦ incomingWave p.1 p.2, contDiff_incomingWave,
    fun _ ht x ↦ incomingWave_equation ht x,
    fun x ↦ ⟨incomingWave_initial x, deriv_incomingWave_initial x⟩,
    incomingWave_pos⟩

/-- Smooth coefficients, lower ellipticity and a smooth eikonal radius away from the
center do not suffice for finite propagation among all smooth classical solutions.
The equation is imposed on the whole positive-time half-space, and the initial data
are required to vanish only on the open optical base. -/
theorem not_finite_propagation_of_lower_ellipticity :
    ¬ (∀ (a q : ℝ → ℝ) (c T : ℝ) (u : ℝ × ℝ → ℝ),
      ContDiff ℝ ∞ a →
      (∃ θ : ℝ, 0 < θ ∧ ∀ x, θ ≤ a x) →
      Continuous q → q c = 0 →
      (∀ x, x ≠ c → 0 < q x) →
      (∀ x, x ≠ c → ContDiffAt ℝ ∞ q x) →
      (∀ x, x ≠ c → a x * deriv q x ^ 2 = 1) →
      0 < T → ContDiff ℝ ∞ u →
      (∀ t, 0 < t → ∀ x,
        deriv (deriv (fun s ↦ u (s, x))) t -
          a x * deriv (deriv (fun y ↦ u (t, y))) x = 0) →
      (∀ x, q x < T → u (0, x) = 0) →
      (∀ x, q x < T → deriv (fun t ↦ u (t, x)) 0 = 0) →
      ∀ t ∈ Set.Ico 0 T, ∀ x, q x < T - t → u (t, x) = 0) := by
  intro hprop
  obtain ⟨u, hu, hwave, hdata, hpos⟩ :=
    exists_nonzero_smooth_wave_with_zero_initial_data
  have hvanishes := hprop OpticalRadius.coefficient OpticalRadius.radius 0 4 u
    OpticalRadius.contDiff_coefficient
    ⟨1, zero_lt_one, OpticalRadius.one_le_coefficient⟩
    OpticalRadius.continuous_radius OpticalRadius.radius_zero
    (fun _ hx ↦ OpticalRadius.radius_pos hx)
    (fun _ hx ↦ OpticalRadius.contDiffAt_radius hx)
    (fun _ hx ↦ OpticalRadius.coefficient_mul_deriv_radius_sq hx)
    (by norm_num) hu hwave (fun x _ ↦ (hdata x).1) (fun x _ ↦ (hdata x).2)
  have hzero : u (3, 0) = 0 := hvanishes 3 (by constructor <;> norm_num) 0 (by
    rw [OpticalRadius.radius_zero]
    norm_num)
  exact (ne_of_gt hpos) hzero

end PDE.Examples.VariableCoefficient
