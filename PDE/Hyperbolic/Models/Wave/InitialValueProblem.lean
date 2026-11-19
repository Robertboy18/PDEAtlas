/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Operator
import PDE.Hyperbolic.Models.Wave.Equation
import PDE.FDeriv.SpaceTime

/-!
# Initial-value problems for the wave equation

The homogeneous and forced wave residuals with assigned Cauchy data: the
problems

`u_tt - Δu = 0` (or `= f`) in `ℝ^n × (0, ∞)`, `u = g`, `u_t = h` on `ℝ^n × {t = 0}`

of Evans, §2.4, with unit propagation speed; the homogeneous problem is (11). Because Lean's
derivative operators are total, satisfying these `PDEProblem`s does not imply
classical regularity. The superposition lemmas therefore assume regularity
where derivative linearity needs it.

The homogeneous problem is the zero-source case of the forced one. For classical
fields the positive-time residual extends continuously to the initial slice.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1, equation (11); §2.4.2, equation (39).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv PDEEquation PDEProblem SatisfiesPDEProblem)

namespace WaveEquation

open Filter PDE.Common Set
open scoped Topology

variable {n : ℕ}

/-- Residual-and-assigned-data form of the forced wave Cauchy equations.

It records `u_tt - Δu = f` at positive time and the equalities
`u(0,x)=g(x)` and `u_t(0,x)=h(x)`. Regularity, trace convergence,
existence, and uniqueness are supplied separately. -/
noncomputable def forcedWaveResidualAssignedCauchyDataProblem
    (f : ℝ^(n + 1) → ℝ)
    (g h : ℝ^n → ℝ) :
    PDEProblem (ℝ^(n + 1)) ℝ :=
  { eqns := [
      { Output := ℝ
        operator := fun u x ↦ waveOperator u x
        rhs := f
        domain := {x : ℝ^(n + 1) | x 0 > 0}
      }
    ],
    sideConditions := [
      { Output := ℝ
        operator := fun u x ↦ u x
        rhs := fun x ↦ g (spatialPartCLM n x)
        domain := {x : ℝ^(n + 1) | x 0 = 0}
      },
      { Output := ℝ
        operator := fun u x ↦ (∂[0] u) x
        rhs := fun x ↦ h (spatialPartCLM n x)
        domain := {x : ℝ^(n + 1) | x 0 = 0}
      }
    ]
  }

/-- Projection from the forced problem to the positive-time residual
`u_tt - Δu = f`. -/
theorem forcedWaveResidualAssignedCauchyDataProblem.residual_eq {f : ℝ^(n + 1) → ℝ} {g h : ℝ^n → ℝ}
    {u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := n) f g h) u)
    {x : ℝ^(n + 1)} (hx : x 0 > 0) :
    waveOperator (n := n) u x = f x := by
  let eqn : PDEEquation (ℝ^(n + 1)) ℝ :=
    { Output := ℝ
      operator := fun u x ↦ waveOperator (n := n) u x
      rhs := f
      domain := {x : ℝ^(n + 1) | x 0 > 0} }
  have heqn : eqn ∈ (forcedWaveResidualAssignedCauchyDataProblem (n := n) f g h).eqns := by
    simp [eqn, forcedWaveResidualAssignedCauchyDataProblem]
  have hres := PDE.SatisfiesPDEProblem.eqn
      (pde := forcedWaveResidualAssignedCauchyDataProblem (n := n) f g h) (u := u) hu heqn hx
  simpa [eqn] using hres

/-- Projection from the forced problem to the assigned position equality. -/
theorem forcedWaveResidualAssignedCauchyDataProblem.initial_position_eq {f : ℝ^(n + 1) → ℝ}
    {g h : ℝ^n → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := n) f g h) u)
    {x : ℝ^(n + 1)} (hx : x 0 = 0) :
    u x = g (spatialPartCLM n x) := by
  let eqn : PDEEquation (ℝ^(n + 1)) ℝ :=
    { Output := ℝ
      operator := fun u x ↦ u x
      rhs := fun x ↦ g (spatialPartCLM n x)
      domain := {x : ℝ^(n + 1) | x 0 = 0} }
  have heqn : eqn ∈
        (forcedWaveResidualAssignedCauchyDataProblem (n := n) f g h).sideConditions := by
    simp [eqn, forcedWaveResidualAssignedCauchyDataProblem]
  have hpos := PDE.SatisfiesPDEProblem.side_condition
      (pde := forcedWaveResidualAssignedCauchyDataProblem (n := n) f g h) (u := u) hu heqn hx
  simpa [eqn] using hpos

/-- Projection from the forced problem to the assigned velocity equality. -/
theorem forcedWaveResidualAssignedCauchyDataProblem.initial_velocity_eq {f : ℝ^(n + 1) → ℝ}
    {g h : ℝ^n → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := n) f g h) u)
    {x : ℝ^(n + 1)} (hx : x 0 = 0) :
    (∂[0] u) x = h (spatialPartCLM n x) := by
  let eqn : PDEEquation (ℝ^(n + 1)) ℝ :=
    { Output := ℝ
      operator := fun u x ↦ (∂[0] u) x
      rhs := fun x ↦ h (spatialPartCLM n x)
      domain := {x : ℝ^(n + 1) | x 0 = 0} }
  have heqn : eqn ∈
        (forcedWaveResidualAssignedCauchyDataProblem (n := n) f g h).sideConditions := by
    simp [eqn, forcedWaveResidualAssignedCauchyDataProblem]
  have hvel := PDE.SatisfiesPDEProblem.side_condition
      (pde := forcedWaveResidualAssignedCauchyDataProblem (n := n) f g h) (u := u) hu heqn hx
  simpa [eqn] using hvel

/-- Constructor for the forced problem from its three clauses. -/
theorem forcedWaveResidualAssignedCauchyDataProblem.of_residual_initial {f : ℝ^(n + 1) → ℝ}
    {g h : ℝ^n → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hres : ∀ x : ℝ^(n + 1), x 0 > 0 → waveOperator (n := n) u x = f x)
    (hpos : ∀ x : ℝ^(n + 1), x 0 = 0 → u x = g (spatialPartCLM n x))
    (hvel : ∀ x : ℝ^(n + 1), x 0 = 0 → (∂[0] u) x = h (spatialPartCLM n x)) :
    SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := n) f g h) u := by
  refine PDE.SatisfiesPDEProblem.mk ?_ ?_
  · intro eqn heqn x hx
    simp only [forcedWaveResidualAssignedCauchyDataProblem, List.mem_singleton] at heqn
    subst heqn
    simpa using hres x hx
  · intro eqn heqn x hx
    simp only [
      forcedWaveResidualAssignedCauchyDataProblem, List.mem_cons, List.not_mem_nil, or_false
    ] at heqn
    rcases heqn with heqn | heqn
    · subst heqn
      simpa using hpos x hx
    · subst heqn
      simpa using hvel x hx

/-- The forced problem is exactly its residual and two assigned-data clauses. -/
theorem forcedWaveResidualAssignedCauchyDataProblem_iff {f : ℝ^(n + 1) → ℝ} {g h : ℝ^n → ℝ}
    {u : ℝ^(n + 1) → ℝ} :
    SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := n) f g h) u ↔
      (∀ x : ℝ^(n + 1), x 0 > 0 →
        waveOperator (n := n) u x = f x) ∧
        (∀ x : ℝ^(n + 1), x 0 = 0 →
          u x = g (spatialPartCLM n x)) ∧
          (∀ x : ℝ^(n + 1), x 0 = 0 →
            (∂[0] u) x = h (spatialPartCLM n x)) := by
  constructor
  · exact fun hu ↦ ⟨fun x hx ↦
      forcedWaveResidualAssignedCauchyDataProblem.residual_eq (n := n) hu hx,
      fun x hx ↦ forcedWaveResidualAssignedCauchyDataProblem.initial_position_eq (n := n) hu hx,
      fun x hx ↦ forcedWaveResidualAssignedCauchyDataProblem.initial_velocity_eq (n := n) hu hx⟩
  · exact fun hclauses ↦ forcedWaveResidualAssignedCauchyDataProblem.of_residual_initial
      (n := n) hclauses.1 hclauses.2.1 hclauses.2.2

/-- Closure under addition for the forced residual-and-assigned-data problem.

The source and both assigned data functions add pointwise. -/
theorem forcedWaveResidualAssignedCauchyDataProblem_add {f q : ℝ^(n + 1) → ℝ}
    {g₁ g₂ h₁ h₂ : ℝ^n → ℝ} {u v : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := n) f g₁ h₁) u)
    (hv : SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := n) q g₂ h₂) v)
    (hcu : ContDiff ℝ 2 u) (hcv : ContDiff ℝ 2 v) :
    SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := n) (fun x ↦ f x + q x)
      (fun x ↦ g₁ x + g₂ x) (fun x ↦ h₁ x + h₂ x)) (fun x ↦ u x + v x) := by
  refine forcedWaveResidualAssignedCauchyDataProblem.of_residual_initial (n := n) ?hres ?hpos ?hvel
  · intro x hx
    rw [waveOperator_add (n := n) hcu.contDiffAt hcv.contDiffAt]
    have hu_res := forcedWaveResidualAssignedCauchyDataProblem.residual_eq (n := n) hu hx
    have hv_res := forcedWaveResidualAssignedCauchyDataProblem.residual_eq (n := n) hv hx
    linarith
  · intro x hx
    have hu_pos := forcedWaveResidualAssignedCauchyDataProblem.initial_position_eq (n := n) hu hx
    have hv_pos := forcedWaveResidualAssignedCauchyDataProblem.initial_position_eq (n := n) hv hx
    simp [hu_pos, hv_pos]
  · intro x hx
    have htime : (∂[0] (fun y ↦ u y + v y)) x = (∂[0] u) x + (∂[0] v) x :=
      PDE.partialDeriv_add (n := n + 1) (i := 0) (f := u) (g := v) (x := x)
        ((hcu.differentiable (by norm_num)).differentiableAt)
        ((hcv.differentiable (by norm_num)).differentiableAt)
    have hu_vel := forcedWaveResidualAssignedCauchyDataProblem.initial_velocity_eq (n := n) hu hx
    have hv_vel := forcedWaveResidualAssignedCauchyDataProblem.initial_velocity_eq (n := n) hv hx
    rw [htime, hu_vel, hv_vel]

/-- Closure under scalar multiplication for the forced problem. -/
theorem forcedWaveResidualAssignedCauchyDataProblem_const_mul (c : ℝ) {f : ℝ^(n + 1) → ℝ}
    {g h : ℝ^n → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := n) f g h) u) :
    SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := n) (fun x ↦ c * f x)
      (fun x ↦ c * g x) (fun x ↦ c * h x)) (fun x ↦ c * u x) := by
  refine forcedWaveResidualAssignedCauchyDataProblem.of_residual_initial (n := n) ?hres ?hpos ?hvel
  · intro x hx
    rw [waveOperator_const_mul (n := n) c u x]
    have hu_res := forcedWaveResidualAssignedCauchyDataProblem.residual_eq (n := n) hu hx
    rw [hu_res]
  · intro x hx
    have hu_pos := forcedWaveResidualAssignedCauchyDataProblem.initial_position_eq (n := n) hu hx
    simp [hu_pos]
  · intro x hx
    have htime : (∂[0] (fun y ↦ c * u y)) x =
          c * (∂[0] u) x := by
      unfold partialDeriv
      change fderiv ℝ (c • u) x _ = _
      rw [fderiv_const_smul_field]
      rfl
    have hu_vel := forcedWaveResidualAssignedCauchyDataProblem.initial_velocity_eq (n := n) hu hx
    rw [htime, hu_vel]

/-- Closure under linear combinations for the forced problem. -/
theorem forcedWaveResidualAssignedCauchyDataProblem_linear_combination (c₁ c₂ : ℝ)
    {f q : ℝ^(n + 1) → ℝ} {g₁ g₂ h₁ h₂ : ℝ^n → ℝ} {u v : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := n) f g₁ h₁) u)
    (hv : SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := n) q g₂ h₂) v)
    (hcu : ContDiff ℝ 2 u) (hcv : ContDiff ℝ 2 v) :
    SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := n)
      (fun x ↦ c₁ * f x + c₂ * q x) (fun x ↦ c₁ * g₁ x + c₂ * g₂ x) (fun x ↦ c₁ * h₁ x + c₂ * h₂ x))
      (fun x ↦ c₁ * u x + c₂ * v x) := by
  have hcu_sol := forcedWaveResidualAssignedCauchyDataProblem_const_mul (n := n) c₁ hu
  have hcv_sol := forcedWaveResidualAssignedCauchyDataProblem_const_mul (n := n) c₂ hv
  exact forcedWaveResidualAssignedCauchyDataProblem_add (n := n) hcu_sol hcv_sol
    (hcu.const_smul c₁) (hcv.const_smul c₂)

/-- Closure under negation for the forced problem. -/
theorem forcedWaveResidualAssignedCauchyDataProblem_neg {f : ℝ^(n + 1) → ℝ} {g h : ℝ^n → ℝ}
    {u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := n) f g h) u) :
    SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := n) (fun x ↦ -f x)
      (fun x ↦ -g x) (fun x ↦ -h x)) (fun x ↦ -u x) := by
  simpa only [one_mul, neg_mul, sub_eq_add_neg] using
    forcedWaveResidualAssignedCauchyDataProblem_const_mul (n := n) (-1 : ℝ) hu

/-- Closure under subtraction for the forced problem. -/
theorem forcedWaveResidualAssignedCauchyDataProblem_sub {f q : ℝ^(n + 1) → ℝ}
    {g₁ g₂ h₁ h₂ : ℝ^n → ℝ} {u v : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := n) f g₁ h₁) u)
    (hv : SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := n) q g₂ h₂) v)
    (hcu : ContDiff ℝ 2 u) (hcv : ContDiff ℝ 2 v) :
    SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := n) (fun x ↦ f x - q x)
      (fun x ↦ g₁ x - g₂ x) (fun x ↦ h₁ x - h₂ x)) (fun x ↦ u x - v x) := by
  simpa [sub_eq_add_neg] using forcedWaveResidualAssignedCauchyDataProblem_linear_combination
      (n := n) (1 : ℝ) (-1 : ℝ) hu hv hcu hcv

/-- Subtracting two fields with the same source and assigned data produces
the zero-source, zero-data problem. -/
theorem forcedWaveResidualAssignedCauchyDataProblem_difference_same_data_zero {f : ℝ^(n + 1) → ℝ}
    {g h : ℝ^n → ℝ} {u v : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := n) f g h) u)
    (hv : SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := n) f g h) v)
    (hcu : ContDiff ℝ 2 u) (hcv : ContDiff ℝ 2 v) :
    SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem (n := n)
      (fun _ : ℝ^(n + 1) ↦ 0) (fun _ : ℝ^n ↦ 0) (fun _ : ℝ^n ↦ 0)) (fun x ↦ u x - v x) := by
  simpa [sub_eq_add_neg] using forcedWaveResidualAssignedCauchyDataProblem_linear_combination
      (n := n) (1 : ℝ) (-1 : ℝ) hu hv hcu hcv

/-- The homogeneous Cauchy problem has zero source and assigned position and velocity. -/
noncomputable def waveResidualAssignedCauchyDataProblem (g h : ℝ^n → ℝ) :
    PDEProblem (ℝ^(n + 1)) ℝ :=
  forcedWaveResidualAssignedCauchyDataProblem (fun _ ↦ 0) g h

/-- A constant field satisfies the homogeneous problem with constant displacement
and zero velocity. -/
theorem waveResidualAssignedCauchyDataProblem_constant_position (c : ℝ) :
    SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem (n := n) (fun _ : ℝ^n ↦ c)
      (fun _ : ℝ^n ↦ 0)) (fun _ : ℝ^(n + 1) ↦ c) := by
  refine forcedWaveResidualAssignedCauchyDataProblem.of_residual_initial (n := n) ?_ ?_ ?_
  · intro x hx
    simp [waveOperator]
  · intro x hx
    simp
  · intro x hx
    simp [partialDeriv]

/-- A classical assigned-Cauchy-data solution also satisfies the wave
residual on the initial slice.

The bundled problem states the residual for `t > 0`; this is its canonical
extension to `t = 0` under the regularity required by the energy method. -/
theorem waveResidualAssignedCauchyDataProblem.residual_eq_initial {g h : ℝ^n → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u)
    (hsol : SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem (n := n) g h) u) (x : ℝ^n) :
    waveOperator (n := n) u (timeSpaceCons 0 x) = 0 := by
  let residual : ℝ → ℝ := fun t ↦ waveOperator (n := n) u (timeSpaceCons t x)
  have htime :
      Continuous (fun t : ℝ ↦ timeSpaceCons (n := n) t x) := by
    rw [continuous_iff_continuousAt]
    exact fun t ↦ (PDE.Common.hasDerivAt_timeSpaceCons_time n t x).continuousAt
  have hcontinuous : Continuous residual := (continuous_waveOperator_of_contDiff_two hu).comp htime
  have hpositive :
      residual =ᶠ[𝓝[>] (0 : ℝ)] fun _ ↦ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact forcedWaveResidualAssignedCauchyDataProblem.residual_eq
        hsol (by simpa [residual] using ht)
  have hlimitValue : Tendsto residual (𝓝[>] (0 : ℝ)) (𝓝 (residual 0)) :=
    hcontinuous.continuousAt.mono_left inf_le_left
  have hlimitZero : Tendsto residual (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_const_nhds.congr' hpositive.symm
  exact tendsto_nhds_unique hlimitValue hlimitZero

/-- A classical assigned-Cauchy-data solution satisfies the wave residual at
every nonnegative time. -/
theorem waveResidualAssignedCauchyDataProblem.residual_eq_nonnegative {g h : ℝ^n → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u)
    (hsol : SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem (n := n) g h) u) {t : ℝ}
    (ht : 0 ≤ t) (x : ℝ^n) :
    waveOperator (n := n) u (timeSpaceCons t x) = 0 := by
  rcases ht.eq_or_lt with rfl | ht
  · exact waveResidualAssignedCauchyDataProblem.residual_eq_initial hu hsol x
  · exact forcedWaveResidualAssignedCauchyDataProblem.residual_eq
        hsol (by simpa using ht)

end WaveEquation
