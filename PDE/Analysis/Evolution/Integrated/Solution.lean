/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.Triple
public import PDE.Analysis.Evolution.Integrated.TimeTestFunction
import PDE.Analysis.Evolution.Compactness.Lp.TimeTesting
import PDE.Analysis.Evolution.Compactness.WeakLimitTesting
import CAS.ExactTactic

/-!
# Integrated weak evolution solutions

The solution concept for the abstract parabolic problem

`u' + B(t) u = ℓ(t)` on `(a, b)`, `u(a) = uInit`,

in the integrated (time-tested) form. For `u ∈ L²(a, b; V)` and a scalar time test
`τ : TimeTest a b` (so `τ, τ' ∈ L²` and `τ b = 0`), the equation is required to hold after
pairing with `τ(t) v` for every `v ∈ V` and integrating by parts in time:

`-∫ₐᵇ ⟪u, v⟫ τ' + ∫ₐᵇ B(t)(u, v) τ = ∫ₐᵇ ℓ(v) τ + ⟪uInit, v⟫ τ(a)`.

The initial datum appears as the boundary term at `t = a`; the term at `t = b` is absent
because `τ b = 0`. Taking tests with `τ a = 0` recovers the weak time derivative, and the
affine test with `τ a = 1` recovers the initial value. This is the formulation in which
Galerkin approximants pass to the weak limit without any prior knowledge of a time
derivative or a trace of the limit. There are two versions: `IsIntegratedWeakSolution`
for a single real inner product space `V`, and `IsGelfandIntegratedWeakSolution` for a
Gelfand triple `V ↪ H`, in which the time term and the initial trace use the pivot inner
product. The first is the second for the identity triple `GelfandTriple.identity`.

Evans, §7.1.1(b), defines a weak solution by requiring `u' ∈ L²(0, T; H⁻¹(U))`, the identity
(i) for each test function and almost every time, and `u(0) = g`. The integrated identity
above, for the test functions `τ(t) v`, is his (34), which he obtains in step 3 of the proof of
§7.1.2, Theorem 3, as the limit of the Galerkin identities (33), and compares with (32) to
show `u(0) = g`.

A Gårding bound `θ ‖w‖_V² ≤ B(t)(w, w) + γ ‖i w‖_H²` is reduced to coercivity by an
exponential shift. The mass-shifted form `B_γ(t) = B(t) + γ ⟪i ·, i ·⟫_H` satisfies
`θ ‖w‖_V² ≤ B_γ(t)(w, w)`, and if `w` solves the shifted problem with forcing
`e^{-γ(t - a)} ℓ`, then `u(t) = e^{γ(t - a)} w(t)` solves the original problem with forcing
`ℓ` and the same initial datum. This is the standard exponential-weight substitution,
carried out at the level of Bochner classes: the proof applies the shifted equation to
the weighted test `e^{γ(t - a)} τ` and uses the product rule recorded in `TimeTest.expMul`.

## Main results

* `IsIntegratedWeakSolution`, `IsGelfandIntegratedWeakSolution`: the solution concepts.
  Integrability of the tested form and forcing terms is part of the structure because
  Mathlib's Bochner integral of a non-integrable function is `0`.
* `gardingShiftForm`, `gardingShiftForm_coercive`, `norm_gardingShiftForm_le`,
  `continuousOn_gardingShiftForm`, `aestronglyMeasurable_gardingShiftForm`: the shifted
  form and the properties it inherits from `B`.
* `exponentialMulLp`: multiplication of an `L²` trajectory by `e^{γ(t - a)}`.
* `IsGelfandIntegratedWeakSolution.of_exponential_gardingShift`: undoing the shift, from a
  solution of the coercive problem to a solution of the original one.
* `IsGelfandIntegratedWeakSolution.sub_L2`, `sub_same_data`,
  `IsIntegratedWeakSolution.sub_same_data`: differences of solutions solve the problem
  with the differenced forcing and initial data.
* `IsIntegratedWeakSolution.congr_forcing_ae` and its Gelfand version: the solution
  concept depends on `ℓ` only through its a.e. class.
* `integrable_gelfandPivotTimeTest`: Hölder integrability of the pivot pairing
  `t ↦ ⟪i(u t), i v⟫ φ(t)` for `u ∈ L²(V)`, `φ ∈ L²`.

## Implementation notes

The forcing is a plain function `ℝ → V*` in the structures, so that both continuous
forcings and coercions of `L²(a, b; V*)` classes can be used; the `_L2` lemmas take
the class and coerce it. Subtraction lemmas use strong measurability of each fixed-vector
evaluation and an a.e. operator-norm bound (`hBmeas`, `hBbound`) to split the Bochner
integrals of the form term.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.1(b), the definition of a weak solution, p. 374,
  and §7.1.2, Theorem 3 (Existence of weak solution), step 3 of its proof, (32)-(34), p. 379.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace PDE.Analysis.Evolution

/-- Exponentially rescale a Bochner `L²` trajectory on `[a,b]` by
`t ↦ exp (gamma * (t-a))`. -/
noncomputable def exponentialMulLp
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a b : ℝ} (gamma : ℝ)
    (u : Lp X 2 (volume.restrict (Set.Ioc a b))) :
    Lp X 2 (volume.restrict (Set.Ioc a b)) :=
  scalarMulLp (fun t ↦ Real.exp (gamma * (t - a)))
    ((Real.continuous_exp.comp
      (continuous_const.mul
        (continuous_id.sub continuous_const))).continuousOn) u

/-- `exponentialMulLp γ u` is a.e. equal to `t ↦ e^{γ(t - a)} u(t)`. -/
theorem exponentialMulLp_apply_ae
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a b : ℝ} (gamma : ℝ)
    (u : Lp X 2 (volume.restrict (Set.Ioc a b))) :
    (exponentialMulLp gamma u : ℝ → X) =ᵐ[
      volume.restrict (Set.Ioc a b)]
        fun t ↦ Real.exp (gamma * (t - a)) • u t :=
  scalarMulLp_apply_ae (fun t ↦ Real.exp (gamma * (t - a)))
    ((Real.continuous_exp.comp
      (continuous_const.mul
        (continuous_id.sub continuous_const))).continuousOn) u

/-- Integrated weak solution of `u' + B(t) u = ℓ(t)`, `u(a) = uInit` on `[a, b]`, in a
single real inner product space `V`: for every `v ∈ V` and every `τ : TimeTest a b`,

`-∫ₐᵇ ⟪u, v⟫ τ' + ∫ₐᵇ B(t)(u, v) τ = ∫ₐᵇ ℓ(t)(v) τ + ⟪uInit, v⟫ τ(a)`.

The form and forcing terms are required to be integrable for every test, since Mathlib
assigns the value zero to the integral of a non-integrable function. The time term is
integrable by Hölder's inequality from `u ∈ L²` and `τ' ∈ L²`. -/
structure IsIntegratedWeakSolution
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {a b : ℝ} (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V)
    (u : Lp V 2 (volume.restrict (Set.Ioc a b))) (uInit : V) : Prop where
  /-- The evolution interval has positive length and is oriented forward in time. -/
  interval_nonempty : a < b
  /-- The tested spatial-form term is integrable. -/
  integrable_form : ∀ (v : V) (τ : TimeTest a b),
    Integrable (fun t ↦ B t (u t) v * τ.toLp t)
      (volume.restrict (Set.Ioc a b))
  /-- The tested forcing term is integrable. -/
  integrable_forcing : ∀ (v : V) (τ : TimeTest a b),
    Integrable (fun t ↦ ell t v * τ.toLp t)
      (volume.restrict (Set.Ioc a b))
  /-- The integrated weak evolution identity. -/
  equation : ∀ (v : V) (τ : TimeTest a b),
    -(∫ t, inner ℝ (u t) v * τ.derivToLp t ∂(volume.restrict (Set.Ioc a b))) +
        ∫ t, B t (u t) v * τ.toLp t ∂(volume.restrict (Set.Ioc a b)) =
      (∫ t, ell t v * τ.toLp t ∂(volume.restrict (Set.Ioc a b))) +
        inner ℝ uInit v * τ.toFun a

/-- Integrated weak solution of `u' + B(t) u = ℓ(t)`, `u(a) = uInit` on `[a, b]` for a
Gelfand triple `i : V ↪ H`, with `u ∈ L²(a, b; V)` and `uInit ∈ H`: for every `v ∈ V` and
every `τ : TimeTest a b`,

`-∫ₐᵇ ⟪i u, i v⟫_H τ' + ∫ₐᵇ B(t)(u, v) τ = ∫ₐᵇ ℓ(t)(v) τ + ⟪uInit, i v⟫_H τ(a)`.

As in `IsIntegratedWeakSolution`, integrability of the tested form and forcing terms is
part of the definition. -/
structure IsGelfandIntegratedWeakSolution
    {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℝ} (T : GelfandTriple (V := V) (H := H))
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    (u : Lp V 2 (volume.restrict (Set.Ioc a b))) (uInit : H) : Prop where
  /-- The evolution interval has positive length and is oriented forward in time. -/
  interval_nonempty : a < b
  /-- The tested spatial-form term is integrable. -/
  integrable_form : ∀ (v : V) (τ : TimeTest a b),
    Integrable (fun t ↦ B t (u t) v * τ.toLp t)
      (volume.restrict (Set.Ioc a b))
  /-- The tested forcing term is integrable. -/
  integrable_forcing : ∀ (v : V) (τ : TimeTest a b),
    Integrable (fun t ↦ ell t v * τ.toLp t)
      (volume.restrict (Set.Ioc a b))
  /-- The integrated weak evolution identity. -/
  equation : ∀ (v : V) (τ : TimeTest a b),
    -(∫ t, inner ℝ (T.inclusion (u t)) (T.inclusion v) * τ.derivToLp t
        ∂(volume.restrict (Set.Ioc a b))) +
        ∫ t, B t (u t) v * τ.toLp t ∂(volume.restrict (Set.Ioc a b)) =
      (∫ t, ell t v * τ.toLp t ∂(volume.restrict (Set.Ioc a b))) +
        inner ℝ uInit (T.inclusion v) * τ.toFun a

/-- The mass-shifted form

`B_γ(t)(u, v) = B(t)(u, v) + γ ⟪i u, i v⟫_H`,

which turns a Gårding lower bound for `B` into coercivity. -/
noncomputable def gardingShiftForm
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : GelfandTriple (V := V) (H := H))
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) (gamma : ℝ) :
    ℝ → V →L[ℝ] StrongDual ℝ V :=
  fun t ↦ B t + gamma • T.energyToDual

/-- The shifted form evaluates as `B(t)(u, v) + γ ⟪i u, i v⟫_H`. -/
@[simp]
theorem gardingShiftForm_apply
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : GelfandTriple (V := V) (H := H))
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) (gamma t : ℝ) (u v : V) :
    gardingShiftForm T B gamma t u v =
      B t u v + gamma * inner ℝ (T.inclusion u) (T.inclusion v) := by
  simp [gardingShiftForm, GelfandTriple.energyToDual_apply]

/-- Continuity of the original form is preserved by the constant mass
shift. -/
theorem continuousOn_gardingShiftForm
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℝ} (T : GelfandTriple (V := V) (H := H))
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {gamma : ℝ}
    (hB : ContinuousOn B (Set.Icc a b)) :
    ContinuousOn (gardingShiftForm T B gamma) (Set.Icc a b) := by
  let : IsTopologicalAddGroup (V →L[ℝ] StrongDual ℝ V) :=
    ContinuousLinearMap.isTopologicalAddGroup
  let : ContinuousAdd (V →L[ℝ] StrongDual ℝ V) :=
    ContinuousLinearMap.isTopologicalAddGroup.toContinuousAdd
  exact hB.add continuousOn_const

/-- Strong measurability of each fixed-vector evaluation is preserved by the constant
mass shift. -/
theorem aestronglyMeasurable_gardingShiftForm
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {μ : Measure ℝ} (T : GelfandTriple (V := V) (H := H))
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {gamma : ℝ}
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) μ) :
    ∀ v, AEStronglyMeasurable (fun t ↦ gardingShiftForm T B gamma t v) μ := by
  intro v
  exact (hB v).add aestronglyMeasurable_const

/-- Operator-norm bound for the Gårding-shifted form. -/
theorem norm_gardingShiftForm_le
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : GelfandTriple (V := V) (H := H))
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) (gamma t : ℝ) :
    ‖gardingShiftForm T B gamma t‖ ≤
      ‖B t‖ + ‖gamma‖ * ‖T.energyToDual‖ := by
  unfold gardingShiftForm
  calc
    ‖B t + gamma • T.energyToDual‖ ≤
        ‖B t‖ + ‖gamma • T.energyToDual‖ :=
      ContinuousLinearMap.opNorm_add_le _ _
    _ ≤ ‖B t‖ + ‖gamma‖ * ‖T.energyToDual‖ :=
      add_le_add le_rfl
        (ContinuousLinearMap.opNorm_smul_le gamma T.energyToDual)

/-- A Gårding lower bound gives the same lower bound for the mass-shifted form. For
`0 < theta` this is coercivity of the shifted form. -/
theorem gardingShiftForm_coercive
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b theta gamma : ℝ}
    (T : GelfandTriple (V := V) (H := H))
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (hGarding : ∀ t ∈ Set.Icc a b, ∀ w : V,
      theta * ‖w‖ ^ 2 ≤
        B t w w + gamma * ‖T.inclusion w‖ ^ 2) :
    ∀ t ∈ Set.Icc a b, ∀ w : V,
      theta * ‖w‖ ^ 2 ≤ gardingShiftForm T B gamma t w w := by
  intro t ht w
  simpa [real_inner_self_eq_norm_sq] using hGarding t ht w

/-- The pivot pairing of an `L²(V)` trajectory with a fixed energy-space
test vector and an `L²` scalar time test is integrable. -/
theorem integrable_gelfandPivotTimeTest
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {μ : Measure ℝ} (T : GelfandTriple (V := V) (H := H))
    (v : V) (φ : Lp ℝ 2 μ) (u : Lp V 2 μ) :
    Integrable (fun t ↦ inner ℝ (T.inclusion (u t)) (T.inclusion v) * φ t) μ := by
  let uH : Lp H 2 μ := T.inclusion.compLpL 2 μ u
  let test : Lp ℝ 2 μ := (innerSL ℝ (T.inclusion v)).compLpL 2 μ uH
  have hinner := L2.integrable_inner (𝕜 := ℝ) φ test
  apply hinner.congr
  filter_upwards [T.inclusion.coeFn_compLpL u,
    (innerSL ℝ (T.inclusion v)).coeFn_compLpL uH] with t huHt htest
  rw [htest, huHt]
  rw [Real.inner_apply]
  change φ t * inner ℝ (T.inclusion v) (T.inclusion (u t)) =
    inner ℝ (T.inclusion (u t)) (T.inclusion v) * φ t
  rw [real_inner_comm (T.inclusion v) (T.inclusion (u t))]
  ring

/-- The tested pivot time term of a difference is the difference of the tested terms. -/
private theorem integral_gelfandPivotTimeTest_sub
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {μ : Measure ℝ} (T : GelfandTriple (V := V) (H := H))
    (v : V) (φ : Lp ℝ 2 μ) (u₁ u₂ : Lp V 2 μ) :
    ∫ t, inner ℝ (T.inclusion ((u₁ - u₂) t)) (T.inclusion v) * φ t ∂μ =
      (∫ t, inner ℝ (T.inclusion (u₁ t)) (T.inclusion v) * φ t ∂μ) -
        ∫ t, inner ℝ (T.inclusion (u₂ t)) (T.inclusion v) * φ t ∂μ := by
  rw [← integral_sub (integrable_gelfandPivotTimeTest T v φ u₁)
    (integrable_gelfandPivotTimeTest T v φ u₂)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub u₁ u₂] with t ht
  rw [ht, Pi.sub_apply, map_sub, inner_sub_left, sub_mul]

/-- The tested form term of a difference is the difference of the tested terms. -/
private theorem integral_timeDependentBilinearTimeTest_sub
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {μ : Measure ℝ} {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) μ) (MB : ℝ)
    (hBbound : ∀ᵐ t ∂μ, ‖B t‖ ≤ MB) (v : V) (φ : Lp ℝ 2 μ) (u₁ u₂ : Lp V 2 μ) :
    ∫ t, B t ((u₁ - u₂) t) v * φ t ∂μ =
      (∫ t, B t (u₁ t) v * φ t ∂μ) - ∫ t, B t (u₂ t) v * φ t ∂μ := by
  rw [← integral_sub (integrable_timeDependentBilinearTimeTest B v φ hBmeas MB hBbound u₁)
    (integrable_timeDependentBilinearTimeTest B v φ hBmeas MB hBbound u₂)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub u₁ u₂] with t ht
  rw [ht, Pi.sub_apply, map_sub, sub_apply, sub_mul]

/-- If `uᵢ` is an integrated Gelfand weak solution with forcing `ℓᵢ ∈ L²(a, b; V*)` and
initial datum `uInitᵢ` (`i = 1, 2`), then `u₁ - u₂` is one with forcing `ℓ₁ - ℓ₂` and
initial datum `uInit₁ - uInit₂`. The form `B` is strongly measurable on each fixed vector
and essentially bounded in operator norm. -/
theorem IsGelfandIntegratedWeakSolution.sub_L2
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell₁ ell₂ : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    {u₁ u₂ : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {uInit₁ uInit₂ : H}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (h₁ : IsGelfandIntegratedWeakSolution T B (fun t ↦ ell₁ t) u₁ uInit₁)
    (h₂ : IsGelfandIntegratedWeakSolution T B (fun t ↦ ell₂ t) u₂ uInit₂) :
    IsGelfandIntegratedWeakSolution T B
      (fun t ↦ ell₁ t - ell₂ t) (u₁ - u₂) (uInit₁ - uInit₂) := by
  refine ⟨h₁.interval_nonempty, fun v τ ↦ integrable_timeDependentBilinearTimeTest B v τ.toLp
    hBmeas MB hBbound (u₁ - u₂), fun v τ ↦ ?_, fun v τ ↦ ?_⟩
  · refine ((h₁.integrable_forcing v τ).sub (h₂.integrable_forcing v τ)).congr
      (.of_forall fun t ↦ ?_)
    simp only [Pi.sub_apply, sub_apply, sub_mul]
  · have hforcing : ∫ t, (ell₁ t - ell₂ t) v * τ.toLp t ∂(volume.restrict (Set.Ioc a b)) =
        (∫ t, ell₁ t v * τ.toLp t ∂(volume.restrict (Set.Ioc a b))) -
          ∫ t, ell₂ t v * τ.toLp t ∂(volume.restrict (Set.Ioc a b)) := by
      rw [← integral_sub (h₁.integrable_forcing v τ) (h₂.integrable_forcing v τ)]
      simp only [sub_apply, sub_mul]
    rw [integral_gelfandPivotTimeTest_sub, integral_timeDependentBilinearTimeTest_sub hBmeas MB
      hBbound, hforcing, inner_sub_left]
    linarith [h₁.equation v τ, h₂.equation v τ]

/-- The difference of two integrated weak solutions with the same forcing
and initial datum is a homogeneous integrated weak solution with zero
initial datum. -/
theorem IsGelfandIntegratedWeakSolution.sub_same_data
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {u₁ u₂ : Lp V 2 (volume.restrict (Set.Ioc a b))} {uInit : H}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (h₁ : IsGelfandIntegratedWeakSolution T B ell u₁ uInit)
    (h₂ : IsGelfandIntegratedWeakSolution T B ell u₂ uInit) :
    IsGelfandIntegratedWeakSolution T B 0 (u₁ - u₂) 0 := by
  refine ⟨h₁.interval_nonempty, fun v τ ↦ integrable_timeDependentBilinearTimeTest B v τ.toLp
    hBmeas MB hBbound (u₁ - u₂), fun v τ ↦ by simp, fun v τ ↦ ?_⟩
  simp only [Pi.zero_apply, zero_apply, zero_mul, integral_zero, inner_zero_left, zero_add]
  rw [integral_gelfandPivotTimeTest_sub, integral_timeDependentBilinearTimeTest_sub hBmeas MB
    hBbound]
  linarith [h₁.equation v τ, h₂.equation v τ]

/--
The difference of two integrated weak solutions in one inner product space with the same
forcing and initial datum is a homogeneous solution with zero initial datum. This is the
single-space form of `IsGelfandIntegratedWeakSolution.sub_same_data`.
-/
theorem IsIntegratedWeakSolution.sub_same_data
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {a b : ℝ} {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell : ℝ → StrongDual ℝ V}
    {u₁ u₂ : Lp V 2 (volume.restrict (Set.Ioc a b))} {uInit : V}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (h₁ : IsIntegratedWeakSolution B ell u₁ uInit)
    (h₂ : IsIntegratedWeakSolution B ell u₂ uInit) :
    IsIntegratedWeakSolution B 0 (u₁ - u₂) 0 := by
  refine ⟨h₁.interval_nonempty, fun v τ ↦ integrable_timeDependentBilinearTimeTest B v τ.toLp
    hBmeas MB hBbound (u₁ - u₂), fun v τ ↦ by simp, fun v τ ↦ ?_⟩
  have htime := integral_gelfandPivotTimeTest_sub (GelfandTriple.identity V) v τ.derivToLp u₁ u₂
  simp only [GelfandTriple.identity_inclusion_apply] at htime
  simp only [Pi.zero_apply, zero_apply, zero_mul, integral_zero, inner_zero_left, zero_add]
  rw [htime, integral_timeDependentBilinearTimeTest_sub hBmeas MB hBbound]
  linarith [h₁.equation v τ, h₂.equation v τ]

/--
The single-space integrated weak equation depends on the forcing only through its
almost-everywhere class on `(a, b]`.
-/
theorem IsIntegratedWeakSolution.congr_forcing_ae
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {a b : ℝ} {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell₁ ell₂ : ℝ → StrongDual ℝ V}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))} {uInit : V}
    (h : ell₁ =ᵐ[volume.restrict (Set.Ioc a b)] ell₂)
    (hu : IsIntegratedWeakSolution B ell₁ u uInit) :
    IsIntegratedWeakSolution B ell₂ u uInit := by
  have hforcing (v : V) (τ : TimeTest a b) : (fun t ↦ ell₁ t v * τ.toLp t)
      =ᵐ[volume.restrict (Set.Ioc a b)] fun t ↦ ell₂ t v * τ.toLp t := by
    filter_upwards [h] with t ht
    rw [ht]
  exact ⟨hu.interval_nonempty, hu.integrable_form,
    fun v τ ↦ (hu.integrable_forcing v τ).congr (hforcing v τ),
    fun v τ ↦ integral_congr_ae (hforcing v τ) ▸ hu.equation v τ⟩

/-- The integrated weak equation depends on the forcing only through its
almost-everywhere class on the time interval. -/
theorem IsGelfandIntegratedWeakSolution.congr_forcing_ae
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell₁ ell₂ : ℝ → StrongDual ℝ V}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))} {uInit : H}
    (h : ell₁ =ᵐ[volume.restrict (Set.Ioc a b)] ell₂)
    (hu : IsGelfandIntegratedWeakSolution T B ell₁ u uInit) :
    IsGelfandIntegratedWeakSolution T B ell₂ u uInit := by
  have hforcing (v : V) (τ : TimeTest a b) : (fun t ↦ ell₁ t v * τ.toLp t)
      =ᵐ[volume.restrict (Set.Ioc a b)] fun t ↦ ell₂ t v * τ.toLp t := by
    filter_upwards [h] with t ht
    rw [ht]
  exact ⟨hu.interval_nonempty, hu.integrable_form,
    fun v τ ↦ (hu.integrable_forcing v τ).congr (hforcing v τ),
    fun v τ ↦ integral_congr_ae (hforcing v τ) ▸ hu.equation v τ⟩

/-- Undo the exponential Gårding shift at the integrated weak-solution
level.

If `w` solves

`w_t + B_γ(t) w = e^{-γ(t - a)} ℓ`, `w(a) = uInit`,

with `B_γ = gardingShiftForm T B γ`, then `u(t) = e^{γ(t - a)} w(t)` solves

`u_t + B(t) u = ℓ`, `u(a) = uInit`.

The proof applies the shifted equation to the time test `e^{γ(t - a)} τ(t)`. Its
product-rule term cancels the added pivot mass form. -/
theorem IsGelfandIntegratedWeakSolution.of_exponential_gardingShift
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b gamma : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    {ell : Lp (StrongDual ℝ V) 2
      (volume.restrict (Set.Ioc a b))}
    {w : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {uInit : H}
    (hw : IsGelfandIntegratedWeakSolution T
      (gardingShiftForm T B gamma)
      (fun t ↦ exponentialMulLp (-gamma) ell t) w uInit) :
    IsGelfandIntegratedWeakSolution T B (fun t ↦ ell t)
      (exponentialMulLp gamma w) uInit := by
  refine ⟨hw.interval_nonempty, fun v τ ↦ integrable_timeDependentBilinearTimeTest B v τ.toLp
    hBmeas MB hBbound _, fun v τ ↦ integrable_dualTimeTest v τ.toLp ell, fun v τ ↦ ?_⟩
  let μab := volume.restrict (Set.Ioc a b)
  set u : Lp V 2 μab := exponentialMulLp gamma w
  have hu : (u : ℝ → V) =ᵐ[μab] fun t ↦ Real.exp (gamma * (t - a)) • w t :=
    exponentialMulLp_apply_ae gamma w
  have hmassInt : Integrable
      (fun t ↦ inner ℝ (T.inclusion (u t)) (T.inclusion v) * τ.toLp t) μab :=
    integrable_gelfandPivotTimeTest T v τ.toLp u
  -- the product rule for the weighted test produces the mass term `γ ⟪u, v⟫ τ` ...
  have htime :
      (∫ t, inner ℝ (T.inclusion (w t)) (T.inclusion v) * (τ.expMul gamma).derivToLp t ∂μab) =
        (∫ t, inner ℝ (T.inclusion (u t)) (T.inclusion v) * τ.derivToLp t ∂μab) +
          gamma * ∫ t, inner ℝ (T.inclusion (u t)) (T.inclusion v) * τ.toLp t ∂μab := by
    rw [← integral_const_mul, ← integral_add (integrable_gelfandPivotTimeTest T v τ.derivToLp u)
      (hmassInt.const_mul gamma)]
    refine integral_congr_ae ?_
    filter_upwards [hu, TimeTest.expMul_derivToLp_ae gamma τ] with t hut hτt
    rw [hut, hτt, map_smul, real_inner_smul_left]
    ring
  -- ... which cancels the added pivot mass form
  have hform :
      (∫ t, gardingShiftForm T B gamma t (w t) v * (τ.expMul gamma).toLp t ∂μab) =
        (∫ t, B t (u t) v * τ.toLp t ∂μab) +
          gamma * ∫ t, inner ℝ (T.inclusion (u t)) (T.inclusion v) * τ.toLp t ∂μab := by
    rw [← integral_const_mul, ← integral_add
      (integrable_timeDependentBilinearTimeTest B v τ.toLp hBmeas MB hBbound u)
      (hmassInt.const_mul gamma)]
    refine integral_congr_ae ?_
    filter_upwards [hu, TimeTest.expMul_toLp_ae gamma τ] with t hut hτt
    rw [hut, hτt, gardingShiftForm_apply]
    simp only [map_smul, smul_apply, real_inner_smul_left, smul_eq_mul]
    ring
  have hforcing :
      (∫ t, exponentialMulLp (-gamma) ell t v * (τ.expMul gamma).toLp t ∂μab) =
        ∫ t, ell t v * τ.toLp t ∂μab := by
    refine integral_congr_ae ?_
    filter_upwards [exponentialMulLp_apply_ae (-gamma) ell, TimeTest.expMul_toLp_ae gamma τ]
      with t hellt hτt
    rw [hellt, hτt, smul_apply, smul_eq_mul]
    have hexp : Real.exp ((-gamma) * (t - a)) * Real.exp (gamma * (t - a)) = 1 := by
      rw [← Real.exp_add]
      cas
    linear_combination (ell t v * τ.toLp t) * hexp
  have hraw := hw.equation v (τ.expMul gamma)
  rw [htime, hform, hforcing] at hraw
  simp only [TimeTest.expMul_toFun, sub_self, mul_zero, Real.exp_zero, one_mul] at hraw
  linarith

end PDE.Analysis.Evolution
