/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.Regularity
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Response estimates in the pivot space

For `u' + B(t) u = f` with zero initial data, a lower bound
`μ ‖i v‖² ≤ B(t)(v,v)` controls the response in `L²(H)`:

`μ ‖i u‖_{L²(H)} ≤ ‖f‖_{L²(H)}`.

The forcing here belongs to the pivot space `H`, and acts on `V` through
the Gelfand embedding into `V*`. The estimate retains the mass parameter
`μ`; it does not lose a factor from the embedding `V ↪ H`. This matters
when a large mass is used to make a nonlinear response map contractive.

The proof uses the weak-solution energy identity and Cauchy–Schwarz
in Bochner `L²`. No symmetry of the form or pointwise time regularity is needed.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A zero-initial-data solution is controlled in the pivot norm by a pivot-valued
forcing. For positive `μ` this is the response bound with constant `1 / μ`; the
multiplied inequality itself holds for every real lower bound `μ`. -/
theorem ContinuousPivotEvolutionOn.mul_norm_pivot_le
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {f : Lp H 2 (volume.restrict (Ioc a b))}
    {u : Lp V 2 (volume.restrict (Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (E : ContinuousPivotEvolutionOn T (fun t ↦ u t) (fun t ↦ g t) a b)
    (hEa : E.representative a = 0)
    (hresidual : (g : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ T.pivotToDual (f t) - B t (u t))
    {μ : ℝ}
    (hcoercive : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v : V,
      μ * ‖T.inclusion v‖ ^ 2 ≤ B t v v)
    (hab : a ≤ b) :
    μ * ‖T.inclusion.compLpL 2 (volume.restrict (Ioc a b)) u‖ ≤ ‖f‖ := by
  let ν := volume.restrict (Ioc a b)
  let U := T.inclusion.compLpL 2 ν u
  have hU : (U : ℝ → H) =ᵐ[ν] fun t ↦ T.inclusion (u t) :=
    T.inclusion.coeFn_compLpL u
  have hpair : Integrable (fun t ↦ g t (u t)) ν :=
    integrable_dual_pairing g u
  have hnorm : Integrable (fun t ↦ ‖U t‖ ^ 2) ν :=
    (Lp.memLp U).integrable_norm_pow (by norm_num)
  have hpoint : ∀ᵐ t ∂ν,
      g t (u t) + μ * ‖U t‖ ^ 2 ≤ inner ℝ (f t) (U t) := by
    filter_upwards [hresidual, hcoercive, hU] with t hres hB hUt
    rw [hres, sub_apply, GelfandTriple.pivotToDual_apply, hUt]
    linarith [hB (u t)]
  have hint := integral_mono_ae (hpair.add (hnorm.const_mul μ))
    (L2.integrable_inner (𝕜 := ℝ) f U) hpoint
  change (∫ t, g t (u t) + μ * ‖U t‖ ^ 2 ∂ν) ≤
    ∫ t, inner ℝ (f t) (U t) ∂ν at hint
  rw [integral_add hpair (hnorm.const_mul μ), integral_const_mul,
    ← Lp.norm_sq_eq_integral_norm_sq, ← L2.inner_def] at hint
  -- The terminal energy is nonnegative; with zero initial data this makes
  -- the integrated time-derivative pairing nonnegative as well.
  have henergy := E.energyIdentity a b (left_mem_uIcc) (right_mem_uIcc)
  rw [hEa, norm_zero, zero_pow (by norm_num), sub_zero,
    intervalIntegral.integral_of_le hab] at henergy
  have hpair_nonneg : 0 ≤ ∫ t, g t (u t) ∂ν := by
    nlinarith [sq_nonneg ‖E.representative b‖]
  have hbound : μ * ‖U‖ ^ 2 ≤ ‖f‖ * ‖U‖ := by
    linarith [real_inner_le_norm f U]
  by_cases hzero : ‖U‖ = 0
  · simpa only [show T.inclusion.compLpL 2 (volume.restrict (Ioc a b)) u = U
      from rfl, hzero, mul_zero] using norm_nonneg f
  have hpos : 0 < ‖U‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
  change μ * ‖U‖ ≤ ‖f‖
  apply (mul_le_mul_iff_right₀ hpos).mp
  simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using hbound

/-- Two weak solutions with the same initial datum satisfy the pivot-space
response estimate for the difference of their forcings. All time derivatives
and traces are recovered from the integrated weak equations. -/
theorem IsGelfandIntegratedWeakSolution.mul_norm_pivot_sub_le
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {f₁ f₂ : Lp H 2 (volume.restrict (Ioc a b))}
    {u₁ u₂ : Lp V 2 (volume.restrict (Ioc a b))} {uInit : H}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖B t‖ ≤ MB)
    {μ : ℝ}
    (hcoercive : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v : V,
      μ * ‖T.inclusion v‖ ^ 2 ≤ B t v v)
    (h₁ : IsGelfandIntegratedWeakSolution T B
      (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f₁) u₁ uInit)
    (h₂ : IsGelfandIntegratedWeakSolution T B
      (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f₂) u₂ uInit) :
    μ * ‖T.inclusion.compLpL 2 (volume.restrict (Ioc a b)) (u₁ - u₂)‖ ≤
      ‖f₁ - f₂‖ := by
  let ν := volume.restrict (Ioc a b)
  let F := T.pivotToDual.compLpL 2 ν
  have hdiff := h₁.sub_L2 hBmeas MB hBbound h₂
  have hforcing :
      (fun t ↦ F f₁ t - F f₂ t) =ᵐ[ν] fun t ↦ F (f₁ - f₂) t := by
    rw [map_sub]
    exact (Lp.coeFn_sub (F f₁) (F f₂)).symm
  have hw := hdiff.congr_forcing_ae hforcing
  obtain ⟨g, E, _hg, hEa, hresidual⟩ :=
    hw.exists_continuousPivotEvolutionOn_initial_L2
      hBmeas MB hBbound h₁.interval_nonempty
  apply E.mul_norm_pivot_le (by simpa using hEa) _ hcoercive h₁.interval_nonempty.le
  filter_upwards [hresidual, T.pivotToDual.coeFn_compLpL (f₁ - f₂)] with t ht hft
  rw [ht, hft]

end PDE.Analysis.Evolution
