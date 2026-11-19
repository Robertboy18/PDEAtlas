/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic
public import PDE.Analysis.Evolution.Integrated.Solution
public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
import PDE.Analysis.Evolution.Core.EnergyEstimate
import PDE.Analysis.Evolution.Core.GardingEstimate
import PDE.Analysis.Evolution.Integrated.Regularity
import PDE.Analysis.MeasureTheory.LpNorm
import CAS.IntegrationTactic

/-!
# Energy bounds for integrated weak solutions

Let `V ↪ H` be a Gelfand triple, `B(t) : V → V*` a bounded measurable family of forms
on `[a, b]`, and `u ∈ L²(a, b; V)` an integrated weak solution of `u' + B(t) u = ℓ` with
initial datum `uInit ∈ H` (`IsGelfandIntegratedWeakSolution`). The time-regularity file
`PDE.Analysis.Evolution.Integrated.Regularity` gives a Lions–Magenes representative
`E : ContinuousPivotEvolutionOn`: an `H`-continuous representative of `u` on `[a, b]`
with weak derivative `g = ℓ - B(·)u ∈ L²(a, b; V*)` and the exact energy identity
`‖E(t)‖² - ‖E(s)‖² = 2 ∫ₛᵗ g(u)`. Here that identity gives the a priori estimates of
parabolic theory.

Substituting `g = ℓ - B u` into the energy identity and applying Young's inequality to the
forcing term gives, under uniform coercivity `C ‖w‖_V² ≤ B(t)(w, w)` with `C > 0`,

`½ ‖E(t)‖_H² + (C/2) ∫ₐᵗ ‖u‖_V² ≤ ½ ‖uInit‖_H² + (1/(2C)) ∫ₐᵗ ‖ℓ‖_{V*}²`,

and under a Gårding lower bound `θ ‖w‖_V² ≤ B(t)(w, w) + γ ‖i w‖_H²`, with `θ > 0`,
the same inequality with `C` replaced by `θ` and the extra term `γ ∫ₐᵗ ‖E‖_H²` on the right.
For `γ ≥ 0`, a scalar Grönwall argument bounds `‖E(t)‖_H²` by
`(‖uInit‖² + θ⁻¹ ‖ℓ‖²_{L²(V*)}) e^{2γ(t-a)}`.
Evans proves these estimates for the Galerkin approximations (§7.1.2, Theorem 2); here they
are stated for the limiting weak solution with forcing in `L²(a, b; V*)`.

## Main results

* `ContinuousPivotEvolutionOn.coercive_energy_bound_L2`: the coercive estimate for a
  representative `E` whose derivative is a.e. the residual `ℓ - B u`.
* `ContinuousPivotEvolutionOn.garding_energy_bound_L2`: the Gårding estimate with the
  pivot-norm correction term.
* `ContinuousPivotEvolutionOn.pivot_norm_sq_le_exp_of_garding_energy_bound_L2`: the
  Grönwall consequence, an explicit exponential bound on `‖E(t)‖_H²`.
* `IsGelfandIntegratedWeakSolution.exists_continuousPivotEvolutionOn_with_garding_bound_L2`:
  existence of `g` and `E` with `E a = uInit`, the residual identity and the Gårding
  estimate on every prefix `[a, t]`, directly from the integrated weak solution.
* `IsGelfandIntegratedWeakSolution.difference_garding_energy_bound_L2`: continuous
  dependence, the same estimate for `u₁ - u₂` in terms of `uInit₁ - uInit₂` and
  `ℓ₁ - ℓ₂`.
* `IsGelfandIntegratedWeakSolution.norm_sub_le_of_coercive_L2`: the Bochner-norm
  stability bound `‖u₁ - u₂‖_{L²(V)} ≤ C⁻¹ ‖ℓ₁ - ℓ₂‖_{L²(V*)}` for solutions with the
  same initial datum, which is the completion estimate used to pass from continuous to
  `L²` forcings.
* `ContinuousPivotEvolutionOn.coercive_energy_bound` and
  `IsGelfandIntegratedWeakSolution.exists_continuousPivotEvolutionOn_with_energy_bound`:
  estimates with a pointwise forcing bound `‖ℓ(t)‖ ≤ M`, giving
  `M² (t - a)/(2C)` in place of the forcing integral. The existence theorem
  additionally assumes continuity of `ℓ`.

## Implementation notes

The estimates are stated in terms of `E.representative`, the continuous `H`-valued
function, because the trajectory `u` itself is only an `L²(V)` class and its `H`-norm at a
single time depends on the chosen representative. The measurability and boundedness hypotheses
`hBmeas`, `hBbound` on `B` are what make the residual `ℓ - B(·)u` an element of
`L²(a, b; V*)`. The interval hypothesis is `a ≤ b` for the pure inequalities and `a < b`
in the theorems that construct the continuous representative from an integrated solution.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, Theorem 2 (energy estimates), estimate (20).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace PDE.Analysis.Evolution

section GelfandWeakTimeDerivative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The energy identity turns an a.e. bound `g(u) + (θ/2)‖u‖² ≤ F` on `(a, t]` into the energy
inequality `½‖E(t)‖² + (θ/2) ∫ₐᵗ ‖u‖² ≤ ½‖E(a)‖² + ∫ₐᵗ F`. -/
private theorem energy_bound_of_ae_le {a b t θ : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (E : ContinuousPivotEvolutionOn T (fun t ↦ u t) (fun t ↦ g t) a b) {uInit : H}
    (hEa : E.representative a = uInit) (hab : a ≤ b) (ht : t ∈ Icc a b) {F : ℝ → ℝ}
    (hF : IntegrableOn F (Ioc a t))
    (hpoint : ∀ᵐ r ∂volume.restrict (Ioc a t), g r (u r) + θ / 2 * ‖u r‖ ^ 2 ≤ F r) :
    1 / 2 * ‖E.representative t‖ ^ 2 + θ / 2 * ∫ s in Ioc a t, ‖u s‖ ^ 2 ≤
      1 / 2 * ‖uInit‖ ^ 2 + ∫ s in Ioc a t, F s := by
  have hmeasure : volume.restrict (Ioc a t) ≤ volume.restrict (Ioc a b) :=
    Measure.restrict_mono_set _ (Ioc_subset_Ioc_right ht.2)
  have hpair := (integrable_dual_pairing g u).mono_measure hmeasure
  have huSq := ((Lp.memLp u).integrable_norm_pow two_ne_zero).mono_measure hmeasure
  have hint : ∫ r in Ioc a t, (g r (u r) + θ / 2 * ‖u r‖ ^ 2) ≤ ∫ r in Ioc a t, F r :=
    integral_mono_ae (hpair.add (huSq.const_mul (θ / 2))) hF hpoint
  rw [integral_add hpair (huSq.const_mul _), integral_const_mul] at hint
  have henergy := E.energyIdentity a t left_mem_uIcc (by rwa [uIcc_of_le hab])
  rw [intervalIntegral.integral_of_le ht.1, hEa] at henergy
  linarith

/-- Post-limit coercive energy estimate with the natural
`L²(a,b; V*)` forcing hypothesis.

If `u_t + A(t)u = ell` in `V*` and
`C ‖v‖_V² ≤ B(t)(v,v)` with `C > 0`, the Lions–Magenes identity and Young's
inequality give

`(1/2) ‖u(t)‖_H² + (C/2) ∫ₐᵗ ‖u(s)‖_V² ds
    ≤ (1/2) ‖u(a)‖_H² + (1/(2C)) ∫ₐᵗ ‖ell(s)‖_{V*}² ds`.

Membership of the forcing in Bochner `L²` ensures that its squared norm
is integrable on every prefix `[a,t]`. Continuity and a pointwise forcing
bound are not required. Evans proves the corresponding estimate (20) for the
Galerkin approximations (§7.1.2, Theorem 2). -/
theorem ContinuousPivotEvolutionOn.coercive_energy_bound_L2
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (E : ContinuousPivotEvolutionOn T (fun t ↦ u t) (fun t ↦ g t) a b)
    {uInit : H} (hEa : E.representative a = uInit)
    (hresidual : (g : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict
      (Set.Ioc a b)] fun t ↦ ell t - B t (u t))
    {C : ℝ} (hC : 0 < C)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (hab : a ≤ b) :
    ∀ t ∈ Set.Icc a b,
      (1 / 2 : ℝ) * ‖E.representative t‖ ^ 2 +
          (C / 2) * ∫ s in a..t, ‖u s‖ ^ 2 ≤
        (1 / 2 : ℝ) * ‖uInit‖ ^ 2 +
          (1 / (2 * C)) * ∫ s in a..t, ‖ell s‖ ^ 2 := by
  intro t ht
  have hmeasure : volume.restrict (Ioc a t) ≤ volume.restrict (Ioc a b) :=
    Measure.restrict_mono_set _ (Ioc_subset_Ioc_right ht.2)
  have h := energy_bound_of_ae_le (θ := C) E hEa hab ht
    ((((Lp.memLp ell).integrable_norm_pow two_ne_zero).mono_measure hmeasure).div_const
      (2 * C)) <| by
    filter_upwards [hresidual.filter_mono (ae_mono hmeasure), ae_restrict_mem measurableSet_Ioc]
      with r hgr hr
    have hellNorm : ell r (u r) ≤ ‖ell r‖ * ‖u r‖ :=
      (le_abs_self _).trans ((ell r).le_opNorm (u r))
    have hyoung := mul_le_sq_div_add_mul_sq_half hC ‖ell r‖ ‖u r‖
    rw [hgr, sub_apply]
    nlinarith [hcoercive r ⟨hr.1.le, hr.2.trans ht.2⟩ (u r),
      mul_nonneg hC.le (sq_nonneg ‖u r‖)]
  rw [integral_div, div_eq_inv_mul _ (2 * C)] at h
  simp only [intervalIntegral.integral_of_le ht.1, one_div] at h ⊢
  linarith

/-- Post-limit energy estimate under the Gårding lower bound

`theta ‖v‖_V² ≤ B(t)(v,v) + gamma ‖v‖_H²`.

For an `L²(a,b;V*)` forcing, the Lions–Magenes energy identity and Young's
inequality give

`(1/2) ‖u(t)‖_H² + (theta/2) ∫ₐᵗ ‖u(s)‖_V² ds
    ≤ (1/2) ‖u(a)‖_H²
      + (1/(2 theta)) ∫ₐᵗ ‖ell(s)‖_{V*}² ds
      + gamma ∫ₐᵗ ‖u(s)‖_H² ds`.

The final pivot-space integral is written using the continuous
Lions–Magenes representative.  This is important at the theorem boundary:
the original trajectory is only an `L²(V)` equivalence class, whereas the
Gårding correction is naturally an `H`-norm.  The estimate is the standard
starting point for Grönwall stability and uniqueness when lower-order terms
prevent the unshifted form from being nonnegative. -/
theorem ContinuousPivotEvolutionOn.garding_energy_bound_L2
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (E : ContinuousPivotEvolutionOn T (fun t ↦ u t) (fun t ↦ g t) a b)
    {uInit : H} (hEa : E.representative a = uInit)
    (hresidual : (g : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict
      (Set.Ioc a b)] fun t ↦ ell t - B t (u t))
    {theta gamma : ℝ} (htheta : 0 < theta)
    (hGarding : ∀ t ∈ Set.Icc a b, ∀ w : V,
      theta * ‖w‖ ^ 2 ≤
        B t w w + gamma * ‖T.inclusion w‖ ^ 2)
    (hab : a ≤ b) :
    ∀ t ∈ Set.Icc a b,
      (1 / 2 : ℝ) * ‖E.representative t‖ ^ 2 +
          (theta / 2) * (∫ s in a..t, ‖u s‖ ^ 2) ≤
        (1 / 2 : ℝ) * ‖uInit‖ ^ 2 +
          (1 / (2 * theta)) * (∫ s in a..t, ‖ell s‖ ^ 2) +
          gamma * (∫ s in a..t, ‖E.representative s‖ ^ 2) := by
  intro t ht
  have hmeasure : volume.restrict (Ioc a t) ≤ volume.restrict (Ioc a b) :=
    Measure.restrict_mono_set _ (Ioc_subset_Ioc_right ht.2)
  have hsub : Icc a t ⊆ uIcc a b := by
    rw [uIcc_of_le hab]
    exact Icc_subset_Icc_right ht.2
  have hellSq := ((Lp.memLp ell).integrable_norm_pow two_ne_zero).mono_measure hmeasure
  have hrepSq : IntegrableOn (fun r ↦ ‖E.representative r‖ ^ 2) (Ioc a t) :=
    ((E.continuousOn.mono hsub).norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hrepAE : E.representative =ᵐ[volume.restrict (Ioc a t)] fun r ↦ T.inclusion (u r) :=
    E.ae_eq_inclusion.filter_mono
      (ae_mono (Measure.restrict_mono_set _ (Ioc_subset_Icc_self.trans hsub)))
  have h := energy_bound_of_ae_le (θ := theta) E hEa hab ht
    ((hellSq.div_const (2 * theta)).add (hrepSq.const_mul gamma)) <| by
    filter_upwards [hresidual.filter_mono (ae_mono hmeasure), hrepAE,
      ae_restrict_mem measurableSet_Ioc] with r hgr hrep hr
    have hellNorm : ell r (u r) ≤ ‖ell r‖ * ‖u r‖ :=
      (le_abs_self _).trans ((ell r).le_opNorm (u r))
    have hyoung := mul_le_sq_div_add_mul_sq_half htheta ‖ell r‖ ‖u r‖
    have hLower := hGarding r ⟨hr.1.le, hr.2.trans ht.2⟩ (u r)
    rw [Pi.add_apply, hgr, sub_apply, hrep]
    nlinarith
  simp only [Pi.add_apply] at h
  rw [integral_add (hellSq.div_const _) (hrepSq.const_mul _), integral_div,
    div_eq_inv_mul _ (2 * theta), integral_const_mul] at h
  simp only [intervalIntegral.integral_of_le ht.1, one_div] at h ⊢
  linarith

/-- Explicit Grönwall consequence of the Gårding energy estimate.

Suppose a continuous pivot representative satisfies the energy inequality

`(1/2) ‖u(t)‖_H² + (theta/2) ∫ₐᵗ ‖u‖_V²
    ≤ (1/2) ‖u(a)‖_H²
      + (1/(2 theta)) ∫ₐᵗ ‖ell‖_{V*}²
      + gamma ∫ₐᵗ ‖u‖_H²`.

When `theta > 0` and `gamma ≥ 0`, its pivot energy obeys the explicit bound

`‖u(t)‖_H² ≤
  (‖u(a)‖_H² + theta⁻¹ ‖ell‖²_{L²(a,b;V*)})
    exp (2 gamma (t-a))`.

The proof first enlarges the forcing integral from `[a,t]` to `[a,b]`,
drops the nonnegative energy-space term, and then applies the scalar
integral Grönwall theorem.  It applies to any construction with the same
energy inequality. -/
theorem ContinuousPivotEvolutionOn.pivot_norm_sq_le_exp_of_garding_energy_bound_L2
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {ell : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (E : ContinuousPivotEvolutionOn T (fun t ↦ u t) (fun t ↦ g t) a b)
    {uInit : H} {theta gamma : ℝ}
    (htheta : 0 < theta) (hgamma : 0 ≤ gamma) (hab : a ≤ b)
    (henergy : ∀ t ∈ Set.Icc a b,
      (1 / 2 : ℝ) * ‖E.representative t‖ ^ 2 +
          (theta / 2) * (∫ s in a..t, ‖u s‖ ^ 2) ≤
        (1 / 2 : ℝ) * ‖uInit‖ ^ 2 +
          (1 / (2 * theta)) * (∫ s in a..t, ‖ell s‖ ^ 2) +
          gamma * (∫ s in a..t, ‖E.representative s‖ ^ 2)) :
    ∀ t ∈ Set.Icc a b,
      ‖E.representative t‖ ^ 2 ≤
        (‖uInit‖ ^ 2 +
            (1 / theta) * (∫ s in a..b, ‖ell s‖ ^ 2)) *
          Real.exp ((2 * gamma) * (t - a)) := by
  exact norm_sq_le_exp_of_garding_energy_bound
    (by simpa only [Set.uIcc_of_le hab] using E.continuousOn)
    (Lp.memLp ell) htheta hgamma hab henergy

/-- Endpoint regularity and the Gårding energy estimate for an integrated
weak solution with `L²(a,b;V*)` forcing.

This is the theorem-level form used in the Evans existence and stability
argument: it returns the weak derivative, the continuous pivot
representative with its prescribed initial trace, the residual identity, and
the energy inequality on every prefix `[a,t]`. -/
theorem IsGelfandIntegratedWeakSolution.exists_continuousPivotEvolutionOn_with_garding_bound_L2
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))} {uInit : H}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    {theta gamma : ℝ} (htheta : 0 < theta)
    (hGarding : ∀ t ∈ Set.Icc a b, ∀ w : V,
      theta * ‖w‖ ^ 2 ≤
        B t w w + gamma * ‖T.inclusion w‖ ^ 2)
    (hu : IsGelfandIntegratedWeakSolution T B (fun t ↦ ell t) u uInit)
    (hab : a < b) :
    ∃ g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)),
      ∃ E : ContinuousPivotEvolutionOn T (fun t ↦ u t) (fun t ↦ g t) a b,
        HasGelfandWeakTimeDerivativeOn T u g ∧
        E.representative a = uInit ∧
        (g : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Set.Ioc a b)]
          (fun t ↦ ell t - B t (u t)) ∧
        ∀ t ∈ Set.Icc a b,
          (1 / 2 : ℝ) * ‖E.representative t‖ ^ 2 +
              (theta / 2) * (∫ s in a..t, ‖u s‖ ^ 2) ≤
            (1 / 2 : ℝ) * ‖uInit‖ ^ 2 +
              (1 / (2 * theta)) * (∫ s in a..t, ‖ell s‖ ^ 2) +
              gamma * (∫ s in a..t, ‖E.representative s‖ ^ 2) := by
  obtain ⟨g, E, hgweak, hEa, hresidual⟩ :=
    hu.exists_continuousPivotEvolutionOn_initial_L2 hBmeas MB hBbound hab
  exact ⟨g, E, hgweak, hEa, hresidual,
    E.garding_energy_bound_L2 hEa hresidual htheta hGarding hab.le⟩

/-- Continuous-dependence energy estimate for two integrated weak solutions.

If `u₁` and `u₂` solve the same nonautonomous operator equation with
different `L²(V*)` forcings and different pivot-space initial data, their
difference has a continuous `H`-representative `E` satisfying

`(1/2) ‖E(t)‖_H² + (theta/2) ∫ₐᵗ ‖u₁-u₂‖_V²
    ≤ (1/2) ‖uInit₁-uInit₂‖_H²
      + (1/(2 theta)) ∫ₐᵗ ‖ell₁-ell₂‖_{V*}²
      + gamma ∫ₐᵗ ‖E‖_H²`.

This is the quantitative form behind uniqueness. A scalar Grönwall step removes the last
integral when an explicit exponential bound is wanted. -/
theorem IsGelfandIntegratedWeakSolution.difference_garding_energy_bound_L2
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell₁ ell₂ : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    {u₁ u₂ : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {uInit₁ uInit₂ : H}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    {theta gamma : ℝ} (htheta : 0 < theta)
    (hGarding : ∀ t ∈ Set.Icc a b, ∀ w : V,
      theta * ‖w‖ ^ 2 ≤
        B t w w + gamma * ‖T.inclusion w‖ ^ 2)
    (h₁ : IsGelfandIntegratedWeakSolution T B (fun t ↦ ell₁ t) u₁ uInit₁)
    (h₂ : IsGelfandIntegratedWeakSolution T B (fun t ↦ ell₂ t) u₂ uInit₂)
    (hab : a < b) :
    ∃ g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)),
      ∃ E : ContinuousPivotEvolutionOn T
          (fun t ↦ (u₁ - u₂) t) (fun t ↦ g t) a b,
        HasGelfandWeakTimeDerivativeOn T (u₁ - u₂) g ∧
        E.representative a = uInit₁ - uInit₂ ∧
        (g : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Set.Ioc a b)]
          (fun t ↦ (ell₁ - ell₂) t - B t ((u₁ - u₂) t)) ∧
        ∀ t ∈ Set.Icc a b,
          (1 / 2 : ℝ) * ‖E.representative t‖ ^ 2 +
              (theta / 2) * (∫ s in a..t, ‖(u₁ - u₂) s‖ ^ 2) ≤
            (1 / 2 : ℝ) * ‖uInit₁ - uInit₂‖ ^ 2 +
              (1 / (2 * theta)) *
                (∫ s in a..t, ‖(ell₁ - ell₂) s‖ ^ 2) +
              gamma * (∫ s in a..t, ‖E.representative s‖ ^ 2) := by
  have hw : IsGelfandIntegratedWeakSolution T B
      (fun t ↦ (ell₁ - ell₂) t) (u₁ - u₂) (uInit₁ - uInit₂) :=
    (h₁.sub_L2 hBmeas MB hBbound h₂).congr_forcing_ae (Lp.coeFn_sub ell₁ ell₂).symm
  exact hw.exists_continuousPivotEvolutionOn_with_garding_bound_L2
    hBmeas MB hBbound htheta hGarding hab

/-- Coercive continuous dependence in the natural Bochner norms.

For two solutions with the same initial datum, uniform coercivity gives the
dimension-free estimate

`‖u₁ - u₂‖_{L²(a,b;V)} ≤ C⁻¹ ‖ell₁ - ell₂‖_{L²(a,b;V*)}`.

This is the completion estimate used to extend the Galerkin construction
from continuous loads to arbitrary `L²(a,b;V*)` loads.  In particular, no
pointwise representative or uniform bound on either forcing appears in the
statement. -/
theorem IsGelfandIntegratedWeakSolution.norm_sub_le_of_coercive_L2
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell₁ ell₂ : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    {u₁ u₂ : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {uInit : H}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    {C : ℝ} (hC : 0 < C)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (h₁ : IsGelfandIntegratedWeakSolution T B (fun t ↦ ell₁ t) u₁ uInit)
    (h₂ : IsGelfandIntegratedWeakSolution T B (fun t ↦ ell₂ t) u₂ uInit)
    (hab : a < b) :
    ‖u₁ - u₂‖ ≤ (1 / C) * ‖ell₁ - ell₂‖ := by
  obtain ⟨g, E, -, -, -, henergy⟩ := h₁.difference_garding_energy_bound_L2 (gamma := 0) hBmeas
    MB hBbound hC (fun t ht w ↦ by simpa using hcoercive t ht w) h₂ hab
  have hbound := henergy b ⟨hab.le, le_rfl⟩
  simp only [intervalIntegral.integral_of_le hab.le, ← Lp.norm_sq_eq_integral_norm_sq, sub_self,
    norm_zero, zero_mul, add_zero] at hbound
  have hcore : C / 2 * ‖u₁ - u₂‖ ^ 2 ≤ 1 / (2 * C) * ‖ell₁ - ell₂‖ ^ 2 := by
    nlinarith [sq_nonneg ‖E.representative b‖]
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  calc ‖u₁ - u₂‖ ^ 2 = 2 / C * (C / 2 * ‖u₁ - u₂‖ ^ 2) := by field_simp
    _ ≤ 2 / C * (1 / (2 * C) * ‖ell₁ - ell₂‖ ^ 2) := by gcongr
    _ = (1 / C * ‖ell₁ - ell₂‖) ^ 2 := by field_simp

/-- Coercive energy estimate for an `L²(a,b;V)` trajectory with a continuous
`H`-valued representative and weak derivative equal a.e. to `ell - B u`.
Uniform coercivity with `C > 0` and the pointwise forcing bound `‖ell(t)‖ ≤ M`
give

`(1/2)‖u(t)‖_H² + (C/2)∫ₐᵗ ‖u(s)‖_V² ds
    ≤ (1/2)‖u(a)‖_H² + M²(t-a)/(2C)`.

The endpoint values in this estimate are those of `E.representative`, with
`E.representative a = uInit`. This is the weak-solution version of
`gelfandGalerkin_integrated_energy_bound` and the a priori estimate in
Evans, *Partial Differential Equations*, 2nd ed., §7.1.2. -/
theorem ContinuousPivotEvolutionOn.coercive_energy_bound
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (E : ContinuousPivotEvolutionOn T (fun t ↦ u t) (fun t ↦ g t) a b)
    {uInit : H} (hEa : E.representative a = uInit)
    (hresidual : (g : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict
      (Set.Ioc a b)] fun t ↦ ell t - B t (u t))
    {C M : ℝ} (hC : 0 < C) (hM : 0 ≤ M)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (hell : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ M)
    (hab : a ≤ b) :
    ∀ t ∈ Set.Icc a b,
      (1 / 2 : ℝ) * ‖E.representative t‖ ^ 2 +
          (C / 2) * ∫ s in a..t, ‖u s‖ ^ 2 ≤
        (1 / 2 : ℝ) * ‖uInit‖ ^ 2 +
          (M ^ 2 / (2 * C)) * (t - a) := by
  intro t ht
  have hmeasure : volume.restrict (Ioc a t) ≤ volume.restrict (Ioc a b) :=
    Measure.restrict_mono_set _ (Ioc_subset_Ioc_right ht.2)
  have h := energy_bound_of_ae_le (θ := C) E hEa hab ht
    (integrableOn_const (C := M ^ 2 / (2 * C)) measure_Ioc_lt_top.ne) <| by
    filter_upwards [hresidual.filter_mono (ae_mono hmeasure), ae_restrict_mem measurableSet_Ioc]
      with r hgr hr
    have hellNorm : ell r (u r) ≤ ‖ell r‖ * ‖u r‖ :=
      (le_abs_self _).trans ((ell r).le_opNorm (u r))
    have hyoung := mul_le_sq_div_add_mul_sq_half hC ‖ell r‖ ‖u r‖
    have hdiv : ‖ell r‖ ^ 2 / (2 * C) ≤ M ^ 2 / (2 * C) := div_le_div_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg _) hM).2 (hell r ⟨hr.1.le, hr.2.trans ht.2⟩)) (by positivity)
    rw [hgr, sub_apply]
    nlinarith [hcoercive r ⟨hr.1.le, hr.2.trans ht.2⟩ (u r),
      mul_nonneg hC.le (sq_nonneg ‖u r‖)]
  have hconst : ∫ _ in Ioc a t, M ^ 2 / (2 * C) = M ^ 2 / (2 * C) * (t - a) := by
    rw [← intervalIntegral.integral_of_le ht.1]
    cas
  rw [hconst] at h
  simp only [intervalIntegral.integral_of_le ht.1]
  linarith

/-- Endpoint regularity and the coercive a priori estimate for an
integrated weak solution.  This is the final-solution counterpart of the
uniform Galerkin estimate in Evans §7.1.2: the returned representative has
the prescribed initial value and satisfies the estimate on every prefix
`[a,t]` of the time interval. -/
theorem IsGelfandIntegratedWeakSolution.exists_continuousPivotEvolutionOn_with_energy_bound
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))} {uInit : H}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (hellCont : ContinuousOn ell (Set.Icc a b))
    {C M : ℝ} (hC : 0 < C) (hM : 0 ≤ M)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (hellBound : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ M)
    (hu : IsGelfandIntegratedWeakSolution T B ell u uInit)
    (hab : a < b) :
    ∃ g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)),
      ∃ E : ContinuousPivotEvolutionOn T (fun t ↦ u t) (fun t ↦ g t) a b,
        HasGelfandWeakTimeDerivativeOn T u g ∧
        E.representative a = uInit ∧
        ∀ t ∈ Set.Icc a b,
          (1 / 2 : ℝ) * ‖E.representative t‖ ^ 2 +
              (C / 2) * ∫ s in a..t, ‖u s‖ ^ 2 ≤
            (1 / 2 : ℝ) * ‖uInit‖ ^ 2 +
              (M ^ 2 / (2 * C)) * (t - a) := by
  obtain ⟨g, E, hgweak, hEa, hresidual⟩ :=
    hu.exists_continuousPivotEvolutionOn_initial hBmeas MB hBbound hellCont hab
  exact ⟨g, E, hgweak, hEa, E.coercive_energy_bound hEa hresidual hC hM hcoercive hellBound hab.le⟩

end GelfandWeakTimeDerivative

end PDE.Analysis.Evolution
