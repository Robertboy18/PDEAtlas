/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.ImprovedRegularity.PivotDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import PDE.Analysis.Evolution.Core.EnergyEstimate
import PDE.Analysis.Evolution.Time.AbsoluteContinuity
import PDE.Analysis.MeasureTheory.LpNorm
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Galerkin regularity with time-dependent principal coefficients

Testing a parabolic Galerkin equation with its coefficient derivative controls
the derivative in the pivot Hilbert space. For a symmetric principal form `A(t)`,
the energy derivative contains the additional term `Ȧ(t)(u(t),u(t)) / 2`.
An operator-norm bound on `Ȧ` controls this term by the `L²(V)` state
estimate, with no dependence on the trial dimension.

Evans does this calculation for coefficients that do not depend on `t` (§7.1.3, hypothesis
(45)), so the term with `Ȧ` does not appear there. The principal form `A`
and the Galerkin trajectories are absolutely continuous. The given `Adot` is
the derivative of `A` in operator norm almost everywhere, with `‖Adot(t)‖ ≤ N`
almost everywhere. Absolute continuity is a separate hypothesis from this derivative
identity. The remainder `R` and the Bochner `L²(H)` forcing are not differentiated.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.3, hypothesis (45) and steps 1-2 of the proof of
  Theorem 5 (the same estimate for coefficients independent of `t`).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Testing the Galerkin equation with the coefficient derivative gives the improved
energy estimate for a time-dependent symmetric principal form. The bound `N` on its
time derivative contributes `N / 2` to the coefficient of the state energy. -/
theorem AEGelfandGalerkinApproximation.improved_energy_estimate_of_symmetric_principal
    (T : GelfandTriple (V := V) (H := H))
    (S : Submodule ℝ V)
    (A Adot R : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b C M L N : ℝ} {u₀ : S}
    (f : Lp H 2 (volume.restrict (Ioc a b)))
    (G : AEGelfandGalerkinApproximation T S
      (fun t ↦ A t + R t) (fun t ↦ T.pivotToDual (f t)) a b C M u₀)
    (hab : a ≤ b)
    (hAAC : AbsolutelyContinuousOnInterval A a b)
    (hAderiv : ∀ᵐ t ∂(volume.restrict (Ioc a b)), HasDerivAt A (Adot t) t)
    (hAdot : ∀ᵐ t ∂(volume.restrict (Ioc a b)), ‖Adot t‖ ≤ N)
    (hAsymm : ∀ t ∈ Icc a b, ∀ u v : V, A t u v = A t v u)
    (hR : ∀ t ∈ Icc a b, ∀ u v : V,
      |R t u v| ≤ L * ‖u‖ * ‖T.inclusion v‖) :
    ∀ t ∈ Icc a b,
      (1 / 2 : ℝ) * A t (G.trajectory t : V) (G.trajectory t : V) +
          (1 / 2 : ℝ) * ∫ s in a..t,
            ‖T.inclusion (G.coefficientDerivative s : V)‖ ^ 2 ≤
        (1 / 2 : ℝ) * A a (u₀ : V) (u₀ : V) +
          ∫ s in a..t,
            (‖f s‖ ^ 2 + (L ^ 2 + N / 2) * ‖(G.trajectory s : V)‖ ^ 2) := by
  intro t ht
  let μab := volume.restrict (Ioc a b)
  let μat := volume.restrict (Ioc a t)
  let u : ℝ → V := fun s ↦ (G.trajectory s : V)
  let du : ℝ → V := fun s ↦ (G.coefficientDerivative s : V)
  let v : ℝ → H := fun s ↦ T.inclusion (du s)
  let E : ℝ → ℝ := fun s ↦ (1 / 2 : ℝ) * A s (u s) (u s)
  have hsub : Ioc a t ⊆ Ioc a b := fun _ hs ↦ ⟨hs.1, hs.2.trans ht.2⟩
  have hmeasure : μat ≤ μab := volume.restrict_mono_set hsub
  have huAC : AbsolutelyContinuousOnInterval u a b :=
    (S.subtypeL.lipschitzWith.comp_absolutelyContinuousOnInterval G.trajectory_ac).congr
      fun _ _ ↦ rfl
  have hEACat : AbsolutelyContinuousOnInterval E a t :=
    ((AbsolutelyContinuousOnInterval.clm_apply (AbsolutelyContinuousOnInterval.clm_apply hAAC huAC)
      huAC).const_mul (1 / 2 : ℝ)).mono
        (uIcc_subset_uIcc_left (by simpa only [uIcc_of_le hab] using ht))
  have hvLp : MemLp v 2 μab := (memLp_congr_ae (G.pivotDerivativeLp_apply_ae T S)).1 (Lp.memLp _)
  have huLp : MemLp u 2 μab :=
    (memLp_congr_ae (G.ambientTrajectoryLp_apply_ae hab)).1 (Lp.memLp _)
  have hvSq : Integrable (fun s ↦ ‖v s‖ ^ 2) μat :=
    (hvLp.integrable_norm_pow (by norm_num)).mono_measure hmeasure
  have huSq : Integrable (fun s ↦ ‖u s‖ ^ 2) μat :=
    (huLp.integrable_norm_pow (by norm_num)).mono_measure hmeasure
  have hfSq : Integrable (fun s ↦ ‖f s‖ ^ 2) μat :=
    ((Lp.memLp f).integrable_norm_pow (by norm_num)).mono_measure hmeasure
  have hrhs : Integrable (fun s ↦ ‖f s‖ ^ 2 + (L ^ 2 + N / 2) * ‖u s‖ ^ 2) μat :=
    hfSq.add (huSq.const_mul _)
  have hpoint : ∀ᵐ s ∂μat,
      deriv E s + (1 / 2 : ℝ) * ‖v s‖ ^ 2 ≤
        ‖f s‖ ^ 2 + (L ^ 2 + N / 2) * ‖u s‖ ^ 2 := by
    filter_upwards [G.derivative_ae.filter_mono (ae_mono hmeasure),
      G.equation_ae.filter_mono (ae_mono hmeasure),
      hAderiv.filter_mono (ae_mono hmeasure),
      hAdot.filter_mono (ae_mono hmeasure),
      ae_restrict_mem measurableSet_Ioc] with s hus heq hAs hAds hs
    have hsab : s ∈ Icc a b := Ioc_subset_Icc_self (hsub hs)
    have huderiv : HasDerivAt u (du s) s :=
      S.subtypeL.hasFDerivAt.comp_hasDerivAt s hus
    have hquadDeriv := (hAs.clm_apply huderiv).clm_apply huderiv
    have hEderiv : HasDerivAt E
        ((1 / 2 : ℝ) * Adot s (u s) (u s) + A s (u s) (du s)) s :=
      (hquadDeriv.const_mul (1 / 2 : ℝ)).congr_deriv
        (by rw [add_apply, hAsymm s hsab (du s) (u s)]; ring)
    have hAdEnergy : Adot s (u s) (u s) ≤ N * ‖u s‖ ^ 2 :=
      (le_abs_self _).trans <| ((Adot s).le_opNorm₂ _ _).trans <| by rw [sq, ← mul_assoc]; gcongr
    have heqTest := heq (G.coefficientDerivative s)
    simp only [add_apply, GelfandTriple.pivotToDual_apply,
      real_inner_self_eq_norm_sq] at heqTest
    change ‖v s‖ ^ 2 + (A s (u s) (du s) + R s (u s) (du s)) =
      inner ℝ (f s) (v s) at heqTest
    have hforce : inner ℝ (f s) (v s) ≤ ‖f s‖ * ‖v s‖ := real_inner_le_norm _ _
    have hRneg : -(R s (u s) (du s)) ≤ L * ‖u s‖ * ‖v s‖ :=
      (neg_le_abs _).trans (hR s hsab (u s) (du s))
    have hYoungF :=
      mul_le_sq_div_add_mul_sq_half (by norm_num : (0 : ℝ) < 1 / 2) ‖f s‖ ‖v s‖
    have hYoungR :=
      mul_le_sq_div_add_mul_sq_half (by norm_num : (0 : ℝ) < 1 / 2)
        (L * ‖u s‖) ‖v s‖
    norm_num at hYoungF hYoungR
    rw [hEderiv.deriv]
    linarith
  have hderivInt : Integrable (deriv E) μat :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).1 hEACat.intervalIntegrable_deriv
  have hmono : (∫ s, deriv E s + (1 / 2 : ℝ) * ‖v s‖ ^ 2 ∂μat) ≤
      ∫ s, ‖f s‖ ^ 2 + (L ^ 2 + N / 2) * ‖u s‖ ^ 2 ∂μat :=
    integral_mono_ae (hderivInt.add (hvSq.const_mul (1 / 2 : ℝ))) hrhs hpoint
  have hFTC : (∫ s, deriv E s ∂μat) = E t - E a := by
    rw [← intervalIntegral.integral_of_le ht.1]
    exact hEACat.integral_deriv_eq_sub
  rw [integral_add hderivInt (hvSq.const_mul (1 / 2 : ℝ)), integral_const_mul, hFTC] at hmono
  have hinitial : E a = (1 / 2 : ℝ) * A a (u₀ : V) (u₀ : V) := by simp only [E, u, G.initial]
  rw [hinitial] at hmono
  rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1]
  change E t + (1 / 2 : ℝ) * ∫ s, ‖v s‖ ^ 2 ∂μat ≤
    (1 / 2 : ℝ) * A a (u₀ : V) (u₀ : V) +
      ∫ s, ‖f s‖ ^ 2 + (L ^ 2 + N / 2) * ‖u s‖ ^ 2 ∂μat
  linarith

/-- Nonnegativity of the terminal principal energy gives a bound for the pivot
derivative in Bochner `L²`. The coefficient derivative contributes `N` times the
integrated state energy, independently of the trial dimension. -/
theorem AEGelfandGalerkinApproximation.norm_pivotDerivativeLp_sq_le_of_symmetric_principal
    (T : GelfandTriple (V := V) (H := H))
    (S : Submodule ℝ V)
    (A Adot R : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b C M L N : ℝ} {u₀ : S}
    (f : Lp H 2 (volume.restrict (Ioc a b)))
    (G : AEGelfandGalerkinApproximation T S
      (fun t ↦ A t + R t) (fun t ↦ T.pivotToDual (f t)) a b C M u₀)
    (hab : a ≤ b)
    (hAAC : AbsolutelyContinuousOnInterval A a b)
    (hAderiv : ∀ᵐ t ∂(volume.restrict (Ioc a b)), HasDerivAt A (Adot t) t)
    (hAdot : ∀ᵐ t ∂(volume.restrict (Ioc a b)), ‖Adot t‖ ≤ N)
    (hAsymm : ∀ t ∈ Icc a b, ∀ u v : V, A t u v = A t v u)
    (hA_nonneg : ∀ u : V, 0 ≤ A b u u)
    (hR : ∀ t ∈ Icc a b, ∀ u v : V,
      |R t u v| ≤ L * ‖u‖ * ‖T.inclusion v‖) :
    ‖G.pivotDerivativeLp T S‖ ^ 2 ≤
      A a (u₀ : V) (u₀ : V) +
        2 * ∫ s in a..b,
          (‖f s‖ ^ 2 + (L ^ 2 + N / 2) * ‖(G.trajectory s : V)‖ ^ 2) := by
  have henergy := G.improved_energy_estimate_of_symmetric_principal
    T S A Adot R f hab hAAC hAderiv hAdot hAsymm hR b ⟨hab, le_rfl⟩
  rw [Lp.norm_sq_eq_integral_norm_sq]
  have hae :
      (fun s ↦ ‖G.pivotDerivativeLp T S s‖ ^ 2) =ᵐ[volume.restrict (Ioc a b)]
        fun s ↦ ‖T.inclusion (G.coefficientDerivative s : V)‖ ^ 2 :=
    (G.pivotDerivativeLp_apply_ae T S).fun_comp (fun z : H ↦ ‖z‖ ^ 2)
  rw [integral_congr_ae hae, ← intervalIntegral.integral_of_le hab]
  linarith [hA_nonneg (G.trajectory b : V)]

/-- Principal coercivity converts the nonautonomous energy estimate into a uniform
bound in the energy space, given a squared `L²(V)` state bound `D` such as the basic
coercive estimate. The bound does not depend on the trial dimension. -/
theorem AEGelfandGalerkinApproximation.norm_trajectory_le_of_symmetric_principal_coercive
    (T : GelfandTriple (V := V) (H := H))
    (S : Submodule ℝ V)
    (A Adot R : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b C M L D : ℝ} {N : NNReal} {u₀ : S}
    (f : Lp H 2 (volume.restrict (Ioc a b)))
    (G : AEGelfandGalerkinApproximation T S
      (fun t ↦ A t + R t) (fun t ↦ T.pivotToDual (f t)) a b C M u₀)
    (hab : a ≤ b) (hC : 0 < C)
    (hAAC : AbsolutelyContinuousOnInterval A a b)
    (hAderiv : ∀ᵐ t ∂(volume.restrict (Ioc a b)), HasDerivAt A (Adot t) t)
    (hAdot : ∀ᵐ t ∂(volume.restrict (Ioc a b)), ‖Adot t‖ ≤ N)
    (hAsymm : ∀ t ∈ Icc a b, ∀ u v : V, A t u v = A t v u)
    (hAprincipal : ∀ t ∈ Icc a b, ∀ w : V, C * ‖w‖ ^ 2 ≤ A t w w)
    (hR : ∀ t ∈ Icc a b, ∀ u v : V,
      |R t u v| ≤ L * ‖u‖ * ‖T.inclusion v‖)
    (hstateL2 : ‖G.ambientTrajectoryLp hab‖ ^ 2 ≤ D) :
    ∀ t ∈ Icc a b,
      ‖(G.trajectory t : V)‖ ≤
        √((‖A a‖ * ‖(u₀ : V)‖ ^ 2 +
          2 * (‖f‖ ^ 2 + (L ^ 2 + (N : ℝ) / 2) * D)) / C) := by
  intro t ht
  let μab := volume.restrict (Ioc a b)
  let μat := volume.restrict (Ioc a t)
  let Q : ℝ := L ^ 2 + (N : ℝ) / 2
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hIocSub : Ioc a t ⊆ Ioc a b := fun _ hs ↦ ⟨hs.1, hs.2.trans ht.2⟩
  have hmeasure : μat ≤ μab := volume.restrict_mono_set hIocSub
  have henergy := G.improved_energy_estimate_of_symmetric_principal
    T S A Adot R f hab hAAC hAderiv hAdot hAsymm hR t ht
  have hduNonneg : 0 ≤ ∫ s in a..t, ‖T.inclusion (G.coefficientDerivative s : V)‖ ^ 2 :=
    intervalIntegral.integral_nonneg ht.1 fun _ _ ↦ by positivity
  have hAcurrent : A t (G.trajectory t : V) (G.trajectory t : V) ≤
      A a (u₀ : V) (u₀ : V) +
        2 * ∫ s in a..t, (‖f s‖ ^ 2 + Q * ‖(G.trajectory s : V)‖ ^ 2) := by
    dsimp only [Q]
    linarith
  have hfInt : Integrable (fun s ↦ ‖f s‖ ^ 2) μab :=
    (Lp.memLp f).integrable_norm_pow (by norm_num)
  have huInt : Integrable (fun s ↦ ‖G.ambientTrajectoryLp hab s‖ ^ 2) μab :=
    (Lp.memLp (G.ambientTrajectoryLp hab)).integrable_norm_pow (by norm_num)
  have hsumInt :
      Integrable (fun s ↦ ‖f s‖ ^ 2 + Q * ‖G.ambientTrajectoryLp hab s‖ ^ 2) μab :=
    hfInt.add (huInt.const_mul Q)
  have hprefix : (∫ s in a..t, (‖f s‖ ^ 2 + Q * ‖(G.trajectory s : V)‖ ^ 2)) ≤
      ‖f‖ ^ 2 + Q * D := by
    have hcoe :
        (fun s ↦ ‖f s‖ ^ 2 + Q * ‖(G.trajectory s : V)‖ ^ 2) =ᵐ[μat]
          fun s ↦ ‖f s‖ ^ 2 + Q * ‖G.ambientTrajectoryLp hab s‖ ^ 2 := by
      filter_upwards
        [(G.ambientTrajectoryLp_apply_ae hab).filter_mono (ae_mono hmeasure)] with s hs
      rw [hs]
    rw [intervalIntegral.integral_of_le ht.1, integral_congr_ae hcoe]
    calc
      (∫ s, (‖f s‖ ^ 2 + Q * ‖G.ambientTrajectoryLp hab s‖ ^ 2) ∂μat) ≤
          ∫ s, (‖f s‖ ^ 2 + Q * ‖G.ambientTrajectoryLp hab s‖ ^ 2) ∂μab :=
        integral_mono_measure hmeasure
          (Filter.Eventually.of_forall fun s ↦ by positivity) hsumInt
      _ = ‖f‖ ^ 2 + Q * ‖G.ambientTrajectoryLp hab‖ ^ 2 := by
        rw [integral_add hfInt (huInt.const_mul Q), integral_const_mul,
          ← Lp.norm_sq_eq_integral_norm_sq, ← Lp.norm_sq_eq_integral_norm_sq]
      _ ≤ ‖f‖ ^ 2 + Q * D := by gcongr
  have hAinitial : A a (u₀ : V) (u₀ : V) ≤ ‖A a‖ * ‖(u₀ : V)‖ ^ 2 :=
    (le_abs_self _).trans (((A a).le_opNorm₂ _ _).trans_eq (by ring))
  refine Real.le_sqrt_of_sq_le ((le_div_iff₀ hC).2 ?_)
  change _ ≤ _ + 2 * (_ + Q * D)
  linarith [hAprincipal t ht (G.trajectory t : V)]

end PDE.Analysis.Evolution
