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
# Evans's autonomous Galerkin energy estimate

For an autonomous symmetric principal form `A`, testing the Galerkin equation with the
coefficient derivative gives

`A(uₘ,uₘ') = (1/2) d/dt A(uₘ,uₘ)`.

After controlling the pivot load and lower-order remainder, the result bounds
the Galerkin velocity in `L²(H)` and the trajectory in `L∞(V)`, with constants
independent of the trial dimension. The trajectories are only absolutely
continuous; all differential identities are used almost everywhere. Evans proves the same
finite-dimensional estimate in steps 1 and 2 of the proof of Theorem 5 in §7.1.3.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.3, proof of Theorem 5, steps 1-2 (the bound for
  `u_m'` in `L²(0, T; L²(U))` and the estimate (48)). <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

/-! ## Autonomous symmetric energy estimate -/

section AutonomousSymmetricEnergy

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Testing the projected equation by the velocity controls the derivative of a
symmetric principal energy; the two mixed products are estimated by Young's inequality. -/
private theorem principal_energy_deriv_le
    (T : GelfandTriple (V := V) (H := H))
    (A R : V →L[ℝ] StrongDual ℝ V) (u : ℝ → V) (du : V) (f : H) (t L : ℝ)
    (hu : HasDerivAt u du t)
    (hA_symm : ∀ v w : V, A v w = A w v)
    (hRabs : |R (u t) du| ≤ L * ‖u t‖ * ‖T.inclusion du‖)
    (heqTest : inner ℝ (T.inclusion du) (T.inclusion du) +
      (A + R) (u t) du = T.pivotToDual f du) :
    deriv (fun r ↦ (1 / 2 : ℝ) * A (u r) (u r)) t +
        (1 / 2 : ℝ) * ‖T.inclusion du‖ ^ 2 ≤ ‖f‖ ^ 2 + L ^ 2 * ‖u t‖ ^ 2 := by
  have hEderiv : HasDerivAt (fun r ↦ (1 / 2 : ℝ) * A (u r) (u r)) (A (u t) du) t :=
    (((A.hasFDerivAt.comp_hasDerivAt t hu).clm_apply hu).const_mul (1 / 2 : ℝ)).congr_deriv
      (by rw [hA_symm du (u t), Function.comp_apply]; ring)
  have hforce : inner ℝ f (T.inclusion du) ≤ ‖f‖ * ‖T.inclusion du‖ := real_inner_le_norm _ _
  have hRneg : -(R (u t) du) ≤ L * ‖u t‖ * ‖T.inclusion du‖ := (neg_le_abs _).trans hRabs
  have hYoungF :=
    mul_le_sq_div_add_mul_sq_half (by norm_num : (0 : ℝ) < 1 / 2) ‖f‖ ‖T.inclusion du‖
  have hYoungR :=
    mul_le_sq_div_add_mul_sq_half (by norm_num : (0 : ℝ) < 1 / 2) (L * ‖u t‖) ‖T.inclusion du‖
  rw [hEderiv.deriv]
  simp only [add_apply, GelfandTriple.pivotToDual_apply, real_inner_self_eq_norm_sq] at heqTest
  norm_num at hYoungF hYoungR
  linarith

/-- If `e` is absolutely continuous and `e' + d ≤ f` almost everywhere, then
`e(b) + ∫_a^b d ≤ e(a) + ∫_a^b f`. -/
private theorem energy_add_integral_le_of_deriv_add_le
    {e d f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (he : AbsolutelyContinuousOnInterval e a b)
    (hd : IntervalIntegrable d volume a b) (hf : IntervalIntegrable f volume a b)
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioc a b), deriv e t + d t ≤ f t) :
    e b + (∫ t in a..b, d t) ≤ e a + ∫ t in a..b, f t := by
  have hmono := intervalIntegral.integral_mono_ae_restrict hab
    (he.intervalIntegrable_deriv.add hd) hf
    (by
      rw [← restrict_Ioc_eq_restrict_Icc]
      exact hderiv)
  rw [intervalIntegral.integral_add he.intervalIntegrable_deriv hd,
    he.integral_deriv_eq_sub] at hmono
  linarith

/-- The velocity test of the Galerkin equation gives the principal-energy
inequality on the same full-measure set as the coefficient derivative. -/
private theorem principal_energy_deriv_le_ae
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    (A : V →L[ℝ] StrongDual ℝ V) (R : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b C M L : ℝ} {u₀ : S}
    (f : Lp H 2 (volume.restrict (Ioc a b)))
    (G : AEGelfandGalerkinApproximation T S
      (fun t ↦ A + R t) (fun t ↦ T.pivotToDual (f t)) a b C M u₀)
    (hA_symm : ∀ u v : V, A u v = A v u)
    (hR : ∀ t ∈ Icc a b, ∀ u v : V, |R t u v| ≤ L * ‖u‖ * ‖T.inclusion v‖) :
    ∀ᵐ t ∂volume.restrict (Ioc a b),
      deriv (fun s ↦ (1 / 2 : ℝ) * A (G.trajectory s : V) (G.trajectory s : V)) t +
          (1 / 2 : ℝ) * ‖T.inclusion (G.coefficientDerivative t : V)‖ ^ 2 ≤
        ‖f t‖ ^ 2 + L ^ 2 * ‖(G.trajectory t : V)‖ ^ 2 := by
  filter_upwards [G.derivative_ae, G.equation_ae, ae_restrict_mem measurableSet_Ioc]
    with t hderiv heq ht
  exact principal_energy_deriv_le T A (R t) (fun s ↦ (G.trajectory s : V))
    (G.coefficientDerivative t : V) (f t) t L
    (S.subtypeL.hasFDerivAt.comp_hasDerivAt t hderiv) hA_symm
    (hR t (Ioc_subset_Icc_self ht) _ _) (heq (G.coefficientDerivative t))

/--
The dimension-independent Galerkin estimate of steps 1 and 2 in the proof of Evans §7.1.3,
Theorem 5.

Write the time-dependent form as an autonomous symmetric principal part plus
a lower-order remainder,

`B(t) = A + R(t)`.

Assume the forcing is represented in the pivot space and the remainder has
the mixed bound

`|R(t)(u,v)| ≤ L ‖u‖_V ‖Jv‖_H`.

Testing the almost-everywhere Galerkin equation with the coefficient
derivative and using symmetry of `A` gives, on every prefix `[a,t]`,

`(1/2) A(u(t),u(t)) + (1/2) ∫ ‖Ju'‖²`
`  ≤ (1/2) A(u(a),u(a)) + ∫ (‖f‖² + L² ‖u‖²)`.

The constants are independent of the trial space. With coercivity of `A` and the basic
Galerkin estimate, this gives uniform `L∞(a,b;V)` and `L²(a,b;H)`-derivative bounds.
-/
theorem AEGelfandGalerkinApproximation.improved_energy_estimate_of_autonomous_symmetric_principal
    (T : GelfandTriple (V := V) (H := H))
    (S : Submodule ℝ V)
    (A : V →L[ℝ] StrongDual ℝ V)
    (R : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b C M L : ℝ} {u₀ : S}
    (f : Lp H 2 (volume.restrict (Set.Ioc a b)))
    (G : AEGelfandGalerkinApproximation T S
      (fun t ↦ A + R t) (fun t ↦ T.pivotToDual (f t))
      a b C M u₀)
    (hab : a ≤ b)
    (hA_symm : ∀ u v : V, A u v = A v u)
    (hR : ∀ t ∈ Set.Icc a b, ∀ u v : V,
      |R t u v| ≤ L * ‖u‖ * ‖T.inclusion v‖) :
    ∀ t ∈ Set.Icc a b,
      (1 / 2 : ℝ) * A (G.trajectory t : V) (G.trajectory t : V) +
          (1 / 2 : ℝ) * ∫ s in a..t,
            ‖T.inclusion (G.coefficientDerivative s : V)‖ ^ 2 ≤
        (1 / 2 : ℝ) * A (G.trajectory a : V) (G.trajectory a : V) +
          ∫ s in a..t,
            (‖f s‖ ^ 2 + L ^ 2 * ‖(G.trajectory s : V)‖ ^ 2) := by
  intro t ht
  let μat := volume.restrict (Set.Ioc a t)
  let uV : ℝ → V := fun s ↦ (G.trajectory s : V)
  let duH : ℝ → H := fun s ↦ T.inclusion (G.coefficientDerivative s : V)
  let E : ℝ → ℝ := fun s ↦ (1 / 2 : ℝ) * A (uV s) (uV s)
  have hmeasure : μat ≤ volume.restrict (Set.Ioc a b) :=
    Measure.restrict_mono_set _ fun _ hs ↦ ⟨hs.1, hs.2.trans ht.2⟩
  have huVAC : AbsolutelyContinuousOnInterval uV a b :=
    (S.subtypeL.lipschitzWith.comp_absolutelyContinuousOnInterval G.trajectory_ac).congr
      fun _ _ ↦ rfl
  have hEACat : AbsolutelyContinuousOnInterval E a t :=
    ((AbsolutelyContinuousOnInterval.clm_apply
      (A.lipschitzWith.comp_absolutelyContinuousOnInterval huVAC) huVAC).const_mul
        (1 / 2 : ℝ)).mono (uIcc_subset_uIcc_left (by simpa only [uIcc_of_le hab] using ht))
  have hduSq : Integrable (fun s ↦ ‖duH s‖ ^ 2) μat :=
    (((Lp.memLp (G.pivotDerivativeLp T S)).integrable_norm_pow (by norm_num)).mono_measure
      hmeasure).congr (((G.pivotDerivativeLp_apply_ae T S).filter_mono (ae_mono hmeasure)).mono
        fun _ hs ↦ congrArg (‖·‖ ^ 2) hs)
  have huSq : Integrable (fun s ↦ ‖uV s‖ ^ 2) μat :=
    (((Lp.memLp (G.ambientTrajectoryLp hab)).integrable_norm_pow (by norm_num)).mono_measure
      hmeasure).congr (((G.ambientTrajectoryLp_apply_ae hab).filter_mono (ae_mono hmeasure)).mono
        fun _ hs ↦ congrArg (‖·‖ ^ 2) hs)
  have hfSq : Integrable (fun s ↦ ‖f s‖ ^ 2) μat :=
    ((Lp.memLp f).integrable_norm_pow (by norm_num)).mono_measure hmeasure
  have hpoint : ∀ᵐ s ∂μat,
      deriv E s + (1 / 2 : ℝ) * ‖duH s‖ ^ 2 ≤ ‖f s‖ ^ 2 + L ^ 2 * ‖uV s‖ ^ 2 :=
    (principal_energy_deriv_le_ae T S A R f G hA_symm hR).filter_mono (ae_mono hmeasure)
  simpa only [intervalIntegral.integral_const_mul, Pi.add_apply, E, uV, duH] using
    energy_add_integral_le_of_deriv_add_le ht.1 hEACat
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).2 (hduSq.const_mul _))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).2 (hfSq.add (huSq.const_mul _)))
      hpoint

/--
Bochner-norm form of the improved derivative estimate.

Assuming the autonomous principal form is nonnegative, the terminal principal
energy can be discarded.  The resulting estimate is

`‖J uₘ'‖²_{L²(H)} ≤ A(uₘ(a),uₘ(a))
  + 2 ∫ (‖f‖² + L² ‖uₘ‖²)`,

which does not depend on the trial dimension.
-/
theorem AEGelfandGalerkinApproximation.norm_pivotDerivativeLp_sq_le
    (T : GelfandTriple (V := V) (H := H))
    (S : Submodule ℝ V)
    (A : V →L[ℝ] StrongDual ℝ V)
    (R : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b C M L : ℝ} {u₀ : S}
    (f : Lp H 2 (volume.restrict (Set.Ioc a b)))
    (G : AEGelfandGalerkinApproximation T S
      (fun t ↦ A + R t) (fun t ↦ T.pivotToDual (f t))
      a b C M u₀)
    (hab : a ≤ b)
    (hA_symm : ∀ u v : V, A u v = A v u)
    (hA_nonneg : ∀ u : V, 0 ≤ A u u)
    (hR : ∀ t ∈ Set.Icc a b, ∀ u v : V,
      |R t u v| ≤ L * ‖u‖ * ‖T.inclusion v‖) :
    ‖G.pivotDerivativeLp T S‖ ^ 2 ≤
      A (u₀ : V) (u₀ : V) +
        2 * ∫ s in a..b,
          (‖f s‖ ^ 2 + L ^ 2 * ‖(G.trajectory s : V)‖ ^ 2) := by
  have hmain := G.improved_energy_estimate_of_autonomous_symmetric_principal
    T S A R f hab hA_symm hR b ⟨hab, le_rfl⟩
  rw [G.initial] at hmain
  rw [Lp.norm_sq_eq_integral_norm_sq, integral_congr_ae
    ((G.pivotDerivativeLp_apply_ae T S).mono fun _ hs ↦ congrArg (‖·‖ ^ 2) hs),
    ← intervalIntegral.integral_of_le hab]
  linarith [hA_nonneg (G.trajectory b : V)]

/--
Pointwise energy-space bound from the improved estimate. If `C ‖w‖² ≤ A(w, w)` and the
Galerkin state satisfies `‖u‖²_{L²(a,b;V)} ≤ D`, then for every `t ∈ [a, b]`

`‖u(t)‖_V ≤ √((‖A‖ ‖u₀‖² + 2 (‖f‖² + L² D)) / C)`,

uniformly in the trial space.
-/
theorem AEGelfandGalerkinApproximation.norm_trajectory_le_of_principal_coercive
    (T : GelfandTriple (V := V) (H := H))
    (S : Submodule ℝ V)
    (A : V →L[ℝ] StrongDual ℝ V)
    (R : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b C M L D : ℝ} {u₀ : S}
    (f : Lp H 2 (volume.restrict (Set.Ioc a b)))
    (G : AEGelfandGalerkinApproximation T S
      (fun t ↦ A + R t) (fun t ↦ T.pivotToDual (f t))
      a b C M u₀)
    (hab : a ≤ b) (hC : 0 < C)
    (hA_symm : ∀ u v : V, A u v = A v u)
    (hAprincipal : ∀ w : V, C * ‖w‖ ^ 2 ≤ A w w)
    (hR : ∀ t ∈ Set.Icc a b, ∀ u v : V,
      |R t u v| ≤ L * ‖u‖ * ‖T.inclusion v‖)
    (hstateL2 :
      ‖G.ambientTrajectoryLp hab‖ ^ 2 ≤ D) :
    ∀ t ∈ Set.Icc a b,
      ‖(G.trajectory t : V)‖ ≤
        √
          ((‖A‖ * ‖(u₀ : V)‖ ^ 2 +
              2 * (‖f‖ ^ 2 + L ^ 2 * D)) / C) := by
  intro t ht
  let μab := volume.restrict (Set.Ioc a b)
  let μat := volume.restrict (Set.Ioc a t)
  have hmeasure : μat ≤ μab := Measure.restrict_mono_set _ fun _ hs ↦ ⟨hs.1, hs.2.trans ht.2⟩
  have henergy := G.improved_energy_estimate_of_autonomous_symmetric_principal
    T S A R f hab hA_symm hR t ht
  rw [G.initial] at henergy
  have hduNonneg : 0 ≤ ∫ s in a..t, ‖T.inclusion (G.coefficientDerivative s : V)‖ ^ 2 :=
    intervalIntegral.integral_nonneg ht.1 fun _ _ ↦ by positivity
  have hfInt : Integrable (fun s ↦ ‖f s‖ ^ 2) μab :=
    (Lp.memLp f).integrable_norm_pow (by norm_num)
  have huInt : Integrable (fun s ↦ ‖G.ambientTrajectoryLp hab s‖ ^ 2) μab :=
    (Lp.memLp (G.ambientTrajectoryLp hab)).integrable_norm_pow (by norm_num)
  have hprefix : (∫ s in a..t, (‖f s‖ ^ 2 + L ^ 2 * ‖(G.trajectory s : V)‖ ^ 2)) ≤
      ‖f‖ ^ 2 + L ^ 2 * D := by
    have hcoe : (fun s ↦ ‖f s‖ ^ 2 + L ^ 2 * ‖(G.trajectory s : V)‖ ^ 2) =ᵐ[μat]
        fun s ↦ ‖f s‖ ^ 2 + L ^ 2 * ‖G.ambientTrajectoryLp hab s‖ ^ 2 := by
      filter_upwards [(G.ambientTrajectoryLp_apply_ae hab).filter_mono (ae_mono hmeasure)]
        with s hs
      rw [hs]
    rw [intervalIntegral.integral_of_le ht.1, integral_congr_ae hcoe]
    calc (∫ s, (‖f s‖ ^ 2 + L ^ 2 * ‖G.ambientTrajectoryLp hab s‖ ^ 2) ∂μat) ≤
          ∫ s, (‖f s‖ ^ 2 + L ^ 2 * ‖G.ambientTrajectoryLp hab s‖ ^ 2) ∂μab :=
        integral_mono_measure hmeasure (.of_forall fun s ↦ by positivity)
          (hfInt.add (huInt.const_mul _))
      _ = ‖f‖ ^ 2 + L ^ 2 * ‖G.ambientTrajectoryLp hab‖ ^ 2 := by
        rw [integral_add hfInt (huInt.const_mul _), integral_const_mul,
          ← Lp.norm_sq_eq_integral_norm_sq, ← Lp.norm_sq_eq_integral_norm_sq]
      _ ≤ ‖f‖ ^ 2 + L ^ 2 * D := by gcongr
  have hAinitial : A (u₀ : V) (u₀ : V) ≤ ‖A‖ * ‖(u₀ : V)‖ ^ 2 :=
    (le_abs_self _).trans ((A.le_opNorm₂ _ _).trans_eq (by ring))
  exact Real.le_sqrt_of_sq_le ((le_div_iff₀ hC).2
    (by linarith [hAprincipal (G.trajectory t : V)]))

end AutonomousSymmetricEnergy

end PDE.Analysis.Evolution
