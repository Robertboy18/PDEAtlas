/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.LionsMagenes.EnergyBound
public import PDE.Analysis.Evolution.Bochner.Duality
public import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Uniform pivot estimates for dissipative weak evolutions

A nonnegative multiple of a dissipative energy-to-dual operator costs nothing
in the pivot energy estimate. The remaining drift is controlled by a one-sided
pivot bound, and the inhomogeneity by its Bochner L² norm. This formulation keeps
the estimate uniform as the dissipative coefficient tends to zero.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped InnerProductSpace

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The dissipative term drops out of a forced pivot energy estimate. -/
theorem GelfandTriple.dissipative_pairing_le
    (T : GelfandTriple (V := V) (H := H))
    (L : V →L[ℝ] StrongDual ℝ V) (C : V →L[ℝ] H)
    {ε K : ℝ} (hε : 0 ≤ ε) (v : V) (f : H)
    (hL : L v v ≤ 0)
    (hC : 2 * ⟪C v, T.inclusion v⟫_ℝ ≤ K * ‖T.inclusion v‖ ^ 2) :
    2 * (ε • L v + T.pivotToDual (f + C v)) v ≤
      (K + 1) * ‖T.inclusion v‖ ^ 2 + ‖f‖ ^ 2 := by
  have hforce := real_inner_le_norm f (T.inclusion v)
  have hyoung := sq_nonneg (‖f‖ - ‖T.inclusion v‖)
  have hdiff := mul_nonpos_of_nonneg_of_nonpos hε hL
  simp only [add_apply, smul_apply,
    smul_eq_mul, GelfandTriple.pivotToDual_apply, inner_add_left]
  nlinarith

/-- A dissipative weak evolution has a uniform-in-time pivot bound depending
on the initial pivot trace and the L² forcing, independently of diffusivity. -/
theorem ContinuousPivotEvolutionOn.norm_le_exp_mul_of_dissipative_equation
    [CompleteSpace V]
    {T : GelfandTriple (V := V) (H := H)} {a b ε K : ℝ}
    (hab : a ≤ b) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (u : Lp V 2 (volume.restrict (Ioc a b)))
    (g : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b)))
    (f : Lp H 2 (volume.restrict (Ioc a b)))
    (E : ContinuousPivotEvolutionOn T u g a b)
    (L : V →L[ℝ] StrongDual ℝ V) (C : ℝ → V →L[ℝ] H)
    (hL : ∀ v, L v v ≤ 0)
    (hC : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v,
      2 * ⟪C t v, T.inclusion v⟫_ℝ ≤ K * ‖T.inclusion v‖ ^ 2)
    (heq : ∀ᵐ t ∂volume.restrict (Ioc a b),
      g t = ε • L (u t) + T.pivotToDual (f t + C t (u t))) :
    ∀ t ∈ Icc a b, ‖E.representative t‖ ≤
      Real.exp ((K + 1) * (b - a)) * (‖E.representative a‖ + ‖f‖) := by
  have hgu : IntervalIntegrable (fun t ↦ g t (u t)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (integrable_dual_pairing g u)
  have hfi : IntervalIntegrable (fun t ↦ ‖f t‖ ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      ((Lp.memLp f).integrable_norm_pow (by norm_num))
  have hbound : ∀ᵐ t ∂volume.restrict (Ioc a b),
      2 * g t (u t) ≤ (K + 1) * ‖T.inclusion (u t)‖ ^ 2 + ‖f t‖ ^ 2 := by
    filter_upwards [heq, hC] with t ht hCt
    rw [ht]
    exact T.dissipative_pairing_le L (C t) hε (u t) (f t) (hL _) (hCt _)
  have henergy := E.norm_sq_le_mul_exp_of_pairing_le hab hgu hfi
    (Eventually.of_forall fun _ ↦ sq_nonneg _) (by linarith : 0 ≤ K + 1) hbound
  have hintegral : (∫ s in a..b, ‖f s‖ ^ 2) = ‖f‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hab, ← Lp.norm_sq_eq_integral_norm_sq]
  intro t ht
  have he := henergy t ht
  rw [hintegral] at he
  have htime : Real.exp ((K + 1) * (t - a)) ≤ Real.exp ((K + 1) * (b - a)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a)
      (by linarith))
  have hlarge : 1 ≤ Real.exp ((K + 1) * (b - a)) :=
    Real.one_le_exp (mul_nonneg (by linarith) (sub_nonneg.mpr hab))
  have hb := mul_le_mul_of_nonneg_left htime
    (add_nonneg (sq_nonneg ‖E.representative a‖) (sq_nonneg ‖f‖))
  have hx : 0 ≤ ‖E.representative a‖ + ‖f‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hs : ‖E.representative a‖ ^ 2 + ‖f‖ ^ 2 ≤
      (‖E.representative a‖ + ‖f‖) ^ 2 := by
    nlinarith [norm_nonneg (E.representative a), norm_nonneg f]
  have hs' := mul_le_mul_of_nonneg_right hs
    (Real.exp_nonneg ((K + 1) * (b - a)))
  have he' := mul_le_mul_of_nonneg_right
    (show Real.exp ((K + 1) * (b - a)) ≤ Real.exp ((K + 1) * (b - a)) ^ 2 by
      nlinarith) (sq_nonneg (‖E.representative a‖ + ‖f‖))
  have hnonneg := mul_nonneg (Real.exp_nonneg ((K + 1) * (b - a))) hx
  nlinarith [norm_nonneg (E.representative t)]

end PDE.Analysis.Evolution
