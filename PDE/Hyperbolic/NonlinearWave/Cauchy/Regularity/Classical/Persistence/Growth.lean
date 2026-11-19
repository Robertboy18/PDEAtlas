/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Semilinear.Continuation

/-!
# Finite-time bounds from affine forcing growth

Variation of constants and Grönwall give a uniform state bound when the
forcing has affine growth along the trajectory. The source need not have
affine growth away from that trajectory.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Analysis.Evolution
open scoped NNReal

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Affine forcing growth along a mild solution gives an exponential bound.
Only a semigroup bound on the specified time interval is required. -/
theorem norm_mildSolutionOn_le_of_affine_source {T : StronglyContinuousSemigroup E} {F : C(E, E)}
    {x : E} {τ M : ℝ≥0} {u : C(Icc (0 : ℝ) (τ : ℝ), E)} (hu : T.IsMildSolutionOn F x τ u)
    (hT : ∀ r ∈ Icc (0 : ℝ≥0) τ, ‖T r‖ ≤ M) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ t, ‖F (u t)‖ ≤ C * (1 + ‖u t‖)) :
    ∀ t, 1 + ‖u t‖ ≤ (1 + (M : ℝ) * ‖x‖) * Real.exp (M * C * (t : ℝ)) := by
  let v := IccExtend τ.coe_nonneg u
  let e : ℝ → ℝ := fun t ↦ 1 + ‖v t‖
  have he : Continuous e := continuous_const.add u.continuous.Icc_extend'.norm
  have hi (t : ℝ) (ht : t ∈ Icc (0 : ℝ) τ) :
      e t ≤ (1 + (M : ℝ) * ‖x‖) + (M * C) * ∫ s in (0 : ℝ)..t, e s := by
    have hn := T.norm_duhamel_sub_le_integral (f := fun s ↦ F (v s)) (g := fun _ ↦ 0)
      (F.continuous.comp u.continuous.Icc_extend') continuous_const hT ht (continuous_const.mul he)
      (D := fun s ↦ C * e s) (fun s _ ↦ by
        simpa only [sub_zero, e, v, IccExtend, Function.comp_apply] using
          hF (projIcc 0 (τ : ℝ) τ.coe_nonneg s))
    have hz : T.duhamel (fun _ ↦ (0 : E)) t = 0 := by
      simp [StronglyContinuousSemigroup.duhamel]
    rw [hz, sub_zero, intervalIntegral.integral_const_mul, ← mul_assoc] at hn
    have htτ : t.toNNReal ≤ τ := by
      simpa only [Real.toNNReal_coe] using Real.toNNReal_mono ht.2
    have hx := (T t.toNNReal).le_of_opNorm_le (hT _ ⟨zero_le, htτ⟩) x
    have hv : ‖v t‖ ≤ (M : ℝ) * ‖x‖ + (M * C) * ∫ s in (0 : ℝ)..t, e s := by
      dsimp only [v]
      rw [IccExtend_of_mem τ.coe_nonneg u ht, hu ⟨t, ht⟩]
      exact (norm_add_le _ _).trans (add_le_add hx hn)
    dsimp only [e]
    linarith
  have hg := le_mul_exp_of_le_const_add_mul_intervalIntegral
    he.continuousOn (mul_nonneg M.coe_nonneg hC) hi
  intro t
  simpa only [e, v, IccExtend_val, sub_zero] using hg t t.property

/-- A fixed finite horizon and an affine source bound yield a single bound
for every mild solution prefix up to that horizon. -/
theorem exists_norm_mildSolutionOn_bound_of_affine_source (T : StronglyContinuousSemigroup E)
    (x : E) {H C : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ {F : C(E, E)} {τ : ℝ≥0}, (τ : ℝ) ≤ H → ∀ {u : C(Icc (0 : ℝ) (τ : ℝ), E)},
      T.IsMildSolutionOn F x τ u → (∀ t, ‖F (u t)‖ ≤ C * (1 + ‖u t‖)) → ∀ t, ‖u t‖ ≤ R := by
  obtain ⟨M, hM, hT⟩ := T.exists_norm_le_on_Icc ⟨H, hH⟩
  let R := (1 + M * ‖x‖) * Real.exp (M * C * H)
  refine ⟨R, mul_nonneg (by positivity) (Real.exp_pos _).le, ?_⟩
  intro F τ hτ u hu hF t
  have hb := norm_mildSolutionOn_le_of_affine_source hu (M := ⟨M, hM⟩)
    (fun r hr ↦ hT r ⟨hr.1, hr.2.trans hτ⟩) hC hF t
  have ht : (t : ℝ) ≤ H := t.property.2.trans hτ
  have he : Real.exp (M * C * (t : ℝ)) ≤ Real.exp (M * C * H) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht (mul_nonneg hM hC))
  exact (by linarith : ‖u t‖ ≤ 1 + ‖u t‖).trans (hb.trans (mul_le_mul_of_nonneg_left he
      (add_nonneg zero_le_one (mul_nonneg hM (norm_nonneg x)))))

/-- Affine forcing growth before a finite endpoint supplies a uniform norm
bound, without assuming boundedness of the unknown trajectory. -/
theorem exists_norm_mildSolutionBefore_bound_of_affine_source {T : StronglyContinuousSemigroup E}
    {F : C(E, E)} {x : E} {b : ℝ} {u : ℝ → E} (hu : T.IsMildSolutionBefore F x b u) (hb : 0 < b)
    {C : ℝ} (hC : 0 ≤ C) (hF : ∀ t ∈ Ico 0 b, ‖F (u t)‖ ≤ C * (1 + ‖u t‖)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Ico 0 b, ‖u t‖ ≤ R := by
  obtain ⟨R, hR, hbound⟩ := exists_norm_mildSolutionOn_bound_of_affine_source T x hb.le hC
  refine ⟨R, hR, ?_⟩
  intro t ht
  exact hbound (τ := ⟨t, ht.1⟩) ht.2.le (hu.isMildSolutionOn_restrictCurve (τ := ⟨t, ht.1⟩) ht.2)
    (fun s ↦ hF s ⟨s.property.1, s.property.2.trans_lt ht.2⟩) ⟨t, ht.1, le_rfl⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy
