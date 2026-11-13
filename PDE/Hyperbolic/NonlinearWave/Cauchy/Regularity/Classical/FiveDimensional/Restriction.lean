/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FourDimensional.Restriction

/-!
# Bounds for restricted wave trajectories with affine forcing

Restriction commutes with the constructed wave semigroup and Duhamel integral.
Grönwall therefore controls the lower wave norm from affine growth of the
restricted forcing, even if that forcing depends on the full higher state.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped NNReal Sobolev

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

/-- Affine growth of the restricted source gives a uniform bound for the
restriction of every higher wave prefix on a fixed finite horizon. -/
theorem exists_norm_higherWaveRestriction_bound_of_affine_source {n r k : ℕ} (hr : r ≤ k)
    (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) {H C : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ {F : C(W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n),
        W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))} {τ : ℝ≥0},
      (τ : ℝ) ≤ H → ∀ {u : C(Icc (0 : ℝ) (τ : ℝ),
        W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))},
      (higherLinearSemigroup n k).IsMildSolutionOn F x τ u →
      (∀ t, ‖higherWaveRestrictionCLM n hr (F (u t))‖ ≤
        C * (1 + ‖higherWaveRestrictionCLM n hr (u t)‖)) →
      ∀ t, ‖higherWaveRestrictionCLM n hr (u t)‖ ≤ R := by
  let L := higherWaveRestrictionCLM n hr
  let T := higherLinearSemigroup n r
  obtain ⟨M, hM, hT⟩ := T.exists_norm_le_on_Icc ⟨H, hH⟩
  refine ⟨(1 + M * ‖L x‖) * Real.exp (M * C * H), by positivity, ?_⟩
  intro F τ hτ u hu hF t
  let v := IccExtend τ.coe_nonneg u
  let e : ℝ → ℝ := fun s ↦ 1 + ‖L (v s)‖
  have he : Continuous e := continuous_const.add (L.continuous.comp u.continuous.Icc_extend').norm
  have hi (s : ℝ) (hs : s ∈ Icc (0 : ℝ) τ) :
      e s ≤ (1 + M * ‖L x‖) + (M * C) * ∫ q in (0 : ℝ)..s, e q := by
    have hn := T.norm_duhamel_sub_le_integral (f := fun q ↦ L (F (v q))) (g := fun _ ↦ 0)
      (L.continuous.comp (F.continuous.comp u.continuous.Icc_extend')) continuous_const
      (τ := τ) (M := ⟨M, hM⟩) (fun q hq ↦ hT q ⟨hq.1, hq.2.trans hτ⟩)
      hs (D := fun q ↦ C * e q) (continuous_const.mul he) (fun q _ ↦ by
        simpa only [sub_zero, e, v, IccExtend, Function.comp_apply] using
          hF (projIcc 0 (τ : ℝ) τ.coe_nonneg q))
    have hz : T.duhamel (fun _ ↦ 0) s = 0 := by
      simp [StronglyContinuousSemigroup.duhamel]
    rw [hz, sub_zero, intervalIntegral.integral_const_mul, ← mul_assoc] at hn
    have hsτ : s.toNNReal ≤ τ := by
      simpa only [Real.toNNReal_coe] using Real.toNNReal_mono hs.2
    have hx := (T s.toNNReal).le_of_opNorm_le (hT _ ⟨zero_le, hsτ.trans hτ⟩) (L x)
    have hv : L (v s) =
        T.realOrbit (L x) s + T.duhamel (fun q ↦ L (F (v q))) s := by
      rw [show v s = u ⟨s, hs⟩ from IccExtend_of_mem τ.coe_nonneg u hs, hu ⟨s, hs⟩, map_add]
      change L ((higherLinearSemigroup n k).realOrbit x s) +
        L ((higherLinearSemigroup n k).duhamel (fun q ↦ F (v q)) s) = _
      dsimp only [L, T]
      rw [higherWaveRestrictionCLM_duhamel n hr (F := fun q ↦ F (v q))
        (F.continuous.comp u.continuous.Icc_extend')]
      change L ((higherLinearSemigroup n k) s.toNNReal x) + _ = _
      rw [higherWaveRestrictionCLM_semigroup]
      rfl
    have hb : ‖L (v s)‖ ≤ M * ‖L x‖ + (M * C) * ∫ q in (0 : ℝ)..s, e q := by
      rw [hv]
      exact (norm_add_le _ _).trans (add_le_add hx hn)
    dsimp only [e]
    linarith
  have hg := le_mul_exp_of_le_const_add_mul_intervalIntegral
    he.continuousOn (mul_nonneg hM hC) hi
  have hb : 1 + ‖L (u t)‖ ≤ (1 + M * ‖L x‖) * Real.exp (M * C * (t : ℝ)) := by
    simpa only [e, v, IccExtend_val, sub_zero] using hg t t.property
  have heH : Real.exp (M * C * (t : ℝ)) ≤ Real.exp (M * C * H) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (t.property.2.trans hτ) (mul_nonneg hM hC))
  exact (by linarith : ‖L (u t)‖ ≤ 1 + ‖L (u t)‖).trans
    (hb.trans (mul_le_mul_of_nonneg_left heH (by positivity)))

end PDE.Hyperbolic.NonlinearWave.Cauchy
