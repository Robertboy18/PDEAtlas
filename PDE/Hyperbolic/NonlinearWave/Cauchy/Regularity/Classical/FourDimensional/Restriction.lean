/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.HigherForcing

/-!
# Restricting higher wave trajectories to a lower energy level

Forgetting derivatives commutes with the constructed wave semigroups and their
Duhamel integrals. A bounded source in H³ × H² therefore bounds that part of
a higher mild wave trajectory on every fixed finite time interval.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped NNReal Sobolev

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

/-- Forget spatial derivatives in both components of higher wave data. -/
def higherWaveRestrictionCLM (n : ℕ) {r k : ℕ} (h : r ≤ k) :
    (W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) →L[ℝ]
      (W^{r + 1,2}(ℝ^n) × W^{r,2}(ℝ^n)) :=
  (lowerOrderCLM (Nat.add_le_add_right h 1)).prodMap (lowerOrderCLM h)

/-- Restriction between higher wave levels preserves the energy coordinates. -/
theorem higherEnergyInclusionCLM_higherWaveRestrictionCLM
    (n : ℕ) {r k : ℕ} (h : r ≤ k) (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :
    higherEnergyInclusionCLM n r (higherWaveRestrictionCLM n h x) =
      higherEnergyInclusionCLM n k x := by
  apply (Hyperbolic.Variational.WaveEnergySpace.coordinates
    (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric).injective
  rw [coordinates_higherEnergyInclusionCLM, coordinates_higherEnergyInclusionCLM]
  change (lowerOrderCLM _ (lowerOrderCLM _ x.1), wkpBaseCoordinateCLM (lowerOrderCLM h x.2)) = _
  rw [lowerOrderCLM_trans_apply]
  rfl

/-- The constructed wave semigroups commute with restriction of Sobolev order. -/
theorem higherWaveRestrictionCLM_semigroup (n : ℕ) {r k : ℕ} (h : r ≤ k) (t : ℝ≥0)
    (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :
    higherWaveRestrictionCLM n h (higherLinearSemigroup n k t x) =
      higherLinearSemigroup n r t (higherWaveRestrictionCLM n h x) := by
  apply higherEnergyInclusionCLM_injective n r
  rw [higherEnergyInclusionCLM_higherWaveRestrictionCLM,
    higherEnergyInclusionCLM_higherLinearSemigroup, higherEnergyInclusionCLM_higherLinearSemigroup,
    higherEnergyInclusionCLM_higherWaveRestrictionCLM]

/-- Restriction of Sobolev order commutes with the wave Duhamel integral. -/
theorem higherWaveRestrictionCLM_duhamel (n : ℕ) {r k : ℕ} (h : r ≤ k)
    {F : ℝ → W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)} (hF : Continuous F) (t : ℝ) :
    higherWaveRestrictionCLM n h ((higherLinearSemigroup n k).duhamel F t) =
      (higherLinearSemigroup n r).duhamel (fun s ↦ higherWaveRestrictionCLM n h (F s)) t := by
  unfold StronglyContinuousSemigroup.duhamel
  rw [← (higherWaveRestrictionCLM n h).intervalIntegral_comp_comm
    (((higherLinearSemigroup n k).continuous_duhamelIntegrand hF t).intervalIntegrable 0 t)]
  apply intervalIntegral.integral_congr
  intro s _
  exact higherWaveRestrictionCLM_semigroup n h (t - s).toNNReal (F s)

/-- A uniform H² bound for the velocity source bounds the H³ × H² restriction
of every higher mild wave prefix on a fixed finite horizon. -/
theorem exists_norm_higherWaveRestriction_bound {n k : ℕ} (h2 : 2 ≤ k)
    (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) {H C : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ {F : C(W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n),
        W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))} {τ : ℝ≥0},
      (τ : ℝ) ≤ H → ∀ {u : C(Icc (0 : ℝ) (τ : ℝ),
        W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))},
      (higherLinearSemigroup n k).IsMildSolutionOn F x τ u →
      (∀ t, ‖higherWaveRestrictionCLM n h2 (F (u t))‖ ≤ C) →
      ∀ t, ‖higherWaveRestrictionCLM n h2 (u t)‖ ≤ R := by
  let L := higherWaveRestrictionCLM n h2
  let T := higherLinearSemigroup n 2
  obtain ⟨M, hM, hT⟩ := T.exists_norm_le_on_Icc ⟨H, hH⟩
  refine ⟨M * ‖L x‖ + M * (H * C), by positivity, ?_⟩
  intro F τ hτ u hu hF t
  let v := IccExtend τ.coe_nonneg u
  have hn := T.norm_duhamel_sub_le_integral (f := fun s ↦ L (F (v s))) (g := fun _ ↦ 0)
    (L.continuous.comp (F.continuous.comp u.continuous.Icc_extend')) continuous_const
    (τ := τ) (M := ⟨M, hM⟩) (fun r hr ↦ hT r ⟨hr.1, hr.2.trans hτ⟩)
    t.property (D := fun _ ↦ C) continuous_const (fun s _ ↦ by
      simpa only [sub_zero, v, IccExtend, Function.comp_apply] using
        hF (projIcc 0 (τ : ℝ) τ.coe_nonneg s))
  have hz : T.duhamel (fun _ ↦ 0) t = 0 := by
    simp [StronglyContinuousSemigroup.duhamel]
  rw [hz, sub_zero, intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hn
  have htτ : (t : ℝ).toNNReal ≤ ⟨H, hH⟩ := by
    have he : H.toNNReal = (⟨H, hH⟩ : ℝ≥0) := by
      apply NNReal.eq
      exact Real.coe_toNNReal H hH
    exact (Real.toNNReal_mono (t.property.2.trans hτ)).trans_eq he
  have hx := (T (t : ℝ).toNNReal).le_of_opNorm_le (hT _ ⟨zero_le, htτ⟩) (L x)
  have he : L (u t) =
      T.realOrbit (L x) t + T.duhamel (fun s ↦ L (F (v s))) t := by
    rw [hu t, map_add]
    change L ((higherLinearSemigroup n k).realOrbit x t) +
      L ((higherLinearSemigroup n k).duhamel (fun s ↦ F (v s)) t) = _
    dsimp only [L, T]
    rw [higherWaveRestrictionCLM_duhamel n h2 (F := fun s ↦ F (v s))
      (F.continuous.comp u.continuous.Icc_extend')]
    change L ((higherLinearSemigroup n k) (t : ℝ).toNNReal x) + _ = _
    rw [higherWaveRestrictionCLM_semigroup]
    rfl
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hx (hn.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (t.property.2.trans hτ) hC) hM)))

end PDE.Hyperbolic.NonlinearWave.Cauchy
