/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Temporal.IntegrateAutonomous
public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.DistributionalDerivatives
public import PDE.Analysis.Evolution.Time.WeakDerivative.L2Representative

/-!
# Improved time regularity of autonomous weak waves

The forcing trace is constructed by the Banach-valued fundamental theorem. Solving
one further weak wave with initial acceleration `f(a) - Lg` and integrating its
state gives the original solution and its differentiated chain. The energy
estimate for that solve controls the two improved time derivatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis.Evolution
open scoped ENNReal

namespace Hyperbolic.Variational

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
  {B : V →L[ℝ] StrongDual ℝ V}

/-- Integrating the differentiated equation gives the complete weak derivative chain.
The initial elliptic load is a pivot vector; its compatibility with `B g` is the
stationary weak equation, which concrete elliptic data discharge separately. -/
theorem exists_improved_wave_of_energy_bound (hab : a < b) {M : ℝ} (hM : 0 < M)
    (henergy : ∀ (f : Lp H 2 (volume.restrict (Ioc a b))) (g : V) (h : H), ∃ u v w,
      IsGelfandWeakWaveSolution T (fun _ ↦ B) (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
      f) u v w g h ∧ MemLp (fun t ↦ u t) ∞ (volume.restrict (Ioc a b)) ∧
      MemLp (fun t ↦ v t) ∞ (volume.restrict (Ioc a b)) ∧ ∀ᵐ t ∂volume.restrict (Ioc a b),
      ‖u t‖ + ‖v t‖ ≤ M * (‖f‖ + ‖g‖ + ‖h‖))
    (f ft : Lp H 2 (volume.restrict (Ioc a b))) (hft : HasWeakTimeDerivativeOn (Ioo a b) f ft)
    (g h : V) (Lg : H) (hLg : T.pivotToDual Lg = B g) :
    let K := (((b - a)⁻¹ + 1) * max 1 (b - a))
    let D := ‖ft‖ + ‖h‖ + K * (‖f‖ + ‖ft‖) + ‖Lg‖
    ∃ (u v : Lp V 2 (volume.restrict (Ioc a b))) (w : Lp H 2 (volume.restrict (Ioc a b)))
      (z : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))),
      IsGelfandWeakWaveSolution T (fun _ ↦ B)
        (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f) u
        (T.inclusion.compLpL 2 (volume.restrict (Ioc a b)) v)
        (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) w) g (T.inclusion h) ∧
      HasWeakTimeDerivativeOn (Ioo a b) u v ∧
      HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ T.inclusion (v t)) w ∧
      HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ T.pivotToDual (w t)) z ∧
      MemLp (fun t ↦ v t) ∞ (volume.restrict (Ioc a b)) ∧
      MemLp (fun t ↦ w t) ∞ (volume.restrict (Ioc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), ‖v t‖ + ‖w t‖ ≤ M * D) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), ‖f t‖ ≤ K * (‖f‖ + ‖ft‖)) ∧
      ‖z‖ ≤ ‖T.pivotToDual‖ * ‖ft‖ + ‖B‖ *
        ((measureUnivNNReal (volume.restrict (Ioc a b)) : ℝ) ^ (2 : ℝ)⁻¹ * (M * D)) := by
  let μ := volume.restrict (Ioc a b)
  let K := (((b - a)⁻¹ + 1) * max 1 (b - a))
  let D := ‖ft‖ + ‖h‖ + K * (‖f‖ + ‖ft‖) + ‖Lg‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨F, hF, hfF, hFTC, hFbound⟩ := hft.exists_continuous_L2_representative_norm_le hab
  let p₁ := F a - Lg
  have hp₁ : ‖p₁‖ ≤ K * (‖f‖ + ‖ft‖) + ‖Lg‖ :=
    (norm_sub_le _ _).trans (add_le_add (hFbound a ⟨le_rfl, hab.le⟩) le_rfl)
  obtain ⟨v, w, z, hv, hvtop, hwtop, hvbound⟩ := henergy ft h p₁
  let ell := T.pivotToDual.compLpL 2 μ f
  let ellDot := T.pivotToDual.compLpL 2 μ ft
  have hell : ∀ᵐ t ∂μ, ell t = T.pivotToDual (F a) + ∫ s in a..t, ellDot s := by
    filter_upwards [T.pivotToDual.coeFn_compLpL f, hfF, ae_restrict_mem measurableSet_Ioc]
      with t ht hft htI
    have hint := (intervalIntegrable_coeFn_L2_restrict_Ioc ft hab.le).mono_set
      (uIcc_subset_uIcc_left (Icc_subset_uIcc (Ioc_subset_Icc_self htI)))
    have hi : (∫ s in a..t, ellDot s) = T.pivotToDual (∫ s in a..t, ft s) := by
      rw [← T.pivotToDual.intervalIntegral_comp_comm hint,
        intervalIntegral.integral_of_le htI.1.le, intervalIntegral.integral_of_le htI.1.le]
      exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right htI.2)
        (T.pivotToDual.coeFn_compLpL ft))
    rw [ht, hft, hFTC a ⟨le_rfl, hab.le⟩ t (Ioc_subset_Icc_self htI), map_add, hi]
  have hcompat : T.pivotToDual p₁ + B g = T.pivotToDual (F a) := by
    simp only [p₁, map_sub, hLg, sub_add_cancel]
  obtain ⟨u, hu, huv⟩ := hv.exists_integral_weakWave hell hcompat
  have hbound : ∀ᵐ t ∂μ, ‖v t‖ + ‖w t‖ ≤ M * D := by
    filter_upwards [hvbound] with t ht
    exact ht.trans (mul_le_mul_of_nonneg_left (by dsimp [D]; linarith) hM.le)
  have hvnorm : ‖v‖ ≤ (measureUnivNNReal μ : ℝ) ^ (2 : ℝ)⁻¹ * (M * D) := by
    apply Lp.norm_le_of_ae_bound (mul_nonneg hM.le hD)
    filter_upwards [hbound] with t ht using (le_add_of_nonneg_right (norm_nonneg (w t))).trans ht
  have hznorm : ‖z‖ ≤ ‖T.pivotToDual‖ * ‖ft‖ + ‖B‖ *
      ((measureUnivNNReal μ : ℝ) ^ (2 : ℝ)⁻¹ * (M * D)) := by
    have hz : z = ellDot - B.compLpL 2 μ v := by
      apply Lp.ext
      filter_upwards [hv.acceleration_eq_residualAE, Lp.coeFn_sub ellDot (B.compLpL 2 μ v),
        B.coeFn_compLpL v] with t ht hsub hB
      rw [ht, hsub, Pi.sub_apply, hB]
    rw [hz]
    exact (norm_sub_le _ _).trans (add_le_add (T.pivotToDual.norm_compLp_le ft)
      ((B.norm_compLp_le v).trans (mul_le_mul_of_nonneg_left hvnorm (norm_nonneg B))))
  refine ⟨u, v, w, z, hu, huv, hv.displacement_hasWeakTimeDerivativeOn,
    hv.velocity_hasWeakTimeDerivativeOn, hvtop, hwtop, hbound, ?_, hznorm⟩
  filter_upwards [hfF, ae_restrict_mem measurableSet_Ioc] with t ht htI
    using ht ▸ hFbound t (Ioc_subset_Icc_self htI)

end Hyperbolic.Variational
