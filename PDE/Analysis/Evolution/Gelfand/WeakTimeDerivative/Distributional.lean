/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.AbsolutelyContinuous
public import PDE.Analysis.Evolution.Time.WeakDerivative.Representative
import PDE.Analysis.Evolution.LionsMagenes.Basic.WeakDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# From distributional derivatives to Gelfand time derivatives

If `u ∈ L²(a, b; X)` has a weak derivative `du ∈ L²(a, b; X)` against smooth compactly
supported tests on `(a, b)`, then `u` agrees almost everywhere with the absolutely continuous
curve `t ↦ c + ∫_a^t du`. Integration by parts against this curve gives the identity for the
endpoint-vanishing tests of the integrated formulation, so a `V`-valued weak derivative `du`
makes `energyToDual ∘ du` the Gelfand weak time derivative of `u`.

Conversely, if the Gelfand weak time derivative of `u` is `pivotToDual ∘ du` for some
`du ∈ L²(a, b; H)`, then `du` is the `H`-valued weak derivative of `ι ∘ u` on `(a, b)`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set

namespace PDE.Analysis.Evolution

/-- If `u ∈ L²(a, b; X)` has weak derivative `du ∈ L²(a, b; X)` on `(a, b)`, then `u` agrees
almost everywhere on `(a, b]` with an absolutely continuous curve `w` such that `w' = du` almost
everywhere. -/
theorem HasWeakTimeDerivativeOn.exists_absolutelyContinuousRepresentative_of_lp
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {a b : ℝ} (hab : a < b)
    {u du : Lp X 2 (volume.restrict (Ioc a b))}
    (hweak : HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ u t) (fun t ↦ du t)) :
    ∃ w : ℝ → X, AbsolutelyContinuousOnInterval w a b ∧
      (u : ℝ → X) =ᵐ[volume.restrict (Ioc a b)] w ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt w (du t) t) := by
  have hdu := intervalIntegrable_coeFn_L2_restrict_Ioc du hab.le
  obtain ⟨v, _, huv, hFTC⟩ := hweak.exists_continuous_representative_Icc hab
    (hdu.1.mono_set Ioo_subset_Ioc_self)
  let w : ℝ → X := fun t ↦ v a + ∫ s in a..t, du s
  have hwAC : AbsolutelyContinuousOnInterval w a b := by
    apply absolutelyContinuousOnInterval_of_eq_add_integral hdu
    intro t _
    simp only [w, intervalIntegral.integral_same, add_zero]
  refine ⟨w, hwAC, ?_, ?_⟩
  · have huv' : (u : ℝ → X) =ᵐ[volume.restrict (Ioc a b)] v := by
      rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at huv
    filter_upwards [huv', ae_restrict_mem measurableSet_Ioc] with t ht hti
    rw [ht]
    have h := hFTC a ⟨le_rfl, hab.le⟩ t ⟨hti.1.le, hti.2⟩
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  · have hd := IntervalIntegrable.ae_hasDerivAt_integral hdu
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hd] with t ht hti
    have hti' : t ∈ uIcc a b := by
      rw [uIcc_of_le hab.le]
      exact ⟨hti.1.le, hti.2⟩
    simpa only [zero_add] using (ht hti' a left_mem_uIcc).const_add (v a)

/-- The absolutely continuous representative of
`exists_absolutelyContinuousRepresentative_of_lp` can be chosen with `w a = v a` for any
representative `v` of `u` that is continuous on `[a, b]`. -/
theorem HasWeakTimeDerivativeOn.exists_absolutelyContinuousRepresentative_eq_initial
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {a b : ℝ} (hab : a < b)
    {u du : Lp X 2 (volume.restrict (Ioc a b))}
    (hweak : HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ u t) (fun t ↦ du t))
    (v : ℝ → X) (hv : ContinuousOn v (Icc a b))
    (huv : v =ᵐ[volume.restrict (Ioc a b)] fun t ↦ u t) :
    ∃ w : ℝ → X, AbsolutelyContinuousOnInterval w a b ∧
      (u : ℝ → X) =ᵐ[volume.restrict (Ioc a b)] w ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt w (du t) t) ∧ w a = v a := by
  obtain ⟨w, hwAC, huw, hwDeriv⟩ :=
    hweak.exists_absolutelyContinuousRepresentative_of_lp hab
  refine ⟨w, hwAC, huw, hwDeriv, ?_⟩
  have hwv : w =ᵐ[volume.restrict (Icc a b)] v := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact huw.symm.trans huv.symm
  exact Measure.eqOn_Icc_of_ae_eq volume hab.ne hwv
    (by simpa only [uIcc_of_le hab.le] using hwAC.continuousOn)
    hv ⟨le_rfl, hab.le⟩

/-- If `u ∈ L²(a, b; V)` has a `V`-valued weak derivative `du` on `(a, b)`, then
`energyToDual ∘ du` is the Gelfand weak time derivative of `u`. -/
theorem HasWeakTimeDerivativeOn.hasGelfandWeakTimeDerivativeOn
    {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : GelfandTriple (V := V) (H := H)) {a b : ℝ} (hab : a < b)
    {u du : Lp V 2 (volume.restrict (Ioc a b))}
    (hweak : HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ u t) (fun t ↦ du t)) :
    HasGelfandWeakTimeDerivativeOn T u
      (T.energyToDual.compLpL 2 (volume.restrict (Ioc a b)) du) := by
  obtain ⟨w, hwAC, huw, hwDeriv⟩ :=
    hweak.exists_absolutelyContinuousRepresentative_of_lp hab
  exact .of_absolutelyContinuousOnInterval T hab.le hwAC hwDeriv huw
    (T.energyToDual.coeFn_compLpL du)

/-- For the identity triple on a Hilbert space `X`, if `u` has weak derivative `du` on
`(a, b)`, then the Riesz image of `du` is the Gelfand weak time derivative of `u`. -/
theorem HasWeakTimeDerivativeOn.identity_hasGelfandWeakTimeDerivativeOn
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {a b : ℝ} (hab : a < b)
    {u du : Lp X 2 (volume.restrict (Ioc a b))}
    (hweak : HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ u t) (fun t ↦ du t)) :
    HasGelfandWeakTimeDerivativeOn (GelfandTriple.identity X) u (rieszToDualLp du) := by
  have h := hweak.hasGelfandWeakTimeDerivativeOn (GelfandTriple.identity X) hab
  have heq : (GelfandTriple.identity X).energyToDual.compLpL
      2 (volume.restrict (Ioc a b)) du = rieszToDualLp du := by
    apply Lp.ext
    filter_upwards [(GelfandTriple.identity X).energyToDual.coeFn_compLpL du,
      rieszToDualLp_apply_ae du] with t ht hr
    rw [ht, hr]
    ext v
    rfl
  rwa [heq] at h

/-- If the Gelfand weak time derivative of `u` is `pivotToDual ∘ du` for some
`du ∈ L²(a, b; H)`, then `du` is the `H`-valued weak derivative of `ι ∘ u` on `(a, b)`. The
proof uses injectivity of `pivotToDual`, which follows from density of `ι`. -/
theorem HasGelfandWeakTimeDerivativeOn.pivot_hasWeakTimeDerivativeOn
    {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {T : GelfandTriple (V := V) (H := H)} {a b : ℝ}
    {u : Lp V 2 (volume.restrict (Ioc a b))}
    {du : Lp H 2 (volume.restrict (Ioc a b))}
    (hweak : HasGelfandWeakTimeDerivativeOn T u
      (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) du)) :
    HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ T.inclusion (u t)) (fun t ↦ du t) := by
  have hu : LocallyIntegrableOn (fun t ↦ u t) (Ioo a b) volume :=
    (locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp u).locallyIntegrable (by norm_num))).mono_set Ioo_subset_Ioc_self
  have hdu : LocallyIntegrableOn (fun t ↦ du t) (Ioo a b) volume :=
    (locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp du).locallyIntegrable (by norm_num))).mono_set Ioo_subset_Ioc_self
  apply HasWeakTimeDerivativeOn.of_map T.pivotToDual T.pivotToDual_injective
    (T.inclusion.locallyIntegrableOn_comp hu) hdu
  exact hweak.hasWeakTimeDerivativeOn.congr_ae_restrict measurableSet_Ioo
    Filter.EventuallyEq.rfl ((T.pivotToDual.coeFn_compLpL du).filter_mono
      (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))

end PDE.Analysis.Evolution
