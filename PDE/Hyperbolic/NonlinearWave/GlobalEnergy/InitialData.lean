/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.ForwardBasic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Initial forward energy from compact Cauchy data

On a finite forward band, the right velocity and spatial displacement
trace determine the initial energy density. Compact C¹ displacement and
continuous compact velocity make this density integrable for every continuous
potential vanishing at zero.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory PDE PDE.Common PDE.Analysis
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- The displacement trace and right velocity determine the initial
forward density on a finite band. -/
theorem forwardSemilinearWaveEnergyDensity_initial_of_contDiffOn_band {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} {T : ℝ} {g h : ℝ^n → ℝ} (hT : 0 < T)
    (hu : ContDiffOn ℝ 1 u {p | 0 ≤ p 0 ∧ p 0 < T}) (hpos : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hvel : ∀ x, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = h x) (x : ℝ^n) :
    forwardSemilinearWaveEnergyDensity V u 0 x =
      (1 / 2 : ℝ) * ((h x) ^ 2 + ∑ i : Fin n, ((∂[i] g) x) ^ 2) + V (g x) := by
  let D := fderivWithin ℝ u {p | 0 ≤ p 0} (timeSpaceCons 0 x)
  have huat : ContDiffWithinAt ℝ 1 u {p | 0 ≤ p 0} (timeSpaceCons 0 x) :=
    (contDiffWithinAt_inter ((isOpen_lt (EuclideanSpace.proj 0).continuous
      continuous_const).mem_nhds (show (timeSpaceCons 0 x) 0 < T by simpa using hT))).mp
        (hu _ (by simpa using hT))
  have hD : HasFDerivWithinAt u D {p | 0 ≤ p 0} (timeSpaceCons 0 x) :=
    (huat.differentiableWithinAt (by norm_num)).hasFDerivWithinAt
  have ht : D (EuclideanSpace.single 0 1) = h x := by
    have hd := hD.comp_hasDerivWithinAt 0 (hasDerivAt_timeSpaceCons_time n 0 x).hasDerivWithinAt
      (show MapsTo (fun t ↦ timeSpaceCons t x) (Ici 0) {p | 0 ≤ p 0} from
        fun t ht ↦ by simpa using ht)
    exact (hd.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans (hvel x)
  have hs : D.comp (embedWithTimeZeroCLM n) = fderiv ℝ g x := by
    have hd := hD.comp_hasFDerivAt x (hasFDerivAt_timeSpaceCons_spatial n 0 x)
      (Eventually.of_forall fun y ↦ (show (0 : ℝ) ≤ (timeSpaceCons 0 y) 0 by simp))
    exact (hd.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ (hpos y).symm)).fderiv.symm
  have hsi (i : Fin n) : D (EuclideanSpace.single i.succ 1) = (∂[i] g) x := by
    have he := congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1)) hs
    simpa [PDE.partialDeriv] using he
  unfold forwardSemilinearWaveEnergyDensity forwardDifferential
  rw [max_self, EuclideanSpace.real_norm_sq_eq]
  change (1 / 2 : ℝ) * ((D (EuclideanSpace.single 0 1)) ^ 2 +
    ∑ i : Fin n, (D (EuclideanSpace.single i.succ 1)) ^ 2) + V (u (timeSpaceCons 0 x)) = _
  simp only [ht, hsi, hpos]

/-- Compact Cauchy data give integrable initial forward energy for every
continuous normalized potential, without support assumptions on later slices. -/
theorem integrable_forwardSemilinearWaveEnergyDensity_initial_of_compact_data {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} {T : ℝ} {g h : ℝ^n → ℝ} (hT : 0 < T) (hV : Continuous V) (hVzero : V 0 = 0)
    (hu : ContDiffOn ℝ 1 u {p | 0 ≤ p 0 ∧ p 0 < T}) (hg : ContDiff ℝ 1 g) (hh : Continuous h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h)
    (hpos : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hvel : ∀ x, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = h x) :
    Integrable (forwardSemilinearWaveEnergyDensity V u 0) := by
  have hi : Integrable (fun x : ℝ^n ↦ (1 / 2 : ℝ) *
      ((h x) ^ 2 + ∑ i : Fin n, ((∂[i] g) x) ^ 2) + V (g x)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · apply Continuous.add
      · apply continuous_const.mul
        apply (hh.pow 2).add
        exact continuous_finsetSum _ (fun i _ ↦
          ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2)
      · exact hV.comp hg.continuous
    · refine HasCompactSupport.intro (hgc.isCompact.union hhc.isCompact) fun x hx ↦ ?_
      have hxg : x ∉ tsupport g := fun h ↦ hx (Or.inl h)
      have hxh : x ∉ tsupport h := fun h ↦ hx (Or.inr h)
      simp only [PDE.partialDeriv, fderiv_of_notMem_tsupport ℝ hxg,
        zero_apply, zero_pow (by decide : 2 ≠ 0),
        Finset.sum_const_zero, image_eq_zero_of_notMem_tsupport hxg,
        image_eq_zero_of_notMem_tsupport hxh, add_zero, mul_zero, hVzero]
  exact hi.congr (Eventually.of_forall fun x ↦
    (forwardSemilinearWaveEnergyDensity_initial_of_contDiffOn_band hT hu hpos hvel x).symm)

end WaveEquation
