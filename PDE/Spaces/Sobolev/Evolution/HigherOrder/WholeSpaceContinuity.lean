/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Evolution.HigherOrder.WholeSpaceTriple
public import PDE.Analysis.Evolution.LionsMagenes.Factorization
public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivatives
import PDE.Analysis.MeasureTheory.ContinuousRepresentative.ClosedEmbedding
import PDE.Spaces.Sobolev.GraphSpace.Topology.FirstDerivatives

/-!
# Whole-space H¹ continuity with a prescribed L² representative

An H² trajectory with an L² time derivative has an H¹ representative continuous
on the closed time interval. Its base coordinate agrees at every time with
any continuous L² representative. In particular, an L² initial identity
determines the full H¹ initial trace.

Applying this result to the first derivatives, and using their closed
graph embedding, also gives H² continuity for an H³ state with H¹ velocity.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory PDE.Analysis.Evolution Set
open scoped ENNReal Sobolev

variable {n : ℕ} {a b : ℝ}

/-- Factorization gives H¹ continuity; almost-everywhere agreement and
continuity identify the prescribed L² representative on the closed interval. -/
theorem exists_continuous_hOne_representative_eq_base
    (hab : a < b)
    (u : Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (g : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b)))
    (hweak : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (u t)) (fun t ↦ g t))
    (z : ℝ → DerivLp n 2 univ) (hz : ContinuousOn z (Icc a b))
    (hzu : z =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ wkpBaseCoordinateCLM (u t)) :
    ∃ v : ℝ → W^{1,2}(ℝ^n), ContinuousOn v (Icc a b) ∧
      v =ᵐ[volume.restrict (Ioc a b)] (fun t ↦ lowerOrderCLM (by omega : 1 ≤ 2) (u t)) ∧
      EqOn (fun t ↦ wkpBaseCoordinateCLM (v t)) z (Icc a b) := by
  let : MeasurableSpace (W^{2,2}(ℝ^n)) := borel _
  have : BorelSpace (W^{2,2}(ℝ^n)) := ⟨rfl⟩
  let : MeasurableSpace (StrongDual ℝ (W^{2,2}(ℝ^n))) := borel _
  have : BorelSpace (StrongDual ℝ (W^{2,2}(ℝ^n))) := ⟨rfl⟩
  obtain ⟨_, _, hrep⟩ :=
    (hTwoHOneTriple n).exists_continuous_representative_of_factorization
      wkpBaseCoordinateCLM (lTwoToHTwoDual n) hTwoHOneTriple_energyToDual hab
  obtain ⟨v, hv, hva, _⟩ := hrep u g hweak
  refine ⟨v, hv, hva, ?_⟩
  let P : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := wkpBaseCoordinateCLM
  have hae : (fun t ↦ P (v t)) =ᵐ[volume.restrict (Icc a b)] z := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    filter_upwards [hva, hzu] with t hvt hzt
    simp only [hvt, hzt, P, hTwoHOneTriple, wkpBaseCoordinateCLM_apply,
      lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex]
  exact Measure.eqOn_Icc_of_ae_eq volume hab.ne hae
    (P.continuous.comp_continuousOn hv) hz

/-- An H³ state with its H¹ time derivative has a continuous H²
representative. Its lower-order trace agrees everywhere with any prescribed
continuous H¹ representative. -/
theorem exists_continuous_hTwo_representative_eq_lowerOrder
    (hab : a < b)
    (u : Lp (W^{3,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (g : Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (hweak : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ lowerOrderCLM (by decide : 1 ≤ 3) (u t)) (fun t ↦ g t))
    (z : ℝ → W^{1,2}(ℝ^n)) (hz : ContinuousOn z (Icc a b))
    (hzu : z =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ lowerOrderCLM (by decide : 1 ≤ 3) (u t)) :
    ∃ v : ℝ → W^{2,2}(ℝ^n), ContinuousOn v (Icc a b) ∧
      v =ᵐ[volume.restrict (Ioc a b)] (fun t ↦ lowerOrderCLM (by decide : 2 ≤ 3) (u t)) ∧
      EqOn (fun t ↦ lowerOrderCLM (by decide : 1 ≤ 2) (v t)) z (Icc a b) := by
  classical
  let ν := volume.restrict (Ioc a b)
  let B : W^{3,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n) := lowerOrderCLM (by decide)
  let B₂ : W^{3,2}(ℝ^n) →L[ℝ] W^{2,2}(ℝ^n) := lowerOrderCLM (by decide)
  let R : W^{2,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n) := lowerOrderCLM (by decide)
  let D (i : Fin n) : W^{3,2}(ℝ^n) →L[ℝ] W^{2,2}(ℝ^n) :=
    partialDerivCLM i
  let Q (i : Fin n) : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ :=
    wkpCoordinateCLM (derivIndexOfList [i] (by simp))
  have hQD (i : Fin n) (U : W^{3,2}(ℝ^n)) :
      Q i (B U) = wkpBaseCoordinateCLM (D i U) := by
    simp only [Q, B, D, partialDerivCLM, wkpCoordinateCLM_apply, lowerOrderCLM_apply,
      wkpBaseCoordinateCLM_apply, derivativeWordCLM_apply, derivativeWordIndex_baseIndex]
    rfl
  have hderiv (i : Fin n) :
      ∃ w : ℝ → W^{1,2}(ℝ^n), ContinuousOn w (Icc a b) ∧
        w =ᵐ[ν] (fun t ↦ R (D i (u t))) := by
    let V := (D i).compLpL 2 ν u
    let H := (Q i).compLpL 2 ν g
    have hs : (fun t ↦ Q i (B (u t))) =ᵐ[ν]
        fun t ↦ wkpBaseCoordinateCLM (V t) := by
      filter_upwards [(D i).coeFn_compLpL u] with t ht
      rw [show V t = D i (u t) from ht]
      exact hQD i (u t)
    have hv : (fun t ↦ Q i (g t)) =ᵐ[ν] fun t ↦ H t :=
      ((Q i).coeFn_compLpL g).symm
    have hw := (hweak.map (Q i)).congr_ae_restrict measurableSet_Ioo
      (hs.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))
      (hv.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))
    have hzV : (fun t ↦ Q i (z t)) =ᵐ[ν] fun t ↦ wkpBaseCoordinateCLM (V t) :=
      (hzu.fun_comp (Q i)).trans hs
    obtain ⟨w, hwc, hwa, _⟩ := exists_continuous_hOne_representative_eq_base hab
      V H hw (fun t ↦ Q i (z t)) ((Q i).continuous.comp_continuousOn hz) hzV
    refine ⟨w, hwc, ?_⟩
    filter_upwards [hwa, (D i).coeFn_compLpL u] with t hwt hDt
    rw [hwt]
    change R (V t) = R (D i (u t))
    rw [show V t = D i (u t) from hDt]
  choose w hwc hwa using hderiv
  let J := firstDerivativeGraphCLM (n := n) (k := 1) (Ω := univ)
  let Z (t : ℝ) := (wkpBaseCoordinateCLM (z t), fun i ↦ w i t)
  have hZ : ContinuousOn Z (Icc a b) :=
    (wkpBaseCoordinateCLM.continuous.comp_continuousOn hz).prodMk
      (continuousOn_pi.mpr hwc)
  have hZu : Z =ᵐ[ν] J ∘ (fun t ↦ B₂ (u t)) := by
    filter_upwards [hzu, Filter.eventually_all.mpr hwa] with t hzt hwt
    apply Prod.ext
    · rw [show (Z t).1 = wkpBaseCoordinateCLM (z t) from rfl, hzt]
      rfl
    · funext i
      change w i t = ∂[i] (B₂ (u t))
      rw [hwt i]
      simp only [R, D, B₂, partialDerivCLM,
        lowerOrderCLM_derivativeWordCLM_apply,
        derivativeWordCLM_lowerOrderCLM_apply]
  have hJ := isClosedEmbedding_firstDerivativeGraphCLM (n := n) (k := 1) isOpen_univ
  obtain ⟨v, hvc, hva, _⟩ := hJ.exists_continuousOn_lift_ae_eq
    hab (fun t ↦ B₂ (u t)) Z hZ hZu
  refine ⟨v, hvc, hva, ?_⟩
  have hae : (fun t ↦ R (v t)) =ᵐ[volume.restrict (Icc a b)] z := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    filter_upwards [hva, hzu] with t hvt hzt
    rw [hvt, hzt]
    exact lowerOrderCLM_trans_apply (by decide : 1 ≤ 2) (by decide : 2 ≤ 3) (u t)
  exact Measure.eqOn_Icc_of_ae_eq volume hab.ne hae
    (R.continuous.comp_continuousOn hvc) hz

end SobolevSpace.GraphSpace
