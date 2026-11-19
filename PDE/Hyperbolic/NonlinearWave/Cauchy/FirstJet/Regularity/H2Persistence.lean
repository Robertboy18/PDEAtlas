/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.Regularity.WeakLimit
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.EllipticResolvent
import PDE.Spaces.Sobolev.GraphSpace.Operators.BochnerIntegral

/-!
# H² persistence for globally Lipschitz first-jet reactions

The full first-jet energy solution with H² × H¹ initial data has bounded
H² displacement, H¹ velocity and L² acceleration on every finite interval.
Weak compactness of energy time quotients supplies the velocity and
acceleration lifts; the massive elliptic inverse recovers displacement.
Measurability follows from the Sobolev graph embedding theorem.

This is the regularity assertion of Evans, §12.2.1, Theorem 1(ii), for whole-space data.
Arbitrary local Sobolev data also require a finite-propagation and patching argument. Evans
proves (ii) with spatial difference quotients and recovers `u''` from the equation; we use
time quotients and recover the displacement from the elliptic equation.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.2.1, Theorem 1(ii) and step 3 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Sobolev SobolevSpace.WholeSpaceHilbert Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

variable {hf : LipschitzWith L f} {hf0 : f 0 = 0}
variable {x : H¹(ℝ^n) × DerivLp n 2 univ}
variable {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}

/-- Generator-domain initial data give uniformly bounded H², H¹ and L²
lifts of displacement, velocity and acceleration on a finite interval. -/
theorem IsEnergySolution.exists_bounded_h2_lifts
    (h : IsEnergySolution hf hf0 x u) {Ax : EnergyState n}
    (hx : (linearSemigroup n).HasGeneratorAt ((C).symm x) Ax) (T : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) T,
      ∃ (U : W^{2,2}(ℝ^n)) (V : H¹(ℝ^n)) (A : DerivLp n 2 univ),
        lowerOrderCLM (by decide : 1 ≤ 2) U = (u t).1 ∧
        (energyTriple n).inclusion V = (u t).2 ∧
        (energyTriple n).pivotToDual A = acceleration hf hf0 (u t) ∧
        A = Δ U - reaction hf hf0 (u t) ∧ ‖U‖ ≤ B ∧ ‖V‖ ≤ B ∧ ‖A‖ ≤ B := by
  obtain ⟨R, hR, hinc⟩ := h.exists_time_increment_bound hx T
  have hs : Continuous (fun t ↦ source hf hf0 (u t)) :=
    (source_lipschitz hf hf0).continuous.comp u.continuous
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) T) hs.continuousOn
  let D := ‖(C).toContinuousLinearMap‖ * R
  let B := ‖(massiveLaplacianEquiv n).symm.toContinuousLinearMap‖ * (max M 0 + D) + D
  have hD : 0 ≤ D := by
    exact mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) hR
  have hB : 0 ≤ B := add_nonneg
    (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (add_nonneg (le_max_right M 0) hD)) hD
  refine ⟨B, hB, ?_⟩
  intro t ht
  obtain ⟨d, hdR, hdV, hdA⟩ := h.exists_energy_derivative_lift ht.1
    (fun a ha ↦ hinc t ht a ⟨ha.1.le, ha.2⟩)
  let V := (C d).1
  let A := (C d).2
  let U := (massiveLaplacianEquiv n).symm (source hf hf0 (u t) - A)
  have hmass : massForm n (u t).1 =
      (energyTriple n).pivotToDual (source hf hf0 (u t) - A) := by
    rw [map_sub, hdA, ← source_sub_massForm]
    abel
  have hlow : lowerOrderCLM (by decide : 1 ≤ 2) U = (u t).1 :=
    lowerOrder_massiveLaplacianEquiv_symm _ _ hmass
  have hbase : wkpBaseCoordinateCLM U = (energyTriple n).inclusion (u t).1 :=
    congrArg (energyTriple n).inclusion hlow
  have hload : A = Δ U - reaction hf hf0 (u t) := by
    have he := (massiveLaplacianEquiv n).apply_symm_apply (source hf hf0 (u t) - A)
    change massiveLaplacianEquiv n U = source hf hf0 (u t) - A at he
    rw [massiveLaplacianEquiv_apply, hbase, source] at he
    apply sub_eq_zero.mp
    calc
      A - (Δ U - reaction hf hf0 (u t)) = ((energyTriple n).inclusion (u t).1 - Δ U) -
            ((energyTriple n).inclusion (u t).1 - reaction hf hf0 (u t) - A) := by abel
      _ = 0 := sub_eq_zero.mpr he
  have hd : ‖C d‖ ≤ D := ((C).toContinuousLinearMap.le_opNorm d).trans
    (mul_le_mul_of_nonneg_left hdR (ContinuousLinearMap.opNorm_nonneg _))
  have hV : ‖V‖ ≤ D := (norm_fst_le (C d)).trans hd
  have hA : ‖A‖ ≤ D := (norm_snd_le (C d)).trans hd
  have hU : ‖U‖ ≤ ‖(massiveLaplacianEquiv n).symm.toContinuousLinearMap‖ *
      (max M 0 + D) := by
    apply ((massiveLaplacianEquiv n).symm.toContinuousLinearMap.le_opNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (ContinuousLinearMap.opNorm_nonneg _)
    exact (norm_sub_le _ _).trans (add_le_add ((hM t ht).trans (le_max_left M 0)) hA)
  have hDB : D ≤ B := le_add_of_nonneg_left
    (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (add_nonneg (le_max_right M 0) hD))
  exact ⟨U, V, A, hlow, hdV, hdA, hload,
    hU.trans (le_add_of_nonneg_right hD), hV.trans hDB, hA.trans hDB⟩

/-- The bounded higher lifts are Bochner L-infinity functions of time.
Their values represent the same energy solution and its acceleration. -/
theorem IsEnergySolution.exists_memLp_h2_lifts
    (h : IsEnergySolution hf hf0 x u) {Ax : EnergyState n}
    (hx : (linearSemigroup n).HasGeneratorAt ((C).symm x) Ax) (T : ℝ) :
    ∃ (U : ℝ → W^{2,2}(ℝ^n)) (V : ℝ → H¹(ℝ^n)) (A : ℝ → DerivLp n 2 univ),
      MemLp U ∞ (volume.restrict (Icc 0 T)) ∧
      MemLp V ∞ (volume.restrict (Icc 0 T)) ∧
      MemLp A ∞ (volume.restrict (Icc 0 T)) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        lowerOrderCLM (by decide : 1 ≤ 2) (U t) = (u t).1 ∧
        (energyTriple n).inclusion (V t) = (u t).2 ∧
        (energyTriple n).pivotToDual (A t) = acceleration hf hf0 (u t) ∧
        A t = Δ (U t) - reaction hf hf0 (u t) := by
  classical
  obtain ⟨B, _, hB⟩ := h.exists_bounded_h2_lifts hx T
  have hall (t : ℝ) : ∃ (U : W^{2,2}(ℝ^n)) (V : H¹(ℝ^n)) (A : DerivLp n 2 univ), t ∈ Icc (0 : ℝ) T →
        lowerOrderCLM (by decide : 1 ≤ 2) U = (u t).1 ∧ (energyTriple n).inclusion V = (u t).2 ∧
        (energyTriple n).pivotToDual A = acceleration hf hf0 (u t) ∧
        A = Δ U - reaction hf hf0 (u t) ∧ ‖U‖ ≤ B ∧ ‖V‖ ≤ B ∧ ‖A‖ ≤ B := by
    by_cases ht : t ∈ Icc (0 : ℝ) T
    · obtain ⟨U, V, A, hh⟩ := hB t ht
      exact ⟨U, V, A, fun _ ↦ hh⟩
    · exact ⟨0, 0, 0, fun hmem ↦ (ht hmem).elim⟩
  choose U V A hrep using hall
  let μ := volume.restrict (Icc (0 : ℝ) T)
  have hmem : ∀ᵐ t ∂μ, t ∈ Icc (0 : ℝ) T := ae_restrict_mem measurableSet_Icc
  have hUbase : (fun t ↦ wkpBaseCoordinateCLM (U t)) =ᵐ[μ]
      (fun t ↦ (energyTriple n).inclusion (u t).1) := by
    filter_upwards [hmem] with t ht
    exact congrArg (energyTriple n).inclusion (hrep t ht).1
  have hVbase : (fun t ↦ wkpBaseCoordinateCLM (V t)) =ᵐ[μ]
      (fun t ↦ (u t).2) := hmem.mono fun t ht ↦ (hrep t ht).2.1
  have hUm : AEStronglyMeasurable U μ :=
    aestronglyMeasurable_of_wkpBaseCoordinateCLM μ isOpen_univ U
      (((energyTriple n).inclusion.continuous.comp u.continuous.fst).aestronglyMeasurable
        |>.congr hUbase.symm)
  have hVm : AEStronglyMeasurable V μ :=
    aestronglyMeasurable_of_wkpBaseCoordinateCLM μ isOpen_univ V
      (u.continuous.snd.aestronglyMeasurable.congr hVbase.symm)
  have hAm : AEStronglyMeasurable A μ := by
    have heq : (fun t ↦ wkpLaplacianCLM (U t) - reaction hf hf0 (u t)) =ᵐ[μ] A :=
      hmem.mono fun t ht ↦ (hrep t ht).2.2.2.1.symm
    exact ((wkpLaplacianCLM.continuous.comp_aestronglyMeasurable hUm).sub
      ((reaction_lipschitz hf hf0).continuous.comp u.continuous).aestronglyMeasurable).congr heq
  refine ⟨U, V, A, memLp_top_of_bound hUm B ?_, memLp_top_of_bound hVm B ?_,
    memLp_top_of_bound hAm B ?_, ?_⟩
  · exact hmem.mono fun t ht ↦ (hrep t ht).2.2.2.2.1
  · exact hmem.mono fun t ht ↦ (hrep t ht).2.2.2.2.2.1
  · exact hmem.mono fun t ht ↦ (hrep t ht).2.2.2.2.2.2
  · intro t ht
    exact ⟨(hrep t ht).1, (hrep t ht).2.1, (hrep t ht).2.2.1, (hrep t ht).2.2.2.1⟩

/-- Arbitrary H² × H¹ data produce a first-jet weak wave with the exact
L-infinity-in-time H²/H¹/L² regularity, for merely globally Lipschitz f. -/
theorem exists_energySolution_h2 (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (g : W^{2,2}(ℝ^n)) (v : H¹(ℝ^n)) :
    ∃ u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ),
      IsEnergySolution hf hf0
        (lowerOrderCLM (by decide : 1 ≤ 2) g, (energyTriple n).inclusion v) u ∧
      ∀ T : ℝ, ∃ (U : ℝ → W^{2,2}(ℝ^n)) (V : ℝ → H¹(ℝ^n))
        (A : ℝ → DerivLp n 2 univ),
        MemLp U ∞ (volume.restrict (Icc 0 T)) ∧
        MemLp V ∞ (volume.restrict (Icc 0 T)) ∧
        MemLp A ∞ (volume.restrict (Icc 0 T)) ∧
        ∀ t ∈ Icc (0 : ℝ) T,
          lowerOrderCLM (by decide : 1 ≤ 2) (U t) = (u t).1 ∧
          (energyTriple n).inclusion (V t) = (u t).2 ∧
          (energyTriple n).pivotToDual (A t) = acceleration hf hf0 (u t) ∧
          A t = Δ (U t) - reaction hf hf0 (u t) := by
  obtain ⟨u, hu⟩ := exists_energySolution hf hf0
    (lowerOrderCLM (by decide : 1 ≤ 2) g, (energyTriple n).inclusion v)
  exact ⟨u, hu, fun T ↦ hu.exists_memLp_h2_lifts (hasGeneratorAt_h2 g v) T⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
