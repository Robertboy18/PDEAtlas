/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Derivative.Evolution

/-!
# Affine H² evolutions along the characteristics

Along the characteristics `X` of an H² curve, consider the affine equation

  `q (X a t) t = Q₀ a + ∫₀ᵗ (L s (q s) + S s) (X a s) ds`,

where `L s` is a bounded linear operator on H² and `S s` an H² forcing, both measurable and
bounded in time. Composition with the forward and inverse characteristics acts boundedly on H²
over the whole closed interval, so in characteristic coordinates this is a globally Lipschitz
Carathéodory equation in H². It has a bounded strongly measurable H² solution on the entire
interval, without any smallness of the time interval.

This generalizes the construction of the first-derivative evolution, where `L s q = ω H q` and
`S = 0`. The higher spatial derivatives of a De Gregorio solution satisfy equations of this form.

## Main results

* `HkCharacteristics.exists_h2_affine_evolution`: existence of the H² solution.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped Topology Sobolev ENNReal
open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- An affine equation along the characteristics, with a bounded measurable family of
linear operators and a bounded measurable forcing on H², has a bounded strongly measurable H²
solution on the whole closed interval. -/
theorem HkCharacteristics.exists_h2_affine_evolution
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} {hT : 0 ≤ T}
    {f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B)}
    {c X Y : ℝ → ℝ → ℝ} (hchar : HkCharacteristics hT f c X Y)
    (L : Icc (0 : ℝ) T → W^{2,2}(ℝ^1) →L[ℝ] W^{2,2}(ℝ^1))
    (hL : ∀ V : Icc (0 : ℝ) T → W^{2,2}(ℝ^1), StronglyMeasurable V →
      StronglyMeasurable (fun t ↦ L t (V t)))
    {K : ℝ} (hK : 0 ≤ K) (hLnorm : ∀ t V, ‖L t V‖ ≤ K * ‖V‖)
    (S : Icc (0 : ℝ) T → W^{2,2}(ℝ^1)) (hS : StronglyMeasurable S)
    {M : ℝ} (hSnorm : ∀ t, ‖S t‖ ≤ M) (Q₀ : W^{2,2}(ℝ^1)) :
    ∃ q : Icc (0 : ℝ) T → W^{2,2}(ℝ^1),
      StronglyMeasurable q ∧ (∃ C ≥ 0, ∀ t, ‖q t‖ ≤ C) ∧
      ∀ a (t : Icc (0 : ℝ) T),
        realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (q t)) (X a t) =
          realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) Q₀) a +
            ∫ s in 0..(t : ℝ), realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2)
              (L (projIcc 0 T hT s) (q (projIcc 0 T hT s)) + S (projIcc 0 T hT s))) (X a s) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (DerivLp 1 2 univ) := Lp.SecondCountableTopology
  have : SecondCountableTopology (W^{2,2}(ℝ^1)) := by infer_instance
  let : MeasurableSpace (W^{2,2}(ℝ^1)) := borel _
  have : BorelSpace (W^{2,2}(ℝ^1)) := ⟨rfl⟩
  obtain ⟨P, Q, hP, hQ, C, hC, hnorm⟩ := hchar.exists_h2_pullbacks
  have hXm : Measurable (Function.uncurry (fun (t : Icc (0 : ℝ) T) x ↦ X x t)) :=
    (hchar.flow_continuous.comp continuous_swap).measurable
  have hYm : Measurable (Function.uncurry (fun (t : Icc (0 : ℝ) T) x ↦ Y x t)) :=
    (hchar.inverse_continuous.comp continuous_swap).measurable
  have hPm {V : Icc (0 : ℝ) T → W^{2,2}(ℝ^1)} (hV : StronglyMeasurable V) :
      StronglyMeasurable (fun t ↦ P t (V t)) :=
    stronglyMeasurable_h2_pullback hXm P hP hV
  have hQm {V : Icc (0 : ℝ) T → W^{2,2}(ℝ^1)} (hV : StronglyMeasurable V) :
      StronglyMeasurable (fun t ↦ Q t (V t)) :=
    stronglyMeasurable_h2_pullback hYm Q hQ hV
  let N (t : Icc (0 : ℝ) T) : W^{2,2}(ℝ^1) →L[ℝ] W^{2,2}(ℝ^1) := (P t).comp ((L t).comp (Q t))
  have hNm (V : W^{2,2}(ℝ^1)) : StronglyMeasurable (fun t ↦ N t V) :=
    hPm (hL _ (hQm stronglyMeasurable_const))
  let D := C * K * C
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hNnorm (t : Icc (0 : ℝ) T) (V : W^{2,2}(ℝ^1)) : ‖N t V‖ ≤ D * ‖V‖ := by
    calc ‖N t V‖ ≤ C * (K * ‖Q t V‖) := (hnorm t _).1.trans (by gcongr; exact hLnorm _ _)
      _ ≤ C * (K * (C * ‖V‖)) := by gcongr; exact (hnorm t V).2
      _ = D * ‖V‖ := by dsimp only [D]; ring
  let F : ℝ → W^{2,2}(ℝ^1) → W^{2,2}(ℝ^1) :=
    fun s V ↦ N (projIcc 0 T hT s) V + P (projIcc 0 T hT s) (S (projIcc 0 T hT s))
  have hPS : StronglyMeasurable (fun t ↦ P t (S t)) := hPm hS
  have hF (V : W^{2,2}(ℝ^1)) :
      Measurable (indicator (Icc (0 : ℝ) T) (fun s ↦ F s V)) :=
    (((hNm V).add hPS).comp_measurable continuous_projIcc.measurable).measurable.indicator
      measurableSet_Icc
  have hKF (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) T) : LipschitzWith ⟨D, hD⟩ (F s) := by
    apply LipschitzWith.of_dist_le_mul
    intro V U
    change dist (N _ V + _) (N _ U + _) ≤ D * dist V U
    rw [dist_add_right, dist_eq_norm, dist_eq_norm, ← map_sub]
    exact hNnorm _ _
  have hzero : IntegrableOn (fun s ↦ F s 0) (Icc (0 : ℝ) T) volume := by
    simp only [F, map_zero, zero_add]
    exact (integrableOn_const (C := C * M) (hs := measure_Icc_lt_top.ne)).mono'
      (hPS.comp_measurable continuous_projIcc.measurable).aestronglyMeasurable.restrict
      (.of_forall fun s ↦ (hnorm _ _).1.trans (mul_le_mul_of_nonneg_left (hSnorm _) hC))
  obtain ⟨Z, hZ, _huniq⟩ :=
    existsUnique_nonlinear_integralCurve hT F hF ⟨D, hD⟩ hKF hzero (P ⟨0, le_rfl, hT⟩ Q₀)
  let q (t : Icc (0 : ℝ) T) := Q t (Z t)
  have hq : StronglyMeasurable q := hQm Z.continuous.stronglyMeasurable
  have hintegrable : IntegrableOn
      (fun s ↦ F s (IccExtend hT Z s)) (Icc (0 : ℝ) T) volume :=
    integrableOn_field_apply_continuousOn hT F hF ⟨D, hD⟩ hKF hzero
      (Z.continuous.Icc_extend' (h := hT)).continuousOn
  refine ⟨q, hq, ⟨C * ‖Z‖, mul_nonneg hC (norm_nonneg _), fun t ↦
    ((hnorm t (Z t)).2.trans (mul_le_mul_of_nonneg_left
      (ContinuousMap.norm_coe_le_norm Z t) hC))⟩, fun a t ↦ ?_⟩
  let E : W^{2,2}(ℝ^1) →L[ℝ] ℝ :=
    (realLineRepresentativeEvalCLM a).comp (lowerOrderCLM (by decide : 1 ≤ 2))
  have heq := congrArg E (hZ t)
  have hint : IntervalIntegrable (fun s ↦ F s (IccExtend hT Z s)) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le t.property.1).mpr
      (hintegrable.mono_set (Icc_subset_Icc_right t.property.2))
  rw [map_add, ← E.intervalIntegral_comp_comm hint] at heq
  have hqt :
      realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (q t)) (X a t) = E (Z t) := by
    change realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (Q t (Z t))) (X a t) = _
    rw [hQ]
    exact congrArg _ (hchar.inverse_flow a t t.property)
  have hE0 : E (P ⟨0, le_rfl, hT⟩ Q₀) =
      realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) Q₀) a := by
    change realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (P ⟨0, le_rfl, hT⟩ Q₀)) a = _
    rw [hP]
    exact congrArg _ (hchar.flow_initial a)
  rw [hqt, heq, hE0]
  refine congrArg _ (intervalIntegral.integral_congr fun s hs ↦ ?_)
  have hsI : s ∈ Icc (0 : ℝ) T := (uIcc_subset_Icc ⟨le_rfl, hT⟩ t.property) hs
  change E (N (projIcc 0 T hT s) (IccExtend hT Z s) +
    P (projIcc 0 T hT s) (S (projIcc 0 T hT s))) = _
  rw [IccExtend_of_mem hT Z hsI, projIcc_of_mem hT hsI]
  change realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2)
    (P ⟨s, hsI⟩ (L ⟨s, hsI⟩ (Q ⟨s, hsI⟩ (Z ⟨s, hsI⟩))) + P ⟨s, hsI⟩ (S ⟨s, hsI⟩))) a = _
  rw [← map_add, hP]

end DeGregorio.Iteration
