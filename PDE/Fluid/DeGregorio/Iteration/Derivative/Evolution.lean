/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Derivative.Pullback
public import PDE.Fluid.DeGregorio.Iteration.Derivative.Source
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Measurability
public import PDE.Fluid.DeGregorio.Iteration.Picard.Output

/-!
# Construction of the H² first-derivative evolution

For the local Picard trajectory, the equation for the first spatial
derivative becomes a bounded linear equation in characteristic coordinates.
The coefficient graph need only be measurable in H². The existing Banach-space
Carathéodory theorem constructs its solution on the entire local interval.

This construction supplies the higher-regularity candidate. Identifying it
with the already existing spatial derivative is a separate uniqueness step.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped Topology Sobolev ENNReal
open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- Lift a frozen output to its bounded measurable H² coefficient graph. -/
theorem IsHkFrozenOutput.exists_measurable_h2_graph
    {B : NNReal} {T R : ℝ} {hT : 0 ≤ T}
    {f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B)}
    {W₀ : W^{2,2}(ℝ^1)} {w₀ : ℝ → ℝ} {c w : ℝ → ℝ → ℝ}
    (h : IsHkFrozenOutput hT f f W₀ w₀ c w) :
    ∃ W : Icc (0 : ℝ) T → W^{2,2}(ℝ^1),
      StronglyMeasurable W ∧ (∀ t, ‖W t‖ ≤ B) ∧
      (∀ t, wkpBaseCoordinateCLM (W t) = (f t).val) ∧
      ∀ t, realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (W t)) =
        fun x ↦ w x t := by
  have hex (t : Icc (0 : ℝ) T) : ∃ W : W^{2,2}(ℝ^1),
      ‖W‖ ≤ B ∧ wkpBaseCoordinateCLM W = (f t).val := (f t).property.1
  choose W hWnorm hWbase using hex
  have hW : StronglyMeasurable W := by
    apply stronglyMeasurable_of_wkpBaseCoordinateCLM isOpen_univ
    simpa only [hWbase, Function.comp_def] using
      (continuous_subtype_val.comp f.continuous).stronglyMeasurable
  refine ⟨W, hW, hWnorm, hWbase, fun t ↦ ?_⟩
  apply (Continuous.ae_eq_iff_eq volume (continuous_realLineRepresentative _)
    (h.continuous.comp (continuous_id.prodMk (continuous_const (y := t))))).mp
  apply (realLineRepresentative_lowerOrder_ae (W t)).symm.trans
  rw [hWbase]
  exact h.representative t

/-- The first-derivative equation along the characteristics has a
uniformly H²-bounded solution for every H² initial derivative. Neither strong
H² continuity of the coefficient nor C² vorticity is assumed. -/
theorem IsHkFrozenOutput.exists_h2_firstDerivative_evolution
    {B : NNReal} {T R : ℝ} {hT : 0 ≤ T}
    {f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B)}
    {W₀ : W^{2,2}(ℝ^1)} {w₀ : ℝ → ℝ} {c w X Y : ℝ → ℝ → ℝ}
    (h : IsHkFrozenOutput hT f f W₀ w₀ c w)
    (hchar : HkCharacteristics hT f c X Y) (Q₀ : W^{2,2}(ℝ^1)) :
    ∃ q : Icc (0 : ℝ) T → W^{2,2}(ℝ^1),
      StronglyMeasurable q ∧ (∃ C ≥ 0, ∀ t, ‖q t‖ ≤ C) ∧
      ∀ a (t : Icc (0 : ℝ) T),
        realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (q t)) (X a t) =
          realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) Q₀) a +
            ∫ s in 0..(t : ℝ), w (X a s) s *
              realLineRepresentative (realHilbertH1
                (lowerOrderCLM (by decide : 1 ≤ 2) (q (projIcc 0 T hT s)))) (X a s) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (DerivLp 1 2 univ) := Lp.SecondCountableTopology
  have : SecondCountableTopology (W^{2,2}(ℝ^1)) := by infer_instance
  let : MeasurableSpace (W^{2,2}(ℝ^1)) := borel _
  have : BorelSpace (W^{2,2}(ℝ^1)) := ⟨rfl⟩
  obtain ⟨W, hW, hWnorm, _hWbase, hWrep⟩ := h.exists_measurable_h2_graph
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
  let L (t : Icc (0 : ℝ) T) : W^{2,2}(ℝ^1) →L[ℝ] W^{2,2}(ℝ^1) :=
    (P t).comp ((firstDerivativeSourceH2CLM (W t)).comp (Q t))
  have hLm (V : W^{2,2}(ℝ^1)) : StronglyMeasurable (fun t ↦ L t V) :=
    hPm (firstDerivativeSourceH2CLM.continuous₂.comp_stronglyMeasurable
      (hW.prodMk (hQm stronglyMeasurable_const)))
  let D := C * (36 * succOrderAssemblyNormBound 1 1) * (B : ℝ) * C
  have hS : 0 ≤ 36 * succOrderAssemblyNormBound 1 1 :=
    mul_nonneg (by norm_num) succOrderAssemblyNormBound_nonneg
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hLnorm (t : Icc (0 : ℝ) T) (V : W^{2,2}(ℝ^1)) :
      ‖L t V‖ ≤ D * ‖V‖ := by
    calc
      ‖L t V‖ ≤ C * ‖firstDerivativeSourceH2CLM (W t) (Q t V)‖ := (hnorm t _).1
      _ ≤ C * ((36 * succOrderAssemblyNormBound 1 1) * ‖W t‖ * ‖Q t V‖) :=
        mul_le_mul_of_nonneg_left (norm_firstDerivativeSourceH2CLM_apply_le _ _) hC
      _ ≤ C * ((36 * succOrderAssemblyNormBound 1 1) * (B : ℝ) * (C * ‖V‖)) := by
        gcongr
        exacts [hWnorm t, (hnorm t V).2]
      _ = D * ‖V‖ := by dsimp only [D]; ring
  let F : ℝ → W^{2,2}(ℝ^1) → W^{2,2}(ℝ^1) :=
    fun s ↦ L (projIcc 0 T hT s)
  have hF (V : W^{2,2}(ℝ^1)) :
      Measurable (indicator (Icc (0 : ℝ) T) (fun s ↦ F s V)) :=
    ((hLm V).comp_measurable continuous_projIcc.measurable).measurable.indicator
      measurableSet_Icc
  have hK (s : ℝ) (_hs : s ∈ Icc (0 : ℝ) T) : LipschitzWith ⟨D, hD⟩ (F s) :=
    (L (projIcc 0 T hT s)).lipschitzWith.weaken
      (ContinuousLinearMap.opNorm_le_bound _ hD (hLnorm _))
  have hzero : IntegrableOn (fun s ↦ F s 0) (Icc (0 : ℝ) T) volume := by
    have heq : (fun s ↦ F s 0) = fun _ : ℝ ↦ (0 : W^{2,2}(ℝ^1)) :=
      funext fun s ↦ map_zero (L (projIcc 0 T hT s))
    exact heq ▸ integrableOn_zero
  obtain ⟨Z, hZ, _huniq⟩ :=
    existsUnique_nonlinear_integralCurve hT F hF ⟨D, hD⟩ hK hzero Q₀
  let q (t : Icc (0 : ℝ) T) := Q t (Z t)
  have hq : StronglyMeasurable q := hQm Z.continuous.stronglyMeasurable
  have hintegrable : IntegrableOn
      (fun s ↦ F s (IccExtend hT Z s)) (Icc (0 : ℝ) T) volume :=
    integrableOn_field_apply_continuousOn hT F hF ⟨D, hD⟩ hK hzero
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
    change realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (Z t))
      (Y (X a t) t) = E (Z t)
    rw [hchar.inverse_flow a t t.property]
    rfl
  rw [hqt, heq]
  refine congrArg _ (intervalIntegral.integral_congr fun s hs ↦ ?_)
  have hsI : s ∈ Icc (0 : ℝ) T := (uIcc_subset_Icc ⟨le_rfl, hT⟩ t.property) hs
  change E (L (projIcc 0 T hT s) (IccExtend hT Z s)) = _
  rw [IccExtend_of_mem hT Z hsI, projIcc_of_mem hT hsI]
  change realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2)
    (P ⟨s, hsI⟩ (firstDerivativeSourceH2CLM (W ⟨s, hsI⟩) (Q ⟨s, hsI⟩ (Z ⟨s, hsI⟩))))) a = _
  rw [hP, realLineRepresentative_firstDerivativeSourceH2CLM, hWrep]

end DeGregorio.Iteration
