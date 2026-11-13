/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Generator
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import CAS.IntegrationTactic

/-!
# Laplace transforms of contraction semigroups

For a strongly continuous contraction semigroup `T`, this file constructs the
Laplace transform

`R_λ x = ∫ s in (0, ∞), exp (-λs) T(s)x`

as a bounded linear operator for `λ > 0`, with operator norm at most `λ⁻¹`.
Finite-horizon transforms are retained as the approximants used in the
improper-integral and generator arguments.

The finite-horizon generator identity contains the boundary term that disappears
as `t → ∞`, giving one of the two inverse identities. This is Evans §7.4.1, Theorem 3(ii):
the resolvent is the Laplace transform of the semigroup, formula (14).

## How it works

Evans proves `(λ - A) R_λ x = x` (his (15)) by differentiating `S(h) R_λ x` under the improper
integral, and `R_λ (λ - A) x = x` from (16) by moving `A` under the integral, which uses that
`A` is closed. We work with the finite-horizon transforms `∫₀ᵗ e^{-λs} T(s)x ds`
(`truncatedLaplaceTransform`) instead, where every integral is a proper Bochner integral. Each
of them lies in the generator domain, with a generator value that carries the boundary term
`e^{-λt} T(t)x` (`hasGeneratorAt_truncatedLaplaceTransform`), and on the domain it inverts
`λ - A` up to the same term (`truncatedLaplaceTransform_generator_identity`). Contractivity
makes the boundary term vanish as `t → ∞`. The identity on the domain then passes to the limit
directly (`laplaceTransform_generator_identity`), and the closedness of the generator
(`isClosed_generatorPMap`) carries the domain membership and the generator value to the limit
(`generatorPMap_laplaceTransform`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.4.1, Theorem 3(ii), (14), and its proof, (15)-(16),
  pp. 438-439. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set Topology

namespace PDE.Analysis.Evolution

namespace StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem continuous_weightedRealOrbit
    (T : StronglyContinuousSemigroup E) (lambda : ℝ) (x : E) :
    Continuous fun s : ℝ ↦ Real.exp (-lambda * s) • T.realOrbit x s := by
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    (T.continuous_realOrbit x)

/-- The finite-horizon Laplace transform of a semigroup orbit. -/
def truncatedLaplaceTransform [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (lambda : ℝ) (t : NNReal) : E →L[ℝ] E :=
  let integralLinearMap : E →ₗ[ℝ] E :=
    { toFun := fun x ↦
        ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-lambda * s) • T.realOrbit x s
      map_add' := by
        intro x y
        rw [← intervalIntegral.integral_add
          ((T.continuous_weightedRealOrbit lambda x).intervalIntegrable _ _)
          ((T.continuous_weightedRealOrbit lambda y).intervalIntegrable _ _)]
        apply intervalIntegral.integral_congr
        intro s _
        simp [realOrbit, smul_add]
      map_smul' := by
        intro c x
        rw [← intervalIntegral.integral_smul]
        apply intervalIntegral.integral_congr
        intro s _
        simp [realOrbit, smul_smul, mul_comm] }
  integralLinearMap.mkContinuousOfExistsBound <| by
    obtain ⟨C, hC0, hC⟩ := T.exists_norm_le_on_Icc t
    refine ⟨Real.exp (|lambda| * (t : ℝ)) * C * (t : ℝ), fun x ↦ ?_⟩
    change ‖∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-lambda * s) • T.realOrbit x s‖ ≤ _
    calc ‖∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-lambda * s) • T.realOrbit x s‖
        ≤ Real.exp (|lambda| * (t : ℝ)) * C * ‖x‖ * |(t : ℝ) - 0| := by
          refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs ↦ ?_
          rw [uIoc_of_le t.coe_nonneg] at hs
          rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, mul_assoc]
          gcongr Real.exp ?_ * ?_
          · exact (mul_le_mul_of_nonneg_right (neg_le_abs lambda) hs.1.le).trans
              (mul_le_mul_of_nonneg_left hs.2 (abs_nonneg _))
          · exact (T s.toNNReal).le_of_opNorm_le
              (hC s.toNNReal ⟨bot_le, Real.toNNReal_le_iff_le_coe.2 hs.2⟩) x
      _ = _ := by rw [sub_zero, abs_of_nonneg t.coe_nonneg]; ring

/-- Evaluating the truncated Laplace transform gives the weighted orbit integral. -/
@[simp]
theorem truncatedLaplaceTransform_apply [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (lambda : ℝ) (t : NNReal) (x : E) :
    T.truncatedLaplaceTransform lambda t x =
      ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-lambda * s) • T.realOrbit x s :=
  rfl

/-- On the generator domain, the truncated Laplace transform inverts
`λ - A` up to the terminal weighted-orbit term. -/
theorem truncatedLaplaceTransform_generator_identity [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (lambda : ℝ) (t : NNReal)
    (x : T.generatorPMap.domain) :
    T.truncatedLaplaceTransform lambda t
        (lambda • (x : E) - T.generatorPMap x) =
      (x : E) - Real.exp (-lambda * (t : ℝ)) • T t x := by
  have hderiv (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) (t : ℝ)) :
      HasDerivWithinAt (fun r : ℝ ↦ Real.exp (-lambda * r) • T.realOrbit x r)
        (Real.exp (-lambda * s) • T.realOrbit (T.generatorPMap x - lambda • (x : E)) s)
        (Ioi s) s := by
    have horbit : HasDerivWithinAt (T.realOrbit (x : E)) (T.realOrbit (T.generatorPMap x) s)
        (Ioi s) s := by
      simpa only [realOrbit, Real.coe_toNNReal s hs.1.le] using
        ((T.hasGeneratorAt_generatorPMap x).hasDerivWithinAt_realOrbit s.toNNReal).mono
          Ioi_subset_Ici_self
    have hweight : HasDerivWithinAt (fun r : ℝ ↦ Real.exp (-lambda * r))
        (-lambda * Real.exp (-lambda * s)) (Ioi s) s := by
      cas
    refine (hweight.fun_smul horbit).congr_deriv ?_
    simp only [realOrbit, map_sub, map_smul]
    module
  have htransform : T.truncatedLaplaceTransform lambda t (T.generatorPMap x - lambda • (x : E)) =
      Real.exp (-lambda * (t : ℝ)) • T t x - (x : E) := by
    rw [truncatedLaplaceTransform_apply]
    simpa [realOrbit] using intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      t.coe_nonneg (T.continuous_weightedRealOrbit lambda x).continuousOn hderiv
      ((T.continuous_weightedRealOrbit lambda _).intervalIntegrable _ _)
  rw [← neg_sub (T.generatorPMap x) (lambda • (x : E)), map_neg, htransform, neg_sub]

private theorem integral_exp_neg_mul {lambda : ℝ} (hlambda : lambda ≠ 0)
    (t : NNReal) :
    ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-lambda * s) =
      (1 - Real.exp (-lambda * (t : ℝ))) / lambda := by
  cas using hlambda

/-- A contraction semigroup has the natural finite-horizon Laplace-transform
bound `(1 - exp (-λt)) / λ`. -/
theorem norm_truncatedLaplaceTransform_le [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (hT : T.IsContraction)
    {lambda : ℝ} (hlambda : 0 < lambda) (t : NNReal) :
    ‖T.truncatedLaplaceTransform lambda t‖ ≤
      (1 - Real.exp (-lambda * (t : ℝ))) / lambda := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact div_nonneg
      (sub_nonneg.mpr <| Real.exp_le_one_iff.mpr <|
        mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlambda.le) t.coe_nonneg)
      hlambda.le
  intro x
  rw [truncatedLaplaceTransform_apply]
  calc
    ‖∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-lambda * s) • T.realOrbit x s‖ ≤
        ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-lambda * s) * ‖x‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le t.coe_nonneg
      · exact Filter.Eventually.of_forall fun s hs ↦ by
          have hs0 : 0 ≤ s := hs.1.le
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul_of_nonneg_left
            (hT.norm_apply_le s.toNNReal x) (Real.exp_nonneg _)
      · exact
          ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
            continuous_const).intervalIntegrable _ _
    _ = ((1 - Real.exp (-lambda * (t : ℝ))) / lambda) * ‖x‖ := by
      rw [intervalIntegral.integral_mul_const, integral_exp_neg_mul hlambda.ne']

private theorem map_weightedIntervalIntegral [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (lambda : ℝ) (x : E) (t h : NNReal) :
    T h (∫ s in (0 : ℝ)..(t : ℝ),
        Real.exp (-lambda * s) • T.realOrbit x s) =
      Real.exp (lambda * (h : ℝ)) •
        ((∫ s in (0 : ℝ)..(t + h : NNReal),
            Real.exp (-lambda * s) • T.realOrbit x s) -
          ∫ s in (0 : ℝ)..(h : ℝ),
            Real.exp (-lambda * s) • T.realOrbit x s) := by
  have hc := T.continuous_weightedRealOrbit lambda x
  calc
    _ = ∫ s in (0 : ℝ)..(t : ℝ), T h (Real.exp (-lambda * s) • T.realOrbit x s) :=
      ((T h).intervalIntegral_comp_comm (hc.intervalIntegrable 0 t)).symm
    _ = ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (lambda * (h : ℝ)) •
          (Real.exp (-lambda * (s + (h : ℝ))) • T.realOrbit x (s + (h : ℝ))) := by
      refine intervalIntegral.integral_congr fun s hs ↦ ?_
      have hs0 : 0 ≤ s := (uIcc_of_le t.coe_nonneg ▸ hs : s ∈ Icc 0 (t : ℝ)).1
      dsimp only
      rw [map_smul, smul_smul, ← Real.exp_add, realOrbit, realOrbit, ← T.map_add_apply,
        Real.toNNReal_add hs0 h.coe_nonneg, Real.toNNReal_coe, add_comm h]
      congr 2
      ring
    _ = Real.exp (lambda * (h : ℝ)) • ∫ s in (h : ℝ)..(t + h : NNReal),
          Real.exp (-lambda * s) • T.realOrbit x s := by
      rw [intervalIntegral.integral_smul]
      congr 1
      simpa only [zero_add, NNReal.coe_add] using
        intervalIntegral.integral_comp_add_right (a := 0) (b := (t : ℝ))
          (fun s : ℝ ↦ Real.exp (-lambda * s) • T.realOrbit x s) (h : ℝ)
    _ = _ := by
      congr 1
      simpa only [NNReal.coe_add] using (intervalIntegral.integral_interval_sub_left
        (hc.intervalIntegrable 0 (t + h : NNReal)) (hc.intervalIntegrable 0 h)).symm

private theorem realOrbit_truncatedLaplaceTransform [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (lambda : ℝ) (x : E) (t : NNReal)
    {h : ℝ} (hh : h ∈ Ici 0) :
    T.realOrbit (T.truncatedLaplaceTransform lambda t x) h =
      Real.exp (lambda * h) •
        ((∫ s in (0 : ℝ)..(t : ℝ) + h,
            Real.exp (-lambda * s) • T.realOrbit x s) -
          ∫ s in (0 : ℝ)..h,
            Real.exp (-lambda * s) • T.realOrbit x s) := by
  rw [realOrbit, truncatedLaplaceTransform_apply,
    T.map_weightedIntervalIntegral]
  simp only [NNReal.coe_add, Real.coe_toNNReal _ hh]

/-- A finite-horizon weighted orbit integral belongs to the generator domain.
Its generator value consists of the interior `λ` term and the two endpoint
terms from differentiation under translation. -/
theorem hasGeneratorAt_truncatedLaplaceTransform [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (lambda : ℝ) (t : NNReal) (x : E) :
    T.HasGeneratorAt (T.truncatedLaplaceTransform lambda t x)
      (lambda • T.truncatedLaplaceTransform lambda t x +
        Real.exp (-lambda * (t : ℝ)) • T t x - x) := by
  let weightedOrbit : ℝ → E := fun s ↦ Real.exp (-lambda * s) • T.realOrbit x s
  have hc : Continuous weightedOrbit := T.continuous_weightedRealOrbit lambda x
  have hupper : HasDerivAt (fun h : ℝ ↦ ∫ s in (0 : ℝ)..(t : ℝ) + h, weightedOrbit s)
      (Real.exp (-lambda * (t : ℝ)) • T t x) 0 := by
    simpa [weightedOrbit, realOrbit_coe] using
      (hc.integral_hasStrictDerivAt 0 ((t : ℝ) + 0)).hasDerivAt.comp_const_add (t : ℝ) 0
  have hlower : HasDerivAt (fun h : ℝ ↦ ∫ s in (0 : ℝ)..h, weightedOrbit s) x 0 := by
    simpa [weightedOrbit, realOrbit_zero] using (hc.integral_hasStrictDerivAt 0 0).hasDerivAt
  have hweight : HasDerivAt (fun h : ℝ ↦ Real.exp (lambda * h)) lambda 0 := by
    cas
  have hderiv : HasDerivAt (fun h : ℝ ↦ Real.exp (lambda * h) •
        ((∫ s in (0 : ℝ)..(t : ℝ) + h, weightedOrbit s) - ∫ s in (0 : ℝ)..h, weightedOrbit s))
      (lambda • T.truncatedLaplaceTransform lambda t x +
        Real.exp (-lambda * (t : ℝ)) • T t x - x) 0 := by
    refine (hweight.smul (hupper.sub hlower)).congr_deriv ?_
    simp only [weightedOrbit, Pi.sub_apply, mul_zero, Real.exp_zero, one_smul, add_zero,
      intervalIntegral.integral_same, sub_zero, truncatedLaplaceTransform_apply]
    module
  exact hderiv.hasDerivWithinAt.congr
    (fun h hh ↦ T.realOrbit_truncatedLaplaceTransform lambda x t hh)
    (by simpa only [weightedOrbit, add_zero] using
      T.realOrbit_truncatedLaplaceTransform lambda x t (show (0 : ℝ) ∈ Ici 0 by simp))

private theorem norm_weightedRealOrbit_le
    (T : StronglyContinuousSemigroup E) (hT : T.IsContraction)
    (lambda : ℝ) (x : E) (s : ℝ) :
    ‖Real.exp (-lambda * s) • T.realOrbit x s‖ ≤
      Real.exp (-lambda * s) * ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left
    (hT.norm_apply_le s.toNNReal x) (Real.exp_nonneg _)

private theorem integrableOn_weightedRealOrbit
    (T : StronglyContinuousSemigroup E) (hT : T.IsContraction)
    {lambda : ℝ} (hlambda : 0 < lambda) (x : E) :
    IntegrableOn
      (fun s : ℝ ↦ Real.exp (-lambda * s) • T.realOrbit x s)
      (Ioi 0) := by
  exact Integrable.mono'
    ((exp_neg_integrableOn_Ioi 0 hlambda).mul_const ‖x‖)
    (T.continuous_weightedRealOrbit lambda x).aestronglyMeasurable
    (Filter.Eventually.of_forall fun s ↦
      T.norm_weightedRealOrbit_le hT lambda x s)

private theorem norm_laplaceIntegral_le
    (T : StronglyContinuousSemigroup E) (hT : T.IsContraction)
    {lambda : ℝ} (hlambda : 0 < lambda) (x : E) :
    ‖∫ s in Ioi (0 : ℝ),
        Real.exp (-lambda * s) • T.realOrbit x s‖ ≤
      lambda⁻¹ * ‖x‖ := by
  calc
    ‖∫ s in Ioi (0 : ℝ),
        Real.exp (-lambda * s) • T.realOrbit x s‖ ≤
        ∫ s in Ioi (0 : ℝ), Real.exp (-lambda * s) * ‖x‖ := by
      exact MeasureTheory.norm_integral_le_of_norm_le
        ((exp_neg_integrableOn_Ioi 0 hlambda).mul_const ‖x‖)
        (Filter.Eventually.of_forall fun s ↦
          T.norm_weightedRealOrbit_le hT lambda x s)
    _ = (∫ s in Ioi (0 : ℝ), Real.exp (-lambda * s)) * ‖x‖ := by
      rw [MeasureTheory.integral_mul_const]
    _ = lambda⁻¹ * ‖x‖ := by
      rw [integral_exp_mul_Ioi (neg_lt_zero.mpr hlambda) 0]
      simp

/-- The Laplace transform of a contraction-semigroup orbit for a positive
spectral parameter. -/
def laplaceTransform
    (T : StronglyContinuousSemigroup E) (hT : T.IsContraction)
    {lambda : ℝ} (hlambda : 0 < lambda) : E →L[ℝ] E :=
  let integralLinearMap : E →ₗ[ℝ] E :=
    { toFun := fun x ↦
        ∫ s in Ioi (0 : ℝ),
          Real.exp (-lambda * s) • T.realOrbit x s
      map_add' := by
        intro x y
        rw [← MeasureTheory.integral_add
          (T.integrableOn_weightedRealOrbit hT hlambda x)
          (T.integrableOn_weightedRealOrbit hT hlambda y)]
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall fun s ↦ by
          simp [realOrbit, smul_add]
      map_smul' := by
        intro c x
        change
          (∫ s in Ioi (0 : ℝ),
            Real.exp (-lambda * s) • T.realOrbit (c • x) s) =
            c • ∫ s in Ioi (0 : ℝ),
              Real.exp (-lambda * s) • T.realOrbit x s
        rw [← MeasureTheory.integral_smul c]
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall fun s ↦ by
          simp [realOrbit, smul_smul, mul_comm] }
  integralLinearMap.mkContinuousOfExistsBound <| by
    exact ⟨lambda⁻¹, fun x ↦ T.norm_laplaceIntegral_le hT hlambda x⟩

/-- Evaluating the semigroup Laplace transform gives its improper Bochner integral. -/
@[simp]
theorem laplaceTransform_apply
    (T : StronglyContinuousSemigroup E) (hT : T.IsContraction)
    {lambda : ℝ} (hlambda : 0 < lambda) (x : E) :
    T.laplaceTransform hT hlambda x =
      ∫ s in Ioi (0 : ℝ),
        Real.exp (-lambda * s) • T.realOrbit x s :=
  rfl

/-- The Laplace transform of a contraction semigroup satisfies the
resolvent estimate `‖R_λ‖ ≤ λ⁻¹`. -/
theorem norm_laplaceTransform_le
    (T : StronglyContinuousSemigroup E) (hT : T.IsContraction)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    ‖T.laplaceTransform hT hlambda‖ ≤ lambda⁻¹ := by
  exact ContinuousLinearMap.opNorm_le_bound
    (T.laplaceTransform hT hlambda) (inv_nonneg.mpr hlambda.le) fun x ↦ by
      simpa only [laplaceTransform_apply] using
        T.norm_laplaceIntegral_le hT hlambda x

/-- Finite-horizon Laplace transforms converge strongly to the improper
Laplace transform. -/
theorem tendsto_truncatedLaplaceTransform_apply [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (hT : T.IsContraction)
    {lambda : ℝ} (hlambda : 0 < lambda) (x : E) :
    Tendsto
      (fun t : NNReal ↦ T.truncatedLaplaceTransform lambda t x)
      atTop (𝓝 (T.laplaceTransform hT hlambda x)) := by
  have hcoe :
      Tendsto (fun t : NNReal ↦ (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  simpa only [truncatedLaplaceTransform_apply, laplaceTransform_apply] using
    intervalIntegral_tendsto_integral_Ioi 0
      (T.integrableOn_weightedRealOrbit hT hlambda x) hcoe

private theorem tendsto_weighted_orbit_atTop
    (T : StronglyContinuousSemigroup E) (hT : T.IsContraction)
    {lambda : ℝ} (hlambda : 0 < lambda) (x : E) :
    Tendsto
      (fun t : NNReal ↦ Real.exp (-lambda * (t : ℝ)) • T t x)
      atTop (𝓝 0) := by
  refine squeeze_zero_norm
    (a := fun t : NNReal ↦ Real.exp (-lambda * (t : ℝ)) * ‖x‖)
    (fun t ↦ ?_) ?_
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left
      (hT.norm_apply_le t x) (Real.exp_nonneg _)
  · have hcoe :
        Tendsto (fun t : NNReal ↦ (t : ℝ)) atTop atTop :=
      NNReal.tendsto_coe_atTop.mpr tendsto_id
    have hdecay :
        Tendsto (fun t : NNReal ↦ Real.exp (-lambda * (t : ℝ))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp <|
        hcoe.const_mul_atTop_of_neg (neg_lt_zero.mpr hlambda)
    simpa using hdecay.mul_const ‖x‖

/-- On the generator domain, the Laplace transform is a left inverse for
`λ - A`: `R(λ)(λx - Ax) = x`. The proof lets the finite-horizon boundary
term tend to zero. -/
theorem laplaceTransform_generator_identity [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (hT : T.IsContraction)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (x : T.generatorPMap.domain) :
    T.laplaceTransform hT hlambda
        (lambda • (x : E) - T.generatorPMap x) = (x : E) := by
  have hright : Tendsto (fun t : NNReal ↦ (x : E) - Real.exp (-lambda * (t : ℝ)) • T t x)
      atTop (𝓝 (x : E)) := by
    simpa using tendsto_const_nhds.sub (T.tendsto_weighted_orbit_atTop hT hlambda (x : E))
  exact tendsto_nhds_unique (T.tendsto_truncatedLaplaceTransform_apply hT hlambda _)
    (hright.congr fun t ↦ (T.truncatedLaplaceTransform_generator_identity lambda t x).symm)

private theorem pair_mem_generatorPMap_graph_of_hasGeneratorAt
    (T : StronglyContinuousSemigroup E) {x Ax : E}
    (h : T.HasGeneratorAt x Ax) :
    (x, Ax) ∈ T.generatorPMap.graph := by
  let y : T.generatorPMap.domain := ⟨x, ⟨Ax, h⟩⟩
  refine (LinearPMap.mem_graph_iff T.generatorPMap).2 ⟨y, rfl, ?_⟩
  exact HasGeneratorAt.unique (T.hasGeneratorAt_generatorPMap y) h

private theorem laplaceTransform_mem_generatorPMap_graph [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (hT : T.IsContraction)
    {lambda : ℝ} (hlambda : 0 < lambda) (x : E) :
    (T.laplaceTransform hT hlambda x,
        lambda • T.laplaceTransform hT hlambda x - x) ∈
      T.generatorPMap.graph := by
  have htransform := T.tendsto_truncatedLaplaceTransform_apply hT hlambda x
  have hgenerator : Tendsto (fun t : NNReal ↦ lambda • T.truncatedLaplaceTransform lambda t x +
      Real.exp (-lambda * (t : ℝ)) • T t x - x) atTop
      (𝓝 (lambda • T.laplaceTransform hT hlambda x - x)) := by
    simpa only [add_zero] using ((htransform.const_smul lambda).add
      (T.tendsto_weighted_orbit_atTop hT hlambda x)).sub_const x
  exact T.isClosed_generatorPMap.mem_of_tendsto (htransform.prodMk_nhds hgenerator)
    (.of_forall fun t ↦ T.pair_mem_generatorPMap_graph_of_hasGeneratorAt
      (T.hasGeneratorAt_truncatedLaplaceTransform lambda t x))

/-- The Laplace transform of arbitrary data belongs to the natural domain of
the infinitesimal generator. -/
theorem laplaceTransform_mem_generatorPMap_domain [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (hT : T.IsContraction)
    {lambda : ℝ} (hlambda : 0 < lambda) (x : E) :
    T.laplaceTransform hT hlambda x ∈ T.generatorPMap.domain :=
  LinearPMap.mem_domain_of_mem_graph
    (T.laplaceTransform_mem_generatorPMap_graph hT hlambda x)

/-- Applying the generator to a Laplace transform gives `λR_λx - x`. -/
theorem generatorPMap_laplaceTransform [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (hT : T.IsContraction)
    {lambda : ℝ} (hlambda : 0 < lambda) (x : E) :
    T.generatorPMap
        ⟨T.laplaceTransform hT hlambda x,
          T.laplaceTransform_mem_generatorPMap_domain hT hlambda x⟩ =
      lambda • T.laplaceTransform hT hlambda x - x := by
  symm
  exact
    (LinearPMap.image_iff
      (T.laplaceTransform_mem_generatorPMap_domain hT hlambda x)).2
      (T.laplaceTransform_mem_generatorPMap_graph hT hlambda x)

/-- The shifted generator is a left inverse for the Laplace transform:
`(λ - A)R_λ = I`. -/
theorem generator_laplaceTransform_identity [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (hT : T.IsContraction)
    {lambda : ℝ} (hlambda : 0 < lambda) (x : E) :
    lambda • T.laplaceTransform hT hlambda x -
        T.generatorPMap
          ⟨T.laplaceTransform hT hlambda x,
            T.laplaceTransform_mem_generatorPMap_domain hT hlambda x⟩ =
      x := by
  rw [T.generatorPMap_laplaceTransform hT hlambda x]
  module

/-- Every positive `λ` lies in the resolvent set in the concrete sense that
`λ - A` maps the generator domain onto the ambient Banach space. -/
theorem exists_generator_shift_eq [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (hT : T.IsContraction)
    {lambda : ℝ} (hlambda : 0 < lambda) (x : E) :
    ∃ y : T.generatorPMap.domain,
      lambda • (y : E) - T.generatorPMap y = x := by
  let y : T.generatorPMap.domain :=
    ⟨T.laplaceTransform hT hlambda x,
      T.laplaceTransform_mem_generatorPMap_domain hT hlambda x⟩
  exact ⟨y, T.generator_laplaceTransform_identity hT hlambda x⟩

end StronglyContinuousSemigroup

end PDE.Analysis.Evolution
