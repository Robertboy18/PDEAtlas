/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.Dilation
public import PDE.Spaces.Sobolev.Calculus.Pullback.Dilation.Continuity

/-!
# Free self-similar heat evolution

The Ornstein–Uhlenbeck evolution in similarity variables is the actual heat
operator at time `exp τ - 1`, followed by spatial dilation by `exp (τ / 2)`
and multiplication by that same scalar. Parabolic covariance proves its
semigroup law; joint strong dilation continuity proves continuous orbits.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Fractional
open PDE.Analysis.Evolution
open scoped ENNReal NNReal Sobolev Topology

namespace HeatEquation.WholeSpace

variable {n k : ℕ}

/-- The physical heat time corresponding to a nonnegative similarity time. -/
def selfsimilarHeatTime (τ : ℝ≥0) : ℝ≥0 :=
  ⟨Real.exp τ - 1, sub_nonneg.2 (Real.one_le_exp_iff.2 τ.property)⟩

@[simp]
theorem coe_selfsimilarHeatTime (τ : ℝ≥0) :
    (selfsimilarHeatTime τ : ℝ) = Real.exp τ - 1 := rfl

/-- The spatial factor in the self-similar change of variables. -/
def selfsimilarFactor (τ : ℝ≥0) : ℝ := Real.exp ((τ : ℝ) / 2)

theorem selfsimilarFactor_pos (τ : ℝ≥0) : 0 < selfsimilarFactor τ := Real.exp_pos _

theorem one_le_selfsimilarFactor (τ : ℝ≥0) : 1 ≤ selfsimilarFactor τ :=
  Real.one_le_exp_iff.2 (by positivity)

@[simp]
theorem selfsimilarFactor_zero : selfsimilarFactor 0 = 1 := by
  simp [selfsimilarFactor]

@[simp]
theorem selfsimilarHeatTime_zero : selfsimilarHeatTime 0 = 0 := by
  apply NNReal.coe_injective
  rw [coe_selfsimilarHeatTime]
  norm_num

theorem selfsimilarFactor_add (s t : ℝ≥0) :
    selfsimilarFactor (s + t) = selfsimilarFactor s * selfsimilarFactor t := by
  simp only [selfsimilarFactor, NNReal.coe_add, add_div, Real.exp_add]

theorem selfsimilarFactor_sq (τ : ℝ≥0) : selfsimilarFactor τ ^ 2 = Real.exp τ := by
  rw [selfsimilarFactor, sq, ← Real.exp_add]
  congr 1
  ring

/-- Physical heat times compose with the dilation required by parabolic covariance. -/
theorem selfsimilarHeatTime_add (s t : ℝ≥0) :
    selfsimilarHeatTime (s + t) =
      parabolicHeatTime (selfsimilarFactor t) (selfsimilarHeatTime s) +
        selfsimilarHeatTime t := by
  apply NNReal.coe_injective
  simp only [coe_selfsimilarHeatTime, NNReal.coe_add, coe_parabolicHeatTime,
    selfsimilarFactor_sq, Real.exp_add]
  ring

/-- The actual free self-similar evolution on integer Sobolev graphs. -/
def selfsimilarHeatSobolev (n k : ℕ) (τ : ℝ≥0) : W^{k,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n) :=
  selfsimilarFactor τ •
    (dilationWkpCLM (by norm_num) (selfsimilarFactor τ)
      (selfsimilarFactor_pos τ).ne').comp (heatSobolev n k (selfsimilarHeatTime τ))

theorem selfsimilarHeatSobolev_apply (τ : ℝ≥0) (u : W^{k,2}(ℝ^n)) :
    selfsimilarHeatSobolev n k τ u = selfsimilarFactor τ •
      dilationWkpCLM (by norm_num) (selfsimilarFactor τ) (selfsimilarFactor_pos τ).ne'
        (heatSobolev n k (selfsimilarHeatTime τ) u) := rfl

/-- The exact physical L² change of variables defining free similarity evolution. -/
theorem baseL2_selfsimilarHeatSobolev (τ : ℝ≥0) (u : W^{k,2}(ℝ^n)) :
    baseL2 (selfsimilarHeatSobolev n k τ u) = selfsimilarFactor τ •
      Lp.compSMul volume 2 (selfsimilarFactor τ) (selfsimilarFactor_pos τ).ne'
        (heatL2 n (selfsimilarHeatTime τ) (baseL2 u)) := by
  rw [selfsimilarHeatSobolev_apply, baseL2_smul, baseL2_dilationWkpCLM,
    baseL2_heatSobolev]

@[simp]
theorem selfsimilarHeatSobolev_zero (u : W^{k,2}(ℝ^n)) :
    selfsimilarHeatSobolev n k 0 u = u := by
  simp only [selfsimilarHeatSobolev_apply, selfsimilarFactor_zero,
    selfsimilarHeatTime_zero, heatSobolev_zero, dilationWkpCLM_one, one_smul]

/-- The free similarity evolution satisfies the genuine semigroup law. -/
theorem selfsimilarHeatSobolev_add (s t : ℝ≥0) (u : W^{k,2}(ℝ^n)) :
    selfsimilarHeatSobolev n k (s + t) u =
      selfsimilarHeatSobolev n k s (selfsimilarHeatSobolev n k t u) := by
  simp only [selfsimilarHeatSobolev_apply, map_smul, smul_smul]
  rw [heatSobolev_dilationWkpCLM, ← heatSobolev_add, ← dilationWkpCLM_mul,
    ← selfsimilarHeatTime_add]
  simp only [← selfsimilarFactor_add, add_comm]

/-- Continuous orbits in the actual Sobolev graph, including similarity time zero. -/
theorem continuous_selfsimilarHeatSobolev (u : W^{k,2}(ℝ^n)) :
    Continuous (fun τ : ℝ≥0 ↦ selfsimilarHeatSobolev n k τ u) := by
  have hfactor : Continuous selfsimilarFactor := by unfold selfsimilarFactor; fun_prop
  have htime : Continuous selfsimilarHeatTime := by
    apply Continuous.subtype_mk
    fun_prop
  have hdilation := continuous_dilationWkpCLM_Ici (n := n) (k := k) (by norm_num : (0 : ℝ) < 1)
  have hpair : Continuous (fun τ : ℝ≥0 ↦
      (heatSobolev n k (selfsimilarHeatTime τ) u,
        (⟨selfsimilarFactor τ, one_le_selfsimilarFactor τ⟩ : Set.Ici (1 : ℝ)))) :=
    ((continuous_heatSobolev u).comp htime).prodMk (hfactor.subtype_mk _)
  simpa only [selfsimilarHeatSobolev_apply, Function.comp_def, Pi.smul_def'] using
    hfactor.smul (hdilation.comp hpair)

/-- The free self-similar heat family as a strongly continuous Sobolev semigroup. -/
def selfsimilarHeatSobolevSemigroup (n k : ℕ) :
    StronglyContinuousSemigroup (W^{k,2}(ℝ^n)) where
  toMonoidHom :=
    { toFun := fun τ ↦ selfsimilarHeatSobolev n k τ.toAdd
      map_one' := by
        apply ContinuousLinearMap.ext
        intro u
        exact selfsimilarHeatSobolev_zero u
      map_mul' := by
        intro s t
        apply ContinuousLinearMap.ext
        intro u
        exact selfsimilarHeatSobolev_add s.toAdd t.toAdd u }
  continuous_toPointwise := by
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    intro u
    exact continuous_selfsimilarHeatSobolev u

end HeatEquation.WholeSpace
