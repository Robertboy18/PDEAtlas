/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.VariableCoefficient.Operator
public import PDE.Analysis.Calculus.SpaceTime.ForwardDerivative
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The initial limit of compact weighted matrix energy

The initial velocity is the right time derivative. A compact support contained
in the open initial data set gives a zero limit for the weighted energy.
The proof uses the continuous forward differential, so second derivatives
at initial time are unnecessary.
-/

@[expose] public noncomputable section

namespace WaveEquation.VariableCoefficient

open Filter MeasureTheory Set PDE.Common PDE.Analysis
open scoped Topology

variable {n : ℕ}

/-- Matrix energy evaluated on a differential, including a derivative within a half-space. -/
def differentialEnergy (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (x : ℝ^n)
    (D : ℝ^(n + 1) →L[ℝ] ℝ) : ℝ :=
  (1 / 2 : ℝ) * ((D (EuclideanSpace.single 0 1)) ^ 2 +
    ∑ i, ∑ j, a x i j * D (EuclideanSpace.single i.succ 1) *
      D (EuclideanSpace.single j.succ 1))

/-- Joint continuity of the matrix field and the differential gives continuous energy. -/
theorem continuous_differentialEnergy {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ}
    (ha : ∀ i j, Continuous (fun x ↦ a x i j)) :
    Continuous (fun p : (ℝ^n) × (ℝ^(n + 1) →L[ℝ] ℝ) ↦ differentialEnergy a p.1 p.2) := by
  apply continuous_const.mul
  apply Continuous.add
  · exact (continuous_snd.clm_apply continuous_const).pow 2
  · exact continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦
      (((ha i j).comp continuous_fst).mul (continuous_snd.clm_apply continuous_const)).mul
          (continuous_snd.clm_apply continuous_const)

/-- The energy of the zero differential is zero. -/
@[simp]
theorem differentialEnergy_zero (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (x : ℝ^n) :
    differentialEnergy a x 0 = 0 := by
  simp [differentialEnergy]

/-- A compactly supported continuous weight has zero initial energy for zero classical data. -/
theorem tendsto_weighted_energy_zero {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ}
    (ha : ∀ i j, Continuous (fun x ↦ a x i j)) {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiffOn ℝ 1 u {p | 0 ≤ p 0}) {φ : ℝ^(n + 1) → ℝ} (hφ : Continuous φ) {K S : Set (ℝ^n)}
    (hK : IsCompact K) (hS : IsOpen S) (hKS : K ⊆ S) (hpos : ∀ x ∈ S, u (timeSpaceCons 0 x) = 0)
    (hvel : ∀ x ∈ S, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = 0)
    (hs : ∀ t : ℝ, 0 < t → ∀ x ∉ K, φ (timeSpaceCons t x) = 0) :
    Tendsto (fun t ↦ ∫ x, φ (timeSpaceCons t x) *
      energyDensity a u (timeSpaceCons t x)) (𝓝[>] 0) (𝓝 0) := by
  let F : ℝ → ℝ^n → ℝ := fun t x ↦ φ (timeSpaceCons t x) *
    differentialEnergy a x (forwardDifferential u t x)
  have hc : Continuous (Function.uncurry F) := by
    apply (hφ.comp (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous).mul
    exact (continuous_differentialEnergy ha).comp
      (continuous_snd.prodMk (continuous_forwardDifferential hu))
  have hF : Continuous (fun t ↦ ∫ x in K, F t x) :=
    continuous_parametric_integral_of_continuous hc hK
  have hz : (∫ x in K, F 0 x) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ ?_
    simp [F, forwardDifferential_initial_eq_zero hu hS hpos hvel (hKS hx)]
  have heq : (fun t ↦ ∫ x, φ (timeSpaceCons t x) *
      energyDensity a u (timeSpaceCons t x)) =ᶠ[𝓝[>] 0] fun t ↦ ∫ x in K, F t x := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hpoint (x : ℝ^n) :
        F t x = φ (timeSpaceCons t x) * energyDensity a u (timeSpaceCons t x) := by
      simp only [F, forwardDifferential_eq_fderiv u ht x]
      rfl
    simp_rw [hpoint]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ by rw [hs t ht x hx, zero_mul])).symm
  exact (hz ▸ hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm

end WaveEquation.VariableCoefficient
