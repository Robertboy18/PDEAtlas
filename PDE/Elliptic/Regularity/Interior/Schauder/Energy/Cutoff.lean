/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.DivergenceForm
public import PDE.Elliptic.Regularity.Localization.CutoffEquation.ZeroBoundaryCutoff
public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Localized
import PDE.Analysis.MeasureTheory.Lp.MultiplierPairing

/-!
# Quantitative cutoff energy for a scalar elliptic weak solution

Testing with `η²u` gives the Caccioppoli estimate with all coefficient and
cutoff dependence displayed. The formula is uniform over coefficient classes
with fixed essential bounds. It applies to an arbitrary open domain and
requires no boundary atlas.

This quantitative form supplies the energy input for constant coefficient
interior derivative estimates and the subsequent Schauder comparison.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Sobolev ENNReal InnerProductSpace Distributions

namespace SobolevSpace.GraphSpace

open DifferenceQuotient

variable {n : ℕ} {Ω : Set ℝ^n}

/-- The cutoff gradient energy is controlled by the coefficient bounds and
the L² data. All constants are explicit, independently of the solution. -/
theorem IsInteriorWeakDivergenceSolution.cutoff_gradient_sq_le
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {α : ℝ} (ha : AEUniformlyElliptic a α)
    (f : DerivLp n 2 Ω) (u : H¹(Ω)) (hu : IsInteriorWeakDivergenceSolution a f u)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω) :
    α ^ 2 * ∑ i, ‖(testFunctionLpTop (Ω := Ω) η •
      wkpCoordinateCLM (singleDerivIndex n i) u : DerivLp n 2 Ω)‖ ^ 2 ≤
      4 * (∑ i, ∑ j, ‖a i j‖ * ‖partialTestFunctionLpTop (Ω := Ω) η i‖) ^ 2 *
        ‖wkpBaseCoordinateCLM u‖ ^ 2 +
      2 * α * ‖testFunctionLpTop (Ω := Ω) η‖ ^ 2 *
        ‖f‖ * ‖wkpBaseCoordinateCLM u‖ := by
  classical
  let q : DerivLp n ∞ Ω := testFunctionLpTop η
  let d (i : Fin n) : DerivLp n ∞ Ω := partialTestFunctionLpTop η i
  let t := wkpBaseCoordinateCLM u
  let du (i : Fin n) := wkpCoordinateCLM (singleDerivIndex n i) u
  let G : PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 Ω) := WithLp.toLp 2 (fun i ↦ q • du i)
  have hGi (i : Fin n) : ‖q • du i‖ ≤ ‖G‖ := PiLp.norm_apply_le G i
  have hGs : ∑ i, ‖q • du i‖ ^ 2 = ‖G‖ ^ 2 := (PiLp.norm_sq_eq_of_L2 _ G).symm
  let v : H¹₀(Ω) := cutoffH1ToH10 hu.isOpen (squaredCutoff η)
    ((tsupport_squaredCutoff_subset η).trans hη) u
  have hv₀ : baseCoordCLM v = q • (q • t) := by
    rw [baseCoordCLM_cutoffH1ToH10]
    change testFunctionLpTop (Ω := Ω) (TestFunction.mul η η) • t = _
    rw [testFunctionLpTop_mul, lpSMul_top_top_two_assoc]
  have hvd (i : Fin n) : derivCoordCLM i v =
      q • (q • du i) + (q • (d i • t) + q • (d i • t)) := by
    rw [derivCoordCLM_cutoffH1ToH10, partialSquaredCutoff_smul]
    change testFunctionLpTop (Ω := Ω) (TestFunction.mul η η) • du i + _ = _
    simp only [testFunctionLpTop_mul, ← lpSMul_top_top_two_assoc]
    rfl
  have hpr (i j : Fin n) : ⟪a i j • du j, derivCoordCLM i v⟫_ℝ =
      ⟪a i j • (q • du j), q • du i⟫_ℝ +
        2 * ⟪a i j • (q • du j), d i • t⟫_ℝ := by
    rw [hvd, inner_add_right, inner_add_right]
    simp only [← Lp.inner_lpSMul_left q, lpSMul_top_top_two_comm q (a i j)]
    ring
  have hcross (i j : Fin n) :
      |⟪a i j • (q • du j), d i • t⟫_ℝ| ≤
        ‖a i j‖ * ‖d i‖ * ‖G‖ * ‖t‖ := by
    calc
      _ ≤ ‖a i j‖ * ‖q • du j‖ * ‖d i • t‖ := Lp.abs_inner_lpSMul_le _ _ _
      _ ≤ ‖a i j‖ * ‖G‖ * (‖d i‖ * ‖t‖) := by gcongr; exacts [hGi j, Lp.norm_smul_le _ _]
      _ = _ := by ring
  let M : ℝ := ∑ i, ∑ j, ‖a i j‖ * ‖d i‖
  have hprincipal : α * ‖G‖ ^ 2 - 2 * M * ‖G‖ * ‖t‖ ≤
      interiorVariableCoeffForm (multiplicationCoefficientOperator a) u v := by
    have he := aeUniformlyElliptic_energy_le a ha (fun i ↦ q • du i)
    simp only [real_inner_self_eq_norm_sq, multiplicationCoefficientOperator_apply,
      hGs] at he
    have hc := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦
      Finset.sum_le_sum (s := Finset.univ) fun j _ ↦
        (neg_le_abs _).trans (hcross i j)
    simp only [Finset.sum_neg_distrib, ← Finset.sum_mul] at hc
    change α * ‖G‖ ^ 2 - 2 * M * ‖G‖ * ‖t‖ ≤
      ∑ i, ∑ j, ⟪a i j • du j, derivCoordCLM i v⟫_ℝ
    simp only [hpr, Finset.sum_add_distrib, ← Finset.mul_sum]
    dsimp only [M] at *
    simp only [← Finset.sum_mul]
    linarith
  have hqbase : ‖baseCoordCLM v‖ ≤ ‖q‖ ^ 2 * ‖t‖ := by
    rw [hv₀, sq, mul_assoc]
    exact (Lp.norm_smul_le _ _).trans (by gcongr; exact Lp.norm_smul_le _ _)
  have hf : loadFunctional f v ≤ ‖f‖ * ‖q‖ ^ 2 * ‖t‖ := by
    rw [mul_assoc]
    exact (le_abs_self _).trans ((abs_real_inner_le_norm f _).trans (by gcongr; exact hqbase))
  rw [hu.equation v] at hprincipal
  have he : α * ‖G‖ ^ 2 ≤ 2 * M * ‖G‖ * ‖t‖ + ‖f‖ * ‖q‖ ^ 2 * ‖t‖ := by
    linarith
  change α ^ 2 * ∑ i, ‖q • du i‖ ^ 2 ≤
    4 * M ^ 2 * ‖t‖ ^ 2 + 2 * α * ‖q‖ ^ 2 * ‖f‖ * ‖t‖
  rw [hGs]
  have hs := sq_nonneg (α * ‖G‖ - 2 * M * ‖t‖)
  have he' := mul_le_mul_of_nonneg_left he ha.1.le
  nlinarith only [hs, he']

end SobolevSpace.GraphSpace
