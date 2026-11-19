/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.TruncatedTesting
public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Localized
import PDE.Analysis.MeasureTheory.Lp.MultiplierPairing

/-!
# Superlevel cutoff energy for measurable elliptic coefficients

Testing the weak equation with `η² (u-k)₊` bounds the gradient of the
superlevel truncation. The forcing is restricted to the superlevel set before
applying Cauchy–Schwarz. Its integrability is derived from that of the original
forcing. No continuity of the state or coefficient field is needed.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Sobolev ENNReal InnerProductSpace Distributions

namespace SobolevSpace.GraphSpace

open DifferenceQuotient

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]
variable [IsFiniteMeasure (domainMeasure n Ω)]

/-- The superlevel Caccioppoli estimate, retaining the restricted forcing.
The cutoff is arbitrary and the coefficient entries are only essentially bounded.
All constants are displayed; in particular there is no dependence on the level. -/
theorem IsInteriorWeakDivergenceSolution.superlevel_cutoff_gradient_sq_le
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {α : ℝ} (ha : AEUniformlyElliptic a α)
    (f : DerivLp n 2 Ω) (u : H¹(Ω)) (hu : IsInteriorWeakDivergenceSolution a f u)
    (k : ℝ) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω) :
    let U := u - wkpConstant k
    let T := lipschitzCompositionOn hΩ.isOpen Lp.lipschitzWith_pos_part U
    let q : DerivLp n ∞ Ω := testFunctionLpTop η
    ∃ g : DerivLp n 2 Ω,
      (g : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        (fun x ↦ if 0 < wkpBaseCoordinateCLM U x then f x else 0) ∧
      α ^ 2 * ∑ i, ‖(q • wkpCoordinateCLM (singleDerivIndex n i) T :
        DerivLp n 2 Ω)‖ ^ 2 ≤
        4 * (∑ i, ∑ j, ‖a i j‖ * ‖partialTestFunctionLpTop (Ω := Ω) η i‖) ^ 2 *
          ‖wkpBaseCoordinateCLM T‖ ^ 2 +
        2 * α * ‖q‖ ^ 2 * ‖g‖ * ‖wkpBaseCoordinateCLM T‖ := by
  classical
  let U : H¹(Ω) := u - wkpConstant k
  let T : H¹(Ω) := lipschitzCompositionOn hΩ.isOpen Lp.lipschitzWith_pos_part U
  let q : DerivLp n ∞ Ω := testFunctionLpTop η
  let d (i : Fin n) : DerivLp n ∞ Ω := partialTestFunctionLpTop η i
  let t : DerivLp n 2 Ω := wkpBaseCoordinateCLM T
  let dt (i : Fin n) : DerivLp n 2 Ω := wkpCoordinateCLM (singleDerivIndex n i) T
  let E := {x | 0 < wkpBaseCoordinateCLM U x}
  have hE : MeasurableSet E :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable _).measurable
  let g : DerivLp n 2 Ω := (MemLp.indicator hE.nullMeasurableSet (Lp.memLp f)).toLp _
  have hg : (g : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ if 0 < wkpBaseCoordinateCLM U x then f x else 0 :=
    MemLp.coeFn_toLp _
  refine ⟨g, hg, ?_⟩
  let G : PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 Ω) :=
    WithLp.toLp 2 (fun i ↦ q • dt i)
  have hGi (i : Fin n) : ‖q • dt i‖ ≤ ‖G‖ := PiLp.norm_apply_le G i
  have hGs : ∑ i, ‖q • dt i‖ ^ 2 = ‖G‖ ^ 2 := (PiLp.norm_sq_eq_of_L2 _ G).symm
  let v : H¹₀(Ω) := cutoffH1ToH10 hΩ.isOpen (squaredCutoff η)
    ((tsupport_squaredCutoff_subset η).trans hη) T
  have hv₀ : baseCoordCLM v = q • (q • t) := by
    rw [baseCoordCLM_cutoffH1ToH10]
    change testFunctionLpTop (Ω := Ω) (TestFunction.mul η η) • t = _
    rw [testFunctionLpTop_mul, lpSMul_top_top_two_assoc]
  have hvd (i : Fin n) : derivCoordCLM i v =
      q • (q • dt i) + (q • (d i • t) + q • (d i • t)) := by
    rw [derivCoordCLM_cutoffH1ToH10, partialSquaredCutoff_smul]
    change testFunctionLpTop (Ω := Ω) (TestFunction.mul η η) • dt i + _ = _
    simp only [testFunctionLpTop_mul, ← lpSMul_top_top_two_assoc]
    rfl
  have hload : loadFunctional f v = loadFunctional g v := by
    rw [loadFunctional_apply, loadFunctional_apply, L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    have hv : (baseCoordCLM v : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ (squaredCutoff η).toFun x * t x :=
      cutoffCLM_base_apply_ae (squaredCutoff η) T
    filter_upwards [hg, hv,
      lipschitzCompositionOn_posPart_coordinate_ae U (baseIndex n 1)]
        with x hx hvx htx
    change t x = if 0 < wkpBaseCoordinateCLM U x then
      wkpBaseCoordinateCLM U x else 0 at htx
    by_cases h : 0 < wkpBaseCoordinateCLM U x
    · rw [hx, ite_eq_left h]
    · rw [ite_eq_right h] at htx
      simp only [hvx, htx, mul_zero, inner_zero_right]
  have hpr (i j : Fin n) : ⟪a i j • dt j, derivCoordCLM i v⟫_ℝ =
      ⟪a i j • (q • dt j), q • dt i⟫_ℝ +
        2 * ⟪a i j • (q • dt j), d i • t⟫_ℝ := by
    rw [hvd, inner_add_right, inner_add_right]
    simp only [← Lp.inner_lpSMul_left q, lpSMul_top_top_two_comm q (a i j)]
    ring
  have hcross (i j : Fin n) :
      |⟪a i j • (q • dt j), d i • t⟫_ℝ| ≤ ‖a i j‖ * ‖d i‖ * ‖G‖ * ‖t‖ := by
    calc
      _ ≤ ‖a i j‖ * ‖q • dt j‖ * ‖d i • t‖ := Lp.abs_inner_lpSMul_le _ _ _
      _ ≤ ‖a i j‖ * ‖G‖ * (‖d i‖ * ‖t‖) := by gcongr; exacts [hGi j, Lp.norm_smul_le _ _]
      _ = _ := by ring
  let M : ℝ := ∑ i, ∑ j, ‖a i j‖ * ‖d i‖
  have hprincipal : α * ‖G‖ ^ 2 - 2 * M * ‖G‖ * ‖t‖ ≤
      interiorVariableCoeffForm (multiplicationCoefficientOperator a) T v := by
    have he := aeUniformlyElliptic_energy_le a ha (fun i ↦ q • dt i)
    simp only [real_inner_self_eq_norm_sq, multiplicationCoefficientOperator_apply,
      hGs] at he
    have hc := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦
      Finset.sum_le_sum (s := Finset.univ) fun j _ ↦
        (neg_le_abs _).trans (hcross i j)
    simp only [Finset.sum_neg_distrib, ← Finset.sum_mul] at hc
    change α * ‖G‖ ^ 2 - 2 * M * ‖G‖ * ‖t‖ ≤
      ∑ i, ∑ j, ⟪a i j • dt j, derivCoordCLM i v⟫_ℝ
    simp only [hpr, Finset.sum_add_distrib, ← Finset.mul_sum]
    dsimp only [M] at *
    simp only [← Finset.sum_mul]
    linarith
  have hqbase : ‖baseCoordCLM v‖ ≤ ‖q‖ ^ 2 * ‖t‖ := by
    rw [hv₀, sq, mul_assoc]
    exact (Lp.norm_smul_le _ _).trans (by gcongr; exact Lp.norm_smul_le _ _)
  have hf : loadFunctional g v ≤ ‖g‖ * ‖q‖ ^ 2 * ‖t‖ := by
    rw [mul_assoc]
    exact (le_abs_self _).trans ((abs_real_inner_le_norm g (baseCoordCLM v)).trans (by gcongr))
  have hweak := hu.superlevel_cutoff_equation a f u k (squaredCutoff η)
    ((tsupport_squaredCutoff_subset η).trans hη)
  change interiorVariableCoeffForm (multiplicationCoefficientOperator a) T v =
    loadFunctional f v at hweak
  rw [hweak, hload] at hprincipal
  have he : α * ‖G‖ ^ 2 ≤ 2 * M * ‖G‖ * ‖t‖ + ‖g‖ * ‖q‖ ^ 2 * ‖t‖ := by
    linarith
  change α ^ 2 * ∑ i, ‖q • dt i‖ ^ 2 ≤
    4 * M ^ 2 * ‖t‖ ^ 2 + 2 * α * ‖q‖ ^ 2 * ‖g‖ * ‖t‖
  rw [hGs]
  have hs := sq_nonneg (α * ‖G‖ - 2 * M * ‖t‖)
  have he' := mul_le_mul_of_nonneg_left he ha.1.le
  nlinarith only [hs, he']

end SobolevSpace.GraphSpace
