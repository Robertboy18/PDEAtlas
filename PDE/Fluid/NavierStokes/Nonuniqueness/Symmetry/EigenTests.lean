/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.Symmetry.SymmetricTests
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates
import PDE.Analysis.MeasureTheory.Function.LocalL2
import PDE.Analysis.MeasureTheory.Lp.EuclideanFields

/-!
# Extending the weak eigenvalue equation from odd tests

For `v` in whole-space `H¹` write `V = Stationary.representative v` and `G_{ij}` for the chosen
representative of the weak derivative `∂ⱼvᵢ`, and `gradientForm v x u w = Σᵢⱼ uᵢ G_{ij}(x) wⱼ`.
The weak eigenvalue density of `WeakEigenEquation U μ v` is the jet density with coefficients

`a = (μ - ½) V + G(U - ½ ξ) - (tr G) U`, `bⱼ = -Vⱼ U + G eⱼ`, `c = 0`

(`weakEigenDensity_eq_jetDensity`). If `V` is odd axisymmetric, the weak gradient transforms as
the gradient of an odd field, `G(g y)(u, w) = parity s · G(y)(g⁻¹u, g⁻¹w)` almost everywhere
(`IsOddAxisymmetric.isOddGradient`, by uniqueness of weak derivatives after the change of
variables `x = g y`). With `U` even axisymmetric the coefficients are then equivariant with the
odd character, and when `U` is square integrable on compact sets the eigenvalue equation tested
with the odd smooth compactly supported solenoidal fields holds for all of them
(`WeakEigenEquation.of_symmetric_tests`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace SobolevSpace.GraphSpace
open NavierStokes.Nonuniqueness
open scoped RealInnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert ContDiff Distributions

namespace NavierStokes.Symmetry

set_option linter.missingDocs true

local notation "H" => PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))

/-! ### The eigenvalue density as a jet density -/

/-- The bilinear form `Σᵢⱼ uᵢ G_{ij}(x) wⱼ` of the chosen weak gradient representative. -/
def gradientForm (v : H) (x : ℝ^3) : ℝ^3 →ₗ[ℝ] ℝ^3 →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u w ↦ ∑ i, ∑ j, u i * Stationary.gradientRepresentative v x i j * w j)
    (fun u u' w ↦ by simp only [PiLp.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c u w ↦ by simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc])
    (fun u w w' ↦ by simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c u w ↦ by
      simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      ring)

/-- Evaluation of the gradient form. -/
theorem gradientForm_apply (v : H) (x u w : ℝ^3) :
    gradientForm v x u w = ∑ i, ∑ j, u i * Stationary.gradientRepresentative v x i j * w j :=
  rfl

/-- The trace `Σⱼ G_{jj}(x)`, the chosen representative of the weak divergence. -/
def gradientTrace (v : H) (x : ℝ^3) : ℝ := ∑ j, Stationary.gradientRepresentative v x j j

/-- The trace is the diagonal sum of the gradient form. -/
theorem gradientTrace_eq (v : H) (x : ℝ^3) :
    gradientTrace v x =
      ∑ k, gradientForm v x (EuclideanSpace.single k 1) (EuclideanSpace.single k 1) := by
  simp [gradientTrace, gradientForm_apply]

/-- The zeroth-order coefficient `(μ - ½) V + G(U - ½ ξ) - (tr G) U` of the weak eigenvalue
density. -/
def eigenZeroth (U : ℝ^3 → ℝ^3) (μ : ℝ) (v : H) (x : ℝ^3) : ℝ^3 :=
  (μ - 1 / 2) • Stationary.representative v x +
    WithLp.toLp 2
      (fun i ↦ ∑ j, (U x j - 1 / 2 * x j) * Stationary.gradientRepresentative v x i j) -
    gradientTrace v x • U x

/-- The first-order coefficients `bⱼ = -Vⱼ U + G eⱼ` of the weak eigenvalue density. -/
def eigenFirst (U : ℝ^3 → ℝ^3) (v : H) (x : ℝ^3) (j : Fin 3) : ℝ^3 :=
  -(Stationary.representative v x j) • U x +
    WithLp.toLp 2 (fun i ↦ Stationary.gradientRepresentative v x i j)

/-- Pairing with the zeroth-order coefficient. -/
theorem inner_eigenZeroth (U : ℝ^3 → ℝ^3) (μ : ℝ) (v : H) (x u : ℝ^3) :
    ⟪u, eigenZeroth U μ v x⟫ = (μ - 1 / 2) * ⟪u, Stationary.representative v x⟫ +
      gradientForm v x u (U x - (1 / 2 : ℝ) • x) - gradientTrace v x * ⟪u, U x⟫ := by
  rw [eigenZeroth, inner_sub_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    gradientForm_apply]
  congr 2
  rw [EuclideanSpace.real_inner_eq_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- The first-order pairing of the eigenvalue coefficients is `-U·L V + Σⱼ G(L eⱼ, eⱼ)`. -/
theorem firstOrderPairing_eigenFirst (U : ℝ^3 → ℝ^3) (v : H) (x : ℝ^3)
    (L : ℝ^3 →L[ℝ] ℝ^3) :
    firstOrderPairing (eigenFirst U v x) L = -⟪U x, L (Stationary.representative v x)⟫ +
      ∑ j, gradientForm v x (L (EuclideanSpace.single j 1)) (EuclideanSpace.single j 1) := by
  rw [EuclideanSpace.map_eq_sum_smul_single L (Stationary.representative v x)]
  simp only [firstOrderPairing, eigenFirst, inner_add_left, real_inner_smul_left, inner_sum,
    real_inner_smul_right, Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [gradientForm_apply, EuclideanSpace.real_inner_eq_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [mul_comm]

/-- At a differentiability point of the test field, the weak eigenvalue density is the jet
density with coefficients `eigenZeroth`, `eigenFirst` and `0`. -/
theorem weakEigenDensity_eq_jetDensity (U : ℝ^3 → ℝ^3) (μ : ℝ) (v : H) {φ : ℝ^3 → ℝ^3}
    {x : ℝ^3} (hφ : DifferentiableAt ℝ φ x) :
    weakEigenDensity U μ v φ x = jetDensity (eigenZeroth U μ v) (eigenFirst U v) 0 φ x := by
  rw [jetDensity, sum_inner_partialDeriv_eq, firstOrderPairing_eigenFirst, real_inner_comm,
    inner_eigenZeroth, Pi.zero_apply, inner_zero_left, add_zero, weakEigenDensity]
  have hpart (i j : Fin 3) :
      (∂[j] (fun y ↦ φ y i)) x = (fderiv ℝ φ x (EuclideanSpace.single j 1)) i :=
    (PDE.partialDeriv_apply j i hφ).symm
  simp only [hpart, gradientForm_apply, real_inner_comm (φ x)]
  have h1 : ∑ x_1, ∑ x_2, (φ x) x_1 * Stationary.gradientRepresentative v x x_1 x_2 *
      (U x - (1 / 2 : ℝ) • x) x_2 = ∑ x_1, ∑ x_2, ((U x) x_2 - 1 / 2 * x x_2) *
        Stationary.gradientRepresentative v x x_1 x_2 * (φ x) x_1 := by
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have h2 : ∑ j, ∑ x_1, ∑ x_2, ((fderiv ℝ φ x) (EuclideanSpace.single j 1)) x_1 *
      Stationary.gradientRepresentative v x x_1 x_2 * (EuclideanSpace.single j (1 : ℝ)) x_2 =
      ∑ x_1, ∑ x_2, Stationary.gradientRepresentative v x x_1 x_2 *
        ((fderiv ℝ φ x) (EuclideanSpace.single x_2 1)) x_1 := by
    have h (j x_1 : Fin 3) : ∑ x_2, ((fderiv ℝ φ x) (EuclideanSpace.single j 1)) x_1 *
        Stationary.gradientRepresentative v x x_1 x_2 * (EuclideanSpace.single j (1 : ℝ)) x_2 =
        Stationary.gradientRepresentative v x x_1 j *
          ((fderiv ℝ φ x) (EuclideanSpace.single j 1)) x_1 := by
      simp [mul_comm]
    simp only [h]
    rw [Finset.sum_comm]
  rw [h1, h2, gradientTrace]
  ring

/-! ### Equivariance -/

/-- The weak gradient of `v` transforms as the gradient of an odd axisymmetric field. -/
def IsOddGradient (v : H) : Prop :=
  ∀ θ s, ∀ᵐ y ∂volume, ∀ u w : ℝ^3, gradientForm v (groupElement θ s y) u w =
    parity s * gradientForm v y ((groupElement θ s).symm u) ((groupElement θ s).symm w)

/-- The trace of an odd gradient changes by the character. -/
theorem gradientTrace_comp_of_isOddGradient {v : H} {θ : ℝ} {s : Bool} {y : ℝ^3}
    (h : ∀ u w : ℝ^3, gradientForm v (groupElement θ s y) u w =
      parity s * gradientForm v y ((groupElement θ s).symm u) ((groupElement θ s).symm w)) :
    gradientTrace v (groupElement θ s y) = parity s * gradientTrace v y := by
  rw [gradientTrace_eq, gradientTrace_eq]
  simp only [h, ← Finset.mul_sum]
  rw [EuclideanSpace.sum_bilinear_isometry (gradientForm v y) (groupElement θ s).symm]

/-- The coefficients of the weak eigenvalue density are equivariant with the odd character. -/
theorem isEquivariantJet_eigen {U : ℝ^3 → ℝ^3} {μ : ℝ} {v : H} (hU : IsEvenAxisymmetric U)
    (hV : IsOddAxisymmetric (Stationary.representative v)) (hG : IsOddGradient v) :
    IsEquivariantJet true (eigenZeroth U μ v) (eigenFirst U v) 0 := by
  refine ⟨fun θ s ↦ ?_, fun θ s ↦ ?_, fun θ s ↦ ?_⟩
  · filter_upwards [hU.ae_comp_groupElement θ s, hV.ae_comp_groupElement θ s, hG θ s]
      with y hUy hVy hGy
    rw [Bool.true_and]
    set g := groupElement θ s
    have hflip (u w : ℝ^3) : ⟪u, g w⟫ = ⟪g.symm u, w⟫ := by
      rw [g.symm.inner_map_eq_flip, LinearIsometryEquiv.symm_symm]
    refine ext_inner_left ℝ fun u ↦ ?_
    rw [inner_eigenZeroth, real_inner_smul_right, hflip, inner_eigenZeroth, hVy, hUy, hGy,
      gradientTrace_comp_of_isOddGradient hGy]
    simp only [real_inner_smul_right, map_sub, map_smul, LinearIsometryEquiv.symm_apply_apply,
      hflip]
    ring
  · filter_upwards [hU.ae_comp_groupElement θ s, hV.ae_comp_groupElement θ s, hG θ s]
      with y hUy hVy hGy L
    rw [Bool.true_and, firstOrderPairing_eigenFirst, firstOrderPairing_eigenFirst, hUy, hVy]
    simp only [hGy, ContinuousLinearMap.comp_apply, groupCLM_apply, groupInvCLM_apply,
      map_smul, LinearIsometryEquiv.symm_apply_apply, real_inner_smul_right,
      LinearIsometryEquiv.inner_map_map, ← Finset.mul_sum]
    have htr := EuclideanSpace.sum_bilinear_isometry ((gradientForm v y).comp L.toLinearMap)
      (groupElement θ s).symm
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe] at htr
    rw [htr]
    ring
  · exact Eventually.of_forall fun y ↦ by simp

/-! ### Integrability -/

/-- The coefficients of the weak eigenvalue density are locally integrable when the base field
is square integrable on compact sets. -/
theorem isLocallyIntegrableJet_eigen {U : ℝ^3 → ℝ^3} (μ : ℝ) (v : H)
    (hUm : AEStronglyMeasurable U volume)
    (hU2 : LocallyIntegrable (fun x ↦ ‖U x‖ ^ 2) volume) :
    IsLocallyIntegrableJet (eigenZeroth U μ v) (eigenFirst U v) 0 := by
  set V := Stationary.representative v
  set G := Stationary.gradientRepresentative v
  have hV := Stationary.memLp_representative v
  have hVm : AEStronglyMeasurable V volume := hV.aestronglyMeasurable
  have hV2 := hV.locallyIntegrable_norm_sq
  have hG (i j : Fin 3) := Stationary.memLp_gradientRepresentative v i j
  have hGm (i j : Fin 3) : AEStronglyMeasurable (fun x ↦ G x i j) volume :=
    (hG i j).aestronglyMeasurable
  have hG2 (i j : Fin 3) := (hG i j).locallyIntegrable_norm_sq
  have hcoord (j : Fin 3) : Continuous (fun x : ℝ^3 ↦ x j) :=
    (EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).continuous
  have hUj (j : Fin 3) : AEStronglyMeasurable (fun x ↦ U x j) volume :=
    (EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hUm
  have hVj (j : Fin 3) : AEStronglyMeasurable (fun x ↦ V x j) volume :=
    (EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hVm
  have hWm : AEStronglyMeasurable
      (fun x ↦ WithLp.toLp 2 (fun i ↦ ∑ j, (U x j - 1 / 2 * x j) * G x i j) : ℝ^3 → ℝ^3)
      volume :=
    aestronglyMeasurable_toLp fun i ↦ Finset.aestronglyMeasurable_fun_sum _ fun j _ ↦
      ((hUj j).sub (continuous_const.mul (hcoord j)).aestronglyMeasurable).mul (hGm i j)
  have htrm : AEStronglyMeasurable (fun x ↦ gradientTrace v x) volume :=
    Finset.aestronglyMeasurable_fun_sum _ fun j _ ↦ hGm j j
  have ham : AEStronglyMeasurable (eigenZeroth U μ v) volume :=
    (((hVm.const_smul (μ - 1 / 2)).add hWm).sub (htrm.smul hUm)).congr (.of_forall fun _ ↦ rfl)
  have hbm (j : Fin 3) : AEStronglyMeasurable (fun x ↦ eigenFirst U v x j) volume :=
    (((hVj j).neg.smul hUm).add (aestronglyMeasurable_toLp (f := fun i x ↦ G x i j)
      fun i ↦ hGm i j)).congr (.of_forall fun _ ↦ rfl)
  have hV1 := locallyIntegrable_norm_of_sq hVm hV2
  have hU1 := locallyIntegrable_norm_of_sq hUm hU2
  have hG1 (i j : Fin 3) := locallyIntegrable_norm_of_sq (hGm i j) (hG2 i j)
  have hUG (i j : Fin 3) := locallyIntegrable_norm_mul_norm hUm (hGm i j) hU2 (hG2 i j)
  have hxG (i j : Fin 3) : LocallyIntegrable (fun x ↦ ‖x‖ * ‖G x i j‖) volume :=
    (hG1 i j).continuous_mul continuous_norm
  have hVU := locallyIntegrable_norm_mul_norm hVm hUm hV2 hU2
  refine ⟨ham, hbm, aestronglyMeasurable_const, ?_, fun j ↦ ?_, ?_⟩
  · -- zeroth order
    have hdom : LocallyIntegrable (fun x ↦ |μ - 1 / 2| * ‖V x‖ +
        ∑ i, ∑ j, (2 * (‖U x‖ * ‖G x i j‖) + ‖x‖ * ‖G x i j‖)) volume :=
      (hV1.continuous_mul continuous_const).add (locallyIntegrable_finsetSum _ fun i _ ↦
        locallyIntegrable_finsetSum _ fun j _ ↦
          ((hUG i j).continuous_mul continuous_const).add (hxG i j))
    refine hdom.mono ham.norm (Eventually.of_forall fun x ↦ ?_)
    rw [norm_norm, Real.norm_of_nonneg (by positivity)]
    have hW : ‖(WithLp.toLp 2 (fun i ↦ ∑ j, (U x j - 1 / 2 * x j) * G x i j) : ℝ^3)‖ ≤
        ∑ i, ∑ j, (‖U x‖ + ‖x‖) * ‖G x i j‖ := by
      refine (EuclideanSpace.norm_le_sum_abs _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
      change |∑ j, (U x j - 1 / 2 * x j) * G x i j| ≤ _
      refine (Finset.abs_sum_le_sum_abs (fun j ↦ (U x j - 1 / 2 * x j) * G x i j)
        Finset.univ).trans (Finset.sum_le_sum fun j _ ↦ ?_)
      rw [abs_mul, Real.norm_eq_abs (G x i j)]
      gcongr
      have h1 : |U x j| ≤ ‖U x‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (U x) j
      have h2 : |x j| ≤ ‖x‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j
      have h3 : |1 / 2 * x j| = 1 / 2 * |x j| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith [abs_sub (U x j) (1 / 2 * x j), abs_nonneg (x j)]
    have htr : |gradientTrace v x| ≤ ∑ i, ∑ j, ‖G x i j‖ := by
      refine (Finset.abs_sum_le_sum_abs (fun j ↦ G x j j) Finset.univ).trans
        (Finset.sum_le_sum fun j _ ↦ ?_)
      rw [← Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun k ↦ ‖G x j k‖) (fun _ _ ↦ norm_nonneg _)
        (Finset.mem_univ j)
    calc ‖eigenZeroth U μ v x‖
        ≤ ‖(μ - 1 / 2) • V x‖ +
            ‖(WithLp.toLp 2 (fun i ↦ ∑ j, (U x j - 1 / 2 * x j) * G x i j) : ℝ^3)‖ +
            ‖gradientTrace v x • U x‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ |μ - 1 / 2| * ‖V x‖ + ∑ i, ∑ j, (‖U x‖ + ‖x‖) * ‖G x i j‖ +
            (∑ i, ∑ j, ‖G x i j‖) * ‖U x‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
          gcongr
      _ = |μ - 1 / 2| * ‖V x‖ +
            ∑ i, ∑ j, (2 * (‖U x‖ * ‖G x i j‖) + ‖x‖ * ‖G x i j‖) := by
          simp only [Finset.sum_mul, add_assoc, ← Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
          ring
  · have hdom : LocallyIntegrable (fun x ↦ ‖V x‖ * ‖U x‖ + ∑ i, ‖G x i j‖) volume :=
      hVU.add (locallyIntegrable_finsetSum _ fun i _ ↦ hG1 i j)
    refine hdom.mono (hbm j).norm (Eventually.of_forall fun x ↦ ?_)
    rw [norm_norm, Real.norm_of_nonneg (by positivity)]
    have hVx : |V x j| ≤ ‖V x‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (V x) j
    calc ‖eigenFirst U v x j‖ ≤ ‖-(V x j) • U x‖ +
          ‖(WithLp.toLp 2 (fun i ↦ G x i j) : ℝ^3)‖ := norm_add_le _ _
      _ ≤ ‖V x‖ * ‖U x‖ + ∑ i, ‖G x i j‖ := by
          rw [norm_smul, norm_neg, Real.norm_eq_abs]
          gcongr
          refine (EuclideanSpace.norm_le_sum_abs _).trans (le_of_eq ?_)
          simp only [Real.norm_eq_abs]
  · simpa using (locallyIntegrable_const (0 : ℝ))

/-! ### The gradient of an odd field -/

/-- The chosen weak gradient of a whole-space `H¹` velocity transforms as the gradient of an
odd axisymmetric field when its representative is odd axisymmetric. -/
theorem _root_.NavierStokes.Nonuniqueness.IsOddAxisymmetric.isOddGradient {v : H}
    (hV : IsOddAxisymmetric (Stationary.representative v)) : IsOddGradient v := by
  intro θ s
  set g := groupElement θ s
  set χ := parity s
  set V := Stationary.representative v
  set G := Stationary.gradientRepresentative v
  let e : Fin 3 → ℝ^3 := fun k ↦ EuclideanSpace.single k 1
  have hG2 (i j : Fin 3) : MemLp (fun x ↦ G x i j) 2 volume :=
    Stationary.memLp_gradientRepresentative v i j
  have hV2 (i : Fin 3) : MemLp (fun x ↦ V x i) 2 volume :=
    memLp_piLp_iff.mp (Stationary.memLp_representative v) i
  have hVg := hV.ae_comp_groupElement θ s
  have hflip (u w : ℝ^3) : ⟪u, g w⟫ = ⟪g.symm u, w⟫ := by
    rw [g.symm.inner_map_eq_flip, LinearIsometryEquiv.symm_symm]
  have hkl (k l : Fin 3) : ∀ᵐ y ∂volume,
      G (g y) k l = χ * gradientForm v y (g.symm (e k)) (g.symm (e l)) := by
    set c := g.symm (e k)
    set d := g.symm (e l)
    have hloc1 : LocallyIntegrable (fun y ↦ G (g y) k l) volume :=
      ((hG2 k l).comp_measurePreserving g.measurePreserving).locallyIntegrable (by norm_num)
    have hloc2 : LocallyIntegrable (fun y ↦ χ * gradientForm v y c d) volume := by
      have h : LocallyIntegrable (fun y ↦ ∑ i, ∑ j, c i * G y i j * d j) volume :=
        locallyIntegrable_finsetSum _ fun i _ ↦ locallyIntegrable_finsetSum _ fun j _ ↦
          (((hG2 i j).locallyIntegrable (by norm_num)).continuous_mul
            continuous_const).mul_continuous continuous_const
      exact h.continuous_mul continuous_const
    refine ae_eq_of_integral_contDiff_smul_eq hloc1 hloc2 fun ψ hψ hψc ↦ ?_
    let φ : ℝ^3 → ℝ := fun x ↦ ψ (g.symm x)
    have hφ : ContDiff ℝ ∞ φ := hψ.comp g.symm.contDiff
    have hφc : HasCompactSupport φ := hψc.comp_homeomorph g.symm.toHomeomorph
    have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
    have hdψ (j : Fin 3) : MemLp (PDE.partialDeriv j ψ) 2 volume :=
      (hψ.partialDeriv j (k := 0) (hkr := by simp)).continuous.memLp_of_hasCompactSupport
        (hψc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j (1 : ℝ)))
    have hψ2 : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
    -- derivative of the pulled-back test at the image point
    have hdφ (y : ℝ^3) : PDE.partialDeriv l φ (g y) = ∑ j, d j * PDE.partialDeriv j ψ y := by
      have hcomp : HasFDerivAt φ ((fderiv ℝ ψ (g.symm (g y))).comp (groupInvCLM θ s)) (g y) :=
        (hψd _).hasFDerivAt.comp (g y) (groupInvCLM θ s).hasFDerivAt
      rw [PDE.partialDeriv, hcomp.fderiv, LinearIsometryEquiv.symm_apply_apply,
        ContinuousLinearMap.comp_apply, groupInvCLM_apply,
        PDE.fderiv_apply_eq_sum_smul_partialDeriv]
      simp only [smul_eq_mul, d, e, g]
    have hint (i j : Fin 3) :
        Integrable (fun y ↦ V y i * PDE.partialDeriv j ψ y) volume :=
      (hV2 i).integrable_mul (hdψ j)
    have hintG (i j : Fin 3) : Integrable (fun y ↦ G y i j * ψ y) volume :=
      (hG2 i j).integrable_mul hψ2
    calc ∫ y, ψ y • G (g y) k l
        = ∫ x, φ x * G x k l := by
          rw [← integral_comp_groupElement θ s (fun x ↦ φ x * G x k l)]
          refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
          change ψ y * G (g y) k l = ψ (g.symm (g y)) * G (g y) k l
          rw [LinearIsometryEquiv.symm_apply_apply]
      _ = -∫ x, V x k * PDE.partialDeriv l φ x := by
          rw [Stationary.integral_representative_mul_partialDeriv v k l hφ hφc, neg_neg]
          exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
      _ = -∫ y, V (g y) k * PDE.partialDeriv l φ (g y) := by
          rw [integral_comp_groupElement θ s (fun x ↦ V x k * PDE.partialDeriv l φ x)]
      _ = -∫ y, χ * ∑ i, ∑ j, c i * d j * (V y i * PDE.partialDeriv j ψ y) := by
          congr 1
          refine integral_congr_ae ?_
          filter_upwards [hVg] with y hy
          rw [hdφ, hy]
          have hVk : (χ • g (V y)) k = χ * ∑ i, c i * V y i := by
            rw [PiLp.smul_apply, smul_eq_mul]
            congr 1
            rw [← EuclideanSpace.real_inner_eq_sum, ← hflip]
            simp [e, EuclideanSpace.inner_single_left]
          rw [hVk, mul_assoc, Finset.sum_mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
          ring
      _ = -(χ * ∑ i, ∑ j, c i * d j * ∫ y, V y i * PDE.partialDeriv j ψ y) := by
          rw [integral_const_mul, integral_finsetSum _ fun i _ ↦
            integrable_finsetSum _ fun j _ ↦ (hint i j).const_mul _]
          simp only [integral_finsetSum _ fun j _ ↦ (hint _ j).const_mul _, integral_const_mul]
      _ = χ * ∑ i, ∑ j, c i * d j * ∫ y, G y i j * ψ y := by
          have hW (i j : Fin 3) : ∫ y, V y i * PDE.partialDeriv j ψ y =
              -∫ y, G y i j * ψ y :=
            Stationary.integral_representative_mul_partialDeriv v i j hψ hψc
          simp only [hW, mul_neg, Finset.sum_neg_distrib, neg_neg]
      _ = ∫ y, ψ y • (χ * gradientForm v y c d) := by
          have hpt : (fun y ↦ ψ y • (χ * gradientForm v y c d)) =
              fun y ↦ ∑ i, ∑ j, (χ * c i * d j) * (G y i j * ψ y) := by
            funext y
            simp only [gradientForm_apply, smul_eq_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
            ring
          rw [hpt, integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
            (hintG i j).const_mul _]
          simp only [integral_finsetSum _ fun j _ ↦ (hintG _ j).const_mul _, integral_const_mul,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
          ring
  filter_upwards [ae_all_iff.mpr fun k ↦ ae_all_iff.mpr fun l ↦ hkl k l] with y hy u w
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hB : gradientForm v (g y) = χ • (gradientForm v y).compl₁₂
      g.symm.toLinearEquiv.toLinearMap g.symm.toLinearEquiv.toLinearMap := by
    refine b.ext fun k ↦ b.ext fun l ↦ ?_
    rw [show b k = e k by simp [b, e], show b l = e l by simp [b, e]]
    have hy' := hy k l
    simp only [LinearMap.smul_apply, LinearMap.compl₁₂_apply, smul_eq_mul,
      LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
    rw [← hy']
    simp [gradientForm_apply, e]
    rfl
  rw [hB]
  simp only [LinearMap.smul_apply, LinearMap.compl₁₂_apply, smul_eq_mul, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv]

/-! ### The weak eigenvalue equation -/

/-- The weak eigenvalue equation of an even axisymmetric base field in `L²_loc` and an odd
axisymmetric `H¹` eigenfunction follows from the equation tested only with odd axisymmetric
smooth compactly supported solenoidal fields. -/
theorem _root_.NavierStokes.Nonuniqueness.WeakEigenEquation.of_symmetric_tests
    {U : ℝ^3 → ℝ^3} {μ : ℝ} {v : H} (hU : IsEvenAxisymmetric U)
    (hUm : AEStronglyMeasurable U volume) (hU2 : LocallyIntegrable (fun x ↦ ‖U x‖ ^ 2) volume)
    (hV : IsOddAxisymmetric (Stationary.representative v))
    (htest : ∀ φ, IsSolenoidalTestField φ → IsOddAxisymmetric φ →
      ∫ x, weakEigenDensity U μ v φ x = 0) :
    WeakEigenEquation U μ v := by
  have hdens (ψ : ℝ^3 → ℝ^3) (hψ : IsSolenoidalTestField ψ) :
      weakEigenDensity U μ v ψ = jetDensity (eigenZeroth U μ v) (eigenFirst U v) 0 ψ :=
    funext fun x ↦ weakEigenDensity_eq_jetDensity U μ v ((hψ.1.differentiable (by simp)) x)
  intro φ hφ
  rw [hdens φ hφ]
  refine weak_eq_of_symmetric_tests true (isLocallyIntegrableJet_eigen μ v hUm hU2)
    (isEquivariantJet_eigen hU hV hV.isOddGradient) (fun ψ hψ hsec ↦ ?_) φ hφ
  rw [← hdens ψ hψ]
  exact htest ψ hψ (isInSector_true_iff.mp hsec)

end NavierStokes.Symmetry
