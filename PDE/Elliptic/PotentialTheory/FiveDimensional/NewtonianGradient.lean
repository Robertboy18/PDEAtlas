/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import CAS.ExactTactic

public import PDE.Elliptic.PotentialTheory.FiveDimensional.NewtonianPotential
import PDE.Elliptic.PotentialTheory.FundamentalSolution.LocalIntegrability

/-!
# First-gradient representation of the Newtonian potential

The first derivative of the five-dimensional Newtonian kernel has size
`|X|⁻⁴`, which is locally integrable in dimension five. Smooth regularization
therefore moves one derivative from a compactly supported C¹ function onto the kernel
without a principal value or a local source correction.

The resulting convolution formula acts on the undifferentiated C¹ source and
allows the source to be nonzero at the evaluation point. The full Fréchet
derivative kernel and its nearby-point comparisons provide fixed majorants
for differentiating noncompact tails.
-/

@[expose] public section

open PDE (partialDeriv)

noncomputable section

open MeasureTheory Filter TopologicalSpace
open PDE.Analysis SobolevSpace
open scoped Distributions ENNReal Topology

-- Use the same real calculus instances as `RegularizedKernel`.

namespace PotentialTheory

/-- The first Cartesian Newtonian kernel, with value zero assigned at the pole.
The value at that single point does not affect its integral operator. -/
def fiveDimensionalGammaGradientKernel (i : Fin 5) (X : ℝ^5) : ℝ :=
  -(3 / (8 * Real.pi ^ 2)) * X i * ‖X‖ ^ (-5 : ℝ)

/-- One coordinate factor reduces the singularity from `|X|⁻⁵` to `|X|⁻⁴`. -/
theorem norm_fiveDimensionalGammaGradientKernel_le (i : Fin 5) (X : ℝ^5) :
    ‖fiveDimensionalGammaGradientKernel i X‖ ≤
      (3 / (8 * Real.pi ^ 2)) * ‖X‖ ^ (-4 : ℝ) := by
  by_cases hX : X = 0
  · subst X
    simp [fiveDimensionalGammaGradientKernel]
  have hr : 0 < ‖X‖ := norm_pos_iff.mpr hX
  have hcoord : |X i| ≤ ‖X‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le X i
  have hmul : ‖X‖ * ‖X‖ ^ (-5 : ℝ) = ‖X‖ ^ (-4 : ℝ) := by
    calc
      _ = ‖X‖ ^ (1 : ℝ) * ‖X‖ ^ (-5 : ℝ) := by rw [Real.rpow_one]
      _ = ‖X‖ ^ ((1 : ℝ) + -5) := (Real.rpow_add hr _ _).symm
      _ = _ := by norm_num
  rw [fiveDimensionalGammaGradientKernel, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_neg, abs_of_nonneg (by positivity : 0 ≤ 3 / (8 * Real.pi ^ 2)),
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg X) _)]
  calc
    _ ≤ (3 / (8 * Real.pi ^ 2)) * ‖X‖ * ‖X‖ ^ (-5 : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoord (by positivity))
        (Real.rpow_nonneg (norm_nonneg X) _)
    _ = _ := by rw [mul_assoc, hmul]

/-- The gradient kernel is locally integrable across its pole. In particular,
the first-gradient representation does not require the source to vanish there. -/
theorem locallyIntegrable_fiveDimensionalGammaGradientKernel (i : Fin 5) :
    LocallyIntegrable (fiveDimensionalGammaGradientKernel i) volume := by
  have hmeas : AEStronglyMeasurable (fiveDimensionalGammaGradientKernel i) volume := by
    unfold fiveDimensionalGammaGradientKernel
    fun_prop
  exact locallyIntegrable_of_norm_le_rpow
    (by norm_num : 1 ≤ Module.finrank ℝ (ℝ^5))
    (by norm_num : (4 : ℝ) < Module.finrank ℝ (ℝ^5))
    (Eventually.of_forall (norm_fiveDimensionalGammaGradientKernel_le i)) hmeas

/-- Regularization only decreases the absolute first-gradient kernel away
from the pole. This gives one majorant for the entire approximation. -/
theorem abs_fiveDimensionalGammaRegularized_partialDeriv_le
    (ε : ℝ) (hε : ε ≠ 0) (i : Fin 5) (X : ℝ^5) (hX : X ≠ 0) :
    |(∂[i] (fiveDimensionalGammaRegularized ε)) X| ≤
      |fiveDimensionalGammaGradientKernel i X| := by
  have hbase : 0 < ‖X‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hX)
  have hpow :
      (‖X‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) ≤
        (‖X‖ ^ 2) ^ (-(5 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hbase
      (le_add_of_nonneg_right (sq_nonneg _)) (by norm_num)
  have heq : (‖X‖ ^ 2) ^ (-(5 / 2 : ℝ)) = ‖X‖ ^ (-5 : ℝ) := by
    rw [← Real.rpow_natCast_mul (norm_nonneg X)]
    norm_num
  rw [heq] at hpow
  rw [fiveDimensionalGammaRegularized_partialDeriv ε hε,
    fiveDimensionalGammaGradientKernel]
  simp only [abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ ‖X‖ ^ 2 + ε ^ 2) _),
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg X) _)]
  exact mul_le_mul_of_nonneg_left hpow (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- Pairing the regularized kernel with a continuous compact factor converges
to the Newtonian pairing. The singular kernel supplies the majorant. -/
private theorem regularized_pairing_tendsto
    (g : ℝ^5 → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (fun n : ℕ ↦ ∫ X : ℝ^5,
      fiveDimensionalGammaRegularized ((n + 1 : ℝ)⁻¹) X * g X) atTop
      (𝓝 (∫ X : ℝ^5, fundamentalSolution 5 X * g X)) := by
  have hint : Integrable (fun X : ℝ^5 ↦ fundamentalSolution 5 X * g X) := by
    simpa only [smul_eq_mul] using
      (locallyIntegrable_fundamentalSolution 5).integrable_smul_right_of_hasCompactSupport hg hgc
  apply tendsto_integral_of_dominated_convergence
    (fun X : ℝ^5 ↦ ‖fundamentalSolution 5 X * g X‖)
  · intro n
    exact (((fiveDimensionalGammaRegularized_contDiff _ (by positivity)).continuous).mul
      hg).aestronglyMeasurable
  · exact hint.norm
  · intro n
    filter_upwards [(Set.countable_singleton (0 : ℝ^5)).ae_notMem volume] with X hX
    have hX0 : X ≠ 0 := by simpa using hX
    have hpow :
        (‖X‖ ^ 2 + ((n + 1 : ℝ)⁻¹) ^ 2) ^ (-(3 / 2 : ℝ)) ≤
          (‖X‖ ^ 2) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (norm_pos_iff.mpr hX0))
        (le_add_of_nonneg_right (sq_nonneg _)) (by norm_num)
    have heq : (‖X‖ ^ 2) ^ (-(3 / 2 : ℝ)) = ‖X‖ ^ (-3 : ℝ) := by
      rw [← Real.rpow_natCast_mul (norm_nonneg X)]
      norm_num
    rw [heq] at hpow
    have hkernel : fiveDimensionalGammaRegularized ((n + 1 : ℝ)⁻¹) X ≤
        fundamentalSolution 5 X := by
      rw [fiveDimensionalGammaRegularized, fundamentalSolution_five]
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    have hreg : 0 ≤ fiveDimensionalGammaRegularized ((n + 1 : ℝ)⁻¹) X := by
      unfold fiveDimensionalGammaRegularized
      positivity
    have hgamma : 0 ≤ fundamentalSolution 5 X := by
      rw [fundamentalSolution_five]
      positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg hreg, abs_of_nonneg hgamma]
    exact mul_le_mul_of_nonneg_right hkernel (abs_nonneg _)
  · filter_upwards [(Set.countable_singleton (0 : ℝ^5)).ae_notMem volume] with X hX
    have hX0 : X ≠ 0 := by simpa using hX
    simpa only [Function.comp_def, one_div] using
      ((fiveDimensionalGammaRegularized_tendsto X hX0).comp
        tendsto_one_div_add_atTop_nhds_zero_nat).mul_const (g X)

/-- The regularized gradient pairings converge by the same fixed integrable
majorant. Unlike a Hessian pairing, this needs no subtraction at the pole. -/
theorem fiveDimensionalGammaRegularized_gradient_pairing_tendsto
    (i : Fin 5) (g : ℝ^5 → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (fun n : ℕ ↦ ∫ X : ℝ^5,
      (∂[i] (fiveDimensionalGammaRegularized ((n + 1 : ℝ)⁻¹))) X * g X) atTop
      (𝓝 (∫ X : ℝ^5, fiveDimensionalGammaGradientKernel i X * g X)) := by
  have hint : Integrable (fun X : ℝ^5 ↦ fiveDimensionalGammaGradientKernel i X * g X) := by
    have hlocal := locallyIntegrable_fiveDimensionalGammaGradientKernel i
    simpa only [smul_eq_mul] using
      hlocal.integrable_smul_right_of_hasCompactSupport hg hgc
  apply tendsto_integral_of_dominated_convergence
    (fun X : ℝ^5 ↦ ‖fiveDimensionalGammaGradientKernel i X * g X‖)
  · intro n
    exact ((PDE.contDiff_top_partialDeriv (i := i)
      (fiveDimensionalGammaRegularized_contDiff _ (by positivity))).continuous.mul
        hg).aestronglyMeasurable
  · exact hint.norm
  · intro n
    filter_upwards [(Set.countable_singleton (0 : ℝ^5)).ae_notMem volume] with X hX
    have hX0 : X ≠ 0 := by simpa using hX
    simpa only [Real.norm_eq_abs, abs_mul] using
      mul_le_mul_of_nonneg_right
        (abs_fiveDimensionalGammaRegularized_partialDeriv_le
          ((n + 1 : ℝ)⁻¹) (by positivity) i X hX0) (abs_nonneg (g X))
  · filter_upwards [(Set.countable_singleton (0 : ℝ^5)).ae_notMem volume] with X hX
    have hX0 : X ≠ 0 := by simpa using hX
    have hε : Tendsto (fun n : ℕ ↦ ((n + 1 : ℝ)⁻¹)) atTop (𝓝 0) := by
      simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hbase : Tendsto (fun n : ℕ ↦ ‖X‖ ^ 2 + ((n + 1 : ℝ)⁻¹) ^ 2) atTop
        (𝓝 (‖X‖ ^ 2)) := by
      simpa only [zero_pow (by norm_num : 2 ≠ 0), add_zero] using
        (tendsto_const_nhds.add (hε.pow 2))
    have hpow := hbase.rpow_const (p := (-(5 / 2 : ℝ)))
      (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hX0)))
    have heq : (‖X‖ ^ 2) ^ (-(5 / 2 : ℝ)) = ‖X‖ ^ (-5 : ℝ) := by
      rw [← Real.rpow_natCast_mul (norm_nonneg X)]
      norm_num
    rw [heq] at hpow
    have hpoint (n : ℕ) :
        (∂[i] (fiveDimensionalGammaRegularized ((n + 1 : ℝ)⁻¹))) X =
          -(3 / (8 * Real.pi ^ 2)) * X i *
            (‖X‖ ^ 2 + ((n + 1 : ℝ)⁻¹) ^ 2) ^ (-(5 / 2 : ℝ)) :=
      fiveDimensionalGammaRegularized_partialDeriv _ (by positivity) i X
    simpa only [hpoint, fiveDimensionalGammaGradientKernel] using
      (hpow.const_mul (-(3 / (8 * Real.pi ^ 2)) * X i)).mul_const (g X)

/-- The first Newtonian derivative is represented by its locally integrable
classical kernel when paired against a compactly supported C¹ function.
No local mass occurs when one derivative is moved across. -/
theorem fundamentalSolution_five_integral_mul_partialDeriv
    (i : Fin 5) (g : ℝ^5 → ℝ) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    (∫ X : ℝ^5, fundamentalSolution 5 X * (∂[i] g) X) =
      -(∫ X : ℝ^5, fiveDimensionalGammaGradientKernel i X * g X) := by
  have hdg : Continuous (∂[i] g) := by
    change Continuous (fun X : ℝ^5 ↦ fderiv ℝ g X (EuclideanSpace.single i (1 : ℝ)))
    exact (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdc : HasCompactSupport (∂[i] g) := by
    change HasCompactSupport (fun X : ℝ^5 ↦
      fderiv ℝ g X (EuclideanSpace.single i (1 : ℝ)))
    exact hgc.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))
  have hleft := regularized_pairing_tendsto (∂[i] g) hdg hdc
  have hright := fiveDimensionalGammaRegularized_gradient_pairing_tendsto i g hg.continuous hgc
  have hparts (n : ℕ) :
      (∫ X : ℝ^5, fiveDimensionalGammaRegularized ((n + 1 : ℝ)⁻¹) X *
        (∂[i] g) X) =
      -(∫ X : ℝ^5, (∂[i]
        (fiveDimensionalGammaRegularized ((n + 1 : ℝ)⁻¹))) X * g X) := by
    let u : ℝ^5 → ℝ := fiveDimensionalGammaRegularized ((n + 1 : ℝ)⁻¹)
    have hu : ContDiff ℝ 1 u :=
      (fiveDimensionalGammaRegularized_contDiff _ (by positivity)).of_le (by simp)
    have hdu : Continuous (∂[i] u) := by
      change Continuous (fun X : ℝ^5 ↦ fderiv ℝ u X (EuclideanSpace.single i (1 : ℝ)))
      exact (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hdug : Integrable (fun X : ℝ^5 ↦ (∂[i] u) X * g X) :=
      (hdu.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
    have hudg : Integrable (fun X : ℝ^5 ↦ u X * (∂[i] g) X) :=
      (hu.continuous.mul hdg).integrable_of_hasCompactSupport hdc.mul_left
    have hug : Integrable (fun X : ℝ^5 ↦ u X * g X) :=
      (hu.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
    simpa only [u, partialDeriv] using
      (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (μ := (volume : Measure (ℝ^5))) (f := u) (g := g)
        (v := EuclideanSpace.single i (1 : ℝ)) hdug hudg hug
        (fun _ _ ↦ (hu.differentiable (by norm_num)).differentiableAt)
        (fun _ _ ↦ (hg.differentiable (by norm_num)).differentiableAt))
  apply tendsto_nhds_unique hleft
  simpa only [hparts] using hright.neg

/-- A first derivative of the Newtonian potential is the absolutely
convergent integral of the gradient kernel against the original compact C¹
source. The source may be nonzero at the evaluation point. -/
theorem fundamentalSolution_five_convolution_partialDeriv_eq_integral
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (i : Fin 5) (X : ℝ^5) :
    Integrable (fun Y : ℝ^5 ↦ fiveDimensionalGammaGradientKernel i (X - Y) * f Y) ∧
      (∂[i]
        (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume)) X =
        ∫ Y : ℝ^5, fiveDimensionalGammaGradientKernel i (X - Y) * f Y := by
  let ψ : ℝ^5 → ℝ := fun Y ↦ f (X - Y)
  have hψ : ContDiff ℝ 1 ψ := hf.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := hfc.comp_homeomorph (Homeomorph.subLeft X)
  have hint : Integrable (fun Y : ℝ^5 ↦
      fiveDimensionalGammaGradientKernel i Y * ψ Y) := by
    have hlocal := locallyIntegrable_fiveDimensionalGammaGradientKernel i
    simpa only [smul_eq_mul] using
      hlocal.integrable_smul_right_of_hasCompactSupport hψ.continuous hψc
  have hshift (Y : ℝ^5) : ψ (X - Y) = f Y := by
    change f (X - (X - Y)) = f Y
    rw [sub_sub_cancel]
  have hchange :
      (∫ Y : ℝ^5, fiveDimensionalGammaGradientKernel i (X - Y) * f Y) =
        ∫ Y : ℝ^5, fiveDimensionalGammaGradientKernel i Y * ψ Y := by
    simpa only [hshift] using
      (integral_sub_left_eq_self
        (fun Y : ℝ^5 ↦ fiveDimensionalGammaGradientKernel i Y * ψ Y)
        (volume : Measure (ℝ^5)) X)
  have hchain (Y : ℝ^5) :
      (∂[i] ψ) Y = -(∂[i] f) (X - Y) := by
    have hfAt : HasFDerivAt f (fderiv ℝ f (X - Y)) (X - Y) :=
      (hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    have hcomp : HasFDerivAt ψ
        ((fderiv ℝ f (X - Y)).comp (-ContinuousLinearMap.id ℝ (ℝ^5))) Y :=
      hfAt.comp Y ((hasFDerivAt_id Y).const_sub X)
    unfold partialDeriv
    rw [hcomp.fderiv]
    simp
  have hpair := fundamentalSolution_five_integral_mul_partialDeriv i ψ hψ hψc
  have hneg :
      (∫ Y : ℝ^5, fundamentalSolution 5 Y * (∂[i] ψ) Y) =
        -convolution (fundamentalSolution 5) (∂[i] f)
          (ContinuousLinearMap.mul ℝ ℝ) volume X := by
    simp_rw [hchain, mul_neg]
    rw [integral_neg]
    rfl
  rw [hneg] at hpair
  refine ⟨?_, ?_⟩
  · simpa only [hshift] using hint.comp_sub_left X
  · rw [convolution_partialDeriv_right _ _ (locallyIntegrable_fundamentalSolution 5)
      hfc hf i X]
    exact (neg_injective hpair).trans hchange.symm


/-- The Newtonian gradient as a continuous linear functional. Its value at
the pole is zero, matching the coordinate kernels. -/
def fiveDimensionalGammaFDerivKernel (X : ℝ^5) : ℝ^5 →L[ℝ] ℝ :=
  (-(3 / (8 * Real.pi ^ 2)) * ‖X‖ ^ (-5 : ℝ)) • innerSL ℝ X

/-- Applying the linear-map kernel to a coordinate vector recovers the
Cartesian gradient kernel. -/
theorem fiveDimensionalGammaFDerivKernel_apply_single (i : Fin 5) (X : ℝ^5) :
    fiveDimensionalGammaFDerivKernel X (EuclideanSpace.single i (1 : ℝ)) =
      fiveDimensionalGammaGradientKernel i X := by
  simp [fiveDimensionalGammaFDerivKernel, fiveDimensionalGammaGradientKernel,
    EuclideanSpace.inner_single_right, mul_assoc, mul_left_comm, mul_comm]

/-- Away from the pole, the linear-map kernel is the Fréchet derivative
of the Newtonian fundamental solution. The coordinate formula already proved
for that solution determines this map on every vector. -/
theorem hasFDerivAt_fiveDimensionalGamma (X : ℝ^5) (hX : X ≠ 0) :
    HasFDerivAt (fundamentalSolution 5) (fiveDimensionalGammaFDerivKernel X) X := by
  have hdiff : DifferentiableAt ℝ (fundamentalSolution 5) X :=
    (contDiffAt_fundamentalSolution 5 X hX).differentiableAt (by simp)
  have hfd : fderiv ℝ (fundamentalSolution 5) X =
      fiveDimensionalGammaFDerivKernel X := by
    apply ContinuousLinearMap.ext
    intro v
    rw [PDE.fderiv_apply_eq_sum_partialDeriv_mul]
    simp_rw [fundamentalSolution_five_partialDeriv _ X hX]
    simp only [fiveDimensionalGammaFDerivKernel, smul_apply,
      innerSL_apply_apply, smul_eq_mul, PiLp.inner_apply, Real.inner_apply,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [← hfd]
  exact hdiff.hasFDerivAt

/-- The norm of the full derivative has the same inverse-fourth-power decay
as the coordinate bounds. This includes the assigned value at the pole. -/
theorem norm_fiveDimensionalGammaFDerivKernel (X : ℝ^5) :
    ‖fiveDimensionalGammaFDerivKernel X‖ =
      (3 / (8 * Real.pi ^ 2)) * ‖X‖ ^ (-4 : ℝ) := by
  by_cases hX : X = 0
  · subst X
    simp [fiveDimensionalGammaFDerivKernel]
  have hr : 0 < ‖X‖ := norm_pos_iff.mpr hX
  have hmul : ‖X‖ * ‖X‖ ^ (-5 : ℝ) = ‖X‖ ^ (-4 : ℝ) := by
    calc
      _ = ‖X‖ ^ (1 : ℝ) * ‖X‖ ^ (-5 : ℝ) := by rw [Real.rpow_one]
      _ = ‖X‖ ^ ((1 : ℝ) + -5) := (Real.rpow_add hr _ _).symm
      _ = _ := by norm_num
  rw [fiveDimensionalGammaFDerivKernel, norm_smul, innerSL_apply_norm,
    Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ 3 / (8 * Real.pi ^ 2)),
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg X) _)]
  calc
    _ = (3 / (8 * Real.pi ^ 2)) * (‖X‖ * ‖X‖ ^ (-5 : ℝ)) := by ring
    _ = _ := by rw [hmul]

/-- The explicit derivative kernel is measurable even at its assigned pole
value, so it can be integrated as a continuous-linear-map-valued function. -/
theorem measurable_fiveDimensionalGammaFDerivKernel :
    Measurable fiveDimensionalGammaFDerivKernel := by
  have hcoeff : Measurable (fun X : ℝ^5 ↦
      -(3 / (8 * Real.pi ^ 2)) * ‖X‖ ^ (-5 : ℝ)) := by
    fun_prop
  exact hcoeff.smul (innerSL ℝ).continuous.measurable

private theorem half_norm_sub_le_of_near {X Z Y : ℝ^5} {r : ℝ}
    (hZ : ‖Z - X‖ ≤ r / 2) (hY : r ≤ ‖X - Y‖) :
    ‖X - Y‖ / 2 ≤ ‖Z - Y‖ := by
  have htriangle : ‖X - Y‖ ≤ ‖X - Z‖ + ‖Z - Y‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (X - Z) (Z - Y)
  rw [norm_sub_rev X Z] at htriangle
  linarith

/-- Moving the evaluation point by at most half the source separation increases
the absolute Newtonian kernel by at most a factor of eight. The positive separation
keeps both kernel arguments away from the pole. -/
theorem abs_fundamentalSolution_five_sub_le_of_near {X Z Y : ℝ^5} {r : ℝ}
    (hr : 0 < r) (hZ : ‖Z - X‖ ≤ r / 2) (hY : r ≤ ‖X - Y‖) :
    |fundamentalSolution 5 (Z - Y)| ≤ 8 * |fundamentalSolution 5 (X - Y)| := by
  have hd : 0 < ‖X - Y‖ := hr.trans_le hY
  have hhalf := half_norm_sub_le_of_near hZ hY
  have hpow : ‖Z - Y‖ ^ (-3 : ℝ) ≤ 8 * ‖X - Y‖ ^ (-3 : ℝ) := by
    calc
      _ ≤ (‖X - Y‖ / 2) ^ (-3 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (half_pos hd) hhalf (by norm_num)
      _ = _ := by
        rw [Real.div_rpow (norm_nonneg _) (by norm_num)]
        norm_num only [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) 3,
          Real.rpow_ofNat]
        cas
  have hgamma (V : ℝ^5) : 0 ≤ fundamentalSolution 5 V := by
    rw [fundamentalSolution_five]
    positivity
  rw [abs_of_nonneg (hgamma (Z - Y)), abs_of_nonneg (hgamma (X - Y))]
  calc
    _ = (1 / (8 * Real.pi ^ 2)) * ‖Z - Y‖ ^ (-3 : ℝ) :=
      fundamentalSolution_five _
    _ ≤ (1 / (8 * Real.pi ^ 2)) * (8 * ‖X - Y‖ ^ (-3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 8 * fundamentalSolution 5 (X - Y) := by
      rw [fundamentalSolution_five]
      cas

/-- On the same neighborhood, the full derivative kernel is bounded by the
potential kernel at the fixed center. For a source vanishing on `ball X r`,
multiplying by its absolute value gives an integrable majorant whenever the
potential pairing at that center is absolutely integrable. -/
theorem norm_fiveDimensionalGammaFDerivKernel_sub_le_of_near
    {X Z Y : ℝ^5} {r : ℝ}
    (hr : 0 < r) (hZ : ‖Z - X‖ ≤ r / 2) (hY : r ≤ ‖X - Y‖) :
    ‖fiveDimensionalGammaFDerivKernel (Z - Y)‖ ≤
      (48 / r) * |fundamentalSolution 5 (X - Y)| := by
  have hhalf := half_norm_sub_le_of_near hZ hY
  have hsep : r / 2 ≤ ‖Z - Y‖ := by linarith
  have hnormpos : 0 < ‖Z - Y‖ := by linarith
  have hratio : (3 : ℝ) / ‖Z - Y‖ ≤ 6 / r := by
    apply (div_le_div_iff₀ hnormpos hr).2
    linarith
  have hkernel : ‖fiveDimensionalGammaFDerivKernel (Z - Y)‖ =
      (3 / ‖Z - Y‖) * |fundamentalSolution 5 (Z - Y)| := by
    have hpow : ‖Z - Y‖ ^ (-4 : ℝ) =
        ‖Z - Y‖ ^ (-3 : ℝ) / ‖Z - Y‖ := by
      simpa only [show (-3 : ℝ) - 1 = -4 by norm_num, Real.rpow_one] using
        Real.rpow_sub hnormpos (-3) 1
    have hgamma : 0 ≤ fundamentalSolution 5 (Z - Y) := by
      rw [fundamentalSolution_five]
      positivity
    rw [norm_fiveDimensionalGammaFDerivKernel, abs_of_nonneg hgamma,
      fundamentalSolution_five, hpow]
    cas
  calc
    _ = (3 / ‖Z - Y‖) * |fundamentalSolution 5 (Z - Y)| := hkernel
    _ ≤ (6 / r) * |fundamentalSolution 5 (Z - Y)| :=
      mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
    _ ≤ (6 / r) * (8 * |fundamentalSolution 5 (X - Y)|) :=
      mul_le_mul_of_nonneg_left
        (abs_fundamentalSolution_five_sub_le_of_near hr hZ hY) (by positivity)
    _ = (48 / r) * |fundamentalSolution 5 (X - Y)| := by cas

end PotentialTheory
