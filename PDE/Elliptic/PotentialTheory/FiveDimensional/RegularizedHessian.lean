/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.SphericalMoments
public import PDE.DistributionTheory.TestFunction.ProperPrecomposition
import PDE.Elliptic.PotentialTheory.FundamentalSolution.NewtonianDistribution
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The distributional and classical Newtonian Hessian

Smooth regularizations converge to the distributional Hessian of the
five-dimensional Newtonian kernel. Away from the pole its Cartesian
derivatives have explicit radial formulas. Coordinate swaps and reflections
transport both test-function pairings and spherical truncations.
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

open MeasureTheory Filter LineDeriv TopologicalSpace SobolevSpace
open scoped Distributions ENNReal Topology
open PDE.Analysis

namespace PotentialTheory

/-- The real power `-(k / 2)` of the squared norm is the power `-k` of the norm. -/
private theorem norm_sq_rpow_neg_half (X : ℝ^5) (k : ℝ) :
    (‖X‖ ^ 2) ^ (-(k / 2)) = ‖X‖ ^ (-k) := by
  rw [← Real.rpow_natCast_mul (norm_nonneg X)]
  congr 1
  ring

/-- The distributional Hessian pairing against a test function is an absolutely
convergent Lebesgue integral; compact support of the test Hessian controls infinity.
-/
theorem fundamentalSolution_five_mul_testHessian_integrable
    (i j : Fin 5) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    Integrable (fun X : ℝ^5 ↦
      (fundamentalSolution 5) X *
        iteratedPartialDeriv (n := 5) [i, j] φ.toFun X) := by
  have hcont : Continuous (fun X : ℝ^5 ↦
      iteratedPartialDeriv (n := 5) [i, j] φ.toFun X) :=
    (PDE.contDiff_top_iteratedPartialDeriv φ.contDiff [i, j]).continuous
  have hcompact : HasCompactSupport (fun X : ℝ^5 ↦
      iteratedPartialDeriv (n := 5) [i, j] φ.toFun X) :=
    SobolevSpace.hasCompactSupport_iteratedPartialDeriv
      φ.hasCompactSupport [i, j]
  simpa [smul_eq_mul] using
    (locallyIntegrable_fundamentalSolution 5).integrable_smul_right_of_hasCompactSupport
      hcont hcompact

/-- Pairing the smooth Newtonian regularizations with a fixed test Hessian
converges to the pairing with the locally integrable singular kernel.
-/
theorem fiveDimensionalGammaRegularized_testHessian_tendsto
    (i j : Fin 5) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    Tendsto (fun n : ℕ ↦
      ∫ X : ℝ^5,
        fiveDimensionalGammaRegularized ((n + 1 : ℝ)⁻¹) X *
          iteratedPartialDeriv (n := 5) [i, j] φ.toFun X)
      atTop
      (nhds (∫ X : ℝ^5,
        (fundamentalSolution 5) X *
          iteratedPartialDeriv (n := 5) [i, j] φ.toFun X)) := by
  have hdφ := (PDE.contDiff_top_iteratedPartialDeriv φ.contDiff [i, j]).continuous
  refine tendsto_integral_of_dominated_convergence
    (fun X ↦ ‖fundamentalSolution 5 X * iteratedPartialDeriv (n := 5) [i, j] φ.toFun X‖)
    (fun n ↦ ((fiveDimensionalGammaRegularized_contDiff _ (by positivity)).continuous.mul
      hdφ).aestronglyMeasurable)
    (fundamentalSolution_five_mul_testHessian_integrable i j φ).norm (fun n ↦ ?_) ?_ <;>
    filter_upwards [(Set.countable_singleton (0 : ℝ^5)).ae_notMem volume] with X (hX : X ≠ 0)
  · rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_right (abs_le_abs_of_nonneg
      (by rw [fiveDimensionalGammaRegularized]; positivity) ?_) (norm_nonneg _)
    rw [fiveDimensionalGammaRegularized, fundamentalSolution_five, ← norm_sq_rpow_neg_half X 3]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (pow_pos (norm_pos_iff.2 hX) 2)
      (le_add_of_nonneg_right (sq_nonneg _)) (by norm_num)) (by positivity)
  · simpa [Function.comp_def, one_div] using
      ((fiveDimensionalGammaRegularized_tendsto X hX).comp
        tendsto_one_div_add_atTop_nhds_zero_nat).mul_const
          (iteratedPartialDeriv (n := 5) [i, j] φ.toFun X)

/-- Every smooth regularized Hessian component converges to the corresponding
distributional Hessian of the singular Newtonian kernel.
-/
theorem fiveDimensionalGammaRegularized_distributionalHessian_tendsto
    (i j : Fin 5) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    Tendsto (fun n : ℕ ↦
      ∫ X : ℝ^5,
        iteratedPartialDeriv (n := 5) [j, i]
          (fiveDimensionalGammaRegularized ((n + 1 : ℝ)⁻¹)) X * φ.toFun X)
      atTop
      (nhds (∫ X : ℝ^5,
        (fundamentalSolution 5) X *
          iteratedPartialDeriv (n := 5) [i, j] φ.toFun X)) := by
  apply (fiveDimensionalGammaRegularized_testHessian_tendsto i j φ).congr'
  filter_upwards [] with n
  exact fiveDimensionalGammaRegularized_integral_by_parts
    ((n + 1 : ℝ)⁻¹) (by positivity) i j φ

/-- The locally integrable Newtonian kernel satisfies `-ΔΓ = δ₀` as a
distribution.  This identifies both the sign and the normalization of the
five-dimensional fundamental solution.
-/
theorem fundamentalSolution_five_distributional_laplacian
    (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    (∑ i : Fin 5,
      ∫ X : ℝ^5,
        (fundamentalSolution 5) X *
          iteratedPartialDeriv (n := 5) [i, i] φ.toFun X) =
      -φ.toFun 0 := by
  let φ₂ : 𝓓^{2}((⊤ : Opens (ℝ^5)), ℝ) :=
    { toFun := φ.toFun
      contDiff' := φ.contDiff.of_le (WithTop.coe_le_coe.mpr le_top)
      hasCompactSupport' := φ.hasCompactSupport
      tsupport_subset' := φ.tsupport_subset }
  calc
    (∑ i : Fin 5, ∫ X : ℝ^5, fundamentalSolution 5 X *
        iteratedPartialDeriv (n := 5) [i, i] φ.toFun X) =
        ∫ X : ℝ^5, ∑ i : Fin 5, fundamentalSolution 5 X *
          iteratedPartialDeriv (n := 5) [i, i] φ.toFun X := by
      symm
      exact integral_finsetSum Finset.univ
        (fun i _ ↦ fundamentalSolution_five_mul_testHessian_integrable i i φ)
    _ = ∫ X : ℝ^5, fundamentalSolution 5 X * PDE.laplacian φ.toFun X := by
      apply integral_congr_ae
      filter_upwards [] with X
      simp only [PDE.laplacian, iteratedPartialDeriv, Finset.mul_sum]
    _ = -φ.toFun 0 :=
      Newtonian.integral_fundamentalSolution_mul_laplacian (by norm_num : 3 ≤ 5) φ₂

/-- Exact first Cartesian derivative of the five-dimensional Newtonian kernel away from its pole.
-/
theorem fundamentalSolution_five_partialDeriv
    (i : Fin 5) (X : ℝ^5) (hX : X ≠ 0) :
    (∂[i] (fundamentalSolution 5)) X =
      -(3 / (8 * Real.pi ^ 2)) * X i * ‖X‖ ^ (-5 : ℝ) := by
  let q : ℝ^5 → ℝ := fun Y ↦ ‖Y‖ ^ 2
  let c : ℝ := 1 / (8 * Real.pi ^ 2)
  have hq : HasFDerivAt q (2 • innerSL ℝ X) X := by
    simpa [q] using (hasFDerivAt_id (𝕜 := ℝ) X).norm_sq
  have hqX : q X ≠ 0 := by simp [q, hX]
  have hp := hq.rpow_const (p := (-(3 / 2 : ℝ))) (Or.inl hqX)
  have hc := hp.const_mul c
  have hfun : (fundamentalSolution 5) = fun Y ↦ c * q Y ^ (-(3 / 2 : ℝ)) :=
    funext fun Y ↦ by simp [fundamentalSolution_five, c, q, norm_sq_rpow_neg_half]
  rw [hfun]
  unfold partialDeriv
  rw [hc.fderiv]
  simp only [c, q, neg_mul, smul_apply, coe_innerSL_apply, nsmul_eq_mul,
    Nat.cast_ofNat, smul_eq_mul, mul_neg, Real.rpow_neg_ofNat, Int.reduceNeg,
    zpow_neg, zpow_ofNat, neg_inj]
  have hnorm : 0 < ‖X‖ := norm_pos_iff.mpr hX
  rw [show -(3 / 2 : ℝ) - 1 = -(5 / 2) by norm_num, norm_sq_rpow_neg_half,
    EuclideanSpace.inner_single_right, conj_trivial, Real.rpow_neg (norm_nonneg X), Real.rpow_ofNat]
  field_simp [Real.pi_ne_zero, hnorm.ne']


/-- Exact classical Hessian kernel away from the pole. Its diagonal trace vanishes
pointwise, while the distributional local mass is handled separately.
-/
theorem fundamentalSolution_five_iteratedPartialDeriv_two
    (i j : Fin 5) (X : ℝ^5)
    (hX : X ≠ 0) :
    iteratedPartialDeriv (n := 5) [j, i] (fundamentalSolution 5) X =
      (15 / (8 * Real.pi ^ 2)) * X i * X j * ‖X‖ ^ (-7 : ℝ) -
        (3 / (8 * Real.pi ^ 2)) * (if i = j then 1 else 0) *
          ‖X‖ ^ (-5 : ℝ) := by
  let q : ℝ^5 → ℝ := fun Y ↦ ‖Y‖ ^ 2
  let K : ℝ := 3 / (8 * Real.pi ^ 2)
  let L : ℝ^5 →L[ℝ] ℝ :=
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 ↦ ℝ) i
  let B : ℝ^5 → ℝ := fun Y ↦
    -K * Y i * q Y ^ (-(5 / 2 : ℝ))
  have hq : HasFDerivAt q (2 • innerSL ℝ X) X := by
    simpa [q] using (hasFDerivAt_id (𝕜 := ℝ) X).norm_sq
  have hqX : q X ≠ 0 := by simp [q, hX]
  have hpow := hq.rpow_const (p := (-(5 / 2 : ℝ))) (Or.inl hqX)
  have hcoord : HasFDerivAt (fun Y : ℝ^5 ↦ Y i) L X := by
    simpa [L] using L.hasFDerivAt
  let P : ℝ^5 →L[ℝ] ℝ :=
    ((-(5 / 2 : ℝ)) * q X ^ (-(5 / 2 : ℝ) - 1)) • (2 • innerSL ℝ X)
  have hpow' : HasFDerivAt (fun Y ↦ q Y ^ (-(5 / 2 : ℝ))) P X := by
    simpa only [P] using hpow
  let B' : ℝ^5 →L[ℝ] ℝ :=
    (-K) • ((X i) • P + q X ^ (-(5 / 2 : ℝ)) • L)
  have hB : HasFDerivAt B B' X := by
    simpa [B, B', mul_assoc, add_comm] using (hcoord.mul hpow').const_mul (-K)
  have hlocal :
      (fun Y ↦ (∂[i] (fundamentalSolution 5)) Y) =ᶠ[nhds X] B := by
    filter_upwards [compl_singleton_mem_nhds_iff.mpr hX] with Y hY
    have hY0 : Y ≠ 0 := by simpa using hY
    rw [fundamentalSolution_five_partialDeriv i Y hY0]
    simp [B, K, q, norm_sq_rpow_neg_half]
  simp only [iteratedPartialDeriv]
  change fderiv ℝ (fun Y ↦ (∂[i] (fundamentalSolution 5)) Y) X
      (EuclideanSpace.single j (1 : ℝ)) = _
  rw [hlocal.fderiv_eq]
  rw [hB.fderiv]
  have hnorm : 0 < ‖X‖ := norm_pos_iff.mpr hX
  have hpow7 : (‖X‖ ^ 2) ^ (-(5 / 2 : ℝ) - 1) = ‖X‖ ^ (-7 : ℝ) := by
    rw [show -(5 / 2 : ℝ) - 1 = -(7 / 2) by norm_num, norm_sq_rpow_neg_half]
  have hpow5 := norm_sq_rpow_neg_half X 5
  by_cases hij : i = j
  · subst j
    simp [B', P, L, q, K, EuclideanSpace.inner_single_right,
      hpow7, hpow5]
    field_simp [Real.pi_ne_zero, hnorm.ne']
    ring
  · simp [B', P, L, q, K, hij, EuclideanSpace.inner_single_right,
      hpow7, hpow5]
    field_simp [Real.pi_ne_zero, hnorm.ne']
    ring

/-- At every nonzero point, the Hessian of the regularization converges to the
classical Hessian kernel along positive regularization parameters.
-/
theorem fiveDimensionalGammaRegularized_hessian_tendsto
    (i j : Fin 5) (X : ℝ^5) (hX : X ≠ 0) :
    Tendsto (fun ε : ℝ ↦ iteratedPartialDeriv (n := 5) [j, i]
        (fiveDimensionalGammaRegularized ε) X)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (iteratedPartialDeriv (n := 5) [j, i]
        (fundamentalSolution 5) X)) := by
  rw [fundamentalSolution_five_iteratedPartialDeriv_two i j X hX, ← norm_sq_rpow_neg_half X 7,
    ← norm_sq_rpow_neg_half X 5, show ‖X‖ ^ 2 = ‖X‖ ^ 2 + (0 : ℝ) ^ 2 by simp]
  have hq : ‖X‖ ^ 2 + (0 : ℝ) ^ 2 ≠ 0 := by simpa using hX
  have hF : ContinuousAt (fun ε : ℝ ↦ 15 / (8 * Real.pi ^ 2) * X i * X j *
      (‖X‖ ^ 2 + ε ^ 2) ^ (-(7 / 2 : ℝ)) - 3 / (8 * Real.pi ^ 2) * (if i = j then 1 else 0) *
        (‖X‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ))) 0 := by
    fun_prop (disch := exact Or.inl hq)
  refine (hF.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (fiveDimensionalGammaRegularized_iteratedPartialDeriv_two ε hε.ne' i j X).symm

/-- Away from the pole, every component of the regularized Hessian is bounded
uniformly in the regularization parameter by the critical homogeneous kernel.
The non-sharp constant keeps the estimate independent of the component.
-/
theorem fiveDimensionalGammaRegularized_hessian_bound
    (ε : ℝ) (hε : ε ≠ 0) (i j : Fin 5)
    (X : ℝ^5) (hX : X ≠ 0) :
    |iteratedPartialDeriv (n := 5) [j, i]
        (fiveDimensionalGammaRegularized ε) X| ≤
      (18 / (8 * Real.pi ^ 2)) * ‖X‖ ^ (-5 : ℝ) := by
  rw [fiveDimensionalGammaRegularized_iteratedPartialDeriv_two ε hε i j X]
  have hr : 0 < ‖X‖ := norm_pos_iff.mpr hX
  have hq : ‖X‖ ^ 2 ≤ ‖X‖ ^ 2 + ε ^ 2 := le_add_of_nonneg_right (sq_nonneg ε)
  have h7 := Real.rpow_le_rpow_of_nonpos (by positivity) hq (by norm_num : (-(7 / 2 : ℝ)) ≤ 0)
  have h5 := Real.rpow_le_rpow_of_nonpos (by positivity) hq (by norm_num : (-(5 / 2 : ℝ)) ≤ 0)
  rw [norm_sq_rpow_neg_half] at h7 h5
  have hcoords : |X i * X j| ≤ ‖X‖ ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (PiLp.norm_apply_le X i) (PiLp.norm_apply_le X j) (abs_nonneg _)
      (norm_nonneg _)
  have h1 : |X i * X j * (‖X‖ ^ 2 + ε ^ 2) ^ (-(7 / 2 : ℝ))| ≤ ‖X‖ ^ (-5 : ℝ) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (‖X‖ ^ 2 + ε ^ 2) ^ (-(7 / 2 : ℝ))),
      show (-5 : ℝ) = 2 + -7 by norm_num,
      Real.rpow_add hr, Real.rpow_two]
    exact mul_le_mul hcoords h7 (by positivity) (by positivity)
  have h2 : |(if i = j then (1 : ℝ) else 0) * (‖X‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ))| ≤
      ‖X‖ ^ (-5 : ℝ) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (‖X‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)))]
    exact (mul_le_of_le_one_left (by positivity) (by split <;> simp)).trans h5
  rw [abs_le] at h1 h2
  calc _ = 1 / (8 * Real.pi ^ 2) * |15 * (X i * X j * (‖X‖ ^ 2 + ε ^ 2) ^ (-(7 / 2 : ℝ))) -
        3 * ((if i = j then 1 else 0) * (‖X‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)))| := by
        rw [← abs_of_pos (by positivity : (0 : ℝ) < 1 / (8 * Real.pi ^ 2)), ← abs_mul]
        congr 1
        ring
    _ ≤ 1 / (8 * Real.pi ^ 2) * (18 * ‖X‖ ^ (-5 : ℝ)) := by
        gcongr
        exact abs_le.2 ⟨by linarith, by linarith⟩
    _ = _ := by ring

/-- Swapping two coordinates exchanges the corresponding diagonal components
of the smooth regularized Hessian, including after integration against a
pulled-back test function.
-/
theorem fiveDimensionalGammaRegularized_diagonal_integral_swap
    (ε : ℝ) (hε : ε ≠ 0) (i j : Fin 5)
    (φ : ℝ^5 → ℝ) :
    (∫ X : ℝ^5,
      iteratedPartialDeriv (n := 5) [i, i]
          (fiveDimensionalGammaRegularized ε) X *
        φ ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
          (Equiv.swap i j)) X)) =
      ∫ X : ℝ^5,
        iteratedPartialDeriv (n := 5) [j, j]
          (fiveDimensionalGammaRegularized ε) X * φ X := by
  set e : ℝ^5 ≃ₗᵢ[ℝ] ℝ^5 := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  rw [← e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (.of_forall fun X ↦ ?_)
  have hee : e (e X) = X := by
    ext k
    simp [e, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]
  dsimp only
  rw [fiveDimensionalGammaRegularized_iteratedPartialDeriv_two ε hε i i (e X),
    fiveDimensionalGammaRegularized_iteratedPartialDeriv_two ε hε j j X, hee, e.norm_map]
  simp [e, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

/-- Pulling back the test function by a single-coordinate sign flip negates
the mixed regularized Hessian pairing; the change of variables preserves volume.
-/
theorem fiveDimensionalGammaRegularized_mixed_integral_signFlip
    (ε : ℝ) (hε : ε ≠ 0) (i j : Fin 5) (hij : i ≠ j)
    (φ : ℝ^5 → ℝ) :
    (∫ X : ℝ^5,
      iteratedPartialDeriv (n := 5) [i, j]
          (fiveDimensionalGammaRegularized ε) X *
        φ (PDE.Common.coordinateReflection i X)) =
      -(∫ X : ℝ^5,
        iteratedPartialDeriv (n := 5) [i, j]
          (fiveDimensionalGammaRegularized ε) X * φ X) := by
  rw [← integral_neg, ← (PDE.Common.measurePreserving_coordinateReflection i).integral_comp
    (PDE.Common.coordinateReflectionLinearIsometryEquiv i).toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (.of_forall fun X ↦ ?_)
  dsimp only
  rw [fiveDimensionalGammaRegularized_iteratedPartialDeriv_two ε hε j i
      (PDE.Common.coordinateReflection i X),
    fiveDimensionalGammaRegularized_iteratedPartialDeriv_two ε hε j i X,
    PDE.Common.coordinateReflection_involutive i X, PDE.Common.norm_coordinateReflection]
  simp [Ne.symm hij]

/-- Pullback of a test function by a coordinate swap.
-/
noncomputable def fiveDimensionalSwapTestFunction
    (i j : Fin 5) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    𝓓((⊤ : Opens ℝ^5), ℝ) :=
  let e : ℝ^5 ≃ₗᵢ[ℝ] ℝ^5 :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  TestFunction.precompProper e e.contDiff
    e.toHomeomorph.isProperMap φ

/-- Evaluation of a coordinate-swapped test function.
-/
@[simp]
theorem fiveDimensionalSwapTestFunction_apply
    (i j : Fin 5) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ))
    (X : ℝ^5) :
    fiveDimensionalSwapTestFunction i j φ X =
      φ ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
        (Equiv.swap i j)) X) := rfl

/-- Pullback of a test function by a coordinate sign flip.
-/
noncomputable def fiveDimensionalSignFlipTestFunction
    (i : Fin 5) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    𝓓((⊤ : Opens ℝ^5), ℝ) :=
  TestFunction.precompProper
    (PDE.Common.coordinateReflection i)
    (PDE.Common.contDiff_coordinateReflection i ⊤)
    (PDE.Common.coordinateReflectionLinearIsometryEquiv i).toHomeomorph.isProperMap φ

/-- Evaluation of a sign-flipped test function.
-/
@[simp]
theorem fiveDimensionalSignFlipTestFunction_apply
    (i : Fin 5) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ))
    (X : ℝ^5) :
    fiveDimensionalSignFlipTestFunction i φ X =
      φ (PDE.Common.coordinateReflection i X) := rfl

/-- The distributional diagonal Hessian pairing is covariant under coordinate
swaps.
-/
theorem fundamentalSolution_five_distributional_diagonal_swap
    (i j : Fin 5) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    (∫ X : ℝ^5, (fundamentalSolution 5) X *
        iteratedPartialDeriv (n := 5) [i, i]
          (fiveDimensionalSwapTestFunction i j φ).toFun X) =
      ∫ X : ℝ^5, (fundamentalSolution 5) X *
        iteratedPartialDeriv (n := 5) [j, j] φ.toFun X := by
  have hi := fiveDimensionalGammaRegularized_distributionalHessian_tendsto
    i i (fiveDimensionalSwapTestFunction i j φ)
  have hj := fiveDimensionalGammaRegularized_distributionalHessian_tendsto j j φ
  apply tendsto_nhds_unique hi
  apply hj.congr'
  filter_upwards [] with n
  simpa using (fiveDimensionalGammaRegularized_diagonal_integral_swap
    ((n + 1 : ℝ)⁻¹) (by positivity) i j φ.toFun).symm

/-- A mixed distributional Hessian pairing changes sign under reflection in
one of its coordinate directions.
-/
theorem fundamentalSolution_five_distributional_mixed_signFlip
    (i j : Fin 5) (hij : i ≠ j) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    (∫ X : ℝ^5, (fundamentalSolution 5) X *
        iteratedPartialDeriv (n := 5) [j, i]
          (fiveDimensionalSignFlipTestFunction i φ).toFun X) =
      -(∫ X : ℝ^5, (fundamentalSolution 5) X *
        iteratedPartialDeriv (n := 5) [j, i] φ.toFun X) := by
  have hflip := fiveDimensionalGammaRegularized_distributionalHessian_tendsto
    j i (fiveDimensionalSignFlipTestFunction i φ)
  have horig := fiveDimensionalGammaRegularized_distributionalHessian_tendsto j i φ
  apply tendsto_nhds_unique hflip
  apply horig.neg.congr'
  filter_upwards [] with n
  simpa using (fiveDimensionalGammaRegularized_mixed_integral_signFlip
    ((n + 1 : ℝ)⁻¹) (by positivity) i j hij φ.toFun).symm

/-- Every positive spherical truncation of a diagonal classical Hessian
pairing is covariant under coordinate swaps.
-/
theorem fundamentalSolution_five_classical_diagonal_truncation_swap
    (δ : ℝ) (hδ : 0 < δ) (i j : Fin 5)
    (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    (∫ X in {X : ℝ^5 | δ < ‖X‖},
      iteratedPartialDeriv (n := 5) [i, i] (fundamentalSolution 5) X *
        (fiveDimensionalSwapTestFunction i j φ).toFun X) =
      ∫ X in {X : ℝ^5 | δ < ‖X‖},
        iteratedPartialDeriv (n := 5) [j, j] (fundamentalSolution 5) X *
          φ.toFun X := by
  let e : ℝ^5 ≃ₗᵢ[ℝ] ℝ^5 := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have h := e.measurePreserving.setIntegral_preimage_emb e.toHomeomorph.measurableEmbedding
    (fun X ↦ iteratedPartialDeriv (n := 5) [j, j] (fundamentalSolution 5) X * φ.toFun X)
    {X | δ < ‖X‖}
  rw [← h]
  simp only [Set.preimage_ofPred_eq, LinearIsometryEquiv.norm_map]
  refine setIntegral_congr_fun (measurableSet_lt measurable_const measurable_norm)
    fun X (hX : δ < ‖X‖) ↦ ?_
  have hX0 : X ≠ 0 := norm_pos_iff.1 (hδ.trans hX)
  rw [fundamentalSolution_five_iteratedPartialDeriv_two i i X hX0,
    fundamentalSolution_five_iteratedPartialDeriv_two j j (e X) (by simpa using hX0)]
  simp [e, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

/-- Every positive spherical truncation of a mixed classical Hessian pairing
changes sign under reflection in one of its coordinate directions.
-/
theorem fundamentalSolution_five_classical_mixed_truncation_signFlip
    (δ : ℝ) (hδ : 0 < δ) (i j : Fin 5) (hij : i ≠ j)
    (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    (∫ X in {X : ℝ^5 | δ < ‖X‖},
      iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X *
        (fiveDimensionalSignFlipTestFunction i φ).toFun X) =
      -(∫ X in {X : ℝ^5 | δ < ‖X‖},
        iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X *
          φ.toFun X) := by
  have h := (PDE.Common.measurePreserving_coordinateReflection i).setIntegral_preimage_emb
    (PDE.Common.coordinateReflectionLinearIsometryEquiv i).toHomeomorph.measurableEmbedding
    (fun X ↦ iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X * φ.toFun X)
    {X | δ < ‖X‖}
  rw [← h, ← integral_neg]
  simp only [Set.preimage_ofPred_eq, PDE.Common.norm_coordinateReflection]
  refine setIntegral_congr_fun (measurableSet_lt measurable_const measurable_norm)
    fun X (hX : δ < ‖X‖) ↦ ?_
  have hX0 : X ≠ 0 := norm_pos_iff.1 (hδ.trans hX)
  rw [fundamentalSolution_five_iteratedPartialDeriv_two j i X hX0,
    fundamentalSolution_five_iteratedPartialDeriv_two j i (PDE.Common.coordinateReflection i X)
      (fun he0 ↦ hX0 ((PDE.Common.coordinateReflection_eq_zero_iff i X).mp he0)),
    PDE.Common.norm_coordinateReflection]
  simp [Ne.symm hij]

end PotentialTheory
