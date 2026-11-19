/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Hyperbolic.FirstOrder.Viscosity.Data
public import PDE.Analysis.Evolution.Time.WeakDerivative.Representative
public import PDE.Analysis.Evolution.Compactness.Lp.Basic
public import PDE.DistributionTheory.TestFunction.IntegrationByParts
public import PDE.FDeriv.Calculus
import CAS.ExactTactic

/-!
# A time-dependent constant is necessary in the viscous velocity estimate

Fix the nonzero smooth compactly supported profile `q = spatialTest` on `ℝ`.
With zero transport and zero initial data, `u(t,x) = t*q(x)` solves
`u_t - ε Δu = q - ε*t*Δq`. Taking `ε = T⁻²`, `T ≥ 1`, makes the terminal
`H¹` norm grow like `T` while the mixed forcing norm grows at most like `√T`.

For the bound on the velocity `u_t` in the energy estimate (17) of Evans, §7.3.2, Theorem 2,
this family shows that the constant depends on the time horizon, as the finite-horizon estimate
in `PDE.Hyperbolic.FirstOrder.Viscosity.UniformVelocity` allows.

`PolynomialFamily.Solution` and `PolynomialFamily.Forcing` realize the solution and its
forcing in the Sobolev spaces of the strong-solution definition, and
`PolynomialFamily.VelocityEstimate` shows that one constant cannot cover every time
horizon.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.3.2(c), Theorem 2 (Energy estimates), (17),
  p. 426.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.Examples.Hyperbolic.Viscosity.PolynomialFamily

open MeasureTheory Set TopologicalSpace PDE.Common
open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Distributions Sobolev

/-- Use the norm inherited from the Sobolev submodule at every profile order. -/
local instance profileNormedAddCommGroup (k : ℕ) : NormedAddCommGroup W^{k,2}(ℝ^1) :=
  (wkpSubmoduleOn 1 k 2 univ).normedAddCommGroup

/-- Scalar multiplication uses the same Sobolev submodule norm. -/
local instance profileNormedSpace (k : ℕ) : NormedSpace ℝ W^{k,2}(ℝ^1) :=
  (wkpSubmoduleOn 1 k 2 univ).normedSpace

/-- The Laplacian `Δq` as a test function. -/
def laplaceTest : 𝓓((⊤ : Opens (ℝ^1)), ℝ) :=
  ⟨laplacian (spatialTest : ℝ^1 → ℝ), spatialTest.contDiff_laplacian,
    spatialTest.hasCompactSupport_laplacian, subset_univ _⟩

/-- The profile `q` as an element of `W^{k,2}`. -/
def profile (k : ℕ) : W^{k,2}(ℝ^1) := globalTestFunctionToWkpOn spatialTest

/-- The Laplacian `Δq` as an element of `W^{k,2}`. -/
def laplaceProfile (k : ℕ) : W^{k,2}(ℝ^1) := globalTestFunctionToWkpOn laplaceTest

/-- The solution `u(t, x) = t q(x)`. -/
def solution (t : ℝ) (x : ℝ^1) : ℝ := t * spatialTest x

/-- Its forcing `q - ε t Δq` for viscosity `ε`. -/
def forcing (ε t : ℝ) (x : ℝ^1) : ℝ :=
  spatialTest x - ε * t * laplacian (spatialTest : ℝ^1 → ℝ) x

/-- `∂ₜu - ε Δu = q - ε t Δq` at every point. -/
theorem solution_equation (ε t : ℝ) (x : ℝ^1) :
    deriv (fun s ↦ solution s x) t - ε * laplacian (solution t) x = forcing ε t x := by
  have hd : deriv (fun s ↦ s * spatialTest x) t = spatialTest x := by cas
  change deriv (fun s ↦ s * spatialTest x) t -
    ε * laplacian (fun y ↦ t * spatialTest y) x = _
  rw [hd, laplacian_const_smul]
  unfold forcing
  cas

/-- The solution as the curve `t ↦ t q` in `W^{k,2}`. -/
def state (k : ℕ) (t : ℝ) : W^{k,2}(ℝ^1) := t • profile k

/-- The `H¹` forcing curve. -/
def forcingCurve (ε t : ℝ) : W^{1,2}(ℝ^1) :=
  profile 1 - (ε * t) • laplaceProfile 1

/-- The forcing as a Bochner `L²(H¹)` element. -/
def forcingLp (T ε : ℝ) : Lp W^{1,2}(ℝ^1) 2 (volume.restrict (Ioc 0 T)) :=
  (memLp_restrict_Ioc_of_continuousOn
    (by unfold forcingCurve; fun_prop : ContinuousOn (forcingCurve ε) (Icc 0 T))).toLp _

/-- The time derivative `-ε Δq` of the forcing, in `L²(L²)`. -/
def forcingVelocityLp (T ε : ℝ) :
    Lp (DerivLp 1 2 univ) 2 (volume.restrict (Ioc 0 T)) :=
  (memLp_const (-ε • wkpBaseCoordinateCLM (laplaceProfile 1))).toLp _

/-- The spatial profile is nonzero as a Sobolev element. -/
theorem profile_one_ne_zero : profile 1 ≠ 0 := by
  intro hz
  have he := globalTestFunctionToWkpOn_coordinate_ae (k := 1) (p := 2) (Ω := univ)
    spatialTest (baseIndex 1 1)
  have hbase : wkpBaseCoordinateCLM (profile 1) = 0 := by rw [hz, map_zero]
  have hae : (0 : ℝ^1 → ℝ) =ᵐ[volume] spatialTest := by
    have he' : (wkpBaseCoordinateCLM (profile 1) : ℝ^1 → ℝ) =ᵐ[volume] spatialTest := by
      simpa only [profile, wkpBaseCoordinateCLM_apply, domainMeasure, Measure.restrict_univ,
        baseIndex_toList, iteratedPartialDeriv, TestFunction.toFun_eq_coe] using he
    rw [hbase] at he'
    have hz0 := Lp.coeFn_zero ℝ 2 (domainMeasure 1 univ)
    simp only [domainMeasure, Measure.restrict_univ] at hz0
    exact hz0.symm.trans he'
  exact spatialTest_ne_zero
    (Measure.eq_of_ae_eq hae.symm spatialTest.continuous continuous_const)

/-- The terminal state grows linearly in the time horizon. -/
theorem norm_state (T : ℝ) (hT : 0 ≤ T) : ‖state 1 T‖ = T * ‖profile 1‖ := by
  simp [state, norm_smul, Real.norm_eq_abs, abs_of_nonneg hT]

private theorem norm_lp_le_sqrt {E : Type*} [NormedAddCommGroup E]
    {T C : ℝ} (hT : 0 ≤ T) {f : Lp E 2 (volume.restrict (Ioc 0 T))}
    (hC : 0 ≤ C) (hf : ∀ᵐ t ∂volume.restrict (Ioc 0 T), ‖f t‖ ≤ C) :
    ‖f‖ ≤ Real.sqrt T * C := by
  convert Lp.norm_le_of_ae_bound hC hf using 1
  simp only [measureUnivNNReal, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
    ENNReal.toReal_ofNat, Real.sqrt_eq_rpow]
  simp only [one_div]
  change T ^ (2 : ℝ)⁻¹ * C = (ENNReal.ofReal T).toReal ^ (2 : ℝ)⁻¹ * C
  rw [ENNReal.toReal_ofReal hT]

/-- On `0 ≤ t ≤ T`, the coefficient `T⁻² t` is at most one. -/
theorem scaled_time_le_one {T t : ℝ} (hT : 1 ≤ T) (ht : t ∈ Icc 0 T) :
    0 ≤ (T ^ 2)⁻¹ * t ∧ (T ^ 2)⁻¹ * t ≤ 1 := by
  have hpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  constructor
  · exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) ht.1
  · apply (inv_mul_le_iff₀ (sq_pos_of_pos hpos)).2
    nlinarith [ht.2]

/-- For `ε = T⁻²` and `T ≥ 1`, the forcing norms are at most `√T` times a constant
independent of `T`. -/
theorem forcing_norm_bound {T : ℝ} (hT : 1 ≤ T) :
    ‖forcingLp T (T ^ 2)⁻¹‖ + ‖forcingVelocityLp T (T ^ 2)⁻¹‖ ≤
      Real.sqrt T * (‖profile 1‖ + ‖laplaceProfile 1‖ +
        ‖wkpBaseCoordinateCLM (laplaceProfile 1)‖) := by
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hF : ‖forcingLp T (T ^ 2)⁻¹‖ ≤
      Real.sqrt T * (‖profile 1‖ + ‖laplaceProfile 1‖) := by
    apply norm_lp_le_sqrt hT0 (add_nonneg (norm_nonneg _) (norm_nonneg _))
    filter_upwards [(memLp_restrict_Ioc_of_continuousOn
      (by unfold forcingCurve; fun_prop :
        ContinuousOn (forcingCurve (T ^ 2)⁻¹) (Icc 0 T))).coeFn_toLp,
      ae_restrict_mem measurableSet_Ioc] with t ht htT
    rw [show forcingLp T (T ^ 2)⁻¹ t = forcingCurve (T ^ 2)⁻¹ t from ht]
    have hs := scaled_time_le_one hT (Ioc_subset_Icc_self htT)
    calc
      ‖forcingCurve (T ^ 2)⁻¹ t‖ ≤
          ‖profile 1‖ + ‖((T ^ 2)⁻¹ * t) • laplaceProfile 1‖ := norm_sub_le _ _
      _ ≤ ‖profile 1‖ + ‖laplaceProfile 1‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
        exact add_le_add_right (mul_le_of_le_one_left (norm_nonneg _) hs.2) _
  have hV : ‖forcingVelocityLp T (T ^ 2)⁻¹‖ ≤
      Real.sqrt T * ‖wkpBaseCoordinateCLM (laplaceProfile 1)‖ := by
    apply norm_lp_le_sqrt hT0 (norm_nonneg _)
    filter_upwards [(memLp_const
      (p := (2 : ℝ≥0∞)) (μ := volume.restrict (Ioc 0 T))
      (-(T ^ 2)⁻¹ • wkpBaseCoordinateCLM (laplaceProfile 1))).coeFn_toLp] with t ht
    rw [show forcingVelocityLp T (T ^ 2)⁻¹ t =
      -(T ^ 2)⁻¹ • wkpBaseCoordinateCLM (laplaceProfile 1) from ht,
      norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply mul_le_of_le_one_left (norm_nonneg _)
    exact inv_le_one_of_one_le₀ (by nlinarith : 1 ≤ T ^ 2)
  calc
    _ ≤ Real.sqrt T * (‖profile 1‖ + ‖laplaceProfile 1‖) +
        Real.sqrt T * ‖wkpBaseCoordinateCLM (laplaceProfile 1)‖ := add_le_add hF hV
    _ = _ := (mul_add _ _ _).symm

/-- No constant `C` gives `‖u(T)‖ ≤ C (‖F‖ + ‖Fₜ‖)` for all `T ≥ 1` with `ε = T⁻²`. -/
theorem not_exists_time_uniform_bound :
    ¬ ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T →
      ‖state 1 T‖ ≤ C * (‖forcingLp T (T ^ 2)⁻¹‖ +
        ‖forcingVelocityLp T (T ^ 2)⁻¹‖) := by
  rintro ⟨C, hC⟩
  let A := ‖profile 1‖
  let K := ‖profile 1‖ + ‖laplaceProfile 1‖ +
    ‖wkpBaseCoordinateCLM (laplaceProfile 1)‖
  have hA : 0 < A := norm_pos_iff.mpr profile_one_ne_zero
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let R := 1 + max C 0 * K / A
  have hR : 1 ≤ R := by
    have hp : 0 ≤ max C 0 * K / A := by positivity
    dsimp [R]
    linarith
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hT : 1 ≤ R ^ 2 := by nlinarith
  have he := hC (R ^ 2) hT
  rw [norm_state _ (sq_nonneg _)] at he
  have hF := forcing_norm_bound hT
  rw [Real.sqrt_sq hR0.le] at hF
  have hbound : R ^ 2 * A ≤ max C 0 * (R * K) := by
    calc
      _ ≤ C * _ := he
      _ ≤ max C 0 * _ := mul_le_mul_of_nonneg_right (le_max_left _ _)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ _ := mul_le_mul_of_nonneg_left hF (le_max_right _ _)
  have hRA : R * A = A + max C 0 * K := by dsimp [R]; cas
  nlinarith

end PDE.Examples.Hyperbolic.Viscosity.PolynomialFamily
