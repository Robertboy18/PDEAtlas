/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.FundamentalSolution
import PDE.Analysis.MeasureTheory.SphereSymmetry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Spherical moments and angular cancellation

Coordinate symmetry determines the second moments of the five-dimensional
unit sphere. The resulting zero angular mean of the Hessian kernel controls
inner boundary limits and the radial principal-value integral.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter LineDeriv TopologicalSpace SobolevSpace
open scoped Distributions ENNReal Topology
open PDE.Analysis

namespace PotentialTheory

/-- Coordinate swaps preserve every diagonal second moment of the canonical
surface measure on the five-dimensional unit sphere.
-/
theorem fiveDimensionalSphere_diagonalMoment_eq (i j : Fin 5) :
    (∫ ω : Metric.sphere (0 : ℝ^5) 1,
        ((ω : ℝ^5) i) ^ 2
        ∂(volume : Measure ℝ^5).toSphere) =
      ∫ ω : Metric.sphere (0 : ℝ^5) 1,
        ((ω : ℝ^5) j) ^ 2
        ∂(volume : Measure ℝ^5).toSphere := by
  let e : ℝ^5 ≃ₗᵢ[ℝ] ℝ^5 :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have h := e.measurePreserving_toSphere.integral_comp
    (MeasureTheory.sphereLinearIsometryEquiv e).measurableEmbedding
    (fun ω : Metric.sphere (0 : ℝ^5) 1 ↦
      ((ω : ℝ^5) i) ^ 2)
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp [MeasureTheory.sphereLinearIsometryEquiv, e,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

/-- Each diagonal second moment on the five-dimensional unit sphere equals
the volume of the unit ball, namely `8*pi^2/15`. This is the analytic source
of the local Hessian coefficient `1/5`.
-/
theorem fiveDimensionalSphere_diagonalMoment (i : Fin 5) :
    (∫ ω : Metric.sphere (0 : ℝ^5) 1,
        ((ω : ℝ^5) i) ^ 2
        ∂(volume : Measure ℝ^5).toSphere) =
      8 * Real.pi ^ 2 / 15 := by
  let μ : Measure (Metric.sphere (0 : ℝ^5) 1) := (volume : Measure ℝ^5).toSphere
  have hint (k : Fin 5) : Integrable (fun ω : Metric.sphere (0 : ℝ^5) 1 ↦ ((ω : ℝ^5) k) ^ 2) μ :=
    (by fun_prop : Continuous fun ω : Metric.sphere (0 : ℝ^5) 1 ↦
      ((ω : ℝ^5) k) ^ 2).integrable_of_hasCompactSupport (.of_compactSpace _)
  have h1 (ω : Metric.sphere (0 : ℝ^5) 1) : ∑ k : Fin 5, ((ω : ℝ^5) k) ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, mem_sphere_zero_iff_norm.mp ω.property, one_pow]
  have htrace : 5 * ∫ ω, ((ω : ℝ^5) i) ^ 2 ∂μ = 5 * (8 * Real.pi ^ 2 / 15) := by
    calc 5 * ∫ ω, ((ω : ℝ^5) i) ^ 2 ∂μ = ∑ k : Fin 5, ∫ ω, ((ω : ℝ^5) k) ^ 2 ∂μ := by
          simp [μ, fiveDimensionalSphere_diagonalMoment_eq _ i]
      _ = ∫ ω, ∑ k : Fin 5, ((ω : ℝ^5) k) ^ 2 ∂μ := (integral_finsetSum _ fun k _ ↦ hint k).symm
      _ = 5 * (8 * Real.pi ^ 2 / 15) := by
        have := PDE.Analysis.unitSphereArea_eq 5
        rw [PDE.Analysis.unitBallVolume_five, Nat.cast_ofNat] at this
        rw [← this]
        simp [μ, h1, PDE.Analysis.unitSphereArea, MeasureTheory.measureReal_def]
  linarith

/-- Distinct coordinate second moments vanish on the five-dimensional unit
sphere by invariance under a single-coordinate sign flip.
-/
theorem fiveDimensionalSphere_mixedMoment_zero
    (i j : Fin 5) (hij : i ≠ j) :
    (∫ ω : Metric.sphere (0 : ℝ^5) 1,
        (ω : ℝ^5) i *
          (ω : ℝ^5) j
        ∂(volume : Measure ℝ^5).toSphere) = 0 := by
  let signs : (k : Fin 5) → ℝ ≃ₗᵢ[ℝ] ℝ := fun k ↦
    if k = i then LinearIsometryEquiv.neg ℝ else
      LinearIsometryEquiv.refl ℝ ℝ
  let e : ℝ^5 ≃ₗᵢ[ℝ] ℝ^5 :=
    LinearIsometryEquiv.piLpCongrRight 2 signs
  have h := e.measurePreserving_toSphere.integral_comp
    (MeasureTheory.sphereLinearIsometryEquiv e).measurableEmbedding
    (fun ω : Metric.sphere (0 : ℝ^5) 1 ↦
      (ω : ℝ^5) i *
        (ω : ℝ^5) j)
  have hneg :
      (∫ ω : Metric.sphere (0 : ℝ^5) 1,
        ((MeasureTheory.sphereLinearIsometryEquiv e ω : Metric.sphere
          (0 : ℝ^5) 1) : ℝ^5) i *
        ((MeasureTheory.sphereLinearIsometryEquiv e ω : Metric.sphere
          (0 : ℝ^5) 1) : ℝ^5) j
          ∂(volume : Measure ℝ^5).toSphere) =
        -(∫ ω : Metric.sphere (0 : ℝ^5) 1,
          (ω : ℝ^5) i *
            (ω : ℝ^5) j
          ∂(volume : Measure ℝ^5).toSphere) := by
    have hji : j ≠ i := Ne.symm hij
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with ω
    simp [MeasureTheory.sphereLinearIsometryEquiv, e, signs,
      LinearIsometryEquiv.piLpCongrRight_apply, hji]
  rw [hneg] at h
  linarith

/-- The angular part of the punctured-sphere Hessian boundary term converges
to the exact diagonal mass and vanishes for mixed coordinates.
-/
theorem fiveDimensionalSphere_testFunction_angularLimit
    (i j : Fin 5) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    Tendsto (fun ε : ℝ ↦
      ∫ ω : Metric.sphere (0 : ℝ^5) 1,
        (ω : ℝ^5) i *
          (ω : ℝ^5) j *
          φ.toFun (ε • (ω : ℝ^5))
        ∂(volume : Measure ℝ^5).toSphere)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((if i = j then 8 * Real.pi ^ 2 / 15 else 0) * φ.toFun 0)) := by
  let μ : Measure (Metric.sphere (0 : ℝ^5) 1) := (volume : Measure ℝ^5).toSphere
  obtain ⟨C, hC⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hφc : Continuous φ.toFun := φ.continuous
  have hcoord (k : Fin 5) (ω : Metric.sphere (0 : ℝ^5) 1) : |(ω : ℝ^5) k| ≤ 1 := by
    simpa [mem_sphere_zero_iff_norm.mp ω.property] using PiLp.norm_apply_le (ω : ℝ^5) k
  have htendsto : Tendsto
      (fun ε : ℝ ↦ ∫ ω, (ω : ℝ^5) i * (ω : ℝ^5) j * φ.toFun (ε • (ω : ℝ^5)) ∂μ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ ω, (ω : ℝ^5) i * (ω : ℝ^5) j * φ.toFun 0 ∂μ)) := by
    refine tendsto_integral_filter_of_norm_le_const
      (.of_forall fun ε ↦ (by fun_prop : Continuous fun ω : Metric.sphere (0 : ℝ^5) 1 ↦
        (ω : ℝ^5) i * (ω : ℝ^5) j * φ.toFun (ε • (ω : ℝ^5))).aestronglyMeasurable)
      ⟨C, .of_forall fun ε ↦ .of_forall fun ω ↦ ?_⟩ (.of_forall fun ω ↦ ?_)
    · have := hcoord i ω
      have := hcoord j ω
      have : |φ.toFun (ε • (ω : ℝ^5))| ≤ C := by simpa using hC (ε • (ω : ℝ^5))
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc _ ≤ 1 * 1 * C := by gcongr
        _ = C := by ring
    · have : Tendsto (fun ε : ℝ ↦ ε • (ω : ℝ^5)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        simpa using ((by fun_prop : Continuous fun ε : ℝ ↦ ε • (ω : ℝ^5)).tendsto 0).mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi 0))
      exact tendsto_const_nhds.mul (hφc.continuousAt.tendsto.comp this)
  have heval : ∫ ω, (ω : ℝ^5) i * (ω : ℝ^5) j * φ.toFun 0 ∂μ =
      (if i = j then 8 * Real.pi ^ 2 / 15 else 0) * φ.toFun 0 := by
    rw [integral_mul_const]
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl, show ∫ ω, (ω : ℝ^5) i * (ω : ℝ^5) i ∂μ = 8 * Real.pi ^ 2 / 15 by
        simpa [pow_two] using fiveDimensionalSphere_diagonalMoment i]
    · rw [ite_eq_right hij, fiveDimensionalSphere_mixedMoment_zero i j hij, zero_mul]
  rwa [heval] at htendsto

/-- A bounded continuous angular multiplier may be passed through the
shrinking-sphere test-function limit.
-/
theorem fiveDimensionalSphere_weighted_testFunction_tendsto
    (a : Metric.sphere (0 : ℝ^5) 1 → ℝ)
    (ha : Continuous a) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    Tendsto (fun ε : ℝ ↦
      ∫ ω : Metric.sphere (0 : ℝ^5) 1,
        a ω * φ.toFun (ε • (ω : ℝ^5))
        ∂(volume : Measure ℝ^5).toSphere)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ ω : Metric.sphere (0 : ℝ^5) 1,
        a ω * φ.toFun 0
        ∂(volume : Measure ℝ^5).toSphere)) := by
  obtain ⟨A, hA⟩ := ha.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace a)
  obtain ⟨C, hC⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  refine tendsto_integral_filter_of_norm_le_const
    (.of_forall fun ε ↦ (ha.mul (φ.continuous.comp (by fun_prop))).aestronglyMeasurable)
    ⟨A * C, .of_forall fun ε ↦ .of_forall fun ω ↦ ?_⟩ (.of_forall fun ω ↦ ?_)
  · rw [norm_mul]
    exact mul_le_mul (hA ω) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hA ω))
  · have : Tendsto (fun ε : ℝ ↦ ε • (ω : ℝ^5)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa using ((by fun_prop : Continuous fun ε : ℝ ↦ ε • (ω : ℝ^5)).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi 0))
    exact tendsto_const_nhds.mul (φ.continuous.continuousAt.tendsto.comp this)

/-- The `Gamma_5 * partial_j phi` inner-boundary term vanishes: surface
scaling leaves one positive power of the shrinking radius.
-/
theorem fundamentalSolution_five_testDerivative_boundary_zero
    (i j : Fin 5) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    Tendsto (fun ε : ℝ ↦
      ε * ∫ ω : Metric.sphere (0 : ℝ^5) 1,
        (ω : ℝ^5) i *
          (∂[j] φ.toFun)
            (ε • (ω : ℝ^5))
        ∂(volume : Measure ℝ^5).toSphere)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let a : Metric.sphere (0 : ℝ^5) 1 → ℝ :=
    fun ω ↦ (ω : ℝ^5) i
  let dφ : 𝓓((⊤ : Opens ℝ^5), ℝ) :=
    TestFunction.lineDerivCLM ℝ
      (EuclideanSpace.single j (1 : ℝ)) φ
  have hdφ (X : ℝ^5) :
      dφ X = (∂[j] φ.toFun) X := by
    rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
    rw [(φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    rfl
  have ha : Continuous a := by fun_prop
  have hInt := fiveDimensionalSphere_weighted_testFunction_tendsto a ha
    dφ
  have heps : Tendsto (fun ε : ℝ ↦ ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  simpa [a, hdφ] using heps.mul hInt

/-- The normal-derivative inner-boundary term has the exact local Hessian
mass `(delta_ij/5) * phi(0)`.
-/
theorem fundamentalSolution_five_normalDerivative_boundary_limit
    (i j : Fin 5) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    Tendsto (fun ε : ℝ ↦
      (3 / (8 * Real.pi ^ 2)) *
        ∫ ω : Metric.sphere (0 : ℝ^5) 1,
          (ω : ℝ^5) i *
            (ω : ℝ^5) j *
            φ.toFun (ε • (ω : ℝ^5))
          ∂(volume : Measure ℝ^5).toSphere)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((if i = j then (1 / 5 : ℝ) else 0) * φ.toFun 0)) := by
  have h :=
    (fiveDimensionalSphere_testFunction_angularLimit i j φ).const_mul
      (3 / (8 * Real.pi ^ 2))
  convert h using 1
  by_cases hij : i = j
  · rw [ite_eq_left hij, ite_eq_left hij]
    field_simp [Real.pi_ne_zero]
    ring_nf
  · simp [hij]

/-- The homogeneous angular kernel of every Cartesian Hessian component has
zero spherical mean. This cancellation removes the apparent logarithmic
divergence in the principal-value integral.
-/
theorem fiveDimensionalHessianAngularMean_zero (i j : Fin 5) :
    (∫ ω : Metric.sphere (0 : ℝ^5) 1,
      ((15 / (8 * Real.pi ^ 2)) *
          (ω : ℝ^5) i *
          (ω : ℝ^5) j -
        (3 / (8 * Real.pi ^ 2)) * (if i = j then 1 else 0))
      ∂(volume : Measure ℝ^5).toSphere) = 0 := by
  have harea : ((volume : Measure ℝ^5).toSphere).real Set.univ = 8 * Real.pi ^ 2 / 3 := by
    have := PDE.Analysis.unitSphereArea_eq 5
    rw [PDE.Analysis.unitSphereArea, PDE.Analysis.unitBallVolume_five] at this
    rw [measureReal_def, this]
    ring
  have hint : Integrable (fun ω : Metric.sphere (0 : ℝ^5) 1 ↦
      15 / (8 * Real.pi ^ 2) * ((ω : ℝ^5) i * (ω : ℝ^5) j)) (volume : Measure ℝ^5).toSphere :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) (.of_compactSpace _)
  simp only [mul_assoc]
  rw [integral_sub hint (integrable_const _), integral_const_mul, integral_const, smul_eq_mul,
    harea]
  by_cases hij : i = j
  · subst j
    simp only [← pow_two, ite_eq_left, fiveDimensionalSphere_diagonalMoment i]
    field_simp
    ring
  · rw [ite_eq_right hij, fiveDimensionalSphere_mixedMoment_zero i j hij]
    ring

/-- After zero-mean angular cancellation, the critical radial Hessian profile
is integrable with respect to `dr`. Equivalently, the original homogeneous
degree `-5` kernel has a well-defined spherical principal value in dimension
five.
-/
theorem fiveDimensionalHessianAngularRadial_integrable
    (i j : Fin 5) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    IntegrableOn (fun r : ℝ ↦ r⁻¹ *
      ∫ ω : Metric.sphere (0 : ℝ^5) 1,
        ((15 / (8 * Real.pi ^ 2)) *
            (ω : ℝ^5) i *
            (ω : ℝ^5) j -
          (3 / (8 * Real.pi ^ 2)) * (if i = j then 1 else 0)) *
          φ.toFun (r • (ω : ℝ^5))
        ∂(volume : Measure ℝ^5).toSphere)
      (Set.Ioi 0) := by
  let S := Metric.sphere (0 : ℝ^5) 1
  let μ : Measure S := (volume : Measure ℝ^5).toSphere
  let a : S → ℝ := fun ω ↦ (15 / (8 * Real.pi ^ 2)) * (ω : ℝ^5) i * (ω : ℝ^5) j -
    (3 / (8 * Real.pi ^ 2)) * (if i = j then 1 else 0)
  let A : ℝ → ℝ := fun r ↦ ∫ ω : S, a ω * φ.toFun (r • (ω : ℝ^5)) ∂μ
  have ha : Continuous a := by dsimp only [a]; fun_prop
  have hamean : ∫ ω : S, a ω ∂μ = 0 := by
    simpa [S, μ, a] using fiveDimensionalHessianAngularMean_zero i j
  have haInt : Integrable a μ := ha.integrable_of_hasCompactSupport (.of_compactSpace _)
  let M : ℝ := ∫ ω : S, |a ω| ∂μ
  have hMnonneg : 0 ≤ M := integral_nonneg fun _ ↦ abs_nonneg _
  obtain ⟨C, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    φ.hasCompactSupport φ.contDiff (by simp)
  obtain ⟨R, hRpos, hφzero⟩ := φ.hasCompactSupport.exists_pos_le_norm
  have hAcont : Continuous A := by
    have hinter : Continuous (Function.uncurry fun (r : ℝ) (ω : S) ↦
        a ω * φ.toFun (r • (ω : ℝ^5))) :=
      (ha.comp continuous_snd).mul
        (φ.continuous.comp (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)))
    simpa [A] using continuousOn_univ.mp (continuousOn_integral_of_compact_support (μ := μ)
      (s := Set.univ) (k := Set.univ) isCompact_univ hinter.continuousOn (by simp))
  -- `∫ a = 0`, so `A r = ∫ a ω (φ (r ω) - φ 0)`, of size at most `C r M`
  have hA_bound (r : ℝ) (hr : 0 < r) : |A r| ≤ (C : ℝ) * r * M := by
    have hInt : Integrable (fun ω : S ↦ a ω * φ.toFun (r • (ω : ℝ^5))) μ :=
      (ha.mul (φ.continuous.comp (by fun_prop))).integrable_of_hasCompactSupport
        (.of_compactSpace _)
    have hA : A r = ∫ ω : S, a ω * (φ.toFun (r • (ω : ℝ^5)) - φ.toFun 0) ∂μ := by
      simp_rw [mul_sub]
      rw [integral_sub hInt (haInt.mul_const _), integral_mul_const, hamean, zero_mul, sub_zero]
    rw [hA, ← Real.norm_eq_abs,
      show (C : ℝ) * r * M = ∫ ω : S, (C : ℝ) * r * |a ω| ∂μ from (integral_const_mul _ _).symm]
    refine norm_integral_le_of_norm_le (haInt.abs.const_mul _) (ae_of_all _ fun ω ↦ ?_)
    have hφdiff : |φ.toFun (r • (ω : ℝ^5)) - φ.toFun 0| ≤ C * r := by
      simpa [Real.norm_eq_abs, norm_smul, abs_of_pos hr, mem_sphere_zero_iff_norm.mp ω.property]
        using hLip.norm_sub_le (r • (ω : ℝ^5)) 0
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hφdiff (abs_nonneg _)
  have hA_zero (r : ℝ) (hr : R ≤ r) : A r = 0 := by
    refine integral_eq_zero_of_ae (ae_of_all _ fun ω ↦ ?_)
    have hz := hφzero (r • (ω : ℝ^5)) (by
      simpa [norm_smul, abs_of_nonneg (hRpos.le.trans hr), mem_sphere_zero_iff_norm.mp ω.property])
    simp [hz]
  -- domination by `C M` on `(0, R]` and `0` beyond
  let K : ℝ := (C : ℝ) * M
  refine (((integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (C := K)
    (s := Set.Ioc 0 R) measure_Ioc_lt_top.ne)).mono_measure Measure.restrict_le_self).mono
    (((continuousOn_inv₀.mono fun r hr ↦ hr.ne').mul hAcont.continuousOn).aestronglyMeasurable
      measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r (hr : 0 < r)
  change |r⁻¹ * A r| ≤ |(Set.Ioc 0 R).indicator (fun _ ↦ K) r|
  by_cases hrR : r ≤ R
  · rw [Set.indicator_of_mem (Set.mem_Ioc.2 ⟨hr, hrR⟩),
      abs_of_nonneg (mul_nonneg C.coe_nonneg hMnonneg), abs_mul, abs_of_pos (inv_pos.2 hr)]
    calc r⁻¹ * |A r| ≤ r⁻¹ * (C * r * M) :=
          mul_le_mul_of_nonneg_left (hA_bound r hr) (inv_nonneg.2 hr.le)
      _ = C * M := by field_simp
  · rw [Set.indicator_of_notMem fun h ↦ hrR h.2]
    simp [hA_zero r (le_of_not_ge hrR)]

/-- The radial form of the spherical principal value converges as the inner
radius tends to zero from above.
-/
theorem fiveDimensionalHessianAngularRadial_tendsto
    (i j : Fin 5) (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    Tendsto (fun ε : ℝ ↦
      ∫ r in Set.Ioi ε, r⁻¹ *
        ∫ ω : Metric.sphere (0 : ℝ^5) 1,
          ((15 / (8 * Real.pi ^ 2)) *
              (ω : ℝ^5) i *
              (ω : ℝ^5) j -
            (3 / (8 * Real.pi ^ 2)) * (if i = j then 1 else 0)) *
            φ.toFun (r • (ω : ℝ^5))
          ∂(volume : Measure ℝ^5).toSphere)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ r in Set.Ioi (0 : ℝ), r⁻¹ *
        ∫ ω : Metric.sphere (0 : ℝ^5) 1,
          ((15 / (8 * Real.pi ^ 2)) *
              (ω : ℝ^5) i *
              (ω : ℝ^5) j -
            (3 / (8 * Real.pi ^ 2)) * (if i = j then 1 else 0)) *
            φ.toFun (r • (ω : ℝ^5))
          ∂(volume : Measure ℝ^5).toSphere)) := by
  let F : ℝ → ℝ := fun r ↦ r⁻¹ * ∫ ω : Metric.sphere (0 : ℝ^5) 1,
    ((15 / (8 * Real.pi ^ 2)) * (ω : ℝ^5) i * (ω : ℝ^5) j -
      (3 / (8 * Real.pi ^ 2)) * (if i = j then 1 else 0)) * φ.toFun (r • (ω : ℝ^5))
    ∂(volume : Measure ℝ^5).toSphere
  have hF : IntegrableOn F (Set.Ioi 0) := fiveDimensionalHessianAngularRadial_integrable i j φ
  have hmeasure : Tendsto (fun ε : ℝ ↦ volume (Set.Ioc (0 : ℝ) ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simp_rw [Real.volume_Ioc, sub_zero]
    simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun ε : ℝ ↦ ε) (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0))
  -- the integral over `(0, ε]` tends to `0`
  have hsmall : Tendsto (fun ε : ℝ ↦ ∫ r in (0 : ℝ)..ε, F r)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine (((integrable_indicator_iff measurableSet_Ioi).2 hF).tendsto_setIntegral_nhds_zero
      hmeasure).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [intervalIntegral.integral_of_le hε.le]
    exact setIntegral_congr_fun measurableSet_Ioc fun r hr ↦ by simp [hr.1]
  change Tendsto (fun ε : ℝ ↦ ∫ r in Set.Ioi ε, F r) (nhdsWithin 0 (Set.Ioi 0))
    (nhds (∫ r in Set.Ioi (0 : ℝ), F r))
  refine (by simpa using (tendsto_const_nhds (x := ∫ r in Set.Ioi (0 : ℝ), F r)).sub hsmall :
    Tendsto (fun ε : ℝ ↦ (∫ r in Set.Ioi (0 : ℝ), F r) - ∫ r in (0 : ℝ)..ε, F r)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ r in Set.Ioi (0 : ℝ), F r))).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  linarith [intervalIntegral.integral_Ioi_sub_Ioi hF hε.le]

end PotentialTheory
