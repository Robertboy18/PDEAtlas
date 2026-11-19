/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.RieszPressure
public import PDE.Fluid.Incompressible.LerayProjection.SobolevDilation
public import PDE.Fluid.NavierStokes.Stationary.SolenoidalDensity
public import PDE.Elliptic.Regularity.Interior.Weyl.SecondOrder

/-!
# The Riesz pressure on Sobolev classes

For a family `M = (Mᵢⱼ)` of classes in `Hᵏ(ℝⁿ)`, with rows `Mᵢ = (Mᵢⱼ)ⱼ` in vector `Hᵏ`,

`rieszPressureSobolev n k M = Σᵢ ((Π Mᵢ)ᵢ - Mᵢᵢ)`

is a class in `Hᵏ(ℝⁿ)` depending linearly and continuously on `M`. For a smooth compactly
supported `χ` the Leray projection of `Δχ eᵢ` is `Δχ eᵢ - ∇∂ᵢχ`, minus the divergence-free field
`curlCurlField χ i`, so the operator solves the weak form
`∫ P Δχ = -Σᵢⱼ ∫ Mᵢⱼ ∂ⱼ∂ᵢχ` of `-ΔP = Σᵢⱼ ∂ᵢ∂ⱼMᵢⱼ`
(`integral_rieszPressureSobolev_mul_laplacian`). A square-integrable function on `ℝⁿ`, `n ≥ 2`,
that annihilates the Laplacian of every test function vanishes
(`LaplacianEquation.ae_eq_zero_of_integral_mul_laplacian_eq_zero`). Hence for `Mᵢⱼ = uᵢuⱼ` the
operator gives the Riesz pressure of `u` (`rieszPressure_ae_eq_rieszPressureSobolev`), and a
velocity whose products depend smoothly on a parameter in `Hᵏ` has a pressure that does too.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory SobolevSpace SobolevSpace.GraphSpace IncompressibleFlow Set
open scoped ENNReal Sobolev RealInnerProductSpace ContDiff

namespace NavierStokes

variable {n k : ℕ}

/-- The Riesz pressure operator `M ↦ Σᵢ ((Π Mᵢ)ᵢ - Mᵢᵢ)` on families of rows in vector `Hᵏ`. -/
def rieszPressureSobolev (n k : ℕ) : (Fin n → VectorH n k) →L[ℝ] W^{k,2}(ℝ^n) :=
  ∑ i : Fin n, (PiLp.proj 2 (fun _ : Fin n ↦ W^{k,2}(ℝ^n)) i).comp
    ((leraySobolev n k - ContinuousLinearMap.id ℝ (VectorH n k)).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ VectorH n k) i))

/-- The base coordinate of the Riesz pressure operator is `Σᵢ ((Π - I) Rᵢ)ᵢ`, with `Rᵢ` the base
row of `Mᵢ`. -/
theorem wkpCoordinateCLM_rieszPressureSobolev (M : Fin n → VectorH n k) :
    wkpCoordinateCLM (baseIndex n k) (rieszPressureSobolev n k M) =
      ∑ i, l2Coordinate i (lerayProjection n (l2SobolevRow (baseIndex n k) (M i)) -
        l2SobolevRow (baseIndex n k) (M i)) := by
  simp only [rieszPressureSobolev, sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, map_sum,
    sub_apply, ContinuousLinearMap.id_apply, PiLp.proj_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [PiLp.sub_apply, map_sub, map_sub, leraySobolev_coordinate, l2Coordinate_l2SobolevRow]

/-- The pairing of a vector base row with a smooth compactly supported field. -/
theorem inner_l2SobolevRow_toLp (V : VectorH n k) {F : ℝ^n → ℝ^n}
    (hF : MemLp F 2 (domainMeasure n univ)) :
    ⟪l2SobolevRow (baseIndex n k) V, hF.toLp F⟫ =
      ∑ j, ∫ x, baseRepresentative (V j) x * F x j := by
  have hbase (j : Fin n) : MemLp (baseRepresentative (V j)) 2 volume := by
    have h := Lp.memLp (wkpBaseCoordinateCLM (V j))
    simp only [domainMeasure, Measure.restrict_univ] at h
    exact h
  have hFj (j : Fin n) : MemLp (fun x ↦ F x j) 2 volume := by
    have h := (EuclideanSpace.proj j : ℝ^n →L[ℝ] ℝ).comp_memLp' hF
    simp only [domainMeasure, Measure.restrict_univ] at h
    exact h
  rw [L2.inner_def, (integral_finsetSum (μ := volume) Finset.univ
    (f := fun j x ↦ baseRepresentative (V j) x * F x j)
    fun j _ ↦ (hbase j).integrable_mul (hFj j)).symm]
  have hrow := Lp.euclideanTuple_apply_ae (fun j ↦ wkpCoordinateCLM (baseIndex n k) (V j))
  have hFe := hF.coeFn_toLp
  simp only [domainMeasure, Measure.restrict_univ] at hrow hFe ⊢
  refine integral_congr_ae ?_
  filter_upwards [hrow, hFe] with x h1 h2
  rw [l2SobolevRow_apply, PiLp.inner_apply, h2]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [h1 j, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real,
    mul_comm, wkpCoordinateCLM_apply]
  rfl

/-- The `i`-th scalar coordinate of a vector `L²` class paired with a scalar field `g` is the
vector pairing with `g eᵢ`. -/
theorem integral_l2Coordinate_mul (W : WholeSpaceL2 n) (i : Fin n) {g : ℝ^n → ℝ}
    (hg : MemLp (fun x ↦ g x • EuclideanSpace.single i (1 : ℝ)) 2 (domainMeasure n univ)) :
    ∫ x, (l2Coordinate i W : ℝ^n → ℝ) x * g x = ⟪W, hg.toLp _⟫ := by
  rw [L2.inner_def]
  have h1 := l2Coordinate_ae i W
  have h2 := hg.coeFn_toLp
  simp only [domainMeasure, Measure.restrict_univ] at h1 h2 ⊢
  refine integral_congr_ae ?_
  filter_upwards [h1, h2] with x hx hy
  rw [hx, hy, inner_smul_right, EuclideanSpace.inner_single_right]
  simp [mul_comm]

/-- The test field `∇∂ᵢχ` as an `L²` gradient. -/
private def partialDerivTestFunction {χ : ℝ^n → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (i : Fin n) : TestFunctionOn n univ :=
  ⟨TestFunction.mk (fun x ↦ PDE.partialDeriv i χ x) (PDE.contDiff_top_partialDeriv hχ)
    (hc.partialDeriv i) (subset_univ _), subset_univ _⟩

/-- **The Leray projection of `Δχ eᵢ`.** For a smooth compactly supported `χ`, the projection
of `Δχ eᵢ` is `Δχ eᵢ - ∇∂ᵢχ`, the negative of the divergence-free field `curlCurlField χ i`. -/
theorem lerayProjection_laplacian_single {χ : ℝ^n → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (i : Fin n)
    (hE : MemLp (fun x ↦ PDE.laplacian χ x • EuclideanSpace.single i (1 : ℝ)) 2
      (domainMeasure n univ))
    (hC : MemLp (Stationary.curlCurlField χ i) 2 (domainMeasure n univ)) :
    lerayProjection n (hE.toLp _) = -hC.toLp _ := by
  set G := l2TestGradient (partialDerivTestFunction hχ hc i)
  have hEG : hE.toLp _ = G - hC.toLp _ := by
    apply Lp.ext
    have h1 := hE.coeFn_toLp
    have h2 := hC.coeFn_toLp
    filter_upwards [h1, h2, Lp.coeFn_sub G (hC.toLp _),
      l2TestGradient_apply_ae (partialDerivTestFunction hχ hc i)] with x hx hy hs hg
    rw [hx, hs, Pi.sub_apply, hy]
    refine PiLp.ext fun j ↦ ?_
    rw [PiLp.sub_apply, hg j, Stationary.curlCurlField_apply, PiLp.smul_apply]
    change _ = PDE.partialDeriv j (fun y ↦ PDE.partialDeriv i χ y) x - _
    by_cases hji : j = i
    · subst hji
      simp
    · simp [hji]
  have hsol : hC.toLp _ ∈ l2Solenoidal n :=
    toLp_mem_l2Solenoidal hC (SpatialFieldDivergenceFree.distributionallyDivergenceFree
      (fun x ↦ Stationary.divergence_curlCurlField hχ i x)
      ((Stationary.contDiff_curlCurlField hχ i).of_le (by simp)))
  have hG : lerayProjection n G = 0 := by
    apply (l2Solenoidal n).eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _)
    intro w hw
    rw [sub_zero, real_inner_comm]
    exact (mem_l2Solenoidal_iff_inner w).mp hw _
  rw [hEG, map_sub, hG, lerayProjection_eq_self hsol, zero_sub]

/-- **The weak Poisson equation of the Riesz pressure operator.** For every smooth compactly
supported `χ`, `∫ P Δχ = -Σᵢⱼ ∫ Mᵢⱼ ∂ⱼ∂ᵢχ` with `P = rieszPressureSobolev n k M`. -/
theorem integral_rieszPressureSobolev_mul_laplacian (M : Fin n → VectorH n k) {χ : ℝ^n → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    ∫ x, baseRepresentative (rieszPressureSobolev n k M) x * PDE.laplacian χ x =
      -∑ i, ∑ j, ∫ x, baseRepresentative (M i j) x * iteratedPartialDeriv [j, i] χ x := by
  set R : Fin n → WholeSpaceL2 n := fun i ↦ l2SobolevRow (baseIndex n k) (M i) with hRdef
  have hΔ : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ PDE.laplacian χ x) := PDE.contDiff_laplacian_coord hχ
  have hΔc : HasCompactSupport (fun x ↦ PDE.laplacian χ x) :=
    HasCompactSupport.coordinate_laplacian hc
  have hE (i : Fin n) : MemLp (fun x ↦ PDE.laplacian χ x • EuclideanSpace.single i (1 : ℝ)) 2
      (domainMeasure n univ) :=
    (hΔ.continuous.smul continuous_const).memLp_of_hasCompactSupport hΔc.smul_right
  have hC (i : Fin n) : MemLp (Stationary.curlCurlField χ i) 2 (domainMeasure n univ) :=
    (Stationary.contDiff_curlCurlField hχ i).continuous.memLp_of_hasCompactSupport
      (Stationary.hasCompactSupport_curlCurlField hc i)
  -- the curl-curl pairing
  have hcurl (i : Fin n) : ⟪R i, (hC i).toLp _⟫ =
      (∑ j, ∫ x, baseRepresentative (M i j) x * iteratedPartialDeriv [j, i] χ x) -
        ∫ x, baseRepresentative (M i i) x * PDE.laplacian χ x := by
    have hb (j : Fin n) : MemLp (baseRepresentative (M i j)) 2 volume := by
      have h := Lp.memLp (wkpBaseCoordinateCLM (M i j))
      simp only [domainMeasure, Measure.restrict_univ] at h
      exact h
    have hd (j : Fin n) : MemLp (fun x ↦ iteratedPartialDeriv [j, i] χ x) 2 volume :=
      (PDE.contDiff_top_iteratedPartialDeriv hχ [j, i]).continuous.memLp_of_hasCompactSupport
        (hc.iteratedPartialDeriv [j, i])
    have hl : MemLp (fun x ↦ PDE.laplacian χ x) 2 volume :=
      hΔ.continuous.memLp_of_hasCompactSupport hΔc
    rw [hRdef, inner_l2SobolevRow_toLp]
    have hsplit (j : Fin n) : ∫ x, baseRepresentative (M i j) x *
        Stationary.curlCurlField χ i x j = (∫ x, baseRepresentative (M i j) x *
          iteratedPartialDeriv [j, i] χ x) -
          ∫ x, baseRepresentative (M i j) x * (if j = i then PDE.laplacian χ x else 0) := by
      have h1 : Integrable (fun x ↦ baseRepresentative (M i j) x *
          iteratedPartialDeriv [j, i] χ x) volume := (hb j).integrable_mul (hd j)
      have h2 : Integrable (fun x ↦ baseRepresentative (M i j) x *
          (if j = i then PDE.laplacian χ x else 0)) volume := by
        by_cases hji : j = i
        · subst hji
          simp only [ite_true]
          exact (hb j).integrable_mul hl
        · simp [hji]
      rw [← integral_sub h1 h2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      simp only [Stationary.curlCurlField_apply, mul_sub]
      rfl
    rw [Finset.sum_congr rfl fun j _ ↦ hsplit j, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_eq_single i (fun j _ hji ↦ by simp [hji]) (by simp)]
    simp
  -- the coordinate of the pressure
  have hcoord : (wkpCoordinateCLM (baseIndex n k) (rieszPressureSobolev n k M) : ℝ^n → ℝ)
      =ᵐ[volume] fun x ↦ ∑ i, (l2Coordinate i (lerayProjection n (R i) - R i) : ℝ^n → ℝ) x := by
    rw [wkpCoordinateCLM_rieszPressureSobolev]
    have h := Lp.coeFn_fun_finsetSum Finset.univ
      (fun i ↦ l2Coordinate i (lerayProjection n (R i) - R i))
    simp only [domainMeasure, Measure.restrict_univ] at h
    exact h
  have hbase : baseRepresentative (rieszPressureSobolev n k M) =
      ⇑(wkpCoordinateCLM (baseIndex n k) (rieszPressureSobolev n k M)) := by
    rw [wkpCoordinateCLM_apply]
    rfl
  have hint (i : Fin n) : Integrable (fun x ↦
      (l2Coordinate i (lerayProjection n (R i) - R i) : ℝ^n → ℝ) x * PDE.laplacian χ x)
      volume := by
    have h := Lp.memLp (l2Coordinate i (lerayProjection n (R i) - R i))
    simp only [domainMeasure, Measure.restrict_univ] at h
    exact h.integrable_mul (q := 2) (hΔ.continuous.memLp_of_hasCompactSupport hΔc)
  have hdiag (i : Fin n) : ⟪R i, (hE i).toLp _⟫ =
      ∫ x, baseRepresentative (M i i) x * PDE.laplacian χ x := by
    rw [← integral_l2Coordinate_mul, hRdef, l2Coordinate_l2SobolevRow, wkpCoordinateCLM_apply]
    rfl
  have hterm (i : Fin n) : ∫ x, (l2Coordinate i (lerayProjection n (R i) - R i) : ℝ^n → ℝ) x *
      PDE.laplacian χ x = -∑ j, ∫ x, baseRepresentative (M i j) x *
        iteratedPartialDeriv [j, i] χ x := by
    rw [integral_l2Coordinate_mul _ i (hE i), inner_sub_left, hdiag]
    have hself : ⟪lerayProjection n (R i), (hE i).toLp _⟫ = -⟪R i, (hC i).toLp _⟫ := by
      rw [lerayProjection, Submodule.inner_starProjection_left_eq_right, ← lerayProjection,
        lerayProjection_laplacian_single hχ hc i (hE i) (hC i), inner_neg_right]
    rw [hself, hcurl]
    ring
  rw [hbase, integral_congr_ae (hcoord.mono fun x hx ↦ by rw [hx]),
    show (fun x ↦ (∑ i, (l2Coordinate i (lerayProjection n (R i) - R i) : ℝ^n → ℝ) x) *
      PDE.laplacian χ x) = fun x ↦ ∑ i, (l2Coordinate i (lerayProjection n (R i) - R i) :
        ℝ^n → ℝ) x * PDE.laplacian χ x from funext fun x ↦ Finset.sum_mul _ _ _,
    integral_finsetSum _ fun i _ ↦ hint i, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ hterm i

/-- **The Riesz pressure through Sobolev classes.** On `ℝⁿ`, `n ≥ 2`, if the classes `Mᵢⱼ` in
`Hᵏ` are the products `uᵢuⱼ` almost everywhere, then the Riesz pressure of `u` is almost
everywhere the base representative of `rieszPressureSobolev n k M`. -/
theorem rieszPressure_ae_eq_rieszPressureSobolev (hn : 2 ≤ n) {u : ℝ^n → ℝ^n}
    (M : Fin n → VectorH n k)
    (hM : ∀ i j, baseRepresentative (M i j) =ᵐ[volume] fun x ↦ u x i * u x j) :
    rieszPressure u =ᵐ[volume] baseRepresentative (rieszPressureSobolev n k M) := by
  have hb {m : ℕ} (V : W^{m,2}(ℝ^n)) : MemLp (baseRepresentative V) 2 volume := by
    have h := Lp.memLp (wkpBaseCoordinateCLM V)
    simp only [domainMeasure, Measure.restrict_univ] at h
    exact h
  have hu (i j : Fin n) : MemLp (fun x ↦ u x i * u x j) 2 volume := (hb (M i j)).ae_eq (hM i j)
  have hP := memLp_two_rieszPressure u
  have hQ := hb (rieszPressureSobolev n k M)
  have hzero := LaplacianEquation.ae_eq_zero_of_integral_mul_laplacian_eq_zero hn
    (hP.sub hQ) fun χ hχ hc ↦ by
      have hl : MemLp (fun x ↦ PDE.laplacian χ x) 2 volume :=
        (PDE.contDiff_laplacian_coord hχ).continuous.memLp_of_hasCompactSupport
          (HasCompactSupport.coordinate_laplacian hc)
      have h1 : Integrable (fun x ↦ rieszPressure u x * PDE.laplacian χ x) volume :=
        hP.integrable_mul hl
      have h2 : Integrable (fun x ↦ baseRepresentative (rieszPressureSobolev n k M) x *
          PDE.laplacian χ x) volume := hQ.integrable_mul hl
      have hsub : (fun x ↦ (rieszPressure u - baseRepresentative (rieszPressureSobolev n k M)) x *
          PDE.laplacian χ x) = fun x ↦ rieszPressure u x * PDE.laplacian χ x -
            baseRepresentative (rieszPressureSobolev n k M) x * PDE.laplacian χ x :=
        funext fun x ↦ by rw [Pi.sub_apply, sub_mul]
      rw [hsub, integral_sub h1 h2, integral_rieszPressure_mul_laplacian hu hχ hc,
        integral_rieszPressureSobolev_mul_laplacian M hχ hc, neg_sub_neg, sub_eq_zero]
      have hterm (i j : Fin n) : ∫ x, baseRepresentative (M i j) x *
          iteratedPartialDeriv [j, i] χ x = ∫ x, u x i * u x j * iteratedPartialDeriv [j, i] χ x :=
        integral_congr_ae ((hM i j).mono fun x hx ↦ by simp only [hx])
      simp_rw [hterm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      simp_rw [mul_comm (u _ j) (u _ i)]
  filter_upwards [hzero] with x hx
  simpa [sub_eq_zero] using hx

/-- **The `L²` bound of the Riesz pressure.** For `u ∈ L⁴(ℝⁿ)`,
`‖P‖_{L²} ≤ n² ‖u‖_{L⁴}²`. -/
theorem toReal_eLpNorm_rieszPressure_le {u : ℝ^n → ℝ^n} (hu : MemLp u 4 volume) :
    (eLpNorm (rieszPressure u) 2 volume).toReal ≤
      (n : ℝ) ^ 2 * (eLpNorm u 4 volume).toReal ^ 2 := by
  have h₁ : (eLpNorm (rieszPressure u) 2 volume).toReal ≤ ‖rieszPressureL2 u‖ := by
    rw [Lp.norm_def, eLpNorm_congr_ae (rieszPressure_ae_eq u)]
    refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top _)
      (eLpNorm_mono (Complex.continuous_re.comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable _)) fun x ↦ ?_)
    rw [Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _
  have h₂ : ‖rieszPressureL2 u‖ ≤ ∑ i, ∑ j, ‖velocityProductL2 u i j‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦
      PDE.Analysis.Fourier.norm_doubleRiesz_apply_le i j _)
  have hcomp (i : Fin n) : (eLpNorm (fun x ↦ u x i) 4 volume) ≤ eLpNorm u 4 volume :=
    eLpNorm_mono ((EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).comp_memLp' hu).aestronglyMeasurable
      fun x ↦ PiLp.norm_apply_le _ i
  have h₃ (i j : Fin n) : ‖velocityProductL2 u i j‖ ≤ (eLpNorm u 4 volume).toReal ^ 2 := by
    have hm := memLp_two_mul_of_memLp_four hu i j
    have hi : MemLp (fun x ↦ u x i) 4 volume :=
      (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).comp_memLp' hu
    have hj : MemLp (fun x ↦ u x j) 4 volume :=
      (EuclideanSpace.proj j : ℝ^n →L[ℝ] ℝ).comp_memLp' hu
    have hnorm : ‖velocityProductL2 u i j‖ = (eLpNorm (fun x ↦ u x i * u x j) 2 volume).toReal := by
      rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_velocityProductL2 hm)]
      congr 1
      exact eLpNorm_congr_norm_ae hm.ofReal.aestronglyMeasurable hm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x ↦ Complex.norm_real _)
    have hH : eLpNorm (fun x ↦ u x i * u x j) 2 volume ≤
        eLpNorm (fun x ↦ u x i) 4 volume * eLpNorm (fun x ↦ u x j) 4 volume :=
      eLpNorm_smul_le_mul_eLpNorm (p := 4) (q := 4) hi.aestronglyMeasurable
        hj.aestronglyMeasurable
    rw [hnorm, sq]
    refine (ENNReal.toReal_mono (ENNReal.mul_ne_top hi.eLpNorm_ne_top hj.eLpNorm_ne_top)
      hH).trans ?_
    rw [ENNReal.toReal_mul]
    exact mul_le_mul (ENNReal.toReal_mono hu.eLpNorm_ne_top (hcomp i))
      (ENNReal.toReal_mono hu.eLpNorm_ne_top (hcomp j)) ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  calc (eLpNorm (rieszPressure u) 2 volume).toReal ≤ ∑ i : Fin n, ∑ j : Fin n,
        ‖velocityProductL2 u i j‖ := h₁.trans h₂
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, (eLpNorm u 4 volume).toReal ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ h₃ i j
    _ = (n : ℝ) ^ 2 * (eLpNorm u 4 volume).toReal ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ]
        ring

end NavierStokes
