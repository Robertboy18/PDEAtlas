/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.BiharmonicUniqueness
public import PDE.Fluid.NavierStokes.Stationary.Exhaustion
public import PDE.FDeriv.PartialDeriv.Support
public import PDE.FDeriv.PartialDeriv.Smooth
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Density of solenoidal test fields in divergence-free `H¹`

Smooth compactly supported divergence-free vector fields are dense, in the `H¹` norm, in the
divergence-free part of `H¹(ℝⁿ)ⁿ` for `n ≥ 1` (`mem_topologicalClosure_span_solenoidalTestFields`).

## How it works

We show that a divergence-free field orthogonal to every solenoidal test field vanishes
(`eq_zero_of_inner_solenoidalTestFields`); applied to a field minus its orthogonal projection onto
the closed span of the test fields, which is again divergence free, this gives the density. A
divergence-free field orthogonal to all test fields is orthogonal in particular to
`curl curl (χ eₖ) = ∇∂ₖχ - Δχ eₖ` (`curlCurlField`) for every smooth compactly supported `χ`. The
`H¹` pairing with a test field is `∑ᵢ ∫ yᵢ (φᵢ - Δφᵢ)` (`inner_testFieldH1`); the gradient part of
`curl curl (χ eₖ)` drops out against the divergence-free field, leaving `∫ yₖ (Δ² - Δ) χ = 0`
(`inner_testFieldH1_curlCurlField`), so each component vanishes by Fourier uniqueness
(`HeatEquation.WholeSpace.ae_eq_zero_of_integral_mul_biharmonic_sub_laplacian`). No Bogovskii
correction or vector potential is used.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace Laplacian
open scoped ENNReal NNReal Sobolev ContDiff SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Stationary

variable {n : ℕ}



theorem contDiff_component {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ) (i : Fin n) :
    ContDiff ℝ ∞ (fun x ↦ φ x i) :=
  (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).contDiff.comp hφ

theorem hasCompactSupport_component {φ : ℝ^n → ℝ^n} (hc : HasCompactSupport φ) (i : Fin n) :
    HasCompactSupport (fun x ↦ φ x i) :=
  hc.comp_left (g := fun v : ℝ^n ↦ v i) (by simp)

/-- The `H¹` embedding of a smooth compactly supported vector field, componentwise. -/
def testFieldH1 (φ : ℝ^n → ℝ^n) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)) :=
  WithLp.toLp 2 fun i ↦ mkWkpSpaceOnOfContDiff (n := n) (k := 1) (p := 2) (Ω := univ)
    (fun x ↦ φ x i) (contDiff_component hφ i) (hasCompactSupport_component hc i)

/-- Smooth compactly supported divergence-free fields, embedded in `H¹`. -/
def solenoidalTestFields (n : ℕ) : Set (PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) :=
  {v | ∃ (φ : ℝ^n → ℝ^n) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
    (∀ x, PDE.divergence φ x = 0) ∧ testFieldH1 φ hφ hc = v}

/-- The coordinates of a test field are the classical derivatives of its components. -/
theorem testFieldH1_coord_ae {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (i : Fin n) (α : DerivIndex n 1) :
    (wkpCoordinateCLM α (testFieldH1 φ hφ hc i) : ℝ^n → ℝ) =ᵐ[volume]
      fun x ↦ iteratedPartialDeriv α.toList (fun y ↦ φ y i) x := by
  have h := mkWkpSpaceOnOfContDiff_apply_ae (n := n) (k := 1) (p := 2) (Ω := univ)
    (fun y ↦ φ y i) (contDiff_component hφ i) (hasCompactSupport_component hc i) α
  have hTi : testFieldH1 φ hφ hc i = mkWkpSpaceOnOfContDiff (n := n) (k := 1) (p := 2)
      (Ω := univ) (fun y ↦ φ y i) (contDiff_component hφ i) (hasCompactSupport_component hc i) :=
    rfl
  rw [hTi]
  simpa [domainMeasure, wkpCoordinateCLM_apply] using h

/-- The base row of a test field is its component. -/
theorem testFieldH1_base_ae {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (i : Fin n) :
    (wkpBaseCoordinateCLM (testFieldH1 φ hφ hc i) : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ φ x i := by
  simpa [iteratedPartialDeriv, wkpBaseCoordinateCLM_apply] using
    testFieldH1_coord_ae hφ hc i (baseIndex n 1)

/-- The first derivative rows of a test field are the classical partial derivatives. -/
theorem testFieldH1_partial_ae {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (i j : Fin n) :
    (wkpCoordinateCLM (singleDerivIndex n j) (testFieldH1 φ hφ hc i) : ℝ^n → ℝ) =ᵐ[volume]
      fun x ↦ PDE.partialDeriv j (fun y ↦ φ y i) x := by
  simpa [iteratedPartialDeriv] using testFieldH1_coord_ae hφ hc i (singleDerivIndex n j)

/-- The `H¹` embedding of test fields is additive. -/
theorem testFieldH1_add {φ ψ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (h : ContDiff ℝ ∞ (φ + ψ))
    (hc : HasCompactSupport (φ + ψ)) :
    testFieldH1 (φ + ψ) h hc = testFieldH1 φ hφ hcφ + testFieldH1 ψ hψ hcψ := by
  ext i : 1
  apply wkpBaseCoordinateCLM_injective (n := n) (p := 2) isOpen_univ
  rw [PiLp.add_apply, map_add]
  apply Lp.ext
  have hsum := Lp.coeFn_add (wkpBaseCoordinateCLM (testFieldH1 φ hφ hcφ i))
    (wkpBaseCoordinateCLM (testFieldH1 ψ hψ hcψ i))
  simp only [domainMeasure, Measure.restrict_univ] at hsum ⊢
  filter_upwards [testFieldH1_base_ae h hc i, testFieldH1_base_ae hφ hcφ i,
    testFieldH1_base_ae hψ hcψ i, hsum] with x h1 h2 h3 h4
  rw [h1, h4, Pi.add_apply, Pi.add_apply, h2, h3, PiLp.add_apply]

/-- The `H¹` embedding of test fields is homogeneous. -/
theorem testFieldH1_smul (c : ℝ) {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (h : ContDiff ℝ ∞ (c • φ)) (hc : HasCompactSupport (c • φ)) :
    testFieldH1 (c • φ) h hc = c • testFieldH1 φ hφ hcφ := by
  ext i : 1
  apply wkpBaseCoordinateCLM_injective (n := n) (p := 2) isOpen_univ
  rw [PiLp.smul_apply, map_smul]
  apply Lp.ext
  have hsmul := Lp.coeFn_smul c (wkpBaseCoordinateCLM (testFieldH1 φ hφ hcφ i))
  simp only [domainMeasure, Measure.restrict_univ] at hsmul ⊢
  filter_upwards [testFieldH1_base_ae h hc i, testFieldH1_base_ae hφ hcφ i,
    hsmul] with x h1 h2 h3
  rw [h1, h3, Pi.smul_apply, Pi.smul_apply, h2, PiLp.smul_apply, smul_eq_mul]

/-- Integration by parts for a whole-space `H¹` function against a smooth compactly supported
test: `∫ u ∂ⱼψ = -∫ (∂ⱼu) ψ`. -/
theorem integral_base_mul_partialDeriv (U : H¹(ℝ^n)) (j : Fin n) {ψ : ℝ^n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    ∫ x, (wkpBaseCoordinateCLM U : ℝ^n → ℝ) x * PDE.partialDeriv j ψ x =
      -∫ x, (wkpCoordinateCLM (singleDerivIndex n j) U : ℝ^n → ℝ) x * ψ x := by
  have h := (U.property (singleDerivIndex n j)).integral_identity
    (TestFunction.mk ψ hψ hc (subset_univ _)) (subset_univ _)
  simp only [singleDerivIndex_toList, List.length_singleton, pow_one, neg_mul, one_mul,
    domainMeasure, Measure.restrict_univ] at h
  simpa [iteratedPartialDeriv, wkpBaseCoordinateCLM_apply, wkpCoordinateCLM_apply] using h

theorem integrable_base_mul (U : H¹(ℝ^n)) {ψ : ℝ^n → ℝ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) :
    Integrable (fun x ↦ (wkpBaseCoordinateCLM U : ℝ^n → ℝ) x * ψ x) volume := by
  have h1 : MemLp (wkpBaseCoordinateCLM U : ℝ^n → ℝ) 2 volume := by
    simpa [domainMeasure] using Lp.memLp (wkpBaseCoordinateCLM U)
  exact h1.integrable_mul (q := 2) (hψ.memLp_of_hasCompactSupport hc)

/-- The `H¹` pairing with a test field is `∑ᵢ ∫ yᵢ (φᵢ - Δφᵢ)`. -/
theorem inner_testFieldH1 (y : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) {φ : ℝ^n → ℝ^n}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    inner ℝ y (testFieldH1 φ hφ hc) = ∑ i, ∫ x, (wkpBaseCoordinateCLM (y i) : ℝ^n → ℝ) x *
      (φ x i - PDE.laplacian (fun z ↦ φ z i) x) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  set f : ℝ^n → ℝ := fun x ↦ φ x i
  have hf : ContDiff ℝ ∞ f := contDiff_component hφ i
  have hfc : HasCompactSupport f := hasCompactSupport_component hc i
  set T : H¹(ℝ^n) := mkWkpSpaceOnOfContDiff (n := n) (k := 1) (p := 2) (Ω := univ) f hf hfc
  have hTi : (testFieldH1 φ hφ hc) i = T := rfl
  rw [hTi]
  change inner ℝ ((y i : WkpAmbientOn n 1 2 univ)) (T : WkpAmbientOn n 1 2 univ) = _
  rw [ambient_inner_eq_base_add_sum_deriv]
  have hcoord : ∀ a : DerivIndex n 1, ((T : WkpAmbientOn n 1 2 univ) a : ℝ^n → ℝ) =ᵐ[volume]
      fun x ↦ iteratedPartialDeriv a.toList f x := by
    intro a
    have h := mkWkpSpaceOnOfContDiff_apply_ae (n := n) (k := 1) (p := 2) (Ω := univ) f hf hfc a
    simpa [domainMeasure] using h
  -- the base pairing
  have hbase : inner ℝ ((y i : WkpAmbientOn n 1 2 univ) (baseIndex n 1))
      ((T : WkpAmbientOn n 1 2 univ) (baseIndex n 1)) =
      ∫ x, (wkpBaseCoordinateCLM (y i) : ℝ^n → ℝ) x * f x := by
    rw [L2.inner_def]
    simp only [domainMeasure, Measure.restrict_univ]
    apply integral_congr_ae
    filter_upwards [hcoord (baseIndex n 1)] with x hx
    rw [hx]
    simp [iteratedPartialDeriv, wkpBaseCoordinateCLM_apply, mul_comm]
  -- the derivative pairings
  have hderiv : ∀ j : Fin n, inner ℝ ((y i : WkpAmbientOn n 1 2 univ) (singleDerivIndex n j))
      ((T : WkpAmbientOn n 1 2 univ) (singleDerivIndex n j)) =
      -∫ x, (wkpBaseCoordinateCLM (y i) : ℝ^n → ℝ) x *
        PDE.partialDeriv j (fun z ↦ PDE.partialDeriv j f z) x := by
    intro j
    rw [integral_base_mul_partialDeriv (y i) j (PDE.contDiff_top_partialDeriv (i := j) hf)
      (hfc.partialDeriv j), neg_neg, L2.inner_def]
    simp only [domainMeasure, Measure.restrict_univ]
    apply integral_congr_ae
    filter_upwards [hcoord (singleDerivIndex n j)] with x hx
    rw [hx]
    simp [iteratedPartialDeriv, wkpCoordinateCLM_apply, mul_comm]
  rw [hbase]
  simp_rw [hderiv]
  have hint : ∀ j : Fin n, Integrable (fun x ↦ (wkpBaseCoordinateCLM (y i) : ℝ^n → ℝ) x *
      PDE.partialDeriv j (fun z ↦ PDE.partialDeriv j f z) x) volume := by
    intro j
    exact integrable_base_mul (y i)
      ((PDE.contDiff_top_partialDeriv (i := j)
        (PDE.contDiff_top_partialDeriv (i := j) hf)).continuous)
      ((hfc.partialDeriv j).partialDeriv j)
  have hf0 := integrable_base_mul (y i) hf.continuous hfc
  simp only [PDE.laplacian, mul_sub, Finset.mul_sum]
  rw [integral_sub hf0 (integrable_finsetSum _ fun j _ ↦ hint j), integral_finsetSum _
    fun j _ ↦ hint j, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- Divergence-free `H¹` fields annihilate gradients of smooth compactly supported functions. -/
theorem sum_integral_base_mul_partialDeriv_eq_zero (y : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)))
    (hy : divergenceCLM y = 0) {ψ : ℝ^n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    ∑ i, ∫ x, (wkpBaseCoordinateCLM (y i) : ℝ^n → ℝ) x * PDE.partialDeriv i ψ x = 0 := by
  have hmem : MemLp ψ 2 (domainMeasure n univ) := by
    simpa [domainMeasure] using hψ.continuous.memLp_of_hasCompactSupport (μ := volume) hc
  set ψL : DerivLp n 2 univ := hmem.toLp ψ
  have hpair : ∀ i : Fin n, ∫ x, (wkpBaseCoordinateCLM (y i) : ℝ^n → ℝ) x *
      PDE.partialDeriv i ψ x =
      -inner ℝ (wkpCoordinateCLM (singleDerivIndex n i) (y i)) ψL := by
    intro i
    rw [integral_base_mul_partialDeriv (y i) i hψ hc, L2.inner_def]
    congr 1
    simp only [domainMeasure, Measure.restrict_univ]
    apply integral_congr_ae
    filter_upwards [show (ψL : ℝ^n → ℝ) =ᵐ[volume] ψ by
      simpa [domainMeasure] using hmem.coeFn_toLp] with x hx
    rw [hx, real_inner_eq_re_inner, RCLike.re_to_real]
    simp [mul_comm]
  simp_rw [hpair]
  rw [Finset.sum_neg_distrib, ← sum_inner, ← divergenceCLM_apply, hy, inner_zero_left, neg_zero]

theorem laplacian_sub_coord {f g : ℝ^n → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : ℝ^n) :
    PDE.laplacian (fun z ↦ f z - g z) x = PDE.laplacian f x - PDE.laplacian g x := by
  simp only [PDE.laplacian, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have h1 : (fun y ↦ PDE.partialDeriv j (fun z ↦ f z - g z) y) =
      fun y ↦ PDE.partialDeriv j f y - PDE.partialDeriv j g y := by
    funext y
    exact PDE.partialDeriv_sub (hf.differentiable (by simp)).differentiableAt
      (hg.differentiable (by simp)).differentiableAt
  rw [h1]
  exact PDE.partialDeriv_sub
    ((PDE.contDiff_top_partialDeriv (i := j) hf).differentiable (by simp)).differentiableAt
    ((PDE.contDiff_top_partialDeriv (i := j) hg).differentiable (by simp)).differentiableAt

theorem partialDeriv_eventuallyEq_zero {g : ℝ^n → ℝ} {x : ℝ^n} (h : g =ᶠ[𝓝 x] 0)
    (j : Fin n) : (fun z ↦ PDE.partialDeriv j g z) =ᶠ[𝓝 x] 0 := by
  filter_upwards [h.eventually_nhds] with z hz
  have hz' : g =ᶠ[𝓝 z] 0 := hz
  simp only [Pi.zero_apply]
  rw [PDE.partialDeriv, hz'.fderiv_eq]
  simp

theorem laplacian_coord_eventuallyEq_zero {g : ℝ^n → ℝ} {x : ℝ^n} (h : g =ᶠ[𝓝 x] 0) :
    (fun z ↦ PDE.laplacian g z) =ᶠ[𝓝 x] 0 := by
  have hdd : ∀ j : Fin n, (fun z ↦ PDE.partialDeriv j (fun w ↦ PDE.partialDeriv j g w) z)
      =ᶠ[𝓝 x] 0 := fun j ↦ partialDeriv_eventuallyEq_zero (partialDeriv_eventuallyEq_zero h j) j
  have hall : ∀ᶠ z in 𝓝 x, ∀ j : Fin n,
      PDE.partialDeriv j (fun w ↦ PDE.partialDeriv j g w) z = 0 :=
    Filter.eventually_all.mpr fun j ↦ hdd j
  filter_upwards [hall] with z hz
  simp only [PDE.laplacian, Pi.zero_apply]
  exact Finset.sum_eq_zero fun j _ ↦ hz j

theorem hasCompactSupport_laplacian_coord {g : ℝ^n → ℝ} (hc : HasCompactSupport g) :
    HasCompactSupport (fun x ↦ PDE.laplacian g x) := by
  apply HasCompactSupport.intro hc
  intro x hx
  exact (laplacian_coord_eventuallyEq_zero (notMem_tsupport_iff_eventuallyEq.mp hx)).eq_of_nhds

/-- The components of the field `x ↦ Dφ(x) x` of a smooth vector field are continuous. -/
theorem continuous_fderiv_apply_self_component {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ)
    (i : Fin n) : Continuous (fun x ↦ fderiv ℝ φ x x i) :=
  (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).continuous.comp
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_id)

/-- The components of the field `x ↦ Dφ(x) x` vanish outside the support of `φ`. -/
theorem hasCompactSupport_fderiv_apply_self_component {φ : ℝ^n → ℝ^n}
    (hc : HasCompactSupport φ) (i : Fin n) : HasCompactSupport (fun x ↦ fderiv ℝ φ x x i) := by
  apply HasCompactSupport.intro hc
  intro x hx
  simp [fderiv_of_notMem_tsupport ℝ hx]

/-- Pairing an `L²` function with `c φᵢ + ½ (Dφ(x) x)ᵢ - Δφᵢ` for a smooth compactly supported
field `φ` splits into the three pairings. With `c = μ + 1` in dimension three this is the
pairing with the formal adjoint of `μ + L₀`, `L₀ = -1/2 - (1/2) x·∇ - Δ`. -/
theorem integral_mul_shiftedAdjoint (f : DerivLp n 2 univ) (c : ℝ) {φ : ℝ^n → ℝ^n}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (i : Fin n) :
    ∫ x, (f : ℝ^n → ℝ) x *
        (c * φ x i + (1 / 2) * fderiv ℝ φ x x i - PDE.laplacian (fun y ↦ φ y i) x) =
      c * (∫ x, (f : ℝ^n → ℝ) x * φ x i) +
        (1 / 2) * (∫ x, (f : ℝ^n → ℝ) x * fderiv ℝ φ x x i) -
        ∫ x, (f : ℝ^n → ℝ) x * PDE.laplacian (fun y ↦ φ y i) x := by
  have hf : MemLp (f : ℝ^n → ℝ) 2 volume := by simpa [domainMeasure] using Lp.memLp f
  have hφi : ContDiff ℝ ∞ (fun x ↦ φ x i) := contDiff_component hφ i
  have hφc : HasCompactSupport (fun x ↦ φ x i) := hasCompactSupport_component hc i
  have h1 : Integrable (fun x ↦ (f : ℝ^n → ℝ) x * φ x i) :=
    hf.integrable_mul (q := 2) (hφi.continuous.memLp_of_hasCompactSupport hφc)
  have h2 : Integrable (fun x ↦ (f : ℝ^n → ℝ) x * fderiv ℝ φ x x i) :=
    hf.integrable_mul (q := 2) ((continuous_fderiv_apply_self_component hφ i)
      |>.memLp_of_hasCompactSupport (hasCompactSupport_fderiv_apply_self_component hc i))
  have h3 : Integrable (fun x ↦ (f : ℝ^n → ℝ) x * PDE.laplacian (fun y ↦ φ y i) x) :=
    hf.integrable_mul (q := 2) ((PDE.contDiff_laplacian_coord hφi).continuous
      |>.memLp_of_hasCompactSupport (hasCompactSupport_laplacian_coord hφc))
  have e : (fun x ↦ (f : ℝ^n → ℝ) x *
      (c * φ x i + (1 / 2) * fderiv ℝ φ x x i - PDE.laplacian (fun y ↦ φ y i) x)) =
      fun x ↦ c * ((f : ℝ^n → ℝ) x * φ x i) + (1 / 2) * ((f : ℝ^n → ℝ) x * fderiv ℝ φ x x i) -
        (f : ℝ^n → ℝ) x * PDE.laplacian (fun y ↦ φ y i) x := by
    funext x
    ring
  rw [e, integral_sub _ h3, integral_add (h1.const_mul _) (h2.const_mul _), integral_const_mul,
    integral_const_mul]
  exact (h1.const_mul _).add (h2.const_mul _)

/-- The field `curl curl (χ eₖ) = ∇∂ₖχ - Δχ eₖ`, written with coordinate derivatives. -/
def curlCurlField (χ : ℝ^n → ℝ) (k : Fin n) (x : ℝ^n) : ℝ^n :=
  WithLp.toLp 2 fun i ↦ PDE.partialDeriv i (fun z ↦ PDE.partialDeriv k χ z) x -
    if i = k then PDE.laplacian χ x else 0

theorem curlCurlField_apply (χ : ℝ^n → ℝ) (k i : Fin n) (x : ℝ^n) :
    curlCurlField χ k x i = PDE.partialDeriv i (fun z ↦ PDE.partialDeriv k χ z) x -
      if i = k then PDE.laplacian χ x else 0 := rfl

theorem contDiff_curlCurlField {χ : ℝ^n → ℝ} (hχ : ContDiff ℝ ∞ χ) (k : Fin n) :
    ContDiff ℝ ∞ (curlCurlField χ k) := by
  apply contDiff_piLp'
  intro i
  simp only [curlCurlField_apply]
  apply (PDE.contDiff_top_partialDeriv (i := i) (PDE.contDiff_top_partialDeriv (i := k) hχ)).sub
  split_ifs
  · exact PDE.contDiff_laplacian_coord hχ
  · exact contDiff_const

theorem hasCompactSupport_curlCurlField {χ : ℝ^n → ℝ} (hc : HasCompactSupport χ) (k : Fin n) :
    HasCompactSupport (curlCurlField χ k) := by
  apply HasCompactSupport.intro hc
  intro x hx
  have hev : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
  have hd : ∀ j : Fin n, (fun z ↦ PDE.partialDeriv j χ z) =ᶠ[𝓝 x] 0 := by
    intro j
    filter_upwards [hev.eventually_nhds] with z hz
    have hz' : χ =ᶠ[𝓝 z] 0 := hz
    simp only [Pi.zero_apply]
    rw [PDE.partialDeriv, hz'.fderiv_eq]
    simp
  have hdd : ∀ i j : Fin n, PDE.partialDeriv i (fun z ↦ PDE.partialDeriv j χ z) x = 0 := by
    intro i j
    rw [PDE.partialDeriv, (hd j).fderiv_eq]
    simp
  ext i
  simp only [curlCurlField_apply, hdd, PDE.laplacian, Finset.sum_const_zero, ite_self,
    sub_zero, PiLp.zero_apply]

/-- The field `curl curl (χ eₖ)` is divergence free. -/
theorem divergence_curlCurlField {χ : ℝ^n → ℝ} (hχ : ContDiff ℝ ∞ χ) (k : Fin n) (x : ℝ^n) :
    PDE.divergence (curlCurlField χ k) x = 0 := by
  simp only [PDE.divergence, curlCurlField_apply]
  have hsub : ∀ i : Fin n, PDE.partialDeriv i (fun y ↦
      PDE.partialDeriv i (fun z ↦ PDE.partialDeriv k χ z) y -
        if i = k then PDE.laplacian χ y else 0) x =
      PDE.partialDeriv i (fun y ↦ PDE.partialDeriv i (fun z ↦ PDE.partialDeriv k χ z) y) x -
        if i = k then PDE.partialDeriv i (fun y ↦ PDE.laplacian χ y) x else 0 := by
    intro i
    split_ifs with hik
    · exact PDE.partialDeriv_sub
        ((PDE.contDiff_top_partialDeriv (i := i)
          (PDE.contDiff_top_partialDeriv (i := k) hχ)).differentiable
          (by simp)).differentiableAt
        ((PDE.contDiff_laplacian_coord hχ).differentiable (by simp)).differentiableAt
    · simp
  simp_rw [hsub, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← PDE.laplacian_partialDeriv_eq hχ k x]
  simp [PDE.laplacian]

/-- Pairing a divergence-free `H¹` field with `curl curl (χ eₖ)` isolates `(Δ² - Δ) χ`
against the `k`-th component. -/
theorem inner_testFieldH1_curlCurlField (y : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)))
    (hy : divergenceCLM y = 0) {χ : ℝ^n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (k : Fin n) :
    inner ℝ y (testFieldH1 (curlCurlField χ k) (contDiff_curlCurlField hχ k)
      (hasCompactSupport_curlCurlField hc k)) =
      ∫ x, (wkpBaseCoordinateCLM (y k) : ℝ^n → ℝ) x *
        (PDE.laplacian (fun z ↦ PDE.laplacian χ z) x - PDE.laplacian χ x) := by
  rw [inner_testFieldH1]
  set Ψ : ℝ^n → ℝ := fun z ↦ PDE.partialDeriv k χ z -
    PDE.laplacian (fun w ↦ PDE.partialDeriv k χ w) z
  have hkχ : ContDiff ℝ ∞ (fun z ↦ PDE.partialDeriv k χ z) := PDE.contDiff_top_partialDeriv hχ
  have hΨ : ContDiff ℝ ∞ Ψ := hkχ.sub (PDE.contDiff_laplacian_coord hkχ)
  have hΨc : HasCompactSupport Ψ :=
    (hc.partialDeriv k).sub (hasCompactSupport_laplacian_coord (hc.partialDeriv k))
  set G : ℝ^n → ℝ := fun x ↦ PDE.laplacian χ x - PDE.laplacian (fun z ↦ PDE.laplacian χ z) x
  have hcomp : ∀ i : Fin n, ∀ x : ℝ^n, curlCurlField χ k x i -
      PDE.laplacian (fun z ↦ curlCurlField χ k z i) x =
      PDE.partialDeriv i Ψ x - if i = k then G x else 0 := by
    intro i x
    simp only [curlCurlField_apply]
    have h1 : ContDiff ℝ ∞ (fun z ↦ PDE.partialDeriv i (fun w ↦ PDE.partialDeriv k χ w) z) :=
      PDE.contDiff_top_partialDeriv hkχ
    have hΨi : PDE.partialDeriv i Ψ x =
        PDE.partialDeriv i (fun w ↦ PDE.partialDeriv k χ w) x -
          PDE.partialDeriv i (fun w ↦ PDE.laplacian (fun v ↦ PDE.partialDeriv k χ v) w) x :=
      PDE.partialDeriv_sub (hkχ.differentiable (by simp)).differentiableAt
        ((PDE.contDiff_laplacian_coord hkχ).differentiable (by simp)).differentiableAt
    rw [hΨi, ← PDE.laplacian_partialDeriv_eq hkχ i x]
    split_ifs with hik
    · rw [laplacian_sub_coord h1 (PDE.contDiff_laplacian_coord hχ)]
      simp only [G]
      ring
    · simp only [sub_zero]
  simp_rw [hcomp]
  have hint1 : ∀ i : Fin n, Integrable (fun x ↦ (wkpBaseCoordinateCLM (y i) : ℝ^n → ℝ) x *
      PDE.partialDeriv i Ψ x) volume := fun i ↦
    integrable_base_mul (y i) (PDE.contDiff_top_partialDeriv (i := i) hΨ).continuous
      (hΨc.partialDeriv i)
  have hGc : Continuous G :=
    (PDE.contDiff_laplacian_coord hχ).continuous.sub
      (PDE.contDiff_laplacian_coord (PDE.contDiff_laplacian_coord hχ)).continuous
  have hGs : HasCompactSupport G :=
    (hasCompactSupport_laplacian_coord hc).sub
      (hasCompactSupport_laplacian_coord (hasCompactSupport_laplacian_coord hc))
  have hint2 : ∀ i : Fin n, Integrable (fun x ↦ (wkpBaseCoordinateCLM (y i) : ℝ^n → ℝ) x *
      (if i = k then G x else 0)) volume := by
    intro i
    split_ifs
    · exact integrable_base_mul (y i) hGc hGs
    · simp
  simp only [mul_sub]
  rw [Finset.sum_congr rfl fun i _ ↦ integral_sub (hint1 i) (hint2 i), Finset.sum_sub_distrib,
    sum_integral_base_mul_partialDeriv_eq_zero y hy hΨ hΨc, zero_sub]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_eq_single k (fun i _ hik ↦ by simp [hik]) (by simp)]
  rw [← integral_neg]
  congr 1
  funext x
  simp only [G, ite_true]
  ring

/-- The `H¹` embedding of a divergence-free test field is divergence free. -/
theorem divergenceCLM_testFieldH1 {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hdiv : ∀ x, PDE.divergence φ x = 0) :
    divergenceCLM (testFieldH1 φ hφ hc) = 0 := by
  rw [divergenceCLM_apply]
  apply Lp.ext
  have hcoord : ∀ j : Fin n, ((wkpCoordinateCLM (singleDerivIndex n j) (testFieldH1 φ hφ hc j) :
      DerivLp n 2 univ) : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ PDE.partialDeriv j (fun z ↦ φ z j) x := by
    intro j
    have h := mkWkpSpaceOnOfContDiff_apply_ae (n := n) (k := 1) (p := 2) (Ω := univ)
      (fun x ↦ φ x j) (contDiff_component hφ j) (hasCompactSupport_component hc j)
      (singleDerivIndex n j)
    simpa [domainMeasure, iteratedPartialDeriv, wkpCoordinateCLM_apply, testFieldH1] using h
  have hsum := Lp.coeFn_finsetSum Finset.univ
    (fun j : Fin n ↦ wkpCoordinateCLM (singleDerivIndex n j) (testFieldH1 φ hφ hc j))
  have hall := ae_all_iff.mpr hcoord
  have hzero := Lp.coeFn_zero ℝ 2 (domainMeasure n univ)
  simp only [domainMeasure, Measure.restrict_univ] at hsum hzero ⊢
  filter_upwards [hsum, hall, hzero] with x h1 h2 h3
  rw [h1, h3, Finset.sum_apply]
  simp only [h2]
  exact hdiv x

/-- A divergence-free `H¹` field orthogonal to every solenoidal test field vanishes. -/
theorem eq_zero_of_inner_solenoidalTestFields (hn : 0 < n)
    (y : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) (hy : divergenceCLM y = 0)
    (horth : ∀ v ∈ solenoidalTestFields n, inner ℝ y v = 0) : y = 0 := by
  ext k : 1
  apply wkpBaseCoordinateCLM_injective (n := n) (p := 2) isOpen_univ
  rw [PiLp.zero_apply, map_zero]
  have hu : MemLp (wkpBaseCoordinateCLM (y k) : ℝ^n → ℝ) 2 volume := by
    simpa [domainMeasure] using Lp.memLp (wkpBaseCoordinateCLM (y k))
  have hzero := HeatEquation.WholeSpace.ae_eq_zero_of_integral_mul_biharmonic_sub_laplacian hn hu
    (fun χ hχ hc ↦ by
      have h := horth _ ⟨curlCurlField χ k, contDiff_curlCurlField hχ k,
        hasCompactSupport_curlCurlField hc k, divergence_curlCurlField hχ k, rfl⟩
      rw [inner_testFieldH1_curlCurlField y hy hχ hc k] at h
      rw [← h]
      apply integral_congr_ae
      filter_upwards with x
      have hΔ : (fun z ↦ PDE.laplacian χ z) = Δ χ := by
        funext z
        exact (hχ.contDiffAt.of_le (by simp)).coordinate_laplacian_eq_laplacian
      have hΔΔ : PDE.laplacian (Δ χ) x = Δ (Δ χ) x :=
        ((hχ.laplacian (by simp) : ContDiff ℝ ∞ (Δ χ)).contDiffAt.of_le
          (by simp)).coordinate_laplacian_eq_laplacian
      rw [hΔ, hΔΔ, show PDE.laplacian χ x = Δ χ x from congrFun hΔ x])
  apply Lp.ext
  have h0 := Lp.coeFn_zero ℝ 2 (domainMeasure n univ)
  simp only [domainMeasure, Measure.restrict_univ] at h0 ⊢
  filter_upwards [hzero, h0] with x h1 h2
  rw [h2]
  exact h1

/-- Smooth compactly supported divergence-free fields are dense in the divergence-free part
of whole-space `H¹`. -/
theorem mem_topologicalClosure_span_solenoidalTestFields (hn : 0 < n)
    (v : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) (hv : divergenceCLM v = 0) :
    v ∈ (Submodule.span ℝ (solenoidalTestFields n)).topologicalClosure := by
  set K := (Submodule.span ℝ (solenoidalTestFields n)).topologicalClosure
  have hSker : ∀ w ∈ solenoidalTestFields n, divergenceCLM w = 0 := by
    rintro _ ⟨φ, hφ, hc, hdiv, rfl⟩
    exact divergenceCLM_testFieldH1 hφ hc hdiv
  have hK : K ≤ LinearMap.ker (divergenceCLM (n := n)).toLinearMap :=
    Submodule.topologicalClosure_minimal _
      (Submodule.span_le.mpr fun w hw ↦ LinearMap.mem_ker.mpr (hSker w hw))
      (divergenceCLM (n := n)).isClosed_ker
  have : CompleteSpace K := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  set y := v - K.starProjection v
  have hyorth : y ∈ Kᗮ := K.sub_starProjection_mem_orthogonal v
  have hydiv : divergenceCLM y = 0 := by
    have hP : divergenceCLM (K.starProjection v) = 0 := hK (K.starProjection_apply_mem v)
    simp only [y, map_sub, hv, hP, sub_zero]
  have hy0 : y = 0 := eq_zero_of_inner_solenoidalTestFields hn y hydiv (fun w hw ↦ by
    have hwK : w ∈ K := Submodule.le_topologicalClosure _ (Submodule.subset_span hw)
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal K y).mp hyorth w hwK)
  have hv' : v = K.starProjection v := sub_eq_zero.mp hy0
  rw [hv']
  exact K.starProjection_apply_mem v

end NavierStokes.Stationary
