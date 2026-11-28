/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.Symmetry.SymmetricTests
public import PDE.Fluid.NavierStokes.Nonuniqueness.Symmetry.Sobolev
public import PDE.FDeriv.PartialDeriv.Support
public import PDE.FDeriv.Laplacian.Continuity
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The tested weak profile equation of a perturbed background

For a background field `B` in `L²_loc` and a test field `φ`, the weak profile density of
`B + V` splits pointwise into the density of `B`, the pairing of `V` with the formal adjoint
`profileAdjoint B φ = φ + ½ Dφ ξ - Δφ - (Dφ)ᵀ B - Dφ B` of the linearization at `B`, and the
quadratic flux `-V·(Dφ V)` (`weakProfileDensity_add`). For `V` the representative of a
whole-space `H¹` velocity the adjoint pairing is a continuous linear functional and the flux is
continuous under compact local observation (`integral_weakProfileDensity_add_representative`),
so the tested equation passes to weak limits of bounded families. The limits are taken in
`PDE.Fluid.NavierStokes.Nonuniqueness.ProfileWeakLimit`, over an exhausting family of balls and
against the even axisymmetric tests, and `WeakProfileEquation.of_symmetric_tests` extends the
limit equation from these tests to all tests.

## How it works

We follow the weak limit step of Hou, Wang and Yang, who pass to a weak limit of the ball solutions
in `H¹` and test with compactly supported divergence-free fields, using Rellich–Kondrachov on the
support of the test. For each test field the tested density of `B + R W` is the tested density of
`B`, plus the continuous linear functional of `W` given by `profileAdjointCoordinates`, plus the
tested flux of a cutoff observation of `W` (`integral_weakProfileDensity_add_representative`). The
cutoff observation `Stationary.cutoffValues ψ` is compact
(`Stationary.cutoffValues_isCompactOperator`) and the flux is continuous. A compactly supported
test field is eventually supported in `B(0, ρ i)` when `ρ i → ∞`
(`eventually_tsupport_subset_ball`).

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 4.3, the weak limit after
  (4.37), p. 31.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set Filter SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal RealInnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert
open scoped Topology Distributions

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

local notation "H" => PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))
local notation "M" => PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 2 univ)

/-! ### The adjoint of the linearization -/

/-- The formal adjoint of the linearization of the stationary operator at `B`, applied to a
test field: `φ + ½ Dφ(ξ) ξ - Δφ - (Dφ)ᵀ B - Dφ B`. -/
def profileAdjoint (B φ : ℝ^3 → ℝ^3) (x : ℝ^3) : ℝ^3 :=
  φ x + (1 / 2 : ℝ) • fderiv ℝ φ x x - PDE.laplacian φ x -
    WithLp.toLp 2 (fun i ↦ ⟪B x, PDE.partialDeriv i φ x⟫) -
      ∑ j, B x j • PDE.partialDeriv j φ x

/-- The weak profile density of `B + V` is that of `B`, plus the pairing of `V` with the
adjoint of the linearization at `B`, minus the quadratic flux `V·(Dφ V)`. -/
theorem weakProfileDensity_add (B V φ : ℝ^3 → ℝ^3) (x : ℝ^3) :
    weakProfileDensity (B + V) φ x = weakProfileDensity B φ x +
      ⟪V x, profileAdjoint B φ x⟫ - ⟪V x, fderiv ℝ φ x (V x)⟫ := by
  have h1 : ⟪B x, fderiv ℝ φ x (V x)⟫ =
      ⟪V x, WithLp.toLp 2 (fun i ↦ ⟪B x, PDE.partialDeriv i φ x⟫)⟫ := by
    rw [PDE.fderiv_apply_eq_sum_smul_partialDeriv, inner_sum, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [inner_smul_right, RCLike.inner_apply, conj_trivial, mul_comm]
  have h2 : fderiv ℝ φ x (B x) = ∑ j, B x j • PDE.partialDeriv j φ x :=
    PDE.fderiv_apply_eq_sum_smul_partialDeriv _ _ _
  simp only [weakProfileDensity, profileAdjoint, Pi.add_apply, map_add, inner_add_left,
    inner_add_right, inner_sub_right, inner_smul_right, h1, ← h2]
  ring

/-- The coordinates of `profileAdjoint B φ` for a smooth field `φ`. -/
theorem profileAdjoint_apply {B φ : ℝ^3 → ℝ^3} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : ℝ^3)
    (m : Fin 3) :
    profileAdjoint B φ x m = φ x m +
      (1 / 2 : ℝ) * ∑ i, x i * PDE.partialDeriv i (fun y ↦ φ y m) x -
      ∑ i, PDE.partialDeriv i (fun z ↦ PDE.partialDeriv i (fun y ↦ φ y m) z) x -
      ∑ k, B x k * PDE.partialDeriv m (fun y ↦ φ y k) x -
      ∑ i, B x i * PDE.partialDeriv i (fun y ↦ φ y m) x := by
  have hd (y : ℝ^3) : DifferentiableAt ℝ φ y := hφ.differentiable (by simp) y
  have hlap : PDE.laplacian φ x m =
      ∑ i, PDE.partialDeriv i (fun z ↦ PDE.partialDeriv i (fun y ↦ φ y m) z) x :=
    PDE.laplacian_apply_of_contDiff (hφ.of_le (by simp) : ContDiff ℝ 2 φ) x m
  have hDx : (fderiv ℝ φ x x) m = ∑ i, x i * PDE.partialDeriv i (fun y ↦ φ y m) x := by
    rw [PDE.fderiv_apply_eq_sum_smul_partialDeriv φ x x, WithLp.ofLp_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [PiLp.smul_apply, smul_eq_mul, PDE.partialDeriv_apply _ _ (hd x)]
  have hBD : (∑ j, B x j • PDE.partialDeriv j φ x) m =
      ∑ i, B x i * PDE.partialDeriv i (fun y ↦ φ y m) x := by
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [PiLp.smul_apply, smul_eq_mul, PDE.partialDeriv_apply _ _ (hd x)]
  have hBi : ⟪B x, PDE.partialDeriv m φ x⟫ =
      ∑ k, B x k * PDE.partialDeriv m (fun y ↦ φ y k) x := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [RCLike.inner_apply, conj_trivial, PDE.partialDeriv_apply _ _ (hd x), mul_comm]
  change (φ x + (1 / 2 : ℝ) • fderiv ℝ φ x x - PDE.laplacian φ x -
    WithLp.toLp 2 (fun i ↦ ⟪B x, PDE.partialDeriv i φ x⟫) -
      ∑ j, B x j • PDE.partialDeriv j φ x) m = _
  rw [PiLp.sub_apply, PiLp.sub_apply, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, hDx, hlap, hBD]
  simp only [hBi]

/-- A continuous compactly supported multiple of a field with locally integrable squared norm
is square integrable. -/
theorem memLp_two_smul_of_locallyIntegrable_sq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : ℝ^3 → E} {c : ℝ^3 → ℝ} (hg : AEStronglyMeasurable g volume)
    (hg2 : LocallyIntegrable (fun x ↦ ‖g x‖ ^ 2) volume) (hc : Continuous c)
    (hcc : HasCompactSupport c) : MemLp (fun x ↦ c x • g x) 2 volume := by
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcc
  have hK : IsCompact (tsupport c) := hcc
  have hgK : MemLp g 2 (volume.restrict (tsupport c)) :=
    (memLp_two_iff_integrable_sq_norm hg.restrict).mpr (hg2.integrableOn_isCompact hK)
  have hdom : MemLp (fun x ↦ C * ‖g x‖) 2 (volume.restrict (tsupport c)) :=
    hgK.norm.const_mul C
  have hcK : MemLp (fun x ↦ c x • g x) 2 (volume.restrict (tsupport c)) := by
    refine hdom.of_le (hc.aestronglyMeasurable.restrict.smul hg.restrict)
      (Eventually.of_forall fun x ↦ ?_)
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC x)
    rw [norm_smul, norm_mul, norm_norm, Real.norm_of_nonneg hC0]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
  rw [← memLp_indicator_iff_restrict hK.measurableSet.nullMeasurableSet] at hcK
  refine hcK.congr_norm (by
    exact (hc.aestronglyMeasurable.smul hg)) (Eventually.of_forall fun x ↦ ?_)
  by_cases hx : x ∈ tsupport c
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, zero_smul]

/-- A field bounded by a continuous compactly supported multiple of the norm of a field with
locally integrable squared norm is square integrable. -/
theorem memLp_two_of_norm_le_mul_norm {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {f : ℝ^3 → F} {g : ℝ^3 → E} {c : ℝ^3 → ℝ}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    (hg2 : LocallyIntegrable (fun x ↦ ‖g x‖ ^ 2) volume) (hc : Continuous c)
    (hcc : HasCompactSupport c) (hfg : ∀ x, ‖f x‖ ≤ c x * ‖g x‖) : MemLp f 2 volume := by
  have hn : LocallyIntegrable (fun x ↦ ‖(fun y ↦ ‖g y‖) x‖ ^ 2) volume := by
    simpa only [norm_norm] using hg2
  refine (memLp_two_smul_of_locallyIntegrable_sq hg.norm hn hc hcc).of_le hf
    (Eventually.of_forall fun x ↦ ?_)
  rw [smul_eq_mul, Real.norm_eq_abs]
  exact (hfg x).trans (le_abs_self _)

variable {B φ : ℝ^3 → ℝ^3}

/-- The partial derivatives of a smooth compactly supported field are continuous with compact
support. -/
private theorem partialDeriv_facts (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (i : Fin 3) : Continuous (PDE.partialDeriv i φ) ∧ HasCompactSupport (PDE.partialDeriv i φ) :=
  ⟨(hφ.partialDeriv i (k := 0)).continuous, hφc.partialDeriv i⟩

/-- The adjoint of the linearization at a background in `L²_loc`, applied to a smooth compactly
supported field, is square integrable. -/
theorem memLp_profileAdjoint (hBm : AEStronglyMeasurable B volume)
    (hB2 : LocallyIntegrable (fun x ↦ ‖B x‖ ^ 2) volume) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) : MemLp (profileAdjoint B φ) 2 volume := by
  have hD : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hDx : MemLp (fun x ↦ fderiv ℝ φ x x) 2 volume :=
    (hD.clm_apply continuous_id).memLp_of_hasCompactSupport
      ((hφc.fderiv (𝕜 := ℝ)).mono fun x hx h ↦ hx (by
        change fderiv ℝ φ x x = 0
        rw [h, zero_apply]))
  have hlap : MemLp (PDE.laplacian φ) 2 volume :=
    (hφ.of_le (by simp) : ContDiff ℝ 2 φ).continuous_coordinate_laplacian.memLp_of_hasCompactSupport
      hφc.coordinate_laplacian
  have hφ2 : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hφc
  have hadj : MemLp (fun x ↦ WithLp.toLp 2 (fun i ↦ ⟪B x, PDE.partialDeriv i φ x⟫) :
      ℝ^3 → ℝ^3) 2 volume := by
    refine memLp_piLp_iff.mpr fun i ↦ ?_
    obtain ⟨hci, hcci⟩ := partialDeriv_facts hφ hφc i
    refine memLp_two_of_norm_le_mul_norm (hBm.inner hci.aestronglyMeasurable) hBm hB2
      hci.norm hcci.norm fun x ↦ ?_
    rw [Real.norm_eq_abs, mul_comm]
    exact abs_real_inner_le_norm _ _
  have htr : MemLp (fun x ↦ ∑ j, B x j • PDE.partialDeriv j φ x) 2 volume := by
    refine memLp_finsetSum _ fun j _ ↦ ?_
    obtain ⟨hcj, hccj⟩ := partialDeriv_facts hφ hφc j
    have hBj : AEStronglyMeasurable (fun x ↦ B x j) volume :=
      (EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hBm
    refine memLp_two_of_norm_le_mul_norm (hBj.smul hcj.aestronglyMeasurable) hBm hB2 hcj.norm
      hccj.norm fun x ↦ ?_
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (B x) j) (norm_nonneg _)
  exact (((hφ2.add (hDx.const_smul (1 / 2 : ℝ))).sub hlap).sub hadj).sub htr

/-- The coordinates of `profileAdjoint B φ` as an element of the Hilbert product of scalar
whole-space `L²` spaces. -/
def profileAdjointCoordinates (hBm : AEStronglyMeasurable B volume)
    (hB2 : LocallyIntegrable (fun x ↦ ‖B x‖ ^ 2) volume) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) : M :=
  WithLp.toLp 2 fun i ↦ MemLp.toLp (fun x ↦ profileAdjoint B φ x i)
    (by simpa only [domainMeasure, Measure.restrict_univ] using
      (memLp_profileAdjoint hBm hB2 hφ hφc).eval_piLp i)

/-- The coordinates of `profileAdjointCoordinates` are those of `profileAdjoint B φ`. -/
theorem profileAdjointCoordinates_ae (hBm : AEStronglyMeasurable B volume)
    (hB2 : LocallyIntegrable (fun x ↦ ‖B x‖ ^ 2) volume) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (i : Fin 3) :
    (profileAdjointCoordinates hBm hB2 hφ hφc i : ℝ^3 → ℝ) =ᵐ[volume]
      fun x ↦ profileAdjoint B φ x i := by
  have h := MemLp.coeFn_toLp (μ := domainMeasure 3 univ)
    (f := fun x ↦ profileAdjoint B φ x i) (by simpa only [domainMeasure, Measure.restrict_univ]
      using (memLp_profileAdjoint hBm hB2 hφ hφc).eval_piLp i)
  simp only [domainMeasure, Measure.restrict_univ] at h
  exact h

/-- The pairing of the mass coordinates of a whole-space `H¹` velocity with the adjoint
coordinates is the integral of the pointwise pairing with `profileAdjoint B φ`. -/
theorem inner_massCLM_profileAdjointCoordinates (hBm : AEStronglyMeasurable B volume)
    (hB2 : LocallyIntegrable (fun x ↦ ‖B x‖ ^ 2) volume) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (W : H) :
    ⟪Stationary.massCLM W, profileAdjointCoordinates hBm hB2 hφ hφc⟫ =
      ∫ x, ⟪Stationary.representative W x, profileAdjoint B φ x⟫ := by
  have hg := memLp_profileAdjoint hBm hB2 hφ hφc
  have hV := Stationary.memLp_representative W
  have hint (i : Fin 3) : Integrable (fun x ↦ Stationary.representative W x i *
      profileAdjoint B φ x i) volume :=
    MemLp.integrable_mul (p := 2) (q := 2) (hV.eval_piLp i) (hg.eval_piLp i)
  rw [PiLp.inner_apply]
  simp_rw [PiLp.inner_apply (Stationary.representative W _)]
  rw [integral_finsetSum _ fun i _ ↦ (hint i).congr (Eventually.of_forall fun x ↦ by
    simp only [RCLike.inner_apply, conj_trivial, mul_comm])]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [L2.inner_def]
  simp only [domainMeasure, Measure.restrict_univ]
  refine integral_congr_ae ?_
  filter_upwards [profileAdjointCoordinates_ae hBm hB2 hφ hφc i] with x hx
  rw [hx, RCLike.inner_apply, RCLike.inner_apply, conj_trivial, conj_trivial]
  rfl

/-! ### Smooth tests as bounded Sobolev fields -/

/-- A component of a smooth compactly supported field, as a test function on the whole
space. -/
def testComponent (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) (i : Fin 3) :
    TestFunctionOn 3 univ :=
  ⟨_root_.TestFunction.mk (fun x ↦ φ x i)
    ((EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).contDiff.comp hφ)
    (hφc.comp_left (g := fun v : ℝ^3 ↦ v i) rfl) (subset_univ _), subset_univ _⟩

/-- The components of a smooth compactly supported field as `W^{1,∞}` functions. -/
def testFieldSobolev (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    Fin 3 → W^{1,∞}(ℝ^3) :=
  fun i ↦ testFunctionToWkp (k := 1) (p := ∞) (testComponent hφ hφc i)

/-- The weak gradient matrix of the `W^{1,∞}` realization is the classical one. -/
theorem testGradient_testFieldSobolev_ae (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (i j : Fin 3) :
    (Stationary.testGradient (testFieldSobolev hφ hφc) (i, j) : ℝ^3 → ℝ) =ᵐ[volume]
      fun x ↦ PDE.partialDeriv j (fun y ↦ φ y i) x := by
  have h := testFunctionToWkp_coordinate_ae (k := 1) (p := ∞) (testComponent hφ hφc i)
    (singleDerivIndex 3 j)
  simp only [domainMeasure, Measure.restrict_univ] at h
  filter_upwards [h] with x hx
  simp only [iteratedPartialDeriv, singleDerivIndex_toList] at hx
  exact hx

/-- The base values of the `W^{1,∞}` realization are the components of the field. -/
theorem base_testFieldSobolev_ae (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (i : Fin 3) :
    (wkpBaseCoordinateCLM (testFieldSobolev hφ hφc i) : ℝ^3 → ℝ) =ᵐ[volume] fun x ↦ φ x i := by
  have h := testFunctionToWkp_coordinate_ae (k := 1) (p := ∞) (testComponent hφ hφc i)
    (baseIndex 3 1)
  simp only [domainMeasure, Measure.restrict_univ] at h
  filter_upwards [h] with x hx
  simp only [iteratedPartialDeriv, baseIndex_toList] at hx
  exact hx

/-- A compactly supported field has a smooth compactly supported cutoff equal to one on its
support. -/
theorem exists_testCutoff (hφc : HasCompactSupport φ) :
    ∃ ψ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^3)), ℝ), ∀ x ∈ tsupport φ, ψ x = 1 := by
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_closedBall (0 : ℝ^3)
  let b : ContDiffBump (0 : ℝ^3) :=
    ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  refine ⟨_root_.TestFunction.mk b b.contDiff b.hasCompactSupport (subset_univ _),
    fun x hx ↦ ?_⟩
  exact b.one_of_mem_closedBall (Metric.closedBall_subset_closedBall
    (by simp only [b]; linarith [le_max_left R 0]) (hR hx))

/-- A cutoff equal to one on the support of `φ` equals one wherever the weak gradient of the
`W^{1,∞}` realization of `φ` is nonzero. -/
theorem testGradient_eq_zero_or_eq_one (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    {ψ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^3)), ℝ)} (hψ : ∀ x ∈ tsupport φ, ψ x = 1)
    (i j : Fin 3) : ∀ᵐ x ∂domainMeasure 3 univ,
      Stationary.testGradient (testFieldSobolev hφ hφc) (i, j) x = 0 ∨ ψ x = 1 := by
  simp only [domainMeasure, Measure.restrict_univ]
  filter_upwards [testGradient_testFieldSobolev_ae hφ hφc i j] with x hx
  by_cases hxs : x ∈ tsupport φ
  · exact Or.inr (hψ x hxs)
  · refine Or.inl ?_
    rw [hx]
    exact PDE.partialDeriv_eq_zero_of_notMem_tsupport j
      fun h ↦ hxs (tsupport_comp_subset (g := fun v : ℝ^3 ↦ v i) rfl φ h)

/-- The quadratic flux `V·(Dφ V)` of a square-integrable field against a smooth compactly
supported field, in coordinates. -/
theorem inner_fderiv_self_eq_sum (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (V : ℝ^3 → ℝ^3) (x : ℝ^3) :
    ⟪V x, fderiv ℝ φ x (V x)⟫ =
      ∑ i, ∑ j, V x i * V x j * PDE.partialDeriv j (fun y ↦ φ y i) x :=
  PDE.inner_fderiv_apply_eq_sum (hφ.differentiable (by simp) x) _ _

/-- The quadratic flux of a square-integrable field against a smooth compactly supported field
is integrable, and so is each of its coordinate terms. -/
theorem integrable_mul_mul_partialDeriv (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) {V : ℝ^3 → ℝ^3} (hV : MemLp V 2 volume) (i j : Fin 3) :
    Integrable (fun x ↦ V x i * V x j * PDE.partialDeriv j (fun y ↦ φ y i) x) volume := by
  have hc : Continuous (PDE.partialDeriv j (fun y ↦ φ y i)) :=
    (((EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).contDiff.comp hφ).partialDeriv j (k := 0)).continuous
  have hcc : HasCompactSupport (PDE.partialDeriv j (fun y ↦ φ y i)) :=
    (hφc.comp_left (g := fun v : ℝ^3 ↦ v i) rfl).partialDeriv j
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcc
  exact (MemLp.integrable_mul (p := 2) (q := 2) (hV.eval_piLp i) (hV.eval_piLp j)).mul_bdd
    hc.aestronglyMeasurable (Eventually.of_forall hC)

/-- The quadratic flux of a square-integrable field against a smooth compactly supported field
is integrable. -/
theorem integrable_inner_fderiv_self (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    {V : ℝ^3 → ℝ^3} (hV : MemLp V 2 volume) :
    Integrable (fun x ↦ ⟪V x, fderiv ℝ φ x (V x)⟫) volume := by
  simp_rw [inner_fderiv_self_eq_sum hφ]
  exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    integrable_mul_mul_partialDeriv hφ hφc hV i j

/-- The tested flux of the mass coordinates against the gradient of a smooth compactly
supported field is minus the integral of `V·(Dφ V)`, `V` the representative. -/
theorem testedFlux_testGradient_massCLM (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (W : H) :
    Stationary.testedFlux (Stationary.testGradient (testFieldSobolev hφ hφc))
        (Stationary.massCLM W) =
      -∫ x, ⟪Stationary.representative W x,
        fderiv ℝ φ x (Stationary.representative W x)⟫ := by
  have hV := Stationary.memLp_representative W
  rw [Stationary.testedFlux_eq_integrals]
  congr 1
  simp_rw [inner_fderiv_self_eq_sum hφ]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    integrable_mul_mul_partialDeriv hφ hφc hV i j]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum _ fun j _ ↦ integrable_mul_mul_partialDeriv hφ hφc hV i j]
  refine Finset.sum_congr rfl fun j _ ↦ integral_congr_ae ?_
  filter_upwards [testGradient_testFieldSobolev_ae hφ hφc i j] with x hx
  rw [hx]
  simp only [Stationary.representative_apply]
  ring

/-- The tested weak profile density of `B + V`, `V` the representative of a whole-space `H¹`
velocity, is the tested density of `B` plus a continuous linear functional of the mass
coordinates plus the quadratic flux of the mass coordinates. -/
theorem integral_weakProfileDensity_add_representative_eq (hBm : AEStronglyMeasurable B volume)
    (hB2 : LocallyIntegrable (fun x ↦ ‖B x‖ ^ 2) volume) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (W : H) :
    ∫ x, weakProfileDensity (B + Stationary.representative W) φ x =
      (∫ x, weakProfileDensity B φ x) +
        ⟪Stationary.massCLM W, profileAdjointCoordinates hBm hB2 hφ hφc⟫ +
        Stationary.testedFlux (Stationary.testGradient (testFieldSobolev hφ hφc))
          (Stationary.massCLM W) := by
  have hV := Stationary.memLp_representative W
  have hg := memLp_profileAdjoint hBm hB2 hφ hφc
  have hB : Integrable (weakProfileDensity B φ) volume := by
    have h := Symmetry.integrable_jetDensity (Symmetry.isLocallyIntegrableJet_profile hBm hB2)
      hφ hφc
    exact h.congr (Eventually.of_forall fun x ↦
      (Symmetry.weakProfileDensity_eq_jetDensity B φ x).symm)
  have hlin : Integrable (fun x ↦ ⟪Stationary.representative W x, profileAdjoint B φ x⟫)
      volume := by
    refine (L2.integrable_inner (hV.toLp _) (hg.toLp _)).congr ?_
    filter_upwards [hV.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [h1, h2]
  have hsplit : ∫ x, weakProfileDensity (B + Stationary.representative W) φ x =
      ∫ x, (weakProfileDensity B φ x + ⟪Stationary.representative W x, profileAdjoint B φ x⟫ -
        ⟪Stationary.representative W x, fderiv ℝ φ x (Stationary.representative W x)⟫) :=
    integral_congr_ae (Eventually.of_forall fun x ↦ weakProfileDensity_add _ _ _ x)
  rw [testedFlux_testGradient_massCLM hφ hφc W,
    inner_massCLM_profileAdjointCoordinates hBm hB2 hφ hφc W, hsplit]
  have h1 := integral_sub (hB.add hlin) (integrable_inner_fderiv_self hφ hφc hV)
  have h2 := integral_add hB hlin
  simp only [Pi.add_apply] at h1 h2
  rw [h1, h2, sub_eq_add_neg]

/-- `integral_weakProfileDensity_add_representative_eq` with the flux of a cutoff observation,
for a cutoff equal to one on the support of the test field. -/
theorem integral_weakProfileDensity_add_representative (hBm : AEStronglyMeasurable B volume)
    (hB2 : LocallyIntegrable (fun x ↦ ‖B x‖ ^ 2) volume) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) {ψ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^3)), ℝ)}
    (hψ : ∀ x ∈ tsupport φ, ψ x = 1) (W : H) :
    ∫ x, weakProfileDensity (B + Stationary.representative W) φ x =
      (∫ x, weakProfileDensity B φ x) +
        ⟪Stationary.massCLM W, profileAdjointCoordinates hBm hB2 hφ hφc⟫ +
        Stationary.testedFlux (Stationary.testGradient (testFieldSobolev hφ hφc))
          (Stationary.cutoffValues ψ W) := by
  rw [integral_weakProfileDensity_add_representative_eq hBm hB2 hφ hφc W]
  congr 1
  exact Stationary.testedFlux_eq_of_multiplier_eq _ _ _ fun i j k ↦
    Stationary.testGradient_mul_cutoffValues _ ψ (testGradient_eq_zero_or_eq_one hφ hφc hψ)
      W i j k

/-! ### Exhausting balls -/

/-- A compactly supported field is eventually supported in `B(0,ρ)` as `ρ → ∞`. -/
theorem eventually_tsupport_subset_ball {ι : Type*} {l : Filter ι} {ρ : ι → ℝ}
    (hρ : Tendsto ρ l atTop) (hφc : HasCompactSupport φ) :
    ∀ᶠ i in l, tsupport φ ⊆ Metric.ball 0 (ρ i) := by
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_ball (0 : ℝ^3)
  filter_upwards [hρ.eventually_ge_atTop R] with i hi
  exact hR.trans (Metric.ball_subset_ball hi)

end NavierStokes.Nonuniqueness
