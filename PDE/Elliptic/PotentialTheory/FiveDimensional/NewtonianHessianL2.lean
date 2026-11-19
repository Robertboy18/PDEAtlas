/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.HessianEnergy
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import PDE.Analysis.MeasureTheory.LpNorm
import PDE.Elliptic.PotentialTheory.FundamentalSolution.LocalIntegrability

/-!
# The Newtonian Hessian on ambient L²

The Hessian of the five-dimensional Newtonian potential extends uniquely from
smooth compact sources to bounded linear maps on all of `L²(ℝ⁵)`. Each component
has norm at most one. The sum of the squared norms of all twenty-five components
equals the squared source norm, and the four components mixing the axial and
transverse directions have combined norm at most half the source norm.

We first regard a test function and its Newtonian Hessian as L² elements.
The smooth-source energy identity bounds this linear map by the input L² norm.
Density and extension of a bounded linear map then construct the rough-source
Hessian. Continuity transfers the energy identity and the combined mixed bound.

For an L² source that vanishes almost everywhere outside a compact set, the
Newtonian potential belongs to L² and has this Hessian as its weak
second derivative. A fixed cutoff keeps smooth approximants in one compact set.
The support-dependent potential bound gives convergence of the potentials,
so their integration-by-parts identities pass to the limit against test functions.

The potential also has L² weak first derivatives. Integration by parts bounds
the squared first-derivative norm by the potential norm times the diagonal
Hessian norm. Applying this estimate to differences gives convergence of the
smooth gradients without a new assumption on the rough source.

For a compact C² source, finite convolution regularity makes the
potential C². Uniqueness of weak derivatives identifies its classical Hessian
with this same bounded operator, without additional source derivatives.

For a general L² source the potential need not lie in L², and the rough-source Hessian is
defined by extension of the bounded map rather than by principal values.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set
open scoped BigOperators Distributions ENNReal

namespace PotentialTheory

local notation "Test" => 𝓓((⊤ : TopologicalSpace.Opens (ℝ^5)), ℝ)
local notation "H" => Lp ℝ 2 (volume : Measure (ℝ^5))

/-- A compact smooth source determines an L² class without choosing a support radius. -/
private def compactSourceL2 : Test →ₗ[ℝ] H where
  toFun φ := (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).toLp φ
  map_add' φ ψ :=
    MemLp.toLp_add
      (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport)
      (ψ.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport)
  map_smul' c φ := by
    change ((c • φ).continuous.memLp_of_hasCompactSupport
        (c • φ).hasCompactSupport).toLp _ =
      c • (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).toLp _
    exact MemLp.toLp_const_smul c
      (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport)

/-- The L² class of a compact smooth source agrees with that source almost everywhere. -/
private theorem compactSourceL2_ae (φ : Test) :
    compactSourceL2 φ =ᵐ[volume] (φ : ℝ^5 → ℝ) :=
  MemLp.coeFn_toLp
    (φ.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) φ.hasCompactSupport)

/-- Smooth compact approximation gives density of the test-function classes. -/
private theorem compactSourceL2_dense : DenseRange compactSourceL2 := by
  have hd := Lp.dense_hasCompactSupport_contDiff
    (E := ℝ^5) (F := ℝ) (μ := volume) (p := 2) ENNReal.ofNat_ne_top
  apply hd.mono
  rintro f ⟨g, hfg, hgc, hgd⟩
  let φ : Test := ⟨g, hgd, hgc, subset_univ _⟩
  refine ⟨φ, Lp.ext ?_⟩
  exact (compactSourceL2_ae φ).trans hfg.symm

/-- One smooth cutoff keeps all approximants in a common compact set. It is one
on the source support and has values in `[0, 1]`, so it cannot increase the L² error.
The support condition is only almost everywhere; no particular measurable representative
of the source is required. -/
private theorem exists_compactSourceL2_tendsto_of_ae_compact_support
    {f : ℝ^5 → ℝ} {K : Set (ℝ^5)} (hf : MemLp f 2 volume) (hK : IsCompact K)
    (hf0 : ∀ᵐ X ∂volume, X ∉ K → f X = 0) :
    ∃ K' : Set (ℝ^5), IsCompact K' ∧ K ⊆ K' ∧ ∃ φ : ℕ → Test,
      (∀ m, tsupport (φ m) ⊆ K') ∧
      Filter.Tendsto (fun m ↦ compactSourceL2 (φ m)) Filter.atTop (nhds (hf.toLp f)) := by
  classical
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℝ^5)
  let η : ContDiffBump (0 : ℝ^5) := ⟨R, R + 1, hR, lt_add_one R⟩
  obtain ⟨v, hv, ht⟩ :=
    mem_closure_iff_seq_limit.mp (compactSourceL2_dense (hf.toLp f))
  choose g hg using hv
  have hgt : Filter.Tendsto (fun m ↦ compactSourceL2 (g m)) Filter.atTop
      (nhds (hf.toLp f)) := by
    simpa only [hg] using ht
  let φ (m : ℕ) : Test :=
    ⟨fun X ↦ η X * g m X, η.contDiff.mul (g m).contDiff,
      η.hasCompactSupport.mul_right, subset_univ _⟩
  have hfix : ∀ᵐ X ∂volume, η X * f X = f X := by
    filter_upwards [hf0] with X hX
    by_cases hx : X ∈ K
    · rw [η.one_of_mem_closedBall (hKR hx), one_mul]
    · rw [hX hx, mul_zero]
  have hbound (m : ℕ) :
      ‖compactSourceL2 (φ m) - hf.toLp f‖ ≤ ‖compactSourceL2 (g m) - hf.toLp f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_sub (compactSourceL2 (φ m)) (hf.toLp f),
      Lp.coeFn_sub (compactSourceL2 (g m)) (hf.toLp f),
      compactSourceL2_ae (φ m), compactSourceL2_ae (g m), hf.coeFn_toLp, hfix]
      with X hφsub hgsub hφ hgX hfX hfixX
    rw [hφsub, hgsub]
    change ‖compactSourceL2 (φ m) X - hf.toLp f X‖ ≤
      ‖compactSourceL2 (g m) X - hf.toLp f X‖
    rw [hφ, hgX, hfX]
    change ‖η X * g m X - f X‖ ≤ ‖g m X - f X‖
    calc _ = ‖η X‖ * ‖g m X - f X‖ := by rw [← norm_mul, mul_sub, hfixX]
      _ ≤ _ := mul_le_of_le_one_left (norm_nonneg _)
        (by rw [Real.norm_of_nonneg η.nonneg]; exact η.le_one)
  refine ⟨Metric.closedBall (0 : ℝ^5) (R + 1), isCompact_closedBall _ _, ?_, φ, ?_, ?_⟩
  · exact hKR.trans (Metric.closedBall_subset_closedBall η.rIn_lt_rOut.le)
  · intro m
    change tsupport (fun X ↦ η X * g m X) ⊆ Metric.closedBall (0 : ℝ^5) (R + 1)
    calc
      tsupport (fun X ↦ η X * g m X) ⊆ tsupport (η : ℝ^5 → ℝ) :=
        tsupport_mul_subset_left
      _ = Metric.closedBall (0 : ℝ^5) (R + 1) := η.tsupport_eq
  · exact tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ ↦ norm_nonneg _) hbound
      (tendsto_iff_norm_sub_tendsto_zero.1 hgt))

/-- The compact-source Newtonian convolution is smooth, although its support need not be compact. -/
private theorem compactPotential_smooth (φ : Test) :
    ContDiff ℝ (⊤ : ℕ∞)
      (convolution (fundamentalSolution 5) φ (ContinuousLinearMap.mul ℝ ℝ) volume) :=
  φ.hasCompactSupport.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (locallyIntegrable_fundamentalSolution 5) φ.contDiff

/-- The Hessian of a compact smooth source is square integrable. -/
private theorem compactHessian_memLp (i j : Fin 5) (φ : Test) :
    MemLp
      (fun X ↦ iteratedPartialDeriv [i, j]
        (convolution (fundamentalSolution 5) φ (ContinuousLinearMap.mul ℝ ℝ) volume) X)
      2 volume :=
  fundamentalSolution_five_convolution_iteratedPartialDeriv_memLp_two
    φ φ.contDiff φ.hasCompactSupport [i, j]

/-- Convolution and coordinate differentiation give additivity of the Hessian. -/
private theorem compactHessian_add (i j : Fin 5) (φ ψ : Test) :
    (fun X ↦ iteratedPartialDeriv [i, j]
      (convolution (fundamentalSolution 5) (φ + ψ : Test)
        (ContinuousLinearMap.mul ℝ ℝ) volume) X) =
      (fun X ↦ iteratedPartialDeriv [i, j]
        (convolution (fundamentalSolution 5) φ (ContinuousLinearMap.mul ℝ ℝ) volume) X) +
      (fun X ↦ iteratedPartialDeriv [i, j]
        (convolution (fundamentalSolution 5) ψ (ContinuousLinearMap.mul ℝ ℝ) volume) X) := by
  have hconv :
      convolution (fundamentalSolution 5) (φ + ψ : Test)
          (ContinuousLinearMap.mul ℝ ℝ) volume =
        convolution (fundamentalSolution 5) φ (ContinuousLinearMap.mul ℝ ℝ) volume +
          convolution (fundamentalSolution 5) ψ (ContinuousLinearMap.mul ℝ ℝ) volume :=
    (φ.hasCompactSupport.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      (locallyIntegrable_fundamentalSolution 5) φ.continuous).distrib_add
        (ψ.hasCompactSupport.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
          (locallyIntegrable_fundamentalSolution 5) ψ.continuous)
  rw [hconv]
  exact PDE.iteratedPartialDeriv_add_of_contDiff [i, j]
    ((compactPotential_smooth φ).of_le (WithTop.coe_le_coe.mpr le_top))
    ((compactPotential_smooth ψ).of_le (WithTop.coe_le_coe.mpr le_top))

/-- A constant scalar passes through the convolution and its Hessian. -/
private theorem compactHessian_smul (i j : Fin 5) (c : ℝ) (φ : Test) :
    (fun X ↦ iteratedPartialDeriv [i, j]
      (convolution (fundamentalSolution 5) (c • φ : Test)
        (ContinuousLinearMap.mul ℝ ℝ) volume) X) =
      c • (fun X ↦ iteratedPartialDeriv [i, j]
        (convolution (fundamentalSolution 5) φ (ContinuousLinearMap.mul ℝ ℝ) volume) X) := by
  have hconv :
      convolution (fundamentalSolution 5) (c • φ : Test)
          (ContinuousLinearMap.mul ℝ ℝ) volume =
        c • convolution (fundamentalSolution 5) φ (ContinuousLinearMap.mul ℝ ℝ) volume :=
    convolution_smul
  rw [hconv]
  exact PDE.iteratedPartialDeriv_const_smul c [i, j] _

/-- The classical Newtonian Hessian, viewed as a linear map from test functions into L². -/
private def compactHessianL2 (i j : Fin 5) : Test →ₗ[ℝ] H where
  toFun φ := (compactHessian_memLp i j φ).toLp _
  map_add' φ ψ := by
    calc
      (compactHessian_memLp i j (φ + ψ)).toLp _ =
          ((compactHessian_memLp i j φ).add (compactHessian_memLp i j ψ)).toLp _ :=
        MemLp.toLp_congr _ _
          (Filter.Eventually.of_forall (congrFun (compactHessian_add i j φ ψ)))
      _ = _ := MemLp.toLp_add _ _
  map_smul' c φ := by
    change (compactHessian_memLp i j (c • φ)).toLp _ =
      c • (compactHessian_memLp i j φ).toLp _
    calc
      (compactHessian_memLp i j (c • φ)).toLp _ =
          ((compactHessian_memLp i j φ).const_smul c).toLp _ :=
        MemLp.toLp_congr _ _
          (Filter.Eventually.of_forall (congrFun (compactHessian_smul i j c φ)))
      _ = _ := MemLp.toLp_const_smul c _

/-- The L² Hessian class retains the coordinate derivative as its representative. -/
private theorem compactHessianL2_ae (i j : Fin 5) (φ : Test) :
    compactHessianL2 i j φ =ᵐ[volume]
      fun X ↦ (∂[i] (∂[j]
        (convolution (fundamentalSolution 5) φ (ContinuousLinearMap.mul ℝ ℝ) volume))) X := by
  change (compactHessian_memLp i j φ).toLp _ =ᵐ[volume]
    (fun X ↦ iteratedPartialDeriv [i, j]
      (convolution (fundamentalSolution 5) φ (ContinuousLinearMap.mul ℝ ℝ) volume) X)
  exact (compactHessian_memLp i j φ).coeFn_toLp

/-- Passing to an L² class preserves the integral of a real square. -/
private theorem norm_toL2_sq (f : ℝ^5 → ℝ) (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖ ^ 2 = ∫ X, f X ^ 2 :=
  (Lp.norm_sq_eq_integral_sq _).trans
    (integral_congr_ae (hf.coeFn_toLp.fun_comp fun z : ℝ ↦ z ^ 2))

/-- The L² inner product of two classes is the integral of the product of any representatives. -/
private theorem inner_eq_integral_mul_of_ae {u v : H} {a b : ℝ^5 → ℝ}
    (hu : u =ᵐ[volume] a) (hv : v =ᵐ[volume] b) : inner ℝ u v = ∫ X, a X * b X := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu, hv] with X huX hvX
  simp only [Real.inner_apply, huX, hvX]

/-- The full smooth-source energy identity is an identity of L² norms. -/
private theorem compactHessianL2_energy (φ : Test) :
    (∑ i : Fin 5, ∑ j : Fin 5, ‖compactHessianL2 i j φ‖ ^ 2) =
      ‖compactSourceL2 φ‖ ^ 2 := by
  have hrow (i j : Fin 5) :
      ‖compactHessianL2 i j φ‖ ^ 2 =
        ∫ X, ((∂[i] (∂[j]
          (convolution (fundamentalSolution 5) φ (ContinuousLinearMap.mul ℝ ℝ) volume))) X) ^ 2 :=
    norm_toL2_sq _ (compactHessian_memLp i j φ)
  have hsource : ‖compactSourceL2 φ‖ ^ 2 = ∫ X, φ X ^ 2 :=
    norm_toL2_sq φ (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport)
  simp_rw [hrow, hsource]
  exact fundamentalSolution_five_convolution_hessian_energy
    φ φ.contDiff φ.hasCompactSupport

/-- Each nonnegative squared Hessian component is bounded by the full source energy. -/
private theorem compactHessianL2_bound (i j : Fin 5) (φ : Test) :
    ‖compactHessianL2 i j φ‖ ≤ ‖compactSourceL2 φ‖ := by
  have hrow : ‖compactHessianL2 i j φ‖ ^ 2 ≤
      ∑ k : Fin 5, ‖compactHessianL2 i k φ‖ ^ 2 :=
    Finset.single_le_sum (f := fun k : Fin 5 ↦ ‖compactHessianL2 i k φ‖ ^ 2)
      (fun k _ ↦ sq_nonneg ‖compactHessianL2 i k φ‖) (Finset.mem_univ j)
  have hfull : (∑ k : Fin 5, ‖compactHessianL2 i k φ‖ ^ 2) ≤
      ∑ l : Fin 5, ∑ k : Fin 5, ‖compactHessianL2 l k φ‖ ^ 2 :=
    Finset.single_le_sum
      (f := fun l : Fin 5 ↦ ∑ k : Fin 5, ‖compactHessianL2 l k φ‖ ^ 2)
      (fun l _ ↦ Finset.sum_nonneg fun k _ ↦ sq_nonneg ‖compactHessianL2 l k φ‖)
      (Finset.mem_univ i)
  have hsquare := (hrow.trans hfull).trans_eq (compactHessianL2_energy φ)
  nlinarith [norm_nonneg (compactHessianL2 i j φ), norm_nonneg (compactSourceL2 φ)]

/-- The four smooth axial mixed components satisfy the half-source bound in L². -/
private theorem compactHessianL2_mixed (φ : Test) :
    Real.sqrt (∑ i : Fin 4, ‖compactHessianL2 i.castSucc (Fin.last 4) φ‖ ^ 2) ≤
      (1 / 2 : ℝ) * ‖compactSourceL2 φ‖ := by
  have hrow (i : Fin 4) :
      ‖compactHessianL2 i.castSucc (Fin.last 4) φ‖ ^ 2 =
        ∫ X, ((∂[i.castSucc] (∂[(Fin.last 4)]
          (convolution (fundamentalSolution 5) φ (ContinuousLinearMap.mul ℝ ℝ) volume))) X) ^ 2 :=
    norm_toL2_sq _ (compactHessian_memLp i.castSucc (Fin.last 4) φ)
  have hsource : ‖compactSourceL2 φ‖ ^ 2 = ∫ X, φ X ^ 2 :=
    norm_toL2_sq φ (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport)
  simp_rw [hrow]
  have h := fundamentalSolution_five_convolution_axial_mixed_l2_le_half
    φ φ.contDiff φ.hasCompactSupport
  rwa [← hsource, Real.sqrt_sq (norm_nonneg _)] at h

/-- The bounded classical Hessian extends along the dense inclusion of test sources into L². -/
private def extendedHessianL2 (i j : Fin 5) : H →L[ℝ] H :=
  (compactHessianL2 i j).extendOfNorm compactSourceL2

/-- Density and the component bound make the extension agree exactly on test inputs. -/
private theorem extendedHessianL2_on_test (i j : Fin 5) (φ : Test) :
    extendedHessianL2 i j (compactSourceL2 φ) = compactHessianL2 i j φ := by
  apply LinearMap.extendOfNorm_eq compactSourceL2_dense
  exact ⟨1, fun ψ ↦ by simpa only [one_mul] using compactHessianL2_bound i j ψ⟩

/-- The operator bound follows from the classical energy estimate and dense extension. -/
private theorem extendedHessianL2_norm (i j : Fin 5) :
    ‖extendedHessianL2 i j‖ ≤ 1 := by
  apply LinearMap.opNorm_extendOfNorm_le compactSourceL2_dense zero_le_one
  intro φ
  simpa only [one_mul] using compactHessianL2_bound i j φ

/-- Finite sums of squared norms are continuous, so the full energy identity survives completion. -/
private theorem extendedHessianL2_energy (f : H) :
    (∑ i : Fin 5, ∑ j : Fin 5, ‖extendedHessianL2 i j f‖ ^ 2) = ‖f‖ ^ 2 := by
  refine compactSourceL2_dense.induction_on f ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro φ
    simp_rw [extendedHessianL2_on_test]
    exact compactHessianL2_energy φ

/-- The combined axial mixed bound is a closed inequality and passes to every L² source. -/
private theorem extendedHessianL2_mixed (f : H) :
    Real.sqrt (∑ i : Fin 4, ‖extendedHessianL2 i.castSucc (Fin.last 4) f‖ ^ 2) ≤
      (1 / 2 : ℝ) * ‖f‖ := by
  refine compactSourceL2_dense.induction_on f ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro φ
    simp_rw [extendedHessianL2_on_test]
    exact compactHessianL2_mixed φ

/-- There is a unique bounded linear Newtonian Hessian on all of `L²(ℝ⁵)` with
the classical action on smooth compact sources. Its full squared Hessian norm
equals the squared source norm. The four axial mixed components together have
norm at most half the source norm, and each individual component has operator
norm at most one. No symmetry or radial assumption is imposed on the source. -/
theorem exists_newtonianHessianL2 :
    ∃! T : Fin 5 → Fin 5 → H →L[ℝ] H,
      (∀ (f : ℝ^5 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
          (hfc : HasCompactSupport f) (i j : Fin 5),
        T i j ((hf.continuous.memLp_of_hasCompactSupport hfc).toLp f) =ᵐ[volume]
          fun X ↦ (∂[i] (∂[j]
            (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume))) X) ∧
      (∀ i j, ‖T i j‖ ≤ 1) ∧
      (∀ f : H, (∑ i : Fin 5, ∑ j : Fin 5, ‖T i j f‖ ^ 2) = ‖f‖ ^ 2) ∧
      (∀ f : H, Real.sqrt (∑ i : Fin 4, ‖T i.castSucc (Fin.last 4) f‖ ^ 2) ≤
        (1 / 2 : ℝ) * ‖f‖) := by
  refine ⟨extendedHessianL2, ?_, ?_⟩
  · refine ⟨?_, extendedHessianL2_norm, extendedHessianL2_energy,
      extendedHessianL2_mixed⟩
    intro f hf hfc i j
    let φ : Test := ⟨f, hf, hfc, subset_univ _⟩
    change extendedHessianL2 i j (compactSourceL2 φ) =ᵐ[volume] _
    rw [extendedHessianL2_on_test]
    exact compactHessianL2_ae i j φ
  · intro S hS
    funext i j
    apply ContinuousLinearMap.ext
    intro f
    refine compactSourceL2_dense.induction_on f ?_ ?_
    · exact isClosed_eq (S i j).continuous (extendedHessianL2 i j).continuous
    · intro φ
      rw [extendedHessianL2_on_test]
      apply Lp.ext
      exact (hS.1 φ φ.contDiff φ.hasCompactSupport i j).trans
        (compactHessianL2_ae i j φ).symm

/-- Absolute convergence allows subtraction inside the Newtonian integral.
Compact support supplies the integrability of both sources; the equality is only
almost everywhere, so exceptional values of the totalized integrals do not enter. -/
private theorem fundamentalSolution_five_convolution_sub_ae
    {f g : ℝ^5 → ℝ} {K : Set (ℝ^5)} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (hK : IsCompact K)
    (hf0 : ∀ᵐ X ∂volume, X ∉ K → f X = 0)
    (hg0 : ∀ᵐ X ∂volume, X ∉ K → g X = 0) :
    convolution (fundamentalSolution 5) (f - g) (ContinuousLinearMap.mul ℝ ℝ) volume =ᵐ[volume]
      convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume -
        convolution (fundamentalSolution 5) g (ContinuousLinearMap.mul ℝ ℝ) volume := by
  have hI (u : ℝ^5 → ℝ) (hu : MemLp u 2 volume)
      (hu0 : ∀ᵐ X ∂volume, X ∉ K → u X = 0) : Integrable u volume := by
    have hlocal : IntegrableOn u K volume :=
      (integrableOn_Lp_of_measure_ne_top (hu.toLp u)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hK.measure_lt_top.ne).congr
          (ae_restrict_of_ae hu.coeFn_toLp)
    exact hlocal.integrable_of_ae_notMem_eq_zero hu0
  filter_upwards
    [ae_convolutionExistsAt_fundamentalSolution_five_of_integrable (hI f hf hf0) hf,
      ae_convolutionExistsAt_fundamentalSolution_five_of_integrable (hI g hg hg0) hg]
    with X hXf hXg
  change (∫ Y, (fundamentalSolution 5) Y * (f (X - Y) - g (X - Y))) =
    (∫ Y, (fundamentalSolution 5) Y * f (X - Y)) -
      ∫ Y, (fundamentalSolution 5) Y * g (X - Y)
  simp_rw [mul_sub]
  exact integral_sub hXf hXg

/-- A common compact support turns L² convergence of sources into L² convergence
of their Newtonian potentials. The support-dependent bound applies to each
source difference, after absolute convergence has justified subtracting the integrals. -/
private theorem tendsto_newtonianPotential_toLp_of_common_compact_support
    {f : ℝ^5 → ℝ} {u : ℕ → ℝ^5 → ℝ} {K : Set (ℝ^5)}
    (hf : MemLp f 2 volume) (hu : ∀ m, MemLp (u m) 2 volume) (hK : IsCompact K)
    (hf0 : ∀ᵐ X ∂volume, X ∉ K → f X = 0)
    (hu0 : ∀ m, ∀ᵐ X ∂volume, X ∉ K → u m X = 0)
    (ht : Filter.Tendsto (fun m ↦ (hu m).toLp (u m)) Filter.atTop
      (nhds (hf.toLp f))) :
    Filter.Tendsto
      (fun m ↦ (memLp_fundamentalSolution_five_convolution_of_ae_compact_support
        (hu m) hK (hu0 m)).toLp
          (convolution (fundamentalSolution 5) (u m) (ContinuousLinearMap.mul ℝ ℝ) volume))
      Filter.atTop (nhds
        ((memLp_fundamentalSolution_five_convolution_of_ae_compact_support hf hK hf0).toLp
          (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume))) := by
  let P (g : ℝ^5 → ℝ) :=
    convolution (fundamentalSolution 5) g (ContinuousLinearMap.mul ℝ ℝ) volume
  have hpf : MemLp (P f) 2 volume :=
    memLp_fundamentalSolution_five_convolution_of_ae_compact_support hf hK hf0
  have hpu (m : ℕ) : MemLp (P (u m)) 2 volume :=
    memLp_fundamentalSolution_five_convolution_of_ae_compact_support (hu m) hK (hu0 m)
  obtain ⟨C, _hC, hCbound⟩ :=
    exists_norm_fundamentalSolution_five_convolution_le_of_ae_compact_support K hK
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ ↦ norm_nonneg _) (fun m ↦ ?_)
    (by simpa only [mul_zero] using (tendsto_iff_norm_sub_tendsto_zero.1 ht).const_mul C))
  have hd0 : ∀ᵐ X ∂volume, X ∉ K → (u m - f) X = 0 := by
    filter_upwards [hu0 m, hf0] with X hXu hXf hX
    simp [hXu hX, hXf hX]
  have h := hCbound (u m - f) ((hu m).sub hf) hd0
  rwa [MemLp.toLp_congr _ ((hpu m).sub hpf)
      (fundamentalSolution_five_convolution_sub_ae (hu m) hf hK (hu0 m) hf0),
    MemLp.toLp_sub, MemLp.toLp_sub] at h

/-- The bounded Newtonian Hessian agrees with the distributional Hessian of the
potential for every compactly supported L² source. Only its classical action
on smooth compact sources is required here; continuity transfers that identity through
a common-support approximation. The source need not be continuous or radial. -/
theorem hasWeakDerivativeOn_newtonianHessianL2_of_ae_compact_support
    (i j : Fin 5) (S : H →L[ℝ] H)
    (hS : ∀ (g : ℝ^5 → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g),
      S ((hg.continuous.memLp_of_hasCompactSupport hgc).toLp g) =ᵐ[volume]
        fun X ↦ (∂[i] (∂[j]
          (convolution (fundamentalSolution 5) g (ContinuousLinearMap.mul ℝ ℝ) volume))) X)
    {f : ℝ^5 → ℝ} {K : Set (ℝ^5)} (hf : MemLp f 2 volume) (hK : IsCompact K)
    (hf0 : ∀ᵐ X ∂volume, X ∉ K → f X = 0) :
    SobolevSpace.HasWeakDerivativeOn Set.univ [i, j]
      (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume)
      (fun X ↦ S (hf.toLp f) X) := by
  obtain ⟨K', hK', hKK', φ, hφsupport, hφt⟩ :=
    exists_compactSourceL2_tendsto_of_ae_compact_support hf hK hf0
  have hf0' : ∀ᵐ X ∂volume, X ∉ K' → f X = 0 := by
    filter_upwards [hf0] with X hX hX' using hX fun h ↦ hX' (hKK' h)
  have hφ (m : ℕ) : MemLp (φ m : ℝ^5 → ℝ) 2 volume :=
    (φ m).continuous.memLp_of_hasCompactSupport (φ m).hasCompactSupport
  have hφ0 (m : ℕ) : ∀ᵐ X ∂volume, X ∉ K' → φ m X = 0 :=
    .of_forall fun X hX ↦ image_eq_zero_of_notMem_tsupport fun hx ↦ hX (hφsupport m hx)
  let P (g : ℝ^5 → ℝ) :=
    convolution (fundamentalSolution 5) g (ContinuousLinearMap.mul ℝ ℝ) volume
  have hpf : MemLp (P f) 2 volume :=
    memLp_fundamentalSolution_five_convolution_of_ae_compact_support hf hK' hf0'
  have hpφ (m : ℕ) : MemLp (P (φ m)) 2 volume :=
    memLp_fundamentalSolution_five_convolution_of_ae_compact_support (hφ m) hK' (hφ0 m)
  refine ⟨(hpf.locallyIntegrable (by norm_num)).locallyIntegrableOn Set.univ,
    ((Lp.memLp (S (hf.toLp f))).locallyIntegrable (by norm_num)).locallyIntegrableOn
      Set.univ, fun θ _ ↦ ?_⟩
  let dθ : ℝ^5 → ℝ := iteratedPartialDeriv [i, j] θ.toFun
  have hdθ : MemLp dθ 2 volume :=
    (PDE.contDiff_top_iteratedPartialDeriv θ.contDiff [i, j]).continuous.memLp_of_hasCompactSupport
      (SobolevSpace.iteratedPartialDeriv_hasCompactSupport θ [i, j])
  have hm (m : ℕ) : inner ℝ ((hpφ m).toLp (P (φ m))) (hdθ.toLp dθ) =
      inner ℝ (S (compactSourceL2 (φ m))) (compactSourceL2 θ) := calc
    _ = ∫ X, P (φ m) X * dθ X := inner_eq_integral_mul_of_ae (hpφ m).coeFn_toLp hdθ.coeFn_toLp
    _ = ∫ X, iteratedPartialDeriv [i, j] (P (φ m)) X * θ X := by
      simpa [SobolevSpace.domainMeasure, dθ, P] using
        (SobolevSpace.GraphSpace.hasWeakDerivativeOn_iteratedPartialDeriv (Ω := Set.univ)
          (compactPotential_smooth (φ m)) [i, j]).integral_identity θ (subset_univ _)
    _ = _ := (inner_eq_integral_mul_of_ae (hS (φ m) (φ m).contDiff (φ m).hasCompactSupport)
      (compactSourceL2_ae θ)).symm
  have hlimit := tendsto_nhds_unique
    ((tendsto_newtonianPotential_toLp_of_common_compact_support hf hφ hK' hf0' hφ0 hφt).inner
      (tendsto_const_nhds (x := hdθ.toLp dθ)))
    ((((S.continuous.tendsto _).comp hφt).inner tendsto_const_nhds).congr fun m ↦ (hm m).symm)
  rw [inner_eq_integral_mul_of_ae hpf.coeFn_toLp hdθ.coeFn_toLp,
    inner_eq_integral_mul_of_ae (u := S (hf.toLp f)) .rfl (compactSourceL2_ae θ)] at hlimit
  simpa [SobolevSpace.domainMeasure, dθ, P] using hlimit

/-- Integration by parts controls a first derivative by the function and its
second derivative. The three L² assumptions make every product integrable, so
no boundary value at infinity is prescribed. -/
private theorem norm_partialDeriv_toLp_sq_le
    (i : Fin 5) {u : ℝ^5 → ℝ} (hu : ContDiff ℝ 2 u)
    (h0 : MemLp u 2 volume) (h1 : MemLp (∂[i] u) 2 volume)
    (h2 : MemLp (∂[i] (∂[i] u)) 2 volume) :
    ‖h1.toLp (∂[i] u)‖ ^ 2 ≤
      ‖h0.toLp u‖ * ‖h2.toLp (∂[i] (∂[i] u))‖ := by
  have hd : ContDiff ℝ 1 (∂[i] u) :=
    PDE.contDiff_partialDeriv_of_succ (m := 1) hu
  have hIBP : (∫ X, u X * (∂[i] (∂[i] u)) X) =
      - ∫ X, (∂[i] u) X * (∂[i] u) X :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (f := u) (g := ∂[i] u)
      (v := EuclideanSpace.single i (1 : ℝ))
      (memLp_one_iff_integrable.mp (h1.fun_mul h1))
      (memLp_one_iff_integrable.mp (h0.fun_mul h2))
      (memLp_one_iff_integrable.mp (h0.fun_mul h1))
      (fun X _ ↦ hu.differentiable (by norm_num) X)
      (fun X _ ↦ hd.differentiable (by norm_num) X)
  have hpair : inner ℝ (h0.toLp u) (h2.toLp (∂[i] (∂[i] u))) =
      - ‖h1.toLp (∂[i] u)‖ ^ 2 := by
    rw [norm_toL2_sq, inner_eq_integral_mul_of_ae h0.coeFn_toLp h2.coeFn_toLp, hIBP]
    simp only [pow_two]
  have h := abs_real_inner_le_norm (h0.toLp u)
    (h2.toLp (∂[i] (∂[i] u)))
  rwa [hpair, abs_neg, abs_of_nonneg (sq_nonneg _)] at h

/-- Apply the first-derivative estimate to a difference. This is the estimate
that makes the gradients Cauchy when the functions and diagonal Hessians converge. -/
private theorem norm_partialDeriv_sub_toLp_sq_le
    (i : Fin 5) {u v : ℝ^5 → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hu0 : MemLp u 2 volume) (hv0 : MemLp v 2 volume)
    (hu1 : MemLp (∂[i] u) 2 volume)
    (hv1 : MemLp (∂[i] v) 2 volume)
    (hu2 : MemLp (∂[i] (∂[i] u)) 2 volume)
    (hv2 : MemLp (∂[i] (∂[i] v)) 2 volume) :
    ‖hu1.toLp (∂[i] u) - hv1.toLp (∂[i] v)‖ ^ 2 ≤
      ‖hu0.toLp u - hv0.toLp v‖ *
        ‖hu2.toLp (∂[i] (∂[i] u)) -
          hv2.toLp (∂[i] (∂[i] v))‖ := by
  have hd1 : ∂[i] (u - v) = ∂[i] u - ∂[i] v := funext fun X ↦
    PDE.partialDeriv_sub (hu.differentiable (by norm_num) X) (hv.differentiable (by norm_num) X)
  have hd2 : ∂[i] (∂[i] (u - v)) = ∂[i] (∂[i] u) - ∂[i] (∂[i] v) := by
    rw [hd1]
    exact funext fun X ↦ PDE.partialDeriv_sub
      ((PDE.contDiff_partialDeriv_of_succ (m := 1) hu).differentiable (by norm_num) X)
      ((PDE.contDiff_partialDeriv_of_succ (m := 1) hv).differentiable (by norm_num) X)
  have h1 : MemLp (∂[i] (u - v)) 2 volume := hd1 ▸ hu1.sub hv1
  have h2 : MemLp (∂[i] (∂[i] (u - v))) 2 volume := hd2 ▸ hu2.sub hv2
  have h := norm_partialDeriv_toLp_sq_le i (hu.sub hv) (hu0.sub hv0) h1 h2
  change ‖h1.toLp (∂[i] (u - v))‖ ^ 2 ≤
    ‖(hu0.sub hv0).toLp (u - v)‖ * ‖h2.toLp (∂[i] (∂[i] (u - v)))‖ at h
  rwa [MemLp.toLp_congr h1 (hu1.sub hv1) (.of_forall (congrFun hd1)),
    MemLp.toLp_congr h2 (hu2.sub hv2) (.of_forall (congrFun hd2)), MemLp.toLp_sub,
    MemLp.toLp_sub, MemLp.toLp_sub] at h

/-- If squared distances are bounded by products of two Cauchy distances,
the middle sequence is Cauchy as well. This uses no compactness or subsequence. -/
private theorem cauchySeq_of_norm_sub_sq_le_product
    {a b c : ℕ → H} (ha : CauchySeq a) (hc : CauchySeq c)
    (hbound : ∀ m n, ‖b m - b n‖ ^ 2 ≤ ‖a m - a n‖ * ‖c m - c n‖) :
    CauchySeq b := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := Metric.cauchySeq_iff.mp ha ε hε
  obtain ⟨N₂, hN₂⟩ := Metric.cauchySeq_iff.mp hc ε hε
  refine ⟨max N₀ N₂, ?_⟩
  intro m hm n hn
  have h0 : ‖a m - a n‖ < ε := by
    simpa only [dist_eq_norm] using
      hN₀ m (le_trans (le_max_left _ _) hm) n (le_trans (le_max_left _ _) hn)
  have h2 : ‖c m - c n‖ < ε := by
    simpa only [dist_eq_norm] using
      hN₂ m (le_trans (le_max_right _ _) hm) n (le_trans (le_max_right _ _) hn)
  have hprod : ‖a m - a n‖ * ‖c m - c n‖ < ε * ε :=
    (mul_le_mul_of_nonneg_left h2.le (norm_nonneg _)).trans_lt
      (mul_lt_mul_of_pos_right h0 hε)
  rw [dist_eq_norm]
  have hb := hbound m n
  nlinarith [norm_nonneg (b m - b n)]

/-- The Newtonian potential of a compactly supported L² source has an
L² weak first derivative. Its squared norm is bounded by the potential norm times
the corresponding diagonal Hessian norm. Smooth approximants have Cauchy gradients
by integration by parts, so the weak identity passes to their L² limit.
The source need not be continuous or radial, and support is required only almost
everywhere. No point value of an L² class is evaluated on a lower-dimensional set. -/
theorem exists_weak_partialDeriv_newtonianPotential_of_ae_compact_support
    (i : Fin 5) (S : H →L[ℝ] H)
    (hS : ∀ (g : ℝ^5 → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g),
      S ((hg.continuous.memLp_of_hasCompactSupport hgc).toLp g) =ᵐ[volume]
        fun X ↦ (∂[i] (∂[i]
          (convolution (fundamentalSolution 5) g (ContinuousLinearMap.mul ℝ ℝ) volume))) X)
    {f : ℝ^5 → ℝ} {K : Set (ℝ^5)} (hf : MemLp f 2 volume) (hK : IsCompact K)
    (hf0 : ∀ᵐ X ∂volume, X ∉ K → f X = 0) :
    ∃ g : H, SobolevSpace.HasWeakDerivativeOn Set.univ [i]
        (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume)
        (fun X ↦ g X) ∧
      ‖g‖ ^ 2 ≤
        ‖(memLp_fundamentalSolution_five_convolution_of_ae_compact_support hf hK hf0).toLp
          (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume)‖ *
          ‖S (hf.toLp f)‖ := by
  obtain ⟨K', hK', hKK', φ, hφsupport, hφt⟩ :=
    exists_compactSourceL2_tendsto_of_ae_compact_support hf hK hf0
  have hf0' : ∀ᵐ X ∂volume, X ∉ K' → f X = 0 := by
    filter_upwards [hf0] with X hX hX' using hX fun h ↦ hX' (hKK' h)
  have hφ (m : ℕ) : MemLp (φ m : ℝ^5 → ℝ) 2 volume :=
    (φ m).continuous.memLp_of_hasCompactSupport (φ m).hasCompactSupport
  have hφ0 (m : ℕ) : ∀ᵐ X ∂volume, X ∉ K' → φ m X = 0 :=
    .of_forall fun X hX ↦ image_eq_zero_of_notMem_tsupport fun hx ↦ hX (hφsupport m hx)
  let P (u : ℝ^5 → ℝ) :=
    convolution (fundamentalSolution 5) u (ContinuousLinearMap.mul ℝ ℝ) volume
  have hpf : MemLp (P f) 2 volume :=
    memLp_fundamentalSolution_five_convolution_of_ae_compact_support hf hK hf0
  have h0 (m : ℕ) : MemLp (P (φ m)) 2 volume :=
    memLp_fundamentalSolution_five_convolution_of_ae_compact_support (hφ m) hK' (hφ0 m)
  have h1 (m : ℕ) : MemLp (∂[i] (P (φ m))) 2 volume :=
    fundamentalSolution_five_convolution_iteratedPartialDeriv_memLp_two
      (φ m) (φ m).contDiff (φ m).hasCompactSupport [i]
  have h2 (m : ℕ) : MemLp (∂[i] (∂[i] (P (φ m)))) 2 volume := compactHessian_memLp i i (φ m)
  have hC2 (m : ℕ) : ContDiff ℝ 2 (P (φ m)) :=
    (compactPotential_smooth (φ m)).of_le (WithTop.coe_le_coe.mpr le_top)
  let U (m : ℕ) : H := (h0 m).toLp (P (φ m))
  let G (m : ℕ) : H := (h1 m).toLp (∂[i] (P (φ m)))
  let Q (m : ℕ) : H := (h2 m).toLp (∂[i] (∂[i] (P (φ m))))
  have hUt : Filter.Tendsto U Filter.atTop (nhds (hpf.toLp (P f))) :=
    tendsto_newtonianPotential_toLp_of_common_compact_support hf hφ hK' hf0' hφ0 hφt
  have hQt : Filter.Tendsto Q Filter.atTop (nhds (S (hf.toLp f))) :=
    ((S.continuous.tendsto _).comp hφt).congr fun m ↦ Lp.ext ((hS (φ m) (φ m).contDiff
      (φ m).hasCompactSupport).trans (h2 m).coeFn_toLp.symm)
  obtain ⟨g, hgt⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_norm_sub_sq_le_product hUt.cauchySeq hQt.cauchySeq fun m n ↦
      norm_partialDeriv_sub_toLp_sq_le i (hC2 m) (hC2 n) (h0 m) (h0 n) (h1 m) (h1 n) (h2 m) (h2 n))
  refine ⟨g, ⟨(hpf.locallyIntegrable (by norm_num)).locallyIntegrableOn Set.univ,
    ((Lp.memLp g).locallyIntegrable (by norm_num)).locallyIntegrableOn Set.univ, fun θ _ ↦ ?_⟩,
    le_of_tendsto_of_tendsto (hgt.norm.pow 2) (hUt.norm.mul hQt.norm) (.of_forall fun m ↦
      norm_partialDeriv_toLp_sq_le i (hC2 m) (h0 m) (h1 m) (h2 m))⟩
  let dθ : ℝ^5 → ℝ := iteratedPartialDeriv [i] θ.toFun
  have hdθ : MemLp dθ 2 volume :=
    (PDE.contDiff_top_iteratedPartialDeriv θ.contDiff [i]).continuous.memLp_of_hasCompactSupport
      (SobolevSpace.iteratedPartialDeriv_hasCompactSupport θ [i])
  have hm (m : ℕ) : inner ℝ (U m) (hdθ.toLp dθ) = - inner ℝ (G m) (compactSourceL2 θ) := calc
    _ = ∫ X, P (φ m) X * dθ X := inner_eq_integral_mul_of_ae (h0 m).coeFn_toLp hdθ.coeFn_toLp
    _ = - ∫ X, (∂[i] (P (φ m))) X * θ X := by
      simpa [SobolevSpace.domainMeasure, dθ, P, iteratedPartialDeriv] using
        (SobolevSpace.GraphSpace.hasWeakDerivativeOn_iteratedPartialDeriv (Ω := Set.univ)
          (compactPotential_smooth (φ m)) [i]).integral_identity θ (subset_univ _)
    _ = _ := congrArg Neg.neg
      (inner_eq_integral_mul_of_ae (h1 m).coeFn_toLp (compactSourceL2_ae θ)).symm
  have hlimit := tendsto_nhds_unique (hUt.inner tendsto_const_nhds)
    ((hgt.inner tendsto_const_nhds).neg.congr fun m ↦ (hm m).symm)
  rw [inner_eq_integral_mul_of_ae hpf.coeFn_toLp hdθ.coeFn_toLp,
    inner_eq_integral_mul_of_ae (u := g) .rfl (compactSourceL2_ae θ)] at hlimit
  simpa [SobolevSpace.domainMeasure, dθ, P] using hlimit

/-- The bounded Newtonian Hessian agrees with the Hessian of a compact
C² source. Finite regularity passes through convolution. Its classical Hessian
and the extended operator are then weak derivatives of the same potential,
so uniqueness identifies them almost everywhere. No principal-value limit or
integrability of the classical Hessian is assumed. -/
theorem newtonianHessianL2_apply_ae_eq_of_contDiff_two
    (i j : Fin 5) (S : H →L[ℝ] H)
    (hS : ∀ (g : ℝ^5 → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g),
      S ((hg.continuous.memLp_of_hasCompactSupport hgc).toLp g) =ᵐ[volume]
        fun X ↦ (∂[i] (∂[j]
          (convolution (fundamentalSolution 5) g (ContinuousLinearMap.mul ℝ ℝ) volume))) X)
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    S ((hf.continuous.memLp_of_hasCompactSupport hfc).toLp f) =ᵐ[volume]
      fun X ↦ (∂[i] (∂[j]
        (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume))) X := by
  have hP : ContDiff ℝ 2
      (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume) :=
    hfc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      (locallyIntegrable_fundamentalSolution 5) hf
  have hf0 : ∀ᵐ X ∂volume, X ∉ tsupport f → f X = 0 := by
    filter_upwards [] with X hX
    exact image_eq_zero_of_notMem_tsupport hX
  have hweak := hasWeakDerivativeOn_newtonianHessianL2_of_ae_compact_support
    i j S hS (K := tsupport f)
    (hf.continuous.memLp_of_hasCompactSupport hfc) hfc hf0
  have hclassical := SobolevSpace.GraphSpace.hasWeakDerivativeOn_iteratedPartialDeriv_finite
    (Ω := Set.univ) [i, j] (by simpa using hP)
  simpa only [SobolevSpace.domainMeasure, Measure.restrict_univ, iteratedPartialDeriv] using
    SobolevSpace.HasWeakDerivativeOn.unique_ae isOpen_univ hweak hclassical

/-- The same unique L² Newtonian Hessian has its classical action on every
compact C² source. The component bound, full energy identity, and combined
axial mixed bound are inherited from the bounded extension. -/
theorem exists_newtonianHessianL2_of_contDiff_two :
    ∃! T : Fin 5 → Fin 5 → H →L[ℝ] H,
      (∀ (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 2 f)
          (hfc : HasCompactSupport f) (i j : Fin 5),
        T i j ((hf.continuous.memLp_of_hasCompactSupport hfc).toLp f) =ᵐ[volume]
          fun X ↦ (∂[i] (∂[j]
            (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume))) X) ∧
      (∀ i j, ‖T i j‖ ≤ 1) ∧
      (∀ f : H, (∑ i : Fin 5, ∑ j : Fin 5, ‖T i j f‖ ^ 2) = ‖f‖ ^ 2) ∧
      (∀ f : H, Real.sqrt (∑ i : Fin 4, ‖T i.castSucc (Fin.last 4) f‖ ^ 2) ≤
        (1 / 2 : ℝ) * ‖f‖) := by
  obtain ⟨T, hT, hunique⟩ := exists_newtonianHessianL2
  refine ⟨T, ⟨?_, hT.2⟩, ?_⟩
  · intro f hf hfc i j
    exact newtonianHessianL2_apply_ae_eq_of_contDiff_two i j (T i j)
      (fun g hg hgc ↦ hT.1 g hg hgc i j) f hf hfc
  · intro S hS
    apply hunique S
    refine ⟨?_, hS.2⟩
    intro f hf hfc i j
    exact hS.1 f (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hfc i j

/-- The Hessian of a compact C² Newtonian source belongs to L².
Membership follows from agreement with the bounded weak operator, without
requiring additional derivatives of the source or a separate decay estimate. -/
theorem fundamentalSolution_five_convolution_hessian_memLp_of_contDiff_two
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (i j : Fin 5) :
    MemLp (fun X ↦ (∂[i] (∂[j]
      (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume))) X)
      2 volume := by
  obtain ⟨T, hT, _⟩ := exists_newtonianHessianL2_of_contDiff_two
  exact (memLp_congr_ae (hT.1 f hf hfc i j)).mp
    (Lp.memLp (T i j ((hf.continuous.memLp_of_hasCompactSupport hfc).toLp f)))


end PotentialTheory
