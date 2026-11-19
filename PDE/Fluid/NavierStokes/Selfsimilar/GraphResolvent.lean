/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Selfsimilar.GraphSolution
public import PDE.Analysis.Integration.CompactByPartsCoordinates

/-!
# The shifted linearization at a divergence-free coefficient with bounded gradient

Let `U` be a smooth divergence-free field on `ℝⁿ` with `‖DU(x)‖ ≤ M` for all `x`, and `b` the
`L∞` class of `U`. On divergence-free test fields `φ` the convection terms of the weak
linearization integrate by parts to `∫ ⟪DU(x) φ(x), φ(x)⟫` (`convectionForm_testFieldH1_self`),
so

`⟨(L_b + μ J) φ, φ⟩ = ‖∇φ‖² + (μ + n/4 - 1/2) ‖φ‖² + ∫ ⟪DU φ, φ⟫
  ≥ ‖∇φ‖² + (μ + n/4 - 1/2 - M) ‖φ‖²`.

For `μ > M + 1/2 - n/4` the shifted linearization is therefore coercive on every
dilation-invariant space of divergence-free test fields, and `existsUnique_graph_resolvent`
solves `L_b h + μ J h = f` uniquely in the graph domain for every `f ∈ E*`, with
`‖h‖ ≤ κ⁻¹ ‖f‖`, `κ = min 1 (μ + n/4 - 1/2 - M)`. In three dimensions the condition is
`μ > M - 1/4`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal NNReal Sobolev ContDiff SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Selfsimilar

open Stationary
open PDE.Analysis.Evolution (restrictForm restrictForm_apply)

variable {n : ℕ}

local notation "H" => PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))

section Convection

variable {U : ℝ^n → ℝ^n} (hU : ContDiff ℝ ∞ U) (hdivU : ∀ x, PDE.divergence U x = 0)
  {b : Fin n → DerivLp n ∞ univ} (hb : ∀ i, (b i : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ U x i)
  {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hdivφ : ∀ x, PDE.divergence φ x = 0)

include hU hdivU hb hdivφ in
/-- On a divergence-free test field the convection terms of the weak linearization at a smooth
divergence-free coefficient are `∫ ⟪DU φ, φ⟫ = ∫ Σᵢⱼ φⱼ ∂ⱼUᵢ φᵢ`. -/
theorem convectionForm_testFieldH1_self :
    convectionForm b (testFieldH1 φ hφ hc) (testFieldH1 φ hφ hc) =
      ∑ i, ∫ x, (∑ j, φ x j * PDE.partialDeriv j (fun y ↦ U y i) x) * φ x i := by
  have hUi : ∀ i : Fin n, ContDiff ℝ ∞ (fun x ↦ U x i) := contDiff_component hU
  have hφi : ∀ i : Fin n, ContDiff ℝ ∞ (fun x ↦ φ x i) := contDiff_component hφ
  have hφc : ∀ i : Fin n, HasCompactSupport (fun x ↦ φ x i) := hasCompactSupport_component hc
  have hdφ : ∀ i j : Fin n, ContDiff ℝ ∞ (fun x ↦ PDE.partialDeriv j (fun y ↦ φ y i) x) :=
    fun i j ↦ PDE.contDiff_top_partialDeriv (hφi i)
  have hmul : ∀ (j : Fin n) (u : DerivLp n 2 univ),
      (mulLpLeft (b j) u : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ U x j * (u : ℝ^n → ℝ) x := by
    intro j u
    have h := mulLpLeft_apply_ae (b j) u
    simp only [domainMeasure, Measure.restrict_univ] at h
    filter_upwards [h, hb j] with x h1 h2
    rw [h1, h2]
  -- the three kinds of terms as integrals
  have t1 : ∀ i j, inner ℝ (mulLpLeft (b j)
      (wkpCoordinateCLM (singleDerivIndex n j) (testFieldH1 φ hφ hc i)))
      (wkpBaseCoordinateCLM (testFieldH1 φ hφ hc i)) =
        ∫ x, U x j * PDE.partialDeriv j (fun y ↦ φ y i) x * φ x i := by
    intro i j
    refine inner_eq_integral_mul_of_ae ((hmul j _).trans ?_) (testFieldH1_base_ae hφ hc i)
    filter_upwards [testFieldH1_partial_ae hφ hc i j] with x hx
    rw [hx]
  have t2 : ∀ i j, inner ℝ (mulLpLeft (b i)
      (wkpCoordinateCLM (singleDerivIndex n j) (testFieldH1 φ hφ hc j)))
      (wkpBaseCoordinateCLM (testFieldH1 φ hφ hc i)) =
        ∫ x, U x i * PDE.partialDeriv j (fun y ↦ φ y j) x * φ x i := by
    intro i j
    refine inner_eq_integral_mul_of_ae ((hmul i _).trans ?_) (testFieldH1_base_ae hφ hc i)
    filter_upwards [testFieldH1_partial_ae hφ hc j j] with x hx
    rw [hx]
  have t3 : ∀ i j, inner ℝ (mulLpLeft (b i) (wkpBaseCoordinateCLM (testFieldH1 φ hφ hc j)))
      (wkpCoordinateCLM (singleDerivIndex n j) (testFieldH1 φ hφ hc i)) =
        ∫ x, U x i * φ x j * PDE.partialDeriv j (fun y ↦ φ y i) x := by
    intro i j
    refine inner_eq_integral_mul_of_ae ((hmul i _).trans ?_) (testFieldH1_partial_ae hφ hc i j)
    filter_upwards [testFieldH1_base_ae hφ hc j] with x hx
    rw [hx]
  -- transport of each component by `U` has no energy
  have s1 : ∀ i, ∑ j, ∫ x, U x j * PDE.partialDeriv j (fun y ↦ φ y i) x * φ x i = 0 := by
    intro i
    have e := sum_integral_mul_mul_partialDeriv_eq_neg (hφi i) hU hdivU (hφi i) (hφc i)
    have hint : ∀ j : Fin n, Integrable (fun x ↦ U x j * PDE.partialDeriv j (fun y ↦ φ y i) x *
        φ x i) volume := fun j ↦
      integrable_mul_of_hasCompactSupport_right ((hUi j).continuous.mul (hdφ i j).continuous)
        (hφi i).continuous (hφc i)
    have hsum : ∫ x, (∑ j, U x j * PDE.partialDeriv j (fun y ↦ φ y i) x) * φ x i =
        ∑ j, ∫ x, U x j * PDE.partialDeriv j (fun y ↦ φ y i) x * φ x i := by
      rw [← integral_finsetSum _ fun j _ ↦ hint j]
      congr 1
      funext x
      rw [Finset.sum_mul]
    have hleft : ∑ j, ∫ x, φ x i * U x j * PDE.partialDeriv j (fun y ↦ φ y i) x =
        ∑ j, ∫ x, U x j * PDE.partialDeriv j (fun y ↦ φ y i) x * φ x i := by
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      congr 1
      funext x
      ring
    rw [hleft, hsum] at e
    linarith
  -- the divergence of the test field vanishes
  have s2 : ∀ i, ∑ j, ∫ x, U x i * PDE.partialDeriv j (fun y ↦ φ y j) x * φ x i = 0 := by
    intro i
    have hint : ∀ j : Fin n, Integrable (fun x ↦ U x i * PDE.partialDeriv j (fun y ↦ φ y j) x *
        φ x i) volume := fun j ↦
      integrable_mul_of_hasCompactSupport_right ((hUi i).continuous.mul (hdφ j j).continuous)
        (hφi i).continuous (hφc i)
    rw [← integral_finsetSum _ fun j _ ↦ hint j]
    have hzero : (fun x ↦ ∑ j, U x i * PDE.partialDeriv j (fun y ↦ φ y j) x * φ x i) =
        fun _ ↦ 0 := by
      funext x
      have hx := hdivφ x
      simp only [PDE.divergence] at hx
      rw [← Finset.sum_mul, ← Finset.mul_sum, hx, mul_zero, zero_mul]
    rw [hzero, integral_zero]
  -- the stretching term
  have s3 : ∀ i, ∑ j, ∫ x, U x i * φ x j * PDE.partialDeriv j (fun y ↦ φ y i) x =
      -∫ x, (∑ j, φ x j * PDE.partialDeriv j (fun y ↦ U y i) x) * φ x i :=
    fun i ↦ sum_integral_mul_mul_partialDeriv_eq_neg (hUi i) hφ hdivφ (hφi i) (hφc i)
  rw [convectionForm_apply]
  simp only [t1, t2, t3, Finset.sum_sub_distrib, s1, s2, s3]
  simp

end Convection

section Resolvent

/-- The stretching energy `∫ ⟪DU φ, φ⟫` is at least `-M ∫ |φ|²` when `‖DU‖ ≤ M`. -/
theorem neg_mul_le_integral_stretching {U : ℝ^n → ℝ^n} (hU : ContDiff ℝ ∞ U) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ U x‖ ≤ M) {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    -M * ∑ i, ∫ x, φ x i * φ x i ≤
      ∑ i, ∫ x, (∑ j, φ x j * PDE.partialDeriv j (fun y ↦ U y i) x) * φ x i := by
  have hUi : ∀ i : Fin n, ContDiff ℝ ∞ (fun x ↦ U x i) := contDiff_component hU
  have hφi : ∀ i : Fin n, ContDiff ℝ ∞ (fun x ↦ φ x i) := contDiff_component hφ
  have hφc : ∀ i : Fin n, HasCompactSupport (fun x ↦ φ x i) := hasCompactSupport_component hc
  have hint1 : ∀ i : Fin n, Integrable (fun x ↦ φ x i * φ x i) volume := fun i ↦
    integrable_mul_of_hasCompactSupport_left (hφi i).continuous (hφi i).continuous (hφc i)
  have hint2 : ∀ i : Fin n, Integrable (fun x ↦
      (∑ j, φ x j * PDE.partialDeriv j (fun y ↦ U y i) x) * φ x i) volume := fun i ↦
    integrable_mul_of_hasCompactSupport_right
      (continuous_finsetSum _ fun j _ ↦ (hφi j).continuous.mul
        (PDE.contDiff_top_partialDeriv (hUi i)).continuous) (hφi i).continuous (hφc i)
  have hpt : ∀ x, -M * ∑ i, φ x i * φ x i ≤
      ∑ i, (∑ j, φ x j * PDE.partialDeriv j (fun y ↦ U y i) x) * φ x i := by
    intro x
    have hdiff : DifferentiableAt ℝ U x := hU.differentiable (by simp) x
    have h1 : ∑ i, (∑ j, φ x j * PDE.partialDeriv j (fun y ↦ U y i) x) * φ x i =
        inner ℝ (fderiv ℝ U x (φ x)) (φ x) := by
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [fderiv_apply_component hdiff, RCLike.inner_apply, conj_trivial, mul_comm]
    have h2 : ∑ i, φ x i * φ x i = ‖φ x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [RCLike.inner_apply, conj_trivial]
    have h3 : |inner ℝ (fderiv ℝ U x (φ x)) (φ x)| ≤ M * ‖φ x‖ ^ 2 := by
      calc |inner ℝ (fderiv ℝ U x (φ x)) (φ x)| ≤ ‖fderiv ℝ U x (φ x)‖ * ‖φ x‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ ‖fderiv ℝ U x‖ * ‖φ x‖ * ‖φ x‖ := by
            gcongr
            exact (fderiv ℝ U x).le_opNorm _
        _ ≤ M * ‖φ x‖ * ‖φ x‖ := by gcongr; exact hM x
        _ = M * ‖φ x‖ ^ 2 := by ring
    rw [h1, h2]
    linarith [neg_abs_le (inner ℝ (fderiv ℝ U x (φ x)) (φ x))]
  rw [Finset.mul_sum]
  have hsum1 : ∑ i, -M * ∫ x, φ x i * φ x i = ∫ x, -M * ∑ i, φ x i * φ x i := by
    rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ hint1 i, Finset.mul_sum]
  have hsum2 : ∑ i, ∫ x, (∑ j, φ x j * PDE.partialDeriv j (fun y ↦ U y i) x) * φ x i =
      ∫ x, ∑ i, (∑ j, φ x j * PDE.partialDeriv j (fun y ↦ U y i) x) * φ x i :=
    (integral_finsetSum _ fun i _ ↦ hint2 i).symm
  rw [hsum1, hsum2]
  exact integral_mono ((integrable_finsetSum _ fun i _ ↦ hint1 i).const_mul _)
    (integrable_finsetSum _ fun i _ ↦ hint2 i) hpt

namespace DilationTestSpace

variable (T : DilationTestSpace n)

/-- The energy lower bound on divergence-free test fields at a divergence-free coefficient with
`‖DU‖ ≤ M`. -/
theorem le_linearization_point_of_divergenceFree
    (hT : ∀ φ ∈ T.carrier, ∀ x, PDE.divergence φ x = 0) {U : ℝ^n → ℝ^n}
    (hU : ContDiff ℝ ∞ U) (hdivU : ∀ x, PDE.divergence U x = 0) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ U x‖ ≤ M) {b : Fin n → DerivLp n ∞ univ}
    (hb : ∀ i, (b i : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ U x i) (μ : ℝ) (φ : T.carrier) :
    ‖gradientCLM (T.toH1 φ)‖ ^ 2 + (μ + n / 4 - 1 / 2 - M) * ‖massCLM (T.toH1 φ)‖ ^ 2 ≤
      (T.linearization b (T.graphPoint φ) + (0 : T.space →L[ℝ] StrongDual ℝ T.space)
        (T.point φ) + μ • T.l2Form (T.point φ)) (T.point φ) := by
  have hφ := T.contDiff φ φ.2
  have hc := T.hasCompactSupport φ φ.2
  have hconv := convectionForm_testFieldH1_self hU hdivU hb hφ hc (hT φ φ.2)
  have hlow := neg_mul_le_integral_stretching hU hM hφ hc
  have hmass : massPairing (T.toH1 φ) (T.toH1 φ) = ∑ i, ∫ x, (φ : ℝ^n → ℝ^n) x i *
      (φ : ℝ^n → ℝ^n) x i := by
    rw [toH1, massPairing_testFieldH1]
    refine Finset.sum_congr rfl fun i _ ↦ integral_congr_ae ?_
    filter_upwards [testFieldH1_base_ae hφ hc i] with x hx
    rw [hx]
  rw [← coe_graphPoint, linearization_add_apply_self, coe_graphPoint, restrictForm_apply, coe_point,
    boundedPart_apply, gradientForm_self, l2Form_apply, coe_point]
  change _ ≤ _ + (0 : T.space →L[ℝ] StrongDual ℝ T.space) (T.point φ) (T.point φ) + _
  rw [zero_apply, zero_apply, add_zero]
  have hconv' : convectionForm b (T.toH1 φ) (T.toH1 φ) =
      ∑ i, ∫ x, (∑ j, (φ : ℝ^n → ℝ^n) x j * PDE.partialDeriv j (fun y ↦ U y i) x) *
        (φ : ℝ^n → ℝ^n) x i := hconv
  rw [hconv', ← massPairing_self_eq_norm_sq, hmass]
  nlinarith [hlow]

end DilationTestSpace

/-- The shifted linearization at a smooth divergence-free coefficient `U` with `‖DU‖ ≤ M`, on a
dilation-invariant space of divergence-free test fields: for `μ > M + 1/2 - n/4` and every
`f ∈ E*` there is exactly one `h` in the graph domain with `L_b h + μ J h = f`, and
`‖h‖ ≤ κ⁻¹ ‖f‖` with `κ = min 1 (μ + n/4 - 1/2 - M)`. Uniqueness holds among all solutions in
the graph domain, without the norm bound (`DilationTestSpace.eq_of_linearization_add_eq`). -/
theorem existsUnique_graph_resolvent (T : DilationTestSpace n)
    (hT : ∀ φ ∈ T.carrier, ∀ x, PDE.divergence φ x = 0) {U : ℝ^n → ℝ^n}
    (hU : ContDiff ℝ ∞ U) (hdivU : ∀ x, PDE.divergence U x = 0) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ U x‖ ≤ M) {b : Fin n → DerivLp n ∞ univ}
    (hb : ∀ i, (b i : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ U x i) {μ : ℝ} (hμ : M + 1 / 2 < μ + n / 4)
    (f : StrongDual ℝ T.space) :
    ∃! h : T.graphDomain, T.linearization b h + μ • T.l2Form h = f ∧
      ‖(h : T.space)‖ ≤ (min 1 (μ + n / 4 - 1 / 2 - M))⁻¹ * ‖f‖ := by
  set κ := min 1 (μ + n / 4 - 1 / 2 - M)
  have hκ : 0 < κ := lt_min one_pos (by linarith)
  have hcoer : ∀ φ, κ * ‖T.point φ‖ ^ 2 ≤
      (T.linearization b (T.graphPoint φ) + (0 : T.space →L[ℝ] StrongDual ℝ T.space)
        (T.point φ) + μ • T.l2Form (T.point φ)) (T.point φ) := by
    intro φ
    refine le_trans ?_ (T.le_linearization_point_of_divergenceFree hT hU hdivU hM hb μ φ)
    have hsq : ‖T.point φ‖ ^ 2 = ‖massCLM (T.toH1 φ)‖ ^ 2 + ‖gradientCLM (T.toH1 φ)‖ ^ 2 := by
      rw [← Submodule.norm_coe, DilationTestSpace.coe_point, norm_sq_eq_mass_add_gradient]
    have h1 : κ ≤ 1 := min_le_left _ _
    have h2 : κ ≤ μ + n / 4 - 1 / 2 - M := min_le_right _ _
    rw [hsq]
    nlinarith [sq_nonneg ‖massCLM (T.toH1 φ)‖, sq_nonneg ‖gradientCLM (T.toH1 φ)‖]
  have h := existsUnique_graph_solution T b 0 hκ μ hcoer f
  simpa only [zero_apply, add_zero] using h

end Resolvent

end NavierStokes.Selfsimilar
