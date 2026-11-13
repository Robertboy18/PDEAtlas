/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Selfsimilar.GraphSolution

/-!
# The graph-domain linearization in a weighted energy norm

Hou, Wang and Yang measure their finite-rank estimates in the energy norm
`‖∇h‖² + η₂ ‖h‖²_{L²}`, not in the `H¹` norm, so we work in `‖h‖_c² = ‖∇h‖² + c ‖h‖²_{L²}` with a
fixed `c > 0`. For a `DilationTestSpace` with closed span `E`, `T.weighted c` is `E` with this
norm: the image of `E` under the embedding `v ↦ (∇v, √c v)` into the `L²` product of gradient
and mass coordinates, with the inherited inner product `⟪∇u, ∇v⟫ + c ⟪u, v⟫`
(`inner_weightedEquiv`).
`T.weightedEquiv hc : E ≃L T.weighted c` identifies the two spaces. The graph domain, the
linearization and the `L²` pairing are transported through it (`weightedGraphDomain`,
`weightedLinearization`, `weightedL2Form`).

`existsUnique_weighted_graph_solution` states existence and uniqueness with the coercivity
hypothesis on the test fields, the bound `‖h‖_c ≤ κ⁻¹ ‖f‖` and the dual norm of `f` all taken in
the weighted norm, so no factor `min 1 c` is lost. `le_weightedLinearization_apply_self` passes
a lower bound from the test fields to the whole weighted graph domain. Abstract results on a
normed space, such as the finite-rank determinant criterion, apply with `E = T.weighted c`.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 4.2.1, the E-inner product,
  p. 26, and Appendix B, p. 60.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Sobolev ContDiff SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Selfsimilar

open Stationary

variable {n : ℕ}

local notation "H" => PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))
local notation "Mass" => PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 univ)
local notation "Grad" => PiLp 2 (fun _ : Fin n ↦ PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 univ))

/-- The weighted embedding `v ↦ (∇v, √c v)` of vector `H¹` into the `L²` product of gradient and
mass coordinates. -/
def weightedEmbedding (c : ℝ) : H →L[ℝ] WithLp 2 (Grad × Mass) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ Grad Mass).symm.toContinuousLinearMap.comp
    (gradientCLM.prod (Real.sqrt c • massCLM))

theorem weightedEmbedding_apply (c : ℝ) (v : H) :
    weightedEmbedding c v = WithLp.toLp 2 (gradientCLM v, Real.sqrt c • massCLM v) :=
  rfl

/-- The weighted inner product `⟪∇u, ∇v⟫ + c ⟪u, v⟫`. -/
theorem inner_weightedEmbedding {c : ℝ} (hc : 0 ≤ c) (u v : H) :
    inner ℝ (weightedEmbedding c u) (weightedEmbedding c v) =
      gradientForm u v + c * massPairing u v := by
  rw [weightedEmbedding_apply, weightedEmbedding_apply, WithLp.prod_inner_apply,
    WithLp.ofLp_toLp, WithLp.ofLp_toLp, real_inner_smul_left, real_inner_smul_right,
    ← mul_assoc, Real.mul_self_sqrt hc, ← massForm_apply]
  rfl

theorem norm_weightedEmbedding_sq {c : ℝ} (hc : 0 ≤ c) (v : H) :
    ‖weightedEmbedding c v‖ ^ 2 = ‖gradientCLM v‖ ^ 2 + c * ‖massCLM v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_weightedEmbedding hc, gradientForm_self,
    massPairing_self_eq_norm_sq]

theorem weightedEmbedding_injective {c : ℝ} (hc : 0 < c) :
    Function.Injective (weightedEmbedding (n := n) c) := by
  refine (injective_iff_map_eq_zero (weightedEmbedding (n := n) c)).mpr fun v hv ↦ ?_
  have h := norm_weightedEmbedding_sq hc.le v
  rw [hv, norm_zero] at h
  have hsq := norm_sq_eq_mass_add_gradient v
  have hm := sq_nonneg ‖massCLM v‖
  have hg := sq_nonneg ‖gradientCLM v‖
  have hm0 : ‖massCLM v‖ ^ 2 = 0 := by nlinarith
  have hv0 : ‖v‖ ^ 2 = 0 := by nlinarith
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hv0)

namespace DilationTestSpace

variable (T : DilationTestSpace n) {c : ℝ}

/-- The closed span of the test fields with the weighted energy norm `‖∇v‖² + c ‖v‖²`. -/
def weighted (c : ℝ) : Submodule ℝ (WithLp 2 (Grad × Mass)) :=
  T.space.map (weightedEmbedding (n := n) c).toLinearMap

/-- The weighted copy as a linear equivalence. -/
def weightedLinearEquiv (hc : 0 < c) : T.space ≃ₗ[ℝ] T.weighted c :=
  Submodule.equivMapOfInjective _ (weightedEmbedding_injective hc) T.space

theorem coe_weightedLinearEquiv (hc : 0 < c) (v : T.space) :
    (T.weightedLinearEquiv hc v : WithLp 2 (Grad × Mass)) = weightedEmbedding c (v : H) :=
  rfl

theorem norm_weightedLinearEquiv_sq (hc : 0 < c) (v : T.space) :
    ‖T.weightedLinearEquiv hc v‖ ^ 2 =
      ‖gradientCLM (v : H)‖ ^ 2 + c * ‖massCLM (v : H)‖ ^ 2 := by
  rw [← Submodule.norm_coe, coe_weightedLinearEquiv, norm_weightedEmbedding_sq hc.le]

theorem norm_le_weightedLinearEquiv (hc : 0 < c) (v : T.space) :
    ‖v‖ ≤ Real.sqrt (min 1 c)⁻¹ * ‖T.weightedLinearEquiv hc v‖ := by
  have hmin : 0 < min 1 c := lt_min one_pos hc
  have h := T.mul_min_mul_norm_sq_le (κ := 1) zero_le_one c v
  rw [← T.norm_weightedLinearEquiv_sq hc, one_mul, one_mul] at h
  have hsq : ‖v‖ ^ 2 ≤ (Real.sqrt (min 1 c)⁻¹ * ‖T.weightedLinearEquiv hc v‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (inv_nonneg.mpr hmin.le), inv_mul_eq_div, le_div_iff₀ hmin]
    linarith
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq

/-- The identification of the closed span with its weighted copy. -/
def weightedEquiv (hc : 0 < c) : T.space ≃L[ℝ] T.weighted c :=
  (T.weightedLinearEquiv hc).toContinuousLinearEquivOfBounds ‖weightedEmbedding (n := n) c‖
    (Real.sqrt (min 1 c)⁻¹)
    (fun v ↦ by
      rw [← Submodule.norm_coe, coe_weightedLinearEquiv, ← Submodule.norm_coe v]
      exact (weightedEmbedding c).le_opNorm _)
    (fun w ↦ by
      have h := T.norm_le_weightedLinearEquiv hc ((T.weightedLinearEquiv hc).symm w)
      rwa [LinearEquiv.apply_symm_apply] at h)

theorem weightedEquiv_apply (hc : 0 < c) (v : T.space) :
    T.weightedEquiv hc v = T.weightedLinearEquiv hc v :=
  rfl

theorem coe_weightedEquiv (hc : 0 < c) (v : T.space) :
    (T.weightedEquiv hc v : WithLp 2 (Grad × Mass)) = weightedEmbedding c (v : H) :=
  rfl

/-- The weighted norm: `‖e v‖² = ‖∇v‖² + c ‖v‖²_{L²}`. -/
theorem norm_weightedEquiv_sq (hc : 0 < c) (v : T.space) :
    ‖T.weightedEquiv hc v‖ ^ 2 = ‖gradientCLM (v : H)‖ ^ 2 + c * ‖massCLM (v : H)‖ ^ 2 :=
  T.norm_weightedLinearEquiv_sq hc v

/-- The weighted inner product: `⟪e u, e v⟫ = ⟪∇u, ∇v⟫ + c ⟪u, v⟫_{L²}`. -/
theorem inner_weightedEquiv (hc : 0 < c) (u v : T.space) :
    inner ℝ (T.weightedEquiv hc u) (T.weightedEquiv hc v) =
      gradientForm (u : H) (v : H) + c * massPairing (u : H) (v : H) := by
  rw [Submodule.coe_inner, coe_weightedEquiv, coe_weightedEquiv, inner_weightedEmbedding hc.le]

/-- Functionals on the closed span and on its weighted copy. -/
def weightedDual (hc : 0 < c) : StrongDual ℝ T.space ≃L[ℝ] StrongDual ℝ (T.weighted c) :=
  (T.weightedEquiv hc).arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)

theorem weightedDual_apply (hc : 0 < c) (g : StrongDual ℝ T.space) (w : T.weighted c) :
    T.weightedDual hc g w = g ((T.weightedEquiv hc).symm w) :=
  rfl

theorem weightedDual_symm_apply (hc : 0 < c) (g : StrongDual ℝ (T.weighted c)) (v : T.space) :
    (T.weightedDual hc).symm g v = g (T.weightedEquiv hc v) :=
  rfl

/-- The graph domain in the weighted copy. -/
def weightedGraphDomain (hc : 0 < c) : Submodule ℝ (T.weighted c) :=
  T.graphDomain.map ((T.weightedEquiv hc).toLinearEquiv : T.space →ₗ[ℝ] T.weighted c)

/-- The identification of the graph domain with its weighted copy. -/
def weightedGraphEquiv (hc : 0 < c) : T.graphDomain ≃ₗ[ℝ] T.weightedGraphDomain hc :=
  Submodule.equivMapOfInjective _ (T.weightedEquiv hc).injective T.graphDomain

theorem coe_weightedGraphEquiv (hc : 0 < c) (h : T.graphDomain) :
    (T.weightedGraphEquiv hc h : T.weighted c) = T.weightedEquiv hc h :=
  rfl

theorem coe_weightedGraphEquiv_symm (hc : 0 < c) (k : T.weightedGraphDomain hc) :
    ((T.weightedGraphEquiv hc).symm k : T.space) = (T.weightedEquiv hc).symm k := by
  conv_rhs => rw [← (T.weightedGraphEquiv hc).apply_symm_apply k]
  rw [coe_weightedGraphEquiv, ContinuousLinearEquiv.symm_apply_apply]

/-- The weak linearization on the weighted graph domain. -/
def weightedLinearization (hc : 0 < c) (b : Fin n → DerivLp n ∞ univ) :
    T.weightedGraphDomain hc →ₗ[ℝ] StrongDual ℝ (T.weighted c) :=
  (T.weightedDual hc).toLinearEquiv.toLinearMap ∘ₗ T.linearization b ∘ₗ
    (T.weightedGraphEquiv hc).symm.toLinearMap

theorem weightedLinearization_apply (hc : 0 < c) (b : Fin n → DerivLp n ∞ univ)
    (k : T.weightedGraphDomain hc) (w : T.weighted c) :
    T.weightedLinearization hc b k w =
      T.linearization b ((T.weightedGraphEquiv hc).symm k) ((T.weightedEquiv hc).symm w) :=
  rfl

/-- The `L²` pairing on the weighted copy. -/
def weightedL2Form (hc : 0 < c) : T.weighted c →L[ℝ] StrongDual ℝ (T.weighted c) :=
  T.l2Form.bilinearComp (T.weightedEquiv hc).symm.toContinuousLinearMap
    (T.weightedEquiv hc).symm.toContinuousLinearMap

theorem weightedL2Form_apply (hc : 0 < c) (u w : T.weighted c) :
    T.weightedL2Form hc u w =
      massPairing (((T.weightedEquiv hc).symm u : T.space) : H)
        (((T.weightedEquiv hc).symm w : T.space) : H) := by
  rw [weightedL2Form, ContinuousLinearMap.bilinearComp_apply]
  exact l2Form_apply _ _ _

theorem weightedL2Form_apply_self_nonneg (hc : 0 < c) (u : T.weighted c) :
    0 ≤ T.weightedL2Form hc u u := by
  rw [weightedL2Form_apply, massPairing_self_eq_norm_sq]
  positivity

/-- A test field as a point of the weighted copy. -/
def weightedPoint (hc : 0 < c) (φ : T.carrier) : T.weighted c :=
  T.weightedEquiv hc (T.point φ)

/-- A test field as a point of the weighted graph domain. -/
def weightedGraphPoint (hc : 0 < c) (φ : T.carrier) : T.weightedGraphDomain hc :=
  T.weightedGraphEquiv hc (T.graphPoint φ)

@[simp]
theorem coe_weightedGraphPoint (hc : 0 < c) (φ : T.carrier) :
    (T.weightedGraphPoint hc φ : T.weighted c) = T.weightedPoint hc φ :=
  rfl

/-- The operator `K` on the weighted copy, transported to the closed span. -/
def unweightedOperator (hc : 0 < c) (K : T.weighted c →L[ℝ] StrongDual ℝ (T.weighted c)) :
    T.space →L[ℝ] StrongDual ℝ T.space :=
  K.bilinearComp (T.weightedEquiv hc).toContinuousLinearMap
    (T.weightedEquiv hc).toContinuousLinearMap

theorem unweightedOperator_apply (hc : 0 < c)
    (K : T.weighted c →L[ℝ] StrongDual ℝ (T.weighted c)) (u v : T.space) :
    T.unweightedOperator hc K u v = K (T.weightedEquiv hc u) (T.weightedEquiv hc v) := by
  rw [unweightedOperator, ContinuousLinearMap.bilinearComp_apply]
  rfl

/-- The shifted weighted operator, evaluated at weighted points, is the shifted operator on
the closed span. -/
theorem weightedShifted_apply (hc : 0 < c) (b : Fin n → DerivLp n ∞ univ)
    (K : T.weighted c →L[ℝ] StrongDual ℝ (T.weighted c)) (μ : ℝ) (h : T.graphDomain)
    (u : T.space) :
    (T.weightedLinearization hc b (T.weightedGraphEquiv hc h) +
        K (T.weightedEquiv hc h) + μ • T.weightedL2Form hc (T.weightedEquiv hc h))
        (T.weightedEquiv hc u) =
      (T.linearization b h + T.unweightedOperator hc K h + μ • T.l2Form h) u := by
  simp only [add_apply, smul_apply, weightedLinearization_apply, weightedL2Form_apply,
    unweightedOperator_apply, LinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply,
    l2Form_apply]

/-- A continuous lower bound of the weighted energy on the test fields holds on the whole
weighted graph domain. -/
theorem le_weightedLinearization_apply_self (hc : 0 < c) (b : Fin n → DerivLp n ∞ univ)
    (K : T.weighted c →L[ℝ] StrongDual ℝ (T.weighted c)) {μ : ℝ} {N : T.weighted c → ℝ}
    (hN : Continuous N)
    (hcoer : ∀ φ, N (T.weightedPoint hc φ) ≤
      (T.weightedLinearization hc b (T.weightedGraphPoint hc φ) + K (T.weightedPoint hc φ) +
        μ • T.weightedL2Form hc (T.weightedPoint hc φ)) (T.weightedPoint hc φ))
    (k : T.weightedGraphDomain hc) :
    N k ≤ (T.weightedLinearization hc b k + K k + μ • T.weightedL2Form hc k) k := by
  have hN' : Continuous fun v : T.space ↦ N (T.weightedEquiv hc v) :=
    hN.comp (T.weightedEquiv hc).continuous
  have hcoer' : ∀ φ, N (T.weightedEquiv hc (T.point φ)) ≤
      (T.linearization b (T.graphPoint φ) + T.unweightedOperator hc K (T.point φ) +
        μ • T.l2Form (T.point φ)) (T.point φ) := fun φ ↦ by
    have h := T.weightedShifted_apply hc b K μ (T.graphPoint φ) (T.point φ)
    rw [coe_graphPoint] at h
    rw [← h]
    exact hcoer φ
  have h := T.le_linearization_apply_self b (T.unweightedOperator hc K) hN' hcoer'
    ((T.weightedGraphEquiv hc).symm k)
  rw [← T.weightedShifted_apply hc b K μ, LinearEquiv.apply_symm_apply,
    ← coe_weightedGraphEquiv, LinearEquiv.apply_symm_apply] at h
  exact h

/-- Weighted coercivity on the test fields, read on the closed span. -/
theorem weightedCoercive_point (hc : 0 < c) (b : Fin n → DerivLp n ∞ univ)
    (K : T.weighted c →L[ℝ] StrongDual ℝ (T.weighted c)) {μ : ℝ} {N : T.weighted c → ℝ}
    (hcoer : ∀ φ, N (T.weightedPoint hc φ) ≤
      (T.weightedLinearization hc b (T.weightedGraphPoint hc φ) + K (T.weightedPoint hc φ) +
        μ • T.weightedL2Form hc (T.weightedPoint hc φ)) (T.weightedPoint hc φ))
    (φ : T.carrier) :
    N (T.weightedEquiv hc (T.point φ)) ≤
      (T.linearization b (T.graphPoint φ) + T.unweightedOperator hc K (T.point φ) +
        μ • T.l2Form (T.point φ)) (T.point φ) := by
  have h := T.weightedShifted_apply hc b K μ (T.graphPoint φ) (T.point φ)
  rw [coe_graphPoint] at h
  rw [← h]
  exact hcoer φ

/-- The shifted weighted operator at a field of the weighted graph domain. -/
theorem weightedShifted_apply_of_mem (hc : 0 < c) (b : Fin n → DerivLp n ∞ univ)
    (K : T.weighted c →L[ℝ] StrongDual ℝ (T.weighted c)) (μ : ℝ)
    (k : T.weightedGraphDomain hc) (u : T.space) :
    (T.weightedLinearization hc b k + K k + μ • T.weightedL2Form hc k) (T.weightedEquiv hc u) =
      (T.linearization b ((T.weightedGraphEquiv hc).symm k) +
        T.unweightedOperator hc K ((T.weightedGraphEquiv hc).symm k) +
        μ • T.l2Form ((T.weightedGraphEquiv hc).symm k)) u := by
  have hk : (k : T.weighted c) = T.weightedEquiv hc ((T.weightedGraphEquiv hc).symm k) := by
    rw [← T.coe_weightedGraphEquiv hc, LinearEquiv.apply_symm_apply]
  have h1 : T.weightedLinearization hc b k (T.weightedEquiv hc u) =
      T.linearization b ((T.weightedGraphEquiv hc).symm k) u := by
    rw [weightedLinearization_apply, ContinuousLinearEquiv.symm_apply_apply]
  have h2 : K (k : T.weighted c) (T.weightedEquiv hc u) =
      T.unweightedOperator hc K ((T.weightedGraphEquiv hc).symm k) u := by
    rw [unweightedOperator_apply, ← hk]
  have h3 : T.weightedL2Form hc k (T.weightedEquiv hc u) =
      T.l2Form ((T.weightedGraphEquiv hc).symm k) u := by
    rw [weightedL2Form_apply, l2Form_apply, coe_weightedGraphEquiv_symm,
      ContinuousLinearEquiv.symm_apply_apply]
  simp only [add_apply, smul_apply, h1, h2, h3]

/-- The weighted equation and the equation on the closed span are equivalent. -/
theorem weightedLinearization_add_eq_iff (hc : 0 < c) (b : Fin n → DerivLp n ∞ univ)
    (K : T.weighted c →L[ℝ] StrongDual ℝ (T.weighted c)) (μ : ℝ)
    (f : StrongDual ℝ (T.weighted c)) (k : T.weightedGraphDomain hc) :
    T.weightedLinearization hc b k + K k + μ • T.weightedL2Form hc k = f ↔
      T.linearization b ((T.weightedGraphEquiv hc).symm k) +
          T.unweightedOperator hc K ((T.weightedGraphEquiv hc).symm k) +
          μ • T.l2Form ((T.weightedGraphEquiv hc).symm k) = (T.weightedDual hc).symm f := by
  constructor
  · intro hkeq
    ext u
    rw [← T.weightedShifted_apply_of_mem hc b K μ k u, hkeq, weightedDual_symm_apply]
  · intro hkeq
    ext w
    rw [← ContinuousLinearEquiv.apply_symm_apply (T.weightedEquiv hc) w,
      T.weightedShifted_apply_of_mem hc b K μ k, hkeq, weightedDual_symm_apply]

/-- The weighted bound for a solution with weighted coercivity on the graph domain. -/
theorem norm_le_of_weighted_coercive {κ : ℝ} (hκ : 0 < κ) (hc : 0 < c)
    (f : StrongDual ℝ (T.weighted c)) {v : T.space}
    (hv : κ * ‖T.weightedEquiv hc v‖ ^ 2 ≤ f (T.weightedEquiv hc v)) :
    ‖T.weightedEquiv hc v‖ ≤ κ⁻¹ * ‖f‖ := by
  have h2 : f (T.weightedEquiv hc v) ≤ ‖f‖ * ‖T.weightedEquiv hc v‖ :=
    (le_abs_self _).trans (f.le_opNorm _)
  rw [le_inv_mul_iff₀ hκ]
  rcases eq_or_lt_of_le (norm_nonneg (T.weightedEquiv hc v)) with h0 | hpos
  · rw [← h0, mul_zero]
    exact norm_nonneg f
  · nlinarith

end DilationTestSpace

/-- Existence and uniqueness in the weighted graph domain. If
`κ ‖φ‖_c² ≤ ⟨(L_b + K + μ J) φ, φ⟩` on the test fields in the weighted norm
`‖v‖_c² = ‖∇v‖² + c ‖v‖²`, `c > 0`, then for every `f` in the dual of the weighted copy there is
exactly one `h` in the weighted graph domain with `L_b h + K h + μ J h = f`, and
`‖h‖_c ≤ κ⁻¹ ‖f‖` with the dual norm of the weighted copy. Uniqueness holds among all solutions
in the weighted graph domain. -/
theorem existsUnique_weighted_graph_solution (T : DilationTestSpace n) {c : ℝ} (hc : 0 < c)
    (b : Fin n → DerivLp n ∞ univ) (K : T.weighted c →L[ℝ] StrongDual ℝ (T.weighted c))
    {κ : ℝ} (hκ : 0 < κ) (μ : ℝ)
    (hcoer : ∀ φ, κ * ‖T.weightedPoint hc φ‖ ^ 2 ≤
      (T.weightedLinearization hc b (T.weightedGraphPoint hc φ) + K (T.weightedPoint hc φ) +
        μ • T.weightedL2Form hc (T.weightedPoint hc φ)) (T.weightedPoint hc φ))
    (f : StrongDual ℝ (T.weighted c)) :
    ∃! k : T.weightedGraphDomain hc,
      T.weightedLinearization hc b k + K k + μ • T.weightedL2Form hc k = f ∧
        ‖(k : T.weighted c)‖ ≤ κ⁻¹ * ‖f‖ := by
  have hκ' : 0 < κ * min 1 c := mul_pos hκ (lt_min one_pos hc)
  have hcoerN := T.weightedCoercive_point hc b K (N := fun w ↦ κ * ‖w‖ ^ 2) hcoer
  have hcoer' : ∀ φ, κ * min 1 c * ‖T.point φ‖ ^ 2 ≤
      (T.linearization b (T.graphPoint φ) + T.unweightedOperator hc K (T.point φ) +
        μ • T.l2Form (T.point φ)) (T.point φ) := fun φ ↦ by
    refine le_trans ?_ (hcoerN φ)
    rw [T.norm_weightedEquiv_sq hc]
    exact T.mul_min_mul_norm_sq_le hκ.le c _
  obtain ⟨h', ⟨heq', -⟩, -⟩ := existsUnique_graph_solution T b (T.unweightedOperator hc K) hκ' μ
    hcoer' ((T.weightedDual hc).symm f)
  have hsol : T.weightedLinearization hc b (T.weightedGraphEquiv hc h') +
      K (T.weightedGraphEquiv hc h') +
      μ • T.weightedL2Form hc (T.weightedGraphEquiv hc h') = f := by
    rw [T.weightedLinearization_add_eq_iff hc b K μ f, LinearEquiv.symm_apply_apply]
    exact heq'
  refine ⟨T.weightedGraphEquiv hc h', ⟨hsol, ?_⟩, fun k ⟨hk, _⟩ ↦ ?_⟩
  · have hle := T.le_linearization_apply_self b (T.unweightedOperator hc K)
      (continuous_const.mul ((T.weightedEquiv hc).continuous.norm.pow 2)) hcoerN h'
    rw [heq', DilationTestSpace.weightedDual_symm_apply] at hle
    rw [T.coe_weightedGraphEquiv hc]
    exact T.norm_le_of_weighted_coercive hκ hc f hle
  · have hk' := (T.weightedLinearization_add_eq_iff hc b K μ f k).mp hk
    have hkh := T.eq_of_linearization_add_eq b (T.unweightedOperator hc K) hκ' hcoer'
      (hk'.trans heq'.symm)
    rw [← hkh, LinearEquiv.apply_symm_apply]

end NavierStokes.Selfsimilar
