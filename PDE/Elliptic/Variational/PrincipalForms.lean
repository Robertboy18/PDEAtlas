/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates
import Mathlib.Algebra.Order.Chebyshev
import PDE.Spaces.Sobolev.Inequalities.Poincare.BoundedDomain

/-!
# Basic elliptic variational forms

The Dirichlet form, the `L²` load, and the mass form on `H¹₀(Ω)`, with positivity and
bounded-domain coercivity of the Dirichlet form. These are the
operator-independent ingredients shared by concrete Poisson and modified Helmholtz problems and by
the variable-coefficient variational layer. The Dirichlet form is Evans's bilinear form (8) of
§6.1.2 for `L = -Δ`, and its coercivity on a bounded domain is the case `γ = 0` of the energy
estimates noted in the Examples after §6.2.2, Theorem 3.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.1.2, (8)-(9), p. 314; §6.2.2, Theorem 2 (Energy
  estimates), pp. 318-319, and the Examples on p. 320.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Sobolev

@[expose] public section

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open scoped Topology NNReal InnerProductSpace

namespace GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}


section DirichletForm

local notation "L2" => DerivLp n 2 Ω

/-- The bilinear Dirichlet energy pairing built from a family of derivative coordinate maps,
before continuity is established. -/
def dirichletFormLinOf
    (V : Type*) [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
    (D : Fin n → V →L[ℝ] L2) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun u v ↦ ∑ i : Fin n, ⟪D i u, D i v⟫_ℝ)
    (by
      intro u₁ u₂ v
      classical
      simp [Finset.sum_add_distrib, inner_add_left])
    (by
      intro c u v
      classical
      simp [Finset.mul_sum, real_inner_smul_left])
    (by
      intro u v₁ v₂
      classical
      simp [Finset.sum_add_distrib, inner_add_right])
    (by
      intro c u v
      classical
      simp [Finset.mul_sum, real_inner_smul_right])

/-- The Dirichlet energy bilinear form built from derivative coordinate maps. -/
def dirichletFormOf
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (D : Fin n → V →L[ℝ] L2) (hD : ∀ i (u : V), ‖D i u‖ ≤ ‖u‖) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  (dirichletFormLinOf (n := n) (Ω := Ω) V D).mkContinuous₂ (n : ℝ) <| by
    classical
    intro u v
    have hterm :
        ∀ i : Fin n, ‖⟪D i u, D i v⟫_ℝ‖ ≤ ‖u‖ * ‖v‖ := by
      intro i
      calc
        ‖⟪D i u, D i v⟫_ℝ‖
            ≤ ‖D i u‖ * ‖D i v‖ := by
              simpa [Real.norm_eq_abs] using
                (abs_real_inner_le_norm (D i u) (D i v))
        _ ≤ ‖u‖ * ‖v‖ :=
          mul_le_mul (hD i u) (hD i v) (norm_nonneg _) (norm_nonneg _)
    calc
      ‖∑ i : Fin n, ⟪D i u, D i v⟫_ℝ‖
          ≤ ∑ i : Fin n, ‖⟪D i u, D i v⟫_ℝ‖ := by
            simpa using (norm_sum_le Finset.univ (fun i : Fin n ↦ ⟪D i u, D i v⟫_ℝ))
      _ ≤ ∑ _i : Fin n, ‖u‖ * ‖v‖ :=
        Finset.sum_le_sum fun i _hi ↦ hterm i
      _ = (n : ℝ) * ‖u‖ * ‖v‖ := by simp [mul_assoc]

/-- The Dirichlet energy bilinear form on `H¹₀(Ω)`. -/
def dirichletForm : H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
  dirichletFormOf (n := n) (Ω := Ω) H¹₀(Ω)
    (fun i ↦ derivCoordCLM (n := n) (Ω := Ω) i) <| by
      intro i u
      exact derivCoordCLM_norm_le (n := n) (Ω := Ω) i u

/-- The load functional `v ↦ ⟪f, v⟫` on `H¹₀(Ω)`, for `f ∈ L²(Ω)`. -/
def loadFunctional (f : L2) : StrongDual ℝ H¹₀(Ω) :=
  (innerSL ℝ f).comp (baseCoordCLM (n := n) (Ω := Ω))

/-- Unfolding the Dirichlet form: `B(u,v) = ∑ᵢ ⟪∂ᵢu, ∂ᵢv⟫_{L²}`, the weak form of
`∫_Ω ∇u · ∇v`. -/
theorem dirichletForm_apply (u v : H¹₀(Ω)) :
    dirichletForm (n := n) (Ω := Ω) u v =
      ∑ i : Fin n,
        ⟪derivCoordCLM (n := n) (Ω := Ω) i u,
          derivCoordCLM (n := n) (Ω := Ω) i v⟫_ℝ :=
  rfl

/-- Symmetry of the Dirichlet form. -/
theorem dirichletForm_symm (u v : H¹₀(Ω)) :
    dirichletForm (n := n) (Ω := Ω) u v =
      dirichletForm (n := n) (Ω := Ω) v u := by
  rw [dirichletForm_apply, dirichletForm_apply]
  exact Finset.sum_congr rfl fun i _hi ↦
    real_inner_comm
      (derivCoordCLM (n := n) (Ω := Ω) i v)
      (derivCoordCLM (n := n) (Ω := Ω) i u)

/-- The load functional pairs `f` with the `L²` base coordinate of `v`: `F(v) = ⟪f, v⟫_{L²}`. -/
theorem loadFunctional_apply (f : L2) (v : H¹₀(Ω)) :
    loadFunctional (n := n) (Ω := Ω) f v =
      ⟪f, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ :=
  rfl

/-- The `L²` load is the integral against the order-zero Sobolev coordinate.
Its integrability follows from the `L² · L²` product estimate. -/
theorem loadFunctional_eq_integral (f : L2) (v : H¹₀(Ω)) :
    loadFunctional f v =
      ∫ x, f x * baseCoordCLM (n := n) (Ω := Ω) v x ∂domainMeasure n Ω := by
  rw [loadFunctional_apply, MeasureTheory.L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial, mul_comm]

/-- On an open domain, the weak load vanishes exactly when its `L²`
density vanishes. This uses density of the supported Sobolev core in `L²`. -/
theorem loadFunctional_eq_zero_iff (hΩopen : IsOpen Ω) (f : L2) :
    loadFunctional (n := n) (Ω := Ω) f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    have heq : (fun w : L2 ↦ inner ℝ f w) = fun _ ↦ 0 := by
      apply (baseCoordCLM_denseRange hΩopen).equalizer
        (innerSL ℝ f).continuous continuous_const
      funext v
      exact DFunLike.congr_fun hf v
    exact inner_self_eq_zero.mp (congrFun heq f)
  · rintro rfl
    ext v
    simp [loadFunctional]

/-- The load functional of the zero datum is the zero functional. -/
@[simp]
theorem loadFunctional_zero :
    loadFunctional (n := n) (Ω := Ω) (0 : L2) = 0 := by
  ext v
  simp [loadFunctional]

/-- The load functional is additive in the datum. -/
@[simp]
theorem loadFunctional_add (f g : L2) :
    loadFunctional (n := n) (Ω := Ω) (f + g) =
      loadFunctional (n := n) (Ω := Ω) f +
        loadFunctional (n := n) (Ω := Ω) g := by
  ext v
  simp [loadFunctional]

/-- The load functional respects subtraction of data. -/
@[simp]
theorem loadFunctional_sub (f g : L2) :
    loadFunctional (n := n) (Ω := Ω) (f - g) =
      loadFunctional (n := n) (Ω := Ω) f -
        loadFunctional (n := n) (Ω := Ω) g := by
  ext v
  simp [loadFunctional]

/-- The load functional of `-f` is the negative of the load functional of `f`. -/
@[simp]
theorem loadFunctional_neg (f : L2) :
    loadFunctional (n := n) (Ω := Ω) (-f) =
      -loadFunctional (n := n) (Ω := Ω) f := by
  ext v
  simp [loadFunctional]

/-- The load functional is homogeneous in the datum. -/
@[simp]
theorem loadFunctional_smul (c : ℝ) (f : L2) :
    loadFunctional (n := n) (Ω := Ω) (c • f) =
      c • loadFunctional (n := n) (Ω := Ω) f := by
  ext v
  simp [loadFunctional]

/-- Cauchy-Schwarz bound for the Dirichlet load functional. -/
theorem norm_loadFunctional_apply_le (f : L2) (v : H¹₀(Ω)) :
    ‖loadFunctional (n := n) (Ω := Ω) f v‖ ≤ ‖f‖ * ‖v‖ := by
  calc
    ‖loadFunctional (n := n) (Ω := Ω) f v‖
        = ‖⟪f, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ‖ := by
            rw [loadFunctional_apply]
    _ ≤ ‖f‖ * ‖baseCoordCLM (n := n) (Ω := Ω) v‖ := by
      simpa [Real.norm_eq_abs] using
        abs_real_inner_le_norm f (baseCoordCLM (n := n) (Ω := Ω) v)
    _ ≤ ‖f‖ * ‖v‖ := by
      exact mul_le_mul_of_nonneg_left
        (baseCoordCLM_norm_le (n := n) (Ω := Ω) v) (norm_nonneg f)

/-- The operator norm of the load functional is bounded by the `L²` norm of the datum. -/
theorem norm_loadFunctional_le (f : L2) :
    ‖loadFunctional (n := n) (Ω := Ω) f‖ ≤ ‖f‖ := by
  exact (loadFunctional (n := n) (Ω := Ω) f).opNorm_le_bound (norm_nonneg f)
    (fun v ↦ norm_loadFunctional_apply_le (n := n) (Ω := Ω) f v)

/-- The assignment `f ↦ (v ↦ ⟪f,v⟫)` as a bounded linear map from `L²(Ω)` into the dual of
`H¹₀(Ω)`. -/
def loadFunctionalCLM : L2 →L[ℝ] StrongDual ℝ H¹₀(Ω) :=
  LinearMap.mkContinuous
    { toFun := loadFunctional (n := n) (Ω := Ω)
      map_add' := loadFunctional_add (n := n) (Ω := Ω)
      map_smul' := loadFunctional_smul (n := n) (Ω := Ω) }
    1
    (fun f ↦ by
      simpa using norm_loadFunctional_le (n := n) (Ω := Ω) f)

/-- The bundled map `L²(Ω) → (H¹₀(Ω))*` evaluates to the load functional. -/
@[simp]
theorem loadFunctionalCLM_apply (f : L2) :
    loadFunctionalCLM (n := n) (Ω := Ω) f =
      loadFunctional (n := n) (Ω := Ω) f :=
  rfl

end DirichletForm

section QuadraticForms

local notation "L2" => DerivLp n 2 Ω

/-- The Dirichlet form on the diagonal is the sum of the squared derivative-coordinate
norms. -/
theorem dirichletForm_self_eq_sum_norm_sq (u : H¹₀(Ω)) :
    dirichletForm (n := n) (Ω := Ω) u u =
      ∑ i : Fin n, ‖derivCoordCLM (n := n) (Ω := Ω) i u‖ ^ 2 := by
  classical
  change
    (∑ i : Fin n,
      ⟪derivCoordCLM (n := n) (Ω := Ω) i u,
        derivCoordCLM (n := n) (Ω := Ω) i u⟫_ℝ) =
      ∑ i : Fin n, ‖derivCoordCLM (n := n) (Ω := Ω) i u‖ ^ 2
  exact Finset.sum_congr rfl fun i _hi ↦ real_inner_self_eq_norm_sq _

/-- The Dirichlet form is the `L²` inner product of the vector
weak gradients. Polarization identifies the bilinear forms from their diagonals. -/
theorem dirichletForm_eq_inner_gradient (u v : H¹₀(Ω)) :
    dirichletForm u v = inner ℝ (∇ (u : H¹(Ω))) (∇ (v : H¹(Ω))) := by
  have hdiag (w : H¹₀(Ω)) :
      dirichletForm w w = inner ℝ (∇ (w : H¹(Ω))) (∇ (w : H¹(Ω))) := by
    rw [real_inner_self_eq_norm_sq, dirichletForm_self_eq_sum_norm_sq]
    exact (norm_gradientCLM_sq_eq_sum_deriv_sq w).symm
  have hsum := hdiag (u + v)
  simp only [Submodule.coe_add, map_add, add_apply, inner_add_left, inner_add_right] at hsum
  rw [hdiag u, hdiag v, dirichletForm_symm v u] at hsum
  linarith [real_inner_comm (∇ (v : H¹(Ω))) (∇ (u : H¹(Ω)))]

/-- The Dirichlet form equals the integrable pointwise pairing of the vector
weak gradients, with the restricted volume measure. -/
theorem dirichletForm_eq_integral_gradient (u v : H¹₀(Ω)) :
    dirichletForm u v =
      ∫ x, inner ℝ (∇ (u : H¹(Ω)) x) (∇ (v : H¹(Ω)) x) ∂domainMeasure n Ω := by
  rw [dirichletForm_eq_inner_gradient, L2.inner_def]

/-- The weak-gradient pairing in the Dirichlet form is integrable. -/
theorem integrable_inner_gradient (u v : H¹₀(Ω)) :
    Integrable (fun x ↦ inner ℝ (∇ (u : H¹(Ω)) x) (∇ (v : H¹(Ω)) x))
      (domainMeasure n Ω) :=
  L2.integrable_inner _ _

/-- Pairing with a supported smooth test function gives the classical
derivatives of that test function and the weak derivatives of `u`. -/
theorem dirichletForm_testFunction_eq_integral (u : H¹₀(Ω)) (φ : TestFunctionOn n Ω) :
    dirichletForm u (testFunctionToH10 φ) =
      ∑ i : Fin n, ∫ x, derivCoordCLM i u x * (∂[i] φ.1.toFun) x
        ∂domainMeasure n Ω := by
  rw [dirichletForm_apply]
  exact Finset.sum_congr rfl fun i _ ↦ inner_deriv_testFunction_eq_integral u i φ

/-- Positivity of the Dirichlet form on the diagonal. -/
theorem dirichletForm_self_nonneg (u : H¹₀(Ω)) :
    0 ≤ dirichletForm (n := n) (Ω := Ω) u u := by
  rw [dirichletForm_self_eq_sum_norm_sq (n := n) (Ω := Ω) u]
  exact Finset.sum_nonneg fun _i _hi ↦ sq_nonneg _

/-- The one-dimensional Dirichlet energy controls the full `H¹₀` norm with
an explicit constant. On a unit-measure domain the coercivity constant is
`1/2`; the base-coordinate contribution is bounded by Poincaré. -/
theorem dirichletForm_coercive_bound_one {Ω : Set (ℝ^1)}
    (hbounded : Bornology.IsBounded Ω) (u : H¹₀(Ω)) :
    ‖u‖ ^ 2 / ((volume Ω).toReal ^ 2 + 1) ≤ dirichletForm u u := by
  have hP := norm_baseCoord_le_poincareConstOne_mul_sum_derivCoord hbounded u
  change ‖baseCoordCLM u‖ ≤ (poincareConstOne Ω : ℝ) *
    ∑ i : Fin 1, ‖derivCoordCLM i u‖ at hP
  simp only [Fin.sum_univ_one, poincareConstOne, ENNReal.coe_toNNReal_eq_toReal] at hP
  have hsq := (sq_le_sq₀ (norm_nonneg (baseCoordCLM u))
    (mul_nonneg ENNReal.toReal_nonneg (norm_nonneg (derivCoordCLM 0 u)))).mpr hP
  rw [norm_sq_eq_base_sq_add_sum_deriv_sq, dirichletForm_self_eq_sum_norm_sq,
    Fin.sum_univ_one, div_le_iff₀ (by positivity)]
  nlinarith [hsq]

/-- A containing coordinate slab gives explicit coercivity for the full
Sobolev norm. A unit-width slab gives the constant `1/2` in every dimension. -/
theorem dirichletForm_coercive_bound_of_slab
    {n : ℕ} {Ω : Set (ℝ^(n + 1))} (i : Fin (n + 1)) {a b : ℝ}
    (hΩ : Ω ⊆ {x | x i ∈ Icc a b}) (u : H¹₀(Ω)) :
    ‖u‖ ^ 2 / ((volume (Icc a b)).toReal ^ 2 + 1) ≤ dirichletForm u u := by
  have hP := norm_baseCoord_le_measure_mul_derivCoord_of_slab i hΩ u
  have hsq := (sq_le_sq₀ (norm_nonneg (baseCoordCLM u))
    (mul_nonneg ENNReal.toReal_nonneg (norm_nonneg (derivCoordCLM i u)))).mpr hP
  rw [mul_pow] at hsq
  have hi : ‖derivCoordCLM i u‖ ^ 2 ≤
      ∑ j : Fin (n + 1), ‖derivCoordCLM j u‖ ^ 2 :=
    Finset.single_le_sum (f := fun j ↦ ‖derivCoordCLM j u‖ ^ 2)
      (fun j _ ↦ sq_nonneg ‖derivCoordCLM j u‖) (Finset.mem_univ i)
  have hmass := hsq.trans
    (mul_le_mul_of_nonneg_left hi (sq_nonneg (volume (Icc a b)).toReal))
  rw [norm_sq_eq_base_sq_add_sum_deriv_sq, dirichletForm_self_eq_sum_norm_sq,
    div_le_iff₀ (by positivity)]
  nlinarith [hmass]

/-- The continuous mass bilinear form `(u, v) ↦ ⟪P u, P v⟫` induced by a norm-nonincreasing
linear map `P` into `L²(Ω)`. -/
def massFormCLMOf
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : V →L[ℝ] L2) (hP : ∀ u, ‖P u‖ ≤ ‖u‖) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ
    (fun u v ↦ ⟪P u, P v⟫_ℝ)
    (by intro u₁ u₂ v; simp [inner_add_left])
    (by intro c u v; simp [real_inner_smul_left])
    (by intro u v₁ v₂; simp [inner_add_right])
    (by intro c u v; simp [real_inner_smul_right])).mkContinuous₂ 1 <| by
    intro u v
    calc
      ‖⟪P u, P v⟫_ℝ‖ ≤ ‖P u‖ * ‖P v‖ := by
        simpa [Real.norm_eq_abs] using
          abs_real_inner_le_norm (P u) (P v)
      _ ≤ ‖u‖ * ‖v‖ :=
        mul_le_mul (hP u) (hP v) (norm_nonneg _) (norm_nonneg _)
      _ = (1 : ℝ) * ‖u‖ * ‖v‖ := by ring

/-- The continuous `L²` mass bilinear form on `H¹₀(Ω)`. -/
def massFormCLM : H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
  massFormCLMOf (n := n) (Ω := Ω) H¹₀(Ω)
    (baseCoordCLM (n := n) (Ω := Ω))
    (baseCoordCLM_norm_le (n := n) (Ω := Ω))

/-- Unfolding the mass form: `M(u,v) = ⟪u, v⟫_{L²}`, computed on the base coordinates. -/
@[simp]
theorem massFormCLM_apply (u v : H¹₀(Ω)) :
    massFormCLM (n := n) (Ω := Ω) u v =
      ⟪baseCoordCLM (n := n) (Ω := Ω) u,
        baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ :=
  rfl

end QuadraticForms

section Coercivity


private theorem dirichletForm_isCoercive_of_poincare
    (C : ℝ≥0)
    (hPoincare : ∀ u : H¹₀(Ω),
      ‖(((u : H¹(Ω)) : WkpAmbientOn n 1 2 Ω) (baseIndex n 1))‖ ≤
        (C : ℝ) * ∑ i : Fin n,
          ‖(((u : H¹(Ω)) : WkpAmbientOn n 1 2 Ω)
              (singleDerivIndex (n := n) i))‖) :
    IsCoercive
      (dirichletForm (n := n) (Ω := Ω)) := by
  have hK : (0 : ℝ) < (C : ℝ) ^ 2 * n + 1 := by positivity
  refine ⟨1 / ((C : ℝ) ^ 2 * n + 1), one_div_pos.2 hK, fun u ↦ ?_⟩
  have hP : ‖baseCoordCLM (n := n) (Ω := Ω) u‖ ≤
      (C : ℝ) * ∑ i : Fin n, ‖derivCoordCLM (n := n) (Ω := Ω) i u‖ := by
    simpa only [baseCoordCLM_apply, derivCoordCLM_apply] using hPoincare u
  have hbase : ‖baseCoordCLM (n := n) (Ω := Ω) u‖ ^ 2 ≤
      (C : ℝ) ^ 2 * (n * ∑ i : Fin n, ‖derivCoordCLM (n := n) (Ω := Ω) i u‖ ^ 2) := calc
    _ ≤ ((C : ℝ) * ∑ i : Fin n, ‖derivCoordCLM (n := n) (Ω := Ω) i u‖) ^ 2 := by gcongr
    _ ≤ _ := by
      rw [mul_pow]
      gcongr
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun i : Fin n ↦ ‖derivCoordCLM (n := n) (Ω := Ω) i u‖)
  rw [dirichletForm_self_eq_sum_norm_sq, mul_assoc, ← sq, one_div_mul_eq_div, div_le_iff₀ hK,
    norm_sq_eq_base_sq_add_sum_deriv_sq]
  linarith

/-- Coercivity of the Dirichlet form on a bounded domain in every positive dimension. -/
theorem dirichletForm_isCoercive
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω) :
    IsCoercive
      (dirichletForm (n := n) (Ω := Ω)) := by
  rcases exists_poincare_H10 (n := n) (Ω := Ω) hn hΩbounded with
    ⟨C, hPoincare⟩
  exact dirichletForm_isCoercive_of_poincare
    (n := n) (Ω := Ω) C hPoincare

end Coercivity

end GraphSpace

end SobolevSpace
