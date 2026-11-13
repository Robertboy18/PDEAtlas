/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.WeakSolution
public import PDE.Elliptic.Variational.PrincipalForms
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.ExtensionByZero
import PDE.Analysis.MeasureTheory.Lp.ConstantMultiplier

/-!
# Divergence-form bilinear forms and ellipticity

Let `V = H¹₀(Ω)`.  A bounded coefficient matrix acts on derivative coordinates through
operators

`Aᵢⱼ : L²(Ω) →L[ℝ] L²(Ω)`.

The associated form is

`Bₐ(u,v) = ∑ᵢ ∑ⱼ ⟪Aᵢⱼ (∂ⱼ u), ∂ᵢ v⟫`.

Boundedness of the coefficient operators makes this form continuous. Ellipticity has a
different job: it bounds the form below by the gradient energy. On a bounded domain in
positive dimension, the zero-boundary Poincaré inequality then controls the full `H¹` norm,
giving the coercivity used by Lax-Milgram.

Measurable `L∞` coefficient fields enter through pointwise multiplication. The theorem
`integratedElliptic_multiplication_of_ae` integrates their almost-everywhere quadratic-form bound,
the uniform ellipticity condition (4) of Evans's §6.1.1, to obtain the energy inequality. For such
coefficients the form is the principal part of Evans's bilinear form (8) in §6.1.2.
`IsWeakDivergenceSolution` is the identity (7) with `b = 0` and `c = 0`, tested against compactly
supported smooth functions, and `isWeakSolution_iff_isWeakDivergenceSolution` identifies it with the
weak formulation (9). General bounded coefficient operators may be nonlocal; the abstract form alone
gives neither a pointwise differential equation nor regularity of its weak solution.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.1.1, (2), the symmetry condition and (4), pp. 311-312;
  §6.1.2, (7)-(9), p. 314; §6.3.1, step 4 of the proof of Theorem 1, (19), p. 330; §6.3.2, step 5 of
  the proof of Theorem 4, (52)-(55), pp. 336-337.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Sobolev

@[expose] public section

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open PDE.Analysis.Variational
open scoped Topology NNReal InnerProductSpace

namespace GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}


section Coefficients

local notation "L2" => DerivLp n 2 Ω

/-- A measurable essentially bounded matrix field, acting by pointwise multiplication on
each `L²` derivative coordinate. -/
def multiplicationCoefficientOperator
    (a : Fin n → Fin n → DerivLp n ∞ Ω) :
    (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)) :=
  fun i j ↦ mulLpLeft (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) (a i j)

/-- A multiplication coefficient acts on `L²(Ω)` through the scalar action of `L∞(Ω)`:
`Aᵢⱼ u = aᵢⱼ • u`. -/
@[simp]
theorem multiplicationCoefficientOperator_apply
    (a : Fin n → Fin n → DerivLp n ∞ Ω) (i j : Fin n) (u : L2) :
    multiplicationCoefficientOperator (n := n) (Ω := Ω) a i j u = a i j • u :=
  rfl

/-- Pointwise representative of the multiplication-coefficient action. -/
theorem multiplicationCoefficientOperator_apply_ae
    (a : Fin n → Fin n → DerivLp n ∞ Ω) (i j : Fin n) (u : L2) :
    ((multiplicationCoefficientOperator (n := n) (Ω := Ω) a i j u : L2) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦ a i j x * u x :=
  mulLpLeft_apply_ae (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) (a i j) u

/-- The identity coefficient matrix.  Its associated operator is the identity on diagonal
entries and zero off the diagonal. -/
def identityCoefficientOperator :
    (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)) :=
  fun i j ↦ if i = j then ContinuousLinearMap.id ℝ L2 else 0

/-- A coefficient field represented by the identity matrix induces the identity operators. -/
theorem multiplicationCoefficientOperator_eq_identity_of_ae
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (ha : ∀ i j, (a i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun _ ↦ if i = j then 1 else 0) :
    multiplicationCoefficientOperator a = identityCoefficientOperator := by
  classical
  funext i j
  apply ContinuousLinearMap.ext
  intro u
  rw [multiplicationCoefficientOperator_apply, Lp.lpSMul_eq_const_smul _ _ (ha i j)]
  by_cases h : i = j <;> simp [identityCoefficientOperator, h]

/-- The bilinear pairing `(u, v) ↦ ∑ᵢ ∑ⱼ ⟪A i j (D j u), E i v⟫` of a coefficient matrix with
two families of derivative coordinate maps, before continuity is established. -/
def variableCoeffFormLinOf
    (U V : Type*)
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (D : Fin n → U →L[ℝ] L2) (E : Fin n → V →L[ℝ] L2)
    (A : Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)) :
    U →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun u v ↦
      ∑ i : Fin n, ∑ j : Fin n,
        ⟪A i j (D j u), E i v⟫_ℝ)
    (by
      intro u₁ u₂ v
      classical
      simp [Finset.sum_add_distrib, inner_add_left])
    (by
      intro c u v
      classical
      simp only [map_smul, real_inner_smul_left]
      simp [Finset.mul_sum])
    (by
      intro u v₁ v₂
      classical
      simp [Finset.sum_add_distrib, inner_add_right])
    (by
      intro c u v
      classical
      simp only [map_smul, real_inner_smul_right]
      simp [Finset.mul_sum])

/-- The continuous bilinear form of a bounded coefficient matrix against two families of
norm-nonincreasing derivative coordinate maps. -/
def variableCoeffFormOf
    (U V : Type*)
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (D : Fin n → U →L[ℝ] L2) (hD : ∀ i u, ‖D i u‖ ≤ ‖u‖)
    (E : Fin n → V →L[ℝ] L2) (hE : ∀ i v, ‖E i v‖ ≤ ‖v‖)
    (A : Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)) :
    U →L[ℝ] V →L[ℝ] ℝ :=
  (variableCoeffFormLinOf (n := n) (Ω := Ω) U V D E A).mkContinuous₂
    (∑ i : Fin n, ∑ j : Fin n, ‖A i j‖) <| by
      classical
      intro u v
      have hterm : ∀ i j : Fin n,
          ‖⟪A i j (D j u), E i v⟫_ℝ‖ ≤
            ‖A i j‖ * ‖u‖ * ‖v‖ := by
        intro i j
        calc
          ‖⟪A i j (D j u), E i v⟫_ℝ‖
              ≤ ‖A i j (D j u)‖ * ‖E i v‖ := by
                simpa [Real.norm_eq_abs] using
                  abs_real_inner_le_norm (A i j (D j u)) (E i v)
          _ ≤ (‖A i j‖ * ‖D j u‖) * ‖E i v‖ := by
                exact mul_le_mul_of_nonneg_right
                  (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
          _ ≤ (‖A i j‖ * ‖D j u‖) * ‖v‖ := by
                exact mul_le_mul_of_nonneg_left
                  (hE i v)
                  (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          _ ≤ (‖A i j‖ * ‖u‖) * ‖v‖ := by
                gcongr
                exact hD j u
          _ = ‖A i j‖ * ‖u‖ * ‖v‖ := rfl
      calc
        ‖∑ i : Fin n, ∑ j : Fin n,
            ⟪A i j (D j u), E i v⟫_ℝ‖
            ≤ ∑ i : Fin n, ∑ j : Fin n,
                ‖⟪A i j (D j u), E i v⟫_ℝ‖ := by
              exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ norm_sum_le _ _)
        _ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖A i j‖ * ‖u‖ * ‖v‖ := by
              exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hterm i j
        _ = (∑ i : Fin n, ∑ j : Fin n, ‖A i j‖) * ‖u‖ * ‖v‖ := by
              simp only [Finset.sum_mul]

/-- Evaluating the bounded form pairs the coefficient operators with the two
families of coordinate maps. -/
@[simp]
theorem variableCoeffFormOf_apply
    (U V : Type*)
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (D : Fin n → U →L[ℝ] L2) (hD : ∀ i u, ‖D i u‖ ≤ ‖u‖)
    (E : Fin n → V →L[ℝ] L2) (hE : ∀ i v, ‖E i v‖ ≤ ‖v‖)
    (A : Fin n → Fin n → (L2 →L[ℝ] L2)) (u : U) (v : V) :
    variableCoeffFormOf U V D hD E hE A u v =
      ∑ i : Fin n, ∑ j : Fin n, ⟪A i j (D j u), E i v⟫_ℝ :=
  rfl

/-- The norm of the form is bounded by the sum of the coefficient operator norms
when every coordinate map is norm-nonincreasing. -/
theorem norm_variableCoeffFormOf_le
    (U V : Type*)
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (D : Fin n → U →L[ℝ] L2) (hD : ∀ i u, ‖D i u‖ ≤ ‖u‖)
    (E : Fin n → V →L[ℝ] L2) (hE : ∀ i v, ‖E i v‖ ≤ ‖v‖)
    (A : Fin n → Fin n → (L2 →L[ℝ] L2)) :
    ‖variableCoeffFormOf U V D hD E hE A‖ ≤
      ∑ i : Fin n, ∑ j : Fin n, ‖A i j‖ := by
  unfold variableCoeffFormOf
  apply LinearMap.mkContinuous₂_norm_le
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

private theorem variableCoeffFormOf_norm_apply_le
    (U V : Type*)
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (D : Fin n → U →L[ℝ] L2) (hD : ∀ i u, ‖D i u‖ ≤ ‖u‖)
    (E : Fin n → V →L[ℝ] L2) (hE : ∀ i v, ‖E i v‖ ≤ ‖v‖)
    (A : Fin n → Fin n → (L2 →L[ℝ] L2)) (u : U) :
    ‖variableCoeffFormOf U V D hD E hE A u‖ ≤
      (∑ i : Fin n, ∑ j : Fin n, ‖A i j‖) * ‖u‖ :=
  (variableCoeffFormOf U V D hD E hE A).le_of_opNorm_le
    (norm_variableCoeffFormOf_le U V D hD E hE A) u

/-- The continuous bilinear form associated with a bounded coefficient matrix. -/
def variableCoeffForm (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) :
    H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
  variableCoeffFormOf (n := n) (Ω := Ω) H¹₀(Ω) H¹₀(Ω)
    (fun i ↦ derivCoordCLM (n := n) (Ω := Ω) i)
    (fun i u ↦ derivCoordCLM_norm_le (n := n) (Ω := Ω) i u)
    (fun i ↦ derivCoordCLM (n := n) (Ω := Ω) i)
    (fun i u ↦ derivCoordCLM_norm_le (n := n) (Ω := Ω) i u) A

/-- The divergence-form bilinear form with an arbitrary `H¹(Ω)` state and an
`H¹₀(Ω)` test. This is the natural form for local weak solutions, where no trace
condition is imposed on the state. -/
def interiorVariableCoeffForm
    (A : Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)) :
    H¹(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
  variableCoeffFormOf (n := n) (Ω := Ω) H¹(Ω) H¹₀(Ω)
    (fun i ↦
      wkpCoordinateCLM
        (n := n) (m := 1) (p := 2) (Ω := Ω)
        (singleDerivIndex (n := n) i))
    (fun i u ↦
      wkpCoordinateCLM_norm_le
        (n := n) (m := 1) (p := 2) (Ω := Ω)
        (singleDerivIndex (n := n) i) u)
    (fun i ↦ derivCoordCLM (n := n) (Ω := Ω) i)
    (fun i v ↦ derivCoordCLM_norm_le (n := n) (Ω := Ω) i v) A

/-- Unfolding the variable-coefficient form on `H¹₀(Ω)`:
`Bₐ(u,v) = ∑ᵢ ∑ⱼ ⟪Aᵢⱼ ∂ⱼu, ∂ᵢv⟫_{L²}`, with the weak derivatives read off the derivative
coordinates. -/
@[simp]
theorem variableCoeffForm_apply (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (u v : H¹₀(Ω)) :
    variableCoeffForm (n := n) (Ω := Ω) A u v =
      ∑ i : Fin n, ∑ j : Fin n,
        ⟪A i j (derivCoordCLM (n := n) (Ω := Ω) j u),
          derivCoordCLM (n := n) (Ω := Ω) i v⟫_ℝ :=
  rfl

/-- Unfolding the interior form, whose first argument ranges over `H¹(Ω)` and whose test
argument over `H¹₀(Ω)`. The weak derivatives of the `H¹` argument are read off the ambient
graph-space coordinates `wkpCoordinateCLM`, those of the test function off `derivCoordCLM`. -/
@[simp]
theorem interiorVariableCoeffForm_apply
    (A : Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))
    (u : H¹(Ω)) (v : H¹₀(Ω)) :
    interiorVariableCoeffForm (n := n) (Ω := Ω) A u v =
      ∑ i : Fin n, ∑ j : Fin n,
        ⟪A i j
            (wkpCoordinateCLM
              (n := n) (m := 1) (p := 2) (Ω := Ω)
              (singleDerivIndex (n := n) j) u),
          derivCoordCLM (n := n) (Ω := Ω) i v⟫_ℝ :=
  rfl

/-- Identity coefficients pair the weak gradient with that of the zero-boundary test. -/
theorem interiorVariableCoeffForm_identity (u : H¹(Ω)) (v : H¹₀(Ω)) :
    interiorVariableCoeffForm identityCoefficientOperator u v =
      ∑ i, ∫ x, wkpCoordinateCLM (singleDerivIndex n i) u x * derivCoordCLM i v x
        ∂domainMeasure n Ω := by
  classical
  simp only [interiorVariableCoeffForm_apply, identityCoefficientOperator]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp only [ite_true, ContinuousLinearMap.id_apply, L2.inner_def]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      simp only [RCLike.inner_apply, conj_trivial]
      exact mul_comm _ _
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

/-- Restricting the interior form to a zero-trace state recovers the standard
Dirichlet bilinear form. -/
theorem interiorVariableCoeffForm_h10SubtypeL
    (A : Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))
    (u v : H¹₀(Ω)) :
    interiorVariableCoeffForm (n := n) (Ω := Ω) A
        (h10SubtypeL (n := n) (Ω := Ω) u) v =
      variableCoeffForm (n := n) (Ω := Ω) A u v :=
  rfl

/-- The coefficient operator norms bound the dual norm of the associated
divergence-form operator. -/
theorem norm_variableCoeffForm_apply_le
    (A : Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))
    (u : H¹₀(Ω)) :
    ‖variableCoeffForm (n := n) (Ω := Ω) A u‖ ≤
      (∑ i : Fin n, ∑ j : Fin n, ‖A i j‖) * ‖u‖ := by
  unfold variableCoeffForm
  apply variableCoeffFormOf_norm_apply_le

/-- The coefficient operator norms bound the interior form in its `H¹` state. -/
theorem norm_interiorVariableCoeffForm_apply_le
    (A : Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))
    (u : H¹(Ω)) :
    ‖interiorVariableCoeffForm (n := n) (Ω := Ω) A u‖ ≤
      (∑ i : Fin n, ∑ j : Fin n, ‖A i j‖) * ‖u‖ := by
  unfold interiorVariableCoeffForm
  apply variableCoeffFormOf_norm_apply_le

/-- Zero coefficients give the zero bilinear form. -/
@[simp]
theorem variableCoeffForm_zero :
    variableCoeffForm (n := n) (Ω := Ω)
      (0 : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) = 0 := by
  ext u v
  simp [variableCoeffForm_apply]

/-- The variable-coefficient form is additive in the coefficient matrix. -/
theorem variableCoeffForm_add_apply
    (A B : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (u v : H¹₀(Ω)) :
    variableCoeffForm (n := n) (Ω := Ω) (A + B) u v =
      variableCoeffForm (n := n) (Ω := Ω) A u v +
        variableCoeffForm (n := n) (Ω := Ω) B u v := by
  simp [variableCoeffForm_apply, Finset.sum_add_distrib, inner_add_left]

/-- The variable-coefficient form commutes with coefficient negation. -/
theorem variableCoeffForm_neg_apply
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (u v : H¹₀(Ω)) :
    variableCoeffForm (n := n) (Ω := Ω) (-A) u v =
      -variableCoeffForm (n := n) (Ω := Ω) A u v := by
  simp [variableCoeffForm_apply]

/-- The variable-coefficient form is subtractive in the coefficient matrix. -/
theorem variableCoeffForm_sub_apply
    (A B : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (u v : H¹₀(Ω)) :
    variableCoeffForm (n := n) (Ω := Ω) (A - B) u v =
      variableCoeffForm (n := n) (Ω := Ω) A u v -
        variableCoeffForm (n := n) (Ω := Ω) B u v := by
  rw [sub_eq_add_neg, variableCoeffForm_add_apply, variableCoeffForm_neg_apply]
  simp [sub_eq_add_neg]

/-- The variable-coefficient form is homogeneous in the coefficient matrix. -/
theorem variableCoeffForm_smul_apply
    (c : ℝ) (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (u v : H¹₀(Ω)) :
    variableCoeffForm (n := n) (Ω := Ω) (c • A) u v =
      c * variableCoeffForm (n := n) (Ω := Ω) A u v := by
  simp [variableCoeffForm_apply, Finset.mul_sum, real_inner_smul_left]

/-- The identity coefficient matrix recovers the usual Dirichlet form exactly. -/
theorem variableCoeffForm_identity (u v : H¹₀(Ω)) :
    variableCoeffForm (n := n) (Ω := Ω)
        (identityCoefficientOperator (n := n) (Ω := Ω)) u v =
      dirichletForm (n := n) (Ω := Ω) u v := by
  rw [variableCoeffForm_apply, dirichletForm_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_eq_single i]
  · simp [identityCoefficientOperator]
  · intro j _hj hji
    have hij : i ≠ j := Ne.symm hji
    simp [identityCoefficientOperator, hij]
  · simp

/-- Symmetry of the coefficient operator in the weak bilinear form sense. For multiplication
coefficients this is the integrated counterpart of the pointwise condition `aᵢⱼ = aⱼᵢ`. -/
def SymmetricCoefficientOperator
    (A : Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)) : Prop :=
  ∀ i j : Fin n, ∀ u v : L2,
    ⟪A i j u, v⟫_ℝ = ⟪A j i v, u⟫_ℝ

/-- The symmetry condition `aᵢⱼ = aⱼᵢ` of Evans's §6.1.1, almost everywhere, for a
measurable coefficient matrix. -/
def AESymmetricCoefficient (a : Fin n → Fin n → DerivLp n ∞ Ω) : Prop :=
  ∀ i j : Fin n, (a i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (a j i : ℝ^n → ℝ)

/-- The identity coefficient operator is symmetric. -/
theorem symmetricCoefficientOperator_identity :
    SymmetricCoefficientOperator (n := n) (Ω := Ω)
      (identityCoefficientOperator (n := n) (Ω := Ω)) := by
  intro i j u v
  by_cases hij : i = j
  · subst j
    simp [identityCoefficientOperator, real_inner_comm]
  · have hji : j ≠ i := Ne.symm hij
    simp [identityCoefficientOperator, hij, hji]

/-- Almost-everywhere symmetry of a multiplication coefficient matrix gives symmetry of the
operator-valued weak bilinear form coefficients. -/
theorem symmetricCoefficientOperator_multiplication_of_ae
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (ha : AESymmetricCoefficient (n := n) (Ω := Ω) a) :
    SymmetricCoefficientOperator (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) := by
  intro i j u v
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [multiplicationCoefficientOperator_apply_ae
      (n := n) (Ω := Ω) a i j u,
     multiplicationCoefficientOperator_apply_ae
      (n := n) (Ω := Ω) a j i v,
     ha i j] with x hleft hright hsymm
  rw [hleft, hright, hsymm]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- A symmetric coefficient operator gives a symmetric weak bilinear form. -/
theorem variableCoeffForm_symm
    {A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))}
    (hA : SymmetricCoefficientOperator (n := n) (Ω := Ω) A)
    (u v : H¹₀(Ω)) :
    variableCoeffForm (n := n) (Ω := Ω) A u v =
      variableCoeffForm (n := n) (Ω := Ω) A v u := by
  rw [variableCoeffForm_apply, variableCoeffForm_apply]
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        ⟪A i j (derivCoordCLM (n := n) (Ω := Ω) j u),
          derivCoordCLM (n := n) (Ω := Ω) i v⟫_ℝ)
        =
      ∑ i : Fin n, ∑ j : Fin n,
        ⟪A j i (derivCoordCLM (n := n) (Ω := Ω) i v),
          derivCoordCLM (n := n) (Ω := Ω) j u⟫_ℝ := by
          exact Finset.sum_congr rfl fun i _ ↦
            Finset.sum_congr rfl fun j _ ↦
              hA i j
                (derivCoordCLM (n := n) (Ω := Ω) j u)
                (derivCoordCLM (n := n) (Ω := Ω) i v)
    _ =
      ∑ j : Fin n, ∑ i : Fin n,
        ⟪A j i (derivCoordCLM (n := n) (Ω := Ω) i v),
          derivCoordCLM (n := n) (Ω := Ω) j u⟫_ℝ := by
          exact Finset.sum_comm
    _ =
      ∑ i : Fin n, ∑ j : Fin n,
        ⟪A i j (derivCoordCLM (n := n) (Ω := Ω) j v),
          derivCoordCLM (n := n) (Ω := Ω) i u⟫_ℝ := rfl

/-- Integrated uniform ellipticity of the coefficient matrix on `H¹₀(Ω)`.

For multiplication operators induced by a measurable matrix field, the usual pointwise condition
`xiᵀ A(x) xi ≥ alpha |xi|²` almost everywhere implies this predicate by integration. -/
def IntegratedElliptic
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (alpha : ℝ) : Prop :=
  0 < alpha ∧ ∀ u : H¹₀(Ω),
    alpha * dirichletForm (n := n) (Ω := Ω) u u ≤
      variableCoeffForm (n := n) (Ω := Ω) A u u

/-- The uniform ellipticity condition (4) of Evans's §6.1.1, for a.e. `x` and all
`ξ`, for a measurable coefficient matrix. The quantifier order `∀ᵐ x, ∀ ξ` permits
specialization to vectors that depend measurably on `x`. -/
def AEUniformlyElliptic
    (a : Fin n → Fin n → DerivLp n ∞ Ω) (alpha : ℝ) : Prop :=
  0 < alpha ∧
    ∀ᵐ x ∂domainMeasure n Ω, ∀ ξ : Fin n → ℝ,
      alpha * ∑ i : Fin n, ξ i * ξ i ≤
        ∑ i : Fin n, ∑ j : Fin n, a i j x * ξ j * ξ i

/-- Every diagonal entry of an almost-everywhere uniformly elliptic matrix is
bounded below by the ellipticity constant.  This is the coordinate-vector
specialization used to divide by the normal coefficient in the boundary `H²`
argument, as with (54) in step 5 of Evans's proof of §6.3.2, Theorem 4. -/
theorem aeUniformlyElliptic_diagonal_lower_bound
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha) (k : Fin n) :
    ∀ᵐ x ∂domainMeasure n Ω, alpha ≤ a k k x := by
  filter_upwards [ha.2] with x hx
  have h := hx (fun i ↦ if i = k then (1 : ℝ) else 0)
  simpa [Finset.mul_sum, Finset.sum_mul] using h

/-- Pointwise uniform ellipticity controls every finite `L²` vector field,
not only vector fields already known to be gradients. This is the form used
with `vᵢ = Dₖʰ(∂ᵢu)` for the bound (19) in step 4 of Evans's proof of §6.3.1,
Theorem 1. -/
theorem aeUniformlyElliptic_energy_le
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (v : Fin n → DerivLp n 2 Ω) :
    alpha * ∑ i : Fin n, inner ℝ (v i) (v i) ≤
      ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ
          (multiplicationCoefficientOperator (n := n) (Ω := Ω) a i j (v j))
          (v i) := by
  classical
  have hpt (i j : Fin n) :
      (fun x ↦ inner ℝ ((multiplicationCoefficientOperator (n := n) (Ω := Ω) a i j (v j) : L2) x)
        (v i x)) =ᵐ[domainMeasure n Ω] fun x ↦ a i j x * v j x * v i x := by
    filter_upwards [multiplicationCoefficientOperator_apply_ae (n := n) (Ω := Ω) a i j (v j)]
      with x hx
    rw [hx]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hdiag (i : Fin n) : Integrable (fun x ↦ v i x * v i x) (domainMeasure n Ω) :=
    (L2.integrable_inner (𝕜 := ℝ) (v i) (v i)).congr (.of_forall fun x ↦ by simp [pow_two])
  have hcoeff (i j : Fin n) :
      Integrable (fun x ↦ a i j x * v j x * v i x) (domainMeasure n Ω) :=
    (L2.integrable_inner (𝕜 := ℝ) _ (v i)).congr (hpt i j)
  calc
    alpha * ∑ i : Fin n, inner ℝ (v i) (v i) =
        ∫ x, alpha * ∑ i : Fin n, v i x * v i x ∂domainMeasure n Ω := by
      rw [integral_const_mul, integral_finsetSum Finset.univ fun i _ ↦ hdiag i]
      congr 1
    _ ≤ ∫ x, ∑ i : Fin n, ∑ j : Fin n, a i j x * v j x * v i x ∂domainMeasure n Ω :=
      integral_mono_ae ((integrable_finsetSum _ fun i _ ↦ hdiag i).const_mul alpha)
        (integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hcoeff i j)
        (by filter_upwards [ha.2] with x hx using hx fun i ↦ v i x)
    _ = _ := by
      rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hcoeff i j]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [integral_finsetSum _ fun j _ ↦ hcoeff i j]
      exact Finset.sum_congr rfl fun j _ ↦ by
        rw [L2.inner_def]
        exact (integral_congr_ae (hpt i j)).symm

/-- The pointwise condition (4) of Evans's §6.1.1, for almost every `x`, implies
integrated uniform ellipticity of the multiplication operator. -/
theorem integratedElliptic_multiplication_of_ae
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha) :
    IntegratedElliptic (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) alpha := by
  refine ⟨ha.1, ?_⟩
  intro u
  let du : Fin n → DerivLp n 2 Ω := fun i ↦
    derivCoordCLM (n := n) (Ω := Ω) i u
  simpa [dirichletForm_apply, variableCoeffForm_apply, du] using
    aeUniformlyElliptic_energy_le (n := n) (Ω := Ω) a ha du

/-- The identity coefficient matrix is uniformly elliptic with constant one. -/
theorem integratedElliptic_identity :
    IntegratedElliptic (n := n) (Ω := Ω)
      (identityCoefficientOperator (n := n) (Ω := Ω)) 1 := by
  refine ⟨by norm_num, fun u ↦ ?_⟩
  rw [variableCoeffForm_identity]
  simp

/-- One multiplication-coefficient term against a smooth test derivative is
the usual integral `∫ aᵢⱼ ∂ⱼu ∂ᵢφ`. -/
theorem inner_multiplicationCoefficient_testFunction_eq_integral
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (u : H¹₀(Ω)) (i j : Fin n) (φ : TestFunctionOn n Ω) :
    ⟪multiplicationCoefficientOperator (n := n) (Ω := Ω) a i j
        (derivCoordCLM (n := n) (Ω := Ω) j u),
      derivCoordCLM (n := n) (Ω := Ω) i
        (testFunctionToH10 (n := n) (Ω := Ω) φ)⟫_ℝ =
      ∫ x, a i j x *
          (derivCoordCLM (n := n) (Ω := Ω) j u : ℝ^n → ℝ) x *
          (∂[i] φ.1.toFun) x
        ∂domainMeasure n Ω := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [multiplicationCoefficientOperator_apply_ae
      (n := n) (Ω := Ω) a i j
      (derivCoordCLM (n := n) (Ω := Ω) j u),
     derivCoordCLM_testFunction_apply_ae
      (n := n) (Ω := Ω) i φ] with x hcoeff htest
  rw [hcoeff, htest]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- One multiplication-coefficient term against an arbitrary `H1_0` test
function is the expected integral.  This is the nonsmooth companion to
`inner_multiplicationCoefficient_testFunction_eq_integral`, needed when a
smooth test is pulled through a merely C1 boundary chart. -/
theorem inner_multiplicationCoefficient_eq_integral
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (u v : H¹₀(Ω)) (i j : Fin n) :
    ⟪multiplicationCoefficientOperator (n := n) (Ω := Ω) a i j
        (derivCoordCLM (n := n) (Ω := Ω) j u),
      derivCoordCLM (n := n) (Ω := Ω) i v⟫_ℝ =
      ∫ x, a i j x *
          (derivCoordCLM (n := n) (Ω := Ω) j u : ℝ^n → ℝ) x *
          (derivCoordCLM (n := n) (Ω := Ω) i v : ℝ^n → ℝ) x
        ∂domainMeasure n Ω := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [multiplicationCoefficientOperator_apply_ae
      (n := n) (Ω := Ω) a i j
      (derivCoordCLM (n := n) (Ω := Ω) j u)] with x hcoeff
  rw [hcoeff]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- The `L2` forcing pairing against an arbitrary `H1_0` test function is
its standard integral representative. -/
theorem inner_base_eq_integral
    (f : DerivLp n 2 Ω) (v : H¹₀(Ω)) :
    ⟪f, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ =
      ∫ x, (f : ℝ^n → ℝ) x *
          (baseCoordCLM (n := n) (Ω := Ω) v : ℝ^n → ℝ) x
        ∂domainMeasure n Ω := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  simp [RCLike.inner_apply, mul_comm]

/-- Restricting the state, coefficients, and forcing to an open subset
commutes with testing against a function supported in that subset. -/
theorem interiorVariableCoeffForm_restrict
    {V : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (hVΩ : V ⊆ Ω) (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (u : H¹(Ω)) (v : H¹₀(V)) :
    interiorVariableCoeffForm (n := n) (Ω := V)
        (multiplicationCoefficientOperator (n := n) (Ω := V)
          (fun i j ↦
            restrictDerivLp (n := n) (p := ∞) hVΩ (a i j)))
        (restrictCLM (n := n) (k := 1) (p := 2)
          hVopen.measurableSet hVΩ u) v =
      interiorVariableCoeffForm (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) u
        (ZeroTrace.zeroExtendH10ToSuperset
          (n := n) hVopen hΩopen hVΩ v) := by
  classical
  rw [interiorVariableCoeffForm_apply, interiorVariableCoeffForm_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  have hstate :
      wkpCoordinateCLM
          (n := n) (m := 1) (p := 2) (Ω := V)
          (singleDerivIndex (n := n) j)
          (restrictCLM (n := n) (k := 1) (p := 2)
            hVopen.measurableSet hVΩ u) =
        restrictDerivLp (n := n) (p := 2) hVΩ
          (wkpCoordinateCLM
            (n := n) (m := 1) (p := 2) (Ω := Ω)
            (singleDerivIndex (n := n) j) u) :=
    Lp.ext (by simp [wkpCoordinateCLM])
  rw [hstate, multiplicationCoefficientOperator_apply,
    multiplicationCoefficientOperator_apply,
    ← restrictDerivLp_lpSMul hVopen.measurableSet]
  exact
    (ZeroTrace.inner_zeroExtendH10ToSuperset_coordinate_eq_inner_restrict
      (n := n) hVopen hΩopen hVΩ
      (a i j •
        wkpCoordinateCLM
          (n := n) (m := 1) (p := 2) (Ω := Ω)
          (singleDerivIndex (n := n) j) u) v
      (singleDerivIndex (n := n) i)).symm

/-- Restricting an `L²` forcing term to an open subset commutes with testing
against zero extension from that subset. -/
theorem loadFunctional_restrict
    {V : Set (ℝ^n)} (hVopen : IsOpen V) (hΩopen : IsOpen Ω)
    (hVΩ : V ⊆ Ω) (f : DerivLp n 2 Ω)
    (v : H¹₀(V)) :
    loadFunctional (n := n) (Ω := V)
        (restrictDerivLp (n := n) (p := 2) hVΩ f) v =
      loadFunctional (n := n) (Ω := Ω) f
        (ZeroTrace.zeroExtendH10ToSuperset
          (n := n) hVopen hΩopen hVΩ v) := by
  rw [loadFunctional_apply, loadFunctional_apply]
  exact
    (ZeroTrace.inner_zeroExtendH10ToSuperset_coordinate_eq_inner_restrict
      (n := n) hVopen hΩopen hVΩ f v (baseIndex n 1)).symm

/-- A local weak solution belongs only to `H¹(Ω)` and satisfies the
divergence-form equation against every zero-trace `H¹` test. No boundary
condition is imposed on the state. -/
def IsInteriorWeakDivergenceSolution
    (a : Fin n → Fin n → DerivLp n ∞ Ω) (f : L2) (u : H¹(Ω)) : Prop :=
  IsOpen Ω ∧
    ∀ v : H¹₀(Ω),
      interiorVariableCoeffForm (n := n) (Ω := Ω)
          (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) u v =
        loadFunctional (n := n) (Ω := Ω) f v

/-- The domain of an interior weak solution is open. -/
theorem IsInteriorWeakDivergenceSolution.isOpen
    {a : Fin n → Fin n → DerivLp n ∞ Ω} {f : L2} {u : H¹(Ω)}
    (hu : IsInteriorWeakDivergenceSolution
      (n := n) (Ω := Ω) a f u) :
    IsOpen Ω :=
  hu.1

/-- The weak equation for an interior solution, evaluated at an arbitrary
zero-trace test. -/
theorem IsInteriorWeakDivergenceSolution.equation
    {a : Fin n → Fin n → DerivLp n ∞ Ω} {f : L2} {u : H¹(Ω)}
    (hu : IsInteriorWeakDivergenceSolution
      (n := n) (Ω := Ω) a f u)
    (v : H¹₀(Ω)) :
    interiorVariableCoeffForm (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) u v =
      loadFunctional (n := n) (Ω := Ω) f v :=
  hu.2 v

/-- An interior weak solution restricts to every smaller open subdomain. -/
theorem IsInteriorWeakDivergenceSolution.restrict
    {a : Fin n → Fin n → DerivLp n ∞ Ω} {f : L2} {u : H¹(Ω)}
    (hu : IsInteriorWeakDivergenceSolution
      (n := n) (Ω := Ω) a f u)
    {V : Set (ℝ^n)} (hVopen : IsOpen V) (hVΩ : V ⊆ Ω) :
    IsInteriorWeakDivergenceSolution
      (n := n) (Ω := V)
      (fun i j ↦
        restrictDerivLp (n := n) (p := ∞) hVΩ (a i j))
      (restrictDerivLp (n := n) (p := 2) hVΩ f)
      (restrictCLM (n := n) (k := 1) (p := 2)
        hVopen.measurableSet hVΩ u) := by
  refine ⟨hVopen, fun v ↦ ?_⟩
  calc
    interiorVariableCoeffForm (n := n) (Ω := V)
        (multiplicationCoefficientOperator (n := n) (Ω := V)
          (fun i j ↦
            restrictDerivLp (n := n) (p := ∞) hVΩ (a i j)))
        (restrictCLM (n := n) (k := 1) (p := 2)
          hVopen.measurableSet hVΩ u) v =
        interiorVariableCoeffForm (n := n) (Ω := Ω)
          (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) u
          (ZeroTrace.zeroExtendH10ToSuperset
            (n := n) hVopen hu.isOpen hVΩ v) :=
      interiorVariableCoeffForm_restrict
        (n := n) (Ω := Ω) hVopen hu.isOpen hVΩ a u v
    _ = loadFunctional (n := n) (Ω := Ω) f
          (ZeroTrace.zeroExtendH10ToSuperset
            (n := n) hVopen hu.isOpen hVΩ v) :=
      hu.2 _
    _ = loadFunctional (n := n) (Ω := V)
          (restrictDerivLp (n := n) (p := 2) hVΩ f) v :=
      (loadFunctional_restrict
        (n := n) (Ω := Ω) hVopen hu.isOpen hVΩ f v).symm

/-- The operator-valued weak equation evaluated at an arbitrary `H1_0`
test, written entirely as the standard divergence-form integral identity. -/
theorem weakSolution_eq_integral
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (f : DerivLp n 2 Ω) (u : H¹₀(Ω))
    (hu : IsWeakSolution
      (variableCoeffForm (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω) a))
      (loadFunctional (n := n) (Ω := Ω) f) u)
    (v : H¹₀(Ω)) :
    (∑ i : Fin n, ∑ j : Fin n,
      ∫ x, a i j x *
          (derivCoordCLM (n := n) (Ω := Ω) j u : ℝ^n → ℝ) x *
          (derivCoordCLM (n := n) (Ω := Ω) i v : ℝ^n → ℝ) x
        ∂domainMeasure n Ω) =
      ∫ x, (f : ℝ^n → ℝ) x *
          (baseCoordCLM (n := n) (Ω := Ω) v : ℝ^n → ℝ) x
        ∂domainMeasure n Ω := by
  have h := hu v
  change (∑ i : Fin n, ∑ j : Fin n,
      ⟪multiplicationCoefficientOperator (n := n) (Ω := Ω) a i j
          (derivCoordCLM (n := n) (Ω := Ω) j u),
        derivCoordCLM (n := n) (Ω := Ω) i v⟫_ℝ) =
    ⟪f, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ at h
  simpa only [inner_multiplicationCoefficient_eq_integral,
    inner_base_eq_integral] using h

/-- The weak formulation of
`-∂ᵢ(aᵢⱼ ∂ⱼu) = f` with homogeneous Dirichlet data on an open set, tested against
compactly supported smooth functions as in Evans's (7) of §6.1.2 with `b = 0` and
`c = 0`.

The openness field prevents a test-function identity on an arbitrary empty-interior measurable
set from being advertised as a distributional PDE. The coefficient is `L∞`
and all weak and test derivatives are `L²`, so every displayed product is
integrable; the definition does not use the fallback value of a totalized
integral. -/
structure IsWeakDivergenceSolution
    (a : Fin n → Fin n → DerivLp n ∞ Ω) (f : L2) (u : H¹₀(Ω)) : Prop where
  /-- The PDE domain is open. -/
  isOpen : IsOpen Ω
  /-- The divergence-form identity against every compactly supported smooth test function. -/
  equation : ∀ φ : TestFunctionOn n Ω,
      (∑ i : Fin n, ∑ j : Fin n,
        ∫ x, a i j x *
            (derivCoordCLM (n := n) (Ω := Ω) j u : ℝ^n → ℝ) x *
            (∂[i] φ.1.toFun) x
          ∂domainMeasure n Ω) =
        ∫ x, (f : ℝ^n → ℝ) x * φ.1.toFun x ∂domainMeasure n Ω

/-- A divergence-form weak solution can be applied directly to a test function. -/
instance {a : Fin n → Fin n → DerivLp n ∞ Ω} {f : L2} {u : H¹₀(Ω)} :
    CoeFun (IsWeakDivergenceSolution (n := n) (Ω := Ω) a f u)
      (fun _ ↦ ∀ φ : TestFunctionOn n Ω,
        (∑ i : Fin n, ∑ j : Fin n,
          ∫ x, a i j x *
              (derivCoordCLM (n := n) (Ω := Ω) j u : ℝ^n → ℝ) x *
              (∂[i] φ.1.toFun) x
            ∂domainMeasure n Ω) =
          ∫ x, (f : ℝ^n → ℝ) x * φ.1.toFun x ∂domainMeasure n Ω) where
  coe h := h.equation

/-- The operator-valued weak equation for a multiplication coefficient field
is equivalent to the standard distributional divergence-form identity. -/
theorem isWeakSolution_iff_isWeakDivergenceSolution
    (hΩopen : IsOpen Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) (f : L2) (u : H¹₀(Ω)) :
    IsWeakSolution
        (variableCoeffForm (n := n) (Ω := Ω)
          (multiplicationCoefficientOperator (n := n) (Ω := Ω) a))
        (loadFunctional (n := n) (Ω := Ω) f) u ↔
      IsWeakDivergenceSolution
        (n := n) (Ω := Ω) a f u := by
  refine ⟨fun hu ↦ ⟨hΩopen, fun φ ↦ ?_⟩, fun hu v ↦ ?_⟩
  · simpa only [variableCoeffForm_apply, loadFunctional_apply,
      inner_multiplicationCoefficient_testFunction_eq_integral,
      inner_base_testFunction_eq_integral] using hu (testFunctionToH10 (n := n) (Ω := Ω) φ)
  refine congrFun ((denseRange_testFunctionToH10Linear (n := n) (Ω := Ω)).equalizer
    (variableCoeffForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) u).continuous
    (loadFunctional (n := n) (Ω := Ω) f).continuous (funext fun φ ↦ ?_)) v
  change variableCoeffForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) u
      (testFunctionToH10 (n := n) (Ω := Ω) φ) =
    loadFunctional (n := n) (Ω := Ω) f (testFunctionToH10 (n := n) (Ω := Ω) φ)
  rw [variableCoeffForm_apply, loadFunctional_apply]
  simpa only [inner_multiplicationCoefficient_testFunction_eq_integral,
    inner_base_testFunction_eq_integral] using hu φ

/-- A zero-trace weak solution is, after forgetting its trace, an interior
weak solution of the same equation. -/
theorem IsWeakDivergenceSolution.toInterior
    {a : Fin n → Fin n → DerivLp n ∞ Ω} {f : L2} {u : H¹₀(Ω)}
    (hu : IsWeakDivergenceSolution (n := n) (Ω := Ω) a f u) :
    IsInteriorWeakDivergenceSolution (n := n) (Ω := Ω) a f
      (h10SubtypeL (n := n) (Ω := Ω) u) := by
  refine ⟨hu.isOpen, ?_⟩
  have hweak :=
    (isWeakSolution_iff_isWeakDivergenceSolution
      (n := n) (Ω := Ω) hu.isOpen a f u).2 hu
  intro v
  rw [interiorVariableCoeffForm_h10SubtypeL]
  exact hweak v

/--
Superposition for the divergence-form weak formulation with fixed coefficients.

The statement is phrased in the integral test-function language
`IsWeakDivergenceSolution`: if two loads are added, subtracted, or scaled, the
corresponding weak equations transform in the same way.  The proof passes through
the operator-valued formulation once, where this is just bilinearity of the form.
-/
theorem IsWeakDivergenceSolution.add
    {a : Fin n → Fin n → DerivLp n ∞ Ω} {f g : L2} {u v : H¹₀(Ω)}
    (hu : IsWeakDivergenceSolution (n := n) (Ω := Ω) a f u)
    (hv : IsWeakDivergenceSolution (n := n) (Ω := Ω) a g v) :
    IsWeakDivergenceSolution (n := n) (Ω := Ω) a (f + g) (u + v) := by
  let B : H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
    variableCoeffForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
  rw [← isWeakSolution_iff_isWeakDivergenceSolution (n := n) (Ω := Ω) hu.isOpen
    a (f + g) (u + v)]
  change IsWeakSolution B
    (loadFunctional (n := n) (Ω := Ω) (f + g)) (u + v)
  have hu' : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) f) u := by
    simpa only [B] using
      (isWeakSolution_iff_isWeakDivergenceSolution
        (n := n) (Ω := Ω) hu.isOpen a f u).2 hu
  have hv' : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) g) v := by
    simpa only [B] using
      (isWeakSolution_iff_isWeakDivergenceSolution
        (n := n) (Ω := Ω) hv.isOpen a g v).2 hv
  have h := hu'.add hv'
  intro w
  calc
    B (u + v) w =
        (loadFunctional (n := n) (Ω := Ω) f +
          loadFunctional (n := n) (Ω := Ω) g) w := h w
    _ = loadFunctional (n := n) (Ω := Ω) f w +
          loadFunctional (n := n) (Ω := Ω) g w := rfl
    _ = loadFunctional (n := n) (Ω := Ω) (f + g) w := by
      simp only [loadFunctional_apply, inner_add_left]

/-- Negating both the load and weak field preserves the divergence-form weak equation. -/
theorem IsWeakDivergenceSolution.neg
    {a : Fin n → Fin n → DerivLp n ∞ Ω} {f : L2} {u : H¹₀(Ω)}
    (hu : IsWeakDivergenceSolution (n := n) (Ω := Ω) a f u) :
    IsWeakDivergenceSolution (n := n) (Ω := Ω) a (-f) (-u) := by
  let B : H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
    variableCoeffForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
  rw [← isWeakSolution_iff_isWeakDivergenceSolution (n := n) (Ω := Ω) hu.isOpen
    a (-f) (-u)]
  change IsWeakSolution B
    (loadFunctional (n := n) (Ω := Ω) (-f)) (-u)
  have hu' : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) f) u := by
    simpa only [B] using
      (isWeakSolution_iff_isWeakDivergenceSolution
        (n := n) (Ω := Ω) hu.isOpen a f u).2 hu
  have h := hu'.neg
  intro w
  calc
    B (-u) w =
        (-loadFunctional (n := n) (Ω := Ω) f) w := h w
    _ = -loadFunctional (n := n) (Ω := Ω) f w := rfl
    _ = loadFunctional (n := n) (Ω := Ω) (-f) w := by
      simp only [loadFunctional_apply, inner_neg_left]

/-- Difference of two divergence-form weak solutions solves the difference-load problem. -/
theorem IsWeakDivergenceSolution.sub
    {a : Fin n → Fin n → DerivLp n ∞ Ω} {f g : L2} {u v : H¹₀(Ω)}
    (hu : IsWeakDivergenceSolution (n := n) (Ω := Ω) a f u)
    (hv : IsWeakDivergenceSolution (n := n) (Ω := Ω) a g v) :
    IsWeakDivergenceSolution (n := n) (Ω := Ω) a (f - g) (u - v) := by
  simpa only [sub_eq_add_neg] using hu.add hv.neg

/-- Scaling a divergence-form weak solution scales the forcing by the same real constant. -/
theorem IsWeakDivergenceSolution.smul
    {a : Fin n → Fin n → DerivLp n ∞ Ω} {f : L2} {u : H¹₀(Ω)}
    (c : ℝ)
    (hu : IsWeakDivergenceSolution (n := n) (Ω := Ω) a f u) :
    IsWeakDivergenceSolution (n := n) (Ω := Ω) a (c • f) (c • u) := by
  let B : H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
    variableCoeffForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
  rw [← isWeakSolution_iff_isWeakDivergenceSolution (n := n) (Ω := Ω) hu.isOpen
    a (c • f) (c • u)]
  change IsWeakSolution B
    (loadFunctional (n := n) (Ω := Ω) (c • f)) (c • u)
  have hu' : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) f) u := by
    simpa only [B] using
      (isWeakSolution_iff_isWeakDivergenceSolution
        (n := n) (Ω := Ω) hu.isOpen a f u).2 hu
  have h := IsWeakSolution.smul c hu'
  intro w
  calc
    B (c • u) w =
        (c • loadFunctional (n := n) (Ω := Ω) f) w := h w
    _ = c * loadFunctional (n := n) (Ω := Ω) f w := rfl
    _ = loadFunctional (n := n) (Ω := Ω) (c • f) w := by
      simp only [loadFunctional_apply, real_inner_smul_left]

/-- Linear combinations of divergence-form weak solutions with the same coefficients. -/
theorem IsWeakDivergenceSolution.linear_combination
    {a : Fin n → Fin n → DerivLp n ∞ Ω} {f g : L2} {u v : H¹₀(Ω)}
    (c₁ c₂ : ℝ)
    (hu : IsWeakDivergenceSolution (n := n) (Ω := Ω) a f u)
    (hv : IsWeakDivergenceSolution (n := n) (Ω := Ω) a g v) :
    IsWeakDivergenceSolution (n := n) (Ω := Ω) a
      (c₁ • f + c₂ • g) (c₁ • u + c₂ • v) :=
  (hu.smul c₁).add (hv.smul c₂)

/-- Difference of two divergence-form weak solutions with the same forcing is homogeneous. -/
theorem IsWeakDivergenceSolution.sub_same_load
    {a : Fin n → Fin n → DerivLp n ∞ Ω} {f : L2} {u v : H¹₀(Ω)}
    (hu : IsWeakDivergenceSolution (n := n) (Ω := Ω) a f u)
    (hv : IsWeakDivergenceSolution (n := n) (Ω := Ω) a f v) :
    IsWeakDivergenceSolution (n := n) (Ω := Ω) a 0 (u - v) := by
  simpa only [sub_self] using hu.sub hv

/-- Uniform ellipticity plus the bounded-domain Poincaré inequality makes the
variable-coefficient form coercive on `H¹₀(Ω)`. -/
theorem variableCoeffForm_isCoercive
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) {alpha : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha) :
    IsCoercive
      (variableCoeffForm (n := n) (Ω := Ω) A) := by
  rcases dirichletForm_isCoercive (n := n) (Ω := Ω) hn hΩbounded with
    ⟨C, hC, hdir⟩
  refine ⟨alpha * C, mul_pos hA.1 hC, ?_⟩
  intro u
  calc
    alpha * C * ‖u‖ * ‖u‖ = alpha * (C * ‖u‖ * ‖u‖) := by ring
    _ ≤ alpha * dirichletForm (n := n) (Ω := Ω) u u :=
      mul_le_mul_of_nonneg_left (hdir u) hA.1.le
    _ ≤ variableCoeffForm (n := n) (Ω := Ω) A u u := hA.2 u

/-- Poincaré's inequality upgrades spatial uniform ellipticity to a single positive
coercivity constant for the whole time-dependent family on `H¹₀`. -/
theorem exists_uniform_coercivity_coefficient_forms
    {n : ℕ} {Ω : Set (ℝ^n)} (hn : 0 < n)
    (hΩbounded : Bornology.IsBounded Ω) {a b : ℝ} (hab : a < b)
    (coeff : ℝ → Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (hElliptic : ∀ t ∈ Icc a b, AEUniformlyElliptic (coeff t) alpha) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc a b, ∀ w : H¹₀(Ω),
      C * ‖w‖ ^ 2 ≤
        variableCoeffForm (multiplicationCoefficientOperator (coeff t)) w w := by
  obtain ⟨C₀, hC₀, hdirichlet⟩ := dirichletForm_isCoercive hn hΩbounded
  have halpha : 0 < alpha := (hElliptic a ⟨le_rfl, hab.le⟩).1
  refine ⟨alpha * C₀, mul_pos halpha hC₀, ?_⟩
  intro t ht w
  calc
    (alpha * C₀) * ‖w‖ ^ 2 = alpha * (C₀ * ‖w‖ * ‖w‖) := by
      simp only [pow_two, mul_assoc]
    _ ≤ alpha * dirichletForm w w :=
      mul_le_mul_of_nonneg_left (hdirichlet w) halpha.le
    _ ≤ variableCoeffForm (multiplicationCoefficientOperator (coeff t)) w w :=
      (integratedElliptic_multiplication_of_ae (coeff t) (hElliptic t ht)).2 w

end Coefficients

end GraphSpace

end SobolevSpace
