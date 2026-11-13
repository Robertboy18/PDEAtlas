/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Products
public import PDE.Analysis.Normed.Operator.FiniteProduct
public import PDE.Spaces.Sobolev.Calculus.Divergence.FirstOrder
public import PDE.Spaces.Sobolev.Calculus.Product.IntegrationByParts
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.VectorZeroBoundary

/-!
# Convection on zero-boundary Sobolev fields

The transport pairing `∫ (a · ∇)u · v` accepts an independent `L⁴` coefficient
and completed `H¹₀` transported and test fields. Hölder puts the product of the
coefficient and test field in `L²`, where it pairs with the weak derivative.

Weak divergence zero implies energy cancellation. We first test against the
square of a compact smooth scalar field, then use ordinary `H¹₀` density in
the transported field. The coefficient remains fixed throughout, so no
solenoidal smooth approximation is needed. The coefficient's boundary values
are unrestricted. Polarization gives skew symmetry.

The test inclusion is an argument: bounded domains can use their compact `L⁴`
embedding, and bounds keep its actual norm. `sobolevConvection` also realizes
the coefficient through this inclusion. An independent coefficient instead
allows the finite-rank correction of Hou, Wang and Yang (Section 4.3) to have nonzero
trace on the artificial bounded-domain boundary.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 4.3, (4.23) and (4.24),
  p. 28.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev InnerProductSpace Topology

namespace IncompressibleFlow

variable {n : ℕ} {Ω : Set (ℝ^n)}

-- Keep the inherited structures available before forming nested operator spaces.
/-- The real scalar action on `H¹₀(Ω)`, for the `H¹` norm. -/
local instance normedSpaceH10 : NormedSpace ℝ H¹₀(Ω) := inferInstance

/-- The `L⁴` norm on the derivative rows. -/
local instance normedAddCommGroupDerivL4 : NormedAddCommGroup (DerivLp n 4 Ω) := inferInstance
/-- The real scalar action on the `L⁴` derivative rows. -/
local instance normedSpaceDerivL4 : NormedSpace ℝ (DerivLp n 4 Ω) := inferInstance

/-- One directional transport pairing with an independent `L⁴` coefficient.
Only the transported and tested fields have zero boundary values. -/
def scalarL4Transport (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω) (i : Fin n) :
    PDE.Analysis.ContinuousTrilinearForm (DerivLp n 4 Ω) (H¹₀(Ω)) (H¹₀(Ω)) :=
  let C : DerivLp n 4 Ω →L[ℝ] H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
    (ContinuousLinearMap.productLoad (p := 4) (q := 4)
      (derivCoordCLM (Ω := Ω) i)).bilinearComp
        (ContinuousLinearMap.id ℝ (DerivLp n 4 Ω)) J
  let flip : (H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ) →L[ℝ]
      H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
    (ContinuousLinearMap.flipₗᵢ ℝ (H¹₀(Ω)) (H¹₀(Ω)) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  flip.comp C

/-- Evaluation uses Hölder multiplication of the coefficient and test. -/
theorem scalarL4Transport_apply (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω) (i : Fin n)
    (A : DerivLp n 4 Ω) (U V : H¹₀(Ω)) :
    scalarL4Transport J i A U V =
      ⟪(ContinuousLinearMap.mul ℝ ℝ).holder 2 A (J V), derivCoordCLM i U⟫_ℝ :=
  rfl

/-- Sobolev transport obtained by realizing the coefficient through the same `L⁴` inclusion. -/
def scalarTransport (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω) (i : Fin n) :
    PDE.Analysis.ContinuousTrilinearForm (H¹₀(Ω)) (H¹₀(Ω)) (H¹₀(Ω)) :=
  (scalarL4Transport J i).restrict J
    (ContinuousLinearMap.id ℝ (H¹₀(Ω))) (ContinuousLinearMap.id ℝ (H¹₀(Ω)))

/-- Evaluation of the constructed form as a Hölder product paired with a derivative. -/
theorem scalarTransport_apply (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω) (i : Fin n)
    (A U V : H¹₀(Ω)) :
    scalarTransport J i A U V =
      ⟪(ContinuousLinearMap.mul ℝ ℝ).holder 2
          (J A) (J V),
        derivCoordCLM i U⟫_ℝ :=
  rfl

/-- The transport estimate before bounding the Sobolev inclusions. Keeping the
individual derivative norm allows the vector estimate to use Cauchy--Schwarz. -/
theorem norm_scalarL4Transport_le
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω) (i : Fin n)
    (A : DerivLp n 4 Ω) (U V : H¹₀(Ω)) :
    ‖scalarL4Transport J i A U V‖ ≤ ‖A‖ * ‖derivCoordCLM i U‖ * ‖J V‖ := by
  rw [scalarL4Transport_apply]
  have hproduct : ‖(ContinuousLinearMap.mul ℝ ℝ).holder 2 A (J V)‖ ≤
      ‖A‖ * ‖J V‖ := by
    calc
      _ ≤ ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖A‖ * ‖J V‖ :=
        ContinuousLinearMap.norm_holder_apply_apply_le _ _ _
      _ ≤ 1 * ‖A‖ * ‖J V‖ := by
        gcongr
        exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
      _ = _ := by rw [one_mul]
  calc
    _ ≤ ‖(ContinuousLinearMap.mul ℝ ℝ).holder 2 A (J V)‖ * ‖derivCoordCLM i U‖ :=
      norm_inner_le_norm _ _
    _ ≤ (‖A‖ * ‖J V‖) * ‖derivCoordCLM i U‖ := by gcongr
    _ = _ := by ring

/-- The `ℓ²` product norm on vector fields with components in `H¹₀(Ω)`. -/
local instance normedAddCommGroupVector (m : ℕ) :
    NormedAddCommGroup (H¹₀(Ω; ℝ^m)) :=
  PiLp.normedAddCommGroup (p := 2) (α := fun _ : Fin m ↦ H¹₀(Ω))

/-- The seminormed group underlying `normedAddCommGroupVector`. -/
local instance seminormedAddCommGroupVector (m : ℕ) :
    SeminormedAddCommGroup (H¹₀(Ω; ℝ^m)) :=
  (normedAddCommGroupVector (Ω := Ω) m).toSeminormedAddCommGroup

/-- The real scalar action on `H¹₀` vector fields, for the product norm. -/
local instance normedSpaceVector (m : ℕ) : NormedSpace ℝ (H¹₀(Ω; ℝ^m)) :=
  PiLp.normedSpace (p := 2) (𝕜 := ℝ) (β := fun _ : Fin m ↦ H¹₀(Ω))

/-- The operator norm on the dual of the `H¹₀` vector fields. -/
local instance seminormedAddCommGroupVectorDual (m : ℕ) :
    SeminormedAddCommGroup (StrongDual ℝ (H¹₀(Ω; ℝ^m))) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

/-- The operator norm on maps from `H¹₀` vector fields to their dual. -/
local instance seminormedAddCommGroupVectorBilinear (m : ℕ) :
    SeminormedAddCommGroup (H¹₀(Ω; ℝ^m) →L[ℝ] StrongDual ℝ (H¹₀(Ω; ℝ^m))) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

/-- Addition on the dual of the `H¹₀` vector fields. -/
local instance addCommMonoidVectorDual (m : ℕ) :
    AddCommMonoid (StrongDual ℝ (H¹₀(Ω; ℝ^m))) :=
  ContinuousLinearMap.addCommMonoid

/-- Addition on maps from `H¹₀` vector fields to their dual. -/
local instance addCommMonoidVectorBilinear (m : ℕ) :
    AddCommMonoid (H¹₀(Ω; ℝ^m) →L[ℝ] StrongDual ℝ (H¹₀(Ω; ℝ^m))) :=
  ContinuousLinearMap.addCommMonoid

/-- Addition on the trilinear forms on `H¹₀` vector fields. -/
local instance addCommMonoidVectorTrilinear (m : ℕ) :
    AddCommMonoid (PDE.Analysis.ContinuousTrilinearForm
      (H¹₀(Ω; ℝ^n)) (H¹₀(Ω; ℝ^m)) (H¹₀(Ω; ℝ^m))) :=
  ContinuousLinearMap.addCommMonoid

/-- Coordinatewise `L⁴` realization with the finite Hilbert product norm. -/
def vectorL4Embedding {m : ℕ} (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω) :
    H¹₀(Ω; ℝ^m) →L[ℝ] PiLp 2 (fun _ : Fin m ↦ DerivLp n 4 Ω) :=
  ContinuousLinearMap.piLpMap 2 fun _ ↦ J

/-- The vector realization applies the scalar inclusion to each coordinate. -/
@[simp]
theorem vectorL4Embedding_apply {m : ℕ}
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω) (U : H¹₀(Ω; ℝ^m)) (i : Fin m) :
    vectorL4Embedding J U i = J (U i) :=
  rfl

/-- The vector `L⁴` realization keeps the sum of coordinate energies. -/
theorem norm_vectorL4Embedding_sq {m : ℕ}
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω) (U : H¹₀(Ω; ℝ^m)) :
    ‖vectorL4Embedding J U‖ ^ 2 = ∑ i, ‖J (U i)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

/-- The vector inclusion retains the scalar inclusion bound, without a
dimension-dependent factor. -/
theorem norm_vectorL4Embedding_le {m : ℕ}
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω) (U : H¹₀(Ω; ℝ^m)) :
    ‖vectorL4Embedding J U‖ ≤ ‖J‖ * ‖U‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ i, (‖J‖ * ‖U i‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (J.le_opNorm (U i))
    _ = _ := by simp only [mul_pow, Finset.mul_sum]

/-- A faithful scalar realization is also injective on vector fields. -/
theorem vectorL4Embedding_injective {m : ℕ}
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω) (hJ : Function.Injective J) :
    Function.Injective (vectorL4Embedding (m := m) J) := by
  intro U V h
  apply PiLp.ext
  intro i
  exact hJ (congrArg (fun u ↦ u i) h)

/-- Rellich compactness of the scalar inclusion gives the weaker compact
topology used by the vector profile iteration. -/
theorem vectorL4Embedding_isCompactOperator {m : ℕ}
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω) (hJ : IsCompactOperator J) :
    IsCompactOperator (vectorL4Embedding (m := m) J) :=
  ContinuousLinearMap.isCompactOperator_piLpMap 2 (fun _ ↦ J) (fun _ ↦ hJ)

private def squareTest (φ : TestFunctionOn n Ω) : TestFunctionOn n Ω :=
  ⟨TestFunction.mul φ.1 φ.1, by
    change tsupport (fun x ↦ φ.1 x * φ.1 x) ⊆ Ω
    exact tsupport_mul_subset_right.trans φ.2⟩

private theorem derivative_squareTest (i : Fin n) (φ : TestFunctionOn n Ω) :
    derivCoordCLM i (testFunctionToH10 (squareTest φ)) =
      (2 : ℝ) • (testFunctionLpTop (Ω := Ω) φ.1 • derivCoordCLM i (testFunctionToH10 φ)) := by
  apply Lp.ext
  filter_upwards [derivCoordCLM_testFunction_apply_ae i (squareTest φ),
    Lp.coeFn_smul (2 : ℝ) (testFunctionLpTop (Ω := Ω) φ.1 •
      derivCoordCLM i (testFunctionToH10 φ)),
    Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (testFunctionLpTop (Ω := Ω) φ.1)
      (derivCoordCLM i (testFunctionToH10 φ)),
    testFunctionLpTop_apply_ae (Ω := Ω) φ.1,
    derivCoordCLM_testFunction_apply_ae i φ] with x hs htwo hmul hφ hdφ
  rw [hs, htwo]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hmul]
  simp only [Pi.mul_apply, smul_eq_mul, hφ, hdφ]
  change (∂[i] (fun y ↦ φ.1.toFun y * φ.1.toFun y)) x =
    2 * (φ.1.toFun x * (∂[i] φ.1.toFun) x)
  rw [PDE.partialDeriv_mul (f := φ.1.toFun) (g := φ.1.toFun) (i := i) (x := x)
    ((φ.1.contDiff.differentiable (by simp)).differentiableAt)
    ((φ.1.contDiff.differentiable (by simp)).differentiableAt)]
  ring

private theorem holder_testFunction_eq_multiplier
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (hJ : ∀ u, (J u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ))
    (A : DerivLp n 4 Ω) (f : DerivLp n 2 Ω)
    (hA : (A : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (f : ℝ^n → ℝ))
    (φ : TestFunctionOn n Ω) :
    (ContinuousLinearMap.mul ℝ ℝ).holder 2
      A
      (J (testFunctionToH10 φ)) =
        testFunctionLpTop (Ω := Ω) φ.1 • f := by
  apply Lp.ext
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2)
      A
      (J (testFunctionToH10 φ)),
    hA,
    hJ (testFunctionToH10 φ),
    baseCoordCLM_testFunction_apply_ae φ,
    testFunctionLpTop_apply_ae (Ω := Ω) φ.1,
    Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞))
      (testFunctionLpTop (Ω := Ω) φ.1) f] with x hp hA hJ hφ htop hmul
  rw [hp, hmul]
  simp only [ContinuousLinearMap.mul_apply', smul_eq_mul, Pi.mul_apply,
    hA, hJ, hφ, htop]
  ring

/-- Integration by parts on a compact square test requires no boundary trace of the coefficient. -/
private theorem sum_scalarL4Transport_test_energy
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (hJ : ∀ u, (J u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ))
    (A : Fin n → DerivLp n 4 Ω) (f g : Fin n → DerivLp n 2 Ω)
    (hA : ∀ i, (A i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (f i : ℝ^n → ℝ))
    (hweak : ∀ i, HasWeakDerivativeOn Ω [i] (f i : ℝ^n → ℝ) (g i : ℝ^n → ℝ))
    (φ : TestFunctionOn n Ω) :
    (2 : ℝ) * (∑ i, scalarL4Transport J i (A i)
      (testFunctionToH10 φ) (testFunctionToH10 φ)) =
        -⟪∑ i, g i, baseCoordCLM (testFunctionToH10 (squareTest φ))⟫_ℝ := by
  have hparts (i : Fin n) := weakDerivative_integrationByParts_H10
    i (f i) (g i) (hweak i)
    (testFunctionToH10 (squareTest φ))
  have hterm (i : Fin n) :
      (2 : ℝ) * scalarL4Transport J i (A i)
        (testFunctionToH10 φ) (testFunctionToH10 φ) =
      ⟪f i, derivCoordCLM i (testFunctionToH10 (squareTest φ))⟫_ℝ := by
    rw [scalarL4Transport_apply, holder_testFunction_eq_multiplier J hJ _ _ (hA i),
      Lp.inner_lpSMul_left, derivative_squareTest, inner_smul_right]
  rw [Finset.mul_sum]
  simp_rw [hterm, hparts]
  rw [Finset.sum_neg_distrib, sum_inner]

/-- An `L⁴` coefficient with `L²` value and diagonal weak derivatives contributes
no transport energy when its weak divergence vanishes.
Its boundary values are unrestricted. Density is used only in the zero-boundary
transported field. -/
theorem sum_scalarL4Transport_energy_eq_zero
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (hJ : ∀ u, (J u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ))
    (A : Fin n → DerivLp n 4 Ω) (f g : Fin n → DerivLp n 2 Ω)
    (hA : ∀ i, (A i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (f i : ℝ^n → ℝ))
    (hweak : ∀ i, HasWeakDerivativeOn Ω [i] (f i : ℝ^n → ℝ) (g i : ℝ^n → ℝ))
    (hdiv : ∑ i, g i = 0) (U : H¹₀(Ω)) :
    (∑ i, scalarL4Transport J i (A i) U U) = 0 := by
  refine DenseRange.induction_on
    (denseRange_testFunctionToH10Linear (n := n) (Ω := Ω)) U ?_ ?_
  · exact isClosed_eq (by fun_prop) continuous_const
  · intro φ
    have h := sum_scalarL4Transport_test_energy J hJ A f g hA hweak φ
    rw [hdiv, inner_zero_left, neg_zero] at h
    change (2 : ℝ) * (∑ i, scalarL4Transport J i (A i)
      (testFunctionToH10Linear φ) (testFunctionToH10Linear φ)) = 0 at h
    linarith only [h]

/-- The zero-boundary coefficient case follows from the same weak-divergence cancellation. -/
theorem sum_scalarTransport_energy_eq_zero
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (hJ : ∀ u, (J u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ))
    (A : Fin n → H¹₀(Ω))
    (hdiv : ∑ i, derivCoordCLM i (A i) = 0) (U : H¹₀(Ω)) :
    (∑ i, scalarTransport J i (A i) U U) = 0 := by
  exact sum_scalarL4Transport_energy_eq_zero J hJ (fun i ↦ J (A i))
    (fun i ↦ baseCoordCLM (A i)) (fun i ↦ derivCoordCLM i (A i))
    (fun i ↦ hJ (A i)) (fun i ↦ by
      simpa only [baseCoordCLM_apply, derivCoordCLM_apply,
        singleDerivIndex_toList] using
        (A i : H¹(Ω)).property (singleDerivIndex n i)) hdiv U

/-- Vector convection with an independent `L⁴` coefficient. The coefficient can
include a finite-rank correction whose trace on the artificial boundary is nonzero. -/
def l4Convection {m : ℕ} (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω) :
    PDE.Analysis.ContinuousTrilinearForm
      (PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω))
      (H¹₀(Ω; ℝ^m)) (H¹₀(Ω; ℝ^m)) :=
  PDE.Analysis.ContinuousTrilinearForm.restrict
    ContinuousLinearMap.transportPairing
    (ContinuousLinearMap.id ℝ (PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω)))
    ZeroBoundaryVectorSpace.gradientCoordinates (vectorL4Embedding J)

/-- Coordinate evaluation of transport by the independently supplied field. -/
theorem l4Convection_apply {m : ℕ}
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (A : PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω)) (U V : H¹₀(Ω; ℝ^m)) :
    l4Convection J A U V = ∑ k, ∑ i, scalarL4Transport J i (A i) (U k) (V k) := by
  rw [l4Convection, PDE.Analysis.ContinuousTrilinearForm.restrict_apply,
    ContinuousLinearMap.transportPairing_apply]
  rfl

/-- Hölder and the full matrix gradient give constant one, independently of dimension. -/
theorem norm_l4Convection_le {m : ℕ}
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (A : PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω)) (U V : H¹₀(Ω; ℝ^m)) :
    ‖l4Convection J A U V‖ ≤
      ‖A‖ * ‖ZeroBoundaryVectorSpace.gradient U‖ * ‖vectorL4Embedding J V‖ := by
  simpa only [l4Convection, PDE.Analysis.ContinuousTrilinearForm.restrict_apply,
    ContinuousLinearMap.id_apply, ZeroBoundaryVectorSpace.norm_gradientCoordinates] using
    ContinuousLinearMap.norm_transportPairing_le A
      (ZeroBoundaryVectorSpace.gradientCoordinates U) (vectorL4Embedding J V)

/-- The dual norm depends on the coefficient's `L⁴` norm and the transported energy norm. -/
theorem norm_l4Convection_dual_le {m : ℕ}
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (A : PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω)) (U : H¹₀(Ω; ℝ^m)) :
    ‖l4Convection J A U‖ ≤ ‖J‖ * ‖A‖ * ‖U‖ := by
  apply (l4Convection J A U).opNorm_le_bound (by positivity)
  intro V
  calc
    ‖l4Convection J A U V‖ ≤
        ‖A‖ * ‖ZeroBoundaryVectorSpace.gradient U‖ * ‖vectorL4Embedding J V‖ :=
      norm_l4Convection_le J A U V
    _ ≤ ‖A‖ * ‖U‖ * (‖J‖ * ‖V‖) := by
      gcongr
      · exact ZeroBoundaryVectorSpace.norm_gradient_le U
      · exact norm_vectorL4Embedding_le J V
    _ = _ := by ring

/-- Weak divergence zero cancels the transport energy, with unrestricted coefficient trace. -/
theorem l4Convection_energy_eq_zero {m : ℕ}
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (hJ : ∀ u, (J u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ))
    (A : PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω)) (f g : Fin n → DerivLp n 2 Ω)
    (hA : ∀ i, (A i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (f i : ℝ^n → ℝ))
    (hweak : ∀ i, HasWeakDerivativeOn Ω [i] (f i : ℝ^n → ℝ) (g i : ℝ^n → ℝ))
    (hdiv : ∑ i, g i = 0) (U : H¹₀(Ω; ℝ^m)) :
    l4Convection J A U U = 0 := by
  rw [l4Convection_apply]
  simp_rw [sum_scalarL4Transport_energy_eq_zero J hJ (fun i ↦ A i) f g hA hweak hdiv]
  simp

/-- A faithful `L⁴` realization of a solenoidal `H¹` coefficient preserves transport energy.
The coefficient need not belong to `H¹₀`. -/
theorem l4Convection_energy_eq_zero_of_sobolev {m : ℕ}
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (hJ : ∀ u, (J u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ))
    (A : PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω)) (Q : Fin n → H¹(Ω))
    (hA : ∀ i, (A i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      (wkpBaseCoordinateCLM (Q i) : ℝ^n → ℝ))
    (hdiv : negativeDivergence Q = 0) (U : H¹₀(Ω; ℝ^m)) :
    l4Convection J A U U = 0 := by
  apply l4Convection_energy_eq_zero J hJ A
    (fun i ↦ wkpBaseCoordinateCLM (Q i))
    (fun i ↦ wkpCoordinateCLM (singleDerivIndex n i) (Q i)) hA
  · intro i
    simpa only [firstDerivIndex_one, wkpBaseCoordinateCLM_apply,
      wkpCoordinateCLM_apply] using
      (Q i).property.hasWeakDerivativeOn_first (by norm_num) i
  · exact neg_eq_zero.mp hdiv

/-- Solenoidal `H¹` coefficients preserve the coercivity modulus even with nonzero trace. -/
theorem isCoercive_add_l4Convection_of_sobolev
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (hJ : ∀ u, (J u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ))
    (A : PiLp 2 (fun _ : Fin n ↦ DerivLp n 4 Ω)) (Q : Fin n → H¹(Ω))
    (hA : ∀ i, (A i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      (wkpBaseCoordinateCLM (Q i) : ℝ^n → ℝ))
    (hdiv : negativeDivergence Q = 0)
    (B : H¹₀(Ω; ℝ^n) →L[ℝ] StrongDual ℝ H¹₀(Ω; ℝ^n))
    (hB : IsCoercive B) : IsCoercive (B + l4Convection J A) := by
  obtain ⟨c, hc, hbound⟩ := hB
  refine ⟨c, hc, fun U ↦ ?_⟩
  simpa only [add_apply,
    l4Convection_energy_eq_zero_of_sobolev J hJ A Q hA hdiv U, add_zero] using hbound U

/-- Sobolev convection realizes the coefficient through the scalar `L⁴` inclusion. -/
def sobolevConvection {m : ℕ}
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω) :
    PDE.Analysis.ContinuousTrilinearForm
      (H¹₀(Ω; ℝ^n)) (H¹₀(Ω; ℝ^m)) (H¹₀(Ω; ℝ^m)) :=
  (l4Convection J).restrict (vectorL4Embedding J)
    (ContinuousLinearMap.id ℝ (H¹₀(Ω; ℝ^m)))
    (ContinuousLinearMap.id ℝ (H¹₀(Ω; ℝ^m)))

/-- The assembled convection evaluates on the original scalar coordinates. -/
theorem sobolevConvection_apply {m : ℕ}
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (A : H¹₀(Ω; ℝ^n)) (U V : H¹₀(Ω; ℝ^m)) :
    sobolevConvection J A U V =
      ∑ k, ∑ i, scalarTransport J i (A i) (U k) (V k) := by
  rw [sobolevConvection, PDE.Analysis.ContinuousTrilinearForm.restrict_apply,
    l4Convection_apply]
  rfl

/-- Hölder and Cauchy--Schwarz control convection using the actual `L⁴`
coordinates and the full weak gradient, with no coordinate-count penalty. -/
theorem norm_sobolevConvection_le {m : ℕ}
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (A : H¹₀(Ω; ℝ^n)) (U V : H¹₀(Ω; ℝ^m)) :
    ‖sobolevConvection J A U V‖ ≤
      ‖vectorL4Embedding J A‖ * ‖ZeroBoundaryVectorSpace.gradient U‖ *
        ‖vectorL4Embedding J V‖ :=
  norm_l4Convection_le J (vectorL4Embedding J A) U V

/-- Convection depends on its advecting coefficient in the weaker `L⁴` norm.
This estimate controls differences of the linear transport solves. -/
theorem norm_sobolevConvection_dual_le
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (A U : H¹₀(Ω; ℝ^n)) :
    ‖sobolevConvection J A U‖ ≤ ‖J‖ * ‖vectorL4Embedding J A‖ * ‖U‖ :=
  norm_l4Convection_dual_le J (vectorL4Embedding J A) U

/-- Actual divergence-free Sobolev transport preserves completed vector energy. -/
theorem sobolevConvection_energy_eq_zero {m : ℕ}
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (hJ : ∀ u, (J u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ))
    (A : H¹₀(Ω; ℝ^n))
    (hdiv : ∑ i, derivCoordCLM i (A i) = 0) (U : H¹₀(Ω; ℝ^m)) :
    sobolevConvection J A U U = 0 := by
  rw [sobolevConvection_apply]
  simp_rw [sum_scalarTransport_energy_eq_zero J hJ (fun i ↦ A i) hdiv]
  simp

/-- Divergence-free transport is skew in the transported and tested fields. -/
theorem sobolevConvection_skew {m : ℕ}
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (hJ : ∀ u, (J u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ))
    (A : H¹₀(Ω; ℝ^n)) (hdiv : ∑ i, derivCoordCLM i (A i) = 0)
    (U V : H¹₀(Ω; ℝ^m)) :
    sobolevConvection J A U V = -sobolevConvection J A V U := by
  have h := sobolevConvection_energy_eq_zero J hJ A hdiv (U + V)
  simp only [map_add, add_apply] at h
  rw [sobolevConvection_energy_eq_zero J hJ A hdiv U,
    sobolevConvection_energy_eq_zero J hJ A hdiv V] at h
  linarith only [h]

/-- Adding divergence-free transport preserves the coercivity modulus exactly.
The advecting field needs only the same zero-boundary Sobolev regularity. -/
theorem isCoercive_add_sobolevConvection
    (J : H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω)
    (hJ : ∀ u, (J u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ))
    (A : H¹₀(Ω; ℝ^n)) (hdiv : ∑ i, derivCoordCLM i (A i) = 0)
    (B : H¹₀(Ω; ℝ^n) →L[ℝ] StrongDual ℝ H¹₀(Ω; ℝ^n))
    (hB : IsCoercive B) : IsCoercive (B + sobolevConvection J A) := by
  obtain ⟨c, hc, hbound⟩ := hB
  refine ⟨c, hc, fun U ↦ ?_⟩
  simpa only [add_apply,
    sobolevConvection_energy_eq_zero J hJ A hdiv U, add_zero] using hbound U

end IncompressibleFlow
