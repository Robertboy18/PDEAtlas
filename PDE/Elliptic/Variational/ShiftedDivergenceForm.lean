/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.ShiftedDivergenceForm.Solution

/-!
# Shifted divergence-form problems

Let `B` be the full divergence-form bilinear form on `H¹₀(Ω)` with lower-order terms,

`B(u,v) = ∑ᵢⱼ ⟪Aᵢⱼ ∂ⱼu, ∂ᵢv⟫ + ∑ᵢ ⟪bᵢ ∂ᵢu, v⟫ + ⟪c u, v⟫`.

The Gårding inequality of `PDE.Elliptic.Variational.LowerOrderForm` shows that
`B_μ(u,v) = B(u,v) + μ ⟪u, v⟫_{L²}` is coercive once `μ` is at least the explicit threshold
`coerciveShift alpha beta gamma`, computed from the ellipticity constant `alpha` and the
operator-norm bounds `beta`, `gamma` on `b` and `c`. Lax–Milgram then gives a unique weak
solution of `B_μ(u, ·) = F` for every load in the `H⁻¹` representation
`F(v) = ⟪f₀, v⟫ + ∑ᵢ ⟪fᵢ, ∂ᵢv⟫` (`ShiftedDivergenceForm.Existence`). This is Evans's First
Existence Theorem for weak solutions (§6.2.2, Theorem 3) with an explicit shift, for the
right-hand sides `f₀ - ∑ᵢ ∂ᵢfᵢ` that he treats right after it.

The solution is `shiftedDivergenceSolve`; it is unique and satisfies an explicit `H¹₀` bound
(`ShiftedDivergenceForm.Solution`). We specialize to measurable `L∞` coefficient
fields acting by multiplication. In that setting the Hilbert-space weak equation is shown to be
equivalent to the distributional identity

`∫ aᵢⱼ ∂ⱼu ∂ᵢφ + ∫ bᵢ ∂ᵢu φ + ∫ (c + μ) u φ = ∫ f₀ φ + ∑ᵢ ∫ fᵢ ∂ᵢφ  for all φ ∈ C_c^∞(Ω)`

on an open set.

## Main results

* `multiplicationFirstOrderOperator`, `multiplicationZeroOrderOperator`,
  `lowerOrderBounds_multiplication`: `L∞` coefficients as bounded operators on `L²`, with
  operator norms controlled by the `L∞` norms.
* `IsWeakShiftedFullDivergenceSolution`,
  `isWeakSolution_iff_isWeakShiftedFullDivergenceSolution`: the distributional formulation
  and its equivalence with the Hilbert-space one.
* `existsUnique_weakShiftedFullDivergenceSolution_of_aeElliptic`,
  `isWeakShiftedFullDivergenceSolution_zero_iff_of_aeElliptic`: existence, uniqueness, and
  zero-data uniqueness under almost-everywhere ellipticity and `L∞` lower-order bounds.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.1.2, (7) and the weak solution of (10), pp. 314-315;
  §6.2.2, Theorem 2 (Energy estimates) and Theorem 3 (First Existence Theorem for weak
  solutions), pp. 318-319, and the right-hand sides `f₀ - ∑ᵢ ∂ᵢfᵢ` of (9), p. 320.
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

section MultiplicationCoefficients

local notation "L2" => DerivLp n 2 Ω

/-- A measurable essentially bounded first-order coefficient field acts on
each weak derivative coordinate by pointwise multiplication. -/
noncomputable def multiplicationFirstOrderOperator
    (b : Fin n → DerivLp n ∞ Ω) :
    (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)) :=
  fun i ↦ mulLpLeft (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) (b i)

/-- A measurable essentially bounded zeroth-order coefficient acts on the
base `L²` coordinate by pointwise multiplication. -/
noncomputable def multiplicationZeroOrderOperator
    (c : DerivLp n ∞ Ω) : L2 →L[ℝ] L2 :=
  mulLpLeft (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) c

/-- A first-order multiplication coefficient acts on an `L²` coordinate through the scalar
action of `L∞`: `bᵢ w = bᵢ • w`. -/
@[simp]
theorem multiplicationFirstOrderOperator_apply
    (b : Fin n → DerivLp n ∞ Ω) (i : Fin n) (w : L2) :
    multiplicationFirstOrderOperator (n := n) (Ω := Ω) b i w = b i • w :=
  rfl

/-- A zeroth-order multiplication coefficient acts on `L²` through the scalar action of `L∞`:
`c w = c • w`. -/
@[simp]
theorem multiplicationZeroOrderOperator_apply
    (c : DerivLp n ∞ Ω) (w : L2) :
    multiplicationZeroOrderOperator (n := n) (Ω := Ω) c w = c • w :=
  rfl

/-- Pointwise representative of a first-order multiplication coefficient. -/
theorem multiplicationFirstOrderOperator_apply_ae
    (b : Fin n → DerivLp n ∞ Ω) (i : Fin n) (w : L2) :
    ((multiplicationFirstOrderOperator (n := n) (Ω := Ω) b i w : L2) :
        ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ b i x * w x :=
  mulLpLeft_apply_ae (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) (b i) w

/-- Pointwise representative of a zeroth-order multiplication coefficient. -/
theorem multiplicationZeroOrderOperator_apply_ae
    (c : DerivLp n ∞ Ω) (w : L2) :
    ((multiplicationZeroOrderOperator (n := n) (Ω := Ω) c w : L2) :
        ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ c x * w x :=
  mulLpLeft_apply_ae (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) c w

/-- Multiplication by an `L∞` coefficient paired with a smooth test
function is the expected integral. -/
theorem inner_mulLpLeft_base_testFunction_eq_integral
    (q : DerivLp n ∞ Ω) (w : L2) (φ : TestFunctionOn n Ω) :
    ⟪mulLpLeft (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) q w,
      baseCoordCLM (n := n) (Ω := Ω)
        (testFunctionToH10 (n := n) (Ω := Ω) φ)⟫_ℝ =
      ∫ x, q x * w x * φ.1.toFun x ∂domainMeasure n Ω := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [mulLpLeft_apply_ae (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) q w,
     baseCoordCLM_testFunction_apply_ae
      (n := n) (Ω := Ω) φ] with x hmul htest
  rw [hmul, htest]
  simp [RCLike.inner_apply]
  ring

/-- An arbitrary `L²` datum paired with a smooth test derivative is the
expected integral. -/
theorem inner_deriv_testFunction_data_eq_integral
    (g : L2) (i : Fin n) (φ : TestFunctionOn n Ω) :
    ⟪g, derivCoordCLM (n := n) (Ω := Ω) i
      (testFunctionToH10 (n := n) (Ω := Ω) φ)⟫_ℝ =
      ∫ x, (g : ℝ^n → ℝ) x * (∂[i] φ.1.toFun) x
        ∂domainMeasure n Ω := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [derivCoordCLM_testFunction_apply_ae
    (n := n) (Ω := Ω) i φ] with x htest
  rw [htest]
  simp [RCLike.inner_apply, mul_comm]

/-- The `L²` mass pairing with a smooth test function is the expected
integral of the base representative. -/
theorem inner_base_base_testFunction_eq_integral
    (u : H¹₀(Ω)) (φ : TestFunctionOn n Ω) :
    ⟪baseCoordCLM (n := n) (Ω := Ω) u,
      baseCoordCLM (n := n) (Ω := Ω)
        (testFunctionToH10 (n := n) (Ω := Ω) φ)⟫_ℝ =
      ∫ x, (baseCoordCLM (n := n) (Ω := Ω) u : ℝ^n → ℝ) x *
        φ.1.toFun x ∂domainMeasure n Ω := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [baseCoordCLM_testFunction_apply_ae
    (n := n) (Ω := Ω) φ] with x htest
  rw [htest]
  simp [RCLike.inner_apply, mul_comm]

/-- Evans' distributional weak formulation of the shifted full
divergence-form equation

`-∂ᵢ(aᵢⱼ ∂ⱼu) + bᵢ ∂ᵢu + c u + λu = f₀ - ∂ᵢfᵢ`

with homogeneous Dirichlet data on an open set. The `L∞` coefficient fields
act on `L²` solution coordinates and are paired with `L²` test coordinates;
the load has the same `L²` pairing structure. Consequently all displayed
integrands are integrable, independently of totalization. -/
structure IsWeakShiftedFullDivergenceSolution
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    (lambda : ℝ) (f0 : L2) (f : Fin n → L2) (u : H¹₀(Ω)) : Prop where
  /-- The PDE domain is open. -/
  isOpen : IsOpen Ω
  /-- The shifted full divergence-form identity against every test function. -/
  equation : ∀ φ : TestFunctionOn n Ω,
      (∑ i : Fin n, ∑ j : Fin n,
        ∫ x, a i j x *
            (derivCoordCLM (n := n) (Ω := Ω) j u : ℝ^n → ℝ) x *
            (∂[i] φ.1.toFun) x
          ∂domainMeasure n Ω) +
        (∑ i : Fin n,
          ∫ x, b i x *
              (derivCoordCLM (n := n) (Ω := Ω) i u : ℝ^n → ℝ) x *
              φ.1.toFun x
            ∂domainMeasure n Ω) +
        (∫ x, c x *
            (baseCoordCLM (n := n) (Ω := Ω) u : ℝ^n → ℝ) x *
            φ.1.toFun x
          ∂domainMeasure n Ω) +
        lambda * (∫ x,
          (baseCoordCLM (n := n) (Ω := Ω) u : ℝ^n → ℝ) x *
            φ.1.toFun x
          ∂domainMeasure n Ω) =
        (∫ x, (f0 : ℝ^n → ℝ) x * φ.1.toFun x
          ∂domainMeasure n Ω) +
        ∑ i : Fin n,
          ∫ x, (f i : ℝ^n → ℝ) x * (∂[i] φ.1.toFun) x
            ∂domainMeasure n Ω

/-- A shifted divergence-form weak solution can be applied directly to a test function. -/
instance
    {a : Fin n → Fin n → DerivLp n ∞ Ω}
    {b : Fin n → DerivLp n ∞ Ω} {c : DerivLp n ∞ Ω}
    {lambda : ℝ} {f0 : L2} {f : Fin n → L2} {u : H¹₀(Ω)} :
    CoeFun
      (IsWeakShiftedFullDivergenceSolution
        (n := n) (Ω := Ω) a b c lambda f0 f u)
      (fun _ ↦ ∀ φ : TestFunctionOn n Ω,
        (∑ i : Fin n, ∑ j : Fin n,
          ∫ x, a i j x *
              (derivCoordCLM (n := n) (Ω := Ω) j u : ℝ^n → ℝ) x *
              (∂[i] φ.1.toFun) x
            ∂domainMeasure n Ω) +
          (∑ i : Fin n,
            ∫ x, b i x *
                (derivCoordCLM (n := n) (Ω := Ω) i u : ℝ^n → ℝ) x *
                φ.1.toFun x
              ∂domainMeasure n Ω) +
          (∫ x, c x *
              (baseCoordCLM (n := n) (Ω := Ω) u : ℝ^n → ℝ) x *
              φ.1.toFun x
            ∂domainMeasure n Ω) +
          lambda * (∫ x,
            (baseCoordCLM (n := n) (Ω := Ω) u : ℝ^n → ℝ) x *
              φ.1.toFun x
            ∂domainMeasure n Ω) =
          (∫ x, (f0 : ℝ^n → ℝ) x * φ.1.toFun x
            ∂domainMeasure n Ω) +
          ∑ i : Fin n,
            ∫ x, (f i : ℝ^n → ℝ) x * (∂[i] φ.1.toFun) x
              ∂domainMeasure n Ω) where
  coe h := h.equation

/-- The bundled Hilbert-space weak equation for multiplication
coefficients is equivalent to Evans' distributional test-function
identity. -/
theorem isWeakSolution_iff_isWeakShiftedFullDivergenceSolution
    (hΩopen : IsOpen Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    (lambda : ℝ) (f0 : L2) (f : Fin n → L2) (u : H¹₀(Ω)) :
    IsWeakSolution
        (shiftedDivergenceForm (n := n) (Ω := Ω)
          (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
          (multiplicationFirstOrderOperator (n := n) (Ω := Ω) b)
          (multiplicationZeroOrderOperator (n := n) (Ω := Ω) c) lambda)
        (generalizedLoad (n := n) (Ω := Ω) f0 f) u ↔
      IsWeakShiftedFullDivergenceSolution
        (n := n) (Ω := Ω) a b c lambda f0 f u := by
  constructor
  · refine fun hu ↦ ⟨hΩopen, fun φ ↦ ?_⟩
    have h := hu (testFunctionToH10 (n := n) (Ω := Ω) φ)
    rw [shiftedDivergenceForm_apply, fullDivergenceForm_apply, generalizedLoad_apply] at h
    simp_rw [inner_multiplicationCoefficient_testFunction_eq_integral,
      multiplicationFirstOrderOperator, multiplicationZeroOrderOperator,
      inner_mulLpLeft_base_testFunction_eq_integral, inner_base_base_testFunction_eq_integral,
      inner_base_testFunction_eq_integral, inner_deriv_testFunction_data_eq_integral] at h
    exact h
  · intro hu v
    refine congrFun ((denseRange_testFunctionToH10Linear (n := n) (Ω := Ω)).equalizer
      (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
      (funext fun φ ↦ ?_)) v
    change shiftedDivergenceForm _ _ _ lambda u (testFunctionToH10 (n := n) (Ω := Ω) φ) =
      generalizedLoad (n := n) (Ω := Ω) f0 f (testFunctionToH10 (n := n) (Ω := Ω) φ)
    rw [shiftedDivergenceForm_apply, fullDivergenceForm_apply, generalizedLoad_apply]
    simp_rw [inner_multiplicationCoefficient_testFunction_eq_integral,
      multiplicationFirstOrderOperator, multiplicationZeroOrderOperator,
      inner_mulLpLeft_base_testFunction_eq_integral, inner_base_base_testFunction_eq_integral,
      inner_base_testFunction_eq_integral, inner_deriv_testFunction_data_eq_integral]
    exact hu φ

/--
The `L²` forcing obtained by moving the first-order, zero-order, and scalar-shift
terms of a full divergence-form equation to the right-hand side.
-/
def fullDivergencePrincipalForcing
    (b : Fin n → DerivLp n ∞ Ω)
    (c : DerivLp n ∞ Ω)
    (lambda : ℝ)
    (f : L2)
    (u : H¹₀(Ω)) :
    L2 :=
  f -
    (∑ i : Fin n,
      b i • derivCoordCLM (n := n) (Ω := Ω) i u) -
    c • baseCoordCLM (n := n) (Ω := Ω) u -
    lambda • baseCoordCLM (n := n) (Ω := Ω) u

/--
Move the lower-order terms of a shifted full divergence-form weak equation
into `fullDivergencePrincipalForcing`, leaving the principal weak equation.
-/
theorem IsWeakShiftedFullDivergenceSolution.toPrincipal
    {a : Fin n → Fin n → DerivLp n ∞ Ω}
    {b : Fin n → DerivLp n ∞ Ω}
    {c : DerivLp n ∞ Ω}
    {lambda : ℝ}
    {f : L2}
    {u : H¹₀(Ω)}
    (hu : IsWeakShiftedFullDivergenceSolution
      (n := n) (Ω := Ω) a b c lambda f
      (0 : Fin n → L2) u) :
    IsWeakDivergenceSolution
      (n := n) (Ω := Ω) a
      (fullDivergencePrincipalForcing b c lambda f u) u := by
  have h := (isWeakSolution_iff_isWeakShiftedFullDivergenceSolution hu.isOpen a b c lambda f 0
    u).2 hu
  refine (isWeakSolution_iff_isWeakDivergenceSolution hu.isOpen a _ u).1 fun v ↦ ?_
  have hv := h v
  rw [shiftedDivergenceForm_apply, fullDivergenceForm_apply, generalizedLoad_apply] at hv
  simp only [multiplicationFirstOrderOperator_apply, multiplicationZeroOrderOperator_apply,
    Pi.zero_apply, inner_zero_left, Finset.sum_const_zero, add_zero] at hv
  rw [variableCoeffForm_apply, loadFunctional_apply]
  simp only [fullDivergencePrincipalForcing, inner_sub_left, sum_inner, real_inner_smul_left]
  linarith

/-- `L∞` bounds on pointwise lower-order coefficients imply the abstract
operator bounds used in the Gårding estimate. -/
theorem lowerOrderBounds_multiplication
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {beta gamma : ℝ} (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb : ∀ i, ‖b i‖ ≤ beta) (hc : ‖c‖ ≤ gamma) :
    LowerOrderBounds (n := n) (Ω := Ω)
      (multiplicationFirstOrderOperator (n := n) (Ω := Ω) b)
      (multiplicationZeroOrderOperator (n := n) (Ω := Ω) c)
      beta gamma := by
  refine ⟨hbeta, hgamma, ?_, ?_⟩
  · intro i
    exact (norm_mulLpLeft_le
      (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) (b i)).trans (hb i)
  · exact (norm_mulLpLeft_le
      (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) c).trans hc

/-- Evans' shifted weak existence and uniqueness theorem for measurable
`L∞` coefficients and forcing in the standard `H⁻¹` representation. -/
theorem existsUnique_weakShiftedFullDivergenceSolution
    (hΩopen : IsOpen Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) alpha)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb : ∀ i, ‖b i‖ ≤ beta) (hc : ‖c‖ ≤ gamma)
    (f0 : L2) (f : Fin n → L2) :
    ∃! u : H¹₀(Ω),
      IsWeakShiftedFullDivergenceSolution
        (n := n) (Ω := Ω) a b c
        (coerciveShift (n := n) alpha beta gamma) f0 f u := by
  obtain ⟨u, hu, huniq⟩ := existsUnique_shiftedDivergence_weakSolution _ _ _ hA
    (lowerOrderBounds_multiplication (n := n) (Ω := Ω) b c hbeta hgamma hb hc) f0 f
  exact ⟨u, (isWeakSolution_iff_isWeakShiftedFullDivergenceSolution hΩopen a b c _ f0 f u).1 hu,
    fun v hv ↦ huniq v
      ((isWeakSolution_iff_isWeakShiftedFullDivergenceSolution hv.isOpen a b c _ f0 f v).2 hv)⟩

/-- Evans §6.2.2, Theorem 3 for every `mu` above the explicit threshold,
with measurable `L∞` coefficients and forcing in the standard `H⁻¹`
representation. -/
theorem existsUnique_weakShiftedFullDivergenceSolution_of_coerciveShift_le
    (hΩopen : IsOpen Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha beta gamma mu : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) alpha)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb : ∀ i, ‖b i‖ ≤ beta) (hc : ‖c‖ ≤ gamma)
    (hmu : coerciveShift (n := n) alpha beta gamma ≤ mu)
    (f0 : L2) (f : Fin n → L2) :
    ∃! u : H¹₀(Ω),
      IsWeakShiftedFullDivergenceSolution
        (n := n) (Ω := Ω) a b c mu f0 f u := by
  obtain ⟨u, hu, huniq⟩ := existsUnique_shifted_weakSolution_of_coerciveShift_le _ _ _ hA
    (lowerOrderBounds_multiplication (n := n) (Ω := Ω) b c hbeta hgamma hb hc) hmu f0 f
  exact ⟨u, (isWeakSolution_iff_isWeakShiftedFullDivergenceSolution hΩopen a b c mu f0 f u).1 hu,
    fun v hv ↦ huniq v
      ((isWeakSolution_iff_isWeakShiftedFullDivergenceSolution hv.isOpen a b c mu f0 f v).2 hv)⟩

/-- Textbook form of shifted weak existence: the principal coefficient
matrix is assumed uniformly elliptic almost everywhere, while the
lower-order fields satisfy ordinary `L∞` norm bounds. -/
theorem existsUnique_weakShiftedFullDivergenceSolution_of_aeElliptic
    (hΩopen : IsOpen Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha beta gamma : ℝ}
    (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb : ∀ i, ‖b i‖ ≤ beta) (hc : ‖c‖ ≤ gamma)
    (f0 : L2) (f : Fin n → L2) :
    ∃! u : H¹₀(Ω),
      IsWeakShiftedFullDivergenceSolution
        (n := n) (Ω := Ω) a b c
        (coerciveShift (n := n) alpha beta gamma) f0 f u :=
  existsUnique_weakShiftedFullDivergenceSolution
    (n := n) (Ω := Ω) hΩopen a b c
    (integratedElliptic_multiplication_of_ae
      (n := n) (Ω := Ω) a ha)
    hbeta hgamma hb hc f0 f

/-- The all-larger-shifts theorem with ellipticity stated directly almost
everywhere for the pointwise coefficient matrix. -/
theorem existsUnique_weakShiftedFullDivergenceSolution_of_aeElliptic_of_coerciveShift_le
    (hΩopen : IsOpen Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha beta gamma mu : ℝ}
    (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb : ∀ i, ‖b i‖ ≤ beta) (hc : ‖c‖ ≤ gamma)
    (hmu : coerciveShift (n := n) alpha beta gamma ≤ mu)
    (f0 : L2) (f : Fin n → L2) :
    ∃! u : H¹₀(Ω),
      IsWeakShiftedFullDivergenceSolution
        (n := n) (Ω := Ω) a b c mu f0 f u :=
  existsUnique_weakShiftedFullDivergenceSolution_of_coerciveShift_le
    (n := n) (Ω := Ω) hΩopen a b c
    (integratedElliptic_multiplication_of_ae
      (n := n) (Ω := Ω) a ha)
    hbeta hgamma hb hc hmu f0 f

/-- The named Gårding/Lax–Milgram solver satisfies Evans' distributional
equation for pointwise multiplication coefficients. -/
theorem shiftedDivergenceSolve_isWeakShiftedFullDivergenceSolution
    (hΩopen : IsOpen Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) alpha)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb : ∀ i, ‖b i‖ ≤ beta) (hc : ‖c‖ ≤ gamma)
    (f0 : L2) (f : Fin n → L2) :
    IsWeakShiftedFullDivergenceSolution
      (n := n) (Ω := Ω) a b c
      (coerciveShift (n := n) alpha beta gamma) f0 f
      (shiftedDivergenceSolve (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
        (multiplicationFirstOrderOperator (n := n) (Ω := Ω) b)
        (multiplicationZeroOrderOperator (n := n) (Ω := Ω) c)
        hA
        (lowerOrderBounds_multiplication
          (n := n) (Ω := Ω) b c hbeta hgamma hb hc)
        f0 f) :=
  (isWeakSolution_iff_isWeakShiftedFullDivergenceSolution hΩopen a b c _ f0 f _).1
    (shiftedDivergenceSolve_isWeakSolution _ _ _ hA _ f0 f)

/-- Evans-readable uniqueness for the shifted full divergence-form problem
with measurable `L∞` coefficients: every distributional weak solution is the
named Gårding/Lax–Milgram solution. -/
theorem eq_shiftedDivergenceSolve_of_isWeakShiftedFullDivergenceSolution
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) alpha)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb : ∀ i, ‖b i‖ ≤ beta) (hc : ‖c‖ ≤ gamma)
    (f0 : L2) (f : Fin n → L2) {u : H¹₀(Ω)}
    (hu : IsWeakShiftedFullDivergenceSolution
      (n := n) (Ω := Ω) a b c
      (coerciveShift (n := n) alpha beta gamma) f0 f u) :
    u =
      shiftedDivergenceSolve (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
        (multiplicationFirstOrderOperator (n := n) (Ω := Ω) b)
        (multiplicationZeroOrderOperator (n := n) (Ω := Ω) c)
        hA
        (lowerOrderBounds_multiplication
          (n := n) (Ω := Ω) b c hbeta hgamma hb hc)
        f0 f := by
  exact eq_shiftedDivergenceSolve_of_isWeakSolution _ _ _ hA _ f0 f
    ((isWeakSolution_iff_isWeakShiftedFullDivergenceSolution hu.isOpen a b c _ f0 f u).2 hu)

/-- Evans-readable iff form for the shifted full divergence-form problem with
measurable `L∞` coefficients. -/
theorem isWeakShiftedFullDivergenceSolution_iff_eq_shiftedDivergenceSolve
    (hΩopen : IsOpen Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) alpha)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb : ∀ i, ‖b i‖ ≤ beta) (hc : ‖c‖ ≤ gamma)
    (f0 : L2) (f : Fin n → L2) {u : H¹₀(Ω)} :
    IsWeakShiftedFullDivergenceSolution
        (n := n) (Ω := Ω) a b c
        (coerciveShift (n := n) alpha beta gamma) f0 f u ↔
      u =
        shiftedDivergenceSolve (n := n) (Ω := Ω)
          (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
          (multiplicationFirstOrderOperator (n := n) (Ω := Ω) b)
          (multiplicationZeroOrderOperator (n := n) (Ω := Ω) c)
          hA
          (lowerOrderBounds_multiplication
            (n := n) (Ω := Ω) b c hbeta hgamma hb hc)
          f0 f := by
  constructor
  · exact eq_shiftedDivergenceSolve_of_isWeakShiftedFullDivergenceSolution
      (n := n) (Ω := Ω) a b c hA hbeta hgamma hb hc f0 f
  · rintro rfl
    exact shiftedDivergenceSolve_isWeakShiftedFullDivergenceSolution
      (n := n) (Ω := Ω) hΩopen a b c hA hbeta hgamma hb hc f0 f

/--
The homogeneous shifted divergence-form equation has only the zero
`H^1_0` weak solution.

This is the concrete Evans version of the Hilbert-space zero-data
statement: after expanding bounded measurable coefficients against smooth
test functions, the uniqueness conclusion is still exactly `u = 0`.
-/
theorem isWeakShiftedFullDivergenceSolution_zero_iff
    (hΩopen : IsOpen Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) alpha)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb : ∀ i, ‖b i‖ ≤ beta) (hc : ‖c‖ ≤ gamma)
    {u : H¹₀(Ω)} :
    IsWeakShiftedFullDivergenceSolution
        (n := n) (Ω := Ω) a b c
        (coerciveShift (n := n) alpha beta gamma)
        (0 : L2) (0 : Fin n → L2) u ↔
      u = 0 := by
  rw [isWeakShiftedFullDivergenceSolution_iff_eq_shiftedDivergenceSolve hΩopen a b c hA hbeta
    hgamma hb hc, shiftedDivergenceSolve_zero]

/--
Textbook zero-data uniqueness with almost-everywhere ellipticity.

This is the version closest to Evans' measurable-coefficient hypotheses:
the principal coefficient field is uniformly elliptic a.e.; lower-order
coefficients are bounded in `L∞`; the shifted homogeneous weak equation has
exactly the zero `H^1_0` solution.
-/
theorem isWeakShiftedFullDivergenceSolution_zero_iff_of_aeElliptic
    (hΩopen : IsOpen Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha beta gamma : ℝ}
    (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb : ∀ i, ‖b i‖ ≤ beta) (hc : ‖c‖ ≤ gamma)
    {u : H¹₀(Ω)} :
    IsWeakShiftedFullDivergenceSolution
        (n := n) (Ω := Ω) a b c
        (coerciveShift (n := n) alpha beta gamma)
        (0 : L2) (0 : Fin n → L2) u ↔
      u = 0 :=
  isWeakShiftedFullDivergenceSolution_zero_iff
    (n := n) (Ω := Ω) hΩopen a b c
    (integratedElliptic_multiplication_of_ae
      (n := n) (Ω := Ω) a ha)
    hbeta hgamma hb hc

end MultiplicationCoefficients

end GraphSpace

end SobolevSpace
