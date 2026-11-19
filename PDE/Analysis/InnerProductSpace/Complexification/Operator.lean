/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.InnerProductSpace.Complexification.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Complexification of bounded operators

A bounded real operator `T` on a real inner product space `H` extends to the complex operator
`complexify T (x + i y) = T x + i T y` on `Complexification H`. The extension preserves the
operator norm, sums, products, powers and real scalar multiples, and it is injective, so it
embeds the ring of bounded real operators in the ring of bounded complex operators. It maps
compact operators to compact operators and conversely, and on a complete space it commutes with
taking adjoints.

Conjugating a complex operator `A` by the conjugation `C (x + i y) = x - i y` gives the complex
operator `conjOp A = C A C`. This is a ring automorphism that preserves the operator norm and
conjugates scalars. Its fixed points are the complexified real operators: if `conjOp A = A`, then
`A = complexify (realOp A)`, where `realOp A x` is the real part of `A (x + i 0)`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Complexification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The complexification `x + i y ↦ T x + i T y` of a bounded real operator. -/
def complexify (T : H →L[ℝ] H) : Complexification H →L[ℂ] Complexification H :=
  LinearMap.mkContinuous
    { toFun z := mk (T z.re) (T z.im)
      map_add' z w := by ext <;> simp
      map_smul' c z := by ext <;> simp } ‖T‖ fun z ↦ by
    rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow]
    change ‖mk (T z.re) (T z.im)‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖z‖ ^ 2
    have h₁ : ‖T z.re‖ ^ 2 ≤ (‖T‖ * ‖z.re‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm _) 2
    have h₂ : ‖T z.im‖ ^ 2 ≤ (‖T‖ * ‖z.im‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm _) 2
    rw [norm_sq_eq, norm_sq_eq z, re_mk, im_mk, mul_add]
    rw [mul_pow] at h₁ h₂
    linarith

theorem complexify_apply (T : H →L[ℝ] H) (z : Complexification H) :
    complexify T z = mk (T z.re) (T z.im) := rfl

@[simp]
theorem re_complexify (T : H →L[ℝ] H) (z : Complexification H) :
    (complexify T z).re = T z.re := rfl

@[simp]
theorem im_complexify (T : H →L[ℝ] H) (z : Complexification H) :
    (complexify T z).im = T z.im := rfl

@[simp]
theorem complexify_mk (T : H →L[ℝ] H) (x y : H) : complexify T (mk x y) = mk (T x) (T y) :=
  rfl

@[simp]
theorem complexify_ofReal (T : H →L[ℝ] H) (x : H) : complexify T (ofReal x) = ofReal (T x) := by
  ext <;> simp

/-- A real eigenvector of `T` is an eigenvector of `complexify T` with the same eigenvalue. -/
theorem complexify_ofReal_eq_smul {T : H →L[ℝ] H} {v : H} {ν : ℝ} (h : T v = ν • v) :
    complexify T (ofReal v) = (ν : ℂ) • ofReal v := by
  rw [complexify_ofReal, h, ofReal_smul, Complex.coe_smul]

@[simp]
theorem complexify_conjLIE (T : H →L[ℝ] H) (z : Complexification H) :
    complexify T (conjLIE z) = conjLIE (complexify T z) := by
  ext <;> simp

/-- A complex operator that acts as `T` on real vectors is the complexification of `T`. -/
theorem eq_complexify_of_apply_ofReal {A : Complexification H →L[ℂ] Complexification H}
    {T : H →L[ℝ] H} (h : ∀ x, A (ofReal x) = ofReal (T x)) : A = complexify T := by
  ext1 z
  conv_lhs => rw [← ofReal_re_add_I_smul_ofReal_im z]
  rw [map_add, map_smul, h, h]
  ext <;> simp

/-- Complexification preserves the operator norm. -/
@[simp]
theorem norm_complexify (T : H →L[ℝ] H) : ‖complexify T‖ = ‖T‖ := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ (norm_nonneg T) _) ?_
  refine T.opNorm_le_bound (norm_nonneg (complexify T)) fun x ↦ ?_
  simpa using (complexify T).le_opNorm (ofReal x)

@[simp]
theorem complexify_zero : complexify (0 : H →L[ℝ] H) = 0 := by
  ext z <;> simp

@[simp]
theorem complexify_one : complexify (1 : H →L[ℝ] H) = 1 := by
  ext z <;> simp

@[simp]
theorem complexify_id : complexify (ContinuousLinearMap.id ℝ H) =
    ContinuousLinearMap.id ℂ (Complexification H) :=
  complexify_one

@[simp]
theorem complexify_add (S T : H →L[ℝ] H) : complexify (S + T) = complexify S + complexify T := by
  ext z <;> simp

@[simp]
theorem complexify_neg (T : H →L[ℝ] H) : complexify (-T) = -complexify T := by
  ext z <;> simp

@[simp]
theorem complexify_sub (S T : H →L[ℝ] H) : complexify (S - T) = complexify S - complexify T := by
  ext z <;> simp

@[simp]
theorem complexify_smul (r : ℝ) (T : H →L[ℝ] H) : complexify (r • T) = r • complexify T := by
  ext z <;> simp

@[simp]
theorem complexify_comp (S T : H →L[ℝ] H) :
    complexify (S.comp T) = (complexify S).comp (complexify T) := by
  ext z <;> simp

@[simp]
theorem complexify_mul (S T : H →L[ℝ] H) : complexify (S * T) = complexify S * complexify T :=
  complexify_comp S T

/-- Complexification as a ring homomorphism of bounded operators. -/
def complexifyRingHom : (H →L[ℝ] H) →+* (Complexification H →L[ℂ] Complexification H) where
  toFun := complexify
  map_one' := complexify_one
  map_mul' := complexify_mul
  map_zero' := complexify_zero
  map_add' := complexify_add

@[simp]
theorem complexifyRingHom_apply (T : H →L[ℝ] H) : complexifyRingHom T = complexify T := rfl

@[simp]
theorem complexify_pow (T : H →L[ℝ] H) (n : ℕ) : complexify (T ^ n) = complexify T ^ n :=
  map_pow complexifyRingHom T n

@[simp]
theorem complexify_algebraMap (r : ℝ) :
    complexify (algebraMap ℝ (H →L[ℝ] H) r) =
      algebraMap ℂ (Complexification H →L[ℂ] Complexification H) (r : ℂ) := by
  ext z <;> simp

theorem complexify_injective : Function.Injective (complexify : (H →L[ℝ] H) → _) :=
  fun S T h ↦ ContinuousLinearMap.ext fun x ↦ by
    simpa using congrArg (fun A ↦ (A (ofReal x)).re) h

@[simp]
theorem complexify_inj {S T : H →L[ℝ] H} : complexify S = complexify T ↔ S = T :=
  complexify_injective.eq_iff

theorem commute_complexify_iff {S T : H →L[ℝ] H} :
    Commute (complexify S) (complexify T) ↔ Commute S T := by
  simp only [Commute, SemiconjBy, ← complexify_mul, complexify_inj]

/-- The complexification of a compact operator is compact. -/
theorem isCompactOperator_complexify {T : H →L[ℝ] H} (hT : IsCompactOperator T) :
    IsCompactOperator (complexify T) := by
  have hre : IsCompactOperator (ofRealCLM ∘ T ∘ reCLM : Complexification H → _) :=
    (hT.comp_clm reCLM).continuous_comp ofRealCLM.continuous
  have him : IsCompactOperator (ofRealCLM ∘ T ∘ imCLM : Complexification H → _) :=
    (hT.comp_clm imCLM).continuous_comp ofRealCLM.continuous
  convert hre.add (him.smul Complex.I) using 1
  funext z
  simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, reCLM_apply, imCLM_apply,
    ofRealCLM_apply]
  rw [← ofReal_re_add_I_smul_ofReal_im (complexify T z), re_complexify, im_complexify]

@[simp]
theorem isCompactOperator_complexify_iff {T : H →L[ℝ] H} :
    IsCompactOperator (complexify T) ↔ IsCompactOperator T := by
  refine ⟨fun h ↦ ?_, isCompactOperator_complexify⟩
  have h' : IsCompactOperator (reCLM ∘ (complexify T) ∘ ofRealCLM : H → H) :=
    (h.comp_clm ofRealCLM).continuous_comp reCLM.continuous
  convert h' using 1
  funext x
  simp

/-- On a complete space, complexification commutes with taking adjoints. -/
@[simp]
theorem complexify_adjoint [CompleteSpace H] (T : H →L[ℝ] H) :
    complexify (ContinuousLinearMap.adjoint T) = ContinuousLinearMap.adjoint (complexify T) := by
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun z w ↦ ?_
  apply Complex.ext <;>
    simp [ContinuousLinearMap.adjoint_inner_left]

/-- The complexification of an operator is self-adjoint exactly when the operator is. -/
theorem isSelfAdjoint_complexify_iff [CompleteSpace H] {T : H →L[ℝ] H} :
    IsSelfAdjoint (complexify T) ↔ IsSelfAdjoint T := by
  simp only [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, ← complexify_adjoint,
    complexify_inj]

/-- The conjugation `x + i y ↦ x - i y` as a continuous conjugate-linear map. -/
def conjCLM : Complexification H →L⋆[ℂ] Complexification H :=
  conjLIE.toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem conjCLM_apply (z : Complexification H) : conjCLM z = conjLIE z := rfl

/-- Conjugation `A ↦ C A C` of complex operators by the conjugation `C` of the
complexification, as a ring automorphism. -/
def conjOp :
    (Complexification H →L[ℂ] Complexification H) ≃+*
      (Complexification H →L[ℂ] Complexification H) where
  toFun A := (conjCLM.comp A : Complexification H →L⋆[ℂ] Complexification H).comp conjCLM
  invFun A := (conjCLM.comp A : Complexification H →L⋆[ℂ] Complexification H).comp conjCLM
  left_inv A := by ext z <;> simp
  right_inv A := by ext z <;> simp
  map_mul' A B := by ext z <;> simp
  map_add' A B := by ext z <;> simp

@[simp]
theorem conjOp_apply (A : Complexification H →L[ℂ] Complexification H) (z : Complexification H) :
    conjOp A z = conjLIE (A (conjLIE z)) := rfl

@[simp]
theorem conjOp_symm : (conjOp (H := H)).symm = conjOp := rfl

@[simp]
theorem conjOp_conjOp (A : Complexification H →L[ℂ] Complexification H) :
    conjOp (conjOp A) = A :=
  conjOp.symm_apply_apply A

/-- Conjugation is conjugate-linear in the scalar. Not a simp lemma: simplifying its left side
first tries the semilinear `map_smulₛₗ`, whose instance search on the ring equivalence `conjOp`
times out (simpNF linter). -/
theorem conjOp_smul (c : ℂ) (A : Complexification H →L[ℂ] Complexification H) :
    conjOp (c • A) = starRingEnd ℂ c • conjOp A := by
  ext z <;> simp [add_comm]

@[simp]
theorem conjOp_algebraMap (c : ℂ) :
    conjOp (algebraMap ℂ (Complexification H →L[ℂ] Complexification H) c) =
      algebraMap ℂ (Complexification H →L[ℂ] Complexification H) (starRingEnd ℂ c) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, conjOp_smul, map_one]

/-- Conjugation preserves the operator norm. -/
@[simp]
theorem norm_conjOp (A : Complexification H →L[ℂ] Complexification H) :
    ‖conjOp A‖ = ‖A‖ := by
  have h (B : Complexification H →L[ℂ] Complexification H) : ‖conjOp B‖ ≤ ‖B‖ :=
    (conjOp B).opNorm_le_bound (norm_nonneg B) fun z ↦ by
      simpa using B.le_opNorm (conjLIE z)
  exact le_antisymm (h A) (by simpa using h (conjOp A))

theorem conjOp_eq_self_iff {A : Complexification H →L[ℂ] Complexification H} :
    conjOp A = A ↔ ∀ z, A (conjLIE z) = conjLIE (A z) := by
  refine ⟨fun h z ↦ ?_, fun h ↦ ContinuousLinearMap.ext fun z ↦ by simp [h]⟩
  simpa using (congrArg (fun B ↦ B (conjLIE z)) h).symm

/-- A complexified real operator is fixed by conjugation. -/
@[simp]
theorem conjOp_complexify (T : H →L[ℝ] H) : conjOp (complexify T) = complexify T :=
  conjOp_eq_self_iff.mpr (complexify_conjLIE T)

/-- The real operator `x ↦ re (A (x + i 0))` determined by a complex operator. -/
def realOp (A : Complexification H →L[ℂ] Complexification H) : H →L[ℝ] H :=
  reCLM.comp ((A.restrictScalars ℝ).comp ofRealCLM)

@[simp]
theorem realOp_apply (A : Complexification H →L[ℂ] Complexification H) (x : H) :
    realOp A x = (A (ofReal x)).re := rfl

@[simp]
theorem realOp_complexify (T : H →L[ℝ] H) : realOp (complexify T) = T := by
  ext x
  simp

/-- The real part of a compact operator is compact. -/
theorem isCompactOperator_realOp {A : Complexification H →L[ℂ] Complexification H}
    (hA : IsCompactOperator A) : IsCompactOperator (realOp A) :=
  (hA.comp_clm ofRealCLM).continuous_comp reCLM.continuous

theorem norm_realOp_le (A : Complexification H →L[ℂ] Complexification H) :
    ‖realOp A‖ ≤ ‖A‖ :=
  (realOp A).opNorm_le_bound (norm_nonneg A) fun x ↦ by
    simpa using (norm_re_le (A (ofReal x))).trans (A.le_opNorm (ofReal x))

@[simp]
theorem realOp_zero : realOp (0 : Complexification H →L[ℂ] Complexification H) = 0 := by
  ext x
  simp

@[simp]
theorem realOp_one : realOp (1 : Complexification H →L[ℂ] Complexification H) = 1 := by
  ext x
  simp

@[simp]
theorem realOp_add (A B : Complexification H →L[ℂ] Complexification H) :
    realOp (A + B) = realOp A + realOp B := by
  ext x
  simp

@[simp]
theorem realOp_sub (A B : Complexification H →L[ℂ] Complexification H) :
    realOp (A - B) = realOp A - realOp B := by
  ext x
  simp

@[simp]
theorem realOp_smul (r : ℝ) (A : Complexification H →L[ℂ] Complexification H) :
    realOp (r • A) = r • realOp A := by
  ext x
  simp

/-- An operator fixed by conjugation maps real vectors to real vectors. -/
theorem apply_ofReal_of_conjOp_eq {A : Complexification H →L[ℂ] Complexification H}
    (hA : conjOp A = A) (x : H) : A (ofReal x) = ofReal (realOp A x) := by
  apply eq_ofReal_re_of_conjLIE_eq
  simpa using (conjOp_eq_self_iff.mp hA (ofReal x)).symm

/-- An operator fixed by conjugation is the complexification of its real part. -/
theorem complexify_realOp {A : Complexification H →L[ℂ] Complexification H}
    (hA : conjOp A = A) : complexify (realOp A) = A :=
  (eq_complexify_of_apply_ofReal (apply_ofReal_of_conjOp_eq hA)).symm

/-- The real part of a product is the product of the real parts when the right factor is fixed
by conjugation. -/
theorem realOp_mul {A B : Complexification H →L[ℂ] Complexification H} (hB : conjOp B = B) :
    realOp (A * B) = realOp A * realOp B := by
  ext x
  change (A (B (ofReal x))).re = realOp A (realOp B x)
  rw [apply_ofReal_of_conjOp_eq hB x]
  rfl

/-- The complexified real operators are exactly the operators fixed by conjugation. -/
theorem conjOp_eq_self_iff_exists_complexify_eq
    {A : Complexification H →L[ℂ] Complexification H} :
    conjOp A = A ↔ ∃ T : H →L[ℝ] H, complexify T = A :=
  ⟨fun h ↦ ⟨realOp A, complexify_realOp h⟩, fun ⟨T, hT⟩ ↦ hT ▸ conjOp_complexify T⟩

end PDE.Analysis.Complexification
