/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import PDE.Analysis.TrilinearForm
public import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Linear assembly and weak products of Lebesgue fields

A continuous linear map on a product acts on two fields with the same Lebesgue exponent. The
construction uses the two composition operators and addition. Its representatives and weak
convergence follow from those operations; no Hilbert assumption is placed on the Lebesgue
spaces.

For two scalar fields whose Hölder exponents give a product in `L²`, `productLoad`
pairs that product with an energy-space test represented in `L²`. Its bound combines
Hölder and Cauchy--Schwarz, on an arbitrary measure space.

`transportPairing` assembles all coefficient and derivative coordinates with
finite Hilbert-product norms. Its bound has constant one. Keeping the derivative
matrix as a separate input allows a transported correction to have nonzero
boundary values; the application supplies the derivative identities.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace PDE

end PDE

/-- Two `L⁴` factors have their product in `L²`. -/
instance ENNReal.HolderTriple.four_four_two : ENNReal.HolderTriple 4 4 2 := ⟨by
  change ((4 : NNReal) : ℝ≥0∞)⁻¹ + ((4 : NNReal) : ℝ≥0∞)⁻¹ =
    ((2 : NNReal) : ℝ≥0∞)⁻¹
  rw [← ENNReal.coe_inv (by norm_num : (4 : NNReal) ≠ 0),
    ← ENNReal.coe_inv (by norm_num : (2 : NNReal) ≠ 0), ← ENNReal.coe_add, ENNReal.coe_inj]
  norm_num⟩

namespace ContinuousLinearMap

variable {α E F G : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Apply a linear map to a pair of fields at a common exponent. -/
def compLpPair (B : E × F →L[ℝ] G) :
    (Lp E p μ × Lp F p μ) →L[ℝ] Lp G p μ :=
  ((B.comp (inl ℝ E F)).compLpL p μ).coprod
    ((B.comp (inr ℝ E F)).compLpL p μ)

/-- The assembled class represents the pointwise linear image of the two fields. -/
theorem coeFn_compLpPair (B : E × F →L[ℝ] G) (f : Lp E p μ) (g : Lp F p μ) :
    B.compLpPair (f, g) =ᵐ[μ] fun x ↦ B (f x, g x) := by
  filter_upwards [Lp.coeFn_add ((B.comp (inl ℝ E F)).compLpL p μ f)
    ((B.comp (inr ℝ E F)).compLpL p μ g),
    (B.comp (inl ℝ E F)).coeFn_compLpL f,
    (B.comp (inr ℝ E F)).coeFn_compLpL g] with x hx hf hg
  change (((B.comp (inl ℝ E F)).compLpL p μ f +
    (B.comp (inr ℝ E F)).compLpL p μ g) : Lp G p μ) x = _
  rw [hx, Pi.add_apply, hf, hg]
  exact (B.map_add (f x, 0) (0, g x)).symm.trans (by simp)

/-- Weak convergence of both fields gives weak convergence of their linear assembly. -/
theorem tendsto_weak_compLpPair (B : E × F →L[ℝ] G)
    {ι : Type*} {l : Filter ι} {f : ι → Lp E p μ} {f₀ : Lp E p μ}
    {g : ι → Lp F p μ} {g₀ : Lp F p μ}
    (hf : Tendsto (fun i ↦ toWeakSpace ℝ (Lp E p μ) (f i)) l
      (𝓝 (toWeakSpace ℝ (Lp E p μ) f₀)))
    (hg : Tendsto (fun i ↦ toWeakSpace ℝ (Lp F p μ) (g i)) l
      (𝓝 (toWeakSpace ℝ (Lp F p μ) g₀))) :
    Tendsto (fun i ↦ toWeakSpace ℝ (Lp G p μ) (B.compLpPair (f i, g i))) l
      (𝓝 (toWeakSpace ℝ (Lp G p μ) (B.compLpPair (f₀, g₀)))) := by
  have hleft := (WeakSpace.map ((B.comp (inl ℝ E F)).compLpL p μ)).continuous
  have hright := (WeakSpace.map ((B.comp (inr ℝ E F)).compLpL p μ)).continuous
  exact (hleft.continuousAt.tendsto.comp hf).add (hright.continuousAt.tendsto.comp hg)

section WeakProduct

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {q : ℝ≥0∞} [Fact (1 ≤ q)] [ENNReal.HolderTriple p q 2]

/-- A pointwise product as a weak load on an energy space. The test-function map `J`
lands in `L²`; Hölder's inequality puts the product of the two input fields in `L²`.
No geometric or finite-measure assumption is required. -/
def productLoad (J : V →L[ℝ] Lp ℝ 2 μ) :
    Lp ℝ p μ →L[ℝ] Lp ℝ q μ →L[ℝ] StrongDual ℝ V :=
  let load : Lp ℝ 2 μ →L[ℝ] StrongDual ℝ V :=
    ((compL ℝ V (Lp ℝ 2 μ) ℝ).flip J).comp (innerSL ℝ)
  (compL ℝ (Lp ℝ q μ) (Lp ℝ 2 μ) (StrongDual ℝ V) load).comp
    ((mul ℝ ℝ).holderL μ p q 2)

/-- The weak product load is the `L²` pairing against the represented test function. -/
theorem productLoad_apply (J : V →L[ℝ] Lp ℝ 2 μ)
    (f : Lp ℝ p μ) (g : Lp ℝ q μ) (v : V) :
    productLoad J f g v = inner ℝ ((mul ℝ ℝ).holder 2 f g) (J v) :=
  rfl

/-- Hölder and Cauchy--Schwarz give a reusable bound for the weak product load. -/
theorem norm_productLoad_apply_le (J : V →L[ℝ] Lp ℝ 2 μ)
    (f : Lp ℝ p μ) (g : Lp ℝ q μ) (v : V) :
    ‖productLoad J f g v‖ ≤ ‖J‖ * ‖f‖ * ‖g‖ * ‖v‖ := by
  have hproduct : ‖(mul ℝ ℝ).holder 2 f g‖ ≤ ‖f‖ * ‖g‖ := by
    calc
      ‖(mul ℝ ℝ).holder 2 f g‖ ≤ ‖mul ℝ ℝ‖ * ‖f‖ * ‖g‖ :=
        norm_holder_apply_apply_le (mul ℝ ℝ) f g
      _ ≤ 1 * ‖f‖ * ‖g‖ := by gcongr; exact opNorm_mul_le ℝ ℝ
      _ = ‖f‖ * ‖g‖ := by rw [one_mul]
  calc
    ‖productLoad J f g v‖ ≤ ‖(mul ℝ ℝ).holder 2 f g‖ * ‖J v‖ := by
      rw [productLoad_apply]
      exact norm_inner_le_norm _ _
    _ ≤ (‖f‖ * ‖g‖) * (‖J‖ * ‖v‖) := by
      gcongr
      exact J.le_opNorm v
    _ = ‖J‖ * ‖f‖ * ‖g‖ * ‖v‖ := by ring

end WeakProduct

section Transport

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

-- Cache the canonical structures before constructing three nested operator spaces.
/-- The `ℓ²` product norm on `τ`-tuples of `Lˢ` functions. -/
local instance normedAddCommGroupLpTuple (τ : Type*) [Fintype τ]
    (s : ℝ≥0∞) [Fact (1 ≤ s)] : NormedAddCommGroup (PiLp 2 (fun _ : τ ↦ Lp ℝ s μ)) :=
  PiLp.normedAddCommGroup (p := 2) (α := fun _ : τ ↦ Lp ℝ s μ)

/-- The real scalar action on `τ`-tuples of `Lˢ` functions, for the product norm. -/
local instance normedSpaceLpTuple (τ : Type*) [Fintype τ]
    (s : ℝ≥0∞) [Fact (1 ≤ s)] : NormedSpace ℝ (PiLp 2 (fun _ : τ ↦ Lp ℝ s μ)) :=
  PiLp.normedSpace (p := 2) (𝕜 := ℝ) (β := fun _ : τ ↦ Lp ℝ s μ)

/-- The seminormed group underlying `normedAddCommGroupLpTuple`. -/
local instance seminormedAddCommGroupLpTuple (τ : Type*) [Fintype τ]
    (s : ℝ≥0∞) [Fact (1 ≤ s)] : SeminormedAddCommGroup (PiLp 2 (fun _ : τ ↦ Lp ℝ s μ)) :=
  (normedAddCommGroupLpTuple τ s).toSeminormedAddCommGroup

/-- The operator norm on the dual of the `L⁴` tuples. -/
local instance seminormedAddCommGroupLpTupleDual :
    SeminormedAddCommGroup (StrongDual ℝ (PiLp 2 (fun _ : κ ↦ Lp ℝ 4 μ))) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

/-- The operator norm on maps from `L²` matrices to the dual of the `L⁴` tuples. -/
local instance seminormedAddCommGroupLpTupleBilinear : SeminormedAddCommGroup
    (PiLp 2 (fun _ : κ × ι ↦ Lp ℝ 2 μ) →L[ℝ]
      StrongDual ℝ (PiLp 2 (fun _ : κ ↦ Lp ℝ 4 μ))) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

/-- Addition on the dual of the `L⁴` tuples. -/
local instance addCommMonoidLpTupleDual :
    AddCommMonoid (StrongDual ℝ (PiLp 2 (fun _ : κ ↦ Lp ℝ 4 μ))) :=
  ContinuousLinearMap.addCommMonoid

/-- Addition on maps from `L²` matrices to the dual of the `L⁴` tuples. -/
local instance addCommMonoidLpTupleBilinear : AddCommMonoid
    (PiLp 2 (fun _ : κ × ι ↦ Lp ℝ 2 μ) →L[ℝ]
      StrongDual ℝ (PiLp 2 (fun _ : κ ↦ Lp ℝ 4 μ))) :=
  ContinuousLinearMap.addCommMonoid

/-- Addition on the trilinear forms on `L⁴` tuples, `L²` matrices and `L⁴` tuples. -/
local instance addCommMonoidLpTupleTrilinear : AddCommMonoid (PDE.Analysis.ContinuousTrilinearForm
    (PiLp 2 (fun _ : ι ↦ Lp ℝ 4 μ)) (PiLp 2 (fun _ : κ × ι ↦ Lp ℝ 2 μ))
    (PiLp 2 (fun _ : κ ↦ Lp ℝ 4 μ))) := ContinuousLinearMap.addCommMonoid

/-- The convection pairing of an `L⁴` coefficient, an `L²` derivative matrix,
and an `L⁴` test field. The finite products carry their Hilbert norms.

The derivative matrix is supplied independently of the transported field;
it can therefore come from a finite-rank correction with a nonzero boundary trace. -/
def transportPairing :
    PDE.Analysis.ContinuousTrilinearForm
      (PiLp 2 (fun _ : ι ↦ Lp ℝ 4 μ))
      (PiLp 2 (fun _ : κ × ι ↦ Lp ℝ 2 μ))
      (PiLp 2 (fun _ : κ ↦ Lp ℝ 4 μ)) :=
  let πA := fun i : ι ↦ (proj i).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ Lp ℝ 4 μ)).toContinuousLinearMap
  let πD := fun ki : κ × ι ↦ (proj ki).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ × ι ↦ Lp ℝ 2 μ)).toContinuousLinearMap
  let πV := fun k : κ ↦ (proj k).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ ↦ Lp ℝ 4 μ)).toContinuousLinearMap
  let P := productLoad (p := 4) (q := 4) (ContinuousLinearMap.id ℝ (Lp ℝ 2 μ))
  let flip : (Lp ℝ 4 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] ℝ) →L[ℝ]
      Lp ℝ 2 μ →L[ℝ] Lp ℝ 4 μ →L[ℝ] ℝ :=
    (flipₗᵢ ℝ (Lp ℝ 4 μ) (Lp ℝ 2 μ) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  ∑ k, ∑ i, PDE.Analysis.ContinuousTrilinearForm.restrict
    (flip.comp P) (πA i) (πD (k, i)) (πV k)

/-- Coordinate evaluation of the convection pairing. The entries of the supplied
matrix are the derivatives of the transported component in each spatial direction. -/
theorem transportPairing_apply
    (A : PiLp 2 (fun _ : ι ↦ Lp ℝ 4 μ))
    (D : PiLp 2 (fun _ : κ × ι ↦ Lp ℝ 2 μ))
    (V : PiLp 2 (fun _ : κ ↦ Lp ℝ 4 μ)) :
    transportPairing A D V =
      ∑ k, ∑ i, inner ℝ ((mul ℝ ℝ).holder 2 (A i) (V k)) (D (k, i)) := by
  simp only [transportPairing, sum_apply, PDE.Analysis.ContinuousTrilinearForm.restrict_apply]
  rfl

/-- The pairing represents the literal coordinate integral of coefficient times
derivative times test. Its Hölder product is integrable on any measure space. -/
theorem transportPairing_eq_integral
    (A : PiLp 2 (fun _ : ι ↦ Lp ℝ 4 μ))
    (D : PiLp 2 (fun _ : κ × ι ↦ Lp ℝ 2 μ))
    (V : PiLp 2 (fun _ : κ ↦ Lp ℝ 4 μ)) :
    transportPairing A D V = ∑ k, ∑ i, ∫ x, A i x * D (k, i) x * V k x ∂μ := by
  rw [transportPairing_apply]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(mul ℝ ℝ).coeFn_holder (r := 2) (A i) (V k)] with x hx
  simp only [hx, mul_apply', RCLike.inner_apply, conj_trivial]
  ring

/-- Hölder and finite-dimensional Cauchy--Schwarz give constant one for the full
coefficient, derivative matrix, and test norms. No coordinate-count factor is lost. -/
theorem norm_transportPairing_le
    (A : PiLp 2 (fun _ : ι ↦ Lp ℝ 4 μ))
    (D : PiLp 2 (fun _ : κ × ι ↦ Lp ℝ 2 μ))
    (V : PiLp 2 (fun _ : κ ↦ Lp ℝ 4 μ)) :
    ‖transportPairing A D V‖ ≤ ‖A‖ * ‖D‖ * ‖V‖ := by
  have hproduct (i : ι) (k : κ) :
      ‖inner ℝ ((mul ℝ ℝ).holder 2 (A i) (V k)) (D (k, i))‖ ≤
        ‖A i‖ * ‖V k‖ * ‖D (k, i)‖ := by
    calc
      _ ≤ ‖(mul ℝ ℝ).holder 2 (A i) (V k)‖ * ‖D (k, i)‖ := norm_inner_le_norm _ _
      _ ≤ (‖A i‖ * ‖V k‖) * ‖D (k, i)‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        calc
          _ ≤ ‖mul ℝ ℝ‖ * ‖A i‖ * ‖V k‖ := norm_holder_apply_apply_le _ _ _
          _ ≤ _ := by
            have hmul := opNorm_mul_le ℝ ℝ
            nlinarith only [hmul, norm_nonneg (A i), norm_nonneg (V k),
              mul_nonneg (norm_nonneg (A i)) (norm_nonneg (V k))]
  have hCS : (∑ k, ∑ i, ‖A i‖ * ‖V k‖ * ‖D (k, i)‖) ^ 2 ≤
      (∑ i, ‖A i‖ ^ 2) * (∑ k, ‖V k‖ ^ 2) * (∑ ki, ‖D ki‖ ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) (Finset.univ : Finset (κ × ι))
      (fun ki ↦ ‖A ki.2‖ * ‖V ki.1‖) (fun ki ↦ ‖D ki‖)
    simp only [Fintype.sum_prod_type] at h ⊢
    simp_rw [mul_pow, ← Finset.sum_mul] at h
    rw [← Finset.mul_sum] at h
    exact h
  have hsum : (∑ k, ∑ i, ‖A i‖ * ‖V k‖ * ‖D (k, i)‖) ≤ ‖A‖ * ‖D‖ * ‖V‖ := by
    apply (sq_le_sq₀
      (Finset.sum_nonneg fun k _ ↦ Finset.sum_nonneg fun i _ ↦
        mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))
      (by positivity)).mp
    calc
      _ ≤ _ := hCS
      _ = _ := by
        rw [mul_pow, mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
          PiLp.norm_sq_eq_of_L2]
        exact mul_right_comm _ _ _
  calc
    _ ≤ ∑ k, ∑ i, ‖inner ℝ ((mul ℝ ℝ).holder 2 (A i) (V k)) (D (k, i))‖ := by
      rw [transportPairing_apply]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ norm_sum_le _ _)
    _ ≤ ∑ k, ∑ i, ‖A i‖ * ‖V k‖ * ‖D (k, i)‖ :=
      Finset.sum_le_sum fun k _ ↦ Finset.sum_le_sum fun i _ ↦ hproduct i k
    _ ≤ _ := hsum

end Transport

end ContinuousLinearMap
