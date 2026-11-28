/-
Authors: Levent Alpöge, Tristan Buckmaster

The lemmas of this file come from modules of the Lean package of the paper
"Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where they were steps of longer proofs. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.GDelta.MetrizableSpace
public import PDE.Analysis.Complex.Numbers

set_option linter.style.header false

/-!
# Matrices and quadratic forms

The lemmas compute products of matrices with vectors, quadratic forms of Hermitian and of positive
semidefinite matrices, and entries of small matrices. The proofs expand the products with
`Matrix.mulVec`, `dotProduct` and `Finset.sum_comm` and use the lemmas of Mathlib on Hermitian
matrices.

## Main results

* `PDE.Analysis.abs_mulVec_apply_le`: For a real square matrix `N` indexed by `Fin k` and a vector
  `w`, each coordinate of the product satisfies `|(N *ᵥ w) i| ≤ ∑ j, |N i j| * |w j|`.
* `PDE.Analysis.abs_re_sum_conj_mul_mul_le`: Let `A` be a complex `12 × 12` matrix with
  `‖A i j‖ ≤ CA` for all `i`, `j`, and let `U W : Fin 12 → ℂ` satisfy `‖U i‖ ^ 2 ≤ EU` and
  `‖W i‖ ^ 2 ≤ EW` for all `i`. Then
  `|(∑ i, ∑ j, (conj (U i) * A i j * W j + conj (W i) * A i j * U j)).re| ≤ 288 * CA * (EU + EW)`.
  Each of the `144` summands has norm at most `2 * CA * (EU + EW)`.
* `PDE.Analysis.conjTranspose_map_ofReal_of_transpose_eq`: If a real square matrix `M` is symmetric,
  `Mᵀ = M`, then its entrywise coercion to `ℂ` is Hermitian:
  `(M.map (fun s ↦ (s : ℂ)))ᴴ = M.map (fun s ↦ (s : ℂ))`.
* `PDE.Analysis.convexOn_univ_sum_mul_sq`: For a finite set `t` of indices in `Fin k` and real
  weights `s`, the function `p ↦ ∑ j ∈ t, (s j * p j) ^ 2` is convex on the whole space `Fin k → ℝ`.
* `PDE.Analysis.dotProduct_mulVec_eq_sum_of_vec_zero`: For a real `N × N` matrix `A`, a finite set
  `S` of indices and a vector `v` with `v a = 0` for all `a ∉ S`, the quadratic form is a sum over
  `S`: `v ⬝ᵥ (A *ᵥ v) = ∑ a ∈ S, ∑ b ∈ S, v a * A a b * v b`. The terms with an index outside `S`
  vanish.
* `PDE.Analysis.fun_ite_eq_pi_single_one`: For `j : Fin 12`, the function
  `fun k => if j = k then (1 : ℂ) else 0` on `Fin 12` equals `Pi.single j 1`.
* `PDE.Analysis.im_inv_mulVec_eq_zero_of_real`: If all entries of a complex square matrix `A`
  indexed by `Fin n` and of a vector `u` are fixed by complex conjugation, that is, are real, then
  every coordinate of `A⁻¹ *ᵥ u` has imaginary part `0`.
* `PDE.Analysis.isUnit_det_of_star_dotProduct_mulVec_pos`: If a square complex matrix `G` satisfies
  `0 < (star c ⬝ᵥ (G *ᵥ c)).re` for every nonzero vector `c`, then `G.det` is a unit. No symmetry of
  `G` is assumed.

There are 29 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open Matrix ComplexConjugate
open scoped ComplexOrder

namespace PDE.Analysis

/-- For a real square matrix `N` indexed by `Fin k` and a vector `w`, each coordinate of the product
satisfies `|(N *ᵥ w) i| ≤ ∑ j, |N i j| * |w j|`. -/
theorem abs_mulVec_apply_le {k : ℕ} (N : Matrix (Fin k) (Fin k) ℝ) (w : Fin k → ℝ)
    (i : Fin k) : |(N *ᵥ w) i| ≤ ∑ j, |N i j| * |w j| := by
  rw [Matrix.mulVec_apply_eq_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  exact abs_mul _ _

/-- Let `A` be a complex `12 × 12` matrix with `‖A i j‖ ≤ CA` for all `i`, `j`, and let
`U W : Fin 12 → ℂ` satisfy `‖U i‖ ^ 2 ≤ EU` and `‖W i‖ ^ 2 ≤ EW` for all `i`. Then
`|(∑ i, ∑ j, (conj (U i) * A i j * W j + conj (W i) * A i j * U j)).re| ≤ 288 * CA * (EU +
EW)`. Each of the `144` summands has norm at most `2 * CA * (EU + EW)`. -/
theorem abs_re_sum_conj_mul_mul_le (A : Matrix (Fin 12) (Fin 12) ℂ) (CA : ℝ)
    (hA : ∀ i j, ‖A i j‖ ≤ CA) (U W : Fin 12 → ℂ)
    (EU EW : ℝ) (hU : ∀ i, ‖U i‖ ^ 2 ≤ EU) (hW : ∀ i, ‖W i‖ ^ 2 ≤ EW) :
    |(∑ i, ∑ j, ((starRingEnd ℂ) (U i) * A i j * W j + (starRingEnd ℂ) (W i) * A i j * U j)).re|
      ≤ 288 * CA * (EU + EW) := by
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ i j, ‖(starRingEnd ℂ) (U i) * A i j * W j + (starRingEnd ℂ) (W i) * A i j * U j‖
      ≤ 2 * CA * (EU + EW) := by
    intro i j
    refine (norm_add_le _ _).trans ?_
    have a1 := norm_conj_mul_mul_le_mul_add (U i) (W j) (A i j) CA (hA i j) EU EW (hU i) (hW j)
    have a2 := norm_conj_mul_mul_le_mul_add (W i) (U j) (A i j) CA (hA i j) EW EU (hW i) (hU j)
    linarith
  calc ∑ i, ‖∑ j, ((starRingEnd ℂ) (U i) * A i j * W j + (starRingEnd ℂ) (W i) * A i j * U j)‖
      ≤ ∑ i : Fin 12, ∑ j : Fin 12, 2 * CA * (EU + EW) :=
        Finset.sum_le_sum fun i _ ↦ (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ h i j)
    _ = 288 * CA * (EU + EW) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

/-- If a real square matrix `M` is symmetric, `Mᵀ = M`, then its entrywise coercion to `ℂ` is
Hermitian: `(M.map (fun s ↦ (s : ℂ)))ᴴ = M.map (fun s ↦ (s : ℂ))`. -/
theorem conjTranspose_map_ofReal_of_transpose_eq {n : Type*} (M : Matrix n n ℝ) (hM : Mᵀ = M) :
    (M.map (fun s : ℝ ↦ (s : ℂ)))ᴴ = M.map (fun s : ℝ ↦ (s : ℂ)) := by
  ext i j
  have h := congrFun (congrFun hM j) i
  simp only [transpose_apply] at h
  simp [conjTranspose_apply, map_apply, h]

/-- For a finite set `t` of indices in `Fin k` and real weights `s`, the function
`p ↦ ∑ j ∈ t, (s j * p j) ^ 2` is convex on the whole space `Fin k → ℝ`. The proof is by induction
on `t`: each term is the square of a linear functional, hence convex, and a sum of convex functions
is convex. -/
theorem convexOn_univ_sum_mul_sq {k : ℕ} (t : Finset (Fin k)) (s : Fin k → ℝ) :
    ConvexOn ℝ Set.univ (fun p : Fin k → ℝ ↦ ∑ j ∈ t, (s j * p j) ^ 2) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using convexOn_const (0 : ℝ) (convex_univ (𝕜 := ℝ) (E := Fin k → ℝ))
  | insert a t ha ih =>
    have h1 : ConvexOn ℝ Set.univ (fun p : Fin k → ℝ ↦ (s a * p a) ^ 2) := by
      have := (even_two.convexOn_pow (𝕜 := ℝ)).comp_linearMap
        (s a • LinearMap.proj a : (Fin k → ℝ) →ₗ[ℝ] ℝ)
      simpa [Function.comp_def] using this
    have e : (fun p : Fin k → ℝ ↦ ∑ j ∈ insert a t, (s j * p j) ^ 2) =
        (fun p ↦ (s a * p a) ^ 2) + (fun p ↦ ∑ j ∈ t, (s j * p j) ^ 2) := by
      funext p
      simp [Finset.sum_insert ha]
    rw [e]
    exact h1.add ih

/-- For a real `N × N` matrix `A`, a finite set `S` of indices and a vector `v` with `v a = 0` for
all `a ∉ S`, the quadratic form is a sum over `S`:
`v ⬝ᵥ (A *ᵥ v) = ∑ a ∈ S, ∑ b ∈ S, v a * A a b * v b`. The terms with an index outside `S` vanish.
-/
theorem dotProduct_mulVec_eq_sum_of_vec_zero {N : ℕ} (S : Finset (Fin N))
    (A : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ)
    (hv : ∀ a ∉ S, v a = 0) :
    v ⬝ᵥ (A *ᵥ v) = ∑ a ∈ S, ∑ b ∈ S, v a * A a b * v b := by
  symm
  calc ∑ a ∈ S, ∑ b ∈ S, v a * A a b * v b = ∑ a ∈ S, ∑ b, v a * A a b * v b :=
        Finset.sum_congr rfl fun a _ ↦
          Finset.sum_subset (Finset.subset_univ S) (fun b _ hb ↦ by simp [hv b hb])
    _ = ∑ a, ∑ b, v a * A a b * v b :=
        Finset.sum_subset (Finset.subset_univ S) (fun a _ ha ↦ Finset.sum_eq_zero fun b _ ↦ by
          simp [hv a ha])
    _ = v ⬝ᵥ (A *ᵥ v) := by
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring

/-- For `j : Fin 12`, the function `fun k ↦ if j = k then (1 : ℂ) else 0` on `Fin 12` equals
`Pi.single j 1`. -/
theorem fun_ite_eq_pi_single_one (j : Fin 12) : (fun k : Fin 12 ↦ if j = k then (1 : ℂ) else 0) =
    Pi.single j 1 := by
  funext k
  simp [Pi.single_apply, eq_comm]

/-- If a square complex matrix `G` satisfies `0 < (star c ⬝ᵥ (G *ᵥ c)).re` for every nonzero vector
`c`, then `G.det` is a unit. No symmetry of `G` is assumed. -/
theorem isUnit_det_of_star_dotProduct_mulVec_pos {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℂ) (hpos : ∀ c : ι → ℂ, c ≠ 0 → 0 < (star c ⬝ᵥ (G *ᵥ c)).re) :
    IsUnit G.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  by_contra hne
  have h := hpos (x - y) (sub_ne_zero.mpr hne)
  rw [Matrix.mulVec_sub, hxy, sub_self, dotProduct_zero] at h
  simp at h

/-- Let `U` be a real `k × k` matrix and `δ < 1` such that
`|∑ j, (U *ᵥ z) j ^ 2 - ∑ j, z j ^ 2| ≤ δ * ∑ j, z j ^ 2` for every vector `z`. Then `U.det` is a
unit. A nonzero `v` with `U *ᵥ v = 0` would give `∑ j, v j ^ 2 ≤ δ * ∑ j, v j ^ 2`, which is
impossible when `δ < 1`. -/
theorem isUnit_det_of_sum_sq_mulVec_le {k : ℕ} (U : Matrix (Fin k) (Fin k) ℝ) (δ : ℝ)
    (hU : ∀ z : Fin k → ℝ, |∑ j, (U *ᵥ z) j ^ 2 - ∑ j, z j ^ 2| ≤ δ * ∑ j, z j ^ 2) (hδ : δ < 1) :
    IsUnit U.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hUv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
  have h1 := hU v
  rw [hUv] at h1
  have hs : 0 ≤ ∑ j, v j ^ 2 := Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  have e : ∑ j, ((0 : Fin k → ℝ) j) ^ 2 = 0 := by simp
  rw [e, zero_sub, abs_neg, abs_of_nonneg hs] at h1
  have hS : ∑ j, v j ^ 2 = 0 := by nlinarith
  apply hv
  funext j
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ sq_nonneg (v i))).1 hS j
      (Finset.mem_univ j)
  simpa using hj

/-- For a complex square matrix `A` indexed by `Fin n`, entrywise conjugation commutes with the
matrix inverse: `(A⁻¹).map (starRingEnd ℂ) = (A.map (starRingEnd ℂ))⁻¹`. -/
theorem map_conj_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (A⁻¹).map (starRingEnd ℂ) = (A.map (starRingEnd ℂ))⁻¹ := by
  have e : ∀ B : Matrix (Fin n) (Fin n) ℂ, B.map (starRingEnd ℂ) = B.conjTranspose.transpose := by
    intro B
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [e, e, Matrix.conjTranspose_nonsing_inv, Matrix.transpose_nonsing_inv]

/-- If the determinant of a real square matrix `M` is a unit, then the entrywise coercions to `ℂ` of
`M` and of `M⁻¹` multiply to the identity:
`M.map (fun s ↦ (s : ℂ)) * M⁻¹.map (fun s ↦ (s : ℂ)) = 1`. -/
theorem map_ofReal_mul_map_inv_eq_one {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ)
    (hM : IsUnit M.det) :
    M.map (fun s : ℝ ↦ (s : ℂ)) * M⁻¹.map (fun s : ℝ ↦ (s : ℂ)) = 1 := by
  have h : (M * M⁻¹).map (fun s : ℝ ↦ (s : ℂ)) =
      M.map (fun s : ℝ ↦ (s : ℂ)) * M⁻¹.map (fun s : ℝ ↦ (s : ℂ)) :=
    Matrix.map_mul (f := Complex.ofRealHom)
  rw [← h, mul_nonsing_inv M hM]
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

/-- For complex square blocks `M i` indexed by a finite type and a vector `x` on the sigma type, the
block diagonal matrix acts block by block:
`(Matrix.blockDiagonal' M *ᵥ x) ⟨i, a⟩ = (M i *ᵥ fun b ↦ x ⟨i, b⟩) a`. -/
theorem mulVec_blockDiagonal_sigma_apply {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    [∀ i, Fintype (X i)]
    (M : (i : ι) → Matrix (X i) (X i) ℂ) (x : (Σ i, X i) → ℂ) (i : ι) (a : X i) :
    (Matrix.blockDiagonal' M *ᵥ x) ⟨i, a⟩ = (M i *ᵥ fun b ↦ x ⟨i, b⟩) a := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_sigma, Finset.sum_eq_single i]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro j _ hj
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    rw [Matrix.blockDiagonal'_apply_ne M a b (Ne.symm hj), zero_mul]
  · simp

/-- For a positive definite real matrix `G`, the matrix
`N = hG.isHermitian.cfc (fun x ↦ (Real.sqrt x)⁻¹)`, the inverse square root of `G` in the
functional calculus, satisfies `N * G * Nᵀ = 1`. The proof uses that `N` is symmetric, that the
functional calculus is multiplicative, and that `(Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹ = 1` at each
eigenvalue `x` of `G`, which is positive. -/
theorem posDef_cfc_inv_sqrt_mul_mul_transpose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosDef) :
    hG.isHermitian.cfc (fun x ↦ (Real.sqrt x)⁻¹) * G *
      (hG.isHermitian.cfc (fun x ↦ (Real.sqrt x)⁻¹)).transpose = 1 := by
  have hH := hG.isHermitian
  rw [← hH.cfc_eq]
  have hsa : IsSelfAdjoint (cfc (fun x : ℝ ↦ (Real.sqrt x)⁻¹) G) := cfc_predicate _ _
  have htr : (cfc (fun x : ℝ ↦ (Real.sqrt x)⁻¹) G).transpose =
      cfc (fun x : ℝ ↦ (Real.sqrt x)⁻¹) G := by
    have h := hsa.star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hfin : (spectrum ℝ G).Finite := Matrix.finite_real_spectrum
  have hsG : IsSelfAdjoint G := hH
  rw [htr]
  calc cfc (fun x : ℝ ↦ (Real.sqrt x)⁻¹) G * G * cfc (fun x : ℝ ↦ (Real.sqrt x)⁻¹) G
      = cfc (fun x : ℝ ↦ (Real.sqrt x)⁻¹) G * cfc (fun x : ℝ ↦ x) G *
          cfc (fun x : ℝ ↦ (Real.sqrt x)⁻¹) G := by
        rw [cfc_id' ℝ G]
    _ = cfc (fun x : ℝ ↦ (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹) G := by
        rw [← cfc_mul (fun x : ℝ ↦ (Real.sqrt x)⁻¹) (fun x : ℝ ↦ x) G (hfin.continuousOn _)
            (hfin.continuousOn _),
          ← cfc_mul (fun x : ℝ ↦ (Real.sqrt x)⁻¹ * x) (fun x : ℝ ↦ (Real.sqrt x)⁻¹) G
            (hfin.continuousOn _) (hfin.continuousOn _)]
    _ = cfc (fun _ : ℝ ↦ (1 : ℝ)) G := by
        refine cfc_congr fun x hx ↦ ?_
        obtain ⟨i, rfl⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hx
        have h0 := hG.eigenvalues_pos i
        have hss := Real.mul_self_sqrt h0.le
        have e : (Real.sqrt (hH.eigenvalues i))⁻¹ * hH.eigenvalues i *
            (Real.sqrt (hH.eigenvalues i))⁻¹ =
            hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i) * Real.sqrt (hH.eigenvalues i))⁻¹ := by
          rw [mul_inv]; ring
        change (Real.sqrt (hH.eigenvalues i))⁻¹ * hH.eigenvalues i *
            (Real.sqrt (hH.eigenvalues i))⁻¹ = 1
        rw [e, hss, mul_inv_cancel₀ h0.ne']
    _ = 1 := cfc_const_one ℝ G

/-- Let `Γ` be a positive definite complex matrix and `τ` a vector of positive reals with
`τ i = τ i'` whenever `Γ i i' ≠ 0`. Then the matrix `M` with entries `M i i' = Γ i i' / τ i` is
positive definite. Proof idea: `M = Dᴴ * Γ * D` for the diagonal matrix `D` with entries
`Real.sqrt (τ i)⁻¹`, and multiplication by `D` is injective. -/
theorem posDef_of_apply_eq_div_of_posDef {n : Type*} [Finite n]
    {Γ M : Matrix n n ℂ} (hΓ : Γ.PosDef) (τ : n → ℝ) (hτ : ∀ i, 0 < τ i)
    (hblock : ∀ i i', Γ i i' ≠ 0 → τ i = τ i') (hM : ∀ i i', M i i' = Γ i i' / (τ i : ℂ)) :
    M.PosDef := by
  classical
  have := Fintype.ofFinite n
  have hs0 : ∀ i, 0 < Real.sqrt (τ i)⁻¹ := fun i ↦ Real.sqrt_pos.mpr (inv_pos.mpr (hτ i))
  have hss : ∀ i, Real.sqrt (τ i)⁻¹ * Real.sqrt (τ i)⁻¹ = (τ i)⁻¹ :=
    fun i ↦ Real.mul_self_sqrt (inv_nonneg.mpr (hτ i).le)
  have hMeq : M = (diagonal fun i ↦ ((Real.sqrt (τ i)⁻¹ : ℝ) : ℂ))ᴴ * Γ
      * diagonal fun i ↦ ((Real.sqrt (τ i)⁻¹ : ℝ) : ℂ) := by
    ext i i'
    rw [mul_diagonal, diagonal_conjTranspose, diagonal_mul, hM]
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    by_cases h : Γ i i' = 0
    · simp [h]
    · have hti := hblock i i' h
      rw [← hti, div_eq_mul_inv]
      have e2 : ((Real.sqrt (τ i)⁻¹ : ℝ) : ℂ) * Γ i i' * ((Real.sqrt (τ i)⁻¹ : ℝ) : ℂ)
          = Γ i i' * ((Real.sqrt (τ i)⁻¹ * Real.sqrt (τ i)⁻¹ : ℝ) : ℂ) := by push_cast; ring
      rw [e2, hss, Complex.ofReal_inv]
  rw [hMeq]
  refine hΓ.conjTranspose_mul_mul_same ?_
  intro x x' hxx
  funext i
  have h1 := congrFun hxx i
  simp only [mulVec_diagonal] at h1
  exact mul_left_cancel₀ (by exact_mod_cast (hs0 i).ne') h1

/-- For vectors `u w : n → ℂ` over a finite type `n`, `(star u ⬝ᵥ w).re = (star w ⬝ᵥ u).re`. -/
theorem re_star_dotProduct_comm {n : Type*} [Fintype n] (u w : n → ℂ) :
    (star u ⬝ᵥ w).re = (star w ⬝ᵥ u).re := by
  simp only [dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- For a real `t` and vectors `u w : n → ℂ` over a finite type `n`,
`(star ((t : ℂ) • u) ⬝ᵥ w).re = t * (star u ⬝ᵥ w).re`. -/
theorem re_star_ofReal_smul_dotProduct {n : Type*} [Fintype n] (t : ℝ) (u w : n → ℂ) :
    (star ((t : ℂ) • u) ⬝ᵥ w).re = t * (star u ⬝ᵥ w).re := by
  rw [star_smul, Complex.star_def, Complex.conj_ofReal, smul_dotProduct, smul_eq_mul,
    Complex.re_ofReal_mul]

/-- Let `F : Fin 3 → Fin 3 → ℂ` have real entries (`(F a b).im = 0` for all `a`, `b`) and suppose
`∑ a, ∑ b, u a * (F a b).re * u b ≤ lam * ∑ a, u a ^ 2` for all `u : Fin 3 → ℝ`. Then for every
`w : Fin 3 → ℂ`, `(∑ a, ∑ b, conj (w a) * (F a b * w b)).re ≤ lam * ∑ a, ‖w a‖ ^ 2`. The proof
applies the real bound to the real and imaginary parts of `w` and adds the two inequalities. -/
theorem re_sum_conj_mul_mul_le (F : Fin 3 → Fin 3 → ℂ) (hreal : ∀ a b, (F a b).im = 0) (lam : ℝ)
    (hle : ∀ u : Fin 3 → ℝ, ∑ a, ∑ b, u a * (F a b).re * u b ≤ lam * ∑ a, u a ^ 2) (w : Fin 3 → ℂ) :
    (∑ a, ∑ b, conj (w a) * (F a b * w b)).re ≤ lam * ∑ a, ‖w a‖ ^ 2 := by
  have h1 := hle (fun a ↦ (w a).re)
  have h2 := hle (fun a ↦ (w a).im)
  have e : (∑ a, ∑ b, conj (w a) * (F a b * w b)).re
      = (∑ a, ∑ b, (w a).re * (F a b).re * (w b).re) + ∑ a, ∑ b,
          (w a).im * (F a b).re * (w b).im := by
    simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        hreal]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    ring
  have e2 : ∑ a, ‖w a‖ ^ 2 = ∑ a, (w a).re ^ 2 + ∑ a, (w a).im ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [e, e2]
  linarith

/-- For a complex matrix `M` and vectors `x`, `w`, the conjugate transpose is the adjoint for the
pairing `star x ⬝ᵥ w`: `star x ⬝ᵥ (Mᴴ *ᵥ w) = star (M *ᵥ x) ⬝ᵥ w`. -/
theorem star_dotProduct_conjTranspose_mulVec {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ)
    (x : n → ℂ) (w : m → ℂ) : star x ⬝ᵥ (Mᴴ *ᵥ w) = star (M *ᵥ x) ⬝ᵥ w := by
  rw [dotProduct_mulVec, star_mulVec]

/-- If `n = 0`, then for every complex matrix `A` and every vector `u` indexed by `Fin n`,
`star u ⬝ᵥ (A⁻¹ *ᵥ u) = 0`. -/
theorem star_dotProduct_inv_mulVec_fin_zero {n : ℕ} (hn : n = 0) (A : Matrix (Fin n) (Fin n) ℂ)
    (u : Fin n → ℂ) :
    star u ⬝ᵥ (A⁻¹ *ᵥ u) = 0 := by
  subst hn
  simp [dotProduct]

/-- For a Hermitian complex matrix `G` and vectors `x`, `c`, the form is conjugate symmetric:
`star x ⬝ᵥ (G *ᵥ c) = conj (star c ⬝ᵥ (G *ᵥ x))`. -/
theorem star_dotProduct_mulVec_conj_symm {ι : Type} [Fintype ι] (G : Matrix ι ι ℂ)
    (hH : G.IsHermitian) (x c : ι → ℂ) :
    star x ⬝ᵥ (G *ᵥ c) = (starRingEnd ℂ) (star c ⬝ᵥ (G *ᵥ x)) := by
  have h1 : star c ⬝ᵥ (G *ᵥ x) = star (G *ᵥ c) ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, hH.eq]
  rw [h1]
  simp only [dotProduct, map_sum, map_mul, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [mul_comm]

/-- For a finite set `S` of indices, a real `N × N` matrix `A` with `A a b = 0` whenever `a ∉ S` or
`b ∉ S`, and any vector `v`, `∑ a ∈ S, ∑ b ∈ S, v a * A a b * v b = v ⬝ᵥ (A *ᵥ v)`. The terms with
an index outside `S` vanish. -/
theorem sum_eq_dotProduct_mulVec_of_matrix_zero {N : ℕ} (S : Finset (Fin N))
    (A : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ)
    (hA : ∀ a b, (a ∉ S ∨ b ∉ S) → A a b = 0) :
    ∑ a ∈ S, ∑ b ∈ S, v a * A a b * v b = v ⬝ᵥ (A *ᵥ v) := by
  calc ∑ a ∈ S, ∑ b ∈ S, v a * A a b * v b = ∑ a ∈ S, ∑ b, v a * A a b * v b :=
        Finset.sum_congr rfl fun a _ ↦
          Finset.sum_subset (Finset.subset_univ S) (fun b _ hb ↦ by simp [hA a b (Or.inr hb)])
    _ = ∑ a, ∑ b, v a * A a b * v b :=
        Finset.sum_subset (Finset.subset_univ S) (fun a _ ha ↦ Finset.sum_eq_zero fun b _ ↦ by
          simp [hA a b (Or.inl ha)])
    _ = v ⬝ᵥ (A *ᵥ v) := by
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring

/-- Orthonormal columns are preserved by the Kronecker product of real square arrays `A : α → α → ℝ`
and `B : β → β → ℝ` over finite index types. If `∑ i, A i a * A i a' = if a = a' then 1 else 0` and
`∑ j, B j b * B j b' = if b = b' then 1 else 0`, then
`∑ r : α × β, A r.1 p.1 * B r.2 p.2 * (A r.1 q.1 * B r.2 q.2) = if p = q then 1 else
0`. The proof writes the sum over the product type as the product of the two sums. -/
theorem sum_kronecker_mul_kronecker_eq_ite {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β]
    (A : α → α → ℝ) (B : β → β → ℝ) (hA : ∀ a a', ∑ i, A i a * A i a' = if a = a' then 1 else 0)
    (hB : ∀ b b', ∑ j, B j b * B j b' = if b = b' then 1 else 0) (p q : α × β) :
    ∑ r : α × β, A r.1 p.1 * B r.2 p.2 * (A r.1 q.1 * B r.2 q.2) = if p = q then 1 else 0 := by
  rw [Fintype.sum_prod_type]
  have e : ∑ i, ∑ j, A (i, j).1 p.1 * B (i, j).2 p.2 * (A (i, j).1 q.1 * B (i, j).2 q.2) =
      (∑ i, A i p.1 * A i q.1) * ∑ j, B j p.2 * B j q.2 := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  rw [e, hA, hB]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> simp [h1, h2, Prod.ext_iff]

/-- Let `A` be a real `k × k` matrix and `δ` a real number such that
`|∑ j, (A *ᵥ z) j ^ 2 - ∑ j, z j ^ 2| ≤ δ * ∑ j, z j ^ 2` for every vector `z`. Then
`∑ j, (Aᵀ *ᵥ x) j ^ 2 ≤ (1 + δ) * ∑ j, x j ^ 2` for every `x`. With `w = Aᵀ *ᵥ x`, the proof
combines `∑ j, w j ^ 2 = ∑ j, x j * (A *ᵥ w) j`, the Cauchy-Schwarz inequality and
`∑ j, (A *ᵥ w) j ^ 2 ≤ (1 + δ) * ∑ j, w j ^ 2`. -/
theorem sum_sq_transpose_mulVec_le {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (δ : ℝ)
    (h : ∀ z : Fin k → ℝ, |∑ j, (A *ᵥ z) j ^ 2 - ∑ j, z j ^ 2| ≤ δ * ∑ j, z j ^ 2) (x : Fin k → ℝ) :
    ∑ j, (Aᵀ *ᵥ x) j ^ 2 ≤ (1 + δ) * ∑ j, x j ^ 2 := by
  set w := Aᵀ *ᵥ x with hw
  have hW : 0 ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  have hX : 0 ≤ ∑ j, x j ^ 2 := Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  have hAw : ∑ j, (A *ᵥ w) j ^ 2 ≤ (1 + δ) * ∑ j, w j ^ 2 := by
    have := (abs_le.mp (h w)).2
    linarith
  have hAx : ∑ j, (A *ᵥ x) j ^ 2 ≤ (1 + δ) * ∑ j, x j ^ 2 := by
    have := (abs_le.mp (h x)).2
    linarith
  have hAx0 : 0 ≤ (1 + δ) * ∑ j, x j ^ 2 :=
    le_trans (Finset.sum_nonneg fun j _ ↦ sq_nonneg _) hAx
  have hdot : ∑ j, w j ^ 2 = ∑ j, x j * (A *ᵥ w) j := by
    have e1 : ∑ j, w j ^ 2 = w ⬝ᵥ w := by
      simp only [dotProduct, sq]
    have e2 : ∑ j, x j * (A *ᵥ w) j = x ⬝ᵥ (A *ᵥ w) := rfl
    have e3 : w = x ᵥ* A := by rw [hw, mulVec_transpose]
    rw [e1, e2, dotProduct_mulVec x A w, ← e3]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (A *ᵥ w)
  rw [← hdot] at hcs
  have hsq : (∑ j, w j ^ 2) ^ 2 ≤ (∑ j, w j ^ 2) * ((1 + δ) * ∑ j, x j ^ 2) := by
    calc (∑ j, w j ^ 2) ^ 2 ≤ (∑ j, x j ^ 2) * ∑ j, (A *ᵥ w) j ^ 2 := hcs
      _ ≤ (∑ j, x j ^ 2) * ((1 + δ) * ∑ j, w j ^ 2) := mul_le_mul_of_nonneg_left hAw hX
      _ = (∑ j, w j ^ 2) * ((1 + δ) * ∑ j, x j ^ 2) := by ring
  rcases hW.lt_or_eq with hpos | hzero
  · nlinarith
  · rw [← hzero]; exact hAx0

/-- For real matrices `X : Matrix m n ℝ` and `A : Matrix n n ℝ` and a vector `w : m → ℝ`, the
quadratic form of `A` at `Xᵀ *ᵥ w` is the quadratic form of `X * A * Xᵀ` at `w`:
`(Xᵀ *ᵥ w) ⬝ᵥ (A *ᵥ (Xᵀ *ᵥ w)) = w ⬝ᵥ ((X * A * Xᵀ) *ᵥ w)`. -/
theorem transpose_mulVec_dotProduct_mulVec {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℝ)
    (A : Matrix n n ℝ) (w : m → ℝ) :
    (X.transpose *ᵥ w) ⬝ᵥ (A *ᵥ (X.transpose *ᵥ w)) = w ⬝ᵥ ((X * A * X.transpose) *ᵥ w) := by
  have e : (X * A * X.transpose) *ᵥ w = X *ᵥ (A *ᵥ (w ᵥ* X)) := by
    rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [e, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec w X]

/-- For a positive definite real matrix `G`, the matrix
`S = hG.isHermitian.cfc (fun x ↦ (Real.sqrt x)⁻¹)`, the inverse square root of `G` given by the
functional calculus, satisfies `S * S = G⁻¹`. Proof idea: `S` is symmetric and `S * G * S = 1`, so
`G * (S * S) = 1`. -/
theorem cfc_inv_sqrt_mul_self_eq_inv {n : Type*} [Fintype n] [DecidableEq n] (G : Matrix n n ℝ)
    (hG : G.PosDef) :
    hG.isHermitian.cfc (fun x ↦ (Real.sqrt x)⁻¹) * hG.isHermitian.cfc (fun x ↦ (Real.sqrt x)⁻¹) =
        G⁻¹ := by
  set S := hG.isHermitian.cfc (fun x ↦ (Real.sqrt x)⁻¹) with hS
  have hST : S.transpose = S := by
    rw [hS, ← hG.isHermitian.cfc_eq]
    have h := (cfc_predicate (fun x : ℝ ↦ (Real.sqrt x)⁻¹) G : IsSelfAdjoint _).star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have h1 := posDef_cfc_inv_sqrt_mul_mul_transpose G hG
  rw [← hS, hST, mul_assoc] at h1
  have h2 : G * S * S = 1 := mul_eq_one_comm.1 h1
  rw [mul_assoc] at h2
  exact (Matrix.inv_eq_right_inv h2).symm

/-- For a complex square matrix `A` indexed by `Fin n` and a vector `u`, the conjugate of the
coordinate `(A⁻¹ *ᵥ u) i` is the `i`-th coordinate of `(A.map (starRingEnd ℂ))⁻¹` applied to the
entrywise conjugate of `u`. -/
theorem conj_inv_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (i : Fin n) :
    starRingEnd ℂ ((A⁻¹ *ᵥ u) i) =
      ((A.map (starRingEnd ℂ))⁻¹ *ᵥ fun j ↦ starRingEnd ℂ (u j)) i := by
  rw [← map_conj_inv]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

/-- For a complex square matrix `D`, a vector `u` and a real `t`, the real part of the quadratic
form scales by `t ^ 2`:
`(star ((t : ℂ) • u) ⬝ᵥ (D *ᵥ ((t : ℂ) • u))).re = t ^ 2 * (star u ⬝ᵥ (D *ᵥ u)).re`. -/
theorem re_star_dotProduct_mulVec_ofReal_smul {n : Type*} [Fintype n] (t : ℝ) (D : Matrix n n ℂ)
    (u : n → ℂ) :
    (star ((t : ℂ) • u) ⬝ᵥ (D *ᵥ ((t : ℂ) • u))).re = t ^ 2 * (star u ⬝ᵥ (D *ᵥ u)).re := by
  rw [re_star_ofReal_smul_dotProduct, mulVec_smul, dotProduct_smul, smul_eq_mul,
      Complex.re_ofReal_mul]
  ring

/-- Let `D` be a complex square matrix with `Dᴴ = D` and `0 ≤ (star v ⬝ᵥ (D *ᵥ v)).re` for all `v`,
and let `H` satisfy `D * H = 1`. Then for all vectors `x`, `y`,
`2 * (star y ⬝ᵥ x).re - (star y ⬝ᵥ (D *ᵥ y)).re ≤ (star x ⬝ᵥ (H *ᵥ x)).re`. Proof idea: apply the
nonnegativity to `y - H *ᵥ x` and expand, using `D *ᵥ (H *ᵥ x) = x`. -/
theorem two_mul_re_dotProduct_sub_le_inv {n : Type*} [Fintype n] [DecidableEq n]
    {D H : Matrix n n ℂ} (hDh : Dᴴ = D)
    (hpos : ∀ v : n → ℂ, 0 ≤ (star v ⬝ᵥ (D *ᵥ v)).re) (hDH : D * H = 1) (x y : n → ℂ) :
    2 * (star y ⬝ᵥ x).re - (star y ⬝ᵥ (D *ᵥ y)).re ≤ (star x ⬝ᵥ (H *ᵥ x)).re := by
  set z := H *ᵥ x with hz
  have hDz : D *ᵥ z = x := by rw [hz, mulVec_mulVec, hDH, one_mulVec]
  have h0 := hpos (y - z)
  have hswap : (star z ⬝ᵥ (D *ᵥ y)).re = (star y ⬝ᵥ x).re := by
    rw [← hDh, star_dotProduct_conjTranspose_mulVec, hDz, re_star_dotProduct_comm]
  have hzx : (star z ⬝ᵥ x).re = (star x ⬝ᵥ z).re := re_star_dotProduct_comm z x
  rw [star_sub, mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hDz] at h0
  simp only [Complex.sub_re] at h0
  linarith

/-- If all entries of a complex square matrix `A` indexed by `Fin n` and of a vector `u` are fixed
by complex conjugation, that is, are real, then every coordinate of `A⁻¹ *ᵥ u` has imaginary part
`0`. -/
theorem im_inv_mulVec_eq_zero_of_real {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ)
    (hA : ∀ i j, starRingEnd ℂ (A i j) = A i j) (hu : ∀ i, starRingEnd ℂ (u i) = u i) (i : Fin n) :
    ((A⁻¹ *ᵥ u) i).im = 0 := by
  have h1 : A.map (starRingEnd ℂ) = A := by
    ext i j
    exact hA i j
  have h2 : (fun j ↦ starRingEnd ℂ (u j)) = u := funext hu
  have h := conj_inv_mulVec A u i
  rw [h1, h2] at h
  exact Complex.conj_eq_iff_im.mp h

/-- For a Hermitian complex matrix `G` on a finite index type and a vector `a`, the number
`star a ⬝ᵥ (G *ᵥ a)` is real: it equals its real part, seen in `ℂ`. The number is equal to its
own conjugate. -/
theorem ofReal_re_star_dotProduct_mulVec_self {ι : Type} [Fintype ι] (G : Matrix ι ι ℂ)
    (hG : G.IsHermitian) (a : ι → ℂ) :
    ((star a ⬝ᵥ (G *ᵥ a)).re : ℂ) = star a ⬝ᵥ (G *ᵥ a) := by
  have h := hG.star_dotProduct_mulVec_comm a a
  apply Complex.ext
  · simp
  · have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    simp; linarith

/-- Cauchy-Schwarz inequality for a Hermitian complex matrix `G` with `0 ≤ (star c ⬝ᵥ (G *ᵥ c)).re`
for all `c`: if `0 < (star c ⬝ᵥ (G *ᵥ c)).re`, then
`‖star c ⬝ᵥ (G *ᵥ x)‖ ^ 2 / (star c ⬝ᵥ (G *ᵥ c)).re ≤ (star x ⬝ᵥ (G *ᵥ x)).re`. The proof applies
the nonnegativity to `x - (β / A) • c`, where `β = star c ⬝ᵥ (G *ᵥ x)` and
`A = (star c ⬝ᵥ (G *ᵥ c)).re`. -/
theorem norm_sq_star_dotProduct_mulVec_div_le {ι : Type} [Fintype ι]
    (G : Matrix ι ι ℂ) (hH : G.IsHermitian)
    (hpos : ∀ c : ι → ℂ, 0 ≤ (star c ⬝ᵥ (G *ᵥ c)).re) (x c : ι → ℂ)
    (hc : 0 < (star c ⬝ᵥ (G *ᵥ c)).re) :
    ‖star c ⬝ᵥ (G *ᵥ x)‖ ^ 2 / (star c ⬝ᵥ (G *ᵥ c)).re ≤ (star x ⬝ᵥ (G *ᵥ x)).re := by
  set A := (star c ⬝ᵥ (G *ᵥ c)).re with hA
  set β := star c ⬝ᵥ (G *ᵥ x) with hβ
  set y : ι → ℂ := x - (β / (A : ℂ)) • c with hy
  have hAc : (A : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hxc : star x ⬝ᵥ (G *ᵥ c) = (starRingEnd ℂ) β := star_dotProduct_mulVec_conj_symm G hH x c
  have hcc : star c ⬝ᵥ (G *ᵥ c) = (A : ℂ) := (ofReal_re_star_dotProduct_mulVec_self G hH c).symm
  have key : star y ⬝ᵥ (G *ᵥ y) = star x ⬝ᵥ (G *ᵥ x) - (β * (starRingEnd ℂ) β) / (A : ℂ) := by
    rw [hy]
    simp only [star_sub, star_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
        dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hxc, hcc, ← hβ]
    simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]
    field_simp
    ring
  have h0 := hpos y
  rw [key, Complex.sub_re] at h0
  have hn : ((β * (starRingEnd ℂ) β) / (A : ℂ)).re = ‖β‖ ^ 2 / A := by
    rw [Complex.mul_conj, ← Complex.ofReal_div, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [hn] at h0
  linarith

/-- For a complex square matrix `A` indexed by `Fin n` and a vector `u`, the real part of
`star u ⬝ᵥ (A⁻¹ *ᵥ u)` does not change when `A` and `u` are replaced by their entrywise conjugates.
-/
theorem re_star_dotProduct_inv_mulVec_conj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    (star (fun j ↦ starRingEnd ℂ (u j)) ⬝ᵥ
      ((A.map (starRingEnd ℂ))⁻¹ *ᵥ fun j ↦ starRingEnd ℂ (u j))).re =
      (star u ⬝ᵥ (A⁻¹ *ᵥ u)).re := by
  rw [← Complex.conj_re (star u ⬝ᵥ (A⁻¹ *ᵥ u))]
  congr 1
  simp only [dotProduct, map_sum, map_mul, Pi.star_apply, conj_inv_mulVec]
  simp

/-- Let `G` be a positive definite real matrix that commutes with `Matrix.diagonal τ`, and let
`S = hG.isHermitian.cfc (fun x ↦ (Real.sqrt x)⁻¹)`. Then for every vector `P`,
`∑ a, τ a * (∑ b, S a b * P b) ^ 2 = ∑ a, ∑ b, τ a * G⁻¹ a b * P a * P b`. Proof idea: `S` is
symmetric, commutes with `Matrix.diagonal τ` and satisfies `S * S = G⁻¹`, so
`Sᵀ * Matrix.diagonal τ * S = Matrix.diagonal τ * G⁻¹`; then expand the square and exchange the
sums. -/
theorem sum_mul_sq_cfc_inv_sqrt_eq {n : Type*} [Fintype n] [DecidableEq n] (G : Matrix n n ℝ)
    (hG : G.PosDef)
    (τ : n → ℝ) (hcomm : G * Matrix.diagonal τ = Matrix.diagonal τ * G) (P : n → ℝ) :
    ∑ a, τ a * (∑ b, hG.isHermitian.cfc (fun x ↦ (Real.sqrt x)⁻¹) a b * P b) ^ 2 =
      ∑ a, ∑ b, τ a * G⁻¹ a b * P a * P b := by
  set S := hG.isHermitian.cfc (fun x ↦ (Real.sqrt x)⁻¹) with hS
  have hSD : S * Matrix.diagonal τ = Matrix.diagonal τ * S := by
    have hc : Commute G (Matrix.diagonal τ) := hcomm
    have h := hc.cfc_real (fun x ↦ (Real.sqrt x)⁻¹)
    rw [hG.isHermitian.cfc_eq] at h
    exact h
  have hST : S.transpose = S := by
    rw [hS, ← hG.isHermitian.cfc_eq]
    have h := (cfc_predicate (fun x : ℝ ↦ (Real.sqrt x)⁻¹) G : IsSelfAdjoint _).star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hmat : S.transpose * Matrix.diagonal τ * S = Matrix.diagonal τ * G⁻¹ := by
    rw [hST, hSD, mul_assoc, hS, cfc_inv_sqrt_mul_self_eq_inv G hG]
  have key : ∀ b c, ∑ a, S a b * τ a * S a c = τ b * G⁻¹ b c := by
    intro b c
    have h := congrFun (congrFun hmat b) c
    rw [Matrix.mul_apply, Matrix.diagonal_mul] at h
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply] at h
    exact h
  calc ∑ a, τ a * (∑ b, S a b * P b) ^ 2
      = ∑ a, ∑ b, ∑ c, S a b * τ a * S a c * P b * P c := by
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ ↦ ?_
        ring
    _ = ∑ b, ∑ c, (∑ a, S a b * τ a * S a c) * P b * P c := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ ↦ ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ ↦ ?_
        rw [Finset.sum_mul, Finset.sum_mul]
    _ = ∑ a, ∑ b, τ a * G⁻¹ a b * P a * P b := by
        refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
        rw [key b c]

/-- Let `hn : n' = n`, and let `B` and `v` be the entrywise conjugates of a complex matrix `A` and a
vector `u` indexed by `Fin n`, reindexed along `Fin.cast hn`:
`B i j = starRingEnd ℂ (A (Fin.cast hn i) (Fin.cast hn j))` and
`v i = starRingEnd ℂ (u (Fin.cast hn i))`. Then
`(star v ⬝ᵥ (B⁻¹ *ᵥ v)).re = (star u ⬝ᵥ (A⁻¹ *ᵥ u)).re`. -/
theorem re_star_dotProduct_inv_mulVec_conj_cast {n n' : ℕ} (hn : n' = n)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n') (Fin n') ℂ) (u : Fin n → ℂ) (v : Fin n' → ℂ)
    (hB : ∀ i j, B i j = starRingEnd ℂ (A (Fin.cast hn i) (Fin.cast hn j)))
    (hv : ∀ i, v i = starRingEnd ℂ (u (Fin.cast hn i))) :
    (star v ⬝ᵥ (B⁻¹ *ᵥ v)).re = (star u ⬝ᵥ (A⁻¹ *ᵥ u)).re := by
  subst hn
  have e1 : B = A.map (starRingEnd ℂ) := by
    ext i j
    simpa using hB i j
  have e2 : v = fun j ↦ starRingEnd ℂ (u j) := by
    funext i
    simpa using hv i
  rw [e1, e2, re_star_dotProduct_inv_mulVec_conj]

/-- Let `G` be a Hermitian complex matrix with `0 < (star c ⬝ᵥ (G *ᵥ c)).re` for all `c ≠ 0` and
with `IsUnit G.det`. For every vector `b`, the supremum of
`‖star c ⬝ᵥ b‖ ^ 2 / (star c ⬝ᵥ (G *ᵥ c)).re` over all `c` with `0 < (star c ⬝ᵥ (G *ᵥ c)).re` equals
`(star b ⬝ᵥ (G⁻¹ *ᵥ b)).re`. The value is attained at `c = G⁻¹ *ᵥ b` when this vector is nonzero,
and the Cauchy-Schwarz inequality for the form gives the upper bound. -/
theorem sSup_norm_sq_dotProduct_div_eq_inv {ι : Type} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ)
    (hH : G.IsHermitian)
    (hpos : ∀ c : ι → ℂ, c ≠ 0 → 0 < (star c ⬝ᵥ (G *ᵥ c)).re) (hG : IsUnit G.det) (b : ι → ℂ) :
    sSup {t : ℝ | ∃ c : ι → ℂ, 0 < (star c ⬝ᵥ (G *ᵥ c)).re ∧
        t = ‖star c ⬝ᵥ b‖ ^ 2 / (star c ⬝ᵥ (G *ᵥ c)).re} = (star b ⬝ᵥ (G⁻¹ *ᵥ b)).re := by
  have hnn : ∀ c : ι → ℂ, 0 ≤ (star c ⬝ᵥ (G *ᵥ c)).re := by
    intro c
    by_cases h : c = 0
    · subst h; simp
    · exact (hpos c h).le
  set x := G⁻¹ *ᵥ b with hx
  have hGx : G *ᵥ x = b := by
    rw [hx, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hG, Matrix.one_mulVec]
  have hval : (star b ⬝ᵥ (G⁻¹ *ᵥ b)).re = (star x ⬝ᵥ (G *ᵥ x)).re := by
    rw [hGx, ← hx]
    have := star_dotProduct_mulVec_conj_symm G hH x x
    rw [hGx] at this
    have h3 : star b ⬝ᵥ x = (starRingEnd ℂ) (star x ⬝ᵥ b) := by
      simp only [dotProduct, map_sum, map_mul, Pi.star_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp [mul_comm]
    rw [h3, Complex.conj_re]
  rw [hval]
  by_cases hb : x = 0
  · have h0 : (star x ⬝ᵥ (G *ᵥ x)).re = 0 := by rw [hb]; simp
    rw [h0]
    have hb0 : b = 0 := by rw [← hGx, hb, Matrix.mulVec_zero]
    apply le_antisymm
    · apply Real.sSup_nonpos
      rintro t ⟨c, hc, rfl⟩
      rw [hb0]; simp
    · apply Real.sSup_nonneg
      rintro t ⟨c, hc, rfl⟩
      exact div_nonneg (sq_nonneg _) hc.le
  · have hxpos := hpos x hb
    apply IsGreatest.csSup_eq
    refine ⟨⟨x, hxpos, ?_⟩, ?_⟩
    · rw [← hGx]
      have hr := ofReal_re_star_dotProduct_mulVec_self G hH x
      have hn : ‖star x ⬝ᵥ (G *ᵥ x)‖ = (star x ⬝ᵥ (G *ᵥ x)).re := by
        conv_lhs => rw [← hr]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
      rw [hn]
      field_simp
    · rintro t ⟨c, hc, rfl⟩
      rw [← hGx]
      exact norm_sq_star_dotProduct_mulVec_div_le G hH hnn x c hc

/-- For a positive definite complex matrix `G` on a finite index type and a vector `a ≠ 0`, the real
part of `star a ⬝ᵥ (G *ᵥ a)` is positive. This is Mathlib's `Matrix.PosDef.re_dotProduct_pos` over
`ℂ`. -/
theorem re_star_dotProduct_mulVec_pos_of_posDef {ι : Type} [Fintype ι] {G : Matrix ι ι ℂ}
    (hG : G.PosDef) {a : ι → ℂ}
    (ha : a ≠ 0) :
    0 < (star a ⬝ᵥ (G *ᵥ a)).re := hG.re_dotProduct_pos ha

/-- Cauchy-Schwarz for a positive definite complex matrix `G` on a finite index type: for all
vectors `c` and `z`,
`‖star c ⬝ᵥ (G *ᵥ z)‖ ^ 2 ≤ (star c ⬝ᵥ (G *ᵥ c)).re * (star z ⬝ᵥ (G *ᵥ z)).re`. For `z ≠ 0`
it follows from `0 ≤ (star v ⬝ᵥ (G *ᵥ v)).re` at `v = c - l • z` for a suitable `l` in `ℂ`. -/
theorem norm_sq_star_dotProduct_mulVec_le {ι : Type} [Fintype ι] {G : Matrix ι ι ℂ} (hG : G.PosDef)
    (c z : ι → ℂ) :
    ‖star c ⬝ᵥ (G *ᵥ z)‖ ^ 2 ≤ (star c ⬝ᵥ (G *ᵥ c)).re * (star z ⬝ᵥ (G *ᵥ z)).re := by
  by_cases hz : z = 0
  · subst hz; simp
  have hs := re_star_dotProduct_mulVec_pos_of_posDef hG hz
  set s := (star z ⬝ᵥ (G *ᵥ z)).re with hs_def
  set β := star c ⬝ᵥ (G *ᵥ z) with hβ
  set l : ℂ := (starRingEnd ℂ) β / (s : ℂ) with hl
  have hpsd : 0 ≤ (star (c - l • z) ⬝ᵥ (G *ᵥ (c - l • z))).re := by
    by_cases h0 : c - l • z = 0
    · rw [h0]; simp
    · exact (re_star_dotProduct_mulVec_pos_of_posDef hG h0).le
  have hzc : star z ⬝ᵥ (G *ᵥ c) = (starRingEnd ℂ) β := by
    rw [hβ, ← Complex.star_def, hG.isHermitian.star_dotProduct_mulVec_comm]
  have hzz : star z ⬝ᵥ (G *ᵥ z) = (s : ℂ) :=
    (ofReal_re_star_dotProduct_mulVec_self G hG.isHermitian z).symm
  have hexp : star (c - l • z) ⬝ᵥ (G *ᵥ (c - l • z)) =
      star c ⬝ᵥ (G *ᵥ c) - l * β - (starRingEnd ℂ) l * (starRingEnd ℂ) β
        + (starRingEnd ℂ) l * l * (s : ℂ) := by
    rw [mulVec_sub, mulVec_smul, star_sub, star_smul, dotProduct_sub, sub_dotProduct,
        sub_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_dotProduct, dotProduct_smul, hzc, hzz, ← hβ]
    simp only [smul_eq_mul, Complex.star_def]
    ring
  rw [hexp] at hpsd
  have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have key : l * β = ((‖β‖ ^ 2 / s : ℝ) : ℂ) := by
    rw [hl, div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast
    ring
  have key2 : (starRingEnd ℂ) l * (starRingEnd ℂ) β = ((‖β‖ ^ 2 / s : ℝ) : ℂ) := by
    rw [← map_mul, key, Complex.conj_ofReal]
  have key3 : (starRingEnd ℂ) l * l * (s : ℂ) = ((‖β‖ ^ 2 / s : ℝ) : ℂ) := by
    rw [mul_comm ((starRingEnd ℂ) l) l, mul_assoc, hl]
    rw [map_div₀, Complex.conj_conj, Complex.conj_ofReal]
    field_simp
    rw [mul_comm _ β, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; field_simp
  rw [key, key2, key3] at hpsd
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at hpsd
  have : ‖β‖ ^ 2 / s ≤ (star c ⬝ᵥ (G *ᵥ c)).re := by linarith
  rw [div_le_iff₀ hs] at this
  linarith

/-- For a positive definite complex matrix `G` on a finite index type and a vector `x`, the
supremum of `‖star c ⬝ᵥ x‖ ^ 2 / (star c ⬝ᵥ (G *ᵥ c)).re` over the vectors `c` with
`0 < (star c ⬝ᵥ (G *ᵥ c)).re` equals `(star x ⬝ᵥ (G⁻¹ *ᵥ x)).re`. With `z = G⁻¹ *ᵥ x`,
Cauchy-Schwarz for `G` gives the upper bound, and `c = z` attains it when `z ≠ 0`. -/
theorem sSup_norm_sq_dotProduct_div_of_posDef {ι : Type} [Fintype ι] [DecidableEq ι]
    {G : Matrix ι ι ℂ} (hG : G.PosDef)
    (x : ι → ℂ) :
    sSup {t : ℝ | ∃ c : ι → ℂ, 0 < (star c ⬝ᵥ (G *ᵥ c)).re ∧
      t = ‖star c ⬝ᵥ x‖ ^ 2 / (star c ⬝ᵥ (G *ᵥ c)).re} = (star x ⬝ᵥ (G⁻¹ *ᵥ x)).re := by
  have hU : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit
  set z := G⁻¹ *ᵥ x with hz
  have hGz : G *ᵥ z = x := by rw [hz, mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]
  have hR : star x ⬝ᵥ (G⁻¹ *ᵥ x) = star z ⬝ᵥ (G *ᵥ z) := by
    rw [← hz]
    conv_lhs => rw [← hGz]
    rw [star_mulVec, hG.isHermitian.eq, ← dotProduct_mulVec]
  rw [hR]
  have hub : ∀ t ∈ {t : ℝ | ∃ c : ι → ℂ, 0 < (star c ⬝ᵥ (G *ᵥ c)).re ∧
      t = ‖star c ⬝ᵥ x‖ ^ 2 / (star c ⬝ᵥ (G *ᵥ c)).re}, t ≤ (star z ⬝ᵥ (G *ᵥ z)).re := by
    rintro t ⟨c, hc, rfl⟩
    rw [div_le_iff₀ hc, ← hGz, mul_comm]
    exact norm_sq_star_dotProduct_mulVec_le hG c z
  by_cases h0 : z = 0
  · have hz0 : (star z ⬝ᵥ (G *ᵥ z)).re = 0 := by rw [h0]; simp
    rw [hz0]
    apply le_antisymm
    · exact Real.sSup_nonpos (fun t ht ↦ hz0 ▸ hub t ht)
    · apply Real.sSup_nonneg
      rintro t ⟨c, hc, rfl⟩
      positivity
  · have hpos := re_star_dotProduct_mulVec_pos_of_posDef hG h0
    apply IsGreatest.csSup_eq
    refine ⟨⟨z, hpos, ?_⟩, hub⟩
    rw [← hGz, ← ofReal_re_star_dotProduct_mulVec_self G hG.isHermitian z, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    simp only [Complex.ofReal_re]
    field_simp

end PDE.Analysis
