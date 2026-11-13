/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.FiniteRankDeterminant
public import CAS.Analysis.Matrix.QuadraticFormBounds
import Mathlib.Tactic.Positivity.Finset

/-!
# Gram certificates for the hypotheses of the finite-rank determinant criterion

The residual and amplification hypotheses of `exists_kernel_of_det_neg` concern the
coordinate map `ℓ = coordinateMap F` of functionals `F i` and the reconstruction
`Φ = reconstruction φ` of fields `φ j`: `‖L Φ ℓ h - ℓ† ℓ h‖ ≤ δ ‖h‖` and
`‖h + Φ ℓ h‖ ≤ t_G ‖h‖`. Both are norms of finite combinations `∑ j, (F j h) • y j`, with
`y j = φ j` for the amplification and `y j = L φ j - F j` for the residual. We bound
them by finite matrix computations.

The functionals are represented in a Hilbert space `H`: `F i x = ⟪q i, ι x⟫` for a bounded
map `ι` with `‖ι x‖² ≤ K ‖x‖²`; for the self-similar linearization `H` is `L²` and `ι` the
inclusion of the energy space, with `K = 1 / c`. If `A` bounds the Gram matrix of `q` from
above and `B` bounds the quadratic form `v ↦ ‖∑ j, v j • y j‖²` from above, then
`g B - B A B ⪰ 0` with `g ≥ 0` gives `‖∑ j, (F j h) • y j‖² ≤ g K ‖h‖²`
(`norm_sum_smul_sq_le_of_sandwich`): with `s = aᵀ B a` for the coordinates `a`, Cauchy–Schwarz
applied to `w = B a` gives `s² ≤ (aᵀ B A B a) K ‖h‖² ≤ g s K ‖h‖²`. The constant `g` is
`λ_max(A^{1/2} B A^{1/2})` at best, and the certificate needs neither square roots nor
inverses. Upper bounds `A` and `B` follow from entrywise enclosures of the Gram matrices
(`norm_sum_smul_sq_le_of_inner_sub_le`), and the dual norm of represented functionals is at
most `√K` times the norm of their representers (`norm_sum_smul_sq_le_of_represented`).
`norm_add_reconstruction_le_of_sandwich` and
`norm_reconstruction_sub_coordTranspose_le_of_sandwich` state the two hypotheses of the
criterion in its own notation.
-/

@[expose] public noncomputable section

open Finset
open scoped Matrix RealInnerProductSpace

namespace PDE.Analysis.Operator

variable {m : ℕ}

section Sandwich

variable {Y : Type*} [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The quadratic form of `B` at `B a` against `A` is the quadratic form of `B A B` at `a`, for
symmetric `B`. -/
theorem quadForm_mulVec_eq_quadForm_mul {A B : Matrix (Fin m) (Fin m) ℝ} (hB : B.IsSymm)
    (a : Fin m → ℝ) :
    ∑ i, ∑ j, A i j * (B *ᵥ a) i * (B *ᵥ a) j = ∑ i, ∑ j, (B * A * B) i j * a i * a j := by
  rw [CAS.Analysis.Matrix.sum_sum_mul_mul_eq_dotProduct_mulVec,
    CAS.Analysis.Matrix.sum_sum_mul_mul_eq_dotProduct_mulVec]
  have hBt : Bᵀ = B := hB
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec a B,
    ← Matrix.mulVec_transpose, hBt]

/-- **Sandwich bound.** Let `B` be a symmetric upper bound of the quadratic form
`v ↦ ‖∑ j, v j • y j‖²` and let the coordinates `a` satisfy `(∑ i, w i a i)² ≤ (wᵀ A w) K` for
every `w`. If `g ≥ 0`, `K ≥ 0` and `g B - B A B ⪰ 0`, then `‖∑ j, a j • y j‖² ≤ g K`. -/
theorem norm_sum_smul_sq_le_of_sandwich (y : Fin m → Y) (a : Fin m → ℝ)
    {A B : Matrix (Fin m) (Fin m) ℝ} {g K : ℝ} (hg : 0 ≤ g) (hK : 0 ≤ K) (hB : B.IsSymm)
    (hy : ∀ v : Fin m → ℝ, ‖∑ j, v j • y j‖ ^ 2 ≤ ∑ i, ∑ j, B i j * v i * v j)
    (ha : ∀ w : Fin m → ℝ, (∑ i, w i * a i) ^ 2 ≤ (∑ i, ∑ j, A i j * w i * w j) * K)
    (hcert : ∀ v : Fin m → ℝ, 0 ≤ ∑ i, ∑ j, (g * B i j - (B * A * B) i j) * v i * v j) :
    ‖∑ j, a j • y j‖ ^ 2 ≤ g * K := by
  set s := ∑ i, ∑ j, B i j * a i * a j with hs
  have hs0 : 0 ≤ s := (sq_nonneg _).trans (hy a)
  have hwa : ∑ i, (B *ᵥ a) i * a i = s := by
    simp only [hs, Matrix.mulVec, dotProduct, sum_mul]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
  have h1 := ha (B *ᵥ a)
  rw [hwa, quadForm_mulVec_eq_quadForm_mul hB a] at h1
  have h2 := hcert a
  have hsplit : ∑ i, ∑ j, (g * B i j - (B * A * B) i j) * a i * a j =
      g * s - ∑ i, ∑ j, (B * A * B) i j * a i * a j := by
    simp only [hs, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
  rw [hsplit] at h2
  have h3 : s ^ 2 ≤ g * s * K := by
    calc s ^ 2 ≤ (∑ i, ∑ j, (B * A * B) i j * a i * a j) * K := h1
      _ ≤ g * s * K := mul_le_mul_of_nonneg_right (by linarith) hK
  have hsK : s ≤ g * K := by
    rcases hs0.eq_or_lt with h | h
    · rw [← h]
      positivity
    · nlinarith
  exact (hy a).trans hsK

end Sandwich

section Represented

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H]

/-- An entrywise enclosure of the Gram matrix of `y` by `G` within `ε` gives the upper bound
`G + m ε I` of the quadratic form `v ↦ ‖∑ j, v j • y j‖²`. -/
theorem norm_sum_smul_sq_le_of_inner_sub_le (y : Fin m → H) {G : Matrix (Fin m) (Fin m) ℝ}
    {ε : ℝ} (hG : ∀ i j, |⟪y i, y j⟫ - G i j| ≤ ε) (v : Fin m → ℝ) :
    ‖∑ j, v j • y j‖ ^ 2 ≤
      ∑ i, ∑ j, (G i j + if i = j then (m : ℝ) * ε else 0) * v i * v j := by
  have hnorm : ‖∑ j, v j • y j‖ ^ 2 = ∑ i, ∑ j, ⟪y i, y j⟫ * v i * v j := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [inner_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  have h := CAS.Analysis.Matrix.abs_quadForm_le_of_abs_le hG v
  have hsplit : ∑ i, ∑ j, (G i j + if i = j then (m : ℝ) * ε else 0) * v i * v j =
      ∑ i, ∑ j, G i j * v i * v j + (m : ℝ) * ε * ∑ i, v i ^ 2 := by
    simp only [add_mul, sum_add_distrib, ite_mul, zero_mul, sum_ite_eq, mem_univ, ite_true,
      mul_sum]
    congr 1
    exact sum_congr rfl fun i _ ↦ by ring
  have hdiff : ∑ i, ∑ j, (⟪y i, y j⟫ - G i j) * v i * v j =
      ∑ i, ∑ j, ⟪y i, y j⟫ * v i * v j - ∑ i, ∑ j, G i j * v i * v j := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ ↦ by rw [← sum_sub_distrib]; exact sum_congr rfl fun j _ ↦ by ring
  rw [hnorm, hsplit]
  rw [hdiff, Fintype.card_fin] at h
  linarith [(abs_le.mp h).2]

/-- Functionals `x ↦ ⟪q i, ι x⟫` with `‖ι x‖² ≤ K ‖x‖²`: an upper bound `A` of the Gram matrix of
`q` bounds `(∑ i, w i F i x)²` by `(wᵀ A w) K ‖x‖²`. -/
theorem sq_sum_mul_apply_le_of_represented (ι : E →L[ℝ] H) {K : ℝ}
    (hι : ∀ x, ‖ι x‖ ^ 2 ≤ K * ‖x‖ ^ 2) (F : Fin m → StrongDual ℝ E) (q : Fin m → H)
    (hF : ∀ i x, F i x = ⟪q i, ι x⟫) {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : ∀ w : Fin m → ℝ, ‖∑ i, w i • q i‖ ^ 2 ≤ ∑ i, ∑ j, A i j * w i * w j)
    (w : Fin m → ℝ) (x : E) :
    (∑ i, w i * F i x) ^ 2 ≤ (∑ i, ∑ j, A i j * w i * w j) * (K * ‖x‖ ^ 2) := by
  have hsum : ∑ i, w i * F i x = ⟪∑ i, w i • q i, ι x⟫ := by
    rw [sum_inner]
    exact sum_congr rfl fun i _ ↦ by rw [hF, real_inner_smul_left]
  rw [hsum]
  calc ⟪∑ i, w i • q i, ι x⟫ ^ 2 ≤ (‖∑ i, w i • q i‖ * ‖ι x‖) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
    _ = ‖∑ i, w i • q i‖ ^ 2 * ‖ι x‖ ^ 2 := by ring
    _ ≤ (∑ i, ∑ j, A i j * w i * w j) * (K * ‖x‖ ^ 2) :=
        mul_le_mul (hA w) (hι x) (sq_nonneg _) ((sq_nonneg _).trans (hA w))

/-- Functionals represented as `x ↦ ⟪R j, ι x⟫` with `‖ι x‖² ≤ K ‖x‖²`: the dual norm of a
combination is at most `√K` times the norm of the combination of the representers. -/
theorem norm_sum_smul_sq_le_of_represented (ι : E →L[ℝ] H) {K : ℝ} (hK : 0 ≤ K)
    (hι : ∀ x, ‖ι x‖ ^ 2 ≤ K * ‖x‖ ^ 2) (r : Fin m → StrongDual ℝ E) (R : Fin m → H)
    (hr : ∀ j x, r j x = ⟪R j, ι x⟫) (v : Fin m → ℝ) :
    ‖∑ j, v j • r j‖ ^ 2 ≤ K * ‖∑ j, v j • R j‖ ^ 2 := by
  have hbound : ‖∑ j, v j • r j‖ ≤ √K * ‖∑ j, v j • R j‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ ?_
    have happ : (∑ j, v j • r j) x = ⟪∑ j, v j • R j, ι x⟫ := by
      rw [_root_.sum_apply, sum_inner]
      exact sum_congr rfl fun j _ ↦ by
        rw [smul_apply, hr, smul_eq_mul, real_inner_smul_left]
    have hιx : ‖ι x‖ ≤ √K * ‖x‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (ι x)), ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul hK]
      exact Real.sqrt_le_sqrt (hι x)
    rw [happ, Real.norm_eq_abs]
    calc |⟪∑ j, v j • R j, ι x⟫| ≤ ‖∑ j, v j • R j‖ * ‖ι x‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖∑ j, v j • R j‖ * (√K * ‖x‖) := mul_le_mul_of_nonneg_left hιx (norm_nonneg _)
      _ = √K * ‖∑ j, v j • R j‖ * ‖x‖ := by ring
  calc ‖∑ j, v j • r j‖ ^ 2 ≤ (√K * ‖∑ j, v j • R j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = K * ‖∑ j, v j • R j‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt hK]

end Represented

section Criterion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Amplification bound.** With the hypotheses of `norm_sum_smul_sq_le_of_sandwich` for the
fields `φ` and the coordinates `F j h`, uniformly in `h` with `K ‖h‖²` in place of `K`,
`‖h + Φ ℓ h‖ ≤ t_G ‖h‖` for `1 + √(g K) ≤ t_G`. -/
theorem norm_add_reconstruction_le_of_sandwich (F : Fin m → StrongDual ℝ E) (φ : Fin m → E)
    {A B : Matrix (Fin m) (Fin m) ℝ} {g K tG : ℝ} (hg : 0 ≤ g) (hK : 0 ≤ K) (hB : B.IsSymm)
    (hφ : ∀ v : Fin m → ℝ, ‖∑ j, v j • φ j‖ ^ 2 ≤ ∑ i, ∑ j, B i j * v i * v j)
    (hF : ∀ (w : Fin m → ℝ) (h : E),
      (∑ i, w i * F i h) ^ 2 ≤ (∑ i, ∑ j, A i j * w i * w j) * (K * ‖h‖ ^ 2))
    (hcert : ∀ v : Fin m → ℝ, 0 ≤ ∑ i, ∑ j, (g * B i j - (B * A * B) i j) * v i * v j)
    (htG : 1 + √(g * K) ≤ tG) (h : E) :
    ‖h + reconstruction φ (coordinateMap F h)‖ ≤ tG * ‖h‖ := by
  have hsq := norm_sum_smul_sq_le_of_sandwich φ (fun j ↦ F j h) hg
    (mul_nonneg hK (sq_nonneg ‖h‖)) hB hφ (hF · h) hcert
  have hΦ : reconstruction φ (coordinateMap F h) = ∑ j, F j h • φ j := by
    rw [reconstruction_apply]
    rfl
  have hnorm : ‖∑ j, F j h • φ j‖ ≤ √(g * K) * ‖h‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (∑ j, F j h • φ j)), ← Real.sqrt_sq (norm_nonneg h),
      ← Real.sqrt_mul (mul_nonneg hg hK)]
    exact Real.sqrt_le_sqrt (by linarith)
  rw [hΦ]
  calc ‖h + ∑ j, F j h • φ j‖ ≤ ‖h‖ + ‖∑ j, F j h • φ j‖ := norm_add_le _ _
    _ ≤ ‖h‖ + √(g * K) * ‖h‖ := by linarith
    _ = (1 + √(g * K)) * ‖h‖ := by ring
    _ ≤ tG * ‖h‖ := mul_le_mul_of_nonneg_right htG (norm_nonneg h)

/-- **Residual bound.** For fields `φ j ∈ D` with residual functionals `r j = L φ j - F j` and a
symmetric upper bound `B` of `v ↦ ‖∑ j, v j • r j‖²` in the dual norm, the sandwich
certificate gives `‖L Φ ℓ h - ℓ† ℓ h‖ ≤ δ ‖h‖` for `√(g K) ≤ δ`. -/
theorem norm_reconstruction_sub_coordTranspose_le_of_sandwich (D : Submodule ℝ E)
    (L : D →ₗ[ℝ] StrongDual ℝ E) (F : Fin m → StrongDual ℝ E) (φ : Fin m → E)
    (hφ : ∀ j, φ j ∈ D) (r : Fin m → StrongDual ℝ E) (hr : ∀ j, r j = L ⟨φ j, hφ j⟩ - F j)
    {A B : Matrix (Fin m) (Fin m) ℝ} {g K δ : ℝ} (hg : 0 ≤ g) (hK : 0 ≤ K) (hB : B.IsSymm)
    (hrB : ∀ v : Fin m → ℝ, ‖∑ j, v j • r j‖ ^ 2 ≤ ∑ i, ∑ j, B i j * v i * v j)
    (hF : ∀ (w : Fin m → ℝ) (h : E),
      (∑ i, w i * F i h) ^ 2 ≤ (∑ i, ∑ j, A i j * w i * w j) * (K * ‖h‖ ^ 2))
    (hcert : ∀ v : Fin m → ℝ, 0 ≤ ∑ i, ∑ j, (g * B i j - (B * A * B) i j) * v i * v j)
    (hδ : √(g * K) ≤ δ) (h : E) :
    ‖L ⟨reconstruction φ (coordinateMap F h), reconstruction_mem hφ _⟩ -
        coordTranspose (coordinateMap F) (coordinateMap F h)‖ ≤ δ * ‖h‖ := by
  have hsq := norm_sum_smul_sq_le_of_sandwich r (fun j ↦ F j h) hg
    (mul_nonneg hK (sq_nonneg ‖h‖)) hB hrB (hF · h) hcert
  have hsum : (⟨reconstruction φ (coordinateMap F h), reconstruction_mem hφ _⟩ : D) =
      ∑ j, F j h • (⟨φ j, hφ j⟩ : D) := by
    ext
    simp only [reconstruction_apply, Submodule.coe_sum, Submodule.coe_smul]
    rfl
  have heq : L ⟨reconstruction φ (coordinateMap F h), reconstruction_mem hφ _⟩ -
      coordTranspose (coordinateMap F) (coordinateMap F h) = ∑ j, F j h • r j := by
    rw [hsum, map_sum]
    ext x
    simp only [sub_apply, _root_.sum_apply, map_smul,
      smul_apply, coordTranspose_coordinateMap_apply, hr, smul_eq_mul,
      coordinateMap_apply]
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun j _ ↦ by ring
  rw [heq]
  have hnorm : ‖∑ j, F j h • r j‖ ≤ √(g * K) * ‖h‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (∑ j, F j h • r j)), ← Real.sqrt_sq (norm_nonneg h),
      ← Real.sqrt_mul (mul_nonneg hg hK)]
    exact Real.sqrt_le_sqrt (by linarith)
  exact hnorm.trans (mul_le_mul_of_nonneg_right hδ (norm_nonneg h))

end Criterion

end PDE.Analysis.Operator
