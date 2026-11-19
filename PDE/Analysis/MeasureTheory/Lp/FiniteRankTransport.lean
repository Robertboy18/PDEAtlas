/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Products
public import PDE.Analysis.Operator.FiniteRankNonlinear

/-!
# Finite-rank transport in the mass norm

An essentially bounded derivative matrix acts on vector `L²` fields. The action
has norm at most the full matrix norm, and at most `M` when the matrix has pointwise
operator norm at most `M` almost everywhere.
The resulting `L²` pairing agrees with the `L⁴` convection pairing whenever
the representatives agree almost everywhere. This transfers the Gram and
finite basis interaction estimate to the nonlinear load of the stationary
Navier–Stokes correction, without a Sobolev embedding constant in its mass bound.
The load is the one bounded in (4.28) of Hou, Wang and Yang.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 4.3, (4.28).
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory Matrix
open scoped BigOperators ENNReal RealInnerProductSpace

namespace ContinuousLinearMap

variable {α ι κ : Type*} [MeasurableSpace α] {μ : Measure α}
  [Fintype ι] [Fintype κ]

/-- Algebraic bounded-matrix action on finite tuples of `L²` fields. -/
def l2MatrixTransportLinear (D : PiLp 2 (fun _ : κ × ι ↦ Lp ℝ ∞ μ)) :
    PiLp 2 (fun _ : ι ↦ Lp ℝ 2 μ) →ₗ[ℝ] PiLp 2 (fun _ : κ ↦ Lp ℝ 2 μ) where
  toFun A := WithLp.toLp 2 (fun k ↦ ∑ i, D (k, i) • A i)
  map_add' A B := by
    apply PiLp.ext
    intro k
    change (∑ i, D (k, i) • (A i + B i)) =
      (∑ i, D (k, i) • A i) + ∑ i, D (k, i) • B i
    simp only [Lp.add_smul, Finset.sum_add_distrib]
  map_smul' r A := by
    apply PiLp.ext
    intro k
    change (∑ i, D (k, i) • (r • A i)) = r • ∑ i, D (k, i) • A i
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (Lp.smul_comm _ _ _).symm

/-- The algebraic matrix action has a bound in the finite Hilbert norms. -/
theorem norm_l2MatrixTransportLinear_le
    (D : PiLp 2 (fun _ : κ × ι ↦ Lp ℝ ∞ μ))
    (A : PiLp 2 (fun _ : ι ↦ Lp ℝ 2 μ)) :
    ‖l2MatrixTransportLinear D A‖ ≤ ‖D‖ * ‖A‖ := by
  have hcoord (k : κ) : ‖(l2MatrixTransportLinear D A) k‖ ≤
      ∑ i, ‖D (k, i)‖ * ‖A i‖ := by
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ Lp.norm_smul_le _ _)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ k, (∑ i, ‖D (k, i)‖ * ‖A i‖) ^ 2 := by
      exact Finset.sum_le_sum fun k _ ↦
        (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ ↦
          mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (hcoord k)
    _ ≤ ∑ k, (∑ i, ‖D (k, i)‖ ^ 2) * (∑ i, ‖A i‖ ^ 2) :=
      Finset.sum_le_sum fun k _ ↦
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    _ = (‖D‖ * ‖A‖) ^ 2 := by
      rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
        Fintype.sum_prod_type, Finset.sum_mul]

/-- An essentially bounded derivative matrix transports an `L²` vector field.
Both vector and matrix products carry their finite Hilbert norms. -/
def l2MatrixTransport (D : PiLp 2 (fun _ : κ × ι ↦ Lp ℝ ∞ μ)) :
    PiLp 2 (fun _ : ι ↦ Lp ℝ 2 μ) →L[ℝ] PiLp 2 (fun _ : κ ↦ Lp ℝ 2 μ) :=
  (l2MatrixTransportLinear D).mkContinuous ‖D‖ (norm_l2MatrixTransportLinear_le D)

/-- Coordinate formula for bounded-matrix transport. -/
theorem l2MatrixTransport_apply
    (D : PiLp 2 (fun _ : κ × ι ↦ Lp ℝ ∞ μ))
    (A : PiLp 2 (fun _ : ι ↦ Lp ℝ 2 μ)) (k : κ) :
    l2MatrixTransport D A k = ∑ i, D (k, i) • A i := rfl

/-- The full matrix norm controls the `L²` transport operator with constant one. -/
theorem norm_l2MatrixTransport_le (D : PiLp 2 (fun _ : κ × ι ↦ Lp ℝ ∞ μ)) :
    ‖l2MatrixTransport D‖ ≤ ‖D‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) (norm_l2MatrixTransportLinear_le D)

/-- A pointwise operator-norm bound controls the `L²` transport operator. If at almost every
point the matrix `(D (k, i) x)` has Euclidean operator norm at most `M`, the transport has norm
at most `M`. This is sharper than `norm_l2MatrixTransport_le`, whose bound is the `ℓ²` norm of
the essential suprema of the entries. -/
theorem norm_l2MatrixTransport_le_of_ae_sum_sq_le
    (D : PiLp 2 (fun _ : κ × ι ↦ Lp ℝ ∞ μ)) {M : ℝ} (hM : 0 ≤ M)
    (hD : ∀ᵐ x ∂μ, ∀ v : ι → ℝ,
      ∑ k, (∑ i, D (k, i) x * v i) ^ 2 ≤ M ^ 2 * ∑ i, v i ^ 2) :
    ‖l2MatrixTransport D‖ ≤ M := by
  refine opNorm_le_bound _ hM fun A ↦ ?_
  have hprod (k : κ) (i : ι) :
      ((D (k, i) • A i : Lp ℝ 2 μ) : α → ℝ) =ᵐ[μ] fun x ↦ D (k, i) x * A i x := by
    filter_upwards [Lp.coeFn_lpSMul (r := 2) (D (k, i)) (A i)] with x hx
    simpa using hx
  have hpair (k : κ) (i j : ι) :
      ⟪D (k, i) • A i, D (k, j) • A j⟫ =
        ∫ x, D (k, i) x * A i x * (D (k, j) x * A j x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hprod k i, hprod k j] with x hi hj
    simp only [hi, hj, RCLike.inner_apply, conj_trivial]
    ring
  have hint (k : κ) (i j : ι) :
      Integrable (fun x ↦ D (k, i) x * A i x * (D (k, j) x * A j x)) μ := by
    refine (L2.integrable_inner (𝕜 := ℝ) (D (k, i) • A i) (D (k, j) • A j)).congr ?_
    filter_upwards [hprod k i, hprod k j] with x hi hj
    simp only [hi, hj, RCLike.inner_apply, conj_trivial]
    ring
  have hsq_int (k : κ) : Integrable (fun x ↦ (∑ i, D (k, i) x * A i x) ^ 2) μ := by
    simp_rw [sq, Finset.sum_mul_sum]
    exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint k i j
  have hT : ‖l2MatrixTransport D A‖ ^ 2 = ∫ x, ∑ k, (∑ i, D (k, i) x * A i x) ^ 2 ∂μ := by
    rw [PiLp.norm_sq_eq_of_L2, integral_finsetSum _ fun k _ ↦ hsq_int k]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← real_inner_self_eq_norm_sq, l2MatrixTransport_apply, sum_inner]
    simp_rw [inner_sum, hpair, sq, Finset.sum_mul_sum]
    rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint k i j]
    exact Finset.sum_congr rfl fun i _ ↦ (integral_finsetSum _ fun j _ ↦ hint k i j).symm
  have hA : ‖A‖ ^ 2 = ∫ x, ∑ i, A i x ^ 2 ∂μ := by
    rw [PiLp.norm_sq_eq_of_L2, integral_finsetSum _ fun i _ ↦ (Lp.memLp (A i)).integrable_sq]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
      simp only [RCLike.inner_apply, conj_trivial, sq])
  have hle : ‖l2MatrixTransport D A‖ ^ 2 ≤ (M * ‖A‖) ^ 2 := by
    rw [hT, mul_pow, hA, ← integral_const_mul]
    refine integral_mono_ae (integrable_finsetSum _ fun k _ ↦ hsq_int k)
      ((integrable_finsetSum _ fun i _ ↦ (Lp.memLp (A i)).integrable_sq).const_mul _) ?_
    filter_upwards [hD] with x hx using hx fun i ↦ A i x
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hle

/-- The `L⁴` convection pairing agrees with bounded-matrix transport in `L²`
when the coefficient, derivative, and test representatives agree. -/
theorem transportPairing_eq_inner_l2MatrixTransport
    (A₄ : PiLp 2 (fun _ : ι ↦ Lp ℝ 4 μ))
    (D₂ : PiLp 2 (fun _ : κ × ι ↦ Lp ℝ 2 μ))
    (V₄ : PiLp 2 (fun _ : κ ↦ Lp ℝ 4 μ))
    (A₂ : PiLp 2 (fun _ : ι ↦ Lp ℝ 2 μ))
    (Dtop : PiLp 2 (fun _ : κ × ι ↦ Lp ℝ ∞ μ))
    (V₂ : PiLp 2 (fun _ : κ ↦ Lp ℝ 2 μ))
    (hA : ∀ i, (A₄ i : α → ℝ) =ᵐ[μ] A₂ i)
    (hD : ∀ ki, (D₂ ki : α → ℝ) =ᵐ[μ] Dtop ki)
    (hV : ∀ k, (V₄ k : α → ℝ) =ᵐ[μ] V₂ k) :
    transportPairing A₄ D₂ V₄ = ⟪l2MatrixTransport Dtop A₂, V₂⟫ := by
  rw [transportPairing_eq_integral, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [l2MatrixTransport_apply, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hA i, hD (k, i), hV k, Lp.coeFn_lpSMul (r := 2) (Dtop (k, i))
    (A₂ i)] with x ha hd hv hm
  simp only [RCLike.inner_apply, conj_trivial, hm, smul_eq_mul, Pi.mul_apply, ha, hd, hv]
  ring

/-- A finite-rank derivative reconstruction has a sharp mass bound from its
Gram matrix, operator norms, and pairwise basis interactions. The first `L⁴`
field represents the unknown plus its reconstructed correction. -/
theorem abs_transportPairing_finiteRank_le {J : Type*} [Fintype J]
    (q φ : J → PiLp 2 (fun _ : ι ↦ Lp ℝ 2 μ))
    (D₂ : J → PiLp 2 (fun _ : κ × ι ↦ Lp ℝ 2 μ))
    (Dtop : J → PiLp 2 (fun _ : κ × ι ↦ Lp ℝ ∞ μ))
    (u : PiLp 2 (fun _ : ι ↦ Lp ℝ 2 μ))
    (v : PiLp 2 (fun _ : κ ↦ Lp ℝ 2 μ))
    (A₄ : PiLp 2 (fun _ : ι ↦ Lp ℝ 4 μ))
    (V₄ : PiLp 2 (fun _ : κ ↦ Lp ℝ 4 μ))
    (hA : ∀ i, (A₄ i : α → ℝ) =ᵐ[μ] (u + ∑ j, ⟪q j, u⟫ • φ j) i)
    (hD : ∀ j ki, (D₂ j ki : α → ℝ) =ᵐ[μ] Dtop j ki)
    (hV : ∀ k, (V₄ k : α → ℝ) =ᵐ[μ] v k)
    {g A B : ℝ} (hg : 0 ≤ g) (hAn : 0 ≤ A) (hBn : 0 ≤ B)
    (hgram : ∀ c : J → ℝ,
      c ⬝ᵥ (Matrix.gram ℝ q) *ᵥ c ≤ g * ∑ j, c j ^ 2)
    (hoperator : ∑ j, ‖l2MatrixTransport (Dtop j)‖ ^ 2 ≤ A ^ 2)
    (hinteraction : ∑ i, ∑ j, ‖l2MatrixTransport (Dtop j) (φ i)‖ ^ 2 ≤ B ^ 2) :
    |transportPairing A₄ (∑ j, ⟪q j, u⟫ • D₂ j) V₄| ≤
      (Real.sqrt g * A + g * B) * ‖u‖ ^ 2 * ‖v‖ := by
  have hpair : transportPairing A₄ (∑ j, ⟪q j, u⟫ • D₂ j) V₄ =
      ⟪∑ j, ⟪q j, u⟫ • l2MatrixTransport (Dtop j)
        (u + ∑ i, ⟪q i, u⟫ • φ i), v⟫ := by
    simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
      sum_inner, real_inner_smul_left]
    apply Finset.sum_congr rfl
    intro j _
    rw [transportPairing_eq_inner_l2MatrixTransport A₄ (D₂ j) V₄
      (u + ∑ i, ⟪q i, u⟫ • φ i) (Dtop j) v hA (hD j) hV]
  rw [hpair]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right
      (PDE.Analysis.norm_finiteRank_remainder_le_of_gram_le q φ
        (fun j ↦ l2MatrixTransport (Dtop j)) u hg hAn hBn hgram hoperator hinteraction)
      (norm_nonneg _))

/-- Componentwise essentially bounded matrix certificates give the operator
budget in the finite-rank mass estimate, with no coordinate-count factor. -/
theorem abs_transportPairing_finiteRank_le_of_matrix_bounds {J : Type*} [Fintype J]
    (q φ : J → PiLp 2 (fun _ : ι ↦ Lp ℝ 2 μ))
    (D₂ : J → PiLp 2 (fun _ : κ × ι ↦ Lp ℝ 2 μ))
    (Dtop : J → PiLp 2 (fun _ : κ × ι ↦ Lp ℝ ∞ μ))
    (u : PiLp 2 (fun _ : ι ↦ Lp ℝ 2 μ))
    (v : PiLp 2 (fun _ : κ ↦ Lp ℝ 2 μ))
    (A₄ : PiLp 2 (fun _ : ι ↦ Lp ℝ 4 μ))
    (V₄ : PiLp 2 (fun _ : κ ↦ Lp ℝ 4 μ))
    (hA : ∀ i, (A₄ i : α → ℝ) =ᵐ[μ] (u + ∑ j, ⟪q j, u⟫ • φ j) i)
    (hD : ∀ j ki, (D₂ j ki : α → ℝ) =ᵐ[μ] Dtop j ki)
    (hV : ∀ k, (V₄ k : α → ℝ) =ᵐ[μ] v k)
    {g A B : ℝ} (hg : 0 ≤ g) (hAn : 0 ≤ A) (hBn : 0 ≤ B)
    (hgram : ∀ c : J → ℝ,
      c ⬝ᵥ (Matrix.gram ℝ q) *ᵥ c ≤ g * ∑ j, c j ^ 2)
    (hmatrix : ∑ j, ‖Dtop j‖ ^ 2 ≤ A ^ 2)
    (hinteraction : ∑ i, ∑ j, ‖l2MatrixTransport (Dtop j) (φ i)‖ ^ 2 ≤ B ^ 2) :
    |transportPairing A₄ (∑ j, ⟪q j, u⟫ • D₂ j) V₄| ≤
      (Real.sqrt g * A + g * B) * ‖u‖ ^ 2 * ‖v‖ := by
  apply abs_transportPairing_finiteRank_le q φ D₂ Dtop u v A₄ V₄ hA hD hV
    hg hAn hBn hgram _ hinteraction
  exact (Finset.sum_le_sum fun j _ ↦
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (norm_l2MatrixTransport_le (Dtop j))).trans hmatrix

end ContinuousLinearMap
