/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import CAS.ExactTactic

/-!
# Matrix damping with local exceptions

An essentially bounded measurable matrix acts on an L² field with an integrable quadratic
form. Pointwise damping can therefore be integrated. On an exceptional region, replacing
the damping bound `-Λ` by an upper bound `λ` costs at most `max (Λ + λ) 0` times the
mass of the field there.

The regions may overlap, since summing the nonnegative losses still gives an upper bound.
The matrix need not be symmetric.

For a weighted field `ξᵢ = √Φᵢ vᵢ`, local bounds on `Φᵢ` and `|vᵢ|` give the
concentration coefficients bounding each local weighted square integral. The last theorem
substitutes these measured local masses into the matrix estimate. All bounds hold almost
everywhere, and the weights may vanish.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.MatrixEnergy

open MeasureTheory Filter
open scoped Matrix ENNReal

variable {X ι κ : Type*} [MeasurableSpace X] [Fintype ι] [Fintype κ]
  {μ : Measure X}

/-- Bounded measurable matrix entries and L² components make the quadratic form integrable.
Each summand is a bounded coefficient times a product of two L² functions. -/
theorem integrable_quadForm_of_memLp
    {M : X → Matrix ι ι ℝ} {ξ : X → ι → ℝ} {K : Matrix ι ι ℝ}
    (hξ : ∀ i, MemLp (fun x ↦ ξ x i) 2 μ)
    (hM : ∀ i j, AEStronglyMeasurable (fun x ↦ M x i j) μ)
    (hK : ∀ i j, ∀ᵐ x ∂μ, ‖M x i j‖ ≤ K i j) :
    Integrable (fun x ↦ ξ x ⬝ᵥ (M x *ᵥ ξ x)) μ := by
  classical
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine integrable_finsetSum Finset.univ fun i _ ↦
    integrable_finsetSum Finset.univ fun j _ ↦ ?_
  have hprod : Integrable (fun x ↦ ξ x i * ξ x j) μ :=
    (hξ i).integrable_mul (hξ j)
  exact (hprod.bdd_mul (hM i j) (hK i j)).congr
    (Eventually.of_forall fun x ↦ mul_left_comm (M x i j) (ξ x i) (ξ x j))

/-- Integrate damping away from finitely many measurable exception regions. The correction
uses their L² masses, with signed local bounds allowed. Overlap only increases the
correction, so disjointness and finiteness of the region measures are unnecessary here. -/
theorem integral_quadForm_le_of_local_bounds
    {M : X → Matrix ι ι ℝ} {ξ : X → ι → ℝ} {K : Matrix ι ι ℝ}
    {B : κ → Set X} {Λ : ℝ} {lambda : κ → ℝ}
    (hξ : ∀ i, MemLp (fun x ↦ ξ x i) 2 μ)
    (hM : ∀ i j, AEStronglyMeasurable (fun x ↦ M x i j) μ)
    (hK : ∀ i j, ∀ᵐ x ∂μ, ‖M x i j‖ ≤ K i j)
    (hB : ∀ ℓ, MeasurableSet (B ℓ))
    (hgood : ∀ᵐ x ∂μ, (∀ ℓ, x ∉ B ℓ) →
      ∀ z : ι → ℝ, z ⬝ᵥ (M x *ᵥ z) ≤ -Λ * ∑ i, z i ^ 2)
    (hbad : ∀ ℓ, ∀ᵐ x ∂μ, x ∈ B ℓ →
      ∀ z : ι → ℝ, z ⬝ᵥ (M x *ᵥ z) ≤ lambda ℓ * ∑ i, z i ^ 2) :
    ∫ x, ξ x ⬝ᵥ (M x *ᵥ ξ x) ∂μ ≤
      -Λ * (∫ x, ∑ i, ξ x i ^ 2 ∂μ) +
        ∑ ℓ, max (Λ + lambda ℓ) 0 * ∫ x in B ℓ, ∑ i, ξ x i ^ 2 ∂μ := by
  classical
  let ρ : X → ℝ := fun x ↦ ∑ i, ξ x i ^ 2
  let γ : κ → ℝ := fun ℓ ↦ max (Λ + lambda ℓ) 0
  have hρ : Integrable ρ μ :=
    integrable_finsetSum Finset.univ fun i _ ↦ (hξ i).integrable_sq
  have hρ0 (x : X) : 0 ≤ ρ x := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hγ (ℓ : κ) : 0 ≤ γ ℓ := le_max_right _ _
  have hterm (ℓ : κ) :
      Integrable (fun x ↦ γ ℓ * (B ℓ).indicator ρ x) μ :=
    (hρ.indicator (hB ℓ)).const_mul _
  have hsum : Integrable (fun x ↦ ∑ ℓ, γ ℓ * (B ℓ).indicator ρ x) μ :=
    integrable_finsetSum Finset.univ fun ℓ _ ↦ hterm ℓ
  have hpoint : ∀ᵐ x ∂μ, ξ x ⬝ᵥ (M x *ᵥ ξ x) ≤
      -Λ * ρ x + ∑ ℓ, γ ℓ * (B ℓ).indicator ρ x := by
    filter_upwards [hgood, ae_all_iff.2 hbad] with x hg hb
    have hnonneg (ℓ : κ) : 0 ≤ γ ℓ * (B ℓ).indicator ρ x := by
      by_cases hx : x ∈ B ℓ
      · simpa only [Set.indicator_of_mem hx] using mul_nonneg (hγ ℓ) (hρ0 x)
      · simp only [Set.indicator_of_notMem hx, mul_zero, le_refl]
    by_cases hx : ∃ ℓ, x ∈ B ℓ
    · obtain ⟨ℓ, hxℓ⟩ := hx
      have hsingle : γ ℓ * ρ x ≤ ∑ j, γ j * (B j).indicator ρ x := by
        simpa only [Set.indicator_of_mem hxℓ] using
          (Finset.single_le_sum (fun j _ ↦ hnonneg j) (Finset.mem_univ ℓ))
      have hloss : (Λ + lambda ℓ) * ρ x ≤ γ ℓ * ρ x :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (hρ0 x)
      have hb' : ξ x ⬝ᵥ (M x *ᵥ ξ x) ≤ lambda ℓ * ρ x := hb ℓ hxℓ (ξ x)
      nlinarith
    · exact (hg (fun ℓ hxℓ ↦ hx ⟨ℓ, hxℓ⟩) (ξ x)).trans
        (le_add_of_nonneg_right (Finset.sum_nonneg fun ℓ _ ↦ hnonneg ℓ))
  calc
    ∫ x, ξ x ⬝ᵥ (M x *ᵥ ξ x) ∂μ ≤
        ∫ x, -Λ * ρ x + ∑ ℓ, γ ℓ * (B ℓ).indicator ρ x ∂μ :=
      integral_mono_ae (integrable_quadForm_of_memLp hξ hM hK)
        ((hρ.const_mul _).add hsum) hpoint
    _ = -Λ * (∫ x, ρ x ∂μ) + ∑ ℓ, γ ℓ * ∫ x in B ℓ, ρ x ∂μ := by
      rw [integral_add (hρ.const_mul _) hsum, integral_const_mul,
        integral_finsetSum Finset.univ (fun ℓ _ ↦ hterm ℓ)]
      congr 1
      apply Finset.sum_congr rfl
      intro ℓ _
      rw [integral_const_mul, integral_indicator (hB ℓ)]

/-- Squaring the weighted field recovers the energy density wherever the weights are
nonnegative. Almost-everywhere nonnegativity suffices for both integrals. -/
private theorem sqrt_weighted_sq_ae
    {Φ v : X → ι → ℝ} (hΦ : ∀ i, ∀ᵐ x ∂μ, 0 ≤ Φ x i) :
    (fun x ↦ ∑ i, (√(Φ x i) * v x i) ^ 2) =ᵐ[μ]
      (fun x ↦ ∑ i, Φ x i * v x i ^ 2) := by
  filter_upwards [ae_all_iff.2 hΦ] with x hx
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, Real.sq_sqrt (hx i)]

/-- A finite region and the bounds `Φᵢ ≤ Sᵢ`, `|vᵢ| ≤ Pᵢ⁰ E₀ + Pᵢᵏ Hₖ` give a
weighted mass estimate. The factor `2` comes from separating the two squares.
Only the weighted components need to be in L², and only on this region. -/
theorem setIntegral_weighted_sq_le_of_pointwise
    {B : Set X} {Φ v : X → ι → ℝ} {S P0 Pk : ι → ℝ} {E0 Hk : ℝ}
    (hfinite : μ B ≠ ∞)
    (hξ : ∀ i, MemLp (fun x ↦ √(Φ x i) * v x i) 2 (μ.restrict B))
    (hΦ : ∀ i, ∀ᵐ x ∂μ.restrict B, 0 ≤ Φ x i)
    (hS : ∀ i, ∀ᵐ x ∂μ.restrict B, Φ x i ≤ S i)
    (hv : ∀ i, ∀ᵐ x ∂μ.restrict B, |v x i| ≤ P0 i * E0 + Pk i * Hk) :
    ∫ x in B, ∑ i, Φ x i * v x i ^ 2 ∂μ ≤
      (2 * μ.real B * ∑ i, S i * P0 i ^ 2) * E0 ^ 2 +
        (2 * μ.real B * ∑ i, S i * Pk i ^ 2) * Hk ^ 2 := by
  classical
  let C : ℝ := ∑ i, (2 * S i * P0 i ^ 2 * E0 ^ 2 + 2 * S i * Pk i ^ 2 * Hk ^ 2)
  have hint : IntegrableOn (fun x ↦ ∑ i, Φ x i * v x i ^ 2) B μ :=
    (integrable_finsetSum Finset.univ fun i _ ↦ (hξ i).integrable_sq).congr
      (sqrt_weighted_sq_ae hΦ)
  have hC : IntegrableOn (fun _ : X ↦ C) B μ := integrableOn_const hfinite
  have hpoint : ∀ᵐ x ∂μ.restrict B, ∑ i, Φ x i * v x i ^ 2 ≤ C := by
    filter_upwards [ae_all_iff.2 hΦ, ae_all_iff.2 hS, ae_all_iff.2 hv] with x hφ hs hvx
    apply Finset.sum_le_sum
    intro i _
    have hS0 : 0 ≤ S i := (hφ i).trans (hs i)
    have hv2 : v x i ^ 2 ≤ (P0 i * E0 + Pk i * Hk) ^ 2 := by
      calc
        v x i ^ 2 = |v x i| ^ 2 := (sq_abs _).symm
        _ ≤ (P0 i * E0 + Pk i * Hk) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (hvx i) 2
    calc
      Φ x i * v x i ^ 2 ≤ S i * v x i ^ 2 :=
        mul_le_mul_of_nonneg_right (hs i) (sq_nonneg _)
      _ ≤ S i * (P0 i * E0 + Pk i * Hk) ^ 2 :=
        mul_le_mul_of_nonneg_left hv2 hS0
      _ ≤ S i * (2 * ((P0 i * E0) ^ 2 + (Pk i * Hk) ^ 2)) :=
        mul_le_mul_of_nonneg_left add_sq_le hS0
      _ = 2 * S i * P0 i ^ 2 * E0 ^ 2 + 2 * S i * Pk i ^ 2 * Hk ^ 2 := by cas
  have hCeq : C = (2 * E0 ^ 2) * (∑ i, S i * P0 i ^ 2) +
      (2 * Hk ^ 2) * (∑ i, S i * Pk i ^ 2) := by
    dsimp only [C]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cas
  calc
    ∫ x in B, ∑ i, Φ x i * v x i ^ 2 ∂μ ≤ ∫ _ : X in B, C ∂μ :=
      integral_mono_ae hint hC hpoint
    _ = (2 * μ.real B * ∑ i, S i * P0 i ^ 2) * E0 ^ 2 +
        (2 * μ.real B * ∑ i, S i * Pk i ^ 2) * Hk ^ 2 := by
      rw [setIntegral_const, smul_eq_mul, hCeq]
      cas

/-- Weighted matrix damping follows from a.e. matrix bounds and local pointwise bounds
on the field. Each exceptional region costs its measured concentration coefficient times
`max (Λ + λℓ) 0`. The coefficient of `E₀²` is therefore the original damping minus these
losses. A positive remainder is the surviving low-order damping margin.

The energy identity identifies `E₀²` with the weighted integral. The matrix entries
are measurable and essentially bounded, so the quadratic integral is integrable. No
bound on that integral or on the exceptional-region masses is assumed. -/
theorem weighted_matrix_damping_of_pointwise
    {M : X → Matrix ι ι ℝ} {K : Matrix ι ι ℝ}
    {Φ v : X → ι → ℝ} {B : κ → Set X} {S P0 Pk : κ → ι → ℝ}
    {Λ E0 Hk : ℝ} {lambda : κ → ℝ}
    (hξ : ∀ i, MemLp (fun x ↦ √(Φ x i) * v x i) 2 μ)
    (hΦ : ∀ i, ∀ᵐ x ∂μ, 0 ≤ Φ x i)
    (hM : ∀ i j, AEStronglyMeasurable (fun x ↦ M x i j) μ)
    (hK : ∀ i j, ∀ᵐ x ∂μ, ‖M x i j‖ ≤ K i j)
    (hB : ∀ ℓ, MeasurableSet (B ℓ))
    (hfinite : ∀ ℓ, μ (B ℓ) ≠ ∞)
    (hS : ∀ ℓ i, ∀ᵐ x ∂μ.restrict (B ℓ), Φ x i ≤ S ℓ i)
    (hv : ∀ ℓ i, ∀ᵐ x ∂μ.restrict (B ℓ),
      |v x i| ≤ P0 ℓ i * E0 + Pk ℓ i * Hk)
    (henergy : (∫ x, ∑ i, Φ x i * v x i ^ 2 ∂μ) = E0 ^ 2)
    (hgood : ∀ᵐ x ∂μ, (∀ ℓ, x ∉ B ℓ) →
      ∀ z : ι → ℝ, z ⬝ᵥ (M x *ᵥ z) ≤ -Λ * ∑ i, z i ^ 2)
    (hbad : ∀ ℓ, ∀ᵐ x ∂μ, x ∈ B ℓ →
      ∀ z : ι → ℝ, z ⬝ᵥ (M x *ᵥ z) ≤ lambda ℓ * ∑ i, z i ^ 2) :
    ∫ x, (fun i ↦ √(Φ x i) * v x i) ⬝ᵥ
      (M x *ᵥ fun i ↦ √(Φ x i) * v x i) ∂μ ≤
        -(Λ - ∑ ℓ, max (Λ + lambda ℓ) 0 *
          (2 * μ.real (B ℓ) * ∑ i, S ℓ i * P0 ℓ i ^ 2)) * E0 ^ 2 +
        (∑ ℓ, max (Λ + lambda ℓ) 0 *
          (2 * μ.real (B ℓ) * ∑ i, S ℓ i * Pk ℓ i ^ 2)) * Hk ^ 2 := by
  classical
  let ξ : X → ι → ℝ := fun x i ↦ √(Φ x i) * v x i
  let ρ : X → ℝ := fun x ↦ ∑ i, ξ x i ^ 2
  let γ : κ → ℝ := fun ℓ ↦ max (Λ + lambda ℓ) 0
  let m0 : κ → ℝ := fun ℓ ↦ 2 * μ.real (B ℓ) * ∑ i, S ℓ i * P0 ℓ i ^ 2
  let mk : κ → ℝ := fun ℓ ↦ 2 * μ.real (B ℓ) * ∑ i, S ℓ i * Pk ℓ i ^ 2
  have heq : ρ =ᵐ[μ] (fun x ↦ ∑ i, Φ x i * v x i ^ 2) :=
    sqrt_weighted_sq_ae hΦ
  have hρenergy : (∫ x, ρ x ∂μ) = E0 ^ 2 := (integral_congr_ae heq).trans henergy
  have hconc (ℓ : κ) :
      ∫ x in B ℓ, ρ x ∂μ ≤ m0 ℓ * E0 ^ 2 + mk ℓ * Hk ^ 2 := by
    rw [integral_congr_ae (heq.restrict (s := B ℓ))]
    exact setIntegral_weighted_sq_le_of_pointwise (hfinite ℓ)
      (fun i ↦ (hξ i).restrict (B ℓ)) (fun i ↦ ae_restrict_of_ae (hΦ i))
      (hS ℓ) (hv ℓ)
  have hmatrix := integral_quadForm_le_of_local_bounds hξ hM hK hB hgood hbad
  change (∫ x, ξ x ⬝ᵥ (M x *ᵥ ξ x) ∂μ) ≤
    -(Λ - ∑ ℓ, γ ℓ * m0 ℓ) * E0 ^ 2 + (∑ ℓ, γ ℓ * mk ℓ) * Hk ^ 2
  calc
    ∫ x, ξ x ⬝ᵥ (M x *ᵥ ξ x) ∂μ ≤
        -Λ * (∫ x, ρ x ∂μ) + ∑ ℓ, γ ℓ * ∫ x in B ℓ, ρ x ∂μ := hmatrix
    _ ≤ -Λ * E0 ^ 2 + ∑ ℓ, γ ℓ * (m0 ℓ * E0 ^ 2 + mk ℓ * Hk ^ 2) := by
      rw [hρenergy]
      exact add_le_add le_rfl (Finset.sum_le_sum fun ℓ _ ↦
        mul_le_mul_of_nonneg_left (hconc ℓ) (le_max_right _ _))
    _ = -(Λ - ∑ ℓ, γ ℓ * m0 ℓ) * E0 ^ 2 + (∑ ℓ, γ ℓ * mk ℓ) * Hk ^ 2 := by
      simp only [mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.sum_mul]
      cas

end PDE.Analysis.MatrixEnergy
