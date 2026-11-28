/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.FDeriv.PartialDeriv.HigherNormSq.Composition
public import PDE.Analysis.Analytic.PowerSeries.ConvolutionWeight
import PDE.Analysis.Scalar.ElementaryBounds

/-!
# Derivative norms of a finite family, and compositions with weighted bounds

## Motivation

For a finite family `v = (v_l)` of functions with derivative bounds of the form
`|Dʲv| ≤ j! c ψ(j) βʲ`, how large are the derivatives of `g ∘ v` when the derivatives of `g` grow
like `m! C Kᵐ`?

## The idea

`familyNorm k v x` is the `ℓ²` norm over `l` of the coordinate norms of order `k` of the
components `v_l`. It dominates the coordinate norm of `v` as a map into `I → ℝ` with the sup
norm. The chain rule `iteratedCoordinateNorm_comp_le` bounds `|Dʳ(g ∘ v)|/r!` by
`∑ₘ C Kᵐ [tʳ] pᵐ`, where `p` has the coefficients `|Dʲv|/j!`. The weight `ψ` is closed under
convolution, so `[tʳ] pᵐ ≤ cᵐ βʳ ψ(r)` and the sum over `m ≥ 2` is a geometric series in `c K`.
The term `m = 1` is `C K |Dʳv|` and is kept as it is: in the regularity argument it is the term
of top order, which is not yet bounded.

## Main results

* `iteratedCoordinateNormSq_le_familyNormSq`: the coordinate square norm of `v` is at most its
  family square norm, for all `v` that are `C^k` at the point.
* `iteratedCoordinateNorm_comp_le_of_convolutionWeight`: for all `1 ≤ r ≤ N + 1`, all `g` that
  are `C^r` at `v x` with `‖Dᵐg(v x)‖ ≤ m! C Kᵐ` for `m ≤ r`, all `v` that are `C^r` at `x` with
  `|Dʲv(x)| ≤ j! c ψ(j) βʲ` for `1 ≤ j ≤ N`, and all constants `C, K, c, β ≥ 0` with `c K ≤ 1/2`:
  `|Dʳ(g ∘ v)(x)| ≤ C K |Dʳv(x)| + r! ψ(r) βʳ · 2 C (c K)²`.

## Relations

The second result is `PDE.iteratedCoordinateNorm_comp_le` with
`PDE.Analysis.coeff_pow_le_convolutionWeight`. It is used in
`PDE.Elliptic.Regularity.Analytic.Structure`.

## What stays open

The constants are not optimized.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology
open PowerSeries (coeff)
open PDE.Analysis

namespace PDE.Elliptic.Regularity.Analytic

variable {n : ℕ} {I : Type*} [Fintype I]

/-- The square norm of order `k` of a finite family of real functions: the sum over the family
of the coordinate square norms of its members. -/
def familyNormSq (k : ℕ) (v : ℝ^n → I → ℝ) (x : ℝ^n) : ℝ :=
  ∑ l, iteratedCoordinateNormSq k (fun y ↦ v y l) x

/-- The family square norm is nonnegative. -/
theorem familyNormSq_nonneg (k : ℕ) (v : ℝ^n → I → ℝ) (x : ℝ^n) : 0 ≤ familyNormSq k v x :=
  Finset.sum_nonneg fun _ _ ↦ iteratedCoordinateNormSq_nonneg k _ x

/-- The norm of order `k` of a finite family of real functions: the square root of
`familyNormSq k v x`. -/
def familyNorm (k : ℕ) (v : ℝ^n → I → ℝ) (x : ℝ^n) : ℝ := √(familyNormSq k v x)

/-- The family norm is nonnegative. -/
theorem familyNorm_nonneg (k : ℕ) (v : ℝ^n → I → ℝ) (x : ℝ^n) : 0 ≤ familyNorm k v x :=
  Real.sqrt_nonneg _

/-- The square of the family norm is the family square norm. -/
theorem familyNorm_sq (k : ℕ) (v : ℝ^n → I → ℝ) (x : ℝ^n) :
    familyNorm k v x ^ 2 = familyNormSq k v x :=
  Real.sq_sqrt (familyNormSq_nonneg k v x)

/-- The family norm as the `ℓ²` norm of the coordinate norms of the members. -/
theorem familyNorm_eq_sqrt_sum (k : ℕ) (v : ℝ^n → I → ℝ) (x : ℝ^n) :
    familyNorm k v x = √(∑ l, iteratedCoordinateNorm k (fun y ↦ v y l) x ^ 2) := by
  simp only [familyNorm, familyNormSq, iteratedCoordinateNorm_sq]

/-- Each member of the family has coordinate norm at most the family norm. -/
theorem iteratedCoordinateNorm_apply_le_familyNorm (k : ℕ) (v : ℝ^n → I → ℝ) (x : ℝ^n)
    (l : I) : iteratedCoordinateNorm k (fun y ↦ v y l) x ≤ familyNorm k v x :=
  Real.sqrt_le_sqrt <| Finset.single_le_sum
    (f := fun l ↦ iteratedCoordinateNormSq k (fun y ↦ v y l) x)
    (fun _ _ ↦ iteratedCoordinateNormSq_nonneg k _ x) (Finset.mem_univ l)

/-- The Cauchy–Schwarz inequality over the family, for two orders of differentiation. -/
theorem sum_iteratedCoordinateNorm_mul_le (k k' : ℕ) (v : ℝ^n → I → ℝ) (x : ℝ^n) :
    ∑ l, iteratedCoordinateNorm k (fun y ↦ v y l) x *
        iteratedCoordinateNorm k' (fun y ↦ v y l) x ≤
      familyNorm k v x * familyNorm k' v x := by
  rw [familyNorm_eq_sqrt_sum, familyNorm_eq_sqrt_sum]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- The coordinate square norm of a family, as a map into `I → ℝ` with the sup norm, is at most
its family square norm, for all families that are `C^k` at the point. -/
theorem iteratedCoordinateNormSq_le_familyNormSq (k : ℕ) {v : ℝ^n → I → ℝ} {x : ℝ^n}
    (hv : ContDiffAt ℝ k v x) : iteratedCoordinateNormSq k v x ≤ familyNormSq k v x := by
  induction k generalizing v with
  | zero =>
    simp only [familyNormSq, iteratedCoordinateNormSq]
    have hsum : 0 ≤ ∑ l, ‖v x l‖ ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have hle : ‖v x‖ ≤ √(∑ l, ‖v x l‖ ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun l ↦ ?_
      refine Real.le_sqrt_of_sq_le ?_
      exact Finset.single_le_sum (f := fun l ↦ ‖v x l‖ ^ 2) (fun _ _ ↦ sq_nonneg _)
        (Finset.mem_univ l)
    calc ‖v x‖ ^ 2 ≤ √(∑ l, ‖v x l‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = ∑ l, ‖v x l‖ ^ 2 := Real.sq_sqrt hsum
  | succ k ih =>
    have hk : (1 : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast Nat.le_add_left 1 k
    -- near `x` the components of `∂ᵢ v` are the derivatives of the components
    have hcomp (i : Fin n) (l : I) :
        (fun y ↦ (∂[i] v) y l) =ᶠ[𝓝 x] ∂[i] (fun y ↦ v y l) := by
      filter_upwards [hv.eventually_differentiableAt hk] with y hy
      simp only [partialDeriv, fderiv_apply hy l, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply]
    calc iteratedCoordinateNormSq (k + 1) v x
        = ∑ i, iteratedCoordinateNormSq k (∂[i] v) x := rfl
      _ ≤ ∑ i, familyNormSq k (∂[i] v) x :=
          Finset.sum_le_sum fun i _ ↦ ih (hv.partialDeriv i le_rfl)
      _ = ∑ i, ∑ l, iteratedCoordinateNormSq k (∂[i] (fun y ↦ v y l)) x :=
          Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun l _ ↦
            (hcomp i l).iteratedCoordinateNormSq k
      _ = familyNormSq (k + 1) v x := Finset.sum_comm

/-- The coordinate norm of a family, as a map into `I → ℝ` with the sup norm, is at most its
family norm, for all families that are `C^k` at the point. -/
theorem iteratedCoordinateNorm_le_familyNorm (k : ℕ) {v : ℝ^n → I → ℝ} {x : ℝ^n}
    (hv : ContDiffAt ℝ k v x) : iteratedCoordinateNorm k v x ≤ familyNorm k v x :=
  Real.sqrt_le_sqrt (iteratedCoordinateNormSq_le_familyNormSq k hv)

/-- **Derivatives of a composition under weighted bounds.** Let `1 ≤ r ≤ N + 1`, let `g` be
`C^r` at `v x` with `‖Dᵐg(v x)‖ ≤ m! C Kᵐ` for all `m ≤ r`, let the family `v` be `C^r` at `x` with
`|Dʲv(x)| ≤ j! c ψ(j) βʲ` for `1 ≤ j ≤ N` with the convolution weight `ψ`, and let
`C, K, c, β ≥ 0` with `c K ≤ 1/2`. Then
`|Dʳ(g ∘ v)(x)| ≤ C K |Dʳv(x)| + r! ψ(r) βʳ · 2 C (c K)²`.
The first term is the part of the chain rule that is linear in `Dʳv`; it needs no bound on
`Dʳv`, so the statement also holds one order above the known bounds. -/
theorem iteratedCoordinateNorm_comp_le_of_convolutionWeight {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {g : (I → ℝ) → G} {v : ℝ^n → I → ℝ} {x : ℝ^n} {C K c β : ℝ} {N r : ℕ}
    (hg : ContDiffAt ℝ r g (v x)) (hv : ContDiffAt ℝ r v x)
    (hgb : ∀ m, m ≤ r → ‖iteratedFDeriv ℝ m g (v x)‖ ≤ m.factorial * C * K ^ m)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hc : 0 ≤ c) (hβ : 0 ≤ β) (hcK : c * K ≤ 1 / 2)
    (hvb : ∀ j, 1 ≤ j → j ≤ N →
      familyNorm j v x ≤ j.factorial * c * convolutionWeight j * β ^ j)
    (hr1 : 1 ≤ r) (hrN : r ≤ N + 1) :
    iteratedCoordinateNorm r (g ∘ v) x ≤
      C * K * familyNorm r v x +
        r.factorial * convolutionWeight r * β ^ r * (2 * C * (c * K) ^ 2) := by
  set p := coordinateNormSeries v x with hp
  have hp0 : coeff 0 p = 0 := coeff_zero_coordinateNormSeries v x
  have hpn : ∀ j, 0 ≤ coeff j p := coeff_coordinateNormSeries_nonneg v x
  have hψr : 0 ≤ convolutionWeight r := (convolutionWeight_pos r).le
  have hcK0 : 0 ≤ c * K := mul_nonneg hc hK
  have hfac (m : ℕ) : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  -- the coefficients of `p` of index at most `min r N` obey the weighted bound
  have hpN : ∀ j, 1 ≤ j → j ≤ min r N → coeff j p ≤ c * β ^ j * convolutionWeight j := by
    intro j hj1 hjN
    have hjr : ((j : ℕ) : WithTop ℕ∞) ≤ ((r : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast hjN.trans (min_le_left r N)
    rw [hp, coeff_coordinateNormSeries v x (by omega), div_le_iff₀ (hfac j)]
    calc iteratedCoordinateNorm j v x ≤ familyNorm j v x :=
          iteratedCoordinateNorm_le_familyNorm j (hv.of_le hjr)
      _ ≤ j.factorial * c * convolutionWeight j * β ^ j :=
          hvb j hj1 (hjN.trans (min_le_right r N))
      _ = c * β ^ j * convolutionWeight j * j.factorial := by ring
  -- powers of `p`, with at least two factors
  have hpow (m : ℕ) : coeff r (p ^ (m + 2)) ≤ c ^ (m + 2) * β ^ r * convolutionWeight r := by
    refine coeff_pow_le_convolutionWeight hp0 hpn hc hβ hpN (by omega) ?_
    rcases Nat.lt_or_ge N r with h | h
    · exact Or.inr ⟨by rw [min_eq_right (by omega)]; omega, by omega⟩
    · exact Or.inl (by rw [min_eq_left h])
  -- the chain rule, with the sum split into `m = 0`, `m = 1` and `m ≥ 2`
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hcomp := iteratedCoordinateNorm_comp_le (r' + 1) hg hv
  rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hcomp
  have h0 : coeff (r' + 1) (p ^ 0) = 0 := by simp [PowerSeries.coeff_one]
  have hterm (m : ℕ) (hm : m < r') : ‖iteratedFDeriv ℝ (m + 2) g (v x)‖ / (m + 2).factorial *
      coeff (r' + 1) (p ^ (m + 2)) ≤
        C * (c * K) ^ 2 * β ^ (r' + 1) * convolutionWeight (r' + 1) * (c * K) ^ m := by
    have h1 : ‖iteratedFDeriv ℝ (m + 2) g (v x)‖ / (m + 2).factorial ≤ C * K ^ (m + 2) := by
      rw [div_le_iff₀ (hfac _)]
      exact (hgb (m + 2) (by omega)).trans_eq (by ring)
    calc ‖iteratedFDeriv ℝ (m + 2) g (v x)‖ / (m + 2).factorial *
          coeff (r' + 1) (p ^ (m + 2))
        ≤ (C * K ^ (m + 2)) * (c ^ (m + 2) * β ^ (r' + 1) * convolutionWeight (r' + 1)) :=
          mul_le_mul h1 (hpow m) (PowerSeries.coeff_pow_nonneg hpn _ _)
            (mul_nonneg hC (pow_nonneg hK _))
      _ = _ := by rw [mul_pow, mul_pow]; ring
  have hsum : ∑ m ∈ Finset.range r', ‖iteratedFDeriv ℝ (m + 2) g (v x)‖ / (m + 2).factorial *
      coeff (r' + 1) (p ^ (m + 2)) ≤
        C * (c * K) ^ 2 * β ^ (r' + 1) * convolutionWeight (r' + 1) * 2 := by
    calc _ ≤ ∑ m ∈ Finset.range r',
          C * (c * K) ^ 2 * β ^ (r' + 1) * convolutionWeight (r' + 1) * (c * K) ^ m :=
          Finset.sum_le_sum fun m hm ↦ hterm m (Finset.mem_range.mp hm)
      _ = C * (c * K) ^ 2 * β ^ (r' + 1) * convolutionWeight (r' + 1) *
            ∑ m ∈ Finset.range r', (c * K) ^ m := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (geom_sum_range_le_two hcK0 hcK r')
          (by positivity)
  have hone : ‖iteratedFDeriv ℝ (0 + 1) g (v x)‖ / (0 + 1).factorial *
      coeff (r' + 1) (p ^ (0 + 1)) ≤ C * K * (familyNorm (r' + 1) v x / (r' + 1).factorial) := by
    have h1 : ‖iteratedFDeriv ℝ (0 + 1) g (v x)‖ / (0 + 1).factorial ≤ C * K := by
      simpa using hgb 1 (by omega)
    have h2 : coeff (r' + 1) (p ^ (0 + 1)) ≤ familyNorm (r' + 1) v x / (r' + 1).factorial := by
      rw [zero_add, pow_one, hp, coeff_coordinateNormSeries v x (Nat.succ_ne_zero r')]
      exact div_le_div_of_nonneg_right (iteratedCoordinateNorm_le_familyNorm _ hv) (hfac _).le
    exact mul_le_mul h1 h2 (PowerSeries.coeff_pow_nonneg hpn _ _) (mul_nonneg hC hK)
  rw [h0, mul_zero, add_zero] at hcomp
  calc iteratedCoordinateNorm (r' + 1) (g ∘ v) x
      ≤ (r' + 1).factorial * (C * (c * K) ^ 2 * β ^ (r' + 1) * convolutionWeight (r' + 1) * 2 +
          C * K * (familyNorm (r' + 1) v x / (r' + 1).factorial)) :=
        hcomp.trans (mul_le_mul_of_nonneg_left (add_le_add hsum hone) (hfac _).le)
    _ = _ := by
        have := (hfac (r' + 1)).ne'
        field_simp
        ring

end PDE.Elliptic.Regularity.Analytic
