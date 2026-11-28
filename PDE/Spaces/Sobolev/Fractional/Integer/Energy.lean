/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Spaces.Sobolev.Evolution.VectorL2Triple
public import PDE.Spaces.Sobolev.Fractional.Integer.Complexification
public import PDE.Spaces.Sobolev.Fractional.Integer.NormComparison
public import PDE.Spaces.Sobolev.GraphSpace.Operators.WholeSpaceVector
public import PDE.Spaces.Sobolev.GraphSpace.Operators.ZeroOrder
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.WholeSpaceClass
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Energy

/-!
# The Sobolev energy at integer order and the graph norm

The vector fields of a fluid live in `VectorH n k`, the finite products of the graph spaces
`W^{k,2}(ℝⁿ)` of integer order. This module compares their graph norms with the energy `E_k` of
the complexified components. The two are equivalent, with constants that depend on `n` and `k`
only: the base coordinate of `U ∈ W^{k,2}(ℝⁿ)` has `E_k ≤ c² ‖U‖²`, and a real `L²` function with
`E_k < ∞` is the base coordinate of some `V ∈ W^{k,2}(ℝⁿ)` with `‖V‖² ≤ c'² E_k`. For vector
fields both directions hold componentwise and add up. The constants come from
`norm_ofWkpSpace_le` and `toWkpSpaceNormBound`; they are not sharp, and the two norms agree only
at `k = 0`. With `besselEnergy_interpolation`, these comparisons turn bounds between graph spaces
into bounds at real orders (`PDE.Spaces.Sobolev.Fractional.Integer.RealOrders`).

## Main results

* `besselEnergy_baseL2_le`, `besselEnergy_vectorBaseL2_le`: the energy of order `k` of the base
  is at most `c² ‖·‖²`, for every `U ∈ W^{k,2}(ℝⁿ)` and every `u ∈ VectorH n k`.
* `exists_wkpSpace_of_besselEnergy_lt_top`, `exists_vectorH_of_besselEnergy_lt_top`: a real
  function, or a vector field, in `L²` with finite energy of order `k` lifts to order `k`, with
  `‖·‖² ≤ c'² E_k`.
* `vectorBaseL2`: the complexified base coordinates of a vector field, additive and injective
  (`vectorBaseL2_add`, `vectorBaseL2_injective`).

## How it works

Each direction is a statement about the base coordinate of a graph-space element. The first is
`norm_ofWkpSpace_le` with `besselEnergy_toL2Fun`. The second is
`SobolevSpace.GraphSpace.exists_wkpSpace_of_isRealL2_of_memLp_besselWeight`, since the energy of
`g` is the square of the `L²` norm of `(1 + |ξ|²)^{k/2} ĝ` (`besselEnergy_unit`). For vector
fields the norm of `VectorH n k` is the Euclidean norm of the components, and the energy of a
family is the sum of the energies of its members (`besselEnergy_eq_sum`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.5, Theorem 8, pp. 297-298; the two-sided bound is (20),
  p. 297.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter FourierTransform BesselPotentialSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal BesselPotentialSpace Sobolev

namespace SobolevSpace.Fractional

variable {n k : ℕ}

/-! ## Scalar functions -/

/-- **The base coordinate of a graph-space element has finite energy of order `k`**, at most
`c² ‖U‖²` with the constant of `norm_ofWkpSpace_le`. -/
theorem besselEnergy_baseL2_le (U : W^{k,2}(ℝ^n)) :
    besselEnergy (k : ℝ) (fun _ : Unit ↦ baseL2 U) ≤ ENNReal.ofReal
      (((2 : ℝ) ^ (k - 1) * (1 + (n : ℝ) ^ (k - 1)) * ((n : ℝ) + 1) * ‖U‖) ^ 2) := by
  rw [← toL2Fun_ofWkpSpace U, besselEnergy_toL2Fun]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (norm_ofWkpSpace_le U) 2)

/-- **A real `L²` function with finite energy of order `k` is the base coordinate of an element
of `W^{k,2}(ℝⁿ)`**, whose squared norm is at most `toWkpSpaceNormBound n k ^ 2` times the
energy. -/
theorem exists_wkpSpace_of_besselEnergy_lt_top (g : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (hg : IsRealL2 g) (h : besselEnergy (k : ℝ) (fun _ : Unit ↦ g) < ⊤) :
    ∃ V : W^{k,2}(ℝ^n), baseL2 V = g ∧ ENNReal.ofReal (‖V‖ ^ 2) ≤
      ENNReal.ofReal (toWkpSpaceNormBound n k ^ 2) *
        besselEnergy (k : ℝ) (fun _ : Unit ↦ g) := by
  rw [besselEnergy_unit] at h ⊢
  have hfin : eLpNorm (fun ξ ↦ besselSymbol n k ξ *
      (𝓕 g : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ) 2 volume < ⊤ := by
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc] at h
    simp at h
  obtain ⟨V, hV, hnorm⟩ := exists_wkpSpace_of_isRealL2_of_memLp_besselWeight g hg hfin
  refine ⟨V, hV, ?_⟩
  refine (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hnorm 2)).trans_eq ?_
  rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.toReal_pow,
    ENNReal.ofReal_toReal (ENNReal.pow_lt_top hfin).ne]

/-! ## Vector fields -/

/-- The complexified base coordinates of a vector field of order `k`, as a family of complex
`L²` functions. -/
def vectorBaseL2 (u : VectorH n k) : Fin n → Lp ℂ 2 (volume : Measure (ℝ^n)) :=
  fun i ↦ baseL2 (u i)

/-- Forgetting derivatives does not change the base coordinates. -/
theorem vectorBaseL2_vectorLowerOrderCLM {j : ℕ} (hjk : j ≤ k) (u : VectorH n k) :
    vectorBaseL2 (vectorLowerOrderCLM hjk u) = vectorBaseL2 u :=
  funext fun i ↦ baseL2_lowerOrderCLM hjk (u i)

/-- The base coordinates of a sum of vector fields are the sums of the base coordinates. -/
theorem vectorBaseL2_add (u v : VectorH n k) :
    vectorBaseL2 (u + v) = vectorBaseL2 u + vectorBaseL2 v :=
  funext fun i ↦ baseL2_add (u i) (v i)

/-- The base coordinates of the opposite vector field. -/
theorem vectorBaseL2_neg (u : VectorH n k) : vectorBaseL2 (-u) = -vectorBaseL2 u := by
  funext i
  change baseL2 (-u i) = -baseL2 (u i)
  rw [← complexifyL2CLM_base, map_neg, map_neg, complexifyL2CLM_base]

/-- The base coordinates of a difference of vector fields. -/
theorem vectorBaseL2_sub (u v : VectorH n k) :
    vectorBaseL2 (u - v) = vectorBaseL2 u - vectorBaseL2 v := by
  rw [sub_eq_add_neg, vectorBaseL2_add, vectorBaseL2_neg, sub_eq_add_neg]

/-- The base coordinates of the zero vector field. -/
theorem vectorBaseL2_zero :
    vectorBaseL2 (0 : VectorH n k) = fun _ : Fin n ↦ (0 : Lp ℂ 2 (volume : Measure (ℝ^n))) := by
  funext i
  change baseL2 (0 : W^{k,2}(ℝ^n)) = 0
  rw [← complexifyL2CLM_base, map_zero, map_zero]

/-- **The base coordinates determine the field**: a vector field of order `k` is determined by
its components as `L²` functions. This is `baseL2_injective` in each component. -/
theorem vectorBaseL2_injective : Function.Injective (vectorBaseL2 (n := n) (k := k)) :=
  fun _ _ h ↦ PiLp.ext fun i ↦ baseL2_injective (congrFun h i)

/-- **The base of a vector field of order `k` has finite energy of order `k`**, at most
`c² ‖u‖²`. -/
theorem besselEnergy_vectorBaseL2_le (u : VectorH n k) :
    besselEnergy (k : ℝ) (vectorBaseL2 u) ≤ ENNReal.ofReal
      (((2 : ℝ) ^ (k - 1) * (1 + (n : ℝ) ^ (k - 1)) * ((n : ℝ) + 1)) ^ 2 * ‖u‖ ^ 2) := by
  rw [besselEnergy_eq_sum, PiLp.norm_sq_eq_of_L2, Finset.mul_sum,
    ENNReal.ofReal_sum_of_nonneg fun i _ ↦ by positivity]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [← mul_pow]
  exact besselEnergy_baseL2_le (u i)

/-- **A vector field in `L²` with finite energy of order `k` lifts to order `k`**: there is
`u ∈ VectorH n k` over it with `‖u‖² ≤ toWkpSpaceNormBound n k ^ 2 * E_k`. -/
theorem exists_vectorH_of_besselEnergy_lt_top (x : VectorH n 0)
    (h : besselEnergy (k : ℝ) (vectorBaseL2 x) < ⊤) :
    ∃ u : VectorH n k, vectorLowerOrderCLM (Nat.zero_le k) u = x ∧
      ENNReal.ofReal (‖u‖ ^ 2) ≤ ENNReal.ofReal (toWkpSpaceNormBound n k ^ 2) *
        besselEnergy (k : ℝ) (vectorBaseL2 x) := by
  rw [besselEnergy_eq_sum] at h ⊢
  have hi (i : Fin n) : besselEnergy (k : ℝ) (fun _ : Unit ↦ baseL2 (x i)) < ⊤ :=
    lt_of_le_of_lt (Finset.single_le_sum
      (f := fun i ↦ besselEnergy (k : ℝ) (fun _ : Unit ↦ baseL2 (x i)))
      (fun _ _ ↦ zero_le) (Finset.mem_univ i)) h
  choose V hV hVn using fun i ↦
    exists_wkpSpace_of_besselEnergy_lt_top (k := k) (baseL2 (x i)) (isRealL2_baseL2 (x i)) (hi i)
  refine ⟨WithLp.toLp 2 V, ?_, ?_⟩
  · refine PiLp.ext fun i ↦ ?_
    rw [vectorLowerOrderCLM_apply]
    apply baseL2_injective
    rw [baseL2_lowerOrderCLM]
    exact hV i
  · rw [PiLp.norm_sq_eq_of_L2, ENNReal.ofReal_sum_of_nonneg fun i _ ↦ sq_nonneg _,
      Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ hVn i

end SobolevSpace.Fractional
