/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.FDeriv.PartialDeriv.OpenSet
public import PDE.FDeriv.PartialDeriv.Power
public import PDE.Analysis.Calculus.SecondPartial
public import PDE.FDeriv.PartialDeriv.HigherNormSq
public import PDE.Elliptic.Regularity.Boundary.CoefficientGeometry
public import PDE.Elliptic.Classical.MaximumPrinciple.MatrixSymmetrization

/-!
# Second-order operators with frozen coefficients

## Motivation

What do the product rule, the square and the powers look like for the operator
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ` with a constant matrix `A`, and what is its sign at a local maximum?

## The idea

A quasilinear operator `∑ᵢⱼ aᵢⱼ(x) ∂ᵢ∂ⱼ` applied at a point `x` only sees the matrix `a(x)`.
Freezing the coefficients at `x` gives an operator that commutes with every coordinate
derivative, and at the point `x` it agrees with the variable one. All identities here are for the
frozen operator `frozenOperator A`. The product rule has the usual two terms and a cross term in
the first derivatives, which is written with the pairing `principalPairing A`. At a local maximum
of a `C²` function the Hessian is negative semidefinite, so the operator is nonpositive there
whenever the quadratic form of `A` is nonnegative.

## Main results

* `frozenOperator_mul`: the product rule, for all `g`, `h` that are `C²` at the point.
* `frozenOperator_sq`, `frozenOperator_pow`: squares and powers.
* `frozenOperator_add`, `frozenOperator_const_mul`, `frozenOperator_sum`: linearity.
* `frozenOperator_nonpos_of_isLocalMax`: the sign at a local maximum, for all matrices with
  nonnegative quadratic form (no symmetry is assumed).
* `frozenOperator_partialDeriv_eventuallyEq`: the operator commutes with `∂ᵢ` near a point where
  the function is `C³`.

## Relations

`frozenOperator_eq_neg_matrixOperator` identifies the operator with the principal part of
`EllipticMaximum.matrixOperator`, and the sign at a local maximum is
`EllipticMaximum.factoredOperator_nonneg_at_localMax` after factoring the symmetric part of `A`.
`frozenOperator_mul` and `frozenOperator_add` are `PDE.secondPartialDeriv_mul_at` and
`PDE.secondPartialDeriv_add_at` summed against the matrix. `frozenOperator_sq` is the case
`g = h` of `frozenOperator_mul`, and `frozenOperator_pow` is an induction with it. These rules
are used by `PDE.Elliptic.Regularity.Analytic.Bernstein`.

## What stays open

Lower-order terms are not included; the operators of this folder have none after freezing.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Topology
open SobolevSpace.GraphSpace.BoundaryRegularity (principalEnergy principalPairing)

namespace PDE.Elliptic.Regularity.Analytic

variable {n : ℕ}

/-- The second-order operator `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ` with constant coefficients `A`. -/
def frozenOperator (A : Fin n → Fin n → ℝ) (h : ℝ^n → ℝ) (x : ℝ^n) : ℝ :=
  ∑ i, ∑ j, A i j * (∂[i] (∂[j] h)) x

/-- The pairing of a vector with itself is the quadratic form. -/
theorem principalPairing_self (A : Fin n → Fin n → ℝ) (ξ : Fin n → ℝ) :
    principalPairing A ξ ξ = principalEnergy A ξ := by
  simp only [principalPairing, principalEnergy]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- The quadratic form of a linear combination of two vectors. -/
theorem principalEnergy_smul_add_smul (A : Fin n → Fin n → ℝ) (s t : ℝ) (ξ ζ : Fin n → ℝ) :
    principalEnergy A (fun i ↦ s * ξ i + t * ζ i) =
      s ^ 2 * principalEnergy A ξ + t ^ 2 * principalEnergy A ζ +
        s * t * (principalPairing A ξ ζ + principalPairing A ζ ξ) := by
  simp only [principalPairing, principalEnergy, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- The pairing is homogeneous in each argument. -/
theorem principalPairing_smul_smul (A : Fin n → Fin n → ℝ) (s t : ℝ) (ξ ζ : Fin n → ℝ) :
    principalPairing A (fun i ↦ s * ξ i) (fun i ↦ t * ζ i) = s * t * principalPairing A ξ ζ := by
  simp only [principalPairing, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- **Product rule** for the frozen operator: the two usual terms and the cross term in the
first derivatives. -/
theorem frozenOperator_mul (A : Fin n → Fin n → ℝ) {g h : ℝ^n → ℝ} {x : ℝ^n}
    (hg : ContDiffAt ℝ 2 g x) (hh : ContDiffAt ℝ 2 h x) :
    frozenOperator A (fun y ↦ g y * h y) x =
      frozenOperator A g x * h x + g x * frozenOperator A h x +
        (principalPairing A (fun i ↦ (∂[i] g) x) (fun i ↦ (∂[i] h) x) +
          principalPairing A (fun i ↦ (∂[i] h) x) (fun i ↦ (∂[i] g) x)) := by
  have hprod (i j : Fin n) := secondPartialDeriv_mul_at i j hg hh
  simp only [frozenOperator, principalPairing, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [hprod i j]; ring

/-- The frozen operator of a square: `L(z²) = 2 z Lz + 2 q(∇z)`. -/
theorem frozenOperator_sq (A : Fin n → Fin n → ℝ) {z : ℝ^n → ℝ} {x : ℝ^n}
    (hz : ContDiffAt ℝ 2 z x) :
    frozenOperator A (fun y ↦ z y ^ 2) x =
      2 * z x * frozenOperator A z x + 2 * principalEnergy A (fun i ↦ (∂[i] z) x) := by
  have h := frozenOperator_mul A hz hz
  simp only [principalPairing_self] at h
  rw [show (fun y ↦ z y ^ 2) = fun y ↦ z y * z y from funext fun y ↦ sq (z y), h]
  ring

/-- The frozen operator of a power:
`L(g^{m+2}) = (m+2)(m+1) gᵐ q(∇g) + (m+2) g^{m+1} Lg`. -/
theorem frozenOperator_pow (A : Fin n → Fin n → ℝ) {g : ℝ^n → ℝ} {x : ℝ^n}
    (hg : ContDiffAt ℝ 2 g x) (m : ℕ) :
    frozenOperator A (fun y ↦ g y ^ (m + 2)) x =
      (m + 2) * (m + 1) * g x ^ m * principalEnergy A (fun i ↦ (∂[i] g) x) +
        (m + 2) * g x ^ (m + 1) * frozenOperator A g x := by
  have hd : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  induction m with
  | zero =>
    rw [frozenOperator_sq A hg]
    ring
  | succ m ih =>
    have hpow : ContDiffAt ℝ 2 (fun y ↦ g y ^ (m + 2)) x := hg.pow (m + 2)
    have hmul := frozenOperator_mul A hpow hg
    have hgrad : (fun i ↦ (∂[i] (fun y ↦ g y ^ (m + 2))) x) =
        fun i ↦ ((m : ℝ) + 2) * g x ^ (m + 1) * (∂[i] g) x := by
      funext i
      rw [hd.partialDeriv_fun_pow_succ (m + 1) i]
      push_cast
      ring
    rw [hgrad] at hmul
    have h1 := principalPairing_smul_smul A (((m : ℝ) + 2) * g x ^ (m + 1)) 1
      (fun i ↦ (∂[i] g) x) (fun i ↦ (∂[i] g) x)
    have h2 := principalPairing_smul_smul A 1 (((m : ℝ) + 2) * g x ^ (m + 1))
      (fun i ↦ (∂[i] g) x) (fun i ↦ (∂[i] g) x)
    simp only [one_mul, principalPairing_self] at h1 h2
    rw [show (fun y ↦ g y ^ (m + 1 + 2)) = fun y ↦ g y ^ (m + 2) * g y from
      funext fun y ↦ pow_succ (g y) (m + 2), hmul, h1, h2, ih]
    push_cast
    ring

/-- The frozen operator is additive on functions that are `C²` at the point. -/
theorem frozenOperator_add (A : Fin n → Fin n → ℝ) {g h : ℝ^n → ℝ} {x : ℝ^n}
    (hg : ContDiffAt ℝ 2 g x) (hh : ContDiffAt ℝ 2 h x) :
    frozenOperator A (fun y ↦ g y + h y) x = frozenOperator A g x + frozenOperator A h x := by
  have hsum (i j : Fin n) := secondPartialDeriv_add_at i j hg hh
  simp only [frozenOperator, hsum, mul_add, Finset.sum_add_distrib]

/-- The frozen operator commutes with multiplication by a constant. -/
theorem frozenOperator_const_mul (A : Fin n → Fin n → ℝ) (c : ℝ) (h : ℝ^n → ℝ) (x : ℝ^n) :
    frozenOperator A (fun y ↦ c * h y) x = c * frozenOperator A h x := by
  simp only [frozenOperator, partialDeriv_partialDeriv_const_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- The frozen operator is additive over finite sums of functions that are `C²` at the point. -/
theorem frozenOperator_sum (A : Fin n → Fin n → ℝ) {ι : Type*} (s : Finset ι)
    {h : ι → ℝ^n → ℝ} {x : ℝ^n} (hh : ∀ l ∈ s, ContDiffAt ℝ 2 (h l) x) :
    frozenOperator A (fun y ↦ ∑ l ∈ s, h l y) x = ∑ l ∈ s, frozenOperator A (h l) x := by
  have hd (j : Fin n) : ∂[j] (fun y ↦ ∑ l ∈ s, h l y) =ᶠ[𝓝 x] fun y ↦ ∑ l ∈ s, (∂[j] (h l)) y := by
    have hev : ∀ᶠ y in 𝓝 x, ∀ l ∈ s, DifferentiableAt ℝ (h l) y :=
      (eventually_all_finset s).mpr fun l hl ↦
        (hh l hl).eventually_differentiableAt (by norm_num)
    filter_upwards [hev] with y hy using partialDeriv_sum s hy j
  have hdd (i j : Fin n) : (∂[i] (∂[j] (fun y ↦ ∑ l ∈ s, h l y))) x =
      ∑ l ∈ s, (∂[i] (∂[j] (h l))) x := by
    rw [((hd j).partialDeriv i).self_of_nhds]
    exact partialDeriv_sum s (fun l hl ↦
      ((hh l hl).partialDeriv j (k := 1) (by norm_num)).differentiableAt (by norm_num)) i
  simp only [frozenOperator, hdd, Finset.mul_sum]
  exact (Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm).trans Finset.sum_comm

/-- The frozen operator depends only on the germ of the function at the point. -/
theorem _root_.Filter.EventuallyEq.frozenOperator_eq (A : Fin n → Fin n → ℝ) {g h : ℝ^n → ℝ}
    {x : ℝ^n} (hgh : g =ᶠ[𝓝 x] h) :
    PDE.Elliptic.Regularity.Analytic.frozenOperator A g x =
      PDE.Elliptic.Regularity.Analytic.frozenOperator A h x := by
  simp only [PDE.Elliptic.Regularity.Analytic.frozenOperator]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
    rw [((hgh.partialDeriv j).partialDeriv i).self_of_nhds]

/-- The frozen operator commutes with a coordinate derivative near a point where the function is
`C³`. -/
theorem frozenOperator_partialDeriv_eventuallyEq (A : Fin n → Fin n → ℝ) {f : ℝ^n → ℝ}
    {x : ℝ^n} (hf : ContDiffAt ℝ 3 f x) (l : Fin n) :
    frozenOperator A (∂[l] f) =ᶠ[𝓝 x] ∂[l] (frozenOperator A f) := by
  filter_upwards [hf.eventually (by simp)] with y hy
  have h3 : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 3 f z := hy.eventually (by simp)
  -- near `y` the two orders of differentiation agree
  have hswap (j : Fin n) : ∂[j] (∂[l] f) =ᶠ[𝓝 y] ∂[l] (∂[j] f) := by
    filter_upwards [h3] with z hz
    exact partialDeriv_partialDeriv_comm_at j l (hz.of_le (by norm_num))
  have hcomm (i j : Fin n) : (∂[i] (∂[j] (∂[l] f))) y = (∂[l] (∂[i] (∂[j] f))) y := by
    rw [((hswap j).partialDeriv i).self_of_nhds]
    exact partialDeriv_partialDeriv_comm_at i l (hy.partialDeriv j (k := 2) (by norm_num))
  have hsum : (∂[l] (frozenOperator A f)) y =
      ∑ i, ∑ j, A i j * (∂[l] (∂[i] (∂[j] f))) y := by
    have hd (i j : Fin n) : DifferentiableAt ℝ (∂[i] (∂[j] f)) y :=
      ((hy.partialDeriv j (k := 2) (by norm_num)).partialDeriv i (k := 1)
        (by norm_num)).differentiableAt (by norm_num)
    change (∂[l] (fun z ↦ ∑ i, ∑ j, A i j * (∂[i] (∂[j] f)) z)) y = _
    rw [partialDeriv_sum Finset.univ (fun i _ ↦ DifferentiableAt.fun_sum fun j _ ↦
      (hd i j).const_mul (A i j)) l]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [partialDeriv_sum Finset.univ (fun j _ ↦ (hd i j).const_mul (A i j)) l]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [partialDeriv_const_mul_fun]
  simp only [frozenOperator, hcomm]
  exact hsum.symm

/-- The frozen operator is the principal part of the matrix operator of the maximum principle,
with the sign of Evans's convention removed. -/
theorem frozenOperator_eq_neg_matrixOperator (A : Fin n → Fin n → ℝ) (h : ℝ^n → ℝ) (x : ℝ^n) :
    frozenOperator A h x =
      -EllipticMaximum.matrixOperator (fun _ ↦ Matrix.of A) (fun _ ↦ 0) (fun _ ↦ 0) h x := by
  simp [frozenOperator, EllipticMaximum.matrixOperator]

/-- **Sign at a local maximum.** If the quadratic form of `A` is nonnegative, the frozen operator
is nonpositive at a local maximum of a `C²` function. The matrix need not be symmetric. -/
theorem frozenOperator_nonpos_of_isLocalMax {A : Fin n → Fin n → ℝ}
    (hA : ∀ ξ : Fin n → ℝ, 0 ≤ principalEnergy A ξ) {h : ℝ^n → ℝ} {x : ℝ^n}
    (hmax : IsLocalMax h x) (hh : ContDiffAt ℝ 2 h x) : frozenOperator A h x ≤ 0 := by
  have hpsd := EllipticMaximum.posSemidef_selfAdjointPart_of_nonneg_quadratic (Matrix.of A)
    (fun v ↦ by simpa [principalEnergy] using hA v)
  obtain ⟨σ, hσ⟩ := EllipticMaximum.exists_factors_of_posSemidef hpsd
  have h1 := EllipticMaximum.matrixOperator_selfAdjointPart (fun _ ↦ Matrix.of A) (fun _ ↦ 0)
    (fun _ ↦ 0) hh
  have h2 := EllipticMaximum.matrixOperator_eq_factoredOperator
    (fun _ ↦ (selfAdjointPart ℝ (Matrix.of A) : Matrix (Fin n) (Fin n) ℝ)) (fun _ ↦ σ)
    (fun _ ↦ 0) (fun _ ↦ 0) hh hσ
  have h3 := EllipticMaximum.factoredOperator_nonneg_at_localMax (fun _ ↦ σ) (fun _ ↦ 0)
    (fun _ ↦ 0) hmax hh (by simp)
  rw [frozenOperator_eq_neg_matrixOperator, ← h1, h2]
  linarith

end PDE.Elliptic.Regularity.Analytic
