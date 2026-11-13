/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite recursion certificates for weighted interpolation

For the squared weighted norms `y_j` of the derivatives of order `j`, the one-step interpolation
inequalities `y_j ≤ η_j y_{j+1} + β_j y_{j-1}` for `0 < j < k`, with the endpoint terms in `y_0` and
`y_k` moved to the right, form a matrix inequality

`Q *ᵥ y ≤ low² • bLow + high² • bHigh`

for the internal vector `y`. We prove that a left inverse of `Q` with nonnegative entries turns it
into `yᵢ ≤ Aᵢ low² + Bᵢ high²` and, since `√(a + b) ≤ √a + √b`, into the additive bounds
`√yᵢ ≤ √Aᵢ low + √Bᵢ high` for the norms. A `FiniteInterpolationRecursionCertificate` records the
matrix, a left inverse with nonnegative entries and nonnegative endpoint source vectors;
`FiniteInterpolationRecursionCertificate.ofTridiagonal` builds one for the tridiagonal matrix
`interpolationRecursionMatrix forward backward`, with `1` on the diagonal, `-forward i` above it and
`-backward i` below it, when `forward` and `backward` are nonnegative, from a left inverse with
nonnegative entries. The one-step inequalities themselves depend on the weights and are not proved
here.

## References

* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, 2nd ed., Cambridge Mathematical
  Library, Cambridge University Press, 1988.
* R. S. Varga, *Matrix Iterative Analysis*, 2nd ed., Springer Series in Computational Mathematics,
  Springer, 2000.
  <https://doi.org/10.1007/978-3-642-05156-2>
* V. Duruisseaux, A. Ganeshram, R. J. George and A. Anandkumar, "Stability Framework for the
  Singularity of the Euler Equations on ℝ³", arXiv:2609.10860v2, Appendix A, Proposition 4,
  (183)-(192), pp. 39-40, for the recursion: the tridiagonal matrix (185), with `forward` and
  `backward` the coefficients `η_j` and `β_j`, the endpoint vectors (186), the nonnegative inverse
  (187) and the square-root step (192).
  <https://arxiv.org/abs/2609.10860v2>
-/

@[expose] public section

noncomputable section

open scoped Matrix

namespace SobolevSpace
namespace Weighted

set_option linter.missingDocs true

variable {ι : Type*} [Fintype ι]

/-- If `A` has nonnegative entries and `x ≤ y` componentwise, then `A x ≤ A y` componentwise. -/
theorem mulVec_le_mulVec_of_entrywise_nonnegative
    (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {x y : ι → ℝ} (hxy : ∀ j, x j ≤ y j) (i : ι) :
    (A *ᵥ x) i ≤ (A *ᵥ y) i := by
  simp only [Matrix.mulVec_apply_eq_sum]
  exact Finset.sum_le_sum fun j _ ↦
    mul_le_mul_of_nonneg_left (hxy j) (hA i j)

/-- For `a, b ≥ 0`, `√(a + b) ≤ √a + √b`. -/
theorem sqrt_add_le_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    √(a + b) ≤ √a + √b := by
  rw [Real.sqrt_le_iff]
  constructor
  · exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- If `Xj² ≤ A Xk² + B X0²` with `A`, `B`, `Xk`, `X0` nonnegative, `√A ≤ η` and `√B ≤ I`, then
`Xj ≤ η Xk + I X0`. -/
theorem le_endpoint_combination_of_sq_le
    {A B η I Xj Xk X0 : ℝ}
    (hXk : 0 ≤ Xk) (hX0 : 0 ≤ X0)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hSq : Xj ^ 2 ≤ A * Xk ^ 2 + B * X0 ^ 2)
    (hη : √A ≤ η) (hI : √B ≤ I) :
    Xj ≤ η * Xk + I * X0 := by
  have htermA : 0 ≤ A * Xk ^ 2 := mul_nonneg hA (sq_nonneg Xk)
  have htermB : 0 ≤ B * X0 ^ 2 := mul_nonneg hB (sq_nonneg X0)
  calc
    Xj ≤ √(Xj ^ 2) := by simpa only [Real.sqrt_sq_eq_abs] using le_abs_self Xj
    _ ≤ √(A * Xk ^ 2 + B * X0 ^ 2) := Real.sqrt_le_sqrt hSq
    _ ≤ √(A * Xk ^ 2) + √(B * X0 ^ 2) :=
        SobolevSpace.Weighted.sqrt_add_le_add_sqrt htermA htermB
    _ = √A * Xk + √B * X0 := by
        rw [Real.sqrt_mul hA, Real.sqrt_mul hB, Real.sqrt_sq hXk, Real.sqrt_sq hX0]
    _ ≤ η * Xk + I * X0 :=
        add_le_add
          (mul_le_mul_of_nonneg_right hη hXk)
          (mul_le_mul_of_nonneg_right hI hX0)

/-- If `M` has nonnegative entries and `y ≤ y0 b0 + yk bk` componentwise, then
`M y ≤ y0 (M b0) + yk (M bk)` componentwise. -/
theorem mulVec_le_endpoint_combination
    (M : Matrix ι ι ℝ)
    (y b0 bk : ι → ℝ) (y0 yk : ℝ)
    (hM : ∀ i j, 0 ≤ M i j)
    (hvec : ∀ i, y i ≤ b0 i * y0 + bk i * yk) :
    ∀ j, M.mulVec y j ≤ M.mulVec b0 j * y0 + M.mulVec bk j * yk := by
  intro j
  calc
    M.mulVec y j ≤ M.mulVec (fun i ↦ b0 i * y0 + bk i * yk) j :=
      SobolevSpace.Weighted.mulVec_le_mulVec_of_entrywise_nonnegative
        M hM hvec j
    _ = M.mulVec b0 j * y0 + M.mulVec bk j * yk := by
      simp [Matrix.mulVec, dotProduct, Finset.sum_add_distrib, Finset.sum_mul,
        mul_add, mul_assoc]

/-- If `Qinv` has nonnegative entries, `Qinv (Q y) = y` and `Q y ≤ y0 b0 + yk bk` componentwise,
then `y ≤ y0 (Qinv b0) + yk (Qinv bk)` componentwise. -/
theorem le_endpoint_combination_of_left_inverse
    (Q Qinv : Matrix ι ι ℝ)
    (y b0 bk : ι → ℝ) (y0 yk : ℝ)
    (hQinv : ∀ i j, 0 ≤ Qinv i j)
    (hleft : Qinv.mulVec (Q.mulVec y) = y)
    (hvec : ∀ i, Q.mulVec y i ≤ b0 i * y0 + bk i * yk) :
    ∀ j, y j ≤ Qinv.mulVec b0 j * y0 + Qinv.mulVec bk j * yk := by
  intro j
  calc
    y j = Qinv.mulVec (Q.mulVec y) j := by rw [hleft]
    _ ≤ Qinv.mulVec b0 j * y0 + Qinv.mulVec bk j * yk :=
      mulVec_le_endpoint_combination Qinv (Q.mulVec y) b0 bk y0 yk
        hQinv hvec j

/-- Exact algebraic data certifying a finite endpoint interpolation
recursion. -/
structure FiniteInterpolationRecursionCertificate (ι : Type*)
    [Fintype ι] [DecidableEq ι] where
  /-- Matrix of the internal recursion inequalities. -/
  system : Matrix ι ι ℝ
  /-- Explicitly checked left inverse of the system matrix. -/
  inverse : Matrix ι ι ℝ
  /-- Exact left-inverse identity. -/
  inverse_mul_system : inverse * system = 1
  /-- Entrywise nonnegativity needed to preserve vector inequalities. -/
  inverse_nonnegative : ∀ i j, 0 ≤ inverse i j
  /-- Nonnegative source vector multiplying the lower endpoint. -/
  lowSource : ι → NNReal
  /-- Nonnegative source vector multiplying the upper endpoint. -/
  highSource : ι → NNReal

namespace FiniteInterpolationRecursionCertificate

variable [DecidableEq ι]
variable (certificate : FiniteInterpolationRecursionCertificate ι)

/-- Every lower-endpoint source coefficient is nonnegative. -/
theorem lowSource_nonnegative (i : ι) :
    0 ≤ (certificate.lowSource i : ℝ) :=
  NNReal.coe_nonneg _

/-- Every upper-endpoint source coefficient is nonnegative. -/
theorem highSource_nonnegative (i : ι) :
    0 ≤ (certificate.highSource i : ℝ) :=
  NNReal.coe_nonneg _

/-- Build a recursion certificate from algebraic invertibility and an
entrywise-positivity proof for the ring inverse, as produced by exact or
interval approximate-inverse verification. -/
def ofIsUnit
    (system : Matrix ι ι ℝ) (hsystem : IsUnit system)
    (hinverseNonnegative :
      ∀ i j, 0 ≤ Ring.inverse system i j)
    (lowSource highSource : ι → ℝ)
    (hlowSource : ∀ i, 0 ≤ lowSource i)
    (hhighSource : ∀ i, 0 ≤ highSource i) :
    FiniteInterpolationRecursionCertificate ι where
  system := system
  inverse := Ring.inverse system
  inverse_mul_system := Ring.inverse_mul_cancel system hsystem
  inverse_nonnegative := hinverseNonnegative
  lowSource := fun i ↦ ⟨lowSource i, hlowSource i⟩
  highSource := fun i ↦ ⟨highSource i, hhighSource i⟩

/-- Endpoint forcing vector for two scalar endpoint values. -/
def endpointVector (low high : ℝ) : ι → ℝ :=
  low • (fun i ↦ (certificate.lowSource i : ℝ)) +
    high • (fun i ↦ (certificate.highSource i : ℝ))

/-- Coefficient vector produced by the lower-endpoint source. -/
def lowResponse : ι → ℝ :=
  certificate.inverse *ᵥ fun i ↦ (certificate.lowSource i : ℝ)

/-- Coefficient vector produced by the upper-endpoint source. -/
def highResponse : ι → ℝ :=
  certificate.inverse *ᵥ fun i ↦ (certificate.highSource i : ℝ)

/-- Every lower-endpoint response coefficient is nonnegative. -/
theorem lowResponse_nonnegative (i : ι) :
    0 ≤ certificate.lowResponse i := by
  simp only [lowResponse, Matrix.mulVec_apply_eq_sum]
  exact Finset.sum_nonneg fun j _ ↦
    mul_nonneg
      (certificate.inverse_nonnegative i j)
      (certificate.lowSource_nonnegative j)

/-- Every upper-endpoint response coefficient is nonnegative. -/
theorem highResponse_nonnegative (i : ι) :
    0 ≤ certificate.highResponse i := by
  simp only [highResponse, Matrix.mulVec_apply_eq_sum]
  exact Finset.sum_nonneg fun j _ ↦
    mul_nonneg
      (certificate.inverse_nonnegative i j)
      (certificate.highSource_nonnegative j)

/-- If `system internal ≤ endpointVector low high` componentwise, then
`internal i ≤ low * lowResponse i + high * highResponse i` for every `i`. -/
theorem internal_le_endpointCombination
    {internal : ι → ℝ} {low high : ℝ}
    (hsystem :
      ∀ i,
        (certificate.system *ᵥ internal) i ≤
          certificate.endpointVector low high i)
    (i : ι) :
    internal i ≤
      low * certificate.lowResponse i +
        high * certificate.highResponse i := by
  have hleft : certificate.inverse *ᵥ (certificate.system *ᵥ internal) = internal := by
    rw [Matrix.mulVec_mulVec, certificate.inverse_mul_system, Matrix.one_mulVec]
  have hbound := le_endpoint_combination_of_left_inverse
    certificate.system certificate.inverse internal
    (fun i ↦ (certificate.lowSource i : ℝ))
    (fun i ↦ (certificate.highSource i : ℝ)) low high
    certificate.inverse_nonnegative hleft
    (by simpa [endpointVector, mul_comm] using hsystem) i
  simpa only [lowResponse, highResponse, mul_comm] using hbound

/-- If `low, high ≥ 0` and the squares of `gauge` satisfy
`system (gauge²) ≤ endpointVector (low²) (high²)` componentwise, then
`gauge i ≤ √(lowResponse i) low + √(highResponse i) high` for every `i`. -/
theorem gauge_le_sqrt_endpointCombination
    {gauge : ι → ℝ} {low high : ℝ}
    (hlow : 0 ≤ low) (hhigh : 0 ≤ high)
    (hsystem :
      ∀ i,
        (certificate.system *ᵥ fun j ↦ gauge j ^ 2) i ≤
          certificate.endpointVector (low ^ 2) (high ^ 2) i)
    (i : ι) :
    gauge i ≤
      √(certificate.lowResponse i) * low +
        √(certificate.highResponse i) * high := by
  have hsquare :
      gauge i ^ 2 ≤
        certificate.lowResponse i * low ^ 2 +
          certificate.highResponse i * high ^ 2 := by
    simpa [mul_comm] using
      certificate.internal_le_endpointCombination hsystem i
  have hbound := le_endpoint_combination_of_sq_le
    hlow hhigh (certificate.lowResponse_nonnegative i)
    (certificate.highResponse_nonnegative i) hsquare le_rfl le_rfl
  exact hbound

/-- Under the hypotheses of `gauge_le_sqrt_endpointCombination`, if `√(lowResponse i)` and
`√(highResponse i)` are at most `lowCoefficient` and `highCoefficient`, then
`gauge i ≤ lowCoefficient * low + highCoefficient * high`. -/
theorem gauge_le_targetCoefficients
    {gauge : ι → ℝ} {low high lowCoefficient highCoefficient : ℝ}
    (hlow : 0 ≤ low) (hhigh : 0 ≤ high)
    (hsystem :
      ∀ i,
        (certificate.system *ᵥ fun j ↦ gauge j ^ 2) i ≤
          certificate.endpointVector (low ^ 2) (high ^ 2) i)
    (i : ι)
    (hlowCoefficient :
      √(certificate.lowResponse i) ≤ lowCoefficient)
    (hhighCoefficient :
      √(certificate.highResponse i) ≤ highCoefficient) :
    gauge i ≤ lowCoefficient * low + highCoefficient * high :=
  (certificate.gauge_le_sqrt_endpointCombination
      hlow hhigh hsystem i).trans
    (add_le_add
      (mul_le_mul_of_nonneg_right hlowCoefficient hlow)
      (mul_le_mul_of_nonneg_right hhighCoefficient hhigh))

end FiniteInterpolationRecursionCertificate

/-- Tridiagonal matrix for a nearest-neighbor interpolation recursion.

The row indexed by `i` has diagonal entry `1`, upper entry
`-forward i`, and lower entry `-backward i` whenever those neighbors exist.
-/
def interpolationRecursionMatrix {n : ℕ}
    (forward backward : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦
    if j = i then 1
    else if j.val = i.val + 1 then -forward i
    else if i.val = j.val + 1 then -backward i
    else 0

/-- Lower-endpoint source for the first row of a finite nearest-neighbor
recursion. -/
def interpolationLowSource {n : ℕ}
    (backward : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ if i.val = 0 then backward i else 0

/-- Upper-endpoint source for the last row of a finite nearest-neighbor
recursion. -/
def interpolationHighSource {n : ℕ}
    (forward : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ if i.val + 1 = n then forward i else 0

/-- The certificate for `interpolationRecursionMatrix forward backward` with nonnegative
coefficients, given a left inverse with nonnegative entries; its endpoint sources are
`interpolationLowSource backward` and `interpolationHighSource forward`. -/
def FiniteInterpolationRecursionCertificate.ofTridiagonal
    {n : ℕ} (forward backward : Fin n → ℝ)
    (inverse : Matrix (Fin n) (Fin n) ℝ)
    (hinverse :
      inverse * interpolationRecursionMatrix forward backward = 1)
    (hinverseNonnegative : ∀ i j, 0 ≤ inverse i j)
    (hforward : ∀ i, 0 ≤ forward i)
    (hbackward : ∀ i, 0 ≤ backward i) :
    FiniteInterpolationRecursionCertificate (Fin n) where
  system := interpolationRecursionMatrix forward backward
  inverse := inverse
  inverse_mul_system := hinverse
  inverse_nonnegative := hinverseNonnegative
  lowSource := fun i ↦
    ⟨interpolationLowSource backward i, by
      simp only [interpolationLowSource]
      split_ifs
      · exact hbackward i
      · exact le_rfl⟩
  highSource := fun i ↦
    ⟨interpolationHighSource forward i, by
      simp only [interpolationHighSource]
      split_ifs
      · exact hforward i
      · exact le_rfl⟩

/-- Let `M` have nonnegative entries, let `y ≤ y0 b0 + yk bk` componentwise, and let
`X j ^ 2 = (M y) j`, `y0 = X0²` and `yk = Xk²` with `X0, Xk ≥ 0`. If `(M bk) j` and `(M b0) j` are
nonnegative with square roots at most `η` and `I`, then `X j ≤ η Xk + I X0`. -/
theorem le_endpoint_combination_of_matrix_bound
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (y b0 bk : Fin n → ℝ) (X : Fin n → ℝ) (y0 yk X0 Xk η I : ℝ) (j : Fin n)
    (hM : ∀ i l, 0 ≤ M i l)
    (hvec : ∀ i, y i ≤ b0 i * y0 + bk i * yk)
    (hX0 : 0 ≤ X0) (hXk : 0 ≤ Xk)
    (hyj : X j ^ 2 = M.mulVec y j)
    (hy0 : y0 = X0 ^ 2) (hyk : yk = Xk ^ 2)
    (hA : 0 ≤ M.mulVec bk j) (hB : 0 ≤ M.mulVec b0 j)
    (hη : √(M.mulVec bk j) ≤ η)
    (hI : √(M.mulVec b0 j) ≤ I) :
    X j ≤ η * Xk + I * X0 := by
  have hmatrix := mulVec_le_endpoint_combination M y b0 bk y0 yk hM hvec j
  have hsq :
      X j ^ 2 ≤ M.mulVec bk j * Xk ^ 2 + M.mulVec b0 j * X0 ^ 2 := by
    calc
      X j ^ 2 = M.mulVec y j := hyj
      _ ≤ M.mulVec b0 j * y0 + M.mulVec bk j * yk := hmatrix
      _ = M.mulVec bk j * Xk ^ 2 + M.mulVec b0 j * X0 ^ 2 := by
        rw [hy0, hyk]
        ring
  exact
    le_endpoint_combination_of_sq_le
      hXk hX0 hA hB hsq hη hI

end Weighted
end SobolevSpace
