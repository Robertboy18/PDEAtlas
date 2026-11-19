/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Approximation.Splines.TensorHorner

/-!
# Mixed derivatives of tensor Horner polynomials

Mathlib's iterated derivative of a power supplies the falling factorial.
Finite-sum differentiation and reindexing then identify the executable derivative
coefficient table with mixed real derivatives, for arbitrary derivative orders.
Value equality on a product cell transfers this identity to any function with the
stated slice regularity. At outer data endpoints that regularity must be
proved for the chosen profile extension; cellwise value agreement does not supply it.
-/

@[expose] public section
namespace CAS.Splines
open scoped BigOperators ContDiff

private theorem sum_descFactorial_reindex (n a : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    (∑ i ∈ Finset.range n, c i * (i.descFactorial a : ℝ) * x ^ (i - a)) =
      ∑ i ∈ Finset.range (n - a), c (i + a) * ((i + a).descFactorial a : ℝ) * x ^ i := by
  by_cases ha : a ≤ n
  · have hn : n = a + (n - a) := by omega
    conv_lhs => rw [hn, Finset.sum_range_add]
    have hzero : (∑ i ∈ Finset.range a, c i * (i.descFactorial a : ℝ) * x ^ (i - a)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [Nat.descFactorial_of_lt (Finset.mem_range.mp hi)]
    rw [hzero, zero_add]
    apply Finset.sum_congr rfl
    intro i _
    simp [Nat.add_comm a i]
  · have hna : n ≤ a := by omega
    rw [Nat.sub_eq_zero_of_le hna, Finset.range_zero, Finset.sum_empty]
    apply Finset.sum_eq_zero
    intro i hi
    have hia : i < a := (Finset.mem_range.mp hi).trans_le hna
    simp [Nat.descFactorial_of_lt hia]

private theorem iteratedDeriv_power_sum (n a : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    iteratedDeriv a (fun r ↦ ∑ i ∈ Finset.range n, c i * r ^ i) x =
      ∑ i ∈ Finset.range (n - a), c (i + a) * ((i + a).descFactorial a : ℝ) * x ^ i := by
  rw [iteratedDeriv_fun_sum (fun i _ ↦ contDiffAt_const.mul (contDiffAt_id.pow i))]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_pow]
  simpa only [mul_assoc] using sum_descFactorial_reindex n a c x

/-- Mixed derivatives of a finite bivariate power sum use shifted falling-factorial coefficients. -/
theorem mixed_iteratedDeriv_power_sum (nx ny a b : ℕ) (c : ℕ → ℕ → ℝ) (x y : ℝ) :
    iteratedDeriv a (fun r ↦ iteratedDeriv b
      (fun z ↦ ∑ i ∈ Finset.range nx, ∑ j ∈ Finset.range ny, c i j * r ^ i * z ^ j) y) x =
      ∑ i ∈ Finset.range (nx - a), ∑ j ∈ Finset.range (ny - b),
        c (i + a) (j + b) * ((i + a).descFactorial a : ℝ) *
          ((j + b).descFactorial b : ℝ) * x ^ i * y ^ j := by
  have haxial (r : ℝ) : iteratedDeriv b
      (fun z ↦ ∑ i ∈ Finset.range nx, ∑ j ∈ Finset.range ny, c i j * r ^ i * z ^ j) y =
        ∑ i ∈ Finset.range nx, ∑ j ∈ Finset.range (ny - b),
          (c i (j + b) * r ^ i) * ((j + b).descFactorial b : ℝ) * y ^ j := by
    rw [iteratedDeriv_fun_sum (fun i _ ↦ ContDiffAt.sum
      (fun j _ ↦ contDiffAt_const.mul (contDiffAt_id.pow j)))]
    apply Finset.sum_congr rfl
    intro i _
    exact iteratedDeriv_power_sum ny b (fun j ↦ c i j * r ^ i) y
  have hfunction : (fun r ↦ iteratedDeriv b
      (fun z ↦ ∑ i ∈ Finset.range nx, ∑ j ∈ Finset.range ny, c i j * r ^ i * z ^ j) y) =
      fun r ↦ ∑ j ∈ Finset.range (ny - b), ∑ i ∈ Finset.range nx,
        (c i (j + b) * ((j + b).descFactorial b : ℝ) * y ^ j) * r ^ i := by
    funext r
    rw [haxial, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfunction, iteratedDeriv_fun_sum (fun j _ ↦ ContDiffAt.sum
    (fun i _ ↦ contDiffAt_const.mul (contDiffAt_id.pow i)))]
  simp_rw [iteratedDeriv_power_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A rectangular tensor polynomial is smooth jointly in both real coordinates. -/
theorem contDiff_tensorHornerValue (nx ny : ℕ) (c : ℕ → ℕ → ℚ) (n : ℕ∞ω) :
    ContDiff ℝ n (fun p : ℝ × ℝ ↦
      tensorHornerValue (tensorCoefficients nx ny c) p.1 p.2) := by
  simp_rw [tensorHornerValue_tensorCoefficients]
  exact ContDiff.sum fun i _ ↦ ContDiff.sum fun j _ ↦
    (contDiff_const.mul (contDiff_fst.pow i)).mul (contDiff_snd.pow j)

/-- Exact mixed-derivative coefficients, with empty tables for orders beyond the degree. -/
def tensorDerivativeCoefficients (nx ny : ℕ) (c : ℕ → ℕ → ℚ) (a b : ℕ) : List (List ℚ) :=
  tensorCoefficients (nx - a) (ny - b) fun i j ↦
    c (i + a) (j + b) * ((i + a).descFactorial a : ℚ) * ((j + b).descFactorial b : ℚ)

/-- The executable derivative coefficient table denotes the mixed tensor derivative. -/
theorem mixed_iteratedDeriv_tensorHornerValue (nx ny : ℕ) (c : ℕ → ℕ → ℚ)
    (a b : ℕ) (x y : ℝ) :
    iteratedDeriv a (fun r ↦ iteratedDeriv b
      (tensorHornerValue (tensorCoefficients nx ny c) r) y) x =
        tensorHornerValue (tensorDerivativeCoefficients nx ny c a b) x y := by
  have hfunction : tensorHornerValue (tensorCoefficients nx ny c) =
      fun r z ↦ ∑ i ∈ Finset.range nx, ∑ j ∈ Finset.range ny, (c i j : ℝ) * r ^ i * z ^ j := by
    funext r z
    exact tensorHornerValue_tensorCoefficients nx ny c r z
  rw [hfunction, mixed_iteratedDeriv_power_sum, tensorDerivativeCoefficients,
    tensorHornerValue_tensorCoefficients]
  simp only [Rat.cast_mul, Rat.cast_natCast]

/-- Axial differentiation leaves a smooth polynomial in the radial coordinate. -/
theorem contDiff_axialJet_tensorHornerValue (nx ny : ℕ) (c : ℕ → ℕ → ℚ)
    (b : ℕ) (n : ℕ∞ω) (y : ℝ) :
    ContDiff ℝ n (fun r ↦ iteratedDeriv b
      (tensorHornerValue (tensorCoefficients nx ny c) r) y) := by
  have heq : (fun r ↦ iteratedDeriv b
      (tensorHornerValue (tensorCoefficients nx ny c) r) y) =
      fun r ↦ tensorHornerValue (tensorDerivativeCoefficients nx ny c 0 b) r y := by
    funext r
    exact mixed_iteratedDeriv_tensorHornerValue nx ny c 0 b r y
  rw [heq]
  have h := (contDiff_tensorHornerValue (nx - 0) (ny - b)
    (fun i j ↦ c (i + 0) (j + b) * ((i + 0).descFactorial 0 : ℚ) *
      ((j + b).descFactorial b : ℚ)) n).comp (contDiff_id.prodMk (contDiff_const (c := y)))
  exact h

private theorem iteratedDeriv_eq_of_eqOn {f g : ℝ → ℝ} {s : Set ℝ} {x : ℝ} (n : ℕ)
    (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) (heq : Set.EqOn f g s)
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    iteratedDeriv n f x = iteratedDeriv n g x := by
  rw [← iteratedDerivWithin_eq_iteratedDeriv hs hf hx,
    ← iteratedDerivWithin_eq_iteratedDeriv hs hg hx]
  exact iteratedDerivWithin_congr heq hx

/-- Value equality on a product cell identifies mixed derivatives with
computed polynomial derivatives. Unique differentiability admits closed and
half-closed nondegenerate cells; the slice regularity hypotheses ensure
ordinary derivatives are used even at knots or other cell boundaries. -/
theorem mixed_iteratedDeriv_eq_tensorHorner_of_eqOn (nx ny : ℕ) (c : ℕ → ℕ → ℚ)
    (f : ℝ → ℝ → ℝ) (a b : ℕ) {sx sy : Set ℝ} {x y : ℝ}
    (hsx : UniqueDiffOn ℝ sx) (hsy : UniqueDiffOn ℝ sy) (hx : x ∈ sx) (hy : y ∈ sy)
    (heq : ∀ r ∈ sx, ∀ z ∈ sy, f r z = tensorHornerValue (tensorCoefficients nx ny c) r z)
    (haxial : ∀ r ∈ sx, ContDiffAt ℝ b (f r) y)
    (hradial : ContDiffAt ℝ a (fun r ↦ iteratedDeriv b (f r) y) x) :
    iteratedDeriv a (fun r ↦ iteratedDeriv b (f r) y) x =
      tensorHornerValue (tensorDerivativeCoefficients nx ny c a b) x y := by
  have haxialEq : Set.EqOn (fun r ↦ iteratedDeriv b (f r) y)
      (fun r ↦ iteratedDeriv b (tensorHornerValue (tensorCoefficients nx ny c) r) y) sx := by
    intro r hr
    apply iteratedDeriv_eq_of_eqOn b hsy hy (heq r hr) (haxial r hr)
    have hp := (contDiff_tensorHornerValue nx ny c b).comp
      ((contDiff_const (c := r)).prodMk contDiff_id)
    exact hp.contDiffAt
  have hpoly := (contDiff_axialJet_tensorHornerValue nx ny c b a y).contDiffAt (x := x)
  exact (iteratedDeriv_eq_of_eqOn a hsx hx haxialEq hradial hpoly).trans
    (mixed_iteratedDeriv_tensorHornerValue nx ny c a b x y)

end CAS.Splines
