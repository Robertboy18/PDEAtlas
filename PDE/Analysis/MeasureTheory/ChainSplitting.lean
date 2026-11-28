/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Splitting a function of mean zero along a chain of overlapping pieces

Let `g` have mean zero on a union of pieces `D₀, …, D_{N-1}`, each overlapping the next. We
write `g` as a sum of functions of mean zero, one on each piece, with the transferred masses
bounded by `k ∫ |g|`. This is the splitting that Bogovskii's operator needs on a domain covered
by a chain of pieces, such as an annulus: the formula on each piece needs data of mean zero
there. The statements hold on any measure space, for any families `χ` and `θ` with
the stated integrability. A cover whose overlaps form a tree needs the same argument along the
tree, which is not written.

## Main results

* `MeasureTheory.sum_chainPart`: the parts add up to `g` when `(∑ χ_k) g = g` and `∫ g = 0`.
* `MeasureTheory.integral_chainPart`: each part has mean zero when `θ_k` and `θ_{k-1}` have mass
  one.
* `MeasureTheory.abs_chainMass_le`: the mass collected before the piece `k` is at most
  `k ∫ |g|` when `|χ_j| ≤ 1`.
* `MeasureTheory.chainMass_add_smul`, `MeasureTheory.chainPart_add_smul`: the masses and the
  parts are linear in `g`.

## How it works

Cut `g` with the partition `χ`, `g = ∑ χ_k g`. The cut pieces do not have mean zero, so the
surplus is passed down the chain. Put a function `θ_k` of mass one on the overlap of `D_k` and
`D_{k+1}`, and let `m_k = ∑_{j < k} ∫ χ_j g` be the mass collected before the piece `k`. The part
`χ_k g - m_{k+1} θ_k + m_k θ_{k-1}` has mass `∫ χ_k g - m_{k+1} + m_k = 0`, the corrections
telescope, and the last surplus is `m_N = ∫ g = 0`. The index `k - 1` is the truncated
subtraction of `ℕ`; at `k = 0` its coefficient is `m_0 = 0`, so the first piece needs no special
case.
-/

@[expose] public noncomputable section

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (χ θ : ℕ → X → ℝ) (g : X → ℝ)

/-- The mass collected before the piece `k`: `∑_{j < k} ∫ χ_j g`. -/
def chainMass (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, ∫ x, χ j x * g x ∂μ

/-- The part of `g` on the piece `k`: `χ_k g - m_{k+1} θ_k + m_k θ_{k-1}`. -/
def chainPart (k : ℕ) (x : X) : ℝ :=
  χ k x * g x - chainMass μ χ g (k + 1) * θ k x + chainMass μ χ g k * θ (k - 1) x

variable {μ χ θ g}

/-- No mass has been collected before the first piece. -/
@[simp]
theorem chainMass_zero : chainMass μ χ g 0 = 0 := by
  simp [chainMass]

/-- The mass collected up to the piece `k`, from the mass up to the piece `k - 1`. -/
theorem chainMass_succ (k : ℕ) :
    chainMass μ χ g (k + 1) = chainMass μ χ g k + ∫ x, χ k x * g x ∂μ :=
  Finset.sum_range_succ _ _

/-- The parts add up to `g`, when the partition is one where `g` lives and `g` has mean zero:
the corrections telescope, and the last one is `m_N = ∫ g = 0`. -/
theorem sum_chainPart {N : ℕ} (hint : ∀ j < N, Integrable (fun x ↦ χ j x * g x) μ)
    (hsum : ∀ x, (∑ k ∈ Finset.range N, χ k x) * g x = g x) (hg : ∫ x, g x ∂μ = 0) (x : X) :
    ∑ k ∈ Finset.range N, chainPart μ χ θ g k x = g x := by
  have hN : chainMass μ χ g N = 0 := by
    rw [chainMass, ← integral_finsetSum _ fun j hj ↦ hint j (Finset.mem_range.1 hj), ← hg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    change ∑ i ∈ Finset.range N, χ i y * g y = g y
    rw [← Finset.sum_mul, hsum]
  have hpart (k : ℕ) : chainPart μ χ θ g k x = χ k x * g x -
      (chainMass μ χ g (k + 1) * θ (k + 1 - 1) x - chainMass μ χ g k * θ (k - 1) x) := by
    rw [Nat.add_sub_cancel, chainPart]
    ring
  simp_rw [hpart]
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun k ↦ chainMass μ χ g k * θ (k - 1) x), hN,
    chainMass_zero, ← Finset.sum_mul, hsum]
  ring

/-- Each part has mean zero when `θ_k` and `θ_{k-1}` have mass one:
`∫ χ_k g - m_{k+1} + m_k = 0`. -/
theorem integral_chainPart {k : ℕ} (hχ : Integrable (fun x ↦ χ k x * g x) μ)
    (hθ : Integrable (θ k) μ) (hθ' : Integrable (θ (k - 1)) μ) (h1 : ∫ x, θ k x ∂μ = 1)
    (h1' : ∫ x, θ (k - 1) x ∂μ = 1) : ∫ x, chainPart μ χ θ g k x ∂μ = 0 := by
  have ha : Integrable (fun x ↦ chainMass μ χ g (k + 1) * θ k x) μ := hθ.const_mul _
  have hb : Integrable (fun x ↦ chainMass μ χ g k * θ (k - 1) x) μ := hθ'.const_mul _
  have hc : Integrable (fun x ↦ χ k x * g x - chainMass μ χ g (k + 1) * θ k x) μ := hχ.sub ha
  simp only [chainPart]
  rw [integral_add hc hb, integral_sub hχ ha, integral_const_mul, integral_const_mul, h1, h1',
    chainMass_succ]
  ring

/-- The collected mass is at most `k ∫ |g|` when the cutoffs are bounded by one. -/
theorem abs_chainMass_le (hχ : ∀ j x, |χ j x| ≤ 1) (hg : Integrable g μ) (k : ℕ) :
    |chainMass μ χ g k| ≤ k * ∫ x, |g x| ∂μ := by
  have hj (j : ℕ) : |∫ x, χ j x * g x ∂μ| ≤ ∫ x, |g x| ∂μ :=
    (abs_integral_le_integral_abs).trans <| integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x ↦ abs_nonneg _) hg.abs
      (Filter.Eventually.of_forall fun x ↦ by
        simpa [abs_mul] using mul_le_mul_of_nonneg_right (hχ j x) (abs_nonneg (g x)))
  calc |chainMass μ χ g k| ≤ ∑ j ∈ Finset.range k, |∫ x, χ j x * g x ∂μ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range k, ∫ x, |g x| ∂μ := Finset.sum_le_sum fun j _ ↦ hj j
    _ = k * ∫ x, |g x| ∂μ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The collected masses are linear in `g`. -/
theorem chainMass_add_smul {h : X → ℝ} {k : ℕ}
    (hg : ∀ j < k, Integrable (fun x ↦ χ j x * g x) μ)
    (hh : ∀ j < k, Integrable (fun x ↦ χ j x * h x) μ) (a b : ℝ) :
    chainMass μ χ (fun x ↦ a * g x + b * h x) k =
      a * chainMass μ χ g k + b * chainMass μ χ h k := by
  simp only [chainMass, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj := Finset.mem_range.1 hj
  have e : (fun x ↦ χ j x * (a * g x + b * h x)) =
      fun x ↦ a * (χ j x * g x) + b * (χ j x * h x) := funext fun x ↦ by ring
  rw [e, integral_add ((hg j hj).const_mul a) ((hh j hj).const_mul b), integral_const_mul,
    integral_const_mul]

/-- The parts are linear in `g`. -/
theorem chainPart_add_smul {h : X → ℝ} {k : ℕ}
    (hg : ∀ j < k + 1, Integrable (fun x ↦ χ j x * g x) μ)
    (hh : ∀ j < k + 1, Integrable (fun x ↦ χ j x * h x) μ) (a b : ℝ) (x : X) :
    chainPart μ χ θ (fun x ↦ a * g x + b * h x) k x =
      a * chainPart μ χ θ g k x + b * chainPart μ χ θ h k x := by
  simp only [chainPart, chainMass_add_smul hg hh,
    chainMass_add_smul (fun j hj ↦ hg j (Nat.lt_succ_of_lt hj))
      (fun j hj ↦ hh j (Nat.lt_succ_of_lt hj))]
  ring

end MeasureTheory
