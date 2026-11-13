/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.LinearAlgebra.GramFourthPower
public import PDE.Analysis.MeasureTheory.Lp.WeightedL2
public import Mathlib.MeasureTheory.Function.L2Space
import CAS.ExactTactic

/-!
# Weighted moments and paired Gram bounds

Normalizing moment functions as `nᵢ / √W` and an input function as `ω √W` puts
both in ordinary `L²`. Their inner products are the moments `∫ nᵢ ω`, and
the paired Gram entries are the signed integrals `∫ n_{σ(i)} nⱼ / W`.
Positivity is required almost everywhere; square-integrability is explicit,
including at singularities of the weight.

For finitely many pairs indexed by `ι × Bool`, a fourth-trace bound controls
the sum of products of moments by the weighted energy of the input. For
three pairs, a trace strictly below `16` supplies a single constant below
one, uniform over all inputs with finite weighted energy.
-/

@[expose] public section

namespace PDE.Analysis

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The real inner product of two `toLp` representatives is their ordinary integral pairing. -/
theorem inner_toLp_eq_integral_mul {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫ = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  simp only [hfx, hgx, RCLike.inner_apply, conj_trivial]
  ring

/-- The normalized `L²` hypotheses imply integrability of the unnormalized moment. -/
theorem integrable_mul_of_memLp_div_sqrt {n omega W : α → ℝ}
    (hW : ∀ᵐ x ∂μ, 0 < W x)
    (hn : MemLp (fun x ↦ n x / √(W x)) 2 μ)
    (homega : MemLp (fun x ↦ omega x * √(W x)) 2 μ) :
    Integrable (fun x ↦ n x * omega x) μ := by
  refine (hn.integrable_mul homega).congr ?_
  filter_upwards [hW] with x hx
  change n x / √(W x) * (omega x * √(W x)) = n x * omega x
  have hsqrt : √(W x) ≠ 0 := Real.sqrt_ne_zero'.mpr hx
  cas using hsqrt

/-- Cancellation of the weight identifies each `L²` pairing with its signed moment. -/
theorem inner_toLp_div_sqrt_mul_sqrt {n omega W : α → ℝ}
    (hW : ∀ᵐ x ∂μ, 0 < W x)
    (hn : MemLp (fun x ↦ n x / √(W x)) 2 μ)
    (homega : MemLp (fun x ↦ omega x * √(W x)) 2 μ) :
    ⟪hn.toLp (fun x ↦ n x / √(W x)),
      homega.toLp (fun x ↦ omega x * √(W x))⟫ = ∫ x, n x * omega x ∂μ := by
  rw [inner_toLp_eq_integral_mul]
  apply integral_congr_ae
  filter_upwards [hW] with x hx
  have hsqrt : √(W x) ≠ 0 := Real.sqrt_ne_zero'.mpr hx
  cas using hsqrt

/-- The squared norm of the weighted input function is its weighted energy. -/
theorem norm_toLp_mul_sqrt_sq {omega W : α → ℝ}
    (hW : ∀ᵐ x ∂μ, 0 ≤ W x)
    (homega : MemLp (fun x ↦ omega x * √(W x)) 2 μ) :
    ‖homega.toLp (fun x ↦ omega x * √(W x))‖ ^ 2 =
      ∫ x, omega x ^ 2 * W x ∂μ := by
  rw [norm_toLp_mul_sqrt_eq_sqrt_integral homega hW, Real.sq_sqrt]
  exact integral_nonneg_of_ae <| hW.mono fun x hx ↦ mul_nonneg (sq_nonneg _) hx

/-- Products of normalized moment vectors give integrable signed Gram densities. -/
theorem integrable_mul_div_of_memLp_div_sqrt {f g W : α → ℝ}
    (hW : ∀ᵐ x ∂μ, 0 < W x)
    (hf : MemLp (fun x ↦ f x / √(W x)) 2 μ)
    (hg : MemLp (fun x ↦ g x / √(W x)) 2 μ) :
    Integrable (fun x ↦ f x * g x / W x) μ := by
  refine (hf.integrable_mul hg).congr ?_
  filter_upwards [hW] with x hx
  change f x / √(W x) * (g x / √(W x)) = f x * g x / W x
  rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hx.le]

/-- The Gram pairing is a signed weighted integral, with no absolute values in its density. -/
theorem inner_toLp_div_sqrt_div_sqrt {f g W : α → ℝ}
    (hW : ∀ᵐ x ∂μ, 0 < W x)
    (hf : MemLp (fun x ↦ f x / √(W x)) 2 μ)
    (hg : MemLp (fun x ↦ g x / √(W x)) 2 μ) :
    ⟪hf.toLp (fun x ↦ f x / √(W x)), hg.toLp (fun x ↦ g x / √(W x))⟫ =
      ∫ x, f x * g x / W x ∂μ := by
  rw [inner_toLp_eq_integral_mul]
  apply integral_congr_ae
  filter_upwards [hW] with x hx
  rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hx.le]

/-- The signed weighted moment matrix, with rows permuted by the pairing.
It need not be symmetric, although the corresponding finite-rank correction is symmetric. -/
def pairedMomentMatrix (μ : Measure α) (W : α → ℝ) (n : ι → α → ℝ)
    (σ : ι → ι) : Matrix ι ι ℝ :=
  fun i j ↦ ∫ x, n (σ i) x * n j x / W x ∂μ

/-- The integral matrix is exactly the paired Gram matrix of the normalized `L²` vectors. -/
theorem pairedGram_toLp_div_sqrt {W : α → ℝ} {n : ι → α → ℝ} (σ : ι → ι)
    (hW : ∀ᵐ x ∂μ, 0 < W x)
    (hn : ∀ i, MemLp (fun x ↦ n i x / √(W x)) 2 μ) :
    pairedGram (fun i ↦ (hn i).toLp (fun x ↦ n i x / √(W x))) σ =
      pairedMomentMatrix μ W n σ := by
  ext i j
  exact inner_toLp_div_sqrt_div_sqrt hW (hn (σ i)) (hn j)

/-- Swap the two members of each moment pair. -/
def momentPairSwap (i : ι × Bool) : ι × Bool :=
  (i.1, !i.2)

/-- Swapping the members of each pair twice gives the original index. -/
theorem momentPairSwap_involutive : Function.Involutive (momentPairSwap (ι := ι)) := by
  rintro ⟨i, b⟩
  simp [momentPairSwap]

/-- The factor `1/2` cancels the two occurrences of each paired product. -/
theorem inner_pairedCorrection_eq_sum_moments [Fintype ι]
    {W omega : α → ℝ} {n : ι × Bool → α → ℝ}
    (hW : ∀ᵐ x ∂μ, 0 < W x)
    (hn : ∀ i, MemLp (fun x ↦ n i x / √(W x)) 2 μ)
    (homega : MemLp (fun x ↦ omega x * √(W x)) 2 μ) :
    ⟪pairedCorrection (fun i ↦ (hn i).toLp (fun x ↦ n i x / √(W x)))
        momentPairSwap (homega.toLp (fun x ↦ omega x * √(W x))),
      homega.toLp (fun x ↦ omega x * √(W x))⟫ =
        ∑ i, (∫ x, n (i, false) x * omega x ∂μ) *
          (∫ x, n (i, true) x * omega x ∂μ) := by
  rw [inner_pairedCorrection_self, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_bool, inner_toLp_div_sqrt_mul_sqrt hW]
  simp only [momentPairSwap, Bool.not_true, Bool.not_false]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- An integral fourth-trace certificate bounds the paired moment form.
All entries of the certificate are signed integrals of the given numerators. -/
theorem abs_sum_moment_products_le_of_trace_le [Fintype ι] [DecidableEq ι]
    {W omega : α → ℝ} {n : ι × Bool → α → ℝ} {C : ℝ}
    (hW : ∀ᵐ x ∂μ, 0 < W x)
    (hn : ∀ i, MemLp (fun x ↦ n i x / √(W x)) 2 μ)
    (hC : 0 ≤ C)
    (htrace : Matrix.trace (pairedMomentMatrix μ W n momentPairSwap ^ 4) ≤ 16 * C ^ 4)
    (homega : MemLp (fun x ↦ omega x * √(W x)) 2 μ) :
    |∑ i, (∫ x, n (i, false) x * omega x ∂μ) *
        (∫ x, n (i, true) x * omega x ∂μ)| ≤ C * ∫ x, omega x ^ 2 * W x ∂μ := by
  rw [← pairedGram_toLp_div_sqrt momentPairSwap hW hn] at htrace
  have h := abs_inner_pairedCorrection_le_of_trace_le
    (fun i ↦ (hn i).toLp (fun x ↦ n i x / √(W x))) momentPairSwap_involutive hC htrace
    (homega.toLp (fun x ↦ omega x * √(W x)))
  rwa [inner_pairedCorrection_eq_sum_moments hW hn homega,
    norm_toLp_mul_sqrt_sq (hW.mono fun _ hx ↦ hx.le) homega] at h

/-- A strict fourth-trace bound gives one constant below one for all weighted inputs.

The constant depends only on the six moment functions, the weight, and the measure.
It controls the sum of the three products of moments for every input with finite
weighted energy. -/
theorem exists_abs_three_moment_products_le_of_trace_lt_sixteen
    {W : α → ℝ} {n : Fin 3 × Bool → α → ℝ}
    (hW : ∀ᵐ x ∂μ, 0 < W x)
    (hn : ∀ i, MemLp (fun x ↦ n i x / √(W x)) 2 μ)
    (htrace : Matrix.trace (pairedMomentMatrix μ W n momentPairSwap ^ 4) < 16) :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧ ∀ omega : α → ℝ,
      MemLp (fun x ↦ omega x * √(W x)) 2 μ →
        |∑ i : Fin 3, (∫ x, n (i, false) x * omega x ∂μ) *
            (∫ x, n (i, true) x * omega x ∂μ)| ≤
          C * ∫ x, omega x ^ 2 * W x ∂μ := by
  let v : Fin 3 × Bool → Lp ℝ 2 μ :=
    fun i ↦ (hn i).toLp (fun x ↦ n i x / √(W x))
  let A := pairedCorrection v momentPairSwap
  have hgram : pairedGram v momentPairSwap = pairedMomentMatrix μ W n momentPairSwap :=
    pairedGram_toLp_div_sqrt momentPairSwap hW hn
  have hA : ‖A‖ < 1 :=
    norm_pairedCorrection_lt_one_of_trace_lt_sixteen v momentPairSwap_involutive
      (hgram ▸ htrace)
  refine ⟨‖A‖, norm_nonneg _, hA, ?_⟩
  intro omega homega
  let y : Lp ℝ 2 μ := homega.toLp (fun x ↦ omega x * √(W x))
  have hbound : |⟪A y, y⟫| ≤ ‖A‖ * ‖y‖ ^ 2 := by
    calc
      _ ≤ ‖A y‖ * ‖y‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖A‖ * ‖y‖) * ‖y‖ :=
        mul_le_mul_of_nonneg_right (A.le_opNorm y) (norm_nonneg _)
      _ = _ := by rw [pow_two, mul_assoc]
  simpa only [A, v, y, inner_pairedCorrection_eq_sum_moments hW hn homega,
    norm_toLp_mul_sqrt_sq (hW.mono fun _ hx ↦ hx.le) homega] using hbound

end

end PDE.Analysis
