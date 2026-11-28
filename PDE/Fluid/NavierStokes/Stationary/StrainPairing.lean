/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Stationary.TestFieldRepresentative
import PDE.Analysis.MeasureTheory.Lp.RealL2
import PDE.FDeriv.PartialDeriv.Transport
import PDE.Analysis.MeasureTheory.Lp.WeightedL2
import PDE.Spaces.Sobolev.Variational.Spaces.WholeSpaceL2Pairing
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# The strain of a divergence-free field against a tensor product

For a divergence-free field `f` in `H¹(ℝ³)³` with strain `Sf = (∇f + ∇ᵀf) / 2`, and vector fields
`g`, `h` with `|g| |h|` square integrable,

`|∫ (g ⊗ h) : Sf| ≤ (1/√3) ‖∇f‖₂ ‖|g| |h|‖₂`.

This is the estimate (A.2) of Hou, Wang and Yang. The constant comes from two facts: the strain
of a divergence-free field has trace zero, and its `L²` norm is `‖∇f‖₂ / √2`. The second holds in
every dimension; the pointwise inequality and (A.2) are stated in dimension three. In dimension
`n ≥ 2` the same argument gives `(n - 1) / n` in place of `2/3` and `√((n - 1) / (2 n))` in place
of `1/√3`, which is not stated.

## Main results

* `sq_sum_sum_mul_le_of_symm_of_trace_eq_zero` (all `a`, `b` in `ℝ³` and all symmetric matrices
  `S` with trace zero): `((a ⊗ b) : S)² ≤ (2/3) |a|² |b|² |S|²`; the form with norms is
  `abs_sum_sum_mul_le_of_symm_of_trace_eq_zero`.
* `sum_inner_gradientCLM_transpose_eq_zero` (all dimensions, all `u` in `H¹`, all
  divergence-free `v` in `H¹`): `∑ᵢⱼ ⟪∂ᵢuⱼ, ∂ⱼvᵢ⟫ = 0`. For `u = v = f`, with integrals of the
  chosen representatives, it is `sum_integral_gradientRepresentative_transpose_eq_zero`.
* `integral_sum_strain_sq` (all dimensions, all divergence-free `f` in `H¹`):
  `∫ |Sf|² = ½ ‖∇f‖₂²`. The integrand is integrable for every `f` in `H¹`
  (`integrable_sum_strain_sq`).
* `abs_integral_tensor_strain_le` (all divergence-free `f` in `H¹(ℝ³)³`, all `g`, `h` with
  `|g| |h|` in `L²`): the estimate (A.2).
* `integrable_tensor_strain` (all dimensions, all `f` in `H¹`, all measurable `g`, `h` with
  `|g| |h|` in `L²`): the integrand `(g ⊗ h) : Sf` is integrable.
* `ae_sum_gradientRepresentative_self_eq_zero`, `integral_sum_gradientRepresentative_sq` (all
  dimensions): the weak gradient of a divergence-free field has trace zero almost everywhere, and
  `∫ ∑ᵢⱼ (∂ⱼfᵢ)² = ‖∇f‖₂²` for every field.

## How it works

The strain of a divergence-free field is symmetric and has trace zero, so at each point the
pairing with `g ⊗ h` sees only the symmetric trace-free part `T` of `g ⊗ h`. For vectors of
`ℝ³`, `|T|² = ½ |g|² |h|² + (1/6) (g · h)² ≤ (2/3) |g|² |h|²`, and the Cauchy–Schwarz inequality
over the nine entries gives `|(g ⊗ h) : Sf| ≤ √(2/3) |g| |h| |Sf|` almost everywhere.

Expanding the square gives `‖Sf‖₂² = ½ ‖∇f‖₂² + ½ ∑ᵢⱼ ∫ ∂ᵢfⱼ ∂ⱼfᵢ`, and the last sum is zero. To
see it, take `u` in `H¹` and a smooth compactly supported divergence-free `φ`. One integration by
parts and the symmetry of the second derivatives of `φ` give
`∑ᵢⱼ ⟪∂ᵢuⱼ, ∂ⱼφᵢ⟫ = -∑ⱼ ∫ uⱼ ∂ⱼ(div φ) = 0` (`PDE.sum_partialDeriv_partialDeriv_eq_zero`). The
left side is continuous in `φ` for the `H¹` norm, and these `φ` are dense in the divergence-free
part of `H¹` (`mem_topologicalClosure_span_solenoidalTestFields`). The Cauchy–Schwarz inequality
in `L²` puts the two facts together, with the constant `√(2/3) · √(1/2) = 1/√3`.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Appendix A, Lemma 7 and (A.2).
  <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped RealInnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert ContDiff

namespace NavierStokes.Stationary

set_option linter.missingDocs true

variable {n : ℕ}

local notation "H" => PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))

/-! ### The pointwise inequality -/

/-- **The pointwise inequality, squared.** For `a`, `b` in `ℝ³` and a symmetric matrix `S` with
trace zero, `(∑ᵢⱼ aᵢ bⱼ Sᵢⱼ)² ≤ (2/3) |a|² |b|² ∑ᵢⱼ Sᵢⱼ²`. The pairing with `S` only sees the
symmetric trace-free part `T = (a ⊗ b + b ⊗ a) / 2 - (a · b) / 3 I` of `a ⊗ b`, and
`∑ᵢⱼ Tᵢⱼ² = ½ |a|² |b|² + (1/6) (a · b)²`. The Cauchy–Schwarz inequality is used over the nine
entries and for `a · b`. -/
theorem sq_sum_sum_mul_le_of_symm_of_trace_eq_zero (a b : Fin 3 → ℝ) (S : Fin 3 → Fin 3 → ℝ)
    (hS : ∀ i j, S i j = S j i) (htr : ∑ i, S i i = 0) :
    (∑ i, ∑ j, a i * b j * S i j) ^ 2 ≤
      2 / 3 * (∑ i, a i ^ 2) * (∑ j, b j ^ 2) * ∑ i, ∑ j, S i j ^ 2 := by
  -- `T` is the symmetric trace-free part of `a ⊗ b`.
  let T : Fin 3 → Fin 3 → ℝ := fun i j ↦
    (a i * b j + a j * b i) / 2 - if i = j then (a 0 * b 0 + a 1 * b 1 + a 2 * b 2) / 3 else 0
  have hT : ∀ i j, T i j = (a i * b j + a j * b i) / 2 -
      if i = j then (a 0 * b 0 + a 1 * b 1 + a 2 * b 2) / 3 else 0 := fun _ _ ↦ rfl
  have hpair : ∑ i, ∑ j, a i * b j * S i j = ∑ i, ∑ j, T i j * S i j := by
    have h01 := hS 0 1
    have h02 := hS 0 2
    have h12 := hS 1 2
    simp only [Fin.sum_univ_three, hT] at htr ⊢
    simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, sub_zero]
    linear_combination (a 0 * b 1 - a 1 * b 0) / 2 * h01 + (a 0 * b 2 - a 2 * b 0) / 2 * h02 +
      (a 1 * b 2 - a 2 * b 1) / 2 * h12 + (a 0 * b 0 + a 1 * b 1 + a 2 * b 2) / 3 * htr
  have hnorm : ∑ i, ∑ j, T i j ^ 2 =
      1 / 2 * (∑ i, a i ^ 2) * (∑ j, b j ^ 2) + 1 / 6 * (∑ k, a k * b k) ^ 2 := by
    simp only [Fin.sum_univ_three, hT]
    simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, sub_zero]
    ring
  have hCS : (∑ i, ∑ j, T i j * S i j) ^ 2 ≤ (∑ i, ∑ j, T i j ^ 2) * ∑ i, ∑ j, S i j ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3 × Fin 3))
      (fun p ↦ T p.1 p.2) (fun p ↦ S p.1 p.2)
    simp only [Fintype.sum_prod_type] at h
    exact h
  have hab : (∑ k, a k * b k) ^ 2 ≤ (∑ i, a i ^ 2) * ∑ j, b j ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have hS0 : 0 ≤ ∑ i, ∑ j, S i j ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg (S i j)
  calc (∑ i, ∑ j, a i * b j * S i j) ^ 2
      = (∑ i, ∑ j, T i j * S i j) ^ 2 := by rw [hpair]
    _ ≤ (∑ i, ∑ j, T i j ^ 2) * ∑ i, ∑ j, S i j ^ 2 := hCS
    _ = (1 / 2 * (∑ i, a i ^ 2) * (∑ j, b j ^ 2) + 1 / 6 * (∑ k, a k * b k) ^ 2) *
          ∑ i, ∑ j, S i j ^ 2 := by rw [hnorm]
    _ ≤ 2 / 3 * (∑ i, a i ^ 2) * (∑ j, b j ^ 2) * ∑ i, ∑ j, S i j ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hab) hS0]

/-- **The pointwise inequality.** For `a`, `b` in `ℝ³` and a symmetric matrix `S` with trace
zero, `|∑ᵢⱼ aᵢ bⱼ Sᵢⱼ| ≤ √(2/3) |a| |b| (∑ᵢⱼ Sᵢⱼ²)^{1/2}`, with the Euclidean norms of `a` and
`b`. -/
theorem abs_sum_sum_mul_le_of_symm_of_trace_eq_zero (a b : ℝ^3) (S : Fin 3 → Fin 3 → ℝ)
    (hS : ∀ i j, S i j = S j i) (htr : ∑ i, S i i = 0) :
    |∑ i, ∑ j, a i * b j * S i j| ≤ √(2 / 3) * (‖a‖ * ‖b‖ * √(∑ i, ∑ j, S i j ^ 2)) := by
  have hS0 : 0 ≤ ∑ i, ∑ j, S i j ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg (S i j)
  have key : (∑ i, ∑ j, a i * b j * S i j) ^ 2 ≤
      2 / 3 * (∑ i, a i ^ 2) * (∑ j, b j ^ 2) * ∑ i, ∑ j, S i j ^ 2 :=
    sq_sum_sum_mul_le_of_symm_of_trace_eq_zero (fun i ↦ a i) (fun j ↦ b j) S hS htr
  refine abs_le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.sqrt_nonneg _)))
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2 / 3),
    Real.sq_sqrt hS0, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  calc _ ≤ _ := key
    _ = _ := by ring

/-! ### The mixed derivatives of a divergence-free field -/

/-- **One integration by parts against a test field.** For `u` in `H¹(ℝⁿ)ⁿ` and a smooth
compactly supported field `φ`, the `L²` pairing of the weak derivative `∂ᵢuⱼ` with the weak
derivative `∂ⱼφᵢ` of the `H¹` class of `φ` is `-∫ uⱼ ∂ᵢ∂ⱼφᵢ`. -/
theorem inner_gradientCLM_testFieldH1 (u : H) {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (i j : Fin n) :
    ⟪gradientCLM u j i, gradientCLM (testFieldH1 φ hφ hc) i j⟫ =
      -∫ x, representative u x j *
        PDE.partialDeriv i (fun y ↦ PDE.partialDeriv j (fun z ↦ φ z i) y) x := by
  have hψ : ContDiff ℝ ∞ (fun y ↦ PDE.partialDeriv j (fun z ↦ φ z i) y) :=
    PDE.contDiff_top_partialDeriv (contDiff_component hφ i)
  have hψc : HasCompactSupport (fun y ↦ PDE.partialDeriv j (fun z ↦ φ z i) y) :=
    (hasCompactSupport_component hc i).partialDeriv j
  rw [integral_representative_mul_partialDeriv u j i hψ hψc, neg_neg]
  exact inner_eq_integral_mul_of_ae Filter.EventuallyEq.rfl
    (gradientRepresentative_testFieldH1_ae hφ hc i j)

/-- For `u` in `H¹(ℝⁿ)ⁿ` and a smooth compactly supported field `φ` with zero divergence,
`∑ᵢⱼ ⟪∂ᵢuⱼ, ∂ⱼφᵢ⟫ = 0`, where `φ` stands for its `H¹` class. After one integration by parts
the sum over `i` is `-∫ uⱼ ∂ⱼ(div φ)`. -/
theorem sum_inner_gradientCLM_transpose_testFieldH1 (u : H) {φ : ℝ^n → ℝ^n}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hdiv : ∀ x, PDE.divergence φ x = 0) :
    ∑ i, ∑ j, ⟪gradientCLM u j i, gradientCLM (testFieldH1 φ hφ hc) i j⟫ = 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  have hrep : MemLp (fun x ↦ representative u x j) 2 volume := by
    have h := Lp.memLp (massCLM u j)
    simp only [domainMeasure, Measure.restrict_univ] at h
    exact h
  have hint (i : Fin n) : Integrable (fun x ↦ representative u x j *
      PDE.partialDeriv i (fun y ↦ PDE.partialDeriv j (fun z ↦ φ z i) y) x) :=
    hrep.integrable_mul (q := 2)
      ((PDE.contDiff_top_partialDeriv (i := i) (PDE.contDiff_top_partialDeriv (i := j)
        (contDiff_component hφ i))).continuous.memLp_of_hasCompactSupport
        (((hasCompactSupport_component hc i).partialDeriv j).partialDeriv i))
  have hzero (x : ℝ^n) : ∑ i, representative u x j *
      PDE.partialDeriv i (fun y ↦ PDE.partialDeriv j (fun z ↦ φ z i) y) x = 0 := by
    rw [← Finset.mul_sum, PDE.sum_partialDeriv_partialDeriv_eq_zero hφ hdiv j x, mul_zero]
  rw [Finset.sum_congr rfl fun i _ ↦ inner_gradientCLM_testFieldH1 u hφ hc i j,
    Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ ↦ hint i, neg_eq_zero]
  calc ∫ x, ∑ i, representative u x j *
        PDE.partialDeriv i (fun y ↦ PDE.partialDeriv j (fun z ↦ φ z i) y) x
      = ∫ _x : ℝ^n, (0 : ℝ) := integral_congr_ae (Filter.Eventually.of_forall hzero)
    _ = 0 := integral_zero _ _

/-- **The transposed gradient pairing vanishes on divergence-free fields.** For every `u` in
`H¹(ℝⁿ)ⁿ` and every divergence-free `v` in `H¹(ℝⁿ)ⁿ`, `∑ᵢⱼ ⟪∂ᵢuⱼ, ∂ⱼvᵢ⟫ = 0` in `L²`. The left
side is a continuous linear functional of `v`. It vanishes on the smooth compactly supported
divergence-free fields, and these are dense in the divergence-free part of `H¹`. In dimension
zero the sums are empty. -/
theorem sum_inner_gradientCLM_transpose_eq_zero (u : H) {v : H} (hv : divergenceCLM v = 0) :
    ∑ i, ∑ j, ⟪gradientCLM u j i, gradientCLM v i j⟫ = 0 := by
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · exact Finset.sum_eq_zero fun i _ ↦ i.elim0
  -- `t` is the transposed weak gradient of `u`, and `L w = ⟪t, ∇w⟫`.
  let t : PiLp 2 (fun _ : Fin n ↦ PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 Set.univ)) :=
    WithLp.toLp 2 fun i ↦ WithLp.toLp 2 fun j ↦ gradientCLM u j i
  let L : H →L[ℝ] ℝ := (innerSL ℝ t).comp gradientCLM
  have hL (w : H) : L w = ⟪t, gradientCLM w⟫ := rfl
  have ht (w : H) : ⟪t, gradientCLM w⟫ = ∑ i, ∑ j, ⟪gradientCLM u j i, gradientCLM w i j⟫ :=
    (PiLp.inner_apply (𝕜 := ℝ) t (gradientCLM w)).trans
      (Finset.sum_congr rfl fun i _ ↦ PiLp.inner_apply (𝕜 := ℝ) (t i) (gradientCLM w i))
  have htest : ∀ w ∈ solenoidalTestFields n, L w = 0 := by
    rintro _ ⟨φ, hφ, hc, hdiv, rfl⟩
    exact (hL _).trans ((ht _).trans (sum_inner_gradientCLM_transpose_testFieldH1 u hφ hc hdiv))
  have hker : (Submodule.span ℝ (solenoidalTestFields n)).topologicalClosure ≤
      LinearMap.ker L.toLinearMap :=
    Submodule.topologicalClosure_minimal _
      (Submodule.span_le.mpr fun w hw ↦ LinearMap.mem_ker.mpr (htest w hw)) L.isClosed_ker
  have hLv : L v = 0 := hker (mem_topologicalClosure_span_solenoidalTestFields hn v hv)
  exact (ht v).symm.trans ((hL v).symm.trans hLv)

/-- **The mixed derivatives of a divergence-free field.** For a divergence-free `f` in
`H¹(ℝⁿ)ⁿ`, `∑ᵢⱼ ∫ ∂ᵢfⱼ ∂ⱼfᵢ = 0`, with the chosen representatives of the weak derivatives. -/
theorem sum_integral_gradientRepresentative_transpose_eq_zero {f : H}
    (hf : divergenceCLM f = 0) :
    ∑ i, ∑ j, ∫ x, gradientRepresentative f x j i * gradientRepresentative f x i j = 0 := by
  have h (i j : Fin n) : ⟪gradientCLM f j i, gradientCLM f i j⟫ =
      ∫ x, gradientRepresentative f x j i * gradientRepresentative f x i j :=
    inner_eq_integral_mul_of_ae Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl
  exact (Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ (h i j).symm).trans
    (sum_inner_gradientCLM_transpose_eq_zero f hf)

/-! ### The strain and its `L²` norm -/

/-- For a divergence-free field of `H¹(ℝⁿ)ⁿ`, the chosen representatives of the diagonal weak
derivatives `∂ᵢfᵢ` sum to zero almost everywhere: the weak gradient has trace zero. -/
theorem ae_sum_gradientRepresentative_self_eq_zero {f : H} (hf : divergenceCLM f = 0) :
    ∀ᵐ x ∂volume, ∑ i, gradientRepresentative f x i i = 0 := by
  let d : Fin n → DerivLp n 2 Set.univ := fun i ↦ wkpCoordinateCLM (singleDerivIndex n i) (f i)
  have hs := Lp.coeFn_fun_finsetSum Finset.univ d
  have h0 := Lp.coeFn_zero ℝ 2 (domainMeasure n Set.univ)
  have hsum : ∑ i, d i = 0 := by
    rw [← hf, divergenceCLM_apply]
  rw [hsum] at hs
  simp only [domainMeasure, Measure.restrict_univ] at hs h0
  filter_upwards [hs.symm.trans h0] with x hx
  simpa [d, gradientRepresentative, gradientCLM_apply] using hx

/-- The sum of the squares of the chosen weak derivatives of a field of `H¹(ℝⁿ)ⁿ` integrates to
the square of the norm of its gradient: `∫ ∑ᵢⱼ (∂ⱼfᵢ)² = ‖∇f‖₂²`. -/
theorem integral_sum_gradientRepresentative_sq (f : H) :
    ∫ x, ∑ i, ∑ j, gradientRepresentative f x i j ^ 2 = ‖gradientCLM f‖ ^ 2 := by
  have hint (i j : Fin n) : Integrable (fun x ↦ gradientRepresentative f x i j ^ 2) :=
    (memLp_gradientRepresentative f i j).integrable_sq
  have hcomp (i j : Fin n) :
      ∫ x, gradientRepresentative f x i j ^ 2 = ‖gradientCLM f i j‖ ^ 2 := by
    rw [Lp.norm_sq_eq_integral_sq]
    simp only [gradientRepresentative, domainMeasure, Measure.restrict_univ]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j,
    PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum _ fun j _ ↦ hint i j, PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl fun j _ ↦ hcomp i j

/-- The strain `Sf = (∇f + ∇ᵀf) / 2` of a field of `H¹(ℝⁿ)ⁿ`, with the chosen representatives of
the weak derivatives: `strain f x i j = (∂ⱼfᵢ(x) + ∂ᵢfⱼ(x)) / 2`. -/
def strain (f : H) (x : ℝ^n) (i j : Fin n) : ℝ :=
  (gradientRepresentative f x i j + gradientRepresentative f x j i) / 2

/-- The strain is symmetric. -/
theorem strain_comm (f : H) (x : ℝ^n) (i j : Fin n) : strain f x i j = strain f x j i := by
  unfold strain
  ring

/-- The diagonal of the strain is the diagonal of the weak gradient. -/
theorem strain_self (f : H) (x : ℝ^n) (i : Fin n) :
    strain f x i i = gradientRepresentative f x i i := by
  unfold strain
  ring

/-- The strain of a divergence-free field of `H¹(ℝⁿ)ⁿ` has trace zero almost everywhere. -/
theorem ae_sum_strain_self_eq_zero {f : H} (hf : divergenceCLM f = 0) :
    ∀ᵐ x ∂volume, ∑ i, strain f x i i = 0 := by
  filter_upwards [ae_sum_gradientRepresentative_self_eq_zero hf] with x hx
  exact (Finset.sum_congr rfl fun i _ ↦ strain_self f x i).trans hx

/-- Each entry of the strain of a field of `H¹(ℝⁿ)ⁿ` is square integrable. -/
theorem memLp_strain (f : H) (i j : Fin n) : MemLp (fun x ↦ strain f x i j) 2 volume := by
  have h := ((memLp_gradientRepresentative f i j).add
    (memLp_gradientRepresentative f j i)).const_mul (1 / 2 : ℝ)
  refine h.ae_eq (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [Pi.add_apply, strain]
  ring

/-- The pointwise squared Frobenius norm `∑ᵢⱼ Sᵢⱼ²` of the strain of a field of `H¹(ℝⁿ)ⁿ` is
integrable. -/
theorem integrable_sum_strain_sq (f : H) :
    Integrable (fun x ↦ ∑ i, ∑ j, strain f x i j ^ 2) :=
  integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    (memLp_strain f i j).integrable_sq

/-- Expanding the square: at every point,
`∑ᵢⱼ Sᵢⱼ² = ½ ∑ᵢⱼ (∂ⱼfᵢ)² + ½ ∑ᵢⱼ ∂ᵢfⱼ ∂ⱼfᵢ` for the strain `S` of `f`. -/
theorem sum_sum_strain_sq (f : H) (x : ℝ^n) :
    ∑ i, ∑ j, strain f x i j ^ 2 =
      1 / 2 * ∑ i, ∑ j, gradientRepresentative f x i j ^ 2 +
        1 / 2 * ∑ i, ∑ j, gradientRepresentative f x j i * gradientRepresentative f x i j := by
  have hterm (i j : Fin n) : strain f x i j ^ 2 =
      1 / 4 * gradientRepresentative f x i j ^ 2 + 1 / 4 * gradientRepresentative f x j i ^ 2 +
        1 / 2 * (gradientRepresentative f x j i * gradientRepresentative f x i j) := by
    unfold strain
    ring
  have hswap : ∑ i, ∑ j, gradientRepresentative f x j i ^ 2 =
      ∑ i, ∑ j, gradientRepresentative f x i j ^ 2 := Finset.sum_comm
  calc ∑ i, ∑ j, strain f x i j ^ 2
      = ∑ i, ∑ j, (1 / 4 * gradientRepresentative f x i j ^ 2 +
          1 / 4 * gradientRepresentative f x j i ^ 2 +
          1 / 2 * (gradientRepresentative f x j i * gradientRepresentative f x i j)) :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ hterm i j
    _ = 1 / 4 * ∑ i, ∑ j, gradientRepresentative f x i j ^ 2 +
          1 / 4 * ∑ i, ∑ j, gradientRepresentative f x j i ^ 2 +
          1 / 2 * ∑ i, ∑ j, gradientRepresentative f x j i * gradientRepresentative f x i j := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = 1 / 2 * ∑ i, ∑ j, gradientRepresentative f x i j ^ 2 +
          1 / 2 * ∑ i, ∑ j, gradientRepresentative f x j i * gradientRepresentative f x i j := by
        rw [hswap]
        ring

/-- **The `L²` norm of the strain.** For a divergence-free `f` in `H¹(ℝⁿ)ⁿ`,
`∫ ∑ᵢⱼ Sᵢⱼ² = ½ ‖∇f‖₂²`, where `S` is the strain of `f`. The square expands into the squares of
the weak derivatives and the mixed products, and the mixed products integrate to zero. -/
theorem integral_sum_strain_sq {f : H} (hf : divergenceCLM f = 0) :
    ∫ x, ∑ i, ∑ j, strain f x i j ^ 2 = 1 / 2 * ‖gradientCLM f‖ ^ 2 := by
  have hmul (i j : Fin n) : Integrable
      (fun x ↦ gradientRepresentative f x j i * gradientRepresentative f x i j) :=
    (memLp_gradientRepresentative f j i).integrable_mul (memLp_gradientRepresentative f i j)
  have hA : Integrable (fun x ↦ ∑ i, ∑ j, gradientRepresentative f x i j ^ 2) :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      (memLp_gradientRepresentative f i j).integrable_sq
  have hB : Integrable (fun x ↦ ∑ i, ∑ j,
      gradientRepresentative f x j i * gradientRepresentative f x i j) :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hmul i j
  have hBzero : ∫ x, ∑ i, ∑ j,
      gradientRepresentative f x j i * gradientRepresentative f x i j = 0 :=
    calc ∫ x, ∑ i, ∑ j, gradientRepresentative f x j i * gradientRepresentative f x i j
        = ∑ i, ∫ x, ∑ j, gradientRepresentative f x j i * gradientRepresentative f x i j :=
          integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hmul i j
      _ = ∑ i, ∑ j, ∫ x, gradientRepresentative f x j i * gradientRepresentative f x i j :=
          Finset.sum_congr rfl fun i _ ↦ integral_finsetSum _ fun j _ ↦ hmul i j
      _ = 0 := sum_integral_gradientRepresentative_transpose_eq_zero hf
  calc ∫ x, ∑ i, ∑ j, strain f x i j ^ 2
      = ∫ x, (1 / 2 * ∑ i, ∑ j, gradientRepresentative f x i j ^ 2 +
          1 / 2 * ∑ i, ∑ j, gradientRepresentative f x j i * gradientRepresentative f x i j) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x ↦ sum_sum_strain_sq f x)
    _ = 1 / 2 * (∫ x, ∑ i, ∑ j, gradientRepresentative f x i j ^ 2) +
          1 / 2 * ∫ x, ∑ i, ∑ j,
            gradientRepresentative f x j i * gradientRepresentative f x i j := by
        rw [integral_add (hA.const_mul _) (hB.const_mul _), integral_const_mul,
          integral_const_mul]
    _ = 1 / 2 * ‖gradientCLM f‖ ^ 2 := by
        rw [integral_sum_gradientRepresentative_sq, hBzero, mul_zero, add_zero]

/-- The pointwise Frobenius norm `(∑ᵢⱼ Sᵢⱼ²)^{1/2}` of the strain of a field of `H¹(ℝⁿ)ⁿ` is
square integrable, and the square of its `L²` norm is `∫ ∑ᵢⱼ Sᵢⱼ²`. -/
theorem memLp_sqrt_sum_strain_sq (f : H) :
    MemLp (fun x ↦ √(∑ i, ∑ j, strain f x i j ^ 2)) 2 volume ∧
      (eLpNorm (fun x ↦ √(∑ i, ∑ j, strain f x i j ^ 2)) 2 volume).toReal ^ 2 =
        ∫ x, ∑ i, ∑ j, strain f x i j ^ 2 := by
  have hint := integrable_sum_strain_sq f
  have hsq (x : ℝ^n) : √(∑ i, ∑ j, strain f x i j ^ 2) ^ 2 = ∑ i, ∑ j, strain f x i j ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _)
  have hmem : MemLp (fun x ↦ √(∑ i, ∑ j, strain f x i j ^ 2)) 2 volume := by
    refine (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hint.aestronglyMeasurable)).mpr ?_
    simpa only [hsq] using hint
  exact ⟨hmem, (integral_sq_eq_eLpNorm_toReal_sq hmem).symm.trans
    (integral_congr_ae (Filter.Eventually.of_forall hsq))⟩

/-! ### The estimate (A.2) -/

/-- **The pointwise form of (A.2).** For a divergence-free `f` in `H¹(ℝ³)³` and vector fields
`g`, `h`, almost everywhere `|(g ⊗ h) : Sf| ≤ √(2/3) |g| |h| |Sf|`, where `Sf` is the strain of
`f` and `|Sf|` its Frobenius norm. -/
theorem ae_abs_tensor_strain_le {f : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))}
    (hf : divergenceCLM f = 0) (g h : ℝ^3 → ℝ^3) :
    ∀ᵐ x ∂volume, |∑ i, ∑ j, g x i * h x j * strain f x i j| ≤
      √(2 / 3) * (‖g x‖ * ‖h x‖ * √(∑ i, ∑ j, strain f x i j ^ 2)) := by
  filter_upwards [ae_sum_strain_self_eq_zero hf] with x hx
  exact abs_sum_sum_mul_le_of_symm_of_trace_eq_zero (g x) (h x) (strain f x)
    (strain_comm f x) hx

/-- For measurable vector fields `g`, `h` on `ℝⁿ` with `|g| |h|` in `L²` and any `f` in
`H¹(ℝⁿ)ⁿ`, the function `(g ⊗ h) : Sf = ∑ᵢⱼ gᵢ hⱼ Sᵢⱼ` is integrable. Each product `gᵢ hⱼ` is
in `L²` because `|gᵢ hⱼ| ≤ |g| |h|`, and each entry of the strain is in `L²`. -/
theorem integrable_tensor_strain (f : H) {g h : ℝ^n → ℝ^n}
    (hg : AEStronglyMeasurable g volume) (hh : AEStronglyMeasurable h volume)
    (hgh : MemLp (fun x ↦ ‖g x‖ * ‖h x‖) 2 volume) :
    Integrable (fun x ↦ ∑ i, ∑ j, g x i * h x j * strain f x i j) := by
  refine integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ ?_
  have hgi : AEStronglyMeasurable (fun x ↦ g x i) volume :=
    (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hg
  have hhj : AEStronglyMeasurable (fun x ↦ h x j) volume :=
    (EuclideanSpace.proj j : ℝ^n →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hh
  have hij : MemLp (fun x ↦ g x i * h x j) 2 volume := by
    refine hgh.of_le (hgi.mul hhj) (Filter.Eventually.of_forall fun x ↦ ?_)
    have hP : 0 ≤ ‖g x‖ * ‖h x‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [norm_mul, Real.norm_of_nonneg hP]
    exact mul_le_mul (PiLp.norm_apply_le (g x) i) (PiLp.norm_apply_le (h x) j)
      (norm_nonneg _) (norm_nonneg _)
  exact hij.integrable_mul (memLp_strain f i j)

/-- **The strain estimate (A.2)** (Hou–Wang–Yang, Lemma 7). For a divergence-free `f` in
`H¹(ℝ³)³` and vector fields `g`, `h` with `|g| |h|` in `L²`,

`|∫ (g ⊗ h) : Sf| ≤ (1/√3) ‖∇f‖₂ ‖|g| |h|‖₂`,

where `Sf` is the strain of `f` and `(g ⊗ h) : Sf = ∑ᵢⱼ gᵢ hⱼ Sᵢⱼ`. The pointwise inequality
`|(g ⊗ h) : Sf| ≤ √(2/3) |g| |h| |Sf|`, the Cauchy–Schwarz inequality in `L²` and
`‖Sf‖₂² = ½ ‖∇f‖₂²` give the constant `√(2/3) · √(1/2) = 1/√3`. No measurability of `g` or `h`
is needed for the bound; for measurable fields the integrand is integrable
(`integrable_tensor_strain`). -/
theorem abs_integral_tensor_strain_le {f : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))}
    (hf : divergenceCLM f = 0) {g h : ℝ^3 → ℝ^3}
    (hgh : MemLp (fun x ↦ ‖g x‖ * ‖h x‖) 2 volume) :
    |∫ x, ∑ i, ∑ j, g x i * h x j * strain f x i j| ≤
      1 / √3 * ‖gradientCLM f‖ * (eLpNorm (fun x ↦ ‖g x‖ * ‖h x‖) 2 volume).toReal := by
  obtain ⟨hS, hS2⟩ := memLp_sqrt_sum_strain_sq f
  have hPS : Integrable (fun x ↦ ‖g x‖ * ‖h x‖ * √(∑ i, ∑ j, strain f x i j ^ 2)) :=
    hgh.integrable_mul hS
  -- The Cauchy–Schwarz inequality in `L²`.
  have hCS : |∫ x, ‖g x‖ * ‖h x‖ * √(∑ i, ∑ j, strain f x i j ^ 2)| ≤
      (eLpNorm (fun x ↦ ‖g x‖ * ‖h x‖) 2 volume).toReal *
        (eLpNorm (fun x ↦ √(∑ i, ∑ j, strain f x i j ^ 2)) 2 volume).toReal := by
    simpa only [toReal_eLpNorm] using abs_integral_mul_le_lpNorm_two_mul_lpNorm_two hgh hS
  -- `√(2/3) ‖Sf‖₂ = ‖∇f‖₂ / √3`, from `‖Sf‖₂² = ½ ‖∇f‖₂²`.
  have h0 : 0 ≤ √(2 / 3) *
      (eLpNorm (fun x ↦ √(∑ i, ∑ j, strain f x i j ^ 2)) 2 volume).toReal :=
    mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg
  have h1 : 0 ≤ 1 / √3 * ‖gradientCLM f‖ :=
    mul_nonneg (one_div_nonneg.mpr (Real.sqrt_nonneg _)) (norm_nonneg _)
  have hnorm : √(2 / 3) *
      (eLpNorm (fun x ↦ √(∑ i, ∑ j, strain f x i j ^ 2)) 2 volume).toReal ≤
        1 / √3 * ‖gradientCLM f‖ := by
    refine (pow_le_pow_iff_left₀ h0 h1 two_ne_zero).mp (le_of_eq ?_)
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2 / 3), hS2,
      integral_sum_strain_sq hf, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  calc |∫ x, ∑ i, ∑ j, g x i * h x j * strain f x i j|
      ≤ ∫ x, |∑ i, ∑ j, g x i * h x j * strain f x i j| := abs_integral_le_integral_abs
    _ ≤ ∫ x, √(2 / 3) * (‖g x‖ * ‖h x‖ * √(∑ i, ∑ j, strain f x i j ^ 2)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x ↦ abs_nonneg _)
          (hPS.const_mul _) (ae_abs_tensor_strain_le hf g h)
    _ = √(2 / 3) * ∫ x, ‖g x‖ * ‖h x‖ * √(∑ i, ∑ j, strain f x i j ^ 2) :=
        integral_const_mul _ _
    _ ≤ √(2 / 3) * ((eLpNorm (fun x ↦ ‖g x‖ * ‖h x‖) 2 volume).toReal *
          (eLpNorm (fun x ↦ √(∑ i, ∑ j, strain f x i j ^ 2)) 2 volume).toReal) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans hCS) (Real.sqrt_nonneg _)
    _ = (eLpNorm (fun x ↦ ‖g x‖ * ‖h x‖) 2 volume).toReal * (√(2 / 3) *
          (eLpNorm (fun x ↦ √(∑ i, ∑ j, strain f x i j ^ 2)) 2 volume).toReal) := by ring
    _ ≤ (eLpNorm (fun x ↦ ‖g x‖ * ‖h x‖) 2 volume).toReal * (1 / √3 * ‖gradientCLM f‖) :=
        mul_le_mul_of_nonneg_left hnorm ENNReal.toReal_nonneg
    _ = 1 / √3 * ‖gradientCLM f‖ * (eLpNorm (fun x ↦ ‖g x‖ * ‖h x‖) 2 volume).toReal := by
        ring

end NavierStokes.Stationary
