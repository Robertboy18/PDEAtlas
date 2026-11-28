/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import PDE.Analysis.Evolution.Semigroup.Complex.Generator
public import PDE.Analysis.Fourier.Uniqueness

/-!
# The point spectral mapping theorem for semigroups

For a complex-linear semigroup `T` with generator `A` on a complex Banach space and a time
`t > 0`, the nonzero eigenvalues of `T(t)` are exactly the numbers `e^{μt}` with `μ` an
eigenvalue of `A`: `σ_p(T(t)) ∖ {0} = e^{t σ_p(A)}`. Eigenvalues of a semigroup operator are often
easier to find, through compactness of `T(t)` or of a difference of two semigroups, and this
theorem turns them into eigenvalues of the generator. For the whole spectrum only the
inclusion `e^{t σ(A)} ⊆ σ(T(t))` holds in general
(`IsComplexLinear.exp_mem_spectrum_of_mem_spectrum_generator`). The corresponding statement
for the residual spectrum is not proved here.

## Main results

* `IsComplexLinear.apply_eq_exp_smul_of_mem_graph_smul`: if `A x = μ x`, then
  `T(t) x = e^{μt} x` for every `t ≥ 0`.
* `IsComplexLinear.exists_mem_graph_smul_of_apply_eq_smul`: if `T(t) x = c x` with `t > 0`,
  `c ≠ 0` and `x ≠ 0`, then `A` has an eigenvalue `μ` with `e^{μt} = c`.
* `IsComplexLinear.exists_apply_eq_smul_iff`: the two together.

## How it works

If `A x = μ x`, the rescaled semigroup `e^{-μt} T(t)` has generator value `0` at `x`, so its
orbit of `x` is constant. Conversely, let `T(t) x = c x`. The numbers `ν` with `e^{νt} = c` are
`ν_n = (log c + 2πin)/t`, and the vector `y_n = ∫₀ᵗ e^{-ν_n s} T(s) x ds` is in the domain of `A`
with `(A - ν_n) y_n = e^{-ν_n t} T(t) x - x = 0`. The orbit `u(s) = e^{-ν₀ s} T(s) x` is
continuous with `u(t) = u(0) = x`, and `y_n` is its Fourier coefficient of index `-n`. If every
`y_n` vanished, `u` would vanish on `[0, t]` by uniqueness of Fourier coefficients
(`eq_zero_of_intervalIntegral_exp_smul_eq_zero`), and so would `x = u(0)`.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Graduate Texts in Mathematics 194, Springer, 2000, Chapter IV, Section 3 (the spectral mapping
  theorem for the point spectrum). <https://doi.org/10.1007/b97696>
-/

@[expose] public noncomputable section

open Set Real

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup.IsComplexLinear

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {T : StronglyContinuousSemigroup X} (hT : T.IsComplexLinear) {x : X}

include hT

/-- **Eigenvectors of the generator are eigenvectors of the semigroup**: if `A x = μ x`, then
`T(t) x = e^{μt} x`. The rescaled semigroup `e^{-μt} T(t)` has generator value `0` at `x`. -/
theorem apply_eq_exp_smul_of_mem_graph_smul {μ : ℂ} (h : (x, μ • x) ∈ hT.generator.graph)
    (t : NNReal) : T t x = Complex.exp (μ * ((t : ℝ) : ℂ)) • x := by
  have hS : (x, (0 : X)) ∈ (hT.isComplexLinear_rescale (-μ)).generator.graph := by
    rw [mem_graph_generator_iff, hasGeneratorAt_rescale_iff, ← mem_graph_generator_iff hT]
    simpa using h
  have h1 := (hT.isComplexLinear_rescale (-μ)).integral_apply_of_mem_graph t hS
  rw [_root_.map_zero, rescale_apply, _root_.smul_apply] at h1
  have h2 : Complex.exp (-μ * ((t : ℝ) : ℂ)) • T t x = x := sub_eq_zero.mp h1.symm
  calc T t x = Complex.exp (μ * ((t : ℝ) : ℂ)) • (Complex.exp (-μ * ((t : ℝ) : ℂ)) • T t x) := by
        rw [smul_smul, ← Complex.exp_add,
          show μ * ((t : ℝ) : ℂ) + -μ * ((t : ℝ) : ℂ) = 0 by ring, Complex.exp_zero, one_smul]
    _ = Complex.exp (μ * ((t : ℝ) : ℂ)) • x := by rw [h2]

/-- **The point spectral mapping theorem, from the semigroup to the generator.** If
`T(t) x = c x` with `t > 0`, `c ≠ 0` and `x ≠ 0`, then the generator `A` has an eigenvalue `μ`
with `e^{μt} = c`. The eigenvector is a Fourier coefficient `∫₀ᵗ e^{-μs} T(s) x ds` of the
periodic orbit `s ↦ e^{-νs} T(s) x`, `e^{νt} = c`; not all of these vanish, because `x ≠ 0`. -/
theorem exists_mem_graph_smul_of_apply_eq_smul {t : NNReal} (ht : 0 < t) {c : ℂ} (hc : c ≠ 0)
    (hx : T t x = c • x) (hx0 : x ≠ 0) :
    ∃ μ : ℂ, Complex.exp (μ * ((t : ℝ) : ℂ)) = c ∧
      ∃ y, y ≠ 0 ∧ (y, μ • y) ∈ hT.generator.graph := by
  have ht' : (0 : ℝ) < t := ht
  have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht'.ne'
  -- the exponents `ν n` with `e^{ν n t} = c`
  obtain ⟨ν, hν⟩ : ∃ ν : ℤ → ℂ,
      ∀ n, ν n = (Complex.log c + n * (2 * π * Complex.I)) / ((t : ℝ) : ℂ) := ⟨_, fun _ ↦ rfl⟩
  have hexp : ∀ n, Complex.exp (ν n * ((t : ℝ) : ℂ)) = c := fun n ↦ by
    rw [hν, div_mul_cancel₀ _ htc, Complex.exp_add, Complex.exp_log hc,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hper : ∀ n, hT.rescale (-ν n) t x = x := fun n ↦ by
    rw [rescale_apply, _root_.smul_apply, hx, smul_smul, ← hexp n, ← Complex.exp_add, neg_mul,
      neg_add_cancel, Complex.exp_zero, one_smul]
  -- the vectors `y n = ∫₀ᵗ e^{-ν n s} T(s) x ds` satisfy `A (y n) = ν n • y n`
  have hy : ∀ n, ((hT.isComplexLinear_rescale (-ν n)).integral t x,
      ν n • (hT.isComplexLinear_rescale (-ν n)).integral t x) ∈ hT.generator.graph := fun n ↦ by
    have h := (hT.isComplexLinear_rescale (-ν n)).integral_mem_graph t x
    rw [hper n, sub_self, mem_graph_generator_iff, hasGeneratorAt_rescale_iff,
      ← mem_graph_generator_iff hT] at h
    simpa using h
  by_contra hno
  have hzero : ∀ n, (hT.isComplexLinear_rescale (-ν n)).integral t x = 0 := fun n ↦
    by_contra fun hne ↦ hno ⟨ν n, hexp n, _, hne, hy n⟩
  -- the orbit `u(s) = e^{-ν 0 s} T(s) x` has period `t` and vanishing Fourier coefficients
  have hu0 : (hT.rescale (-ν 0)).realOrbit x 0 = (hT.rescale (-ν 0)).realOrbit x (t : ℝ) := by
    rw [realOrbit_zero, realOrbit_coe, hper 0]
  have hcoef : ∀ n : ℤ, ∫ s in (0 : ℝ)..(t : ℝ),
      Complex.exp (2 * π * Complex.I * n * s / (t : ℝ)) • (hT.rescale (-ν 0)).realOrbit x s =
        0 := fun n ↦ by
    have h := hzero (-n)
    rw [integral_apply] at h
    refine Eq.trans (intervalIntegral.integral_congr fun s hs ↦ ?_) h
    rw [uIcc_of_le ht'.le] at hs
    simp only [realOrbit, rescale_apply, _root_.smul_apply, smul_smul, Real.coe_toNNReal s hs.1]
    congr 1
    rw [← Complex.exp_add]
    congr 1
    rw [hν, hν]
    push_cast
    field_simp
    ring
  have hu := eq_zero_of_intervalIntegral_exp_smul_eq_zero ht'
    ((hT.rescale (-ν 0)).continuous_realOrbit x).continuousOn hu0 hcoef (s := 0)
    ⟨le_rfl, ht'.le⟩
  rw [realOrbit_zero] at hu
  exact hx0 hu

/-- **The point spectral mapping theorem**, `σ_p(T(t)) ∖ {0} = e^{t σ_p(A)}` for `t > 0`: a
nonzero number `c` is an eigenvalue of `T(t)` if and only if `c = e^{μt}` for an eigenvalue `μ`
of the generator. -/
theorem exists_apply_eq_smul_iff {t : NNReal} (ht : 0 < t) {c : ℂ} (hc : c ≠ 0) :
    (∃ x, x ≠ 0 ∧ T t x = c • x) ↔
      ∃ μ : ℂ, Complex.exp (μ * ((t : ℝ) : ℂ)) = c ∧
        ∃ y, y ≠ 0 ∧ (y, μ • y) ∈ hT.generator.graph :=
  ⟨fun ⟨_, hx0, hx⟩ ↦ hT.exists_mem_graph_smul_of_apply_eq_smul ht hc hx hx0,
    fun ⟨μ, hμ, y, hy0, hy⟩ ↦
      ⟨y, hy0, by rw [hT.apply_eq_exp_smul_of_mem_graph_smul hy t, hμ]⟩⟩

end PDE.Analysis.Evolution.StronglyContinuousSemigroup.IsComplexLinear
