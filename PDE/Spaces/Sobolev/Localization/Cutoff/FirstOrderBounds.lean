/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Localization.Cutoff.ZeroBoundary
public import PDE.Spaces.Sobolev.Calculus.Product.Operator

/-!
# First-order cutoff bounds

Multiplication by a smooth compactly supported cutoff `ψ` is a bounded operator on `H¹(Ω)`, with
norm controlled by the `W^{1,∞}` norm of `ψ`. This is the `L²` case of the Leibniz rule for weak
derivatives, `∂_i(ψ u) = (∂_i ψ) u + ψ ∂_i u` (Evans, PDE, §5.2.3, Theorem 1(iv), proves it for
`ψ ∈ C_c^∞(Ω)`; here the support of `ψ` may meet the boundary), read as an operator bound:
each coordinate of `ψ u` is a sum of products of a bounded function with a coordinate of `u`.

The proof does not redo the estimate. It restricts the global test function `ψ`
to `Ω` as an element of `W^{1,∞}(Ω)` and shows that the cutoff operator `cutoffCLM ψ` on `H¹(Ω)`
coincides with the general `W^{1,∞}` multiplier `w1TopMultiplierCLM`. The multiplier's
graph-norm and operator-norm estimates then transfer to the cutoff operator, to the interior
cutoff `H¹(Ω) → H¹₀(Ω)`, and to cutoff multiplication on `H¹₀(Ω)`.

## Main results

* `globalTestFunctionToW1TopOn`: the cutoff as a `W^{1,∞}(Ω)` coefficient, with
  `globalTestFunctionToW1TopOn_base` and `globalTestFunctionToW1TopOn_singleDeriv` identifying
  its rows.
* `cutoffCLM_eq_w1TopMultiplierCLM`: on an open domain the cutoff operator is the `W^{1,∞}`
  multiplier of that coefficient.
* `norm_cutoffCLM_apply_le`, `norm_cutoffCLM_le`: the estimates
  `‖ψ u‖_{H¹} ≤ C_n ‖ψ‖_{W^{1,∞}} ‖u‖_{H¹}` with `C_n = w1TopMultiplierNormBound n`.
* `norm_cutoffH1ToH10_le`, `norm_cutoffH10_le`: the same bounds for the interior cutoff into
  `H¹₀(Ω)` and for cutoff multiplication on `H¹₀(Ω)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.3, Theorem 1(iv), (7), pp. 261-262.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open TopologicalSpace
open scoped Distributions ENNReal Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory Set

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A global test function, restricted to `Ω` and viewed as a
`W^{1,∞}(Ω)` multiplier. -/
noncomputable def globalTestFunctionToW1TopOn
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    W^{1,∞}(Ω) :=
  globalTestFunctionToWkpOn
    (n := n) (k := 1) (p := ∞) (Ω := Ω) ψ

/-- The base coordinate of the `W^{1,∞}` test-function realization is the
standard `L∞` realization of the same test function. -/
theorem globalTestFunctionToW1TopOn_base
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ((globalTestFunctionToW1TopOn
        (n := n) (Ω := Ω) ψ : WkpAmbientOn n 1 ∞ Ω)
        (baseIndex n 1)) =
      testFunctionLpTop (n := n) (Ω := Ω) ψ := by
  apply MeasureTheory.Lp.ext
  filter_upwards
    [globalTestFunctionToWkpOn_coordinate_ae
      (n := n) (k := 1) (p := ∞) (Ω := Ω) ψ (baseIndex n 1),
    testFunctionLpTop_apply_ae (n := n) (Ω := Ω) ψ] with x hglobal hcoefficient
  have hglobal' :
      ((globalTestFunctionToW1TopOn
          (n := n) (Ω := Ω) ψ : WkpAmbientOn n 1 ∞ Ω)
          (baseIndex n 1) : ℝ^n → ℝ) x = ψ.toFun x := by
    simpa [globalTestFunctionToW1TopOn, baseIndex_toList, iteratedPartialDeriv]
      using hglobal
  exact hglobal'.trans hcoefficient.symm

/-- A first-derivative coordinate of the `W^{1,∞}` test-function realization
is the standard `L∞` realization of the corresponding partial derivative. -/
theorem globalTestFunctionToW1TopOn_singleDeriv
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (i : Fin n) :
    ((globalTestFunctionToW1TopOn
        (n := n) (Ω := Ω) ψ : WkpAmbientOn n 1 ∞ Ω)
        (singleDerivIndex n i)) =
      partialTestFunctionLpTop (n := n) (Ω := Ω) ψ i := by
  apply MeasureTheory.Lp.ext
  filter_upwards
    [globalTestFunctionToWkpOn_coordinate_ae
      (n := n) (k := 1) (p := ∞) (Ω := Ω) ψ
        (singleDerivIndex n i),
    partialTestFunctionLpTop_apply_ae
      (n := n) (Ω := Ω) ψ i] with x hglobal hcoefficient
  have hglobal' :
      ((globalTestFunctionToW1TopOn
          (n := n) (Ω := Ω) ψ : WkpAmbientOn n 1 ∞ Ω)
          (singleDerivIndex n i) : ℝ^n → ℝ) x =
        iteratedPartialDeriv (n := n) [i] ψ.toFun x := by
    simpa [globalTestFunctionToW1TopOn, singleDerivIndex_toList]
      using hglobal
  exact hglobal'.trans hcoefficient.symm

/-- Smooth cutoff multiplication on the ambient `H¹` derivative bundle is
the general `W^{1,∞}` multiplier associated with the cutoff. -/
theorem cutoffAmbient_eq_w1TopMultiplierAmbient
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    cutoffAmbient (n := n) (p := 2) (Ω := Ω) ψ =
      w1TopMultiplierAmbient (n := n) (Ω := Ω)
        (globalTestFunctionToW1TopOn (n := n) (Ω := Ω) ψ) := by
  ext U a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    rw [cutoffAmbient_apply, w1TopMultiplierAmbient_base]
    simp [cutoffLpAt, globalTestFunctionToW1TopOn_base]
  · subst a
    rw [cutoffAmbient_apply, w1TopMultiplierAmbient_singleDeriv]
    simp [cutoffLpAt, globalTestFunctionToW1TopOn_base,
      globalTestFunctionToW1TopOn_singleDeriv]

/-- On an open domain, smooth cutoff multiplication on `H¹(Ω)` is the
general bounded `W^{1,∞}` graph-space multiplier. -/
theorem cutoffCLM_eq_w1TopMultiplierCLM
    (hΩopen : IsOpen Ω) (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    cutoffCLM (n := n) (p := 2) (Ω := Ω) ψ =
      w1TopMultiplierCLM (n := n) (Ω := Ω) hΩopen
        (globalTestFunctionToW1TopOn (n := n) (Ω := Ω) ψ) := by
  apply ContinuousLinearMap.ext
  intro U
  apply Subtype.ext
  exact DFunLike.congr_fun
    (cutoffAmbient_eq_w1TopMultiplierAmbient
      (n := n) (Ω := Ω) ψ)
    (U : WkpAmbientOn n 1 2 Ω)

/-- Graph-norm estimate for multiplication by a smooth cutoff on `H¹(Ω)`. -/
theorem norm_cutoffCLM_apply_le
    (hΩopen : IsOpen Ω) (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (U : W^{1,2}(Ω)) :
    ‖cutoffCLM (n := n) (p := 2) (Ω := Ω) ψ U‖ ≤
      w1TopMultiplierNormBound n *
        ‖globalTestFunctionToW1TopOn (n := n) (Ω := Ω) ψ‖ * ‖U‖ := by
  rw [cutoffCLM_eq_w1TopMultiplierCLM
    (n := n) (Ω := Ω) hΩopen ψ]
  exact norm_w1TopMultiplierCLM_apply_le
    (n := n) (Ω := Ω) hΩopen
    (globalTestFunctionToW1TopOn (n := n) (Ω := Ω) ψ) U

/-- Operator-norm estimate for multiplication by a smooth cutoff on
`H¹(Ω)`. -/
theorem norm_cutoffCLM_le
    (hΩopen : IsOpen Ω) (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ‖cutoffCLM (n := n) (p := 2) (Ω := Ω) ψ‖ ≤
      w1TopMultiplierNormBound n *
        ‖globalTestFunctionToW1TopOn (n := n) (Ω := Ω) ψ‖ := by
  rw [cutoffCLM_eq_w1TopMultiplierCLM
    (n := n) (Ω := Ω) hΩopen ψ]
  exact norm_w1TopMultiplierCLM_le
    (n := n) (Ω := Ω) hΩopen
    (globalTestFunctionToW1TopOn (n := n) (Ω := Ω) ψ)

/-- Graph-norm estimate for an interior cutoff regarded as a map from
`H¹(Ω)` to `H¹₀(Ω)`. -/
theorem norm_cutoffH1ToH10_apply_le
    (hΩopen : IsOpen Ω) (ρ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hρΩ : tsupport ρ.toFun ⊆ Ω) (u : H¹(Ω)) :
    ‖cutoffH1ToH10 hΩopen ρ hρΩ u‖ ≤
      w1TopMultiplierNormBound n *
        ‖globalTestFunctionToW1TopOn (n := n) (Ω := Ω) ρ‖ * ‖u‖ := by
  change
    ‖((cutoffH1ToH10 hΩopen ρ hρΩ u :
        H¹₀(Ω)) : H¹(Ω))‖ ≤ _
  rw [cutoffH1ToH10_apply_coe]
  exact norm_cutoffCLM_apply_le
    (n := n) (Ω := Ω) hΩopen ρ u

/-- Operator-norm estimate for an interior cutoff from `H¹(Ω)` to
`H¹₀(Ω)`. -/
theorem norm_cutoffH1ToH10_le
    (hΩopen : IsOpen Ω) (ρ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hρΩ : tsupport ρ.toFun ⊆ Ω) :
    ‖cutoffH1ToH10 hΩopen ρ hρΩ‖ ≤
      w1TopMultiplierNormBound n *
        ‖globalTestFunctionToW1TopOn (n := n) (Ω := Ω) ρ‖ := by
  exact (cutoffH1ToH10 hΩopen ρ hρΩ).opNorm_le_bound
    (mul_nonneg w1TopMultiplierNormBound_nonneg
      (norm_nonneg
        (globalTestFunctionToW1TopOn (n := n) (Ω := Ω) ρ)))
    (fun u ↦ by
      simpa [mul_assoc] using
        norm_cutoffH1ToH10_apply_le
          (n := n) (Ω := Ω) hΩopen ρ hρΩ u)

/-- Graph-norm estimate for smooth cutoff multiplication on `H¹₀(Ω)`. -/
theorem norm_cutoffH10_apply_le
    (hΩopen : IsOpen Ω) (ρ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (u : H¹₀(Ω)) :
    ‖cutoffH10 hΩopen ρ u‖ ≤
      w1TopMultiplierNormBound n *
        ‖globalTestFunctionToW1TopOn (n := n) (Ω := Ω) ρ‖ * ‖u‖ := by
  change
    ‖((cutoffH10 hΩopen ρ u :
        H¹₀(Ω)) : H¹(Ω))‖ ≤
      w1TopMultiplierNormBound n *
        ‖globalTestFunctionToW1TopOn (n := n) (Ω := Ω) ρ‖ *
          ‖(u : H¹(Ω))‖
  rw [cutoffH10_apply_coe]
  exact norm_cutoffCLM_apply_le
    (n := n) (Ω := Ω) hΩopen ρ (u : H¹(Ω))

/-- Operator-norm estimate for smooth cutoff multiplication on `H¹₀(Ω)`. -/
theorem norm_cutoffH10_le
    (hΩopen : IsOpen Ω) (ρ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ‖cutoffH10 hΩopen ρ‖ ≤
      w1TopMultiplierNormBound n *
        ‖globalTestFunctionToW1TopOn (n := n) (Ω := Ω) ρ‖ := by
  exact (cutoffH10 hΩopen ρ).opNorm_le_bound
    (mul_nonneg w1TopMultiplierNormBound_nonneg
      (norm_nonneg
        (globalTestFunctionToW1TopOn (n := n) (Ω := Ω) ρ)))
    (fun u ↦ by
      simpa [mul_assoc] using
        norm_cutoffH10_apply_le
          (n := n) (Ω := Ω) hΩopen ρ u)

end SobolevSpace.GraphSpace
