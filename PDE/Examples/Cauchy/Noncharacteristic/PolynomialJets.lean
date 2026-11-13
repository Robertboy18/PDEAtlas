/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Cauchy.Noncharacteristic
public import PDE.Analysis.Calculus.MultiIndex.PartialDeriv
public import PDE.Examples.Cauchy.Noncharacteristic.Parabola
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# Quasilinear jet determination on a parabola

The equation `(1 + v²) ∂₀²v = 2 (1 + p²)`, with coefficient depending on the unknown, has
the polynomial solution `p = x₀² + x₁³`. By the jet theorem
`iteratedFDeriv_eq_on_of_cauchy_data` on the parabola `x₀ = x₁²`, every smooth solution
with the same normal data of orders `0` and `1` has the same jets as `p` at every point of
the parabola (`quadratic_cauchy_jets`).
-/

@[expose] public noncomputable section

open Set PDE.Analysis.MultiIndex
open scoped ContDiff

namespace PDE.Examples.Cauchy.Quasilinear

private def coefficient (k : ℕ) (hk : 0 < k) (α : Sym (Fin 2) k)
    (z : ℝ^2 × (∀ i : Fin k, Sym (Fin 2) (i : ℕ) → ℝ)) : ℝ :=
  if α = Sym.replicate k 0 then 1 + (z.2 ⟨0, hk⟩ 0) ^ 2 else 0

private theorem coefficient_contDiff (k : ℕ) (hk : 0 < k) (α : Sym (Fin 2) k) :
    ContDiff ℝ ∞ (coefficient k hk α) := by
  classical
  unfold coefficient
  split_ifs
  · let L : (∀ i : Fin k, Sym (Fin 2) (i : ℕ) → ℝ) →L[ℝ]
        (Sym (Fin 2) 0 → ℝ) := ContinuousLinearMap.proj (⟨0, hk⟩ : Fin k)
    have hs : ContDiff ℝ ∞ (fun z :
        ℝ^2 × (∀ i : Fin k, Sym (Fin 2) (i : ℕ) → ℝ) ↦ z.2 ⟨0, hk⟩) :=
      L.contDiff.comp contDiff_snd
    exact contDiff_const.add (((contDiff_apply ℝ (fun _ ↦ ℝ) 0).comp hs).pow 2)
  · exact contDiff_const

private theorem coefficient_sum (k : ℕ) (hk : 0 < k)
    (z : ℝ^2 × (∀ i : Fin k, Sym (Fin 2) (i : ℕ) → ℝ))
    (v : Sym (Fin 2) k → ℝ) :
    ∑ α, coefficient k hk α z * v α =
      (1 + (z.2 ⟨0, hk⟩ 0) ^ 2) * v (Sym.replicate k 0) := by
  classical
  simp [coefficient, ite_mul]

private theorem determine_polynomial (k : ℕ) (hk : 0 < k)
    (p : ℝ^2 → ℝ) (c : ℝ) (hp : ContDiff ℝ ∞ p)
    (hDp : ∀ x, ((partialDeriv (0 : Fin 2))^[k] p) x = c)
    {v : ℝ^2 → ℝ} (hv : ContDiff ℝ ∞ v)
    (hdata : ∀ j < k, ∀ x ∈ parabola,
      normalData j p (parabolaNormal x) x = normalData j v (parabolaNormal x) x)
    (hPv : ∀ x, (1 + (v x) ^ 2) * ((partialDeriv (0 : Fin 2))^[k] v) x =
      c * (1 + (p x) ^ 2)) :
    ∀ j, EqOn (iteratedFDeriv ℝ j p) (iteratedFDeriv ℝ j v) parabola := by
  classical
  have hvalue (f : ℝ^2 → ℝ) (x : ℝ^2) :
      coordinateJetLT k f x ⟨0, hk⟩ 0 = f x := rfl
  apply PDE.Cauchy.Quasilinear.iteratedFDeriv_eq_on_of_cauchy_data hk
    (coefficient k hk) (fun z ↦ c * (1 + (p z.1) ^ 2))
    isOpen_univ (subset_univ parabola)
    (fun α ↦ (coefficient_contDiff k hk α).contDiffOn)
    (contDiff_const.mul (contDiff_const.add ((hp.comp contDiff_fst).pow 2))).contDiffOn
    parabolaNormal
    (fun x _ ↦ parabolaNormal_ne_zero x) parabola_hasConormalParametrizations
    ?_ hp.contDiffOn hv.contDiffOn hdata ?_ ?_
  · intro x _ q
    rw [coefficient_sum, monomial_replicate, parabolaNormal_zero, one_pow, mul_one]
    positivity
  · intro x _
    rw [coefficient_sum]
    dsimp only
    rw [hvalue,
      coordinateDeriv_replicate 0 (hp.contDiffAt.of_le (by simp)), hDp]
    exact mul_comm _ _
  · intro x _
    rw [coefficient_sum]
    dsimp only
    rw [hvalue,
      coordinateDeriv_replicate 0 (hv.contDiffAt.of_le (by simp))]
    exact hPv x

/-- A polynomial with nonzero second and third coordinate derivatives. -/
def quadraticCauchySolution (x : ℝ^2) : ℝ := (x 0) ^ 2 + (x 1) ^ 3

/-- A smooth solution of `(1 + v²) ∂₀²v = 2 (1 + p²)`, `p = quadraticCauchySolution`, with
the normal data of `p` of orders `0` and `1` on the parabola, has the jets of `p` there. -/
theorem quadratic_cauchy_jets
    {v : ℝ^2 → ℝ} (hv : ContDiff ℝ ∞ v)
    (hdata : ∀ j < 2, ∀ x ∈ parabola,
      normalData j quadraticCauchySolution (parabolaNormal x) x =
        normalData j v (parabolaNormal x) x)
    (hPv : ∀ x, (1 + (v x) ^ 2) * (∂[0] (∂[0] v)) x =
      2 * (1 + (quadraticCauchySolution x) ^ 2)) :
    ∀ j, EqOn (iteratedFDeriv ℝ j quadraticCauchySolution)
      (iteratedFDeriv ℝ j v) parabola := by
  refine determine_polynomial 2 (by decide) quadraticCauchySolution 2
    (by cas) ?_ hv hdata ?_
  · intro x
    change (∂[0] (∂[0] quadraticCauchySolution)) x = 2
    have hD : ∂[0] quadraticCauchySolution = fun x ↦ 2 * x 0 := by
      funext x
      cas
    rw [hD]
    cas
  · simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using hPv

end PDE.Examples.Cauchy.Quasilinear
