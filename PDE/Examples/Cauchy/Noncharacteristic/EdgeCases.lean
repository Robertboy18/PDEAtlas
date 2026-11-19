/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Cauchy.Noncharacteristic
public import PDE.Analysis.Calculus.MultiIndex.PartialDeriv
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# A one-point Cauchy set in one dimension

In one dimension the initial hypersurface can be the point `0`. The jet theorem
`iteratedFDeriv_eq_on_of_cauchy_data_of_symbol_at_jet` shows that `v v' = 0`, `v 0 = 1`
fixes every derivative of `v` at `0`, although the symbol vanishes at jets with value zero.
-/

@[expose] public noncomputable section

open Set PDE.Analysis PDE.Analysis.MultiIndex
open scoped ContDiff

namespace PDE.Examples.Cauchy.Quasilinear

private def lineNormal : ℝ^1 := EuclideanSpace.single 0 1

private theorem point_hasConormalParametrizations :
    HasConormalParametrizations (ℝ^0) ({0} : Set (ℝ^1))
      (fun _ ↦ (innerSL ℝ lineNormal).toLinearMap) := by
  intro x hx
  obtain rfl : x = 0 := mem_singleton_iff.mp hx
  refine ⟨fun _ ↦ 0, 0, 0, rfl, hasFDerivAt_const _ _, ?_, ?_⟩
  · ext w
    constructor
    · rintro ⟨z, rfl⟩
      simp
    · intro hw
      have hw0 : w 0 = 0 := by
        simpa [lineNormal, PiLp.inner_apply, Fin.sum_univ_one] using hw
      refine ⟨0, ?_⟩
      ext i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact hw0.symm
  · exact Filter.Eventually.of_forall fun _ ↦ mem_singleton 0

/-- A smooth solution of `v v′ = 0` with `v 0 = 1` has the jet of the constant `1` at `0`.
The symbol `v` vanishes at jets with value zero but not at this one. -/
theorem one_dimensional_value_dependent_cauchy_jets
    {v : ℝ^1 → ℝ} (hv : ContDiff ℝ ∞ v) (hv0 : v 0 = 1)
    (hPv : ∀ x, v x * (∂[0] v) x = 0) :
    ∀ j, iteratedFDeriv ℝ j (fun _ : ℝ^1 ↦ (1 : ℝ)) 0 =
      iteratedFDeriv ℝ j v 0 := by
  classical
  let a (_α : Sym (Fin 1) 1)
      (z : ℝ^1 × (∀ i : Fin 1, Sym (Fin 1) (i : ℕ) → ℝ)) :=
    z.2 0 (Sym.replicate 0 0)
  have h := PDE.Cauchy.Quasilinear.iteratedFDeriv_eq_on_of_cauchy_data_of_symbol_at_jet
    (n := 1) (k := 1) (by decide) a (fun _ ↦ 0)
    isOpen_univ (subset_univ ({0} : Set (ℝ^1)))
    (fun _ ↦ (((ContinuousLinearMap.proj (Sym.replicate 0 (0 : Fin 1)) :
      (Sym (Fin 1) 0 → ℝ) →L[ℝ] ℝ).contDiff).comp
        (((ContinuousLinearMap.proj (0 : Fin 1) :
          (∀ i : Fin 1, Sym (Fin 1) (i : ℕ) → ℝ) →L[ℝ] (Sym (Fin 1) 0 → ℝ)).contDiff).comp
            contDiff_snd)).contDiffOn) contDiff_const.contDiffOn (fun _ ↦ lineNormal)
    (fun _ _ ↦ by
      intro h
      have := congrArg (fun x : ℝ^1 ↦ x 0) h
      simp [lineNormal] at this)
    point_hasConormalParametrizations (u := fun _ ↦ 1)
    (fun x _ ↦ by
      rw [Fintype.sum_subsingleton _ (Sym.replicate 1 (0 : Fin 1))]
      simp [a, coordinateJetLT, coordinateJetMap, jetLT, iteratedFDeriv_zero_apply,
        monomial_replicate, lineNormal])
    contDiff_const.contDiffOn hv.contDiffOn ?_ ?_ ?_
  · exact fun j ↦ h j (mem_singleton 0)
  · intro j hj x hx
    obtain rfl : j = 0 := by omega
    obtain rfl : x = 0 := mem_singleton_iff.mp hx
    simpa using hv0.symm
  · intro x _
    rw [Fintype.sum_subsingleton _ (Sym.replicate 1 (0 : Fin 1))]
    rw [coordinateDeriv_replicate 0 contDiffAt_const]
    change _ * (∂[0] (fun _ : ℝ^1 ↦ (1 : ℝ))) x = 0
    simp only [partialDeriv_const, mul_zero]
  · intro x _
    rw [Fintype.sum_subsingleton _ (Sym.replicate 1 (0 : Fin 1))]
    rw [coordinateDeriv_replicate 0 (hv.contDiffAt.of_le (by simp))]
    change iteratedFDeriv ℝ 0 v x (directions (Sym.replicate 0 (0 : Fin 1))) *
      (∂[0] v) x = 0
    simpa only [iteratedFDeriv_zero_apply] using hPv x

/-- The symbol of `v v′` vanishes at the zero jet, so it is not nonzero at every
lower jet. -/
theorem value_dependent_symbol_not_nonzero_at_every_jet :
    ¬ ∀ p : ∀ i : Fin 1, Sym (Fin 1) (i : ℕ) → ℝ,
      ∑ α : Sym (Fin 1) 1, p 0 (Sym.replicate 0 0) *
        monomial α (EuclideanSpace.single 0 (1 : ℝ)) ≠ 0 := by
  intro h
  simpa only [zero_mul, Finset.sum_const_zero, ne_eq, not_true_eq_false] using
    h (fun _ _ ↦ 0)

end PDE.Examples.Cauchy.Quasilinear
