/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.DistributionalPoisson
import PDE.Spaces.Sobolev.Calculus.Differentiation.SecondDerivatives

/-!
# One-dimensional `H²` regularity for the Poisson equation

Let `Ω ⊆ ℝ¹` be open. A weak solution `u ∈ H¹₀(Ω)` of `-u'' = f` with `f ∈ L²(Ω)` has an `H²`
representative with the same first derivative and with `u'' = -f` almost everywhere
(`exists_oneDimensional_h2_of_weak_poisson_solution`). The proof assembles compatible first- and
second-order weak derivatives into the library's `W^{2,2}` space and reads the weak Poisson identity

`∫ u' φ' = ∫ f φ`

as the statement that `u'` has weak derivative `-f`.

This is the one-dimensional case, for `L = -d²/dx²`, of the `H²`-regularity theorems of Evans's
§6.3.1, Theorem 1, and §6.3.2, Theorem 4. The set `Ω` need not be bounded or have a regular
boundary, and no difference quotients are used. The multidimensional interior theorems are in
`PDE.Elliptic.Regularity.Interior.H2Compactness`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, Theorem 1 (Interior H²-regularity), p. 327; §6.3.2,
  Theorem 4 (Boundary H²-regularity), (38)-(42), p. 334.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

open scoped Sobolev

noncomputable section
namespace SobolevSpace.GraphSpace
open MeasureTheory Set Function
open scoped ENNReal

variable {Ω : Set (ℝ^1)}

/-- A one-dimensional `H¹₀` weak Poisson solution with `L²` forcing has an
`H²` representative whose second weak derivative equals `-f` almost
everywhere.

This is the one-dimensional case of `H²` regularity for the Laplacian; unlike the
multidimensional theorems, it needs no difference quotients or boundary charts. -/
theorem exists_oneDimensional_h2_of_weak_poisson_solution
    (f : DerivLp 1 2 Ω)
    (u : H¹₀(Ω))
    (hu : IsWeakPoissonSolution (n := 1) (Ω := Ω) f u) :
    ∃ W : W^{2,2}(Ω),
      baseRepresentative W =ᵐ[domainMeasure 1 Ω]
        (fun x ↦
          ⇑((u.1 : WkpAmbientOn 1 1 2 Ω)
            (baseIndex 1 1) : DerivLp 1 2 Ω) x) ∧
      (⇑((W : WkpAmbientOn 1 2 2 Ω)
          (firstDerivIndex 1 2 (by norm_num) (0 : Fin 1)) :
            DerivLp 1 2 Ω)
        =ᵐ[domainMeasure 1 Ω]
          ⇑((u.1 : WkpAmbientOn 1 1 2 Ω)
            (singleDerivIndex (n := 1) (0 : Fin 1)) : DerivLp 1 2 Ω)) ∧
      (⇑((W : WkpAmbientOn 1 2 2 Ω)
          (pairDerivIndex 1 (0 : Fin 1) (0 : Fin 1)) :
            DerivLp 1 2 Ω)
        =ᵐ[domainMeasure 1 Ω] fun x ↦ -(f x)) := by
  let f1 : ℝ^1 → ℝ :=
    (((u.1 : WkpAmbientOn 1 1 2 Ω)
      (singleDerivIndex (n := 1) (0 : Fin 1)) : DerivLp 1 2 Ω) : ℝ^1 → ℝ)
  have hnegMem : MeasureTheory.MemLp (fun x : ℝ^1 ↦ -(f x)) 2 (domainMeasure 1 Ω) := by
    exact (MeasureTheory.Lp.memLp f).neg
  have hsecond : HasWeakDerivativeOn (n := 1) Ω [(0 : Fin 1)] f1
      (fun x ↦ -(f x)) := by
    refine ⟨memLp_locallyIntegrableOn_domain (MeasureTheory.Lp.memLp
      ((u.1 : WkpAmbientOn 1 1 2 Ω)
        (singleDerivIndex (n := 1) (0 : Fin 1)))) (by norm_num),
      memLp_locallyIntegrableOn_domain hnegMem (by norm_num), ?_⟩
    intro φ hφ
    have hweak := hu.2 ⟨φ, hφ⟩
    simpa [f1, derivCoordCLM_apply,
      iteratedPartialDeriv, partialDeriv, Fin.sum_univ_one,
      MeasureTheory.integral_neg] using hweak
  obtain ⟨W, hbase, hfirst, hsecondCoord, _hnorm⟩ :=
    exists_H2_of_firstDerivatives_haveWeakDerivatives
      (U := u.1) (g := fun _ _ x ↦ -(f x)) (fun _ _ ↦ hnegMem) (fun i j ↦ by
        simpa [Subsingleton.elim i (0 : Fin 1), Subsingleton.elim j (0 : Fin 1)]
          using hsecond)
  refine ⟨W, hbase, hfirst 0, ?_⟩
  apply hsecondCoord
    (pairDerivIndex 1 (0 : Fin 1) (0 : Fin 1)) 0 0
  let a := pairDerivIndex 1 (0 : Fin 1) (0 : Fin 1)
  have hrep : a.toList = List.replicate a.toList.length (0 : Fin 1) :=
    List.eq_replicate_of_mem (fun b _ ↦ Subsingleton.elim b (0 : Fin 1))
  have hlen : a.toList.length = 2 := by
    rw [DerivIndex.toList_length]
    rfl
  simpa [hlen] using hrep

end SobolevSpace.GraphSpace
