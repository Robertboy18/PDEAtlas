/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Cauchy.Formal.Equation
public import PDE.Analytic.CauchyKovalevskaya.Formal.Recursion

/-!
# Formal time recursion for the scalar Cauchy equation

The coefficient filtration determines each new time coefficient from earlier
ones. The order-`k` time recursion
`PDE.Analytic.CauchyKovalevskaya.existsUnique_iterate_pderiv_eq_of_coeff_depend_lt`,
applied with a single unknown, gives the unique formal solution with zero lower
Cauchy data. Convergence is proved in `Formal/Convergence`. Compare step 3 of the proof
of the Cauchy–Kovalevskaya theorem in Evans, §4.6.3, Theorem 2, where the coefficients of the
first-order system are computed by induction on the order in `xₙ`, starting from (22).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3(b), proof of Theorem 2 (Cauchy–Kovalevskaya
  Theorem), step 3, (22)-(25), pp. 241-242.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MvPowerSeries
open scoped BigOperators

namespace PDE.Cauchy.Quasilinear.Analytic

variable {d k : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]

/-- A scalar quasilinear equation solved for its highest time derivative has a
unique formal solution with zero Cauchy data. -/
theorem existsUnique_formal_solution
    (hk : 0 < k)
    (a : {α : Sym (Fin (d + 1)) k // α ≠ Sym.replicate k 0} →
      MvPowerSeries ((Σ j : Fin k, Sym (Fin (d + 1)) (j : ℕ)) ⊕ Fin (d + 1)) R)
    (b : MvPowerSeries
      ((Σ j : Fin k, Sym (Fin (d + 1)) (j : ℕ)) ⊕ Fin (d + 1)) R) :
    ∃! u : MvPowerSeries (Fin (d + 1)) R,
      (∀ j < k, PowerSeries.coeff j (finSuccEquiv R d u) = 0) ∧
        (pderiv 0)^[k] u = formalRightHandSide a b u := by
  obtain ⟨u, hu, huniq⟩ :=
    PDE.Analytic.CauchyKovalevskaya.existsUnique_iterate_pderiv_eq_of_coeff_depend_lt
      (ι := Unit) k (fun u _ ↦ formalRightHandSide a b (u ())) fun _ u v hu hv h _ ↦
        coeff_formalRightHandSide_eq hk a b (hasSubst_formalArguments (hu ()))
          (hasSubst_formalArguments (hv ())) (h ())
  exact ⟨u (), ⟨hu.1 (), hu.2 ()⟩, fun w hw ↦
    congrFun (huniq (fun _ ↦ w) ⟨fun _ ↦ hw.1, fun _ ↦ hw.2⟩) ()⟩

end PDE.Cauchy.Quasilinear.Analytic
