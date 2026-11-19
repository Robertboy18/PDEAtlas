/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Cauchy.Formal.JetSystem.Equations
public import PDE.Analytic.CauchyKovalevskaya.Formal.Recursion

/-!
# Autonomous reduction of the scalar jet system

The finite lower-jet state is numbered by `Fin` so that the coupled Cauchy
theorem applies. A clock component absorbs explicit time dependence, as the extra component
`u^{m+1} = xₙ` does after (15) in Evans, §4.6.3. The coordinate permutation
`jetArgumentEquiv` keeps every jet and position argument.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3, after (15).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MvPowerSeries
open scoped BigOperators

namespace PDE.Cauchy.Quasilinear.Analytic

variable {d k : ℕ}

local notation "J" => (Σ j : Fin (k + 1), Sym (Fin (d + 1)) (j : ℕ))
local notation "T" => {α : Sym (Fin (d + 1)) (k + 1) // α ≠ Sym.replicate (k + 1) 0}
local notation "m" => Fintype.card J
local notation "A" => J ⊕ Fin (d + 1)
local notation "C" => Fin (m + 1) ⊕ Fin d

/-- Reindex the complete coefficient arguments by a clock, the lower jet, and
the spatial coordinates. -/
def jetArgumentEquiv : A ≃ C where
  toFun z := Sum.elim (fun α ↦ Sum.inl ((Fintype.equivFin J) α).succ)
    (Fin.cases (.inl 0) (fun j ↦ .inr j)) z
  invFun z := Sum.elim
    (Fin.cases (.inr 0) (fun i ↦ .inl ((Fintype.equivFin J).symm i)))
    (fun j ↦ .inr j.succ) z
  left_inv z := by
    cases z with
    | inl α => simp
    | inr i => refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
  right_inv z := by
    cases z with
    | inl i => refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
    | inr j => rfl

variable {R : Type*} [CommRing R]

/-- Number the formal lower jet and adjoin the formal time coordinate `X 0`. -/
def formalClockTuple (u : MvPowerSeries (Fin (d + 1)) R) :
    Fin (m + 1) → MvPowerSeries (Fin (d + 1)) R :=
  Fin.cons (X 0) (fun i ↦ formalDerivativeTuple (k + 1) u ((Fintype.equivFin J).symm i))

/-- The autonomous coefficient arguments become the original jet and position
arguments after the coordinate permutation. -/
theorem formalArguments_clockTuple (u : MvPowerSeries (Fin (d + 1)) R) :
    PDE.Analytic.CauchyKovalevskaya.formalArguments (formalClockTuple (k := k) u) ∘
      jetArgumentEquiv = formalArguments (k + 1) u := by
  funext z
  cases z with
  | inl α =>
    simp only [Function.comp_apply, jetArgumentEquiv, Equiv.coe_fn_mk,
      Sum.elim_inl, PDE.Analytic.CauchyKovalevskaya.formalArguments,
      formalClockTuple, Fin.cons_succ, Equiv.symm_apply_apply, formalArguments]
  | inr i =>
    refine Fin.cases ?_ (fun j ↦ ?_) i <;>
      simp only [Function.comp_apply, jetArgumentEquiv, Equiv.coe_fn_mk,
        Sum.elim_inr, Fin.cases_zero, Fin.cases_succ,
        PDE.Analytic.CauchyKovalevskaya.formalArguments, Sum.elim_inl,
        formalClockTuple, Fin.cons_zero, formalArguments]

/-- Zero scalar Cauchy coefficients give zero initial trace for the numbered
jet and clock together. -/
theorem constantCoeff_formalClockTuple
    {u : MvPowerSeries (Fin (d + 1)) R}
    (hu : ∀ j < k + 1, PowerSeries.coeff j (finSuccEquiv R d u) = 0)
    (i : Fin (m + 1)) :
    PowerSeries.constantCoeff (finSuccEquiv R d (formalClockTuple (k := k) u i)) = 0 := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp only [formalClockTuple, Fin.cons_zero, finSuccEquiv_X_zero,
      PowerSeries.constantCoeff_X]
  · exact constantCoeff_formalDerivativeTuple hu ((Fintype.equivFin J).symm j)

/-- The autonomous principal matrices have zero clock row and column. -/
def reducedCoefficients (a : T → R) (j : Fin d) (i l : Fin (m + 1)) : R :=
  Fin.cases 0 (fun i ↦ Fin.cases 0
    (fun l ↦ jetCoefficients a j ((Fintype.equivFin J).symm i) ((Fintype.equivFin J).symm l))
      l) i

/-- The autonomous forcing has unit clock speed and the scalar jet forcing. -/
def reducedForcing (b : R) (v : Fin (m + 1) → R) (i : Fin (m + 1)) : R :=
  Fin.cases 1 (fun i ↦ jetForcing b
    (fun α ↦ v ((Fintype.equivFin J) α).succ) ((Fintype.equivFin J).symm i)) i

/-- Ring homomorphisms commute with the numbered autonomous matrices. -/
theorem map_reducedCoefficients {S : Type*} [CommRing S] (f : R →+* S)
    (a : T → R) (j : Fin d) (i l : Fin (m + 1)) :
    f (reducedCoefficients a j i l) =
      reducedCoefficients (fun γ ↦ f (a γ)) j i l := by
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · simp only [reducedCoefficients, Fin.cases_zero, map_zero]
  · refine Fin.cases ?_ (fun l ↦ ?_) l
    · simp only [reducedCoefficients, Fin.cases_succ, Fin.cases_zero, map_zero]
    · exact map_jetCoefficients f a j _ _

/-- Ring homomorphisms commute with the numbered forcing, including its clock row. -/
theorem map_reducedForcing {S : Type*} [CommRing S] (f : R →+* S)
    (b : R) (v : Fin (m + 1) → R) (i : Fin (m + 1)) :
    f (reducedForcing b v i) = reducedForcing (f b) (fun l ↦ f (v l)) i := by
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · simp only [reducedForcing, Fin.cases_zero, map_one]
  · simp only [reducedForcing, Fin.cases_succ]
    exact map_jetForcing f b
      (fun α ↦ v ((Fintype.equivFin J) α).succ) ((Fintype.equivFin J).symm i)

/-- The numbered tuple with clock satisfies the corresponding autonomous rows
after evaluating the original scalar coefficients. -/
theorem formalClockTuple_equation
    (a : T → MvPowerSeries A R) (b : MvPowerSeries A R)
    {u : MvPowerSeries (Fin (d + 1)) R}
    (hu : (pderiv 0)^[k + 1] u = formalRightHandSide a b u) (i : Fin (m + 1)) :
    pderiv 0 (formalClockTuple (k := k) u i) =
      (∑ j, ∑ l, reducedCoefficients
        (fun γ ↦ subst (formalArguments (k + 1) u) (a γ)) j i l *
          pderiv j.succ (formalClockTuple (k := k) u l)) +
      reducedForcing (subst (formalArguments (k + 1) u) b) (formalClockTuple (k := k) u) i := by
  classical
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · simp only [formalClockTuple, Fin.cons_zero, pderiv_X_self, reducedCoefficients,
      Fin.cases_zero, zero_mul, Finset.sum_const_zero, reducedForcing, zero_add]
  · simp only [formalClockTuple, Fin.cons_succ, reducedCoefficients, Fin.cases_succ,
      Fin.sum_univ_succ, Fin.cases_zero, zero_mul, zero_add, reducedForcing,
      Equiv.symm_apply_apply]
    convert formalDerivativeTuple_equation a b hu ((Fintype.equivFin J).symm i) using 1
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact (Fintype.equivFin J).symm.sum_comp
      (fun β : J ↦ jetCoefficients
        (fun γ ↦ subst (formalArguments (k + 1) u) (a γ)) j
          ((Fintype.equivFin J).symm i) β *
            pderiv j.succ (formalDerivativeTuple (k + 1) u β))

/-- Substitution of the clock and jet undoes the permutation of coefficient variables. -/
theorem subst_rename_jetArgumentEquiv
    {u : MvPowerSeries (Fin (d + 1)) R}
    (hu : ∀ j < k + 1, PowerSeries.coeff j (finSuccEquiv R d u) = 0)
    (f : MvPowerSeries A R) :
    subst (PDE.Analytic.CauchyKovalevskaya.formalArguments (formalClockTuple (k := k) u))
      (rename jetArgumentEquiv f) = subst (formalArguments (k + 1) u) f := by
  have hc := PDE.Analytic.CauchyKovalevskaya.hasSubst_formalArguments
    (constantCoeff_formalClockTuple hu)
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) hc]
  simp only [Function.comp_apply, subst_X hc]
  exact congrArg (fun args : A → MvPowerSeries (Fin (d + 1)) R ↦ subst args f)
    (formalArguments_clockTuple u)

/-- The scalar formal solution, its mixed formal derivatives, and the clock
satisfy the formal system of the analytic coupled Cauchy theorem. -/
theorem formalClockTuple_solution
    (a : T → MvPowerSeries A R) (b : MvPowerSeries A R)
    {u : MvPowerSeries (Fin (d + 1)) R}
    (ht : ∀ j < k + 1, PowerSeries.coeff j (finSuccEquiv R d u) = 0)
    (hu : (pderiv 0)^[k + 1] u = formalRightHandSide a b u) :
    (∀ i, PowerSeries.constantCoeff
      (finSuccEquiv R d (formalClockTuple (k := k) u i)) = 0) ∧
    ∀ i, pderiv 0 (formalClockTuple (k := k) u i) =
      PDE.Analytic.CauchyKovalevskaya.formalRightHandSide
        (fun j i l ↦ reducedCoefficients (fun γ ↦ rename jetArgumentEquiv (a γ)) j i l)
        (fun i ↦ reducedForcing (rename jetArgumentEquiv b) (fun l ↦ X (.inl l)) i)
        (formalClockTuple (k := k) u) i := by
  refine ⟨constantCoeff_formalClockTuple ht, fun i ↦ ?_⟩
  have hc := PDE.Analytic.CauchyKovalevskaya.hasSubst_formalArguments
    (constantCoeff_formalClockTuple ht)
  let F := (substAlgHom (R := R) hc).toRingHom
  have hF (f : MvPowerSeries C R) :
      F f = subst
        (PDE.Analytic.CauchyKovalevskaya.formalArguments (formalClockTuple (k := k) u)) f :=
    substAlgHom_apply hc f
  have hvar (l : Fin (m + 1)) : F (X (.inl l)) = formalClockTuple (k := k) u l := by
    rw [hF, subst_X hc]
    rfl
  rw [formalClockTuple_equation a b hu]
  unfold PDE.Analytic.CauchyKovalevskaya.formalRightHandSide
  simp only [← hF, map_reducedCoefficients, map_reducedForcing, hvar]
  simp only [hF, subst_rename_jetArgumentEquiv ht]

end PDE.Cauchy.Quasilinear.Analytic
