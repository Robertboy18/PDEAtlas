/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Composition.Reindex
public import PDE.Analytic.CauchyKovalevskaya.Majorant.Convergence
public import PDE.Cauchy.Formal.JetSystem.Autonomous
public import PDE.Cauchy.Formal.Recursion

/-!
# Convergence of the scalar Cauchy series

Analytic scalar coefficients give analytic coefficients for the finite jet
system. Uniqueness of its formal solution identifies the formal jet tuple of the
scalar series with the convergent coupled solution, so its zeroth jet component
converges. The jet state is the jet of the scalar series, so no separate
compatibility hypothesis is needed. The reduction of the scalar problem (14) to the
first-order system (15) is that of Evans, §4.6.3(a).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3(a), (14)-(15).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MvPowerSeries

namespace PDE.Cauchy.Quasilinear.Analytic

variable {d k : ℕ}

local notation "J" => (Σ j : Fin (k + 1), Sym (Fin (d + 1)) (j : ℕ))
local notation "T" => {α : Sym (Fin (d + 1)) (k + 1) // α ≠ Sym.replicate (k + 1) 0}
local notation "m" => Fintype.card J
local notation "A" => J ⊕ Fin (d + 1)
local notation "C" => Fin (m + 1) ⊕ Fin d

/-- Positive-radius scalar coefficient expansions give a positive-radius scalar
solution of arbitrary positive order. All initial time coefficients below that
order vanish as entire spatial series. -/
theorem exists_convergent_formal_solution
    (a : T → FormalMultilinearSeries ℝ (A → ℝ) ℝ)
    (b : FormalMultilinearSeries ℝ (A → ℝ) ℝ)
    (ha : ∀ γ, 0 < (a γ).radius) (hb : 0 < b.radius) :
    ∃ u : MvPowerSeries (Fin (d + 1)) ℝ,
      (∀ j < k + 1, PowerSeries.coeff j (finSuccEquiv ℝ d u) = 0) ∧
      (pderiv 0)^[k + 1] u = formalRightHandSide
        (fun γ ↦ (a γ).toMvPowerSeries) b.toMvPowerSeries u ∧
      0 < u.toFormalMultilinearSeries.radius := by
  classical
  let e : A ≃ C := jetArgumentEquiv
  let g (z : C → ℝ) : A → ℝ := fun α ↦ z (e α)
  have hg : AnalyticAt ℝ g 0 := AnalyticAt.pi fun α ↦
    (ContinuousLinearMap.proj (e α) : (C → ℝ) →L[ℝ] ℝ).analyticAt 0
  have hga (γ : T) : AnalyticAt ℝ (fun z ↦ (a γ).sum (g z)) 0 :=
    ((a γ).hasFPowerSeriesOnBall (ha γ)).hasFPowerSeriesAt.analyticAt.comp_of_eq hg rfl
  choose pa hpa using hga
  have hpaeq (γ : T) :
      (pa γ).toMvPowerSeries = rename e (a γ).toMvPowerSeries :=
    ((a γ).hasFPowerSeriesOnBall (ha γ)).hasFPowerSeriesAt.toMvPowerSeries_comp_reindex
      e (hpa γ)
  have hB (j : Fin d) (i l : Fin (m + 1)) :
      ∃ p : FormalMultilinearSeries ℝ (C → ℝ) ℝ,
        0 < p.radius ∧ p.toMvPowerSeries =
          reducedCoefficients (fun γ ↦ rename e (a γ).toMvPowerSeries) j i l := by
    let P : MvPolynomial T ℝ := reducedCoefficients MvPolynomial.X j i l
    obtain ⟨p, hp⟩ := AnalyticAt.aeval_mvPolynomial (fun γ ↦ (hpa γ).analyticAt) P
    refine ⟨p, hp.radius_pos, ?_⟩
    rw [HasFPowerSeriesAt.toMvPowerSeries_eval_comp hpa P hp]
    change (MvPolynomial.aeval fun γ ↦ (pa γ).toMvPowerSeries).toRingHom
      (reducedCoefficients MvPolynomial.X j i l) = _
    rw [map_reducedCoefficients]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X, hpaeq]
  choose pB hpBr hpBeq using hB
  let f (j : Option (Fin (m + 1))) (z : C → ℝ) : ℝ :=
    Option.elim j (b.sum (g z)) (fun i ↦ z (.inl i))
  have hf (j : Option (Fin (m + 1))) : AnalyticAt ℝ (f j) 0 := by
    cases j with
    | none => exact (b.hasFPowerSeriesOnBall hb).hasFPowerSeriesAt.analyticAt.comp_of_eq hg rfl
    | some i => exact (ContinuousLinearMap.proj (.inl i) : (C → ℝ) →L[ℝ] ℝ).analyticAt 0
  choose pf hpf using hf
  have hpfnone : (pf none).toMvPowerSeries = rename e b.toMvPowerSeries :=
    (b.hasFPowerSeriesOnBall hb).hasFPowerSeriesAt.toMvPowerSeries_comp_reindex e (hpf none)
  have hpfsome (i : Fin (m + 1)) : (pf (some i)).toMvPowerSeries = X (.inl i) :=
    (hpf (some i)).toMvPowerSeries_proj (Sum.inl i)
  have hc (i : Fin (m + 1)) :
      ∃ p : FormalMultilinearSeries ℝ (C → ℝ) ℝ,
        0 < p.radius ∧ p.toMvPowerSeries =
          reducedForcing (rename e b.toMvPowerSeries) (fun l ↦ X (.inl l)) i := by
    let P : MvPolynomial (Option (Fin (m + 1))) ℝ :=
      reducedForcing (MvPolynomial.X none) (fun l ↦ MvPolynomial.X (some l)) i
    obtain ⟨p, hp⟩ := AnalyticAt.aeval_mvPolynomial (fun j ↦ (hpf j).analyticAt) P
    refine ⟨p, hp.radius_pos, ?_⟩
    rw [HasFPowerSeriesAt.toMvPowerSeries_eval_comp hpf P hp]
    change (MvPolynomial.aeval fun j ↦ (pf j).toMvPowerSeries).toRingHom
      (reducedForcing (MvPolynomial.X none) (fun l ↦ MvPolynomial.X (some l)) i) = _
    rw [map_reducedForcing]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X,
      hpfnone, hpfsome]
  choose pc hpcr hpceq using hc
  obtain ⟨u, hu, _⟩ := existsUnique_formal_solution (Nat.succ_pos k)
    (fun γ ↦ (a γ).toMvPowerSeries) b.toMvPowerSeries
  have hclock := formalClockTuple_solution
    (fun γ ↦ (a γ).toMvPowerSeries) b.toMvPowerSeries hu.1 hu.2
  obtain ⟨v, hvzero, hveq, hvr⟩ :=
    PDE.Analytic.CauchyKovalevskaya.exists_convergent_formal_solution pB pc hpBr hpcr
  simp only [hpBeq, hpceq] at hveq
  obtain ⟨w, _, hwunique⟩ := PDE.Analytic.CauchyKovalevskaya.existsUnique_formal_solution
    (fun j i l ↦ reducedCoefficients (fun γ ↦ rename e (a γ).toMvPowerSeries) j i l)
    (fun i ↦ reducedForcing (rename e b.toMvPowerSeries) (fun l ↦ X (.inl l)) i)
  have huv : formalClockTuple (k := k) u = v :=
    (hwunique _ hclock).trans (hwunique _ ⟨hvzero, hveq⟩).symm
  let α : J := ⟨⟨0, Nat.succ_pos k⟩, Sym.nil⟩
  have hcomponent : formalClockTuple (k := k) u ((Fintype.equivFin J) α).succ = u := by
    change formalDerivativeTuple (k + 1) u
      ((Fintype.equivFin J).symm ((Fintype.equivFin J) α)) = u
    rw [Equiv.symm_apply_apply]
    exact iteratedPDeriv_zero_multiset u
  refine ⟨u, hu.1, hu.2, ?_⟩
  rw [← hcomponent, huv]
  exact hvr _

end PDE.Cauchy.Quasilinear.Analytic
