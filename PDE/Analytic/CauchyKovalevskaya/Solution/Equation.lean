/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Composition
public import PDE.Analysis.Analytic.PowerSeries.Differentiation
public import PDE.Analysis.Analytic.PowerSeries.FiniteOperations
public import PDE.Analytic.CauchyKovalevskaya.Formal.Recursion

/-!
# The analytic reduced Cauchy equation

The right-hand side is built from Fréchet derivatives of the component
functions. Its power series is the formal right-hand side used in the time
recursion.

Time is coordinate zero and the initial surface is `{t = 0}`. The coefficients `B j i k` and
the forcing `c i` are functions of the state and the spatial coordinates (`arguments`), so
the system is

```text
∂ₜ uᵢ = ∑ⱼ ∑ₖ Bⱼᵢₖ(u, x) ∂ⱼ uₖ + cᵢ(u, x),   uᵢ(0, x) = gᵢ(x),
```

with `∂ⱼ` the derivative in spatial coordinate `j`. This is the system (15)-(16) of Evans,
§4.6.3, with time in place of `xₙ` and with general initial data. As in Evans, explicit time
dependence is removed by adjoining a clock variable
(`PDE.Analytic.CauchyKovalevskaya.Solution.TimeDependent`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3, (15)-(16).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Topology
open Filter

noncomputable section

namespace PDE.Analytic.CauchyKovalevskaya

variable {d m : ℕ}

/-- The state and spatial coordinates at a spacetime point. -/
def arguments (u : (Fin (d + 1) → ℝ) → Fin m → ℝ) (x : Fin (d + 1) → ℝ) :
    (Fin m ⊕ Fin d) → ℝ :=
  Sum.elim (u x) (Fin.tail x)

/-- The quasilinear right-hand side in the reduced first-order Cauchy system. -/
def rightHandSide
    (B : Fin d → Fin m → Fin m → ((Fin m ⊕ Fin d) → ℝ) → ℝ)
    (c : Fin m → ((Fin m ⊕ Fin d) → ℝ) → ℝ)
    (u : (Fin (d + 1) → ℝ) → Fin m → ℝ) (i : Fin m) (x : Fin (d + 1) → ℝ) : ℝ :=
  (∑ j, ∑ k, B j i k (arguments u x) *
    fderiv ℝ (fun y ↦ u y k) x (Pi.single j.succ 1)) + c i (arguments u x)

/-- Analytic component functions give analytic state-coordinate arguments. -/
theorem analyticAt_arguments {u : (Fin (d + 1) → ℝ) → Fin m → ℝ}
    {x : Fin (d + 1) → ℝ} (hu : ∀ i, AnalyticAt ℝ (fun y ↦ u y i) x) :
    AnalyticAt ℝ (arguments u) x := by
  apply AnalyticAt.pi
  intro i
  cases i with
  | inl i => exact hu i
  | inr j =>
    exact (ContinuousLinearMap.proj j.succ : (Fin (d + 1) → ℝ) →L[ℝ] ℝ).analyticAt x

/-- At zero state and zero spatial coordinates, the combined argument is zero. -/
theorem arguments_zero {u : (Fin (d + 1) → ℝ) → Fin m → ℝ} (hu : u 0 = 0) :
    arguments u 0 = 0 := by
  ext i
  cases i with
  | inl i => exact congrFun hu i
  | inr j => rfl

/-- Analytic coefficients and an analytic state give an analytic right-hand side. -/
theorem analyticAt_rightHandSide
    {B : Fin d → Fin m → Fin m → ((Fin m ⊕ Fin d) → ℝ) → ℝ}
    {c : Fin m → ((Fin m ⊕ Fin d) → ℝ) → ℝ}
    {u : (Fin (d + 1) → ℝ) → Fin m → ℝ}
    (hB : ∀ j i k, AnalyticAt ℝ (B j i k) 0) (hc : ∀ i, AnalyticAt ℝ (c i) 0)
    (hu : ∀ i, AnalyticAt ℝ (fun x ↦ u x i) 0) (hu0 : u 0 = 0) (i : Fin m) :
    AnalyticAt ℝ (rightHandSide B c u i) 0 := by
  have ha := analyticAt_arguments hu
  have ha0 := arguments_zero hu0
  apply AnalyticAt.add
  · apply Finset.analyticAt_fun_sum
    intro j hj
    apply Finset.analyticAt_fun_sum
    intro k hk
    let L := ContinuousLinearMap.apply ℝ ℝ (Pi.single j.succ 1 : Fin (d + 1) → ℝ)
    exact ((hB j i k).comp_of_eq ha ha0).mul ((L.analyticAt _).comp (hu k).fderiv)
  · exact (hc i).comp_of_eq ha ha0

/-- The power series of the right-hand side is the formal right-hand side evaluated
at the power series of the coefficients, the forcing, and the state. -/
theorem toMvPowerSeries_rightHandSide
    {B : Fin d → Fin m → Fin m → ((Fin m ⊕ Fin d) → ℝ) → ℝ}
    {c : Fin m → ((Fin m ⊕ Fin d) → ℝ) → ℝ}
    {u : (Fin (d + 1) → ℝ) → Fin m → ℝ}
    {pB : Fin d → Fin m → Fin m →
      FormalMultilinearSeries ℝ ((Fin m ⊕ Fin d) → ℝ) ℝ}
    {pc : Fin m → FormalMultilinearSeries ℝ ((Fin m ⊕ Fin d) → ℝ) ℝ}
    {pu : Fin m → FormalMultilinearSeries ℝ (Fin (d + 1) → ℝ) ℝ}
    (hB : ∀ j i k, HasFPowerSeriesAt (B j i k) (pB j i k) 0)
    (hc : ∀ i, HasFPowerSeriesAt (c i) (pc i) 0)
    (hu : ∀ i, HasFPowerSeriesAt (fun x ↦ u x i) (pu i) 0)
    (hu0 : u 0 = 0) (i : Fin m)
    {r : FormalMultilinearSeries ℝ (Fin (d + 1) → ℝ) ℝ}
    (hr : HasFPowerSeriesAt (rightHandSide B c u i) r 0) :
    r.toMvPowerSeries = formalRightHandSide
      (fun j i k ↦ (pB j i k).toMvPowerSeries) (fun i ↦ (pc i).toMvPowerSeries)
      (fun i ↦ (pu i).toMvPowerSeries) i := by
  have ha := analyticAt_arguments (fun i ↦ (hu i).analyticAt)
  have ha0 := arguments_zero hu0
  have hacomp (j : Fin m ⊕ Fin d) : AnalyticAt ℝ (fun x ↦ arguments u x j) 0 :=
    ((ContinuousLinearMap.proj j : ((Fin m ⊕ Fin d) → ℝ) →L[ℝ] ℝ).analyticAt _).comp ha
  choose pa hpa using hacomp
  have hpaeq : (fun j ↦ (pa j).toMvPowerSeries) =
      formalArguments (fun i ↦ (pu i).toMvPowerSeries) := by
    funext j
    cases j with
    | inl i => exact (hpa (.inl i)).toMvPowerSeries_eq (hu i) EventuallyEq.rfl
    | inr j => exact (hpa (.inr j)).toMvPowerSeries_proj j.succ
  have hcomp {F : ((Fin m ⊕ Fin d) → ℝ) → ℝ}
      {pF : FormalMultilinearSeries ℝ ((Fin m ⊕ Fin d) → ℝ) ℝ}
      (hF : HasFPowerSeriesAt F pF 0)
      {s : FormalMultilinearSeries ℝ (Fin (d + 1) → ℝ) ℝ}
      (hs : HasFPowerSeriesAt (fun x ↦ F (arguments u x)) s 0) :
      s.toMvPowerSeries =
        pF.toMvPowerSeries.subst (formalArguments fun i ↦ (pu i).toMvPowerSeries) := by
    rw [hF.toMvPowerSeries_comp hpa ha0 hs, hpaeq]
  have hba (j : Fin d) (k : Fin m) :
      AnalyticAt ℝ (fun x ↦ B j i k (arguments u x)) 0 :=
    (hB j i k).analyticAt.comp_of_eq ha ha0
  choose pb hpb using hba
  let pd (j : Fin d) (k : Fin m) := ContinuousLinearMap.compFormalMultilinearSeries
    (ContinuousLinearMap.apply ℝ ℝ (Pi.single j.succ 1 : Fin (d + 1) → ℝ)) (pu k).derivSeries
  have hpd (j : Fin d) (k : Fin m) : HasFPowerSeriesAt
      (fun x ↦ fderiv ℝ (fun y ↦ u y k) x (Pi.single j.succ 1)) (pd j k) 0 :=
    (hu k).fderiv_apply (Pi.single j.succ 1)
  have ht (j : Fin d) (k : Fin m) : AnalyticAt ℝ
      (fun x ↦ B j i k (arguments u x) *
        fderiv ℝ (fun y ↦ u y k) x (Pi.single j.succ 1)) 0 :=
    (hpb j k).analyticAt.mul (hpd j k).analyticAt
  choose pt hpt using ht
  have hs (j : Fin d) : AnalyticAt ℝ
      (fun x ↦ ∑ k, B j i k (arguments u x) *
        fderiv ℝ (fun y ↦ u y k) x (Pi.single j.succ 1)) 0 :=
    Finset.univ.analyticAt_fun_sum (fun k _ ↦ (hpt j k).analyticAt)
  choose ps hps using hs
  obtain ⟨pall, hpall⟩ := Finset.univ.analyticAt_fun_sum (fun j _ ↦ (hps j).analyticAt)
  obtain ⟨pf, hpf⟩ := (hc i).analyticAt.comp_of_eq ha ha0
  have hadd := hpall.toMvPowerSeries_add hpf (show HasFPowerSeriesAt
      ((fun x ↦ ∑ j, ∑ k, B j i k (arguments u x) *
        fderiv ℝ (fun y ↦ u y k) x (Pi.single j.succ 1)) +
        fun x ↦ c i (arguments u x)) r 0 from hr)
  rw [hadd, hcomp (hc i) hpf,
    HasFPowerSeriesAt.toMvPowerSeries_sum Finset.univ hps hpall]
  unfold formalRightHandSide
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [HasFPowerSeriesAt.toMvPowerSeries_sum Finset.univ (hpt j) (hps j)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [(hpb j k).toMvPowerSeries_mul (hpd j k) (hpt j k), hcomp (hB j i k) (hpb j k),
    (hu k).toMvPowerSeries_fderiv_apply j.succ (hpd j k)]

end PDE.Analytic.CauchyKovalevskaya
