/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analytic.CauchyKovalevskaya.Solution.Existence
public import PDE.Analytic.CauchyKovalevskaya.Solution.Uniqueness

/-!
# Analytic initial data for the reduced Cauchy system

Subtracting the analytic initial function reduces the Cauchy data to zero, as in the
reduction of Evans, §4.6.3(a). Its spatial derivatives enter the transformed forcing; the
principal coefficient matrices are evaluated at the shifted state.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3(a).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Topology
open Filter

noncomputable section

namespace PDE.Analytic.CauchyKovalevskaya

variable {d m : ℕ}

/-- Shift the state by its prescribed analytic initial function. -/
def shiftArguments (g : (Fin d → ℝ) → Fin m → ℝ) (z : (Fin m ⊕ Fin d) → ℝ) :
    (Fin m ⊕ Fin d) → ℝ :=
  Sum.elim (fun i ↦ z (.inl i) + g (fun j ↦ z (.inr j)) i) (fun j ↦ z (.inr j))

/-- The forcing after subtracting the initial function includes its spatial derivatives. -/
def shiftedForcing
    (B : Fin d → Fin m → Fin m → ((Fin m ⊕ Fin d) → ℝ) → ℝ)
    (c : Fin m → ((Fin m ⊕ Fin d) → ℝ) → ℝ)
    (g : (Fin d → ℝ) → Fin m → ℝ) (i : Fin m) (z : (Fin m ⊕ Fin d) → ℝ) : ℝ :=
  (∑ j, ∑ k, B j i k (shiftArguments g z) *
    fderiv ℝ (fun y ↦ g y k) (fun l ↦ z (.inr l)) (Pi.single j 1)) +
      c i (shiftArguments g z)

/-- Restore the initial function to a state with zero initial trace. -/
def addInitialData (g : (Fin d → ℝ) → Fin m → ℝ)
    (v : (Fin (d + 1) → ℝ) → Fin m → ℝ) (x : Fin (d + 1) → ℝ) : Fin m → ℝ :=
  v x + g (Fin.tail x)

/-- The shifted origin is the original initial state and zero spatial position. -/
theorem shiftArguments_zero (g : (Fin d → ℝ) → Fin m → ℝ) :
    shiftArguments g 0 = Sum.elim (g 0) 0 := by
  ext i
  cases i <;> simp only [shiftArguments, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_add]
  rfl

/-- Analytic initial data make the change of state analytic. -/
theorem analyticAt_shiftArguments {g : (Fin d → ℝ) → Fin m → ℝ}
    (hg : AnalyticAt ℝ g 0) : AnalyticAt ℝ (shiftArguments g) 0 := by
  let L : (((Fin m ⊕ Fin d) → ℝ) →L[ℝ] (Fin d → ℝ)) :=
    ContinuousLinearMap.pi (fun j ↦ ContinuousLinearMap.proj (.inr j))
  have hgL : AnalyticAt ℝ (fun z ↦ g (L z)) 0 :=
    hg.comp_of_eq (L.analyticAt 0) (map_zero L)
  apply AnalyticAt.pi
  intro i
  cases i with
  | inl i =>
    let P : ((Fin m ⊕ Fin d) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (.inl i)
    let Q : (Fin m → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
    exact (P.analyticAt 0).add ((Q.analyticAt _).comp hgL)
  | inr j =>
    exact (ContinuousLinearMap.proj (.inr j) : ((Fin m ⊕ Fin d) → ℝ) →L[ℝ] ℝ).analyticAt 0

/-- The transformed forcing is analytic when the coefficients and initial data are. -/
theorem analyticAt_shiftedForcing
    {B : Fin d → Fin m → Fin m → ((Fin m ⊕ Fin d) → ℝ) → ℝ}
    {c : Fin m → ((Fin m ⊕ Fin d) → ℝ) → ℝ}
    {g : (Fin d → ℝ) → Fin m → ℝ}
    (hB : ∀ j i k, AnalyticAt ℝ (B j i k) (Sum.elim (g 0) 0))
    (hc : ∀ i, AnalyticAt ℝ (c i) (Sum.elim (g 0) 0))
    (hg : AnalyticAt ℝ g 0) (i : Fin m) :
    AnalyticAt ℝ (shiftedForcing B c g i) 0 := by
  let L : (((Fin m ⊕ Fin d) → ℝ) →L[ℝ] (Fin d → ℝ)) :=
    ContinuousLinearMap.pi (fun j ↦ ContinuousLinearMap.proj (.inr j))
  have hga := analyticAt_shiftArguments hg
  apply AnalyticAt.add
  · apply Finset.analyticAt_fun_sum
    intro j hj
    apply Finset.analyticAt_fun_sum
    intro k hk
    have hgk : AnalyticAt ℝ (fun x ↦ g x k) 0 :=
      ((ContinuousLinearMap.proj k : (Fin m → ℝ) →L[ℝ] ℝ).analyticAt _).comp hg
    let E := ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1 : Fin d → ℝ)
    have hd := ((E.analyticAt _).comp hgk.fderiv).comp_of_eq (L.analyticAt 0) (map_zero L)
    exact ((hB j i k).comp_of_eq hga (shiftArguments_zero g)).mul hd
  · exact (hc i).comp_of_eq hga (shiftArguments_zero g)

/-- Restoring the initial function adds only the derivative of its spatial pullback. -/
theorem fderiv_addInitialData
    {g : (Fin d → ℝ) → Fin m → ℝ} {v : (Fin (d + 1) → ℝ) → Fin m → ℝ}
    {x : Fin (d + 1) → ℝ} {i : Fin m}
    (hv : DifferentiableAt ℝ (fun y ↦ v y i) x)
    (hg : DifferentiableAt ℝ (fun y ↦ g y i) (Fin.tail x)) (h : Fin (d + 1) → ℝ) :
    fderiv ℝ (fun y ↦ addInitialData g v y i) x h =
      fderiv ℝ (fun y ↦ v y i) x h +
        fderiv ℝ (fun y ↦ g y i) (Fin.tail x) (Fin.tail h) := by
  let L : (Fin (d + 1) → ℝ) →L[ℝ] (Fin d → ℝ) :=
    ContinuousLinearMap.pi (fun j ↦ ContinuousLinearMap.proj j.succ)
  have hd := hv.hasFDerivAt.add (hg.hasFDerivAt.comp x L.hasFDerivAt)
  exact congrArg (fun T : (Fin (d + 1) → ℝ) →L[ℝ] ℝ ↦ T h) hd.fderiv

/-- Restoring the initial function converts the transformed equation into the
original equation. Only differentiability of `v` and `g` at the point is used. -/
theorem cauchy_eq_addInitialData_iff
    (B : Fin d → Fin m → Fin m → ((Fin m ⊕ Fin d) → ℝ) → ℝ)
    (c : Fin m → ((Fin m ⊕ Fin d) → ℝ) → ℝ)
    {g : (Fin d → ℝ) → Fin m → ℝ} {v : (Fin (d + 1) → ℝ) → Fin m → ℝ}
    {x : Fin (d + 1) → ℝ}
    (hv : ∀ i, DifferentiableAt ℝ (fun y ↦ v y i) x)
    (hg : ∀ i, DifferentiableAt ℝ (fun y ↦ g y i) (Fin.tail x)) (i : Fin m) :
    fderiv ℝ (fun y ↦ addInitialData g v y i) x (Pi.single 0 1) =
        rightHandSide B c (addInitialData g v) i x ↔
      fderiv ℝ (fun y ↦ v y i) x (Pi.single 0 1) =
        rightHandSide (fun j i k z ↦ B j i k (shiftArguments g z))
          (shiftedForcing B c g) v i x := by
  have ht0 : Fin.tail (Pi.single 0 1 : Fin (d + 1) → ℝ) = 0 := by
    ext j
    simp [Fin.tail, Fin.succ_ne_zero]
  have hts (j : Fin d) :
      Fin.tail (Pi.single j.succ 1 : Fin (d + 1) → ℝ) = Pi.single j 1 := by
    ext k
    simp [Fin.tail, Pi.single_apply]
  have htime := fderiv_addInitialData (hv i) (hg i) (Pi.single 0 1)
  rw [ht0, map_zero, add_zero] at htime
  have harg : arguments (addInitialData g v) x = shiftArguments g (arguments v x) := rfl
  have hR : rightHandSide B c (addInitialData g v) i x =
      rightHandSide (fun j i k z ↦ B j i k (shiftArguments g z))
        (shiftedForcing B c g) v i x := by
    simp only [rightHandSide, shiftedForcing, harg]
    simp_rw [fderiv_addInitialData (hv _) (hg _), hts, mul_add]
    simp only [Finset.sum_add_distrib, add_assoc]
    rfl
  rw [htime, hR]

/-- A reduced coupled Cauchy system with analytic coefficients and arbitrary
analytic initial data has an analytic solution on a ball of positive radius.
The coefficients are assumed analytic at the initial state `Sum.elim (g 0) 0`;
the conclusion is stated for the original coefficients and data. -/
theorem exists_analytic_solution
    (B : Fin d → Fin m → Fin m → ((Fin m ⊕ Fin d) → ℝ) → ℝ)
    (c : Fin m → ((Fin m ⊕ Fin d) → ℝ) → ℝ)
    (g : (Fin d → ℝ) → Fin m → ℝ)
    (hB : ∀ j i k, AnalyticAt ℝ (B j i k) (Sum.elim (g 0) 0))
    (hc : ∀ i, AnalyticAt ℝ (c i) (Sum.elim (g 0) 0))
    (hg : AnalyticAt ℝ g 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ u : (Fin (d + 1) → ℝ) → Fin m → ℝ,
      AnalyticOnNhd ℝ u (Metric.ball 0 r) ∧
      (∀ x ∈ Metric.ball (0 : Fin d → ℝ) r, u (Fin.cons 0 x) = g x) ∧
      ∀ x ∈ Metric.ball 0 r, ∀ i,
        fderiv ℝ (fun y ↦ u y i) x (Pi.single 0 1) = rightHandSide B c u i x := by
  have hB' (j : Fin d) (i k : Fin m) :
      AnalyticAt ℝ (fun z ↦ B j i k (shiftArguments g z)) 0 :=
    (hB j i k).comp_of_eq (analyticAt_shiftArguments hg) (shiftArguments_zero g)
  obtain ⟨r, hr, v, hva, hvt, hve⟩ := exists_analytic_solution_zero
    (fun j i k z ↦ B j i k (shiftArguments g z)) (shiftedForcing B c g)
    hB' (analyticAt_shiftedForcing hB hc hg)
  let L : (Fin (d + 1) → ℝ) →L[ℝ] (Fin d → ℝ) :=
    ContinuousLinearMap.pi (fun j ↦ ContinuousLinearMap.proj j.succ)
  have hv0 := hva 0 (Metric.mem_ball_self hr)
  have hua : AnalyticAt ℝ (addInitialData g v) 0 :=
    hv0.add (hg.comp_of_eq (L.analyticAt 0) (map_zero L))
  have hL : Tendsto L (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, map_zero] using L.continuous.continuousAt (x := 0)
  have hEq : ∀ᶠ x in 𝓝 0, ∀ i,
      fderiv ℝ (fun y ↦ addInitialData g v y i) x (Pi.single 0 1) =
        rightHandSide B c (addInitialData g v) i x := by
    filter_upwards [Metric.ball_mem_nhds 0 hr, hv0.eventually_analyticAt,
      hL.eventually hg.eventually_analyticAt] with x hx hvx hgx
    have hvd (i : Fin m) : DifferentiableAt ℝ (fun y ↦ v y i) x :=
      (((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).analyticAt _).comp
        hvx).differentiableAt
    have hgd (i : Fin m) : DifferentiableAt ℝ (fun y ↦ g y i) (Fin.tail x) :=
      (((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).analyticAt _).comp
        hgx).differentiableAt
    exact fun i ↦ (cauchy_eq_addInitialData_iff B c hvd hgd i).mpr (hve x hx i)
  have htrace : (fun x : Fin d → ℝ ↦ addInitialData g v (Fin.cons 0 x))
      =ᶠ[𝓝 0] g := by
    filter_upwards [Metric.ball_mem_nhds 0 hr] with x hx
    simp only [addInitialData, hvt x hx, Fin.tail_cons, zero_add]
  obtain ⟨r₁, hr₁, h₁⟩ := Metric.mem_nhds_iff.mp (hua.eventually_analyticAt.and hEq)
  obtain ⟨r₂, hr₂, h₂⟩ := Metric.mem_nhds_iff.mp htrace
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, addInitialData g v, ?_, ?_, ?_⟩
  · intro x hx
    exact (h₁ (Metric.ball_subset_ball (min_le_left _ _) hx)).1
  · intro x hx
    exact h₂ (Metric.ball_subset_ball (min_le_right _ _) hx)
  · intro x hx i
    exact (h₁ (Metric.ball_subset_ball (min_le_left _ _) hx)).2 i

/-- Analytic solutions with the same analytic initial function and the same
original Cauchy system agree on a neighborhood of the origin. -/
theorem eventuallyEq_of_analytic_solutions
    {B : Fin d → Fin m → Fin m → ((Fin m ⊕ Fin d) → ℝ) → ℝ}
    {c : Fin m → ((Fin m ⊕ Fin d) → ℝ) → ℝ}
    {g : (Fin d → ℝ) → Fin m → ℝ}
    (hB : ∀ j i k, AnalyticAt ℝ (B j i k) (Sum.elim (g 0) 0))
    (hc : ∀ i, AnalyticAt ℝ (c i) (Sum.elim (g 0) 0))
    (hg : AnalyticAt ℝ g 0)
    {u v : (Fin (d + 1) → ℝ) → Fin m → ℝ}
    (hu : AnalyticAt ℝ u 0) (hv : AnalyticAt ℝ v 0)
    (hutrace : (fun x : Fin d → ℝ ↦ u (Fin.cons 0 x)) =ᶠ[𝓝 0] g)
    (hvtrace : (fun x : Fin d → ℝ ↦ v (Fin.cons 0 x)) =ᶠ[𝓝 0] g)
    (hueq : ∀ i, (fun x ↦ fderiv ℝ (fun y ↦ u y i) x (Pi.single 0 1))
      =ᶠ[𝓝 0] rightHandSide B c u i)
    (hveq : ∀ i, (fun x ↦ fderiv ℝ (fun y ↦ v y i) x (Pi.single 0 1))
      =ᶠ[𝓝 0] rightHandSide B c v i) :
    u =ᶠ[𝓝 0] v := by
  let L : (Fin (d + 1) → ℝ) →L[ℝ] (Fin d → ℝ) :=
    ContinuousLinearMap.pi (fun j ↦ ContinuousLinearMap.proj j.succ)
  have hgL : AnalyticAt ℝ (fun x : Fin (d + 1) → ℝ ↦ g (Fin.tail x)) 0 := by
    change AnalyticAt ℝ (fun x ↦ g (L x)) 0
    exact hg.comp_of_eq (L.analyticAt 0) (map_zero L)
  have hL : Tendsto L (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, map_zero] using L.continuous.continuousAt (x := 0)
  let w (z : (Fin (d + 1) → ℝ) → Fin m → ℝ) (x : Fin (d + 1) → ℝ) :=
    z x - g (Fin.tail x)
  have hred (z : (Fin (d + 1) → ℝ) → Fin m → ℝ)
      (hz : AnalyticAt ℝ z 0)
      (ht : (fun x : Fin d → ℝ ↦ z (Fin.cons 0 x)) =ᶠ[𝓝 0] g)
      (he : ∀ i, (fun x ↦ fderiv ℝ (fun y ↦ z y i) x (Pi.single 0 1))
        =ᶠ[𝓝 0] rightHandSide B c z i) :
      (∀ i, AnalyticAt ℝ (fun x ↦ w z x i) 0) ∧
      (∀ i, (fun x : Fin d → ℝ ↦ w z (Fin.cons 0 x) i) =ᶠ[𝓝 0] 0) ∧
      ∀ i, (fun x ↦ fderiv ℝ (fun y ↦ w z y i) x (Pi.single 0 1))
        =ᶠ[𝓝 0] rightHandSide (fun j i k a ↦ B j i k (shiftArguments g a))
          (shiftedForcing B c g) (w z) i := by
    have hw : AnalyticAt ℝ (w z) 0 := hz.sub hgL
    have hrestore : addInitialData g (w z) = z := by
      funext x
      exact sub_add_cancel (z x) (g (Fin.tail x))
    refine ⟨fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_⟩
    · exact ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).analyticAt _).comp hw
    · filter_upwards [ht] with x hx
      simp only [w, hx, Fin.tail_cons, sub_self, Pi.zero_apply]
    · filter_upwards [he i, hw.eventually_analyticAt,
        hL.eventually hg.eventually_analyticAt] with x hx hwx hgx
      have hwd (k : Fin m) : DifferentiableAt ℝ (fun y ↦ w z y k) x :=
        (((ContinuousLinearMap.proj k : (Fin m → ℝ) →L[ℝ] ℝ).analyticAt _).comp
          hwx).differentiableAt
      have hgd (k : Fin m) : DifferentiableAt ℝ (fun y ↦ g y k) (Fin.tail x) :=
        (((ContinuousLinearMap.proj k : (Fin m → ℝ) →L[ℝ] ℝ).analyticAt _).comp
          hgx).differentiableAt
      apply (cauchy_eq_addInitialData_iff B c hwd hgd i).mp
      simpa only [hrestore] using hx
  have hu' := hred u hu hutrace hueq
  have hv' := hred v hv hvtrace hveq
  have hB' (j : Fin d) (i k : Fin m) :
      AnalyticAt ℝ (fun z ↦ B j i k (shiftArguments g z)) 0 :=
    (hB j i k).comp_of_eq (analyticAt_shiftArguments hg) (shiftArguments_zero g)
  have heq := eventuallyEq_of_analytic_solutions_zero hB'
    (analyticAt_shiftedForcing hB hc hg) hu'.1 hv'.1
    hu'.2.1 hv'.2.1 hu'.2.2 hv'.2.2
  filter_upwards [heq] with x hx
  have h := congrArg (fun a : Fin m → ℝ ↦ a + g (Fin.tail x)) hx
  simpa only [w, sub_add_cancel] using h

end PDE.Analytic.CauchyKovalevskaya
