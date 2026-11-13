/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analytic.CauchyKovalevskaya.Solution.InitialData

/-!
# Explicit time dependence in the analytic Cauchy system

Adjoining a clock state converts explicit time dependence into state dependence;
Evans does the same after (15) in §4.6.3 with the extra component `u^{m+1} = xₙ`.
The clock equation and its initial trace determine the clock as the time
coordinate by analytic germ uniqueness.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3, after (15).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Topology
open Filter

noncomputable section

namespace PDE.Analytic.CauchyKovalevskaya

variable {d m : ℕ}

/-- Read time, state, and spatial position from a state enlarged by one clock component. -/
def timeArguments (z : (Fin (m + 1) ⊕ Fin d) → ℝ) :
    ℝ × ((Fin m ⊕ Fin d) → ℝ) :=
  (z (.inl 0), Sum.elim (fun i ↦ z (.inl i.succ)) (fun j ↦ z (.inr j)))

/-- Principal coefficients for the enlarged system; the clock row and column vanish. -/
def clockCoefficients
    (B : Fin d → Fin m → Fin m → (ℝ × ((Fin m ⊕ Fin d) → ℝ)) → ℝ)
    (j : Fin d) (i k : Fin (m + 1)) (z : (Fin (m + 1) ⊕ Fin d) → ℝ) : ℝ :=
  Fin.cases 0 (fun i ↦ Fin.cases 0 (fun k ↦ B j i k (timeArguments z)) k) i

/-- The clock has unit forcing, while the other components retain the original forcing. -/
def clockForcing
    (c : Fin m → (ℝ × ((Fin m ⊕ Fin d) → ℝ)) → ℝ)
    (i : Fin (m + 1)) (z : (Fin (m + 1) ⊕ Fin d) → ℝ) : ℝ :=
  Fin.cases 1 (fun i ↦ c i (timeArguments z)) i

/-- The right-hand side with coefficients depending explicitly on time. -/
def timeDependentRightHandSide
    (B : Fin d → Fin m → Fin m → (ℝ × ((Fin m ⊕ Fin d) → ℝ)) → ℝ)
    (c : Fin m → (ℝ × ((Fin m ⊕ Fin d) → ℝ)) → ℝ)
    (u : (Fin (d + 1) → ℝ) → Fin m → ℝ) (i : Fin m)
    (x : Fin (d + 1) → ℝ) : ℝ :=
  (∑ j, ∑ k, B j i k (x 0, arguments u x) *
    fderiv ℝ (fun y ↦ u y k) x (Pi.single j.succ 1)) + c i (x 0, arguments u x)

/-- Extracting the clock and the remaining coordinates is analytic. -/
theorem analyticAt_timeArguments (z : (Fin (m + 1) ⊕ Fin d) → ℝ) :
    AnalyticAt ℝ (timeArguments (d := d) (m := m)) z := by
  let L : (((Fin (m + 1) ⊕ Fin d) → ℝ) →L[ℝ] ((Fin m ⊕ Fin d) → ℝ)) :=
    ContinuousLinearMap.pi (fun i ↦ Sum.elim
      (fun i ↦ ContinuousLinearMap.proj (.inl i.succ))
      (fun j ↦ ContinuousLinearMap.proj (.inr j)) i)
  let T : (((Fin (m + 1) ⊕ Fin d) → ℝ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.proj (.inl 0)
  have h : timeArguments = (T.prod L) := by
    funext x
    apply Prod.ext
    · rfl
    · funext i
      cases i <;> rfl
  rw [h]
  exact (T.prod L).analyticAt z

/-- Adjoining the clock preserves analyticity of the principal coefficients. -/
theorem analyticAt_clockCoefficients
    {B : Fin d → Fin m → Fin m → (ℝ × ((Fin m ⊕ Fin d) → ℝ)) → ℝ}
    {z : (Fin (m + 1) ⊕ Fin d) → ℝ}
    (hB : ∀ j i k, AnalyticAt ℝ (B j i k) (timeArguments z))
    (j : Fin d) (i k : Fin (m + 1)) :
    AnalyticAt ℝ (clockCoefficients B j i k) z := by
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · exact analyticAt_const
  · refine Fin.cases ?_ (fun k ↦ ?_) k
    · exact analyticAt_const
    · exact (hB j i k).comp (analyticAt_timeArguments z)

/-- Adjoining the clock preserves analyticity of the forcing. -/
theorem analyticAt_clockForcing
    {c : Fin m → (ℝ × ((Fin m ⊕ Fin d) → ℝ)) → ℝ}
    {z : (Fin (m + 1) ⊕ Fin d) → ℝ}
    (hc : ∀ i, AnalyticAt ℝ (c i) (timeArguments z)) (i : Fin (m + 1)) :
    AnalyticAt ℝ (clockForcing c i) z := by
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · exact analyticAt_const
  · exact (hc i).comp (analyticAt_timeArguments z)

/-- The enlarged clock equation has right-hand side one for every state. -/
theorem rightHandSide_clock_zero
    (B : Fin d → Fin m → Fin m → (ℝ × ((Fin m ⊕ Fin d) → ℝ)) → ℝ)
    (c : Fin m → (ℝ × ((Fin m ⊕ Fin d) → ℝ)) → ℝ)
    (v : (Fin (d + 1) → ℝ) → Fin (m + 1) → ℝ) (x : Fin (d + 1) → ℝ) :
    rightHandSide (clockCoefficients B) (clockForcing c) v 0 x = 1 := by
  simp [rightHandSide, clockCoefficients, clockForcing]

/-- Once the clock equals time, the remaining equations are exactly the
original equations with explicit time dependence. -/
theorem rightHandSide_clock_succ
    (B : Fin d → Fin m → Fin m → (ℝ × ((Fin m ⊕ Fin d) → ℝ)) → ℝ)
    (c : Fin m → (ℝ × ((Fin m ⊕ Fin d) → ℝ)) → ℝ)
    (v : (Fin (d + 1) → ℝ) → Fin (m + 1) → ℝ)
    (x : Fin (d + 1) → ℝ) (ht : v x 0 = x 0) (i : Fin m) :
    rightHandSide (clockCoefficients B) (clockForcing c) v i.succ x =
      timeDependentRightHandSide B c (fun y ↦ Fin.tail (v y)) i x := by
  have hargs : timeArguments (arguments v x) =
      (x 0, arguments (fun y ↦ Fin.tail (v y)) x) := by
    exact Prod.ext ht rfl
  simp [rightHandSide, clockCoefficients, clockForcing, Fin.sum_univ_succ,
    hargs, timeDependentRightHandSide, Fin.tail]

private theorem eventuallyEq_time_of_analyticAt
    {w : (Fin (d + 1) → ℝ) → ℝ} (hw : AnalyticAt ℝ w 0)
    (ht : (fun x : Fin d → ℝ ↦ w (Fin.cons 0 x)) =ᶠ[𝓝 0] 0)
    (he : (fun x ↦ fderiv ℝ w x (Pi.single 0 1)) =ᶠ[𝓝 0] 1) :
    w =ᶠ[𝓝 0] fun x ↦ x 0 := by
  let T : (Fin (d + 1) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hT (x : Fin (d + 1) → ℝ) :
      fderiv ℝ (fun y ↦ y 0) x (Pi.single 0 1) = 1 := by
    change fderiv ℝ T x (Pi.single 0 1) = 1
    rw [T.fderiv]
    simp [T]
  have hEq := eventuallyEq_of_analytic_solutions_zero
    (B := fun (_ : Fin d) (_ _ : Fin 1) (_ : (Fin 1 ⊕ Fin d) → ℝ) ↦ 0)
    (c := fun (_ : Fin 1) (_ : (Fin 1 ⊕ Fin d) → ℝ) ↦ 1)
    (u := fun x _ ↦ w x) (v := fun x _ ↦ x 0)
    (fun _ _ _ ↦ analyticAt_const) (fun _ ↦ analyticAt_const)
    (fun _ ↦ hw) (fun _ ↦ T.analyticAt 0)
    (fun _ ↦ ht) (fun _ ↦ Filter.Eventually.of_forall (fun _ ↦ rfl))
    (fun _ ↦ by
      filter_upwards [he] with x hx
      simpa only [rightHandSide, zero_mul, Finset.sum_const_zero, zero_add] using! hx)
    (fun _ ↦ Filter.Eventually.of_forall (fun x ↦ by
      simpa only [rightHandSide, zero_mul, Finset.sum_const_zero, zero_add] using hT x))
  filter_upwards [hEq] with x hx
  exact congrFun hx 0

/-- Explicitly time-dependent analytic coefficients and analytic Cauchy data
admit an analytic solution on a ball of positive radius. The clock is shown to
equal time from its equation and initial trace. -/
theorem exists_analytic_solution_time_dependent
    (B : Fin d → Fin m → Fin m → (ℝ × ((Fin m ⊕ Fin d) → ℝ)) → ℝ)
    (c : Fin m → (ℝ × ((Fin m ⊕ Fin d) → ℝ)) → ℝ)
    (g : (Fin d → ℝ) → Fin m → ℝ)
    (hB : ∀ j i k, AnalyticAt ℝ (B j i k) (0, Sum.elim (g 0) 0))
    (hc : ∀ i, AnalyticAt ℝ (c i) (0, Sum.elim (g 0) 0))
    (hg : AnalyticAt ℝ g 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ u : (Fin (d + 1) → ℝ) → Fin m → ℝ,
      AnalyticOnNhd ℝ u (Metric.ball 0 r) ∧
      (∀ x ∈ Metric.ball (0 : Fin d → ℝ) r, u (Fin.cons 0 x) = g x) ∧
      ∀ x ∈ Metric.ball 0 r, ∀ i,
        fderiv ℝ (fun y ↦ u y i) x (Pi.single 0 1) =
          timeDependentRightHandSide B c u i x := by
  let G (x : Fin d → ℝ) : Fin (m + 1) → ℝ := Fin.cons 0 (g x)
  have hG : AnalyticAt ℝ G 0 := by
    apply AnalyticAt.pi
    intro i
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · exact analyticAt_const
    · exact ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).analyticAt _).comp hg
  have hcenter : timeArguments (d := d) (Sum.elim (G 0) 0) =
      (0, Sum.elim (g 0) 0) := rfl
  have hB' (j : Fin d) (i k : Fin (m + 1)) :
      AnalyticAt ℝ (clockCoefficients B j i k) (Sum.elim (G 0) 0) :=
    analyticAt_clockCoefficients (by simpa only [hcenter] using hB) j i k
  have hc' (i : Fin (m + 1)) :
      AnalyticAt ℝ (clockForcing c i) (Sum.elim (G 0) 0) :=
    analyticAt_clockForcing (by simpa only [hcenter] using hc) i
  obtain ⟨r, hr, v, hva, hvt, hve⟩ :=
    exists_analytic_solution (clockCoefficients B) (clockForcing c) G hB' hc' hG
  have hv0 := hva 0 (Metric.mem_ball_self hr)
  have ht : (fun x ↦ v x 0) =ᶠ[𝓝 0] fun x ↦ x 0 := by
    apply eventuallyEq_time_of_analyticAt
      (((ContinuousLinearMap.proj 0 : (Fin (m + 1) → ℝ) →L[ℝ] ℝ).analyticAt _).comp hv0)
    · filter_upwards [Metric.ball_mem_nhds 0 hr] with x hx
      exact congrFun (hvt x hx) 0
    · filter_upwards [Metric.ball_mem_nhds 0 hr] with x hx
      exact (hve x hx 0).trans (rightHandSide_clock_zero B c v x)
  let U (x : Fin (d + 1) → ℝ) := Fin.tail (v x)
  let L : (Fin (m + 1) → ℝ) →L[ℝ] (Fin m → ℝ) :=
    ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.proj i.succ)
  have hEq : ∀ᶠ x in 𝓝 0, ∀ i,
      fderiv ℝ (fun y ↦ U y i) x (Pi.single 0 1) =
        timeDependentRightHandSide B c U i x := by
    filter_upwards [Metric.ball_mem_nhds 0 hr, ht] with x hx htx
    exact fun i ↦ (hve x hx i.succ).trans (rightHandSide_clock_succ B c v x htx i)
  obtain ⟨s, hs, hse⟩ := Metric.mem_nhds_iff.mp hEq
  refine ⟨min r s, lt_min hr hs, U, ?_, ?_, ?_⟩
  · intro x hx
    exact (L.analyticAt _).comp (hva x (Metric.ball_subset_ball (min_le_left _ _) hx))
  · intro x hx
    exact congrArg Fin.tail (hvt x (Metric.ball_subset_ball (min_le_left _ _) hx))
  · intro x hx i
    exact hse (Metric.ball_subset_ball (min_le_right _ _) hx) i

/-- Analytic solutions of the explicitly time-dependent Cauchy system with the
same analytic initial data agree on a neighborhood of the origin. -/
theorem eventuallyEq_of_analytic_solutions_time_dependent
    {B : Fin d → Fin m → Fin m → (ℝ × ((Fin m ⊕ Fin d) → ℝ)) → ℝ}
    {c : Fin m → (ℝ × ((Fin m ⊕ Fin d) → ℝ)) → ℝ}
    {g : (Fin d → ℝ) → Fin m → ℝ}
    (hB : ∀ j i k, AnalyticAt ℝ (B j i k) (0, Sum.elim (g 0) 0))
    (hc : ∀ i, AnalyticAt ℝ (c i) (0, Sum.elim (g 0) 0))
    (hg : AnalyticAt ℝ g 0)
    {u v : (Fin (d + 1) → ℝ) → Fin m → ℝ}
    (hu : AnalyticAt ℝ u 0) (hv : AnalyticAt ℝ v 0)
    (hutrace : (fun x : Fin d → ℝ ↦ u (Fin.cons 0 x)) =ᶠ[𝓝 0] g)
    (hvtrace : (fun x : Fin d → ℝ ↦ v (Fin.cons 0 x)) =ᶠ[𝓝 0] g)
    (hueq : ∀ i, (fun x ↦ fderiv ℝ (fun y ↦ u y i) x (Pi.single 0 1))
      =ᶠ[𝓝 0] timeDependentRightHandSide B c u i)
    (hveq : ∀ i, (fun x ↦ fderiv ℝ (fun y ↦ v y i) x (Pi.single 0 1))
      =ᶠ[𝓝 0] timeDependentRightHandSide B c v i) :
    u =ᶠ[𝓝 0] v := by
  let G (x : Fin d → ℝ) : Fin (m + 1) → ℝ := Fin.cons 0 (g x)
  have hG : AnalyticAt ℝ G 0 := by
    apply AnalyticAt.pi
    intro i
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · exact analyticAt_const
    · exact ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).analyticAt _).comp hg
  have hcenter : timeArguments (d := d) (Sum.elim (G 0) 0) =
      (0, Sum.elim (g 0) 0) := rfl
  have hB' (j : Fin d) (i k : Fin (m + 1)) :
      AnalyticAt ℝ (clockCoefficients B j i k) (Sum.elim (G 0) 0) :=
    analyticAt_clockCoefficients (by simpa only [hcenter] using hB) j i k
  have hc' (i : Fin (m + 1)) :
      AnalyticAt ℝ (clockForcing c i) (Sum.elim (G 0) 0) :=
    analyticAt_clockForcing (by simpa only [hcenter] using hc) i
  let T : (Fin (d + 1) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  let W (z : (Fin (d + 1) → ℝ) → Fin m → ℝ) (x : Fin (d + 1) → ℝ) :
      Fin (m + 1) → ℝ := Fin.cons (x 0) (z x)
  have hWa (z : (Fin (d + 1) → ℝ) → Fin m → ℝ) (hz : AnalyticAt ℝ z 0) :
      AnalyticAt ℝ (W z) 0 := by
    apply AnalyticAt.pi
    intro i
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · exact T.analyticAt 0
    · exact ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).analyticAt _).comp hz
  have hWt (z : (Fin (d + 1) → ℝ) → Fin m → ℝ)
      (ht : (fun x : Fin d → ℝ ↦ z (Fin.cons 0 x)) =ᶠ[𝓝 0] g) :
      (fun x : Fin d → ℝ ↦ W z (Fin.cons 0 x)) =ᶠ[𝓝 0] G := by
    filter_upwards [ht] with x hx
    simp only [W, G, Fin.cons_zero, hx]
  have hWe (z : (Fin (d + 1) → ℝ) → Fin m → ℝ)
      (he : ∀ i, (fun x ↦ fderiv ℝ (fun y ↦ z y i) x (Pi.single 0 1))
        =ᶠ[𝓝 0] timeDependentRightHandSide B c z i) :
      ∀ i, (fun x ↦ fderiv ℝ (fun y ↦ W z y i) x (Pi.single 0 1))
        =ᶠ[𝓝 0] rightHandSide (clockCoefficients B) (clockForcing c) (W z) i := by
    intro i
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · apply Filter.Eventually.of_forall
      intro x
      change fderiv ℝ T x (Pi.single 0 1) = _
      rw [T.fderiv, rightHandSide_clock_zero]
      simp [T]
    · filter_upwards [he i] with x hx
      rw [rightHandSide_clock_succ B c (W z) x rfl i]
      exact hx
  have heq := eventuallyEq_of_analytic_solutions hB' hc' hG
    (hWa u hu) (hWa v hv) (hWt u hutrace) (hWt v hvtrace) (hWe u hueq) (hWe v hveq)
  filter_upwards [heq] with x hx
  exact congrArg Fin.tail hx

end PDE.Analytic.CauchyKovalevskaya
