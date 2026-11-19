/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Variational
public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Regularity
import Mathlib.Analysis.Convex.Integral
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Comparison
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Semigroup
import CAS.IntegrationTactic

/-!
# Autonomous optimal-control representation of Hopf–Lax

We give a one-dimensional autonomous control formulation in the setting of
Evans, §10.3.1, with dynamics `ẋ = a`, running cost `L(a)`, and the datum charged at the free
initial point `y`. A control `a` is admissible from `y` to `x` in time `t`
when it and its Lagrangian cost are interval integrable and

`y + integral_0^t a(s) ds = x`.

Evans takes the controls in a compact set; here they may be unbounded.

Admissibility is a predicate on the
initial state and control. Jensen's inequality shows that every admissible
control costs at least the constant control with the same displacement.
Consequently the control value equals both the Hopf–Lax formula and the
absolutely-continuous-path value from `OneDimensional.HopfLax.Variational`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.3.1-§10.3.2; §10.3.4, formula (44).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HopfLax1D

noncomputable section

set_option linter.missingDocs true

open MeasureTheory Set

/-- A control is admissible when it has finite velocity and Lagrangian
integrals and reaches the prescribed terminal state. -/
def IsAdmissibleControl (H : ℝ → ℝ) (t x y : ℝ) (a : ℝ → ℝ) : Prop :=
  IntervalIntegrable a volume 0 t ∧
    IntervalIntegrable (fun s ↦ legendreTransform H (a s)) volume 0 t ∧
      y + ∫ s in (0 : ℝ)..t, a s = x

/-- Initial cost plus accumulated Lagrangian cost for a control. -/
noncomputable def controlCost (H φ : ℝ → ℝ) (t y : ℝ) (a : ℝ → ℝ) : ℝ :=
  φ y + ∫ s in (0 : ℝ)..t, legendreTransform H (a s)

/-- The set of costs of controls reaching `x` at time `t`. -/
def controlCostSet (H φ : ℝ → ℝ) (t x : ℝ) : Set ℝ :=
  {c | ∃ y a, IsAdmissibleControl H t x y a ∧ controlCost H φ t y a = c}

/-- The value of the autonomous control problem. -/
noncomputable def controlValue (H φ : ℝ → ℝ) (t x : ℝ) : ℝ :=
  sInf (controlCostSet H φ t x)

/-- The autonomous control value on closed forward time.

Positive horizons use the control problem itself. At nonpositive times the
canonical Hopf–Lax extension is used, so the time-zero value is exactly the
initial datum. -/
noncomputable def controlValueEvolution (H φ : ℝ → ℝ) (t x : ℝ) : ℝ :=
  if 0 < t then controlValue H φ t x else hopfLaxEvolution H φ t x

/-- At time zero, the closed-time control evolution is the initial datum. -/
@[simp]
theorem controlValueEvolution_zero (H φ : ℝ → ℝ) (x : ℝ) :
    controlValueEvolution H φ 0 x = φ x := by
  simp [controlValueEvolution]

/-- At positive time, the closed-time control evolution is the control value. -/
theorem controlValueEvolution_of_pos (H φ : ℝ → ℝ) {t x : ℝ} (ht : 0 < t) :
    controlValueEvolution H φ t x = controlValue H φ t x := by
  simp [controlValueEvolution, ht]

/-- At nonpositive time, the control evolution uses the canonical Hopf–Lax
extension. -/
theorem controlValueEvolution_of_nonpos (H φ : ℝ → ℝ) {t x : ℝ} (ht : t ≤ 0) :
    controlValueEvolution H φ t x = hopfLaxEvolution H φ t x := by
  simp [controlValueEvolution, not_lt.mpr ht]

/-- The constant control joining `y` to `x` in positive time is admissible. -/
theorem isAdmissibleControl_const {H : ℝ → ℝ} {t x : ℝ} (ht : 0 < t) (y : ℝ) :
    IsAdmissibleControl H t x y (fun _ ↦ (x - y) / t) := by
  refine ⟨continuous_const.intervalIntegrable 0 t, continuous_const.intervalIntegrable 0 t, ?_⟩
  cas

/-- The constant-control cost is the Hopf–Lax pointwise integrand. -/
theorem controlCost_const (H φ : ℝ → ℝ) {t x : ℝ} (y : ℝ) :
    controlCost H φ t y (fun _ ↦ (x - y) / t) = hopfLaxIntegrand H φ t x y := by
  simp only [controlCost, hopfLaxIntegrand]
  cas

/-- Jensen's inequality bounds the action of a control by the Lagrangian of
its average velocity. -/
theorem lagrangian_displacement_le_control_action {H : ℝ → ℝ} (hFin : LegendreFinite H) {t x y : ℝ}
    (ht : 0 < t) {a : ℝ → ℝ} (ha : IsAdmissibleControl H t x y a) :
    t * legendreTransform H ((x - y) / t) ≤ ∫ s in (0 : ℝ)..t, legendreTransform H (a s) := by
  have hvol : volume.real (Set.Ioc (0 : ℝ) t) = t := by simp [ht.le]
  have hJensen := (convexOn_legendreTransform hFin).map_set_average_le
    (continuous_legendreTransform hFin).continuousOn isClosed_univ
    (by simp [ht] : volume (Set.Ioc (0 : ℝ) t) ≠ 0) (by simp) (by simp)
    (by simpa [uIoc_of_le ht.le] using intervalIntegrable_iff.mp ha.1)
    (by simpa [uIoc_of_le ht.le, Function.comp_def] using intervalIntegrable_iff.mp ha.2.1)
  rw [setAverage_eq, setAverage_eq, hvol, ← intervalIntegral.integral_of_le ht.le,
    ← intervalIntegral.integral_of_le ht.le,
    show ∫ s in (0 : ℝ)..t, a s = x - y by linarith [ha.2.2]] at hJensen
  simp only [smul_eq_mul, ← div_eq_inv_mul] at hJensen
  rw [le_div_iff₀ ht] at hJensen
  linarith

/-- The Hopf–Lax value is a lower bound for every admissible control cost. -/
theorem hopfLax_le_controlCost {H φ : ℝ → ℝ} (hFin : LegendreFinite H) {t x y : ℝ} (ht : 0 < t)
    (hbb : HopfLaxBddBelow H φ t x) {a : ℝ → ℝ} (ha : IsAdmissibleControl H t x y a) :
    hopfLax H φ t x ≤ controlCost H φ t y a :=
  (hopfLax_le_integrand hbb).trans (by
    unfold hopfLaxIntegrand controlCost
    gcongr
    exact lagrangian_displacement_le_control_action hFin ht ha)

/-- Positive time guarantees that the set of admissible control costs is
nonempty. -/
theorem controlCostSet_nonempty (H φ : ℝ → ℝ) {t x : ℝ} (ht : 0 < t) :
    (controlCostSet H φ t x).Nonempty := by
  refine ⟨controlCost H φ t x (fun _ ↦ 0), x, fun _ ↦ 0, ?_, rfl⟩
  simpa only [sub_self, zero_div] using (isAdmissibleControl_const (H := H) (t := t) (x := x) ht x)

/-- A lower bound for the Hopf–Lax integrand also bounds every admissible
control cost. -/
theorem controlCostSet_bddBelow {H φ : ℝ → ℝ} (hFin : LegendreFinite H) {t x : ℝ} (ht : 0 < t)
    (hbb : HopfLaxBddBelow H φ t x) :
    BddBelow (controlCostSet H φ t x) :=
  ⟨hopfLax H φ t x, by rintro c ⟨y, a, ha, rfl⟩; exact hopfLax_le_controlCost hFin ht hbb ha⟩

/-- The autonomous control value is exactly the Hopf–Lax formula. -/
theorem hopfLax_eq_controlValue {H φ : ℝ → ℝ} (hFin : LegendreFinite H) {t x : ℝ} (ht : 0 < t)
    (hbb : HopfLaxBddBelow H φ t x) :
    hopfLax H φ t x = controlValue H φ t x := by
  refine le_antisymm (le_csInf (controlCostSet_nonempty H φ ht) ?_)
    (le_csInf (Set.range_nonempty _) (Set.forall_mem_range.2 fun y ↦ ?_))
  · rintro c ⟨y, a, ha, rfl⟩
    exact hopfLax_le_controlCost hFin ht hbb ha
  · exact (csInf_le (controlCostSet_bddBelow hFin ht hbb)
      ⟨y, _, isAdmissibleControl_const ht y, rfl⟩).trans_eq (controlCost_const H φ y)

/-- The path-space and control-space formulations have the same value. -/
theorem controlValue_eq_variationalValue {H φ : ℝ → ℝ} (hFin : LegendreFinite H) {t x : ℝ}
    (ht : 0 < t) (hbb : HopfLaxBddBelow H φ t x) :
    controlValue H φ t x = variationalValue H φ t x := by
  rw [← hopfLax_eq_controlValue hFin ht hbb, ← hopfLax_eq_variationalValue hFin ht hbb]

/-- Lipschitz initial data supply the bounded-below hypothesis in the
control representation. -/
theorem hopfLax_eq_controlValue_of_lipschitz {H φ : ℝ → ℝ} (hFin : LegendreFinite H) {K : NNReal}
    (hφ : LipschitzWith K φ) {t x : ℝ} (ht : 0 < t) :
    hopfLax H φ t x = controlValue H φ t x :=
  hopfLax_eq_controlValue hFin ht (hopfLaxBddBelow_of_lipschitz hFin hφ ht)

/-- For Lipschitz initial data, the closed-time control evolution is the
canonical Hopf–Lax evolution. -/
theorem controlValueEvolution_eq_hopfLaxEvolution_of_lipschitz {H φ : ℝ → ℝ}
    (hFin : LegendreFinite H) {K : NNReal} (hφ : LipschitzWith K φ) (t x : ℝ) :
    controlValueEvolution H φ t x = hopfLaxEvolution H φ t x := by
  by_cases ht : 0 < t
  · rw [controlValueEvolution_of_pos H φ ht, hopfLaxEvolution_of_ne_zero H φ (ne_of_gt ht)]
    exact (hopfLax_eq_controlValue_of_lipschitz hFin hφ ht).symm
  · exact controlValueEvolution_of_nonpos H φ (le_of_not_gt ht)

/-- The closed-time control evolution preserves the spatial Lipschitz
constant of the initial datum. -/
theorem controlValueEvolution_lipschitzWith_space_of_lipschitz {H φ : ℝ → ℝ}
    (hFin : LegendreFinite H) {K : NNReal} (hφ : LipschitzWith K φ) {t : ℝ} (ht : 0 ≤ t) :
    LipschitzWith K (fun x ↦ controlValueEvolution H φ t x) := by
  simpa only [controlValueEvolution_eq_hopfLaxEvolution_of_lipschitz hFin hφ] using
    hopfLaxEvolution_lipschitzWith_space_of_lipschitz hFin hφ ht

/-- Closed-time autonomous control evolutions form a semigroup on
nonnegative times. -/
theorem controlValueEvolution_semigroup_of_lipschitz {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) {t s x : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    controlValueEvolution H φ (t + s) x =
      controlValueEvolution H (fun z ↦ controlValueEvolution H φ s z) t x := by
  simp only [controlValueEvolution_eq_hopfLaxEvolution_of_lipschitz hFin hφ]
  rw [controlValueEvolution_eq_hopfLaxEvolution_of_lipschitz hFin
    (hopfLaxEvolution_lipschitzWith_space_of_lipschitz hFin hφ hs)]
  exact hopfLaxEvolution_semigroup_of_lipschitz hFin hφ ht hs

/-- Dynamic programming for the closed-time control evolution at an
intermediate time `s ∈ [0, t]`. -/
theorem controlValueEvolution_dynamic_programming_of_lipschitz {H φ : ℝ → ℝ}
    (hFin : LegendreFinite H) {K : NNReal} (hφ : LipschitzWith K φ) {s t x : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) :
    controlValueEvolution H φ t x =
      controlValueEvolution H (fun z ↦ controlValueEvolution H φ s z) (t - s) x := by
  simpa only [sub_add_cancel] using
    controlValueEvolution_semigroup_of_lipschitz hFin hφ (sub_nonneg.mpr hst) hs (x := x)

/-- Bellman's dynamic-programming identity for the autonomous control value.

Both time intervals are positive because `controlValue` is the unpatched
positive-time value function; the closed-time Hopf–Lax evolution handles the
zero-time endpoints separately. -/
theorem controlValue_dynamic_programming_of_lipschitz {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) {s t x : ℝ} (hs : 0 < s) (hst : s < t) :
    controlValue H φ t x = controlValue H (fun z ↦ controlValue H φ s z) (t - s) x := by
  have ht := hs.trans hst
  have hτ := sub_pos.mpr hst
  have hinner : (fun z ↦ hopfLax H φ s z) = fun z ↦ controlValue H φ s z :=
    funext fun z ↦ hopfLax_eq_controlValue_of_lipschitz hFin hφ hs
  have hLip := hopfLax_lipschitzWith_space_of_lipschitz hFin hφ hs
  rw [← hopfLax_eq_controlValue_of_lipschitz hFin hφ ht, ← hinner,
    ← hopfLax_eq_controlValue_of_lipschitz hFin hLip hτ]
  simpa only [sub_add_cancel] using hopfLax_semigroup (x := x) hFin hτ hs
    (by simpa only [sub_add_cancel] using hopfLaxBddBelow_of_lipschitz hFin hφ ht)
    (fun z ↦ hopfLaxBddBelow_of_lipschitz hFin hφ hs) (hopfLaxBddBelow_of_lipschitz hFin hLip hτ)

/-- For Lipschitz initial data, an optimal control exists and may be chosen
constant. -/
theorem exists_controlValue_eq_controlCost_of_lipschitz {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) {t x : ℝ} (ht : 0 < t) :
    ∃ y a, IsAdmissibleControl H t x y a ∧ controlValue H φ t x = controlCost H φ t y a := by
  obtain ⟨y, hy⟩ := exists_hopfLax_eq_integrand_of_lipschitz (x := x) hFin hφ ht
  exact ⟨y, _, isAdmissibleControl_const ht y, ((hopfLax_eq_controlValue_of_lipschitz hFin hφ
    ht).symm.trans hy).trans (controlCost_const H φ y).symm⟩

end

end HopfLax1D
