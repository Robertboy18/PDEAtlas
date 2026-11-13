/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.LionsMagenes.Regularity.LocalRepresentative -- shake: keep

/-!
# Continuous representatives on open time intervals

Given `u ∈ L²(a, b; V)` with Gelfand weak derivative `g ∈ L²(a, b; V*)`, the file
`PDE.Analysis.Evolution.LionsMagenes.Regularity.LocalRepresentative` produces, on each
compact subinterval `[c, d] ⊆ (a, b)`, an `H`-continuous representative of `u` with the
integrated derivative and energy identity. Two such representatives agree on the overlap
of their intervals, because both are continuous and both equal `i(u t)` for a.e. `t`
there. We glue them into a single continuous representative on the open interval
`(a, b)`. Around every `t ∈ (a, b)` the chart `[(a + t)/2, (t + b)/2]` is used; evaluating
each point's own chart at that point defines the representative, continuity at `t`
follows from local agreement with the fixed chart centred at `t`, and the countable
exhaustion `⋃ₙ (a + (b-a)/(n+2), b - (b-a)/(n+2)) = (a, b)` by open subintervals with
closure in `(a, b)` shows that the glued function is a.e. equal to `i ∘ u` on `(a, b)`.

The result, `ContinuousPivotEvolutionOnOpen`, is the interior statement of the theorem
`u ∈ L²(0, T; V)`, `u' ∈ L²(0, T; V*) ⟹ u ∈ C([0, T]; H)`, the abstract form of Evans
§5.9.2, Theorem 3(i); the
extension to the closed interval is the subject of the `EndpointRegularity` files.

## Main results

* `interiorIntervalExhaustion`, `iUnion_interiorIntervalExhaustion`,
  `interiorIntervalExhaustion_endpoints`: the countable exhaustion of `(a, b)` by the open
  subintervals `(a + (b-a)/(n+2), b - (b-a)/(n+2))` and its elementary properties.
* `HasWeakTimeDerivativeOn.interiorPivotChart`: the compact chart centred at an
  interior time.
* `HasWeakTimeDerivativeOn.interiorPivotRepresentative`,
  `continuousOn_interiorPivotRepresentative`, `interiorPivotRepresentative_ae_eq`: the
  glued representative, its continuity on `(a, b)`, and its a.e. identification with
  `t ↦ i(u t)`.
* `HasWeakTimeDerivativeOn.nonempty_continuousPivotEvolutionOnOpen`: the
  open-interval Lions–Magenes evolution.

## Implementation notes

`interiorPivotRepresentative` is set to `0` outside `(a, b)` purely so that it is a total
function; nothing is claimed about it there. The chart for the point `t` is chosen by
`Classical.choice` from the nonemptiness statement of the local theorem, so the
representative is not computable, and its independence of the choice is exactly the
overlap-uniqueness argument.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2, Theorem 3. <https://doi.org/10.1090/gsm/019>
* J.-L. Lions and E. Magenes, *Non-Homogeneous Boundary Value Problems and Applications*,
  Vol. I, Springer, 1972, Chapter 1 (Hilbert theory of trace and interpolation spaces).
  <https://doi.org/10.1007/978-3-642-65161-8>
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace PDE.Analysis.Evolution

section GelfandWeakTimeDerivative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The standard countable exhaustion of `(a,b)` by intervals staying a
distance `(b-a)/(n+2)` from each endpoint. -/
def interiorIntervalExhaustion (a b : ℝ) (n : ℕ) : Set ℝ :=
  Set.Ioo (a + (b - a) / (n + 2 : ℝ))
    (b - (b - a) / (n + 2 : ℝ))

/-- The compactly contained intervals `interiorIntervalExhaustion a b n`
cover the whole open interval when `a < b`. -/
theorem iUnion_interiorIntervalExhaustion {a b : ℝ} (hab : a < b) :
    (⋃ n : ℕ, interiorIntervalExhaustion a b n) = Set.Ioo a b := by
  ext x
  simp only [mem_iUnion, interiorIntervalExhaustion, mem_Ioo]
  constructor
  · rintro ⟨n, h₁, h₂⟩
    have : 0 < (b - a) / (n + 2 : ℝ) := div_pos (sub_pos.2 hab) (by positivity)
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hxa, hxb⟩
    have hε : 0 < min (x - a) (b - x) := lt_min (sub_pos.2 hxa) (sub_pos.2 hxb)
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ((b - a) / min (x - a) (b - x))
    have hsmall : (b - a) / (N + 2 : ℝ) < min (x - a) (b - x) := by
      rw [div_lt_iff₀ hε] at hN
      rw [div_lt_iff₀ (by positivity)]
      linarith
    exact ⟨N, by linarith [min_le_left (x - a) (b - x)],
      by linarith [min_le_right (x - a) (b - x)]⟩

/-- Every member of the standard exhaustion is compactly contained in the
ambient interval (the first member is the empty interval `Ioo m m` at the
midpoint). -/
theorem interiorIntervalExhaustion_endpoints {a b : ℝ} (hab : a < b) (n : ℕ) :
    a < a + (b - a) / (n + 2 : ℝ) ∧
    a + (b - a) / (n + 2 : ℝ) ≤
      b - (b - a) / (n + 2 : ℝ) ∧
    b - (b - a) / (n + 2 : ℝ) < b := by
  have hgap : 0 < (b - a) / (n + 2 : ℝ) := div_pos (sub_pos.2 hab) (by positivity)
  have htwice : 2 * ((b - a) / (n + 2 : ℝ)) ≤ b - a := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    linarith [mul_nonneg (sub_pos.2 hab).le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The canonical compact chart centered at an interior time.  Its endpoints
are halfway from `t` to the endpoints of `(a,b)`, so `t` lies strictly in the
chart interior. -/
noncomputable def HasWeakTimeDerivativeOn.interiorPivotChart
    [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h : HasWeakTimeDerivativeOn (Set.Ioo a b)
      (fun t ↦ T.energyToDual (u t)) (fun t ↦ g t))
    (t : ℝ) (ht : t ∈ Set.Ioo a b) :
    ContinuousPivotEvolutionOn T (fun s ↦ u s) (fun s ↦ g s)
      ((a + t) / 2) ((t + b) / 2) :=
  (h.exists_continuous_representativeOn
    (by linarith [ht.1]) (by linarith [ht.1, ht.2]) (by linarith [ht.2])).some

/-- The interior pivot representative obtained by evaluating the canonical
local chart at each interior time.  It is set to zero outside `(a,b)` only to
make it an everywhere-defined Lean function; all mathematical claims below
are restricted to the open interval. -/
noncomputable def HasWeakTimeDerivativeOn.interiorPivotRepresentative
    [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h : HasWeakTimeDerivativeOn (Set.Ioo a b)
      (fun t ↦ T.energyToDual (u t)) (fun t ↦ g t)) : ℝ → H :=
  fun t ↦ if ht : t ∈ Set.Ioo a b then
    (h.interiorPivotChart t ht).representative t
  else 0

/-- The glued representative agrees with every compact chart at the interior points of that
chart, by overlap uniqueness with the chart centred at the point. -/
private theorem interiorPivotRepresentative_eq_of_mem_Ioo
    [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b c d x : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h : HasWeakTimeDerivativeOn (Set.Ioo a b)
      (fun t ↦ T.energyToDual (u t)) (fun t ↦ g t))
    (E : ContinuousPivotEvolutionOn T (fun r ↦ u r) (fun r ↦ g r) c d)
    (hxab : x ∈ Ioo a b) (hx : x ∈ Ioo c d) :
    h.interiorPivotRepresentative x = E.representative x := by
  rw [HasWeakTimeDerivativeOn.interiorPivotRepresentative, dite_eq_left hxab]
  exact (h.interiorPivotChart x hxab).representative_eq_of_mem_Ioo E
    (by linarith [hxab.1, hxab.2]) (hx.1.le.trans hx.2.le)
    ⟨by linarith [hxab.1], by linarith [hxab.2]⟩ hx

/-- The chartwise representative is strongly continuous throughout the open
time interval.  Overlap uniqueness makes it locally equal to the single
compact chart centered at the point under consideration. -/
theorem HasWeakTimeDerivativeOn.continuousOn_interiorPivotRepresentative
    [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h : HasWeakTimeDerivativeOn (Set.Ioo a b)
      (fun t ↦ T.energyToDual (u t)) (fun t ↦ g t)) :
    ContinuousOn h.interiorPivotRepresentative (Set.Ioo a b) := by
  intro t ht
  have hct : (a + t) / 2 < t := by linarith [ht.1]
  have htd : t < (t + b) / 2 := by linarith [ht.2]
  let E := h.interiorPivotChart t ht
  refine ((E.continuousOn.continuousAt ?_).congr_of_eventuallyEq ?_).continuousWithinAt
  · rw [uIcc_of_le (hct.trans htd).le]
    exact Icc_mem_nhds hct htd
  · filter_upwards [Ioo_mem_nhds hct htd] with x hx
    exact interiorPivotRepresentative_eq_of_mem_Ioo h E
      ⟨by linarith [ht.1, hx.1], by linarith [ht.2, hx.2]⟩ hx

/-- The glued interior representative belongs to the original Bochner
equivalence class on `(a,b)`.  The proof uses the countable exhaustion above;
on each member the glued function agrees pointwise with one compact chart,
which is almost everywhere equal to the original trajectory. -/
theorem HasWeakTimeDerivativeOn.interiorPivotRepresentative_ae_eq
    [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h : HasWeakTimeDerivativeOn (Set.Ioo a b)
      (fun t ↦ T.energyToDual (u t)) (fun t ↦ g t)) (hab : a < b) :
    h.interiorPivotRepresentative =ᵐ[volume.restrict (Set.Ioo a b)]
      fun t ↦ T.inclusion (u t) := by
  -- on each member of the exhaustion the glued function is one compact chart
  have hlocal (n : ℕ) : h.interiorPivotRepresentative
      =ᵐ[volume.restrict (interiorIntervalExhaustion a b n)] fun t ↦ T.inclusion (u t) := by
    obtain ⟨hac, hcd, hdb⟩ := interiorIntervalExhaustion_endpoints hab n
    let E := (h.exists_continuous_representativeOn hac hcd hdb).some
    exact Filter.EventuallyEq.trans (ae_restrict_of_forall_mem measurableSet_Ioo fun x hx ↦
      interiorPivotRepresentative_eq_of_mem_Ioo h E ⟨hac.trans hx.1, hx.2.trans hdb⟩ hx)
        (E.ae_eq_inclusion.filter_mono (ae_mono (Measure.restrict_mono_set _
          fun x hx ↦ Icc_subset_uIcc (Ioo_subset_Icc_self hx))))
  rw [← iUnion_interiorIntervalExhaustion hab]
  exact (ae_eq_restrict_iUnion_iff _ _ _).2 hlocal

/-- Open-interval Lions–Magenes theorem for a finite-time weak Gelfand
trajectory.  The compact representatives are glued by overlap uniqueness
into one `H`-continuous representative on `(a,b)`.  It is almost everywhere
the original Bochner trajectory and satisfies both the integrated `V*`
fundamental theorem and the exact energy identity between arbitrary interior
times. -/
theorem HasWeakTimeDerivativeOn.nonempty_continuousPivotEvolutionOnOpen
    [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h : HasWeakTimeDerivativeOn (Set.Ioo a b)
      (fun t ↦ T.energyToDual (u t)) (fun t ↦ g t)) (hab : a < b) :
    Nonempty (ContinuousPivotEvolutionOnOpen T
      (fun t ↦ u t) (fun t ↦ g t) a b) := by
  let uH : ℝ → H := h.interiorPivotRepresentative
  have hchart : ∀ s t, s ∈ Ioo a b → t ∈ Ioo a b →
      ∃ (c d : ℝ) (E : ContinuousPivotEvolutionOn T (fun r ↦ u r) (fun r ↦ g r) c d),
        s ∈ Ioo c d ∧ t ∈ Ioo c d ∧ EqOn uH E.representative (uIcc s t) := by
    intro s t hs ht
    have h₁ := min_le_left s t
    have h₂ := min_le_right s t
    have h₃ := le_max_left s t
    have h₄ := le_max_right s t
    have hamin : a < min s t := lt_min hs.1 ht.1
    have hmaxb : max s t < b := max_lt hs.2 ht.2
    let E := (h.exists_continuous_representativeOn (c := (a + min s t) / 2)
      (d := (max s t + b) / 2) (by linarith) (by linarith) (by linarith)).some
    refine ⟨_, _, E, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, fun r hr ↦ ?_⟩
    have hr' : min s t ≤ r ∧ r ≤ max s t := by simpa only [uIcc, mem_Icc] using hr
    exact interiorPivotRepresentative_eq_of_mem_Ioo h E ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩
  refine ⟨{
    representative := uH
    continuousOn := h.continuousOn_interiorPivotRepresentative
    ae_eq_inclusion := h.interiorPivotRepresentative_ae_eq hab
    integratedDerivative := fun s t hs ht ↦ ?_
    energyIdentity := fun s t hs ht ↦ ?_ }⟩
  · obtain ⟨c, d, E, hsE, htE, heq⟩ := hchart s t hs ht
    have hsub := E.integratedDerivative.subinterval (Icc_subset_uIcc (Ioo_subset_Icc_self hsE))
      (Icc_subset_uIcc (Ioo_subset_Icc_self htE))
    exact ⟨hsub.intervalIntegrable, fun r hr ↦ by
      rw [heq hr, heq left_mem_uIcc]
      exact hsub.eq_add_integral r hr⟩
  · obtain ⟨c, d, E, hsE, htE, heq⟩ := hchart s t hs ht
    rw [heq right_mem_uIcc, heq left_mem_uIcc]
    exact E.energyIdentity s t (Icc_subset_uIcc (Ioo_subset_Icc_self hsE))
      (Icc_subset_uIcc (Ioo_subset_Icc_self htE))

end GelfandWeakTimeDerivative

end PDE.Analysis.Evolution
