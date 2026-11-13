/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean.SpaceTime
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import PDE.Analysis.MeasureTheory.StronglyMeasurable.Hilbert
import PDE.FDeriv.SpaceTime
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Square-integrable time curves of spatial slices

A spacetime function that is continuous on the open slab `(0,T) × ℝ^n` and has square-integrable
slices at positive times defines a curve of `L²` classes. Testing against a fixed `L²` class
gives a measurable function of time by Fubini, so the curve is almost everywhere strongly
measurable by the Pettis theorem in the separable Hilbert space `L²`. An integrable bound on
the squared slice norms then puts the curve in `L²(0,T; L²)`.
-/

@[expose] public section

namespace PDE.Analysis

open EuclideanSpace MeasureTheory Filter PDE.Common
open scoped Topology

set_option linter.missingDocs true

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The curve of `L²` slices of a function continuous on the open slab, with an integrable
bound on the squared slice norms, is square integrable in time. -/
theorem memLp_two_sliceCurve {D : ℝ^(n + 1) → E} {T : ℝ}
    (hD : ∀ {t : ℝ}, t ∈ Set.Ioc 0 T → MemLp (fun x ↦ D (timeSpaceCons t x)) 2 volume)
    (hcont : ContinuousOn D {z | 0 < z 0 ∧ z 0 < T}) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Set.Ioc 0 T))
    (hle : ∀ t ∈ Set.Ioc 0 T,
      (eLpNorm (fun x ↦ D (timeSpaceCons t x)) 2 volume).toReal ^ 2 ≤ g t) :
    MemLp (fun t ↦ if ht : t ∈ Set.Ioc 0 T then (hD ht).toLp (fun x ↦ D (timeSpaceCons t x))
      else 0) 2 (volume.restrict (Set.Icc 0 T)) := by
  set F : ℝ → Lp E 2 (volume : Measure (ℝ^n)) := fun t ↦
    if ht : t ∈ Set.Ioc 0 T then (hD ht).toLp (fun x ↦ D (timeSpaceCons t x)) else 0
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc.symm]
  rw [IntegrableOn, Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm] at hg
  have hmeas : AEStronglyMeasurable F (volume.restrict (Set.Ioo 0 T)) := by
    have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
    apply aestronglyMeasurable_of_forall_inner
    intro v
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ^n ↦ (v : ℝ^n → E) p.2)
        ((volume.restrict (Set.Ioo 0 T)).prod volume) :=
      (Lp.aestronglyMeasurable v).comp_snd
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ^n ↦ D (timeSpaceCons p.1 p.2))
        ((volume.restrict (Set.Ioo 0 T)).prod volume) := by
      rw [← Measure.restrict_univ (μ := (volume : Measure (ℝ^n))), Measure.prod_restrict]
      apply ContinuousOn.aestronglyMeasurable _ (measurableSet_Ioo.prod MeasurableSet.univ)
      refine hcont.comp (contDiff_timeSpaceCons_uncurry n (m := 0)).continuous.continuousOn ?_
      intro p hp
      simpa using hp.1
    refine (h1.inner h2).integral_prod_right'.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht' : t ∈ Set.Ioc 0 T := Set.Ioo_subset_Ioc_self ht
    simp only [F, ht', ↓reduceDIte]
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hD ht').coeFn_toLp] with x hx
    rw [hx]
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine hg.mono' (hmeas.norm.pow 2) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have ht' : t ∈ Set.Ioc 0 T := Set.Ioo_subset_Ioc_self ht
  simp only [F, ht', ↓reduceDIte, Lp.norm_toLp, norm_pow, Real.norm_eq_abs, sq_abs]
  exact hle t ht'

end PDE.Analysis
