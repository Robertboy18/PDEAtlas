/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic
public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
import PDE.Analysis.Evolution.LionsMagenes.Regularity.LocalRepresentative

/-!
# Cross-energy identity for weak Gelfand evolutions

For two `L²(V)` trajectories with weak derivatives in `L²(V*)`, the
polarized Lions–Magenes identity expresses the increment of their pivot
inner product as the integral of the two duality pairings.  The result is
stated on compact subintervals carrying continuous pivot representatives.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, proof of Theorem 4, identity (39).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace PDE.Analysis.Evolution

section GelfandWeakTimeDerivative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Transport the representative of the Bochner sum to the pointwise sum of representatives. -/
private theorem exists_pointwise_sum_representative
    [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b c d : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u₁ u₂ : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g₁ g₂ : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h₁ : HasGelfandWeakTimeDerivativeOn T u₁ g₁)
    (h₂ : HasGelfandWeakTimeDerivativeOn T u₂ g₂)
    (E₁ : ContinuousPivotEvolutionOn T
      (fun t ↦ u₁ t) (fun t ↦ g₁ t) c d)
    (E₂ : ContinuousPivotEvolutionOn T
      (fun t ↦ u₂ t) (fun t ↦ g₂ t) c d)
    (hac : a < c) (hcd : c < d) (hdb : d < b)
    : Nonempty (ContinuousPivotEvolutionOn T
      (fun r ↦ u₁ r + u₂ r) (fun r ↦ g₁ r + g₂ r) c d) := by
  let μab := volume.restrict (Set.Ioc a b)
  have hle : volume.restrict (Icc c d) ≤ μab :=
    Measure.restrict_mono_set _ fun r hr ↦ ⟨hac.trans_le hr.1, hr.2.trans hdb.le⟩
  have hsub {x y : ℝ} (hx : x ∈ uIcc c d) (hy : y ∈ uIcc c d) :
      volume.restrict (uIoc x y) ≤ volume.restrict (Icc c d) :=
    Measure.restrict_mono_set _ fun r hr ↦
      (uIcc_of_le hcd.le).subset (uIcc_subset_uIcc hx hy (uIoc_subset_uIcc hr))
  obtain ⟨E₁₂⟩ :=
    (h₁.add h₂).hasWeakTimeDerivativeOn.exists_continuous_representativeOn hac hcd.le hdb
  have hu : ((u₁ + u₂ : Lp V 2 μab) : ℝ → V) =ᵐ[volume.restrict (Icc c d)]
      fun r ↦ u₁ r + u₂ r := (Lp.coeFn_add u₁ u₂).filter_mono (ae_mono hle)
  have hg : ((g₁ + g₂ : Lp (StrongDual ℝ V) 2 μab) : ℝ → StrongDual ℝ V)
      =ᵐ[volume.restrict (Icc c d)] fun r ↦ g₁ r + g₂ r :=
    (Lp.coeFn_add g₁ g₂).filter_mono (ae_mono hle)
  exact ⟨{
    representative := E₁₂.representative
    continuousOn := E₁₂.continuousOn
    ae_eq_inclusion := by
      have hae := E₁₂.ae_eq_inclusion
      rw [uIcc_of_le hcd.le] at hae ⊢
      filter_upwards [hae, hu] with r hrep hadd
      rw [hrep, hadd, map_add]
    integratedDerivative := ⟨E₁.integratedDerivative.intervalIntegrable.add
        E₂.integratedDerivative.intervalIntegrable, fun r hr ↦ by
      rw [E₁₂.integratedDerivative.eq_add_integral r hr]
      congr 1
      exact intervalIntegral.integral_congr_ae_restrict
        (hg.filter_mono (ae_mono (hsub left_mem_uIcc hr)))⟩
    energyIdentity := fun x y hx hy ↦ by
      rw [E₁₂.energyIdentity x y hx hy]
      congr 1
      refine intervalIntegral.integral_congr_ae_restrict ?_
      filter_upwards [hg.filter_mono (ae_mono (hsub hx hy)),
        hu.filter_mono (ae_mono (hsub hx hy))] with r hgr hur
      rw [hgr, hur] }⟩

/--
Polarized Lions–Magenes product rule for two `L²` Gelfand trajectories.

Continuous pivot representatives for the two trajectories on a compact
interior interval are hypotheses.  Their weak-derivative
relations automatically produce a representative for the sum.  Continuity
and almost-everywhere uniqueness identify that representative pointwise
with the sum of the original representatives, after which
`ContinuousPivotEvolutionOn.cross_energy_identity` gives

`⟪u₁(t),u₂(t)⟫ - ⟪u₁(s),u₂(s)⟫
  = ∫ₛᵗ (g₁(r)(u₂(r)) + g₂(r)(u₁(r))) dr`.

All four duality products are interval-integrable automatically by Bochner
`L²` Hölder duality. This is the low-regularity integration by parts that gives
(39) in the proof of Evans §7.2.2, Theorem 4.
-/
theorem HasGelfandWeakTimeDerivativeOn.cross_energy_identity
    [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b c d : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u₁ u₂ : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g₁ g₂ : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h₁ : HasGelfandWeakTimeDerivativeOn T u₁ g₁)
    (h₂ : HasGelfandWeakTimeDerivativeOn T u₂ g₂)
    (E₁ : ContinuousPivotEvolutionOn T
      (fun t ↦ u₁ t) (fun t ↦ g₁ t) c d)
    (E₂ : ContinuousPivotEvolutionOn T
      (fun t ↦ u₂ t) (fun t ↦ g₂ t) c d)
    (hac : a < c) (hcd : c < d) (hdb : d < b)
    {s t : ℝ} (hs : s ∈ Set.Icc c d) (ht : t ∈ Set.Icc c d) :
    inner ℝ (E₁.representative t) (E₂.representative t) -
        inner ℝ (E₁.representative s) (E₂.representative s) =
      ∫ r in s..t, g₁ r (u₂ r) + g₂ r (u₁ r) := by
  obtain ⟨Epoint⟩ := exists_pointwise_sum_representative h₁ h₂ E₁ E₂ hac hcd hdb
  have h := uIcc_of_le hcd.le
  -- the continuous representative of the sum is the sum of the representatives on `[c, d]`
  have hsumRep : ∀ r ∈ Icc c d,
      Epoint.representative r = E₁.representative r + E₂.representative r := by
    refine Measure.eqOn_Icc_of_ae_eq volume hcd.ne ?_ (h ▸ Epoint.continuousOn)
      (h ▸ E₁.continuousOn.add E₂.continuousOn)
    filter_upwards [h ▸ Epoint.ae_eq_inclusion, h ▸ E₁.ae_eq_inclusion,
      h ▸ E₂.ae_eq_inclusion] with r h₁₂r h₁r h₂r
    rw [h₁₂r, h₁r, h₂r, map_add]
  have hpair (g : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b)))
      (u : Lp V 2 (volume.restrict (Ioc a b))) :
      IntervalIntegrable (fun r ↦ g r (u r)) volume s t :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hcd.le).2
      ((integrable_dual_pairing g u).mono_measure (Measure.restrict_mono_set _ fun r hr ↦
        ⟨hac.trans hr.1, hr.2.trans hdb.le⟩))).mono_set
      (uIcc_subset_uIcc (Icc_subset_uIcc hs) (Icc_subset_uIcc ht))
  exact E₁.cross_energy_identity E₂ Epoint (fun r hr ↦ hsumRep r (h.subset hr))
    (Icc_subset_uIcc hs) (Icc_subset_uIcc ht) (hpair g₁ u₁) (hpair g₁ u₂) (hpair g₂ u₁)
    (hpair g₂ u₂)

end GelfandWeakTimeDerivative

end PDE.Analysis.Evolution
