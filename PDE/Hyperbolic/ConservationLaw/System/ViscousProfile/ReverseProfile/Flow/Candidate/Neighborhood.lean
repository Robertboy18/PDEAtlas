/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Candidate.Chronology
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Matching.Neighborhood

/-!
# One neighborhood for the prescribed coupled candidate

The supplied family, event maps, and fixed base gate are retained. Joint candidate
regularity and the matched base tail give a common late margin. After its endpoint
is chosen, continuity of the supplied terminal event places that event strictly
inside the shortened tail interval. The chronology theorem then supplies
the coupled field equation on the entire closed time interval.

The gate coefficients remain signed.
-/

@[expose] public noncomputable section

open Set
open PDE.Analysis.Evolution PDE.Analysis.NormalizedPulse
open scoped BigOperators ContDiff

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- The same explicit candidate solves the coupled equation on one open product
neighborhood, with the same terminal event strictly inside the late interval.
The phase bounds are the tube conclusions for the supplied `F` and `N`.
Joint gate smoothness and small support are outputs of the fixed-gate theorems;
matching is required only at the retained coefficient `cStar` and base parameter. -/
theorem exists_prescribed_clock_coupled_neighborhood {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {L Bhit : ℝ × ℝ → ℝ}
    {β : Fin 3 → ℝ → ℝ} {cStar : Fin 3 → ℝ} {N : Set (ℝ × ℝ)} {A B rUp rDown τ0 Hmax : ℝ}
    (hF : ContDiff ℝ ∞ F) (hN : IsOpen N) (hbase : (0, 0) ∈ N) (hL : ContinuousOn L N)
    (hLbase : L (0, 0) = τ0) (hrτ : rDown < τ0) (hHmax : τ0 < Hmax) (hAB : A ^ 2 < B ^ 2)
    (hB : 0 ≤ B) (hmargin : B < (F (τ0, (0, 0))).2)
    (hode : ∀ p ∈ N, ∀ t ∈ Icc (0 : ℝ) Hmax,
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hearly : ∀ p ∈ N, ∀ t ∈ Icc (0 : ℝ) rUp, (F (t, p)).1 ∈ Ioo (-1 : ℝ) (20501 / 100) ∧
      (F (t, p)).2 ^ 2 < A ^ 2)
    (hmiddle : ∀ p ∈ N, ∀ t ∈ Icc rUp rDown, (205 : ℝ) < (F (t, p)).1)
    (hlate : ∀ p ∈ N, ∀ t ∈ Icc rDown Hmax, (F (t, p)).1 ∈ Ioo (-1 : ℝ) (20501 / 100) ∧ B ^ 2 <
      (F (t, p)).2 ^ 2) :
    let D0 := parameterizedClockPassageData L Bhit (0, 0)
    let b : (Fin 3 → ℝ) × ℝ → ℝ := fun z ↦
      (Ioo (205 : ℝ) (2051 / 10)).indicator
        (fun y ↦ (∑ j, z.1 j * β j y) / D0.wMinus y) z.2
    let xhat : ℝ × ((ℝ × ℝ) × (Fin 3 → ℝ)) → ℝ := fun z ↦
      (F (z.1, z.2.1)).2 * scalarLinearSolution (fun _ ↦ 4)
        (fun s ↦ b (z.2.2, (F (s, z.2.1)).1)) 0 0 z.1
    let q : (ℝ × ℝ) → (Fin 3 → ℝ) → ℝ → ℝ^3 := fun p c t ↦
      !₂[xhat (t, (p, c)), (F (t, p)).1, (F (t, p)).2]
    ContDiff ℝ ∞ b →
    (∀ c : Fin 3 → ℝ,
      tsupport (fun y ↦ b (c, y)) ⊆ Ioo (20501 / 100 : ℝ) (20509 / 100)) →
    EqOn (fun t ↦ xhat (t, ((0, 0), cStar)))
      (fun t ↦ (F (τ0, (0, 0))).2 * Real.exp (2 * (τ0 - t))) (Icc rDown Hmax) →
    ∃ (H : ℝ) (U : Set (ℝ × ℝ)) (V : Set (Fin 3 → ℝ)),
      H ∈ Ioo τ0 Hmax ∧ IsOpen U ∧ (0, 0) ∈ U ∧ U ⊆ N ∧
        IsOpen V ∧ cStar ∈ V ∧
        ∀ p ∈ U, L p ∈ Ioo rDown H ∧ ∀ c ∈ V, ∀ t ∈ Icc (0 : ℝ) H,
          HasDerivAt (q p c)
            (GatedFlux.flux (fun s ↦ 2 * s) MiddleClock.g cutoff (clockFeedback A B)
              (fun y ↦ b (c, y)) (q p c t) - p.1 • q p c t) t := by
  intro D0 b xhat q hb hsmall htail
  obtain ⟨H, N', V, hH, hN', hbaseN', hN'N, hV, hcV, _hVuniv, hresponse⟩ :=
    exists_prescribed_clock_matched_neighborhood
      (F := F) (L := L) (Bhit := Bhit) (β := β) (cStar := cStar) (V := univ)
      hN hbase isOpen_univ (mem_univ cStar) hHmax hB hmargin
      (contDiff_prescribed_clock_scalar_candidate hF hb).continuous htail
  change ∀ p ∈ N', ∀ c ∈ V, ∀ t ∈ Icc rDown H, B < xhat (t, (p, c)) at hresponse
  have hUN : N' ∩ L ⁻¹' Ioo rDown H ⊆ N := fun _ hp ↦ hN'N hp.1
  refine ⟨H, N' ∩ L ⁻¹' Ioo rDown H, V, hH, (hL.mono hN'N).isOpen_inter_preimage hN' isOpen_Ioo,
    ⟨hbaseN', (hLbase ▸ ⟨hrτ, hH.1⟩ : L (0, 0) ∈ Ioo rDown H)⟩, hUN, hV, hcV,
    fun p hp ↦ ⟨hp.2, fun c hc ↦ ?_⟩⟩
  let X : ℝ → ℝ := fun t ↦ (F (t, p)).1
  let Z : ℝ → ℝ := fun t ↦ (F (t, p)).2
  have hpN : p ∈ N := hUN hp
  have hpair (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H) :
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t :=
    hode p hpN t ⟨ht.1, ht.2.trans hH.2.le⟩
  exact hasDerivAt_prescribed_coupled_candidate_of_itinerary
    (X := X) (Z := Z) (b := fun y ↦ b (c, y)) (A := A) (B := B) (μ := p.1)
    (rUp := rUp) (rDown := rDown) (H := H)
    ((hb.continuous.comp (continuous_const.prodMk continuous_id)).comp
      (hF.continuous.comp (continuous_id.prodMk continuous_const)).fst) (hsmall c) hAB hB
    (fun t ht ↦ by
      simpa only [Function.comp_def, ContinuousLinearMap.coe_fst', prescribedSpeedField, X, Z]
        using (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hpair t ht))
    (fun t ht ↦ by
      simpa only [Function.comp_def, ContinuousLinearMap.coe_snd', prescribedSpeedField, Z]
        using (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hpair t ht))
    (fun t ht ↦ ⟨(hearly p hpN t ht).1.1, (hearly p hpN t ht).1.2, (hearly p hpN t ht).2⟩)
    (hmiddle p hpN) (fun t ht ↦ ⟨(hlate p hpN t ⟨ht.1, ht.2.trans hH.2.le⟩).1.1,
      (hlate p hpN t ⟨ht.1, ht.2.trans hH.2.le⟩).2⟩) (hresponse p hp.1 c hc)

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
