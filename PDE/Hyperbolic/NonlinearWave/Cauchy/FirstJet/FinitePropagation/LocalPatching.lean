/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.LocalCompatibility
public import PDE.Analysis.MeasureTheory.Function.Gluing

/-!
# Patching local wave trajectories

Compatible energy curves on expanding cylinders determine displacement and
velocity fields at every forward time. On each finite cylinder their spatial
classes agree with one whole-space curve, so its strong time continuity and
weak spatial derivatives transfer to the patched fields.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ}

/-- The two scalar representatives of an energy state. -/
def stateRepresentative (z : H¹(ℝ^n) × DerivLp n 2 univ) (y : ℝ^n) : ℝ × ℝ :=
  (baseRepresentative z.1 y, z.2 y)

/-- Agreement in local energy implies agreement of the represented pair. -/
theorem stateRepresentative_ae_eq_of_restrictStateCLM_eq {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω)
    {x y : H¹(ℝ^n) × DerivLp n 2 univ}
    (h : restrictStateCLM hΩ.measurableSet x = restrictStateCLM hΩ.measurableSet y) :
    stateRepresentative x =ᵐ[domainMeasure n Ω] stateRepresentative y := by
  obtain ⟨hq, hv⟩ := (restrictStateCLM_eq_iff hΩ x y).mp h
  filter_upwards [hq, hv] with z hzq hzv
  exact Prod.ext hzq hzv

/-- A compatible family of local energy curves has scalar representatives
agreeing with every curve throughout its cylinder, at every time there. -/
theorem exists_representative_of_compatible_energy_curves (u : ℕ → C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ))
    (hcompat : ∀ (i j : ℕ), i ≤ j → ∀ t ∈ Icc (0 : ℝ) ((i : ℝ) + 1),
      restrictStateCLM (measurableSet_ball (x := (0 : ℝ^n)) (ε := (i : ℝ) + 1)) (u i t) =
      restrictStateCLM measurableSet_ball (u j t)) :
    ∃ w : ℝ → ℝ^n → ℝ × ℝ, ∀ (i : ℕ) t, t ∈ Icc (0 : ℝ) ((i : ℝ) + 1) →
      w t =ᵐ[volume.restrict (ball 0 ((i : ℝ) + 1))] stateRepresentative (u i t) := by
  have hfixed (t : ℝ) (ht : 0 ≤ t) : ∃ w : ℝ^n → ℝ × ℝ, ∀ i : ℕ, t ≤ (i : ℝ) + 1 →
        w =ᵐ[volume.restrict (ball 0 ((i : ℝ) + 1))] stateRepresentative (u i t) := by
    obtain ⟨m, hm⟩ := exists_nat_ge t
    let B : ℕ → Set (ℝ^n) := fun i ↦ ball 0 ((i : ℝ) + 1)
    let F : ℕ → ℝ^n → ℝ × ℝ := fun i ↦ stateRepresentative (u (max m i) t)
    have htime (i : ℕ) : t ≤ (max m i : ℕ) + (1 : ℝ) := by
      have hmi : (m : ℝ) ≤ (max m i : ℕ) := by exact_mod_cast le_max_left m i
      linarith
    have hordered (i j : ℕ) (hij : i ≤ j) : F i =ᵐ[volume.restrict (B i)] F j := by
      have h := stateRepresentative_ae_eq_of_restrictStateCLM_eq isOpen_ball
        (hcompat (max m i) (max m j) (max_le_max_left m hij) t ⟨ht, htime i⟩)
      have hsub : B i ⊆ ball (0 : ℝ^n) ((max m i : ℕ) + (1 : ℝ)) :=
        ball_subset_ball (by exact_mod_cast Nat.add_le_add_right (le_max_right m i) 1)
      exact ae_restrict_of_ae_restrict_of_subset hsub h
    have hpair (i j : ℕ) : F i =ᵐ[volume.restrict (B i ∩ B j)] F j := by
      rcases le_total i j with hij | hji
      · exact ae_restrict_of_ae_restrict_of_subset inter_subset_left (hordered i j hij)
      · exact ae_restrict_of_ae_restrict_of_subset inter_subset_right (hordered j i hji).symm
    have hmeas (i : ℕ) : AEStronglyMeasurable (F i) (volume.restrict (B i)) :=
      ((Lp.stronglyMeasurable (wkpBaseCoordinateCLM (u (max m i) t).1)).prodMk
        (Lp.stronglyMeasurable (u (max m i) t).2)).aestronglyMeasurable
    obtain ⟨w, _, hw⟩ := exists_aestronglyMeasurable_of_ae_eq_on_intersections
      B (fun _ ↦ measurableSet_ball) F hmeas hpair
    refine ⟨w, ?_⟩
    intro i hti
    have h := stateRepresentative_ae_eq_of_restrictStateCLM_eq isOpen_ball
      (hcompat i (max m i) (le_max_right m i) t ⟨ht, hti⟩)
    exact (hw i).trans h.symm
  have hall (t : ℝ) : ∃ w : ℝ^n → ℝ × ℝ, ∀ i : ℕ, t ∈ Icc (0 : ℝ) ((i : ℝ) + 1) →
        w =ᵐ[volume.restrict (ball 0 ((i : ℝ) + 1))] stateRepresentative (u i t) := by
    by_cases ht : 0 ≤ t
    · obtain ⟨w, hw⟩ := hfixed t ht
      exact ⟨w, fun i hi ↦ hw i hi.2⟩
    · exact ⟨0, fun _ hi ↦ (ht hi.1).elim⟩
  choose w hw using hall
  exact ⟨w, fun i t ht ↦ hw t i ht⟩

/-- Every bounded spatial set and finite time fit into one cylinder of the
integer exhaustion. -/
theorem exists_exhaustion_cylinder {V : Set (ℝ^n)} (hV : Bornology.IsBounded V) (T : ℝ) :
    ∃ i : ℕ, T ≤ (i : ℝ) + 1 ∧ V ⊆ ball 0 ((i : ℝ) + 1) := by
  obtain ⟨R, hR⟩ := hV.exists_norm_le
  obtain ⟨i, hi⟩ := exists_nat_ge (max T R)
  refine ⟨i, (le_max_left T R).trans (hi.trans (by linarith)), ?_⟩
  intro y hy
  rw [mem_ball, dist_zero_right]
  exact (hR y hy).trans_lt (lt_of_le_of_lt ((le_max_right T R).trans hi) (by linarith))

/-- Patching compact extensions retains any additional property of the
whole-space curves used to represent the field on finite cylinders. -/
theorem exists_patched_local_energy_fields_of_extensions {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}
    (hf : LipschitzWith L f) (hf0 : f 0 = 0) {g v : ℝ^n → ℝ}
    {P : (H¹(ℝ^n) × DerivLp n 2 univ) → C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ) → Prop}
    (hext : ∀ K : Set (ℝ^n), IsCompact K → ∃ x : H¹(ℝ^n) × DerivLp n 2 univ,
      baseRepresentative x.1 =ᵐ[volume.restrict K] g ∧ (x.2 : ℝ^n → ℝ) =ᵐ[volume.restrict K] v ∧
      ∃ u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ), IsEnergySolution hf hf0 x u ∧ P x u) :
    ∃ w : ℝ → ℝ^n → ℝ × ℝ,
      (∀ i : ℕ, w 0 =ᵐ[volume.restrict (ball 0 ((i : ℝ) + 1))] fun y ↦ (g y, v y)) ∧
      ∀ {V : Set (ℝ^n)}, Bornology.IsBounded V → ∀ T : ℝ,
        ∃ (x : H¹(ℝ^n) × DerivLp n 2 univ)
          (u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)),
          IsEnergySolution hf hf0 x u ∧ P x u ∧
          ∀ t ∈ Icc (0 : ℝ) T,
            w t =ᵐ[volume.restrict V] stateRepresentative (u t) := by
  obtain ⟨x, u, hu, hP, hx, hcompat⟩ :=
    exists_compatible_energy_truncations_of_extensions hf hf0 hext
  obtain ⟨w, hw⟩ := exists_representative_of_compatible_energy_curves u hcompat
  refine ⟨w, ?_, ?_⟩
  · intro i
    have h := hw i 0 ⟨le_rfl, by positivity⟩
    rw [(hu i).initial] at h
    filter_upwards [h, (hx i).1, (hx i).2] with y hy hq hp
    exact hy.trans (Prod.ext hq hp)
  · intro V hV T
    obtain ⟨i, hiT, hiV⟩ := exists_exhaustion_cylinder hV T
    exact ⟨x i, u i, hu i, hP i, fun t ht ↦
      ae_restrict_of_ae_restrict_of_subset hiV (hw i t ⟨ht.1, ht.2.trans hiT⟩)⟩

/-- Patching arbitrary local H¹ × L² Cauchy data gives fields represented,
on every finite cylinder, by a continuous whole-space weak wave curve. -/
theorem exists_patched_local_energy_fields {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}
    (hf : LipschitzWith L f) (hf0 : f 0 = 0) {g v : ℝ^n → ℝ} (hg : IsLocallyWkpOn 1 2 univ g)
    (hv : IsLocallyWkpOn 0 2 univ v) :
    ∃ w : ℝ → ℝ^n → ℝ × ℝ,
      (∀ i : ℕ, w 0 =ᵐ[volume.restrict (ball 0 ((i : ℝ) + 1))] fun y ↦ (g y, v y)) ∧
      ∀ {V : Set (ℝ^n)}, Bornology.IsBounded V → ∀ T : ℝ,
        ∃ (x : H¹(ℝ^n) × DerivLp n 2 univ)
          (u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)),
          IsEnergySolution hf hf0 x u ∧
          ∀ t ∈ Icc (0 : ℝ) T,
            w t =ᵐ[volume.restrict V] stateRepresentative (u t) := by
  have hext (K : Set (ℝ^n)) (hK : IsCompact K) : ∃ x : H¹(ℝ^n) × DerivLp n 2 univ,
        baseRepresentative x.1 =ᵐ[volume.restrict K] g ∧ (x.2 : ℝ^n → ℝ) =ᵐ[volume.restrict K] v ∧
        ∃ u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ),
          IsEnergySolution hf hf0 x u ∧ True := by
    obtain ⟨x, hxg, hxv, u, hu⟩ := exists_energySolution_truncation hf hf0 hg hv hK
    exact ⟨x, hxg, hxv, u, hu, trivial⟩
  obtain ⟨w, hw0, hw⟩ := exists_patched_local_energy_fields_of_extensions hf hf0 hext
  refine ⟨w, hw0, ?_⟩
  intro V hV T
  obtain ⟨x, u, hu, _, heq⟩ := hw hV T
  exact ⟨x, u, hu, heq⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
