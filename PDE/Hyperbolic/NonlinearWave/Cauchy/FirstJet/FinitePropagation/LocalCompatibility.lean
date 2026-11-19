/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.LocalState
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.LocalData
import CAS.ExactTactic

/-!
# Compatibility of compact truncations of local wave data

Finite propagation identifies local energy restrictions of two whole-space
solutions from identical data on a larger ball. Expanding truncations therefore
stabilize on every bounded spatial set and finite forward time interval.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}
variable {hf : LipschitzWith L f} {hf0 : f 0 = 0}

/-- Equality of states restricts to any smaller open spatial set. -/
theorem restrictStateCLM_eq_mono {Ω V : Set (ℝ^n)} (hΩ : IsOpen Ω) (hV : IsOpen V) (hsub : Ω ⊆ V)
    {x y : H¹(ℝ^n) × DerivLp n 2 univ}
    (h : restrictStateCLM hV.measurableSet x = restrictStateCLM hV.measurableSet y) :
    restrictStateCLM hΩ.measurableSet x = restrictStateCLM hΩ.measurableSet y := by
  obtain ⟨hq, hv⟩ := (restrictStateCLM_eq_iff hV x y).mp h
  exact (restrictStateCLM_eq_iff hΩ x y).mpr ⟨ae_restrict_of_ae_restrict_of_subset hsub hq,
      ae_restrict_of_ae_restrict_of_subset hsub hv⟩

/-- Agreement of the two initial functions on a larger ball implies equality
of the local H¹ × L² states for a fixed finite time. -/
theorem IsEnergySolution.restrictState_eq_on_ball {x y : H¹(ℝ^n) × DerivLp n 2 univ}
    {u v : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)} (hu : IsEnergySolution hf hf0 x u)
    (hv : IsEnergySolution hf hf0 y v) {C R T : ℝ} (hC : 0 ≤ C) (hR : 0 < R) (hT : 0 ≤ T)
    (hgrad : ∀ (i : Fin n) (z : ℝ^n), |(∂[i] (SobolevSpace.Approximation.cutoff R)) z| ≤ C / R)
    (hspeed : (n : ℝ) * C * T < R)
    (hq : baseRepresentative x.1 =ᵐ[volume.restrict (ball 0 (3 * R))] baseRepresentative y.1)
    (hp : (x.2 : ℝ^n → ℝ) =ᵐ[volume.restrict (ball 0 (3 * R))] y.2) :
    restrictStateCLM (measurableSet_ball (x := (0 : ℝ^n)) (ε := R)) (u T) =
      restrictStateCLM measurableSet_ball (v T) := by
  have hinit := (restrictStateCLM_eq_iff_energyDensity isOpen_ball x y).mp
    ((restrictStateCLM_eq_iff isOpen_ball x y).mpr ⟨hq, hp⟩)
  have hsub : closedBall (0 : ℝ^n) (2 * R) ⊆ ball 0 (3 * R) :=
    closedBall_subset_ball (by linarith)
  have hzero : ∀ᵐ z ∂(domainMeasure n univ).restrict (closedBall 0 (2 * R)),
      energyDensity (x - y) z = 0 := by
    simpa only [domainMeasure, Measure.restrict_univ] using
      ae_restrict_of_ae_restrict_of_subset hsub hinit
  have hs : (n : ℝ) * (C / R) * T < 1 := by
    have he : (n : ℝ) * (C / R) * T = ((n : ℝ) * C * T) / R := by
      cas using hR.ne'
    rw [he]
    exact (div_lt_one hR).mpr hspeed
  have hlocal := hu.energyDensity_sub_eq_zero_on_ball hv hC hR hT hgrad hs hzero
  apply (restrictStateCLM_eq_iff_energyDensity isOpen_ball (u T) (v T)).mpr
  simpa only [domainMeasure, Measure.restrict_univ] using
    ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hlocal

/-- Any family of compact data extensions yields compatible energy curves.
An additional property of each extended trajectory, such as higher Sobolev
persistence, is retained by the construction. -/
theorem exists_compatible_energy_truncations_of_extensions (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    {g v : ℝ^n → ℝ} {P : (H¹(ℝ^n) × DerivLp n 2 univ) → C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ) → Prop}
    (hext : ∀ K : Set (ℝ^n), IsCompact K → ∃ x : H¹(ℝ^n) × DerivLp n 2 univ,
      baseRepresentative x.1 =ᵐ[volume.restrict K] g ∧ (x.2 : ℝ^n → ℝ) =ᵐ[volume.restrict K] v ∧
      ∃ u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ), IsEnergySolution hf hf0 x u ∧ P x u) :
    ∃ (x : ℕ → H¹(ℝ^n) × DerivLp n 2 univ)
      (u : ℕ → C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)),
      (∀ i, IsEnergySolution hf hf0 (x i) (u i)) ∧ (∀ i, P (x i) (u i)) ∧
      (∀ i, baseRepresentative (x i).1 =ᵐ[volume.restrict (ball 0 ((i : ℝ) + 1))] g ∧
        ((x i).2 : ℝ^n → ℝ) =ᵐ[volume.restrict (ball 0 ((i : ℝ) + 1))] v) ∧
      ∀ (i j : ℕ), i ≤ j → ∀ t ∈ Icc (0 : ℝ) ((i : ℝ) + 1),
        restrictStateCLM (measurableSet_ball (x := (0 : ℝ^n)) (ε := (i : ℝ) + 1)) (u i t) =
          restrictStateCLM measurableSet_ball (u j t) := by
  obtain ⟨C, hC, hgrad⟩ := exists_cutoff_gradient_bound n
  let R : ℕ → ℝ := fun i ↦ ((i : ℝ) + 2) * (1 + (n : ℝ) * C)
  have hNC : 0 ≤ (n : ℝ) * C := mul_nonneg (Nat.cast_nonneg n) hC
  have hR (i : ℕ) : 0 < R i := mul_pos (by positivity) (by positivity)
  have hRi (i : ℕ) : (i : ℝ) + 1 < R i := by
    dsimp only [R]
    nlinarith [Nat.cast_nonneg (α := ℝ) i]
  have hmono : Monotone R := by
    intro i j hij
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hij 2)
      (by positivity)
  have hall (i : ℕ) := hext (closedBall 0 (3 * R i)) (isCompact_closedBall (0 : ℝ^n) (3 * R i))
  choose x hgx hvx u hu hP using hall
  refine ⟨x, u, hu, hP, ?_, ?_⟩
  · intro i
    have hsub : ball (0 : ℝ^n) ((i : ℝ) + 1) ⊆ closedBall 0 (3 * R i) :=
      ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith [hRi i, hR i]))
    exact ⟨ae_restrict_of_ae_restrict_of_subset hsub (hgx i),
      ae_restrict_of_ae_restrict_of_subset hsub (hvx i)⟩
  · intro i j hij t ht
    have hsub (a : ℕ) (hia : i ≤ a) : ball (0 : ℝ^n) (3 * R i) ⊆ closedBall 0 (3 * R a) :=
      ball_subset_closedBall.trans
        (closedBall_subset_closedBall (mul_le_mul_of_nonneg_left (hmono hia) (by positivity)))
    have hqi : baseRepresentative (x i).1 =ᵐ[volume.restrict (ball 0 (3 * R i))] g :=
      ae_restrict_of_ae_restrict_of_subset (hsub i le_rfl) (hgx i)
    have hqj : baseRepresentative (x j).1 =ᵐ[volume.restrict (ball 0 (3 * R i))] g :=
      ae_restrict_of_ae_restrict_of_subset (hsub j hij) (hgx j)
    have hpi : ((x i).2 : ℝ^n → ℝ) =ᵐ[volume.restrict (ball 0 (3 * R i))] v :=
      ae_restrict_of_ae_restrict_of_subset (hsub i le_rfl) (hvx i)
    have hpj : ((x j).2 : ℝ^n → ℝ) =ᵐ[volume.restrict (ball 0 (3 * R i))] v :=
      ae_restrict_of_ae_restrict_of_subset (hsub j hij) (hvx j)
    have hspeed : (n : ℝ) * C * t < R i := by
      have hbound := mul_le_mul_of_nonneg_left ht.2 hNC
      dsimp only [R]
      nlinarith [Nat.cast_nonneg (α := ℝ) i]
    exact restrictStateCLM_eq_mono isOpen_ball isOpen_ball (ball_subset_ball (hRi i).le)
      ((hu i).restrictState_eq_on_ball (hu j) hC (hR i) ht.1
        (hgrad (R i) (hR i)) hspeed (hqi.trans hqj.symm) (hpi.trans hpj.symm))

/-- Local H¹ × L² data admit a sequence of whole-space solutions compatible
on every cylinder `[0,i+1] × ball(0,i+1)`. The initial traces on these balls
are the original local data. There is no global norm hypothesis on the data. -/
theorem exists_compatible_energy_truncations (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    {g v : ℝ^n → ℝ} (hg : IsLocallyWkpOn 1 2 univ g) (hv : IsLocallyWkpOn 0 2 univ v) :
    ∃ (x : ℕ → H¹(ℝ^n) × DerivLp n 2 univ)
      (u : ℕ → C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)),
      (∀ i, IsEnergySolution hf hf0 (x i) (u i)) ∧
      (∀ i, baseRepresentative (x i).1 =ᵐ[volume.restrict (ball 0 ((i : ℝ) + 1))] g ∧
        ((x i).2 : ℝ^n → ℝ) =ᵐ[volume.restrict (ball 0 ((i : ℝ) + 1))] v) ∧
      ∀ (i j : ℕ), i ≤ j → ∀ t ∈ Icc (0 : ℝ) ((i : ℝ) + 1),
        restrictStateCLM (measurableSet_ball (x := (0 : ℝ^n)) (ε := (i : ℝ) + 1)) (u i t) =
          restrictStateCLM measurableSet_ball (u j t) := by
  have hext (K : Set (ℝ^n)) (hK : IsCompact K) := exists_energySolution_truncation hf hf0 hg hv hK
  have hP (K : Set (ℝ^n)) (hK : IsCompact K) : ∃ x : H¹(ℝ^n) × DerivLp n 2 univ,
        baseRepresentative x.1 =ᵐ[volume.restrict K] g ∧ (x.2 : ℝ^n → ℝ) =ᵐ[volume.restrict K] v ∧
        ∃ u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ),
          IsEnergySolution hf hf0 x u ∧ True := by
    obtain ⟨x, hxg, hxv, u, hu⟩ := hext K hK
    exact ⟨x, hxg, hxv, u, hu, trivial⟩
  obtain ⟨x, u, hu, _, hx, hcompat⟩ := exists_compatible_energy_truncations_of_extensions hf hf0 hP
  exact ⟨x, u, hu, hx, hcompat⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
