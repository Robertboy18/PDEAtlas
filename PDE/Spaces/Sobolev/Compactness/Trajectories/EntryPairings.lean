/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Evolution.Compactness.HalfLine
public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Cutoff

/-!
# Half-line compactness from entry-test identities

Temporal L² bounds for every eventually admissible Galerkin test supply dense
pairing moduli. One subsequence converges on every bounded time window, including
all compact H¹ observations of the same path.
-/

@[expose] public noncomputable section

open Filter MeasureTheory TopologicalSpace Set PDE.Common SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Topology Distributions Sobolev

namespace PDE.Analysis.Evolution

/-- Temporal L² control of every fixed entry test along a Hilbert-space path. -/
def EntryTimePairings
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (trials : StableTrialSystem (GelfandTriple.identity H))
    (a b : ℝ) (u : ℕ → ℝ → H) : Prop :=
  ∀ j (v : trials.space j),
    ∃ g : ℕ → Lp ℝ 2 (volume.restrict (Ioc a b)), ∃ B : ℝ,
      (∀ n, j ≤ n → ‖g n‖ ≤ B) ∧
      ∀ n, j ≤ n → ∀ t₀ t₁ : Icc a b,
        inner ℝ (v : H) (u n t₁) - inner ℝ (v : H) (u n t₀) =
          ∫ r in (t₀ : ℝ)..(t₁ : ℝ), g n r

/-- The entry-test integral identities supply the dense test moduli needed
for one half-line subsequence. Every compact H1 observation uses that subsequence. -/
theorem half_line_of_entry_pairings
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (trials : StableTrialSystem (GelfandTriple.identity H))
    (a : ℝ) (u : ℕ → ℝ → H) (M : ℝ)
    (hu : ∀ n, ContinuousOn (u n) (Ici a))
    (hbound : ∀ n, ∀ t ∈ Ici a, ‖u n t‖ ≤ M)
    (hpair : ∀ k : ℕ, EntryTimePairings H trials a (a + k) u) :
    ∃ uLimit : Ici a → H, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ t, ‖uLimit t‖ ≤ M) ∧
      Continuous (fun t ↦ toWeakSpace ℝ H (uLimit t)) ∧
      (∀ k : ℕ, ∀ v : H, TendstoUniformly
        (fun n (t : Icc a (a + k)) ↦ inner ℝ v (u (φ n) t))
        (fun t : Icc a (a + k) ↦ inner ℝ v (uLimit ⟨t.val, t.property.1⟩)) atTop) ∧
      ∀ (k d : ℕ) (recover : H →L[ℝ] W^{1,2}(ℝ^d))
        (χ : 𝓓((⊤ : Opens (ℝ^d)), ℝ)),
        let J := ((wkpBaseCoordinateCLM (n := d) (m := 1) (p := 2)
          (Ω := univ)).comp (cutoffCLM (n := d) (p := 2) (Ω := univ) χ)).comp recover
        TendstoUniformly (fun n (t : Icc a (a + k)) ↦ J (u (φ n) t))
          (fun t : Icc a (a + k) ↦ J (uLimit ⟨t.val, t.property.1⟩)) atTop := by
  let test : (Σ j, trials.space j) → H := fun v ↦ v.2.val
  have hdense : DenseRange test := by
    rw [Metric.denseRange_iff]
    intro x ε hε
    obtain ⟨j, v, hv⟩ := (trials.densePivot x ε hε).exists
    exact ⟨⟨j, v⟩, by
      simpa only [test, dist_eq_norm, GelfandTriple.identity_inclusion_apply] using hv⟩
  have hpairTail : ∀ k : ℕ, ∀ v, ∃ N : ℕ, Equicontinuous
      (fun n : Ici N ↦ fun t : Icc a (a + k) ↦ inner ℝ (test v) (u n.val t)) := by
    intro k v
    obtain ⟨g, B, hg, hint⟩ := hpair k v.1 v.2
    refine ⟨v.1, ?_⟩
    apply Metric.equicontinuous_of_continuity_modulus (fun r ↦ Real.sqrt r * B)
    · simpa using (Real.continuous_sqrt.tendsto 0).mul_const B
    · intro s t n
      have hnorm := norm_intervalIntegral_coeFn_L2_restrict_Ioc_le
        (g n.val) s.property t.property
      have hsub : |inner ℝ (test v) (u n.val s) - inner ℝ (test v) (u n.val t)| ≤
          Real.sqrt |(t : ℝ) - s| * B := by
        rw [abs_sub_comm, hint n.val n.property s t]
        have hnorm' : |∫ r in (s : ℝ)..(t : ℝ), g n.val r| ≤
            Real.sqrt |(t : ℝ) - s| * ‖g n.val‖ := by
          simpa only [Real.norm_eq_abs] using hnorm
        exact hnorm'.trans
          (mul_le_mul_of_nonneg_left (hg n.val n.property) (Real.sqrt_nonneg _))
      simpa only [Real.dist_eq, Subtype.dist_eq, abs_sub_comm] using hsub
  let : ∀ j, FiniteDimensional ℝ (trials.space j) := trials.finiteDimensional
  let : ∀ j, SeparableSpace (trials.space j) := fun _ ↦ inferInstance
  let : SeparableSpace H := hdense.separableSpace
    (continuous_sigma fun _ ↦ continuous_subtype_val)
  obtain ⟨uLimit, φ, hφ, hlimit, hcont, hweak⟩ := exists_weak_trajectory_limit_Ici
    a test hdense (fun n t ↦ u n t)
      (fun n ↦ (hu n).comp_continuous continuous_subtype_val (fun t ↦ t.property))
      M (fun n t ↦ hbound n t t.property) hpairTail
  refine ⟨uLimit, φ, hφ, hlimit, hcont, hweak, ?_⟩
  intro k d recover χ
  dsimp only
  have hcompact := (RellichKondrachov.cutoffBaseCoordinate_isCompactOperator
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) χ).comp_clm recover
  exact tendstoUniformly_compactOperator_of_dense_pairings _ hcompact id denseRange_id
    (fun n (t : Icc a (a + k)) ↦ u (φ n) t)
    (fun t : Icc a (a + k) ↦ uLimit ⟨t.val, t.property.1⟩) M
    (fun n t ↦ hbound (φ n) t t.property.1)
    (fun t ↦ hlimit ⟨t.val, t.property.1⟩) (hweak k)

end PDE.Analysis.Evolution
