/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.Pointwise
public import Mathlib.Topology.MetricSpace.Holder
import PDE.Analysis.Calculus.UniformClosure
import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
# Interior Hölder representatives from mean oscillation

A locally integrable scalar field whose integral mean oscillation decays as
`r^γ`, with `γ > 0`, has a Hölder representative on a smaller ball. Lebesgue
differentiation identifies almost every point with its ball-average limit.
The dyadic estimate controls differences on this dense set; uniform extension
then constructs the representative without assuming continuity of the field.

The constant depends only on the dimension and exponent. Local integrability
is stated on the ambient space; only balls in the doubled input ball enter
the oscillation hypothesis and estimates.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set Filter
open scoped Topology NNReal

namespace PDE.Elliptic.Regularity.Campanato

private theorem holderOnWith_of_dist_bound
    {X : Type*} [PseudoMetricSpace X] {s : Set X} {g : X → ℝ} {K γ : ℝ≥0}
    (h : ∀ x ∈ s, ∀ y ∈ s, dist (g x) (g y) ≤ K * dist x y ^ (γ : ℝ)) :
    HolderOnWith K γ g s := by
  intro x hx y hy
  rw [edist_dist, edist_dist,
    ENNReal.ofReal_rpow_of_nonneg dist_nonneg γ.coe_nonneg,
    ENNReal.coe_nnreal_eq K, ← ENNReal.ofReal_mul K.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (h x hx y hy)

variable {n : ℕ}

/-- A power bound on integral mean oscillation produces a Hölder
representative on the ball with one eighth the radius. The constant is chosen
before the field, the centre, the radius and the oscillation bound. No pointwise
regularity or prescribed representative is an input. -/
theorem exists_holderOnWith_representative {γ : ℝ≥0} (hγ : 0 < γ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (f : ℝ^n → ℝ) (M : ℝ≥0),
      LocallyIntegrable f volume → ∀ (z : ℝ^n) (R : ℝ), 0 < R →
      (∀ x ∈ ball z R, ∀ r, 0 < r → r ≤ R →
        (⨍ y in closedBall x r, ‖f y - ⨍ w in closedBall x r, f w‖) ≤
          M * r ^ (γ : ℝ)) →
      ∃ g : ℝ^n → ℝ, Continuous g ∧ HolderOnWith (C * M) γ g (ball z (R / 8)) ∧
        g =ᵐ[volume.restrict (ball z (R / 8))] f := by
  have hγR : (0 : ℝ) < γ := hγ
  have hden : 0 < 1 - (1 / 2 : ℝ) ^ (γ : ℝ) :=
    sub_pos.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) hγR)
  let C : ℝ≥0 := ⟨2 * (2 : ℝ) ^ n / (1 - (1 / 2 : ℝ) ^ (γ : ℝ)) +
    2 * (2 : ℝ) ^ n * 2 ^ (γ : ℝ), by positivity⟩
  refine ⟨C, NNReal.coe_pos.mp (by change (0 : ℝ) < _ / _ + _; positivity), ?_⟩
  intro f M hf z R hR hcamp
  let good : Set ℝ^n :=
    {x | Tendsto (fun r ↦ ⨍ y in closedBall x r, f y) (𝓝[>] 0) (𝓝 (f x))}
  have hgood : ∀ᵐ x ∂volume, x ∈ good := by
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average volume hf 0] with x hx
    exact hx (fun _ : ℝ ↦ x) (fun r ↦ r) tendsto_id
      (Eventually.of_forall fun _ ↦ by simp)
  let S := ball z (R / 8) ∩ good
  have hS : HolderOnWith (C * M) γ f S := by
    apply holderOnWith_of_dist_bound
    intro x hx y hy
    have hxR : x ∈ ball z R := (ball_subset_ball (by linarith : R / 8 ≤ R)) hx.1
    have hyR : y ∈ ball z R := (ball_subset_ball (by linarith : R / 8 ≤ R)) hy.1
    have hxy : 2 * dist x y ≤ R := by
      linarith [dist_triangle_right x y z, mem_ball.mp hx.1, mem_ball.mp hy.1]
    change dist (f x) (f y) ≤
      (2 * (2 : ℝ) ^ n / (1 - (1 / 2 : ℝ) ^ (γ : ℝ)) +
        2 * (2 : ℝ) ^ n * 2 ^ (γ : ℝ)) * M * dist x y ^ (γ : ℝ)
    exact
      dist_le_of_meanOscillation hf hγR hxy (hcamp x hxR) (hcamp y hyR) hx.2 hy.2
  obtain ⟨g, hg, heq⟩ := (hS.uniformContinuousOn hγ).exists_continuous_eqOn
  have hclosure : ball z (R / 8) ⊆ closure S :=
    (volume.dense_of_ae hgood).open_subset_closure_inter isOpen_ball
  refine ⟨g, hg, ?_, ?_⟩
  · apply holderOnWith_of_dist_bound
    intro x hx y hy
    have hclosed : IsClosed {p : (ℝ^n) × (ℝ^n) |
        dist (g p.1) (g p.2) ≤ (C * M : ℝ≥0) * dist p.1 p.2 ^ (γ : ℝ)} :=
      isClosed_le ((hg.comp continuous_fst).dist (hg.comp continuous_snd))
        (continuous_const.mul ((continuous_fst.dist continuous_snd).rpow_const
          (fun _ ↦ Or.inr γ.coe_nonneg)))
    change (x, y) ∈ {p : (ℝ^n) × (ℝ^n) |
      dist (g p.1) (g p.2) ≤ (C * M : ℝ≥0) * dist p.1 p.2 ^ (γ : ℝ)}
    apply (hclosed.closure_subset_iff (s := S ×ˢ S)).mpr ?_ ?_
    · rintro ⟨a, b⟩ ⟨ha, hb⟩
      change dist (g a) (g b) ≤ _
      rw [heq ha, heq hb]
      exact hS.dist_le ha hb
    · rw [closure_prod_eq]
      exact ⟨hclosure hx, hclosure hy⟩
  · filter_upwards [ae_restrict_of_ae hgood, ae_restrict_mem isOpen_ball.measurableSet]
      with x hx hxball
    exact heq ⟨hxball, hx⟩

end PDE.Elliptic.Regularity.Campanato
