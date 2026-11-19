/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.UpToBoundary
public import PDE.Spaces.Sobolev.Approximation.Mollification.Congruence
import Mathlib.Topology.TietzeExtension
import CAS.ExactTactic

/-!
# Inward mollification of continuous representatives

An inward ball condition on an open domain also leaves a smaller mollifier ball
at points of its closure. On such a ball, mollification depends only on the
representative inside the domain. Tietze extension and the approximate identity
theorem then identify the pointwise boundary limit without any differentiability
assumption on the continuous representative.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace SobolevSpace.Approximation.UpToBoundary

open GraphSpace

variable {n : ℕ}

/-- An inward ball condition extends to the closure if the radius is halved. -/
theorem closedBall_subset_of_inward_ball {Ω V : Set (ℝ^n)} (hV : IsOpen V)
    (v : ℝ^n) {t : ℝ} (ht : 0 < t)
    (hball : ∀ z ∈ V ∩ Ω, closedBall (z + t • v) t ⊆ Ω)
    {x : ℝ^n} (hx : x ∈ V ∩ closure Ω) :
    closedBall (x + t • v) (t / 2) ⊆ Ω := by
  obtain ⟨z, hz, hxz⟩ := mem_closure_iff.mp (hV.inter_closure hx) (t / 2) (half_pos ht)
  intro y hy
  apply hball z hz
  have hdist : dist (x + t • v) (z + t • v) = dist x z := dist_add_right _ _ _
  have htri := dist_triangle y (x + t • v) (z + t • v)
  rw [hdist] at htri
  change dist y (z + t • v) ≤ t
  change dist y (x + t • v) ≤ t / 2 at hy
  linarith

/-- Mollification at centers converging to `x` converges to the value of a continuous
function at `x`. Both the center and the mollifier scale may vary. -/
theorem mollify_tendsto_of_continuous_of_tendsto (μ : Mollifier n)
    {f : ℝ^n → ℝ} (hf : Continuous f)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (hε0 : Tendsto ε atTop (𝓝 0))
    {x : ℝ^n} (a : ℕ → ℝ^n) (ha : Tendsto a atTop (𝓝 x)) :
    Tendsto (fun j ↦ mollify μ (ε j) f (a j)) atTop (𝓝 (f x)) := by
  simpa only [mollify, convolution] using
    (convolution_tendsto_right (μ := (volume : Measure (ℝ^n)))
      (g := fun _j : ℕ ↦ f) (φ := fun j ↦ scaled μ (ε j)) (k := a)
      (hnφ := Eventually.of_forall fun j y ↦ scaled_nonneg μ (hε j) y)
      (hiφ := Eventually.of_forall fun j ↦ scaled_integral_one μ (hε j))
      (hφ := tendsto_support_scaled μ ε hε hε0)
      (hmg := Eventually.of_forall fun _ ↦ hf.aestronglyMeasurable)
      (hcg := hf.continuousAt.tendsto.comp tendsto_snd) (hk := ha))

/-- Inward mollifications recover any representative continuous on the closure.
The function being mollified only has to agree with that representative inside. -/
theorem mollify_inward_tendsto (μ : Mollifier n) {R : ℝ} (hR : 0 < R)
    (hμ : tsupport μ.ρ ⊆ closedBall (0 : ℝ^n) R)
    {Ω V : Set (ℝ^n)} (hΩ : IsOpen Ω) (hV : IsOpen V)
    {f g : ℝ^n → ℝ} (hf : ContinuousOn f (closure Ω))
    (hgf : g =ᵐ[domainMeasure n Ω] f)
    (v : ℝ^n) (t : ℕ → ℝ) (ht : ∀ j, 0 < t j)
    (ht0 : Tendsto t atTop (𝓝 0))
    (hball : ∀ j, ∀ z ∈ V ∩ Ω, closedBall (z + t j • v) (t j) ⊆ Ω)
    {x : ℝ^n} (hx : x ∈ V ∩ closure Ω) :
    Tendsto (fun j ↦ mollify μ (t j / (2 * R)) g (x + t j • v))
      atTop (𝓝 (f x)) := by
  let F : C(closure Ω, ℝ) := ⟨fun z ↦ f z, hf.domRestrict⟩
  obtain ⟨G, hG⟩ := F.exists_restrict_eq isClosed_closure
  have hGeq (z : ℝ^n) (hz : z ∈ closure Ω) : G z = f z :=
    congrArg (fun H : C(closure Ω, ℝ) ↦ H ⟨z, hz⟩) hG
  have hgG : g =ᵐ[domainMeasure n Ω] G := by
    filter_upwards [hgf, ae_restrict_mem hΩ.measurableSet] with z hz hzΩ
    exact hz.trans (hGeq z (subset_closure hzΩ)).symm
  have hε (j : ℕ) : 0 < t j / (2 * R) := div_pos (ht j) (by positivity)
  have heq (j : ℕ) :
      mollify μ (t j / (2 * R)) g (x + t j • v) =
        mollify μ (t j / (2 * R)) G (x + t j • v) := by
    apply mollify_eq_of_ae_on μ (hε j) hμ hΩ.measurableSet hgG
    have hr : t j / (2 * R) * R = t j / 2 := by cas using hR
    rw [hr]
    exact closedBall_subset_of_inward_ball hV v (ht j) (hball j) hx
  simp_rw [heq]
  rw [← hGeq x hx.2]
  apply mollify_tendsto_of_continuous_of_tendsto μ G.continuous _ hε
  · simpa only [zero_div] using ht0.div_const (2 * R)
  · simpa only [zero_smul, add_zero] using
      tendsto_const_nhds.add (ht0.smul_const v)

end SobolevSpace.Approximation.UpToBoundary
