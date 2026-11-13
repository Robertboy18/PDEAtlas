/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.Cutoff.Bounds
public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.Convergence
public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Graph.Convergence
import PDE.Spaces.Sobolev.Fractional.Domain.Localization.C1

/-!
# Expanding cutoffs converge in the fractional graph

Multiplication by the standard cutoff at radius `R` approaches the identity
as `R` tends to infinity. This controls both the `Lᵖ` tail and the weighted
difference quotient, on an arbitrary domain.

The cutoff has compact support in the ambient space. Its support need not lie
inside the domain.
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology
open SobolevSpace.Approximation

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)} {p : ℝ≥0∞}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Truncation by the standard smooth cutoff preserves the fractional space. -/
theorem MemGagliardo.cutoff {u : ℝ^n → F}
    (hu : MemGagliardo n s Ω u (p := p)) (hs0 : 0 < s) (hs1 : s < 1)
    (hp0 : p ≠ 0) (hp : p ≠ ∞) {R : ℝ} (hR : R ≠ 0) :
    MemGagliardo n s Ω (fun x ↦ cutoff R x • u x) (p := p) :=
  Localization.memGagliardo_smul_of_contDiff_hasCompactSupport hs0 hs1
    ((cutoff_contDiff R).of_le (by simp)) (cutoff_hasCompactSupport hR) hu hp0 hp

namespace GagliardoSpace

variable [Fact (1 ≤ p)]

/-- Expanding cutoffs converge to the original function in the full fractional
graph norm, for every finite exponent at least one. -/
theorem tendsto_cutoff_ofFunction (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    {u : ℝ^n → F} (hu : MemGagliardo n s Ω u (p := p))
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (R : ι → ℝ) (hpos : ∀ i, 0 < R i) (hR : Tendsto R l atTop) :
    Tendsto (fun i ↦ ofFunction (fun x ↦ cutoff (R i) x • u x)
      (hu.cutoff hs0 hs1 (ne_of_gt (zero_lt_one.trans_le Fact.out)) hp (hpos i).ne'))
      l (𝓝 (ofFunction u hu)) := by
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))
  let φ (i : ι) (x : ℝ^n) := cutoff (R i) x - 1
  obtain ⟨L, hL⟩ := exists_lipschitzWith_cutoff (n := n)
  have hLip : ∀ᶠ i in l, LipschitzWith L (φ i) := by
    filter_upwards [hR.eventually (eventually_ge_atTop 1)] with i hi
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [φ, dist_sub_right] using (hL (R i) hi).dist_le_mul x y
  have hbound : ∀ᶠ i in l, ∀ x, ‖φ i x‖ ≤ (1 : ℝ≥0) :=
    Eventually.of_forall fun i x ↦ by
      rw [Real.norm_eq_abs, NNReal.coe_one]
      apply abs_le.mpr
      constructor <;> dsimp only [φ]
      · linarith [cutoff_nonneg (R i) x]
      · linarith [cutoff_le_one (R i) x]
  have hzero : ∀ᵐ x ∂volume.restrict Ω, Tendsto (fun i ↦ φ i x) l (𝓝 0) := by
    apply ae_of_all
    intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_cutoff_eq_one hR x] with i hi
    simp only [φ, hi, sub_self]
  have hbase := Localization.tendsto_eLpNorm_smul_zero hp0 hp
    (hLip.mono fun i hi ↦ hi.continuous.aestronglyMeasurable) hbound hu.1 hzero
  have hdiff := Localization.tendsto_eLpNorm_diffQuot_smul_zero
    hs0 hs1 hp0 hp hLip hbound hu hzero
  apply (tendsto_ofFunction_iff _ hu).2
  constructor
  · convert hbase using 1
    funext i
    congr 1
    funext x
    simp only [Pi.sub_apply, φ, sub_smul, one_smul]
  · convert hdiff using 1
    funext i
    congr 1
    funext z
    simp only [diffQuot, Pi.sub_apply, φ, sub_smul, one_smul, smul_sub]
    abel

end GagliardoSpace

end SobolevSpace.Fractional
