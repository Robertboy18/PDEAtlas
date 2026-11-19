/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Variational
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.InitialValue
import CAS.ExactTactic

/-!
# The initial trace and uniform spacetime estimates

For bounded uniformly continuous data, every positive tolerance admits a
global bound `|g(x) - g(y)| ≤ ε + Kε * dist x y`. Superlinearity then bounds
the initial error by `ε + Cε * t`, uniformly over space. Comparing equal
velocities preserves the spatial modulus, and dynamic programming gives the
same modulus for time increments.

Lipschitz data retain the sharper linear trace and spacetime estimates below,
even when unbounded. Bounded data give boundedness on each finite time slab.
For Lipschitz data these are the estimates of Lemma 2 in Evans, §3.3.2(b): the value is
Lipschitz on the closed forward half-space and equals the datum at time zero.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(b), Lemma 2 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi.HopfLax

open Filter
open scoped Topology

set_option linter.missingDocs true

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- Superlinearity provides a nonnegative constant controlling both the
lower cost estimate for `K`-Lipschitz data and the zero-velocity upper estimate. -/
theorem exists_trace_constant {L : E → ℝ} (hL : Superlinear L) (K : NNReal) :
    ∃ C : ℝ, 0 ≤ C ∧ L 0 ≤ C ∧ ∀ q, (K : ℝ) * ‖q‖ - C ≤ L q := by
  obtain ⟨B, hB⟩ := hL K
  refine ⟨max 0 (max B (L 0)), le_max_left _ _, ?_, ?_⟩
  · exact (le_max_right _ _).trans (le_max_right _ _)
  · exact fun q ↦ (sub_le_sub_left ((le_max_left B (L 0)).trans (le_max_right _ _)) _).trans (hB q)

/-- Every positive tolerance gives a global affine modulus for bounded uniformly
continuous data: use uniform continuity nearby and boundedness farther away. -/
private theorem exists_affine_modulus {X : Type*} [PseudoMetricSpace X] {g : X → ℝ}
    (hg : UniformContinuous g) (hgb : Bornology.IsBounded (Set.range g)) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : NNReal, ∀ x y, |g x - g y| ≤ ε + (K : ℝ) * dist x y := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp hg ε hε
  obtain ⟨M, hMpos, hM⟩ := hgb.exists_pos_norm_le
  have hK : 0 ≤ 2 * M / δ := div_nonneg (by positivity) hδ.le
  refine ⟨⟨2 * M / δ, hK⟩, fun x y ↦ ?_⟩
  change |g x - g y| ≤ ε + (2 * M / δ) * dist x y
  by_cases hxy : dist x y < δ
  · have hc : |g x - g y| < ε := by simpa only [Real.dist_eq] using hclose hxy
    linarith [mul_nonneg hK (dist_nonneg (x := x) (y := y))]
  · have hx : |g x| ≤ M := by simpa only [Real.norm_eq_abs] using hM (g x) ⟨x, rfl⟩
    have hy : |g y| ≤ M := by simpa only [Real.norm_eq_abs] using hM (g y) ⟨y, rfl⟩
    have hfar : 2 * M ≤ (2 * M / δ) * dist x y := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
      exact mul_le_mul_of_nonneg_left (not_lt.mp hxy) (by positivity)
    linarith [abs_sub (g x) (g y)]

/-- The Hopf–Lax value converges uniformly over all space to bounded
uniformly continuous data as time decreases to zero. Superlinearity suffices. -/
theorem tendstoUniformly_initial_right_of_uniformContinuous {L g : E → ℝ} (hL : Superlinear L)
    (hg : UniformContinuous g) (hgb : Bornology.IsBounded (Set.range g)) :
    TendstoUniformly (fun t : ℝ ↦ value L g t) g (𝓝[>] (0 : ℝ)) := by
  refine Metric.tendstoUniformly_iff.mpr fun ε hε ↦ ?_
  obtain ⟨K, hmod⟩ := exists_affine_modulus hg hgb (half_pos hε)
  obtain ⟨C, hC, hLC, hbound⟩ := exists_trace_constant hL K
  have hC1 : 0 < C + 1 := by linarith
  filter_upwards [Ioo_mem_nhdsGT (div_pos (half_pos hε) hC1)] with t ht
  intro x
  have hsmall : t * (C + 1) < ε / 2 := (lt_div_iff₀ hC1).mp ht.2
  have hb := abs_value_sub_data_le_of_modulus (half_pos hε).le hmod hbound hLC ht.1.le x
  have hCt : C * t ≤ t * (C + 1) := by nlinarith [ht.1]
  rw [Real.dist_eq, abs_sub_comm]
  linarith

/-- Uniform continuity of the datum is inherited at every nonnegative time.
Only an affine lower bound is needed to keep the cost infima finite; the
datum may be unbounded. -/
theorem uniformContinuous_value {L g : E → ℝ} (hL : Superlinear L) (hg : UniformContinuous g)
    {K : NNReal} {A : ℝ} (hlower : ∀ y, -A - (K : ℝ) * ‖y‖ ≤ g y) {t : ℝ} (ht : 0 ≤ t) :
    UniformContinuous (value L g t) := by
  refine Metric.uniformContinuous_iff.mpr fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp hg (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun x y hxy ↦ ?_⟩
  have hv : |value L g t x - value L g t y| ≤ ε / 2 := by
    refine abs_value_sub_le_of_translate_bound hL hlower ht x y fun z ↦ ?_
    have hd : dist (x - z) (y - z) = dist x y := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      abel
    have hc := hclose (a := x - z) (b := y - z) (by rwa [hd])
    simpa only [Real.dist_eq] using hc.le
  rw [Real.dist_eq]
  exact hv.trans_lt (half_lt_self hε)

/-- The positive-time formula converges to the prescribed initial datum.
The estimate used in the proof is uniform in the spatial point. -/
theorem tendsto_initial_right {L g : E → ℝ} (hL : Superlinear L)
    {K : NNReal} (hg : LipschitzWith K g) (x : E) :
    Tendsto (fun t : ℝ ↦ value L g t x) (𝓝[>] (0 : ℝ)) (𝓝 (g x)) := by
  obtain ⟨C, hC, hLC, hbound⟩ := exists_trace_constant hL K
  rw [Metric.tendsto_nhdsWithin_nhds]
  refine fun ε hε ↦ ⟨ε / (C + 1), by positivity, fun {t} ht hdist ↦ ?_⟩
  have ht : 0 < t := ht
  rw [Real.dist_eq, sub_zero, abs_of_pos ht, lt_div_iff₀ (by positivity)] at hdist
  rw [Real.dist_eq]
  linarith [abs_value_sub_data_le hg hbound le_rfl hLC ht.le x]

section ModulusTime

variable [ProperSpace E] {L g : E → ℝ}
    (hcont : Continuous L) (hL : Superlinear L)
    (hconv : ConvexOn ℝ Set.univ L) (hg : Continuous g)
    {K : NNReal} {A : ℝ} (hlower : ∀ y, -A - (K : ℝ) * ‖y‖ ≤ g y)
    {ε D C : ℝ} (hε : 0 ≤ ε)
    (hmod : ∀ x y, |g x - g y| ≤ ε + D * dist x y)
    (hLC : L 0 ≤ C) (hbound : ∀ q, D * ‖q‖ - C ≤ L q)

include hcont hL hconv hg hlower hε hmod hLC hbound

/-- Dynamic programming transfers the initial modulus estimate to an interval
starting at any nonnegative time, with the same constants. -/
private theorem abs_time_sub_le_of_le_of_modulus {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (x : E) :
    |value L g t x - value L g s x| ≤ ε + C * (t - s) := by
  rcases hst.eq_or_lt with rfl | hst
  · simpa only [sub_self, abs_zero, mul_zero, add_zero] using hε
  rcases hs.eq_or_lt with rfl | hs
  · simpa only [value_zero, sub_zero] using
      abs_value_sub_data_le_of_modulus hε hmod hbound hLC hst.le x
  have hsemigroup :=
    dynamic_programming_of_norm_lower_bound hcont hL hconv hg hlower hs (sub_pos.mpr hst) x
  rw [show s + (t - s) = t by ring] at hsemigroup
  rw [hsemigroup]
  exact abs_value_sub_data_le_of_modulus hε (abs_value_sub_le_of_modulus hL hlower hmod hs.le)
    hbound hLC (sub_pos.mpr hst).le x

/-- A spatial modulus, up to tolerance `ε`, gives the same tolerance for
every time increment. Dynamic programming transfers the initial estimate
to later times without changing its constants. -/
theorem abs_value_sub_time_le_of_modulus {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : E) :
    |value L g t x - value L g s x| ≤ ε + C * |t - s| := by
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using
      abs_time_sub_le_of_le_of_modulus hcont hL hconv hg hlower hε hmod hLC hbound hs hst x
  · have hh := abs_time_sub_le_of_le_of_modulus hcont hL hconv hg hlower hε hmod hLC hbound ht hts x
    simpa only [abs_sub_comm (value L g s x), abs_sub_comm t,
      abs_of_nonneg (sub_nonneg.mpr hts)] using hh

end ModulusTime

section Time

variable [ProperSpace E] {L g : E → ℝ}
    (hcont : Continuous L) (hL : Superlinear L)
    (hconv : ConvexOn ℝ Set.univ L) {K : NNReal} (hg : LipschitzWith K g)
    {C : ℝ} (hC : 0 ≤ C) (hLC : L 0 ≤ C)
    (hbound : ∀ q, (K : ℝ) * ‖q‖ - C ≤ L q)

include hcont hL hconv hg hLC hbound

/-- The initial-trace constant also bounds every time increment. -/
theorem abs_value_sub_time_le {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : E) :
    |value L g t x - value L g s x| ≤ C * |t - s| := by
  have hlower : ∀ y, -(-g 0) - (K : ℝ) * ‖y‖ ≤ g y := fun y ↦ by
    have h := hg.dist_le_mul y 0
    rw [Real.dist_eq, dist_zero_right] at h
    linarith [neg_le_abs (g y - g 0)]
  have hmod : ∀ x y, |g x - g y| ≤ (0 : ℝ) + (K : ℝ) * dist x y := fun x y ↦ by
    simpa only [zero_add, Real.dist_eq] using hg.dist_le_mul x y
  simpa only [zero_add] using abs_value_sub_time_le_of_modulus hcont hL hconv hg.continuous
    hlower le_rfl hmod hLC hbound hs ht x

/-- Spacetime Lipschitz continuity on the whole forward half-space.
The product uses its maximum norm. -/
theorem lipschitzOnWith_forward :
    LipschitzOnWith (K + ⟨C, hC⟩) (fun z : E × ℝ ↦ value L g z.2 z.1) {z | 0 ≤ z.2} := by
  refine LipschitzOnWith.of_dist_le_mul fun z hz w hw ↦ ?_
  have hx := (lipschitzWith_value hL hg hz).dist_le_mul z.1 w.1
  have ht := abs_value_sub_time_le hcont hL hconv hg hLC hbound hw hz w.1
  have htri := dist_triangle (value L g z.2 z.1) (value L g z.2 w.1) (value L g w.2 w.1)
  have hdx : dist z.1 w.1 ≤ dist z w := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hdt : |z.2 - w.2| ≤ dist z w := by
    rw [Prod.dist_eq, Real.dist_eq]
    exact le_max_right _ _
  simp only [Real.dist_eq] at htri hx
  change |value L g z.2 z.1 - value L g w.2 w.1| ≤ ((K : ℝ) + C) * dist z w
  linarith [mul_le_mul_of_nonneg_left hdx K.coe_nonneg, mul_le_mul_of_nonneg_left hdt hC]

end Time

section UniformContinuity

variable [ProperSpace E] {L g : E → ℝ}
    (hcont : Continuous L) (hL : Superlinear L)
    (hconv : ConvexOn ℝ Set.univ L) (hg : UniformContinuous g)
    (hgb : Bornology.IsBounded (Set.range g))

include hcont hL hconv hg hgb

/-- Bounded uniformly continuous data give a uniformly continuous value on
the whole forward spacetime half-space. The constants may depend on the
requested tolerance; no spatial or temporal Lipschitz claim is made. -/
theorem uniformContinuousOn_forward :
    UniformContinuousOn (fun z : E × ℝ ↦ value L g z.2 z.1) {z | 0 ≤ z.2} := by
  obtain ⟨M, hM⟩ := hgb.exists_norm_le
  have hlower : ∀ y, -M - ((0 : NNReal) : ℝ) * ‖y‖ ≤ g y := by
    intro y
    have hh : |g y| ≤ M := by
      simpa only [Real.norm_eq_abs] using hM (g y) ⟨y, rfl⟩
    simpa only [NNReal.coe_zero, zero_mul, sub_zero] using (abs_le.mp hh).1
  refine Metric.uniformContinuousOn_iff.mpr fun ε hε ↦ ?_
  have hquarter : 0 < ε / 4 := by positivity
  obtain ⟨D, hmod⟩ := exists_affine_modulus hg hgb hquarter
  obtain ⟨C, hC, hLC, hbound⟩ := exists_trace_constant hL D
  have hsum : 0 < (D : ℝ) + C + 1 := by positivity
  refine ⟨(ε / 2) / ((D : ℝ) + C + 1), div_pos (half_pos hε) hsum, fun z hz w hw hzw ↦ ?_⟩
  have hx := abs_value_sub_le_of_modulus hL hlower hmod hz z.1 w.1
  have ht := abs_value_sub_time_le_of_modulus hcont hL hconv hg.continuous
    hlower hquarter.le hmod hLC hbound hw hz w.1
  have hdx : dist z.1 w.1 ≤ dist z w := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hdt : |z.2 - w.2| ≤ dist z w := by
    rw [Prod.dist_eq, Real.dist_eq]
    exact le_max_right _ _
  have hxmul := mul_le_mul_of_nonneg_left hdx D.coe_nonneg
  have htmul := mul_le_mul_of_nonneg_left hdt hC
  have hsmall : dist z w * ((D : ℝ) + C + 1) < ε / 2 := (lt_div_iff₀ hsum).mp hzw
  have htri := dist_triangle (value L g z.2 z.1) (value L g z.2 w.1) (value L g w.2 w.1)
  have hd : 0 ≤ dist z w := dist_nonneg
  simp only [Real.dist_eq] at htri ⊢
  linarith

/-- The value of bounded uniformly continuous data is bounded and
uniformly continuous on every finite closed time slab. Superlinearity
provides the lower bound; the zero-velocity path provides the upper bound. -/
theorem boundedUniformContinuousOnSlabs :
    IsBoundedUniformContinuousOnSlabs (fun z : E × ℝ ↦ value L g z.2 z.1) := by
  have huc := uniformContinuousOn_forward hcont hL hconv hg hgb
  obtain ⟨M, hM⟩ := hgb.exists_norm_le
  have hlower : ∀ y, -M - ((0 : NNReal) : ℝ) * ‖y‖ ≤ g y := by
    intro y
    have hh : |g y| ≤ M := by
      simpa only [Real.norm_eq_abs] using hM (g y) ⟨y, rfl⟩
    simpa only [NNReal.coe_zero, zero_mul, sub_zero] using (abs_le.mp hh).1
  obtain ⟨C, hC, hLC, hbound⟩ := exists_trace_constant hL 0
  intro T _hT
  refine ⟨?_, huc.mono (fun z hz ↦ hz.1)⟩
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨M + C * T, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hlo := norm_lower_bound_value hlower hbound hz.1 z.1
  have hhi : value L g z.2 z.1 ≤ cost L g z.2 z.1 0 :=
    csInf_le (bddBelow_cost_of_norm_lower_bound hL hlower hz.1 z.1) ⟨0, rfl⟩
  have hdatum : |g z.1| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM (g z.1) ⟨z.1, rfl⟩
  have hdatumUpper := (abs_le.mp hdatum).2
  have htime := mul_le_mul_of_nonneg_left hz.2 hC
  have hcost := mul_le_mul_of_nonneg_left hLC hz.1
  simp only [NNReal.coe_zero, zero_mul, sub_zero] at hlo
  simp only [cost, smul_zero, sub_zero] at hhi
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

end UniformContinuity

end HamiltonJacobi.HopfLax

end
