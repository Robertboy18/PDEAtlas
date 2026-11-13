/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Strongly measurable joint representatives

Summably accurate simple approximations of an Lᵖ-valued map yield joint representatives
for every parameter, including when `p = ∞`. A measurable cutoff to the set of absolute
convergence makes the approximating series converge everywhere. The complete normed
target need not be separable, and neither measure needs to be finite.
-/

@[expose] public section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] {ν : Measure β}

/-- Evaluating the finitely many Lᵖ values of a simple function gives a jointly strongly
measurable function. No measurable choice of representatives over all of Lᵖ is required. -/
theorem SimpleFunc.stronglyMeasurable_uncurry_Lp
    {p : ℝ≥0∞} (s : SimpleFunc α (Lp E p ν)) :
    StronglyMeasurable (fun z : α × β ↦ (s z.1) z.2) := by
  classical
  let F (v : Lp E p ν) (z : α × β) : E := if s z.1 = v then v z.2 else 0
  have hF (v : Lp E p ν) : StronglyMeasurable (F v) := by
    apply StronglyMeasurable.ite
      ((s.measurableSet_fiber v).preimage measurable_fst)
    · exact (Lp.stronglyMeasurable v).comp_measurable measurable_snd
    · exact stronglyMeasurable_const
  have hsum := s.range.stronglyMeasurable_fun_sum (fun v _ ↦ hF v)
  have heq : (fun z : α × β ↦ ∑ v ∈ s.range, F v z) =
      fun z : α × β ↦ (s z.1) z.2 := by
    funext z
    rw [Finset.sum_eq_single (s z.1)]
    · simp only [F, ite_eq_left rfl]
    · intro v _ hv
      exact ite_eq_right (Ne.symm hv)
    · exact fun h ↦ (h (s.mem_range_self z.1)).elim
  exact heq ▸ hsum

/-- A strongly measurable Lᵖ-valued map has a jointly strongly measurable representative
agreeing with every spatial section almost everywhere, for any complete normed additive
commutative target and `1 ≤ p`, including `p = ∞`. No measurable structure or separability
assumption on the target is needed. -/
theorem StronglyMeasurable.exists_stronglyMeasurable_jointLpRepresentative {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E] [CompleteSpace E]
    {ν : Measure β} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {u : α → Lp E p ν} (hu : StronglyMeasurable u) :
    ∃ U : α × β → E, StronglyMeasurable U ∧
      ∀ t, (fun x ↦ U (t, x)) =ᵐ[ν] (u t : β → E) := by
  classical
  have hex (n : ℕ) (t : α) : ∃ k, dist (hu.approx k t) (u t) < (1 / 2 : ℝ) ^ n :=
    ((hu.tendsto_approx t).eventually
      (Metric.ball_mem_nhds _ (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n))).exists
  let k (n : ℕ) (t : α) := Nat.find (hex n t)
  let w (n : ℕ) (t : α) : Lp E p ν := hu.approx (k n t) t
  let R (n : ℕ) (z : α × β) : E := w n z.1 z.2
  have hclose (n : ℕ) (t : α) : dist (w n t) (u t) < (1 / 2 : ℝ) ^ n :=
    Nat.find_spec (hex n t)
  have hR (n : ℕ) : StronglyMeasurable (R n) := by
    borelize E
    refine stronglyMeasurable_iff_measurable_separable.mpr ⟨?_, ?_⟩
    · apply Measurable.find
        (fun j ↦ (hu.approx j).stronglyMeasurable_uncurry_Lp.measurable)
        (fun j ↦ _root_.measurableSet_lt
          (((hu.approx j).stronglyMeasurable.comp_measurable measurable_fst).dist
            (hu.comp_measurable measurable_fst)).measurable measurable_const)
        (fun z ↦ hex n z.1)
    · have hsep : TopologicalSpace.IsSeparable
          (⋃ j, range (fun z : α × β ↦ (hu.approx j z.1) z.2)) :=
        .iUnion fun j ↦ (hu.approx j).stronglyMeasurable_uncurry_Lp.isSeparable_range
      apply hsep.mono
      rintro _ ⟨z, rfl⟩
      exact mem_iUnion_of_mem (k n z.1) (mem_range_self z)
  have hgeo : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hnorm (t : α) : Summable (fun n ↦ ‖w (n + 1) t - w n t‖) :=
    ((summable_nat_add_iff 1).mpr hgeo |>.add hgeo).of_nonneg_of_le (fun n ↦ norm_nonneg _)
      fun n ↦ (dist_eq_norm _ _).symm.trans_le <| (dist_triangle _ (u t) _).trans
        (add_le_add (hclose (n + 1) t).le (by simpa only [dist_comm] using (hclose n t).le))
  have hlim (t : α) : Tendsto (fun n ↦ w n t) atTop (𝓝 (u t)) :=
    tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero (fun n ↦ dist_nonneg)
      (fun n ↦ (hclose n t).le)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  have hsum (t : α) : HasSum (fun n ↦ w (n + 1) t - w n t) (u t - w 0 t) := by
    rw [hasSum_iff_tendsto_nat_of_summable_norm (hnorm t)]
    simpa only [Finset.sum_range_sub (fun n ↦ w n t)] using (hlim t).sub_const (w 0 t)
  -- Outside absolute convergence, set the increments to zero. Their partial sums then
  -- converge everywhere, so the joint limit is strongly measurable in an arbitrary target.
  let D (n : ℕ) (z : α × β) := R (n + 1) z - R n z
  let A := {z : α × β | ∑' n : ℕ, ‖D n z‖ₑ ≠ ∞}
  have hA : MeasurableSet A :=
    (_root_.measurableSet_eq_fun (Measurable.tsum fun n ↦
      ((hR (n + 1)).sub (hR n)).enorm) measurable_const).compl
  let V (n : ℕ) := A.indicator (D n)
  have hV (n : ℕ) : StronglyMeasurable (V n) :=
    ((hR (n + 1)).sub (hR n)).indicator hA
  have hVs (z : α × β) : Summable (fun n ↦ V n z) := by
    by_cases hz : z ∈ A
    · simpa only [V, indicator_of_mem hz] using
        (tsum_enorm_ne_top_iff_summable_norm.mp hz).of_norm
    · simp only [V, indicator_of_notMem hz]
      exact summable_zero
  have hsumV : StronglyMeasurable (fun z ↦ ∑' n, V n z) :=
    stronglyMeasurable_of_tendsto (u := atTop)
      (fun m ↦ (Finset.range m).stronglyMeasurable_fun_sum fun n _ ↦ hV n)
      (tendsto_pi_nhds.mpr fun z ↦ (hVs z).hasSum.tendsto_sum_nat)
  refine ⟨fun z ↦ R 0 z + ∑' n : ℕ, V n z, (hR 0).add hsumV, fun t ↦ ?_⟩
  have hd : ∀ᵐ x ∂ν, ∀ n : ℕ,
      (w (n + 1) t - w n t : Lp E p ν) x = w (n + 1) t x - w n t x :=
    ae_all_iff.mpr fun n ↦ Lp.coeFn_sub _ _
  have hAae : ∀ᵐ x ∂ν, (t, x) ∈ A := by
    have h := summable_norm_of_tsum_eLpNorm_ne_top (Fact.out : 1 ≤ p)
      (f := fun n ↦ (w (n + 1) t - w n t : Lp E p ν)) (by
        simpa only [Lp.enorm_def] using
          tsum_enorm_ne_top_iff_summable_norm.mpr (hnorm t))
    filter_upwards [h, hd] with x hx hxd
    apply tsum_enorm_ne_top_iff_summable_norm.mpr
    simpa only [D, R, ← hxd] using hx
  filter_upwards [Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr (hnorm t)),
    Lp.coeFn_sub (u t) (w 0 t), hd, hAae] with x hxsum hxsub hxd hxA
  have heq : (∑' n : ℕ, (R (n + 1) (t, x) - R n (t, x))) = u t x - R 0 (t, x) := by
    calc
      _ = ∑' n : ℕ, (w (n + 1) t - w n t : Lp E p ν) x :=
        tsum_congr fun n ↦ (hxd n).symm
      _ = (∑' n : ℕ, (w (n + 1) t - w n t) : Lp E p ν) x := hxsum.symm
      _ = (u t - w 0 t : Lp E p ν) x := congrArg (fun v : Lp E p ν ↦ v x) (hsum t).tsum_eq
      _ = _ := hxsub
  simp only [V, indicator_of_mem hxA, D, heq, add_sub_cancel]


end MeasureTheory
