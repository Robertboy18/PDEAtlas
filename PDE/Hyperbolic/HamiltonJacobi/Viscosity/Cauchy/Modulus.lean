/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.Cauchy.Barriers
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.Cauchy.Translations
public import PDE.Analysis.Topology.Semicontinuity.Piecewise

/-!
# The modulus of the Cauchy Perron envelope

Maximality against translated subsolutions proves the modulus, rather than
assuming continuity of the envelope. Forward time translations stay inside
the half-space. A backward translate is lowered by a positive constant and
pasted to the lower barrier before its starting time. The positive constant
ensures agreement near the seam and is sent to zero in the final inequality.
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi.Cauchy

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {H g : E → ℝ} {K : NNReal} {C : ℝ} {u : E × ℝ → ℝ}
  (hg : LipschitzWith K g) (hC : 0 ≤ C)
  (hlsub : IsSpatialViscositySubsolution (fun p _ ↦ H p) positiveTimeDomain
    (fun z : E × ℝ ↦ g z.1 - C * z.2))
  (hu : UpperSemicontinuousOn u positiveTimeDomain)
  (husub : IsSpatialViscositySubsolution (fun p _ ↦ H p) positiveTimeDomain u)
  (hub : ∀ z ∈ positiveTimeDomain, g z.1 - C * z.2 ≤ u z ∧ u z ≤ g z.1 + C * z.2)
  (hmax : ∀ v : E × ℝ → ℝ, UpperSemicontinuousOn v positiveTimeDomain →
    IsSpatialViscositySubsolution (fun p _ ↦ H p) positiveTimeDomain v →
    (∀ z ∈ positiveTimeDomain, g z.1 - C * z.2 ≤ v z ∧ v z ≤ g z.1 + C * z.2) →
    ∀ z ∈ positiveTimeDomain, v z ≤ u z)

include hg hlsub hu husub hub hmax in
/-- A forward spacetime translate, lowered by the barrier modulus, lies below
the greatest subsolution. This also gives its spatial Lipschitz estimate. -/
theorem translate_le_of_greatest_subsolution (a : E × ℝ) (ha : 0 ≤ a.2) {z : E × ℝ} (hz : 0 < z.2) :
    u (z + a) - ((K : ℝ) * ‖a.1‖ + C * a.2) ≤ u z := by
  let l : E × ℝ → ℝ := fun w ↦ g w.1 - C * w.2
  let c : ℝ := (K : ℝ) * ‖a.1‖ + C * a.2
  let v : E × ℝ → ℝ := fun w ↦ u (w + a) - c
  have hmap : MapsTo (· + a) positiveTimeDomain positiveTimeDomain := by
    intro w hw
    change 0 < w.2 + a.2
    exact add_pos_of_pos_of_nonneg hw ha
  have hl : Continuous l := (hg.continuous.comp continuous_fst).sub
    (continuous_const.mul continuous_snd)
  have hv : UpperSemicontinuousOn v positiveTimeDomain := by
    simpa only [v, sub_eq_add_neg, Function.comp_def, Pi.add_apply, id_eq] using!
      (hu.comp (continuous_id.add continuous_const).continuousOn hmap).add
        (continuous_const.continuousOn.upperSemicontinuousOn)
  have hvsub := husub.translate_sub_const a c isOpen_positiveTimeDomain hmap
  have hvb : ∀ w ∈ positiveTimeDomain, v w ≤ g w.1 + C * w.2 := by
    intro w hw
    have hbound := (hub (w + a) (hmap hw)).2
    have hdist := (hg.norm_sub_le (w.1 + a.1) w.1)
    simp only [Real.norm_eq_abs, add_sub_cancel_left] at hdist
    have hgupper := (abs_le.mp hdist).2
    dsimp [v, c] at *
    nlinarith only [hbound, hgupper]
  have hle := hmax (fun w ↦ max (l w) (v w))
    (hl.continuousOn.upperSemicontinuousOn.sup hv) (hlsub.max hvsub)
    (fun w hw ↦ ⟨le_max_left _ _, max_le ((hub w hw).1.trans (hub w hw).2) (hvb w hw)⟩) z hz
  exact (le_max_right _ _).trans hle

include hg hC hlsub hu husub hub hmax in
/-- A backward translate can be pasted to the lower barrier. The conclusion
has no error term: the strictly positive pasting margin is sent to zero. -/
theorem backward_translate_le_of_greatest_subsolution
    (s : ℝ) (hs : 0 ≤ s) {z : E × ℝ} (hz : s < z.2) :
    u (z.1, z.2 - s) - C * s ≤ u z := by
  classical
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  let l : E × ℝ → ℝ := fun w ↦ g w.1 - C * w.2
  let V : Set (E × ℝ) := {w | s < w.2}
  let a : E × ℝ := (0, -s)
  let ψ : E × ℝ → ℝ := fun w ↦ u (w + a) - (C * s + ε)
  let v : E × ℝ → ℝ := V.piecewise (fun w ↦ max (l w) (ψ w)) l
  have hV : IsOpen V := isOpen_lt continuous_const continuous_snd
  have hzU : z ∈ positiveTimeDomain := hs.trans_lt hz
  have hmap : MapsTo (· + a) (positiveTimeDomain ∩ V) positiveTimeDomain := by
    intro w hw
    change 0 < w.2 + -s
    have := hw.2
    dsimp [V] at this
    linarith only [this]
  have hl : Continuous l := (hg.continuous.comp continuous_fst).sub
    (continuous_const.mul continuous_snd)
  have hψ : UpperSemicontinuousOn ψ (positiveTimeDomain ∩ V) := by
    simpa only [ψ, sub_eq_add_neg, Function.comp_def, Pi.add_apply, id_eq] using!
      (hu.comp (continuous_id.add continuous_const).continuousOn hmap).add
        (continuous_const.continuousOn.upperSemicontinuousOn)
  have hψsub := husub.translate_sub_const a (C * s + ε) (isOpen_positiveTimeDomain.inter hV) hmap
  have hglue : ∀ w ∈ positiveTimeDomain, w ∉ V →
      ∀ᶠ y in 𝓝[positiveTimeDomain] w, y ∈ V → ψ y ≤ l y := by
    intro w _ hw
    have hws : w.2 ≤ s := le_of_not_gt hw
    have hmargin : 2 * C * (w.2 - s) < ε :=
      lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hws)) hε
    have hnear : ∀ᶠ y in 𝓝 w, 2 * C * (y.2 - s) < ε :=
      (by fun_prop : ContinuousAt (fun y : E × ℝ ↦ 2 * C * (y.2 - s)) w).eventually
        (eventually_lt_nhds hmargin)
    filter_upwards [mem_nhdsWithin_of_mem_nhds hnear, self_mem_nhdsWithin] with y hy hyU hyV
    have hb := (hub (y + a) (hmap ⟨hyU, hyV⟩)).2
    dsimp [ψ, a, l] at *
    simp only [add_zero] at hb ⊢
    nlinarith only [hb, hy]
  have hv : UpperSemicontinuousOn v positiveTimeDomain :=
    PDE.upperSemicontinuousOn_piecewise_max hl.continuousOn.upperSemicontinuousOn hV hψ hglue
  have hvsub : IsSpatialViscositySubsolution (fun p _ ↦ H p) positiveTimeDomain v :=
    Perron.isSpatialViscositySubsolution_piecewise_max hlsub hV hψsub hglue
  have hvb : ∀ w ∈ positiveTimeDomain,
      g w.1 - C * w.2 ≤ v w ∧ v w ≤ g w.1 + C * w.2 := by
    intro w hw
    by_cases hwV : w ∈ V
    · dsimp only [v]
      rw [piecewise_eq_of_mem _ _ _ hwV]
      refine ⟨le_max_left _ _, max_le ((hub w hw).1.trans (hub w hw).2) ?_⟩
      have hb := (hub (w + a) (hmap ⟨hw, hwV⟩)).2
      dsimp [ψ, a] at *
      simp only [add_zero] at hb ⊢
      nlinarith only [hb, mul_nonneg hC hs, hε]
    · dsimp only [v]
      rw [piecewise_eq_of_notMem _ _ _ hwV]
      exact ⟨le_rfl, (hub w hw).1.trans (hub w hw).2⟩
  have hle := hmax v hv hvsub hvb z hzU
  have hψle : ψ z ≤ u z := by
    apply (le_max_right (l z) (ψ z)).trans
    change V.piecewise (fun w ↦ max (l w) (ψ w)) l z ≤ u z at hle
    rwa [piecewise_eq_of_mem _ _ _ (show z ∈ V from hz)] at hle
  change u (z.1 + 0, z.2 + -s) - (C * s + ε) ≤ u z at hψle
  simp only [add_zero, ← sub_eq_add_neg] at hψle
  linarith only [hψle]

include hg hC hlsub hu husub hub hmax in
/-- The greatest subsolution inherits the datum's spatial Lipschitz constant
and the barrier's time Lipschitz constant. -/
theorem abs_sub_le_of_greatest_subsolution {z w : E × ℝ} (hz : 0 < z.2) (hw : 0 < w.2) :
    |u z - u w| ≤ (K : ℝ) * ‖z.1 - w.1‖ + C * |z.2 - w.2| := by
  have hforward := translate_le_of_greatest_subsolution hg hlsub hu husub hub hmax
  have hback := backward_translate_le_of_greatest_subsolution hg hC hlsub hu husub hub hmax
  have hspace : ∀ x y : E, ∀ t : ℝ, 0 < t →
      |u (x, t) - u (y, t)| ≤ (K : ℝ) * ‖x - y‖ := by
    intro x y t ht
    have hxy := hforward (x - y, 0) le_rfl (z := (y, t)) ht
    have hyx := hforward (y - x, 0) le_rfl (z := (x, t)) ht
    simp only [Prod.mk_add_mk, add_sub_cancel, add_zero, mul_zero, norm_sub_rev y x] at hxy hyx
    exact abs_le.mpr ⟨by linarith only [hyx], by linarith only [hxy]⟩
  have htimeOrdered : ∀ x : E, ∀ s t : ℝ, 0 < s → s ≤ t →
      |u (x, t) - u (x, s)| ≤ C * (t - s) := by
    intro x s t hs hst
    have hf := hforward (0, t - s) (sub_nonneg.mpr hst) (z := (x, s)) hs
    have hb := hback (t - s) (sub_nonneg.mpr hst) (z := (x, t)) (by linarith)
    simp only [Prod.mk_add_mk, add_zero, add_sub_cancel, norm_zero, mul_zero,
      zero_add, sub_sub_cancel] at hf hb
    exact abs_le.mpr ⟨by linarith only [hb], by linarith only [hf]⟩
  have htime : |u (w.1, z.2) - u (w.1, w.2)| ≤ C * |z.2 - w.2| := by
    rcases le_total w.2 z.2 with h | h
    · simpa only [abs_of_nonneg (sub_nonneg.mpr h)] using htimeOrdered w.1 w.2 z.2 hw h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      have ht := htimeOrdered w.1 z.2 w.2 hz h
      rw [abs_sub_comm] at ht
      linarith only [ht]
  exact (abs_sub_le (u z) (u (w.1, z.2)) (u w)).trans (add_le_add (hspace z.1 w.1 z.2 hz) htime)

include hg hC hlsub hu husub hub hmax in
/-- In particular, the envelope is Lipschitz on the positive-time half-space
for the usual product metric. -/
theorem lipschitzOnWith_of_greatest_subsolution :
    LipschitzOnWith (K + ⟨C, hC⟩) u positiveTimeDomain := by
  refine LipschitzOnWith.of_dist_le_mul fun z hz w hw ↦ ?_
  have h := abs_sub_le_of_greatest_subsolution hg hC hlsub hu husub hub hmax hz hw
  rw [Real.dist_eq]
  apply h.trans
  have hx : ‖z.1 - w.1‖ ≤ dist z w := by
    rw [Prod.dist_eq, dist_eq_norm]
    exact le_max_left _ _
  have ht : |z.2 - w.2| ≤ dist z w := by
    rw [Prod.dist_eq, Real.dist_eq]
    exact le_max_right _ _
  change _ ≤ ((K : ℝ) + C) * dist z w
  nlinarith only [mul_le_mul_of_nonneg_left hx K.coe_nonneg, mul_le_mul_of_nonneg_left ht hC]

end HamiltonJacobi.Cauchy
