/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Dynamics.Flow.Limit
public import PDE.Analysis.Evolution.ODE.Autonomous.Scalar.Interval

/-!
# Scalar heteroclinic connections

Between consecutive equilibria, a C¹ scalar field of strict sign has a whole-line
C² connection through every interior state. Bounded monotone orbits have limits,
and the flow law makes those limits equilibria. Time reversal gives the negative
orientation without a second existence argument.

These are the scalar connections behind the traveling waves of Evans §11.4.1, where a
profile solves `v̇ = G(v)` with `G(u_l) = G(u_r) = 0` (equations (14) and (15)).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.1, equations (10), (14) and (15).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace PDE.Analysis.Evolution.Scalar

/-- A positive field between two equilibria has a strictly increasing C² connection
through every interior state. Endpoint zeros may be degenerate. -/
theorem exists_heteroclinic_of_pos {f : ℝ → ℝ} {a b x₀ : ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc a b))
    (ha : f a = 0) (hb : f b = 0)
    (hpos : ∀ z ∈ Ioo a b, 0 < f z) (hx₀ : x₀ ∈ Ioo a b) :
    ∃ x : ℝ → ℝ,
      x 0 = x₀ ∧ ContDiff ℝ 2 x ∧
      (∀ t, HasDerivAt x (f (x t)) t) ∧
      (∀ t, x t ∈ Ioo a b) ∧ StrictMono x ∧
      Tendsto x atBot (𝓝 a) ∧ Tendsto x atTop (𝓝 b) ∧
      Tendsto (deriv x) atBot (𝓝 0) ∧ Tendsto (deriv x) atTop (𝓝 0) := by
  have hab : a < b := hx₀.1.trans hx₀.2
  obtain ⟨Φ, _, _, hmem, hd⟩ := exists_flow_Ioo hab hf ha hb
  let x : ℝ → ℝ := fun t ↦ Φ t x₀
  have hzero : x 0 = x₀ := Φ.map_zero_apply x₀
  have hx (t : ℝ) : x t ∈ Ioo a b := hmem x₀ hx₀ t
  have hdx (t : ℝ) : HasDerivAt x (f (x t)) t := hd x₀ hx₀ t
  have hmono : StrictMono x := strictMono_of_hasDerivAt_pos hdx (fun t ↦ hpos _ (hx t))
  have hboundedAbove : BddAbove (range x) := by
    refine ⟨b, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact (hx t).2.le
  have hboundedBelow : BddBelow (range x) := by
    refine ⟨a, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact (hx t).1.le
  have hleft : Tendsto x atBot (𝓝 (sInf (range x))) :=
    tendsto_atBot_ciInf hmono.monotone hboundedBelow
  have hright : Tendsto x atTop (𝓝 (sSup (range x))) :=
    tendsto_atTop_ciSup hmono.monotone hboundedAbove
  have hclosed (t : ℝ) : x t ∈ Icc a b := ⟨(hx t).1.le, (hx t).2.le⟩
  have hleft_mem := isClosed_Icc.mem_of_tendsto hleft (Eventually.of_forall hclosed)
  have hright_mem := isClosed_Icc.mem_of_tendsto hright (Eventually.of_forall hclosed)
  have hinf : sInf (range x) ≤ x₀ := by
    simpa only [hzero] using csInf_le hboundedBelow (mem_range_self (0 : ℝ))
  have hsup : x₀ ≤ sSup (range x) := by
    simpa only [hzero] using le_csSup hboundedAbove (mem_range_self (0 : ℝ))
  have hnotfixed (z : ℝ) (hz : z ∈ Ioo a b) (hfix : ∀ t, Φ t z = z) : False := by
    have hcurve : (fun t ↦ Φ t z) = fun _ : ℝ ↦ z := funext hfix
    have hderiv : HasDerivAt (fun _ : ℝ ↦ z) (f z) 0 := by
      simpa only [Φ.map_zero_apply, hcurve] using hd z hz 0
    exact (hpos z hz).ne' (hderiv.unique (hasDerivAt_const 0 z))
  have hinf_eq : sInf (range x) = a := by
    apply le_antisymm _ hleft_mem.1
    by_contra h
    exact hnotfixed _ ⟨lt_of_not_ge h, hinf.trans_lt hx₀.2⟩
      (fun t ↦ Φ.map_eq_of_tendsto_atBot hleft t)
  have hsup_eq : sSup (range x) = b := by
    apply le_antisymm hright_mem.2
    by_contra h
    exact hnotfixed _ ⟨hx₀.1.trans_le hsup, lt_of_not_ge h⟩
      (fun t ↦ Φ.map_eq_of_tendsto_atTop hright t)
  have hleft' : Tendsto x atBot (𝓝 a) := by simpa only [hinf_eq] using hleft
  have hright' : Tendsto x atTop (𝓝 b) := by simpa only [hsup_eq] using hright
  have hderiv_eq : deriv x = fun t ↦ f (x t) := funext (fun t ↦ (hdx t).deriv)
  have hdiff : Differentiable ℝ x := fun t ↦ (hdx t).differentiableAt
  have hmaps : MapsTo x univ (Icc a b) := fun t _ ↦ hclosed t
  have hC1 : ContDiff ℝ 1 x := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨hdiff, ?_⟩
    rw [hderiv_eq]
    exact continuousOn_univ.mp (hf.continuousOn.comp hdiff.continuous.continuousOn hmaps)
  have hC2 : ContDiff ℝ 2 x := by
    apply (contDiff_succ_iff_deriv (n := 1)).mpr
    refine ⟨hdiff, by simp, ?_⟩
    rw [hderiv_eq]
    exact contDiffOn_univ.mp (hf.comp hC1.contDiffOn hmaps)
  have hvelocity_left : Tendsto (deriv x) atBot (𝓝 0) := by
    rw [hderiv_eq, ← ha]
    exact (hf.continuousOn a (left_mem_Icc.mpr hab.le)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hleft', Eventually.of_forall hclosed⟩)
  have hvelocity_right : Tendsto (deriv x) atTop (𝓝 0) := by
    rw [hderiv_eq, ← hb]
    exact (hf.continuousOn b (right_mem_Icc.mpr hab.le)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hright', Eventually.of_forall hclosed⟩)
  exact ⟨x, hzero, hC2, hdx, hx, hmono, hleft', hright',
    hvelocity_left, hvelocity_right⟩

/-- A negative field between two equilibria gives the reversed connection, with
the same freely prescribed interior value at time zero. -/
theorem exists_heteroclinic_of_neg {f : ℝ → ℝ} {a b x₀ : ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc a b))
    (ha : f a = 0) (hb : f b = 0)
    (hneg : ∀ z ∈ Ioo a b, f z < 0) (hx₀ : x₀ ∈ Ioo a b) :
    ∃ x : ℝ → ℝ,
      x 0 = x₀ ∧ ContDiff ℝ 2 x ∧
      (∀ t, HasDerivAt x (f (x t)) t) ∧
      (∀ t, x t ∈ Ioo a b) ∧ StrictAnti x ∧
      Tendsto x atBot (𝓝 b) ∧ Tendsto x atTop (𝓝 a) ∧
      Tendsto (deriv x) atBot (𝓝 0) ∧ Tendsto (deriv x) atTop (𝓝 0) := by
  obtain ⟨y, hy0, hyC2, hyd, hymem, hymono, hya, hyb, hyda, hydb⟩ :=
    exists_heteroclinic_of_pos hf.neg (by simpa using ha)
      (by simpa using hb) (fun z hz ↦ neg_pos.mpr (hneg z hz)) hx₀
  let x : ℝ → ℝ := fun t ↦ y (-t)
  have hxd (t : ℝ) : HasDerivAt x (f (x t)) t := by
    simpa [x, Function.comp_def] using (hyd (-t)).comp t (hasDerivAt_id t).neg
  have hxderiv : deriv x = fun t ↦ -(deriv y (-t)) := by
    funext t
    rw [(hxd t).deriv, (hyd (-t)).deriv]
    simp [x]
  refine ⟨x, by simpa [x] using hy0, hyC2.comp contDiff_id.neg, hxd,
    fun t ↦ hymem (-t), (fun _ _ h ↦ hymono (neg_lt_neg h)),
    hyb.comp tendsto_neg_atBot_atTop, hya.comp tendsto_neg_atTop_atBot, ?_, ?_⟩
  · rw [hxderiv]
    simpa using (hydb.comp tendsto_neg_atBot_atTop).neg
  · rw [hxderiv]
    simpa using (hyda.comp tendsto_neg_atTop_atBot).neg

end PDE.Analysis.Evolution.Scalar
