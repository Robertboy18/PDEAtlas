/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.IntegralPotential.PowerBounds

/-!
# Mountain-pass geometry of superquadratic integral potentials

An upper power bound gives a small sphere on which the energy is bounded below by a positive
constant. A positive lower power bound gives points of nonpositive energy outside every ball,
provided the inclusion is not identically zero. Both facts are derived from scalar bounds on
the potential. They are the hypotheses (ii) and (iii) of the mountain pass theorem, which
Evans checks in step 5 of the proof of §8.5.2, Theorem 3, from (25):
`exists_sphere_barrier` takes `a = r² / 4` as he does, and `exists_escape_point` scales a
vector `w` with `J w ≠ 0`, as he scales `u` to `v = tu`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.5.2, step 5 of the proof of Theorem 3 (Existence),
  (36), pp. 510-511. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace PDE.Analysis.Variational.IntegralPotential

variable {α H : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)] {G : ℝ → ℝ} {a A : ℝ}

/-- The superquadratic upper bound constructs a positive small sphere. -/
theorem exists_sphere_barrier
    (J : H →L[ℝ] Lp ℝ p μ) (hp_zero : p ≠ 0) (hp_top : p ≠ ∞)
    (hp2 : 2 < p.toReal) (hc : Continuous G) (hA : 0 ≤ A)
    (hG : ∀ z, |G z| ≤ A * |z| ^ p.toReal) :
    ∃ r b : ℝ, 0 < r ∧ 0 < b ∧ ∀ u, ‖u‖ = r → b ≤ energy J G u := by
  let D := A * ‖J‖ ^ p.toReal
  have hexp : 0 < p.toReal - 2 := sub_pos.mpr hp2
  have hlim : Tendsto (fun r : ℝ ↦ D * r ^ (p.toReal - 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hexp.ne', mul_zero] using
      ((Real.continuous_rpow_const hexp.le).const_mul D).continuousAt
        (x := 0) |>.tendsto.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, D * r ^ (p.toReal - 2) < 1 / 4 :=
    hlim.eventually (gt_mem_nhds (by norm_num))
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, hsmall⟩ := (hpos.and hsmall).exists
  have hrpos : 0 < r := hr
  refine ⟨r, r ^ 2 / 4, hrpos, by positivity, fun u hu ↦ ?_⟩
  have hsplit : r ^ p.toReal = r ^ (p.toReal - 2) * r ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_add hrpos]
    congr 1
    ring
  have hb := energy_lower_bound_opNorm J hp_zero hp_top hc hA hG u
  rw [hu, hsplit] at hb
  have hscaled := mul_le_mul_of_nonneg_right hsmall.le (sq_nonneg r)
  dsimp only [D] at hscaled
  nlinarith

/-- A positive lower power bound constructs an escape point beyond every
specified radius, provided the inclusion has a nonzero value. -/
theorem exists_escape_point
    (J : H →L[ℝ] Lp ℝ p μ) (hp_zero : p ≠ 0) (hp_top : p ≠ ∞)
    (hp2 : 2 < p.toReal) (hc : Continuous G) (ha : 0 < a)
    (hG : ∀ z, |G z| ≤ A * |z| ^ p.toReal)
    (hlower : ∀ z, a * |z| ^ p.toReal ≤ G z)
    {w : H} (hw : J w ≠ 0) (r : ℝ) :
    ∃ v : H, r < ‖v‖ ∧ energy J G v ≤ 0 := by
  have hw0 : w ≠ 0 := fun h ↦ hw (by simp [h])
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  let D := a * ‖J w‖ ^ p.toReal
  have hD : 0 < D := mul_pos ha (Real.rpow_pos_of_pos (norm_pos_iff.mpr hw) _)
  have hlarge : ∀ᶠ t : ℝ in atTop,
      ‖w‖ ^ 2 / (2 * D) ≤ t ^ (p.toReal - 2) :=
    (tendsto_rpow_atTop (sub_pos.mpr hp2)).eventually
      (eventually_ge_atTop _)
  obtain ⟨t, ht, hnorm, hpower⟩ :=
    ((eventually_gt_atTop 0).and ((eventually_gt_atTop (r / ‖w‖)).and hlarge)).exists
  refine ⟨t • w, ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg ht.le]
    exact (div_lt_iff₀ hnw).mp hnorm
  have hscaled : (1 / 2 : ℝ) * ‖w‖ ^ 2 ≤ D * t ^ (p.toReal - 2) := by
    have h := (div_le_iff₀ (mul_pos (by norm_num) hD)).mp hpower
    nlinarith
  have hbound := energy_upper_bound J hp_zero hp_top hc hG hlower (t • w)
  rw [map_smul, norm_smul, norm_smul, Real.norm_of_nonneg ht.le,
    mul_pow, Real.mul_rpow ht.le (norm_nonneg (J w))] at hbound
  have hsplit : t ^ p.toReal = t ^ (p.toReal - 2) * t ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_add ht]
    congr 1
    ring
  rw [hsplit] at hbound
  have hscaled2 := mul_le_mul_of_nonneg_right hscaled (sq_nonneg t)
  dsimp only [D] at hscaled2
  nlinarith

end PDE.Analysis.Variational.IntegralPotential
