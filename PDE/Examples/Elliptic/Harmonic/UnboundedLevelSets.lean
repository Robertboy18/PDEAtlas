/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Module.Connected
public import PDE.Elliptic.Classical.Harmonic.Definitions
public import PDE.Analysis.Convex.Star.Topology
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Harmonic level sets on an unbounded exterior domain

Outside the unit disk, a harmonic combination of two multipoles equals one on
its boundary but has an intermediate level that cannot be the frontier of any
set star-convex about the origin. Two points of the level lie on the same ray,
with a point outside the level between them.

The example has the hypotheses of the star-shaped level-set theorem, Evans, §9.5.1, Theorem 1,
except boundedness of the outer domain. The theorem does not list that bound, but its proof applies
the strong maximum principle of §2.2.3, which assumes a bounded open set. The outer set is the whole
plane, so its zero boundary condition is vacuous. A level set counts as star-shaped when it is the
frontier of a set star-convex about the origin.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.3, p. 26, and §9.5.1, (1) and Theorem 1
  (Star-shaped level sets), pp. 554-555.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Set Metric LaplacianEquation
open scoped ContDiff

namespace PDE.Examples.HarmonicUnboundedLevelSets

/-- The exterior of the closed unit disk. -/
def exterior : Set (ℝ^2) := (closedBall 0 1)ᶜ

/-- The exterior is an open subset of the plane. -/
theorem isOpen_exterior : IsOpen exterior := isClosed_closedBall.isOpen_compl

/-- The closure is exactly the set of points with radius at least one. -/
theorem closure_exterior : closure exterior = {p | 1 ≤ ‖p‖} := by
  rw [exterior, closure_compl, interior_closedBall 0 one_ne_zero]
  ext p
  simp

/-- The frontier of the exterior is the unit circle. -/
theorem frontier_exterior : frontier exterior = sphere 0 1 := by
  rw [exterior, frontier_compl, frontier_closedBall 0 one_ne_zero]

/-- The exterior is connected: it is the image of the product of the unit circle with
the radii greater than one under `(v, r) ↦ r • v`. -/
theorem isConnected_exterior : IsConnected exterior := by
  have hrank : 1 < Module.rank ℝ (ℝ^2) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  have himage : (fun z : (ℝ^2) × ℝ ↦ z.2 • z.1) ''
      (sphere 0 1 ×ˢ Ioi 1) = exterior := by
    ext p
    constructor
    · rintro ⟨⟨v, r⟩, ⟨hv, hr⟩, rfl⟩
      have hvnorm : ‖v‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hv
      simpa [exterior, norm_smul, abs_of_pos (zero_lt_one.trans hr), hvnorm] using hr
    · intro hp
      have hn : 1 < ‖p‖ := by simpa [exterior] using hp
      have hn0 : ‖p‖ ≠ 0 := (zero_lt_one.trans hn).ne'
      refine ⟨(‖p‖⁻¹ • p, ‖p‖), ⟨?_, hn⟩, ?_⟩
      · simp [norm_smul, hn0]
      · simp [smul_smul, hn0]
  rw [← himage]
  exact ((isConnected_sphere hrank 0 (by norm_num : (0 : ℝ) ≤ 1)).prod
    isConnected_Ioi).image _ (continuous_snd.smul continuous_fst).continuousOn

/-- Removing the closed unit disk leaves an unbounded domain. -/
theorem not_isBounded_exterior : ¬ Bornology.IsBounded exterior := by
  intro h
  apply NormedSpace.unbounded_univ ℝ (ℝ^2)
  have hunion := (isBounded_closedBall (x := (0 : ℝ^2)) (r := 1)).union h
  simpa only [exterior, union_compl_self] using hunion

/-- Squared radius in Cartesian coordinates. -/
noncomputable def radiusSquared (p : ℝ^2) : ℝ := (p 0) ^ 2 + (p 1) ^ 2

/-- The harmonic function `1 - x (1 - r⁻²) + (x² - y²) (1 - r⁻⁴) / 10`, with `r² = x² + y²`:
a harmonic polynomial plus a dipole and a quadrupole, equal to one on the unit circle. -/
noncomputable def profile (p : ℝ^2) : ℝ :=
  1 - p 0 * (1 - 1 / radiusSquared p) +
    ((p 0) ^ 2 - (p 1) ^ 2) / 10 * (1 - 1 / (radiusSquared p) ^ 2)

private theorem radiusSquared_eq_norm_sq (p : ℝ^2) :
    radiusSquared p = ‖p‖ ^ 2 := by
  simpa [radiusSquared, Fin.sum_univ_two] using
    (EuclideanSpace.real_norm_sq_eq p).symm

private theorem radiusSquared_pos_on_closure {p : ℝ^2} (hp : p ∈ closure exterior) :
    0 < radiusSquared p := by
  have hnorm : 1 ≤ ‖p‖ := by simpa only [closure_exterior, mem_ofPred_eq] using hp
  rw [radiusSquared_eq_norm_sq]
  nlinarith

private theorem contDiffAt_profile {p : ℝ^2} (hp : radiusSquared p ≠ 0) :
    ContDiffAt ℝ ⊤ profile p := by
  have hx : ContDiff ℝ ⊤ (fun p : ℝ^2 ↦ p 0) := by fun_prop
  have hy : ContDiff ℝ ⊤ (fun p : ℝ^2 ↦ p 1) := by fun_prop
  have hq : ContDiffAt ℝ ⊤ radiusSquared p := by
    unfold radiusSquared
    fun_prop
  exact (contDiffAt_const.sub (hx.contDiffAt.mul
    (contDiffAt_const.sub (contDiffAt_const.div hq hp)))).add
      (((hx.contDiffAt.pow 2).sub (hy.contDiffAt.pow 2)).div_const 10 |>.mul
        (contDiffAt_const.sub (contDiffAt_const.div (hq.pow 2) (pow_ne_zero 2 hp))))

private theorem isHarmonicPDE_polynomial :
    IsHarmonicPDE 2 (fun p : ℝ^2 ↦ 1 - p 0 + ((p 0) ^ 2 - (p 1) ^ 2) / 10)
      exterior := by
  refine ⟨by fun_prop, fun p _ ↦ ?_⟩
  cas

private theorem isHarmonicPDE_dipole :
    IsHarmonicPDE 2 (fun p : ℝ^2 ↦ p 0 / radiusSquared p) exterior := by
  refine ⟨?_, ?_⟩
  · intro p hp
    have hq := (radiusSquared_pos_on_closure (subset_closure hp)).ne'
    exact (by fun_prop : ContDiffAt ℝ 2 (fun p : ℝ^2 ↦ p 0) p).div
      (by unfold radiusSquared; fun_prop) hq |>.contDiffWithinAt
  · intro p hp
    have hq : (p 0) ^ 2 + (p 1) ^ 2 ≠ 0 :=
      (radiusSquared_pos_on_closure (subset_closure hp)).ne'
    unfold radiusSquared
    cas

private theorem isHarmonicPDE_quadrupole :
    IsHarmonicPDE 2 (fun p : ℝ^2 ↦ ((p 0) ^ 2 - (p 1) ^ 2) / (radiusSquared p) ^ 2)
      exterior := by
  refine ⟨?_, ?_⟩
  · intro p hp
    have hq := (radiusSquared_pos_on_closure (subset_closure hp)).ne'
    exact (by fun_prop : ContDiffAt ℝ 2 (fun p : ℝ^2 ↦ (p 0) ^ 2 - (p 1) ^ 2) p).div
      (by unfold radiusSquared; fun_prop) (pow_ne_zero 2 hq) |>.contDiffWithinAt
  · intro p hp
    have hq : (p 0) ^ 2 + (p 1) ^ 2 ≠ 0 :=
      (radiusSquared_pos_on_closure (subset_closure hp)).ne'
    unfold radiusSquared
    cas

/-- The profile is harmonic on the exterior domain. -/
theorem isHarmonicPDE_profile : IsHarmonicPDE 2 profile exterior := by
  have h := (isHarmonicPDE_polynomial.add isHarmonicPDE_dipole isOpen_exterior).sub
    (isHarmonicPDE_quadrupole.const_mul (1 / 10)) isOpen_exterior
  convert h using 1
  ext p
  simp only [profile, Pi.sub_apply]
  cas

/-- The profile is smooth in the ambient plane at every point of the exterior closure. -/
theorem contDiffAt_profile_closure {p : ℝ^2} (hp : p ∈ closure exterior) :
    ContDiffAt ℝ ⊤ profile p :=
  contDiffAt_profile (radiusSquared_pos_on_closure hp).ne'

/-- The profile is smooth up to the inner boundary. -/
theorem contDiffOn_profile_closure : ContDiffOn ℝ ⊤ profile (closure exterior) :=
  fun _ hp ↦ (contDiffAt_profile_closure hp).contDiffWithinAt

/-- The profile extends continuously to the inner boundary. -/
theorem continuousOn_profile_closure : ContinuousOn profile (closure exterior) :=
  contDiffOn_profile_closure.continuousOn

/-- The boundary value on the unit circle is one. -/
theorem profile_inner (p : ℝ^2) (hp : p ∈ frontier (ball 0 1)) : profile p = 1 := by
  rw [frontier_ball 0 one_ne_zero] at hp
  have hnorm : ‖p‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hp
  simp [profile, radiusSquared_eq_norm_sq, hnorm]

/-- The restriction to the first-coordinate axis is an explicit rational function. -/
theorem profile_axis (s : ℝ) :
    profile (EuclideanSpace.single 0 s) =
      1 - s * (1 - 1 / s ^ 2) + s ^ 2 / 10 * (1 - 1 / (s ^ 2) ^ 2) := by
  simp [profile, radiusSquared]

/-- At the point `(1, 0)` the profile equals one. -/
theorem profile_axis_one : profile (EuclideanSpace.single 0 (1 : ℝ)) = 1 := by
  norm_num [profile_axis]

/-- At the point `(2, 0)` the profile equals `-1/8`. -/
theorem profile_axis_two : profile (EuclideanSpace.single 0 (2 : ℝ)) = -(1 / 8) := by
  norm_num [profile_axis]

/-- At the point `(9, 0)` the profile equals `17/81`. -/
theorem profile_axis_nine : profile (EuclideanSpace.single 0 (9 : ℝ)) = 17 / 81 := by
  norm_num [profile_axis]

private theorem axis_mem_exterior {s : ℝ} (hs : 1 < s) :
    EuclideanSpace.single 0 s ∈ exterior := by
  simpa [exterior, abs_of_pos (zero_lt_one.trans hs)] using hs

/-- The profile does not map the exterior domain into `(0, 1)`. -/
theorem not_mapsTo_profile_unit_interval : ¬ MapsTo profile exterior (Ioo 0 1) := by
  intro h
  have htwo := h (axis_mem_exterior (by norm_num : (1 : ℝ) < 2))
  norm_num [profile_axis_two] at htwo

/-- The level set `{profile = 17/81}` in the exterior domain is nonempty. -/
theorem level_nonempty : {p | p ∈ exterior ∧ profile p = 17 / 81}.Nonempty :=
  ⟨EuclideanSpace.single 0 (9 : ℝ), axis_mem_exterior (by norm_num), profile_axis_nine⟩

private theorem smul_single_one (s : ℝ) :
    s • (EuclideanSpace.single 0 (1 : ℝ) : ℝ^2) = EuclideanSpace.single 0 s := by
  ext i
  fin_cases i <;> simp [PiLp.smul_apply]

/-- The level `17/81` meets the positive first-coordinate ray at two distinct radii,
with the point at radius two strictly below that level. -/
theorem exists_repeated_ray_level :
    ∃ a ∈ Ioo (1 : ℝ) 2,
      profile (EuclideanSpace.single 0 a) = 17 / 81 ∧
      profile (EuclideanSpace.single 0 (9 : ℝ)) = 17 / 81 ∧
      profile (EuclideanSpace.single 0 (2 : ℝ)) ≠ 17 / 81 := by
  have hcont : ContinuousOn (fun s : ℝ ↦ profile (EuclideanSpace.single 0 s)) (Icc 1 2) := by
    intro s hs
    have hq : radiusSquared (EuclideanSpace.single 0 s) ≠ 0 := by
      simpa [radiusSquared] using (ne_of_gt (zero_lt_one.trans_le hs.1))
    have haxis : Continuous (fun s : ℝ ↦ (EuclideanSpace.single 0 s : ℝ^2)) := by
      convert (continuous_id.smul continuous_const :
        Continuous (fun s : ℝ ↦ s • (EuclideanSpace.single 0 (1 : ℝ) : ℝ^2))) using 1
      funext s
      exact (smul_single_one s).symm
    exact ((contDiffAt_profile hq).continuousAt.comp haxis.continuousAt).continuousWithinAt
  obtain ⟨a, ha, heq⟩ := intermediate_value_Icc' (by norm_num : (1 : ℝ) ≤ 2) hcont
    (show (17 / 81 : ℝ) ∈ Icc (profile (EuclideanSpace.single 0 (2 : ℝ)))
      (profile (EuclideanSpace.single 0 (1 : ℝ))) by norm_num [profile_axis_one, profile_axis_two])
  have ha1 : a ≠ 1 := by
    intro h
    subst a
    norm_num [profile_axis_one, profile_axis_two] at heq
  have ha2 : a ≠ 2 := by
    intro h
    subst a
    norm_num [profile_axis_one, profile_axis_two] at heq
  exact ⟨a, ⟨lt_of_le_of_ne ha.1 ha1.symm, lt_of_le_of_ne ha.2 ha2⟩, heq,
    profile_axis_nine, by norm_num [profile_axis_two]⟩

/-- The level set `{profile = 17/81}` in the exterior domain is not the frontier of any
set star-convex about the origin: it contains `(a, 0)` for some `a ∈ (1, 2)` and `(9, 0)`,
but not `(2, 0)`. -/
theorem level_not_frontier_starConvex :
    ¬ ∃ s : Set (ℝ^2), StarConvex ℝ 0 s ∧
      frontier s = {p | p ∈ exterior ∧ profile p = 17 / 81} := by
  obtain ⟨a, ha, hae, hne, htwo⟩ := exists_repeated_ray_level
  rintro ⟨s, hs, hfront⟩
  have hlow : EuclideanSpace.single 0 a ∈ frontier s := by
    rw [hfront]
    exact ⟨axis_mem_exterior ha.1, hae⟩
  have hhigh : EuclideanSpace.single 0 (9 : ℝ) ∈ frontier s := by
    rw [hfront]
    exact ⟨axis_mem_exterior (by norm_num), hne⟩
  have hm := hs.smul_mem_frontier_of_between
    (v := EuclideanSpace.single 0 (1 : ℝ)) (zero_lt_one.trans ha.1) ha.2.le
    (by norm_num : (2 : ℝ) ≤ 9) (by simpa only [smul_single_one] using hlow)
    (by simpa only [smul_single_one] using hhigh)
  rw [hfront] at hm
  apply htwo
  simpa only [smul_single_one] using hm.2

/-- For an unbounded outer domain a level set need not be star-shaped. With `V` the
unit disk and `W = ℝ²`, the profile is harmonic on the connected set `W \ closure V`,
equals one on `frontier V`, does not take values in `(0, 1)`, and its level `17/81` is
not the frontier of a set star-convex about the origin. The zero condition on
`frontier W = ∅` holds vacuously. -/
theorem unbounded_outer_domain_counterexample :
    ∃ (V W : Set (ℝ^2)) (u : ℝ^2 → ℝ) (c : ℝ),
      IsOpen V ∧ IsOpen W ∧ (0 : ℝ^2) ∈ V ∧
      IsConnected V ∧ IsConnected W ∧
      StarConvex ℝ 0 V ∧ StarConvex ℝ 0 (closure V) ∧ StarConvex ℝ 0 W ∧
      IsCompact (closure V) ∧ closure V ⊆ W ∧
      ¬ Bornology.IsBounded W ∧ frontier W = ∅ ∧
      IsOpen (W \ closure V) ∧ IsConnected (W \ closure V) ∧
      ¬ Bornology.IsBounded (W \ closure V) ∧
      IsHarmonicPDE 2 u (W \ closure V) ∧
      (∀ p ∈ closure (W \ closure V), ContDiffAt ℝ ⊤ u p) ∧
      ContDiffOn ℝ ⊤ u (closure (W \ closure V)) ∧
      ContinuousOn u (closure (W \ closure V)) ∧
      (∀ p ∈ frontier V, u p = 1) ∧ (∀ p ∈ frontier W, u p = 0) ∧
      ¬ MapsTo u (W \ closure V) (Ioo 0 1) ∧
      0 < c ∧ c < 1 ∧ {p | p ∈ W \ closure V ∧ u p = c}.Nonempty ∧
      ¬ ∃ s : Set (ℝ^2), StarConvex ℝ 0 s ∧
        frontier s = {p | p ∈ W \ closure V ∧ u p = c} := by
  have hdomain : (univ : Set (ℝ^2)) \ closure (ball 0 1) = exterior := by
    rw [closure_ball 0 one_ne_zero]
    ext p
    simp [exterior]
  have hstar : StarConvex ℝ 0 (ball (0 : ℝ^2) 1) :=
    (convex_ball 0 1).starConvex (mem_ball_self zero_lt_one)
  refine ⟨ball 0 1, univ, profile, 17 / 81, isOpen_ball, isOpen_univ,
    mem_ball_self zero_lt_one, isConnected_ball zero_lt_one, isConnected_univ,
    hstar, hstar.closure, starConvex_univ 0, ?_, subset_univ _,
    NormedSpace.unbounded_univ ℝ (ℝ^2), frontier_univ, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    profile_inner, ?_, ?_, by norm_num, by norm_num, ?_, ?_⟩
  · rw [closure_ball 0 one_ne_zero]
    exact isCompact_closedBall 0 1
  · simpa only [hdomain] using isOpen_exterior
  · simpa only [hdomain] using isConnected_exterior
  · simpa only [hdomain] using not_isBounded_exterior
  · simpa only [hdomain] using isHarmonicPDE_profile
  · simpa only [hdomain] using (fun p hp ↦ contDiffAt_profile_closure (p := p) hp)
  · simpa only [hdomain] using contDiffOn_profile_closure
  · simpa only [hdomain] using continuousOn_profile_closure
  · simp
  · simpa only [hdomain] using not_mapsTo_profile_unit_interval
  · simpa only [hdomain] using level_nonempty
  · simpa only [hdomain] using level_not_frontier_starConvex

end PDE.Examples.HarmonicUnboundedLevelSets
