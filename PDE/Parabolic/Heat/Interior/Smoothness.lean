/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Interior.Residual
public import PDE.Parabolic.Heat.Equation
import PDE.Analysis.Calculus.SpaceTime.Regularity
import PDE.Parabolic.Heat.ConvolutionSpace.JointSmoothness
import PDE.Parabolic.Heat.Duhamel.TimeTruncation

/-!
# Interior smoothness of classical heat solutions

A classical heat solution on `Ω × (0,T]` is `C∞` there, terminal time included. This is Evans's
§2.3.3(b), Theorem 8 (Smoothness), with the terminal time retained. The hypotheses are the
continuous derivative fields of a local `C^{2,1}` solution. No mixed derivative, second time
derivative, boundary regularity, growth bound, or prior representation is assumed.

## Main results

* `contDiffOn_of_heat_equation`: interior smoothness on `Ω × (0,T]`.
* `exists_smooth_extension_of_heat_equation`, `exists_smooth_extension_of_heat_equation_on_Icc`:
  near each point, a smooth function on an open set that agrees with the solution on the cylinder.

## How it works

Evans multiplies `u` by a cutoff `ζ(x, t)` in space and time, so that `v = ζu` vanishes at `t = 0`,
(33). Theorems 2 and 7 identify `v` with the Duhamel integral of its residual, (36), and an
integration by parts gives a kernel representation (37)-(38) whose kernel vanishes near the
evaluation point. He first assumes `u` smooth and removes the assumption by mollifying. We cut off
in space only, with a bump equal to one near the point.
`spatialCutoff_eq_initialValueSolution_add_integral` writes the cutoff field as the heat evolution
of its slice at an earlier positive time plus the Duhamel integral of its residual, and
`spatialCutoff_heatResidual_support` places the residual in the cutoff annulus, away from the point.
The evolution term is smooth because its heat age is positive, and the Duhamel term is smooth near
the point by `contDiffAt_heatPotential_of_spatial_gap`. The representation holds for `C^{2,1}`
fields, so no mollification is needed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.3(b), Theorem 8 (Smoothness) and its proof, (33)-(38),
  pp. 59-61.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

open Filter MeasureTheory Metric Set
open scoped Topology Interval ContDiff

namespace HeatEquation

variable {n : ℕ}

/-- A classical heat field on a closed time interval has a smooth
extension near every spatial interior point after its initial time. The open
extension domain includes points beyond the terminal time; agreement is only
required on the original cylinder. -/
theorem exists_smooth_extension_of_heat_equation_on_Icc
    {Ω : Set (ℝ^n)} {a b : ℝ} {u : ℝ^n → ℝ → ℝ}
    {Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ}
    {Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ}
    {Dt : ℝ^n × ℝ → ℝ}
    (hΩ : IsOpen Ω)
    (hu : ContinuousOn u.uncurry (Ω ×ˢ Icc a b))
    (hDx : ContinuousOn Dx (Ω ×ˢ Icc a b))
    (hDxx : ContinuousOn Dxx (Ω ×ˢ Icc a b))
    (hDt : ContinuousOn Dt (Ω ×ˢ Icc a b))
    (hspace : ∀ p ∈ Ω ×ˢ Icc a b,
      HasFDerivAt (fun x ↦ u x p.2) (Dx p) p.1)
    (hhessian : ∀ p ∈ Ω ×ˢ Icc a b,
      HasFDerivAt (fun x ↦ Dx (x, p.2)) (Dxx p) p.1)
    (htime : ∀ p ∈ Ω ×ˢ Icc a b,
      HasDerivWithinAt (u p.1) (Dt p) (Icc a b) p.2)
    (hheat : ∀ p ∈ Ω ×ˢ Icc a b,
      Dt p - laplacian (fun y ↦ u y p.2) p.1 = 0)
    {x : ℝ^n} {t : ℝ} (hx : x ∈ Ω) (hat : a < t) (htb : t ≤ b) :
    ∃ (v : ℝ^n × ℝ → ℝ) (W : Set (ℝ^n × ℝ)),
      IsOpen W ∧ (x, t) ∈ W ∧ ContDiffOn ℝ ∞ v W ∧
        EqOn u.uncurry v (W ∩ (Ω ×ˢ Icc a b)) := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hx)
  let χ : ContDiffBump x := ⟨r / 2, r, by positivity, by linarith⟩
  have hχΩ : tsupport χ ⊆ Ω := χ.tsupport_eq ▸ hball
  let K : Set (ℝ^n) := tsupport χ \ ball x (χ.rIn / 2)
  have hK : IsCompact K := χ.hasCompactSupport.diff isOpen_ball
  let R : ℝ^n × ℝ → ℝ := fun p ↦
    χ p.1 * Dt p - laplacian (fun y ↦ χ y * u y p.2) p.1
  have hR : ContinuousOn R (univ ×ˢ Icc a b) :=
    continuousOn_spatialCutoff_heatResidual hΩ hu hDx hDxx hDt hspace hhessian
      χ.contDiff hχΩ
  have hRsupport : ∀ s ∈ Icc a b, ∀ y ∉ K, R (y, s) = 0 :=
    fun _ hs _ hy ↦ spatialCutoff_heatResidual_support χ hχΩ hheat hs hy
  let g : ℝ^n → ℝ := fun y ↦ χ y * u y a
  have hg : ContDiff ℝ 2 g := by
    simpa only [smul_eq_mul, g] using
      PDE.Analysis.contDiff_spatial_cutoff_smul (m := 2) hΩ χ.contDiff hχΩ
        (PDE.Analysis.contDiffOn_two_slice_of_space_derivatives hΩ hDxx hspace hhessian
          (left_mem_Icc.mpr (hat.le.trans htb)))
  have hgb : ∃ M, ∀ y, |g y| ≤ M := by
    simpa only [Real.norm_eq_abs] using hg.continuous.bounded_above_of_compact_support
      (χ.hasCompactSupport.mul_right (f' := fun y ↦ u y a))
  let V : ℝ^n × ℝ → ℝ := fun p ↦ initialValueSolution g p.1 (p.2 - a) +
    ∫ q in K ×ˢ Icc a b, R q * fundamentalSolutionHeat (p.1 - q.1) (p.2 - q.2)
  have hV : ContDiffOn ℝ ∞ V (ball x (χ.rIn / 2) ×ˢ Ioi a) := by
    intro p hp
    have hinit : ContDiffAt ℝ ∞
        (fun q : ℝ^n × ℝ ↦ initialValueSolution g q.1 (q.2 - a)) p :=
      (contDiffAt_initialValueSolution_timeSpace g p.1 (p.2 - a) (sub_pos.mpr hp.2)
        hg.continuous hgb).comp p
        ((contDiffAt_snd.sub contDiffAt_const).prodMk contDiffAt_fst)
    have hpotential : ContDiffAt ℝ ∞
        (fun p : ℝ^n × ℝ ↦ ∫ q in K ×ˢ Icc a b,
          R q * fundamentalSolutionHeat (p.1 - q.1) (p.2 - q.2)) p := by
      apply contDiffAt_heatPotential_of_spatial_gap hK
        (hR.mono (prod_mono_left (subset_univ K))) p.2
        (sub_pos.mpr (show dist p.1 x < χ.rIn / 2 from hp.1))
      intro y hy
      have hyx : χ.rIn / 2 ≤ dist x y := by
        simpa only [mem_ball, not_lt, dist_comm] using hy.2
      linarith [dist_triangle p.1 x y, dist_triangle x p.1 y, dist_comm x p.1]
    exact (hinit.add hpotential).contDiffWithinAt
  refine ⟨V, ball x (χ.rIn / 2) ×ˢ Ioi a, isOpen_ball.prod isOpen_Ioi,
    ⟨mem_ball_self (half_pos χ.rIn_pos), hat⟩, hV, ?_⟩
  rintro p ⟨hp, hpQ⟩
  have hpK : p.1 ∉ K := fun h ↦ h.2 hp.1
  have hχone : χ p.1 = 1 :=
    χ.one_of_mem_closedBall
      (ball_subset_closedBall (ball_subset_ball (half_le_self χ.rIn_pos.le) hp.1))
  have hsub : Ω ×ˢ Icc a p.2 ⊆ Ω ×ˢ Icc a b :=
    prod_mono_right (Icc_subset_Icc le_rfl hpQ.2.2)
  have hlocal := spatialCutoff_eq_initialValueSolution_add_integral
    hp.2.le hΩ (hu.mono hsub) (hDx.mono hsub) (hDxx.mono hsub) (hDt.mono hsub)
    (fun q hq ↦ hspace q (hsub hq)) (fun q hq ↦ hhessian q (hsub hq))
    (fun q hq ↦ (htime q (hsub hq)).mono (Icc_subset_Icc le_rfl hpQ.2.2))
    χ.contDiff χ.hasCompactSupport hχΩ p.1
  have hpot := heatPotential_eq_duhamel_of_notMem hp.2.le hpQ.2.2 hK hR hRsupport hpK
  change u p.1 p.2 = V p
  change χ p.1 * u p.1 p.2 =
    initialValueSolution g p.1 (p.2 - a) +
      ∫ s in a..p.2, initialValueSolution (fun y ↦ R (y, s)) p.1 (p.2 - s) at hlocal
  simpa only [V, hχone, one_mul, hpot] using hlocal

/-- A classical heat solution on `Ω × (0,T]` has a constructed smooth
extension on an open neighborhood of each point, including the terminal time.
Only the extension, not the given function, is evaluated smoothly beyond `T`. -/
theorem exists_smooth_extension_of_heat_equation
    {Ω : Set (ℝ^n)} {T : ℝ} {u : ℝ^n → ℝ → ℝ}
    {Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ}
    {Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ}
    {Dt : ℝ^n × ℝ → ℝ}
    (hΩ : IsOpen Ω)
    (hu : ContinuousOn u.uncurry (Ω ×ˢ Ioc 0 T))
    (hDx : ContinuousOn Dx (Ω ×ˢ Ioc 0 T))
    (hDxx : ContinuousOn Dxx (Ω ×ˢ Ioc 0 T))
    (hDt : ContinuousOn Dt (Ω ×ˢ Ioc 0 T))
    (hspace : ∀ p ∈ Ω ×ˢ Ioc 0 T,
      HasFDerivAt (fun x ↦ u x p.2) (Dx p) p.1)
    (hhessian : ∀ p ∈ Ω ×ˢ Ioc 0 T,
      HasFDerivAt (fun x ↦ Dx (x, p.2)) (Dxx p) p.1)
    (htime : ∀ p ∈ Ω ×ˢ Ioc 0 T,
      HasDerivWithinAt (u p.1) (Dt p) (Ioc 0 T) p.2)
    (hheat : ∀ p ∈ Ω ×ˢ Ioc 0 T,
      Dt p - laplacian (fun y ↦ u y p.2) p.1 = 0)
    {p : ℝ^n × ℝ} (hp : p ∈ Ω ×ˢ Ioc 0 T) :
    ∃ (v : ℝ^n × ℝ → ℝ) (W : Set (ℝ^n × ℝ)),
      IsOpen W ∧ p ∈ W ∧ ContDiffOn ℝ ∞ v W ∧
        EqOn u.uncurry v (W ∩ (Ω ×ˢ Ioc 0 T)) := by
  have htimeSubset : Icc (p.2 / 2) T ⊆ Ioc 0 T :=
    fun _ hs ↦ ⟨(half_pos hp.2.1).trans_le hs.1, hs.2⟩
  have hsub : Ω ×ˢ Icc (p.2 / 2) T ⊆ Ω ×ˢ Ioc 0 T :=
    prod_mono_right htimeSubset
  obtain ⟨v, W, hW, hpW, hv, heq⟩ := exists_smooth_extension_of_heat_equation_on_Icc
    hΩ (hu.mono hsub) (hDx.mono hsub) (hDxx.mono hsub) (hDt.mono hsub)
    (fun q hq ↦ hspace q (hsub hq)) (fun q hq ↦ hhessian q (hsub hq))
    (fun q hq ↦ (htime q (hsub hq)).mono htimeSubset)
    (fun q hq ↦ hheat q (hsub hq)) hp.1 (half_lt_self hp.2.1) hp.2.2
  refine ⟨v, W ∩ {q | p.2 / 2 < q.2},
    hW.inter (isOpen_lt continuous_const continuous_snd),
    ⟨hpW, half_lt_self hp.2.1⟩, hv.mono inter_subset_left, ?_⟩
  rintro q ⟨⟨hqW, hq⟩, hqQ⟩
  exact heq ⟨hqW, hqQ.1, hq.le, hqQ.2.2⟩

/-- Interior smoothness of a classical heat solution on `Ω × (0,T]`.
The spatial domain is any open set. Continuous first and second spatial
derivatives and the time derivative within `(0,T]` suffice. The conclusion
retains the terminal time and imposes no regularity on the function beyond it. -/
theorem contDiffOn_of_heat_equation
    {Ω : Set (ℝ^n)} {T : ℝ} {u : ℝ^n → ℝ → ℝ}
    {Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ}
    {Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ}
    {Dt : ℝ^n × ℝ → ℝ}
    (hΩ : IsOpen Ω)
    (hu : ContinuousOn u.uncurry (Ω ×ˢ Ioc 0 T))
    (hDx : ContinuousOn Dx (Ω ×ˢ Ioc 0 T))
    (hDxx : ContinuousOn Dxx (Ω ×ˢ Ioc 0 T))
    (hDt : ContinuousOn Dt (Ω ×ˢ Ioc 0 T))
    (hspace : ∀ p ∈ Ω ×ˢ Ioc 0 T,
      HasFDerivAt (fun x ↦ u x p.2) (Dx p) p.1)
    (hhessian : ∀ p ∈ Ω ×ˢ Ioc 0 T,
      HasFDerivAt (fun x ↦ Dx (x, p.2)) (Dxx p) p.1)
    (htime : ∀ p ∈ Ω ×ˢ Ioc 0 T,
      HasDerivWithinAt (u p.1) (Dt p) (Ioc 0 T) p.2)
    (hheat : ∀ p ∈ Ω ×ˢ Ioc 0 T,
      Dt p - laplacian (fun y ↦ u y p.2) p.1 = 0) :
    ContDiffOn ℝ ∞ u.uncurry (Ω ×ˢ Ioc 0 T) := by
  intro p hp
  obtain ⟨v, W, hW, hpW, hv, heq⟩ := exists_smooth_extension_of_heat_equation
    hΩ hu hDx hDxx hDt hspace hhessian htime hheat hp
  apply ((hv.contDiffAt (hW.mem_nhds hpW)).contDiffWithinAt
    (s := Ω ×ˢ Ioc 0 T)).congr_of_eventuallyEq_of_mem (f₁ := u.uncurry) ?_ hp
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hpW),
    self_mem_nhdsWithin] with q hqW hqQ
  exact heq ⟨hqW, hqQ⟩

/-- At an interior time, a time derivative within `(0,T]` is an ordinary
derivative, so the heat equation stated with it gives
`heatParabolicOperator u x t = 0`. -/
theorem heatParabolicOperator_eq_zero_of_within_time_derivative
    {u : ℝ^n → ℝ → ℝ} {x : ℝ^n} {t T d : ℝ}
    (ht : t ∈ Ioo 0 T)
    (hd : HasDerivWithinAt (u x) d (Ioc 0 T) t)
    (hheat : d - laplacian (fun y ↦ u y t) x = 0) :
    heatParabolicOperator u x t = 0 := by
  rw [heatParabolicOperator, (hd.hasDerivAt (Ioc_mem_nhds ht.1 ht.2)).deriv]
  exact hheat

end HeatEquation
