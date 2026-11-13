/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Interior.Estimates.Mixed
public import PDE.Parabolic.Heat.Interior.Smoothness
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Local L1 estimates for classical heat solutions

On every compactly contained backward cylinder, the mixed derivatives are bounded with the parabolic
power of the radius. Derivatives are taken within the original domain `Ω × (0,T]`, so the assertion
includes `t=T`. The constant does not depend on the domain, solution, cylinder or jets. This is
Evans's §2.3.3(c), Theorem 9 (Estimates on derivatives), in the multilinear operator norm.

## Main results

* `exists_local_derivative_bound`: the bound by `C / r ^ (k + 2l + n + 2)` times the `L¹` norm on
  the cylinder of radius `r`, with `C` depending only on `n`, `k` and `l`.

## How it works

Evans proves Theorem 9 in two steps. On the unit cylinder the kernel representation `u = ∫∫ K u`
from his proof of Theorem 8 gives (39), and the rescaling `v(x, t) = u(rx, r²t)` gives the general
radius. We follow the same plan. `Estimates.Cutoffs` fixes a space-time cutoff of the unit cylinder
and one smooth compactly supported kernel that agrees with the Gaussian wherever the cutoff residual
lives. `Estimates.Representation` and `Estimates.KernelPairing` represent the field near the half
cylinder by this kernel with no derivatives on the field, as in Evans's (37)-(38).
`Estimates.UnitCylinder` bounds every derivative of the representation with constants chosen before
the field, and `exists_norm_spaceTimeMixedFDerivWithin_on_Icc_le` pulls the bound back along
`(y, s) ↦ (x + ry, t + r²s)`, which produces the denominator `r ^ (k + 2l + n + 2)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.3(c), Theorem 9 (Estimates on derivatives) and its
  proof, (39), pp. 61-62, with the representation (37)-(38) from the proof of Theorem 8, p. 61.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian spaceTimeMixedFDerivWithin)

open MeasureTheory Metric Set
open scoped ContDiff

namespace HeatEquation

/-- Every mixed derivative of a C²,¹ heat solution obeys the local
spacetime L1 estimate on the closed half cylinder, where its norm attains
a maximum. Integrability follows from continuity and compact containment.
The constant depends only on the dimension and derivative orders; zero dimension
and orders are allowed. -/
theorem exists_local_derivative_bound (n k l : ℕ) :
    ∃ C > 0, ∀ (Ω : Set (ℝ^n)) (T : ℝ) (u : ℝ^n → ℝ → ℝ)
      (Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ)
      (Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ)
      (Dt : ℝ^n × ℝ → ℝ),
      IsOpen Ω →
      ContinuousOn u.uncurry (Ω ×ˢ Ioc 0 T) →
      ContinuousOn Dx (Ω ×ˢ Ioc 0 T) →
      ContinuousOn Dxx (Ω ×ˢ Ioc 0 T) →
      ContinuousOn Dt (Ω ×ˢ Ioc 0 T) →
      (∀ p ∈ Ω ×ˢ Ioc 0 T,
        HasFDerivAt (fun y ↦ u y p.2) (Dx p) p.1) →
      (∀ p ∈ Ω ×ˢ Ioc 0 T,
        HasFDerivAt (fun y ↦ Dx (y, p.2)) (Dxx p) p.1) →
      (∀ p ∈ Ω ×ˢ Ioc 0 T,
        HasDerivWithinAt (u p.1) (Dt p) (Ioc 0 T) p.2) →
      (∀ p ∈ Ω ×ˢ Ioc 0 T,
        Dt p - laplacian (fun y ↦ u y p.2) p.1 = 0) →
      ∀ (x : ℝ^n) (t r : ℝ), 0 < r →
        closedBall x r ×ˢ Icc (t - r ^ 2) t ⊆ Ω ×ˢ Ioc 0 T →
        IntegrableOn u.uncurry (closedBall x r ×ˢ Icc (t - r ^ 2) t) ∧
          (∃ p ∈ closedBall x (r / 2) ×ˢ Icc (t - (r / 2) ^ 2) t,
            IsMaxOn (fun q ↦
              ‖spaceTimeMixedFDerivWithin k l u.uncurry (Ω ×ˢ Ioc 0 T) q‖)
              (closedBall x (r / 2) ×ˢ Icc (t - (r / 2) ^ 2) t) p) ∧
          ∀ p ∈ closedBall x (r / 2) ×ˢ Icc (t - (r / 2) ^ 2) t,
            ‖spaceTimeMixedFDerivWithin k l u.uncurry (Ω ×ˢ Ioc 0 T) p‖ ≤
              C / r ^ (k + 2 * l + n + 2) *
                ∫ q in closedBall x r ×ˢ Icc (t - r ^ 2) t, ‖u q.1 q.2‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_spaceTimeMixedFDerivWithin_on_Icc_le n k l
  refine ⟨C, hC, fun Ω T u Dx Dxx Dt hΩ hu hDx hDxx hDt
    hspace hhessian htime hheat x t r hr hcontain ↦ ?_⟩
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hbottom := hcontain
    (show (x, t - r ^ 2) ∈ closedBall x r ×ˢ Icc (t - r ^ 2) t from
      ⟨mem_closedBall_self hr.le, le_rfl, sub_le_self _ hr2.le⟩)
  have htop := hcontain
    (show (x, t) ∈ closedBall x r ×ˢ Icc (t - r ^ 2) t from
      ⟨mem_closedBall_self hr.le, sub_le_self _ hr2.le, le_rfl⟩)
  have hball : closedBall x r ⊆ Ω := fun y hy ↦
    (hcontain (show (y, t) ∈ closedBall x r ×ˢ Icc (t - r ^ 2) t from
      ⟨hy, sub_le_self _ hr2.le, le_rfl⟩)).1
  have hI : Icc (t - r ^ 2) t ⊆ Ioc 0 T :=
    fun _ hs ↦ ⟨hbottom.2.1.trans_le hs.1, hs.2.trans htop.2.2⟩
  have hsub : Ω ×ˢ Icc (t - r ^ 2) t ⊆ Ω ×ˢ Ioc 0 T := prod_mono_right hI
  have hsmooth :=
    contDiffOn_of_heat_equation hΩ hu hDx hDxx hDt hspace hhessian htime hheat
  have hhalf : (r / 2) ^ 2 = r ^ 2 / 4 := by cas
  have hhalfsub :
      closedBall x (r / 2) ×ˢ Icc (t - (r / 2) ^ 2) t ⊆
        Ω ×ˢ Icc (t - r ^ 2) t := by
    intro p hp
    refine ⟨hball ((closedBall_subset_closedBall (half_le_self hr.le)) hp.1), ?_, hp.2.2⟩
    have ht := hp.2.1
    rw [hhalf] at ht
    linarith [hr2.le]
  have hQ : UniqueDiffOn ℝ (Ω ×ˢ Ioc 0 T) :=
    hΩ.uniqueDiffOn.prod (uniqueDiffOn_Ioc 0 T)
  have hcont := (hsmooth.continuousOn_spaceTimeMixedFDerivWithin k l (by simp)
    hQ).norm.mono (hhalfsub.trans hsub)
  have hmax := ((isCompact_closedBall x (r / 2)).prod
    (isCompact_Icc (a := t - (r / 2) ^ 2) (b := t))).exists_isMaxOn
      ⟨(x, t), mem_closedBall_self (by positivity),
        sub_le_self _ (sq_nonneg _), le_rfl⟩ hcont
  refine ⟨(hu.mono hcontain).integrableOn_compact
    ((isCompact_closedBall x r).prod isCompact_Icc), hmax, fun p hp ↦ ?_⟩
  have hpS := hhalfsub hp
  have hjet :
      iteratedFDerivWithin ℝ (l + k) u.uncurry (Ω ×ˢ Icc (t - r ^ 2) t) p =
        iteratedFDerivWithin ℝ (l + k) u.uncurry (Ω ×ˢ Ioc 0 T) p :=
    iteratedFDerivWithin_subset hsub
      (hΩ.uniqueDiffOn.prod (uniqueDiffOn_Icc (by linarith)))
      (hΩ.uniqueDiffOn.prod (uniqueDiffOn_Ioc 0 T)) (hsmooth.of_le (by simp)) hpS
  have hmixed :
      spaceTimeMixedFDerivWithin k l u.uncurry (Ω ×ˢ Icc (t - r ^ 2) t) p =
        spaceTimeMixedFDerivWithin k l u.uncurry (Ω ×ˢ Ioc 0 T) p := by
    unfold spaceTimeMixedFDerivWithin
    rw [hjet]
  rw [← hmixed]
  exact hbound Ω u Dx Dxx Dt x t r hr hΩ hball
    (hu.mono hsub) (hDx.mono hsub) (hDxx.mono hsub) (hDt.mono hsub)
    (fun q hq ↦ hspace q (hsub hq)) (fun q hq ↦ hhessian q (hsub hq))
    (fun q hq ↦ (htime q (hsub hq)).mono hI) (fun q hq ↦ hheat q (hsub hq)) p hp

end HeatEquation
