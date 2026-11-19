/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.RiemannSolver.EntropyProduction
public import PDE.Hyperbolic.ConservationLaw.System.ShockCurve.Speed
import PDE.Hyperbolic.ConservationLaw.System.WaveCurve.Compression
import PDE.Hyperbolic.ConservationLaw.System.WaveCurve.LaxOrientation

/-!
# Strict convex entropy selects nearby Lax shocks

The exact derivative of entropy production along a Hugoniot curve is the speed
derivative times a tangent remainder. Strict convexity makes that remainder
positive off the base state, using only the `C¹` regularity of the entropy pair.
Genuine nonlinearity then identifies the sign with the Lax orientation. All
neighborhoods are chosen before the entropy pair, the right state, and the shock speed.

The criterion assumes a globally strictly convex compatible entropy.

The entropy pairs are the convex pairs (25)-(26) of Evans, §11.4.2, with `C¹` regularity, and
admissibility is the jump form of the entropy inequality (28)-(29) for a shock. For `u_r`
close to `u_l`, `exists_radius_lax_of_strict_entropy_admissible` derives from admissibility
for a strictly convex entropy the Lax entropy condition (42) of Evans, §11.2.3, for some
family `k`, together with the inequalities for the other families.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.3, equation (42); §11.4.2, equations (25)-(29).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Metric Set
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System

variable {m : ℕ} {flux : ℝ^m → ℝ^m}

/-- Near a regular Hugoniot branch with nonzero speed derivative, strictly convex
C¹ entropy production has the sign of the strength times that derivative.
The parameter neighborhood is independent of the entropy pair. -/
theorem eventually_shock_production_mul_pos {S : ℝ → ℝ^m} {speed : ℝ → ℝ} {q : ℝ^m} {c : ℝ}
    (hS : ContDiffAt ℝ 1 S 0) (hspeed : ContDiffAt ℝ 1 speed 0) (hzero : S 0 = q)
    (hRH : ∀ᶠ a in 𝓝 0, RankineHugoniot flux q (S a) (speed a)) (hne : ∀ᶠ a in 𝓝 0, a ≠ 0 → S a ≠ q)
    (hd : HasDerivAt speed c 0) (hc : c ≠ 0) :
    ∀ᶠ a in 𝓝 0, a ≠ 0 → ∀ E : ConvexEntropyPair flux, StrictConvexOn ℝ univ E.entropy → 0 <
      (c * a) *
      (E.entropyFlux (S a) - E.entropyFlux q - speed a * (E.entropy (S a) - E.entropy q)) := by
  have hderiv : ContinuousAt (deriv speed) 0 :=
    (hspeed.derivWithin (m := 0) (by norm_num)).continuousAt
  have hpos : 0 < c * deriv speed 0 := by rw [hd.deriv]; exact mul_self_pos.mpr hc
  have hnear : ∀ᶠ a in 𝓝 0, ContDiffAt ℝ 1 S a ∧ ContDiffAt ℝ 1 speed a ∧
      0 < c * deriv speed a ∧ RankineHugoniot flux q (S a) (speed a) ∧
      (a ≠ 0 → S a ≠ q) := by
    filter_upwards [hS.eventually (by simp), hspeed.eventually (by simp),
      (continuousAt_const.mul hderiv) (Ioi_mem_nhds hpos), hRH, hne] with a hSa hσa hca hRHa hnea
    exact ⟨hSa, hσa, hca, hRHa, hnea⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  filter_upwards [ball_mem_nhds (0 : ℝ) hδ] with a ha hane E hstrict
  let D : ℝ → ℝ := fun t ↦ E.entropyFlux (S t) - E.entropyFlux q -
    speed t * (E.entropy (S t) - E.entropy q)
  let g : ℝ → ℝ := fun t ↦ c * D t
  have hgzero : g 0 = 0 := by simp [g, D, hzero]
  have hmem {t : ℝ} (ht : t ∈ Ioo (-δ) δ) : t ∈ ball (0 : ℝ) δ := Real.ball_zero_eq_Ioo δ ▸ ht
  have hgderiv {t : ℝ} (ht : t ∈ Ioo (-δ) δ) : HasDerivAt g (c * (deriv speed t *
        (fderiv ℝ E.entropy (S t) (S t - q) - (E.entropy (S t) - E.entropy q)))) t := by
    have hlocal : ∀ᶠ s in 𝓝 t, RankineHugoniot flux q (S s) (speed s) :=
      eventually_of_mem (isOpen_ball.mem_nhds (hmem ht)) fun s hs ↦ (hball hs).2.2.2.1
    exact (E.toEntropyPair.hasDerivAt_shock_production
      (hball (hmem ht)).1.differentiableAt_one.hasDerivAt
      (hball (hmem ht)).2.1.differentiableAt_one.hasDerivAt hlocal).const_mul c
  have hmono {l r : ℝ} (hl : -δ < l) (hr : r < δ) (hz : 0 ∉ Ioo l r) :
      StrictMonoOn g (Icc l r) := by
    have hsub : Icc l r ⊆ Ioo (-δ) δ := Icc_subset_Ioo hl hr
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
      (fun t ht ↦ (hgderiv (hsub ht)).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hgderiv (hsub (interior_subset ht))).hasDerivWithinAt)
    intro t ht
    have ht' : t ∈ Ioo l r := by simpa only [interior_Icc] using ht
    have htne : t ≠ 0 := fun heq ↦ hz (heq ▸ ht')
    have hbt := hball (hmem (hsub (interior_subset ht)))
    rw [← mul_assoc]
    exact mul_pos hbt.2.2.1 (E.relative_remainder_pos hstrict (hbt.2.2.2.2 htne).symm)
  have ha' : a ∈ Ioo (-δ) δ := Real.ball_zero_eq_Ioo δ ▸ ha
  have hsign : 0 < a * g a := by
    rcases lt_or_gt_of_ne hane with hneg | hpos
    · have hg := hmono ha'.1 hδ (by simp) ⟨le_rfl, hneg.le⟩ ⟨hneg.le, le_rfl⟩ hneg
      rw [hgzero] at hg
      exact mul_pos_of_neg_of_neg hneg hg
    · have hg := hmono (neg_neg_of_pos hδ) ha'.2 (by simp) ⟨le_rfl, hpos.le⟩ ⟨hpos.le, le_rfl⟩ hpos
      rw [hgzero] at hg
      exact mul_pos hpos hg
  simpa only [g, D, mul_left_comm a c, mul_assoc] using hsign

/-- A C² strictly hyperbolic genuinely nonlinear flux has a fixed neighborhood
where admissibility for any strictly convex C¹ entropy implies all strict Lax
inequalities and strictly negative entropy production. The radius precedes the
entropy pair, right state, and arbitrary shock speed. -/
theorem exists_radius_lax_of_strict_entropy_admissible (hflux : ContDiff ℝ 2 flux) (q : ℝ^m)
    (hhyper : IsStrictlyHyperbolicAt flux q) (hgn : ∀ k, IsGenuinelyNonlinearFamily flux k) :
    ∃ δ > 0, ∀ E : ConvexEntropyPair flux,
      StrictConvexOn ℝ univ E.entropy →
      ∀ r ∈ ball q δ, r ≠ q → ∀ speed : ℝ,
      E.toEntropyPair.IsAdmissibleShock q r speed →
      E.entropyFlux r - E.entropyFlux q < speed * (E.entropy r - E.entropy q) ∧
        ∃ k, characteristicSpeed flux k r < speed ∧
          speed < characteristicSpeed flux k q ∧
          (∀ j, j < k → characteristicSpeed flux j q < speed) ∧
          (∀ j, k < j → speed < characteristicSpeed flux j r) := by
  obtain ⟨b, eig, S, σ, I₀, V₀, horder, heigen, hI₀, hzero₀, hV₀, hqV₀, _hVU, hcurves, hclass₀⟩ :=
    exists_local_shock_curves isOpen_univ (mem_univ q) hflux.contDiffOn hhyper
  have hcanonical (k : Fin m) : eig k = characteristicSpeed flux k q :=
    (congrFun (characteristicSpeed_eq_of_eigenbasis b horder heigen) k).symm
  let c : Fin m → ℝ := fun k ↦ fderiv ℝ (characteristicSpeed flux k) q (b k)
  have hc (k : Fin m) : c k ≠ 0 :=
    (hgn k q).2 (b k) ⟨Module.End.mem_eigenspace_iff.mpr (hcanonical k ▸ heigen k), b.ne_zero k⟩
  have hbase (k : Fin m) : σ k 0 = characteristicSpeed flux k q :=
    (hcurves k).2.1.trans (hcanonical k)
  have hregularS (k : Fin m) : ContDiffAt ℝ 1 (S k) 0 :=
    (hcurves k).2.2.1.contDiffAt (hI₀.mem_nhds hzero₀)
  have hregularσ (k : Fin m) : ContDiffAt ℝ 1 (σ k) 0 :=
    (hcurves k).2.2.2.1.contDiffAt (hI₀.mem_nhds hzero₀)
  have hRHcoord (k : Fin m) : ∀ᶠ a in 𝓝 0,
      RankineHugoniot flux q (S k a) (σ k a) ∧ b.equivFun (S k a - q) k = a :=
    eventually_of_mem (hI₀.mem_nhds hzero₀) fun a ha ↦ ((hcurves k).2.2.2.2.2 a ha).2
  have hhalf (k : Fin m) : HasDerivAt (σ k) ((1 / 2 : ℝ) * c k) 0 :=
    hasDerivAt_shock_speed isOpen_univ (mem_univ q) hflux.contDiffOn b eig
      horder heigen (hcurves k).1 (hcurves k).2.1 (hcurves k).2.2.2.2.1
      (hregularσ k).continuousAt (hRHcoord k)
  have hproduction (k : Fin m) : ∀ᶠ a in 𝓝 0, a ≠ 0 →
      ∀ E : ConvexEntropyPair flux, StrictConvexOn ℝ univ E.entropy →
      0 < (((1 / 2 : ℝ) * c k) * a) * (E.entropyFlux (S k a) - E.entropyFlux q -
          σ k a * (E.entropy (S k a) - E.entropy q)) := by
    have hne : ∀ᶠ a in 𝓝 0, a ≠ 0 → S k a ≠ q := (hRHcoord k).mono fun a ha hane heq ↦
      hane (by simpa only [heq, sub_self, map_zero, Pi.zero_apply] using ha.2.symm)
    exact eventually_shock_production_mul_pos (hregularS k) (hregularσ k)
      (hcurves k).1 ((hRHcoord k).mono fun _ h ↦ h.1) hne (hhalf k)
      (mul_ne_zero (by norm_num) (hc k))
  have hsign (k : Fin m) : ∀ᶠ a in 𝓝 0, (characteristicSpeed flux k (S k a) < σ k a ∧
        σ k a < characteristicSpeed flux k q) ↔ c k * a < 0 :=
    eventually_lax_iff_mul_neg (hgn k q).1 (hcurves k).1 (hbase k)
      (hcurves k).2.2.2.2.1 (hhalf k) (hc k)
  have hseparation : ∀ᶠ a in 𝓝 0, ∀ k, (∀ j, j < k → characteristicSpeed flux j q < σ k a) ∧
      (∀ j, k < j → σ k a < characteristicSpeed flux j (S k a)) := by
    have hnear := eventually_lax_separation (eig := characteristicSpeed flux)
      (S := fun k (p : ℝ × ℝ^m) ↦ S k p.1) (speed := fun k (p : ℝ × ℝ^m) ↦ σ k p.1)
      (fun k ↦ (hgn k q).1.continuousAt) (fun k ↦ (hregularS k).continuousAt.comp_of_eq
        (continuousAt_fst : ContinuousAt (Prod.fst : ℝ × ℝ^m → ℝ) (0, q)) rfl)
      (fun k ↦ (hregularσ k).continuousAt.comp_of_eq
        (continuousAt_fst : ContinuousAt (Prod.fst : ℝ × ℝ^m → ℝ) (0, q)) rfl)
      (fun k ↦ ⟨(hcurves k).1, hbase k⟩) (characteristicSpeed_spec hhyper).1
    exact (continuousAt_id.prodMk continuousAt_const).eventually hnear
  obtain ⟨I, hIsub, hI, hzero⟩ := _root_.mem_nhds_iff.mp
    (Filter.inter_mem (hI₀.mem_nhds hzero₀) ((eventually_all.mpr hproduction).and
      ((eventually_all.mpr hsign).and hseparation)))
  obtain ⟨V, hV, hqV, _hVV, hclass⟩ :=
    exists_shock_classification_on_parameter_neighborhood b hI hzero
      (fun a ha ↦ (hIsub ha).1) hV₀ hqV₀ (fun k a ha ↦ ((hcurves k).2.2.2.2.2 a ha).2.2) hclass₀
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hqV)
  refine ⟨δ, hδ, fun E hstrict r hr hrne speed hadm ↦ ?_⟩
  obtain ⟨k, a, ha, hane, rfl, rfl⟩ := (hclass r (hball hr) speed hrne).mp hadm.1
  have hmul := (hIsub ha).2.1 k hane E hstrict
  have hDle : E.entropyFlux (S k a) - E.entropyFlux q -
      σ k a * (E.entropy (S k a) - E.entropy q) ≤ 0 := sub_nonpos.mpr hadm.2
  have hca : ((1 / 2 : ℝ) * c k) * a < 0 :=
    lt_of_not_ge fun h ↦ (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos h hDle)) hmul
  have hDneg : E.entropyFlux (S k a) - E.entropyFlux q -
      σ k a * (E.entropy (S k a) - E.entropy q) < 0 :=
    hDle.lt_of_ne fun heq ↦ by rw [heq, mul_zero] at hmul; exact lt_irrefl _ hmul
  have hstrength : c k * a < 0 := by nlinarith [hca]
  have hlax := ((hIsub ha).2.2.1 k).mpr hstrength
  exact ⟨sub_neg.mp hDneg, k, hlax.1, hlax.2, (hIsub ha).2.2.2 k⟩

end PDE.Hyperbolic.ConservationLaw.System
