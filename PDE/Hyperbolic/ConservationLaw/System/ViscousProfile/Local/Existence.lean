/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Local.Characteristics
public import PDE.Hyperbolic.ConservationLaw.System.ShockCurve.Speed
import PDE.Hyperbolic.ConservationLaw.System.WaveCurve.Compression
import PDE.Hyperbolic.ConservationLaw.System.WaveCurve.LaxOrientation

/-!
# Small viscous profiles from the flux

The shock curves classify every nearby nonzero Rankine–Hugoniot jump,
including its speed. Their continuity supplies the speed neighborhood required
by the invariant graph. The half derivative of the shock speed then identifies
the compressive orientation, independently of the normalization of eigenvectors.

Both radii are chosen before the right state and speed. Necessity concerns
profiles whose entire range lies in the chosen physical ball. Equal states
are excluded.

`exists_small_viscousProfile_iff_lax` is Evans, §11.4.1, Theorem 1, for traveling waves
(3)-(5) with values in a fixed ball around `u_l`: for `u_r` close to `u_l`, such a wave
exists exactly when Rankine–Hugoniot (9) and the Lax entropy condition (42) of §11.2.3 hold
for some `k`, which near `u_l` is the condition `u_r ∈ S_k^-(u_l)` of (12). Evans omits
the proof of sufficiency. The bound on the range is needed for necessity:
`exists_fixed_flux_nonLax_viscous_profiles` gives a flux that satisfies the hypotheses of
Theorem 1 and has traveling waves to arbitrarily close right states outside every
`S_k^-(u_l)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.1, equations (3)-(5), (9) and (12), Theorem 1 and
  its proof; §11.2.3, equation (42) and the definition of `S_k^-(z₀)`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Metric Set
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System

/-- A smooth strictly hyperbolic genuinely nonlinear flux admits a small
complete viscous profile precisely for nearby distinct Lax shock states.
The speed is arbitrary: its required local bound is derived from the
Rankine–Hugoniot equation. The profile, its regularity, and all four limits
are constructed, and necessity applies to every profile in the stated ball. -/
theorem exists_small_viscousProfile_iff_lax {m : ℕ} {flux : ℝ^m → ℝ^m}
    (hflux : ContDiff ℝ ∞ flux) (hhyper : ∀ u, IsStrictlyHyperbolicAt flux u)
    (hgn : ∀ k, IsGenuinelyNonlinearFamily flux k) (q : ℝ^m) :
    ∃ δ ρ : ℝ, 0 < δ ∧ δ < ρ ∧
      ∀ uR ∈ ball q δ, uR ≠ q → ∀ speed : ℝ,
        ((∃ v : ℝ → ℝ^m, IsViscousProfile flux q uR speed v ∧
            ∀ t, v t ∈ ball q ρ) ↔
          RankineHugoniot flux q uR speed ∧
            ∃ k, characteristicSpeed flux k uR < speed ∧
              speed < characteristicSpeed flux k q) := by
  classical
  -- In dimension zero every two states coincide, so the condition `uR ≠ q` never holds.
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨1, 2, one_pos, one_lt_two, fun uR _ hne ↦ (hne (Subsingleton.elim uR q)).elim⟩
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨b, S, σ, I₀, V₀, C, _hC, hdiag, hI₀, hzero₀, hV₀, hqV₀, _hVU, hcurves, hclass₀⟩ :=
    exists_local_shock_curves_with_quadratic_speed (n := 2)
      (by norm_num) isOpen_univ (mem_univ q)
      (hflux.of_le (by simp)).contDiffOn (hhyper q)
  have hfamily (k : Fin m) :=
    exists_characteristic_profile_radius hflux q (hhyper q) b k hdiag (hgn k)
  choose ρ₀ hρ₀ hfamily using hfamily
  let ρ : ℝ := Finset.univ.inf' Finset.univ_nonempty ρ₀
  have hρ : 0 < ρ := (Finset.lt_inf'_iff _).mpr (fun k _ ↦ hρ₀ k)
  have hρle (k : Fin m) : ρ ≤ ρ₀ k := Finset.inf'_le _ (Finset.mem_univ k)
  have hfamily' (k : Fin m) := hfamily k ρ hρ (hρle k)
  choose δ₀ η hδ₀ hδρ hη hprofile using hfamily'
  have hsign (k : Fin m) : ∀ᶠ s in 𝓝 0, (characteristicSpeed flux k (S k s) < σ k s ∧
          σ k s < characteristicSpeed flux k q) ↔
        fderiv ℝ (characteristicSpeed flux k) q (b k) * s < 0 :=
    eventually_lax_iff_mul_neg (hgn k q).1 (hcurves k).1 (hcurves k).2.1 (hcurves k).2.2.2.2.1
      (hcurves k).2.2.2.2.2.1 ((hgn k q).2 (b k)
        ⟨Module.End.mem_eigenspace_iff.mpr (hdiag k), b.ne_zero k⟩)
  have hspeed (k : Fin m) : ∀ᶠ s in 𝓝 0, σ k s - characteristicSpeed flux k q ∈ ball 0 (η k) :=
    (hcurves k).2.2.2.2.2.1.continuousAt.sub_const (characteristicSpeed flux k q)
      (by simpa only [(hcurves k).2.1, sub_self] using isOpen_ball.mem_nhds (mem_ball_self (hη k)))
  have hseparation : ∀ᶠ s in 𝓝 0, ∀ k, (∀ j, j < k → characteristicSpeed flux j q < σ k s) ∧
      (∀ j, k < j → σ k s < characteristicSpeed flux j (S k s)) := by
    have hnear := eventually_lax_separation (eig := characteristicSpeed flux)
      (S := fun k (p : ℝ × ℝ^m) ↦ S k p.1) (speed := fun k (p : ℝ × ℝ^m) ↦ σ k p.1)
      (fun k ↦ (hgn k q).1.continuousAt) (fun k ↦ (hcurves k).2.2.2.2.1.continuousAt.comp_of_eq
        (continuousAt_fst : ContinuousAt (Prod.fst : ℝ × ℝ^m → ℝ) (0, q)) rfl)
      (fun k ↦ (hcurves k).2.2.2.2.2.1.continuousAt.comp_of_eq
        (continuousAt_fst : ContinuousAt (Prod.fst : ℝ × ℝ^m → ℝ) (0, q)) rfl)
      (fun k ↦ ⟨(hcurves k).1, (hcurves k).2.1⟩) (characteristicSpeed_spec (hhyper q)).1
    exact (continuousAt_id.prodMk continuousAt_const).eventually hnear
  obtain ⟨I, hIsub, hI, hzero⟩ := _root_.mem_nhds_iff.mp (Filter.inter_mem (hI₀.mem_nhds hzero₀)
      ((eventually_all.mpr hsign).and ((eventually_all.mpr hspeed).and hseparation)))
  obtain ⟨V, hV, hqV, _hVV, hclass⟩ :=
    exists_shock_classification_on_parameter_neighborhood b hI hzero
      (fun s hs ↦ (hIsub hs).1) hV₀ hqV₀ (fun k s hs ↦ ((hcurves k).2.2.2.2.2.2 s hs).2.2.1) hclass₀
  have hstates : ∀ᶠ u in 𝓝 q, u ∈ V ∧ ∀ k, u ∈ ball q (δ₀ k) :=
    Filter.Eventually.and (hV.mem_nhds hqV)
      (eventually_all.mpr fun k ↦ isOpen_ball.mem_nhds (mem_ball_self (hδ₀ k)))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hstates
  let δ := min ε (ρ / 2)
  refine ⟨δ, ρ, lt_min hε (half_pos hρ), (min_le_right _ _).trans_lt (half_lt_self hρ),
    fun uR huR hne speed ↦ ?_⟩
  have hsmall := hεsub (ball_subset_ball (min_le_left _ _) huR)
  have hclassified (hRH : RankineHugoniot flux q uR speed) :
      (∃ v : ℝ → ℝ^m, IsViscousProfile flux q uR speed v ∧ ∀ t, v t ∈ ball q ρ) ↔
        ∃ k, characteristicSpeed flux k uR < speed ∧
          speed < characteristicSpeed flux k q := by
    obtain ⟨k, s, hs, _hsne, hstate, heqσ⟩ := (hclass uR hsmall.1 speed hne).mp hRH
    have hμ : speed - characteristicSpeed flux k q ∈ ball 0 (η k) := heqσ ▸ (hIsub hs).2.2.1 k
    have hcanonical : characteristicSpeed flux k q +
        (speed - characteristicSpeed flux k q) = speed := add_sub_cancel _ _
    have hiff := hprofile k uR (hsmall.2 k) hne
      (speed - characteristicSpeed flux k q) hμ (hcanonical.symm ▸ hRH)
    rw [hcanonical] at hiff
    have hcoord : b.equivFunL (uR - q) k = s := by
      rw [hstate]
      exact ((hcurves k).2.2.2.2.2.2 s (hIsub hs).1).2.2.1
    rw [hcoord] at hiff
    have hsign' : (characteristicSpeed flux k uR < speed ∧ speed < characteristicSpeed flux k q) ↔
        fderiv ℝ (characteristicSpeed flux k) q (b k) * s < 0 := by
      rw [hstate, heqσ]
      exact (hIsub hs).2.1 k
    rw [← hsign'] at hiff
    refine hiff.trans ⟨fun hk ↦ ⟨k, hk⟩, ?_⟩
    rintro ⟨j, hjleft, hjright⟩
    rcases lt_trichotomy j k with hj | rfl | hj
    · have hsep := ((hIsub hs).2.2.2 k).1 j hj
      rw [← heqσ] at hsep
      exact (lt_asymm hsep hjright).elim
    · exact ⟨hjleft, hjright⟩
    · have hsep := ((hIsub hs).2.2.2 k).2 j hj
      rw [← heqσ, ← hstate] at hsep
      exact (lt_asymm hsep hjleft).elim
  refine ⟨fun hv ↦ ?_, fun ⟨hRH, hLax⟩ ↦ (hclassified hRH).mpr hLax⟩
  have hRH := hv.choose_spec.1.rankineHugoniot (hflux.differentiable (by simp))
  exact ⟨hRH, (hclassified hRH).mp hv⟩

end PDE.Hyperbolic.ConservationLaw.System
