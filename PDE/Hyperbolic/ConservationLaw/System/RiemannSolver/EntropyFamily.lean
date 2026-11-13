/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.WaveCurve.Construction
public import PDE.Hyperbolic.ConservationLaw.System.RiemannSolver.EntropyProduction
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Local wave families retaining entropy dissipation

The joint shock and flow construction retains the half-speed derivative at zero strength,
(31) of Evans, §11.2.3. It gives entropy dissipation uniformly in the left state and in every
convex compatible entropy pair. The elementary-family chart then supplies the same local
inverse strength map as in the proof of Theorem 4 of §11.2.4.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.3, proof of Theorem 2, equation (31); §11.2.4,
  Theorem 4; §11.4.2, equations (25)-(29).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Metric Set
open scoped Topology

open Classical in
/-- A `C²` strictly hyperbolic flux whose ordered families are genuinely
nonlinear or linearly degenerate has a local elementary wave family.
The shock and flow carriers are retained, with their regularity and exact
equations, for constructing uniformly bounded self-similar fans. The negative
Hugoniot branches dissipate all convex compatible entropies on a neighborhood
chosen independently of the entropy pair. No wave curves,
admissibility inequalities, or smooth eigenframe are inputs. -/
theorem exists_local_elementary_wave_family_with_shock_entropy {m : ℕ} {flux : ℝ^m → ℝ^m}
    (hflux : ContDiff ℝ 2 flux) (hhyper : ∀ q, IsStrictlyHyperbolicAt flux q)
    (hfamilies : ∀ k, IsGenuinelyNonlinearFamily flux k ∨ IsLinearlyDegenerateFamily flux k)
    (q₀ : ℝ^m) :
    ∃ fields : Fin m → CharacteristicField flux,
      (∀ k, (fields k).speed = characteristicSpeed flux k) ∧
      ∃ states : Set (ℝ^m), IsOpen states ∧ q₀ ∈ states ∧
      ∃ W : LocalWaveFamily flux fields states, W.IsElementary ∧
      ∃ b : Module.Basis (Fin m) ℝ (ℝ^m),
        (∀ k, b k = (fields k).rightEigenvector q₀) ∧
      ∃ S : Fin m → ℝ × ℝ^m → ℝ^m,
      ∃ speed : Fin m → ℝ × ℝ^m → ℝ,
      ∃ R : Fin m → ℝ × ℝ^m → ℝ^m,
        (∀ k, ContDiffAt ℝ 1 (S k) (0, q₀) ∧
          ContDiffAt ℝ 1 (speed k) (0, q₀) ∧
          ContDiffAt ℝ 1 (R k) (0, q₀) ∧
          ContDiffAt ℝ 1 (fun p : ℝ × ℝ^m ↦ W.curve k p.1 p.2) (0, q₀)) ∧
        (∀ᶠ q in 𝓝 q₀, ∀ k,
          S k (0, q) = q ∧ R k (0, q) = q ∧
            speed k (0, q) = (fields k).speed q) ∧
        (∀ᶠ p in 𝓝 ((0 : ℝ), q₀), ∀ k,
          W.curve k p.1 p.2 =
            (if IsGenuinelyNonlinearFamily flux k then
              if p.1 ≤ 0 then S k p else R k p else R k p) ∧
          RankineHugoniot flux p.2 (S k p) (speed k p) ∧
          HasDerivAt (fun t ↦ R k (t, p.2))
            ((fields k).rightEigenvector (R k p)) p.1) ∧
        (∀ k, IsGenuinelyNonlinearFamily flux k →
          0 < fderiv ℝ (fields k).speed q₀ ((fields k).rightEigenvector q₀)) ∧
        (∀ᶠ p in 𝓝 ((0 : ℝ), q₀), ∀ k,
          IsGenuinelyNonlinearFamily flux k → p.1 ≤ 0 → ∀ E : ConvexEntropyPair flux,
            E.entropyFlux (S k p) - E.entropyFlux p.2 ≤
              speed k p * (E.entropy (S k p) - E.entropy p.2)) := by
  classical
  obtain ⟨r, eig, S, speed, R, hreg, hspec, hzero, hflow, _hcompress, horient⟩ :=
    exists_joint_shock_rarefaction hflux (hhyper q₀)
  have hfluxDiff : Differentiable ℝ flux := fun q ↦ (hhyper q).1
  obtain ⟨fields, hcanonical, hr⟩ := exists_characteristicFields_of_eigenframe hhyper hspec
  have heig (k : Fin m) : (fields k).speed =ᶠ[𝓝 q₀] eig k :=
    hcanonical k ▸ characteristicSpeed_eventuallyEq_of_eigenframe hspec k
  have heigReg (k : Fin m) : ContDiffAt ℝ 1 (fields k).speed q₀ :=
    hcanonical k ▸ contDiffAt_characteristicSpeed hflux (hhyper q₀) k
  have hpositive (k : Fin m) (hgn : IsGenuinelyNonlinearFamily flux k) :
      0 < fderiv ℝ (fields k).speed q₀ ((fields k).rightEigenvector q₀) := by
    rw [(heig k).fderiv_eq, hr.self_of_nhds k]
    exact lt_of_le_of_ne (horient k) (hgn.fderiv_ne_zero_of_eigenframe hspec).symm
  have hentropy (k : Fin m) : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀),
      IsGenuinelyNonlinearFamily flux k → p.1 ≤ 0 → ∀ E : ConvexEntropyPair flux,
        E.entropyFlux (S k p) - E.entropyFlux p.2 ≤
          speed k p * (E.entropy (S k p) - E.entropy p.2) := by
    by_cases hgn : IsGenuinelyNonlinearFamily flux k
    · have hpos : 0 < fderiv ℝ (eig k) q₀ (r k q₀) := by
        simpa only [(heig k).fderiv_eq, hr.self_of_nhds k] using hpositive k hgn
      exact (eventually_shock_entropy_of_positive_speed_deriv (hreg k).2.2.1 (hreg k).2.2.2.1
        (hzero.mono fun _ h ↦ (h k).1) (hflow.mono fun _ h ↦ (h k).1)
        (hzero.self_of_nhds k).2.2.2.2.2.2
        (mul_pos (by norm_num) hpos)).mono fun _ hp _ ↦ hp
    · exact Eventually.of_forall fun _ h ↦ (hgn h).elim
  have hz : ∀ᶠ q in 𝓝 q₀, ∀ k, S k (0, q) = q ∧ R k (0, q) = q ∧
        speed k (0, q) = (fields k).speed q := by
    filter_upwards [hzero, eventually_all.mpr heig] with q hq heq
    exact fun k ↦ ⟨(hq k).1, (hq k).2.1, (hq k).2.2.1.trans (heq k).symm⟩
  have hflowC (k : Fin m) : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), HasDerivAt (fun t ↦ R k (t, p.2))
        ((fields k).rightEigenvector (R k p)) p.1 := by
    have ht : Tendsto (R k) (𝓝 (0, q₀)) (𝓝 q₀) := by
      simpa only [ContinuousAt, (hzero.self_of_nhds k).2.1] using (hreg k).2.2.2.2.1.continuousAt
    filter_upwards [hflow, ht.eventually hr] with p hp hrp
    rw [hrp k]
    exact (hp k).2.2
  have hsep := eventually_lax_separation (fun k ↦ (heigReg k).continuousAt)
    (fun k ↦ (hreg k).2.2.1.continuousAt) (fun k ↦ (hreg k).2.2.2.1.continuousAt)
    (fun k ↦ ⟨(hz.self_of_nhds k).1, (hz.self_of_nhds k).2.2⟩)
    (by simpa only [hcanonical] using (characteristicSpeed_spec (hhyper q₀)).1)
  let T (k : Fin m) (p : ℝ × ℝ^m) := if IsGenuinelyNonlinearFamily flux k then
      if p.1 ≤ 0 then S k p else R k p else R k p
  have hTreg (k : Fin m) : ContDiffAt ℝ 1 (T k) (0, q₀) := by
    dsimp only [T]
    split_ifs
    exacts [(hreg k).2.2.2.2.2, (hreg k).2.2.2.2.1]
  have hTzero : ∀ᶠ q in 𝓝 q₀, ∀ k, T k (0, q) = q :=
    hzero.mono fun q hq k ↦ by simp only [T, le_refl, (hq k).1, (hq k).2.1, ite_self]
  have hTderiv : ∀ᶠ q in 𝓝 q₀, ∀ k, HasStrictFDerivAt (T k)
        (waveStepDerivative ((fields k).rightEigenvector q)) (0, q) := by
    have hRnear (k : Fin m) : ∀ᶠ q in 𝓝 q₀, ContDiffAt ℝ 1 (R k) (0, q) :=
      (continuousAt_const.prodMk continuousAt_id)
        ((hreg k).2.2.2.2.1.eventually (by simp))
    filter_upwards [hzero, hr, eventually_all.mpr hRnear] with q hq hrq hRq
    intro k
    rw [waveStepDerivative, hrq k, add_comm]
    dsimp only [T]
    split_ifs
    exacts [(hq k).2.2.2.2.2.1, (hRq k).hasStrictFDerivAt' (hq k).2.2.2.2.1 one_ne_zero]
  have hTelem (k : Fin m) : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀),
      IsElementaryConnection fields k p.2 (T k p) := by
    by_cases hgn : IsGenuinelyNonlinearFamily flux k
    · have htanS : HasDerivAt (fun s ↦ S k (s, q₀))
          ((fields k).rightEigenvector q₀) 0 := by
        rw [hr.self_of_nhds k]
        simpa [Function.comp_def] using (hzero.self_of_nhds k).2.2.2.1.comp_hasDerivAt (0 : ℝ)
            ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) q₀))
      have htanR : HasDerivAt (fun s ↦ R k (s, q₀))
          ((fields k).rightEigenvector q₀) 0 := by
        simpa only [(hz.self_of_nhds k).2.1] using (hflowC k).self_of_nhds
      have hhalf : HasDerivAt (fun s ↦ speed k (s, q₀)) ((1 / 2 : ℝ) *
            fderiv ℝ (fields k).speed q₀ ((fields k).rightEigenvector q₀)) 0 := by
        rw [(heig k).fderiv_eq, hr.self_of_nhds k]
        exact (hzero.self_of_nhds k).2.2.2.2.2.2
      simpa only [T, ite_eq_left hgn] using eventually_isElementaryConnection_joined (heigReg k)
          (hreg k).2.2.1 (hreg k).2.2.2.2.1 (hreg k).2.2.2.1
          (hz.mono fun _ h ↦ h k) htanS htanR hhalf (hpositive k hgn)
          (hflow.mono fun _ h ↦ (h k).1) (hflowC k) (hsep.mono fun _ h ↦ h k)
    · have hld := (isLinearlyDegenerateFamily_iff hhyper k (fields k)
        (hcanonical k)).mp ((hfamilies k).resolve_left hgn)
      obtain ⟨δ, hδ, hcontact⟩ := exists_uniform_contact_of_local_flow hfluxDiff
        (hreg k).2.2.2.2.1.continuousAt (hz.mono fun _ h ↦ (h k).2.1)
        (hflowC k) (Filter.Eventually.of_forall fun q ↦
          ⟨hld.1 q, hld.2 q, ((fields k).eigenvector q).apply_eq_smul⟩)
      filter_upwards [ball_mem_nhds ((0 : ℝ), q₀) hδ] with p hp
      rw [← ball_prod_same, Real.ball_zero_eq_Ioo] at hp
      obtain ⟨hspeed, hRH⟩ := hcontact p.2 hp.2 p.1 hp.1
      simp only [T, ite_eq_right hgn]
      exact .contact ((fields k).speed p.2) ⟨hRH, rfl, hspeed.symm⟩
  obtain ⟨states, hopen, hq₀, W, hW, hWT⟩ :=
    LocalWaveFamily.exists_of_local_curves hTzero hTderiv (eventually_all.mpr hTelem)
  obtain ⟨_horder, _heigen, b, hb⟩ := hspec.self_of_nhds
  refine ⟨fields, hcanonical, states, hopen, hq₀, W, hW, b,
    fun k ↦ (hb k).trans (hr.self_of_nhds k).symm, S, speed, R,
    fun k ↦ ⟨(hreg k).2.2.1, (hreg k).2.2.2.1, (hreg k).2.2.2.2.1,
      (hTreg k).congr_of_eventuallyEq (hWT.mono fun _ h ↦ h k)⟩, hz, ?_,
    hpositive, eventually_all.mpr hentropy⟩
  filter_upwards [hWT, hflow, eventually_all.mpr hflowC] with p hp hFp hCp
  exact fun k ↦ ⟨hp k, (hFp k).1, hCp k⟩

end PDE.Hyperbolic.ConservationLaw.System
