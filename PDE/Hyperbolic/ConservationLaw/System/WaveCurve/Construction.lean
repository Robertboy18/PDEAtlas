/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Piecewise
public import PDE.Analysis.ODE.SmoothDependence.Local
public import PDE.Hyperbolic.ConservationLaw.System.WaveCurve.Admissibility
public import PDE.Hyperbolic.ConservationLaw.System.WaveCurve.Shock
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Joint shock and rarefaction construction

Strict hyperbolicity and a `C²` flux construct local ordered eigenfields, implicit
shock branches, and rarefaction flows. Their full derivatives agree along
zero strength, including the initial-state block. The joined transformation is
therefore jointly `C¹` and strictly differentiable.

For every positively oriented family, the half-factor gives compression and the
flow gives expansion on common intervals for nearby left states. The eigenfields
are oriented by a constant sign at the base state.

In the notation of Evans, §11.2, `S k (s, q)` runs along the shock curve `S_k(q)` of §11.2.3,
Theorem 2, with shock speed `speed k (s, q)`, and `R k (s, q)` along the rarefaction curve
`R_k(q)` of (6) in §11.2.1. Both curves have tangent `r_k(q)` at zero strength, as in Theorem
2(i), and the shock speed has derivative `Dλ_k · r_k / 2` there, the derivative form of Theorem
2(iii). When `Dλ_k · r_k > 0` at `q₀`, then for `q` near `q₀` and small strengths the positive
branch of `R k` lies in `R_k^+(q)` and the negative branch of `S k` in `S_k^-(q)`. The joined
map, `S k` for negative and `R k` for positive strength, then parametrizes the curve `T_k(q)`
of §11.2.4 near `q`, and its strict derivative at zero strength is the `C¹` property of
`T_k(z₀)` stated there. `exists_local_elementary_wave_family` gives these curves for every
family under the hypotheses of §11.2.4, Theorem 4, with the derivative `r_k` at zero strength
that step 3 of its proof uses; for a linearly degenerate family the wave curve is `R k`, as
`T_k(z₀) = R_k(z₀)` there.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.1, equation (6) and the notation `R_k^±(z₀)`;
  §11.2.3, Theorem 2 and the definition of `S_k^-(z₀)`; §11.2.4, the definition of `T_k(z₀)`,
  Theorem 4 and step 3 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Metric Set
open scoped Topology

/-- Local hyperbolicity constructs joint shock and rarefaction branches with
matching full derivatives. Positive directional eigenvalue derivative yields
uniform compression and expansion; neither inequality is an input. -/
theorem exists_joint_shock_rarefaction {m : ℕ} {flux : ℝ^m → ℝ^m} (hflux : ContDiff ℝ 2 flux)
    {q₀ : ℝ^m} (hhyper : IsStrictlyHyperbolicAt flux q₀) :
    ∃ r : Fin m → ℝ^m → ℝ^m, ∃ eig : Fin m → ℝ^m → ℝ,
    ∃ S : Fin m → ℝ × ℝ^m → ℝ^m, ∃ speed : Fin m → ℝ × ℝ^m → ℝ,
    ∃ R : Fin m → ℝ × ℝ^m → ℝ^m,
      (∀ k, ContDiffAt ℝ 1 (r k) q₀ ∧ ContDiffAt ℝ 1 (eig k) q₀ ∧
        ContDiffAt ℝ 1 (S k) (0, q₀) ∧ ContDiffAt ℝ 1 (speed k) (0, q₀) ∧
        ContDiffAt ℝ 1 (R k) (0, q₀) ∧
        ContDiffAt ℝ 1 (fun p ↦ if p.1 ≤ 0 then S k p else R k p) (0, q₀)) ∧
      (∀ᶠ q in 𝓝 q₀, StrictMono (fun k ↦ eig k q) ∧
        (∀ k, fderiv ℝ flux q (r k q) = eig k q • r k q) ∧
        ∃ b : Module.Basis (Fin m) ℝ (ℝ^m), ∀ k, b k = r k q) ∧
      (∀ᶠ q in 𝓝 q₀, ∀ k,
        S k (0, q) = q ∧ R k (0, q) = q ∧ speed k (0, q) = eig k q ∧
        HasFDerivAt (S k)
          (ContinuousLinearMap.snd ℝ ℝ (ℝ^m) +
            (ContinuousLinearMap.fst ℝ ℝ (ℝ^m)).smulRight (r k q)) (0, q) ∧
        HasFDerivAt (R k)
          (ContinuousLinearMap.snd ℝ ℝ (ℝ^m) +
            (ContinuousLinearMap.fst ℝ ℝ (ℝ^m)).smulRight (r k q)) (0, q) ∧
        HasStrictFDerivAt (fun p ↦ if p.1 ≤ 0 then S k p else R k p)
          (ContinuousLinearMap.snd ℝ ℝ (ℝ^m) +
            (ContinuousLinearMap.fst ℝ ℝ (ℝ^m)).smulRight (r k q)) (0, q) ∧
        HasDerivAt (fun s ↦ speed k (s, q))
          ((1 / 2 : ℝ) * fderiv ℝ (eig k) q (r k q)) 0) ∧
      (∀ᶠ p in 𝓝 ((0 : ℝ), q₀), ∀ k,
        RankineHugoniot flux p.2 (S k p) (speed k p) ∧
        (p.1 ≠ 0 → S k p ≠ p.2) ∧
        HasDerivAt (fun t ↦ R k (t, p.2)) (r k (R k p)) p.1) ∧
      (∀ k, 0 < fderiv ℝ (eig k) q₀ (r k q₀) →
        ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ ball q₀ δ,
          StrictMonoOn (fun s ↦ eig k (R k (s, q))) (Ioo (-δ) δ) ∧
          ∀ s ∈ Ioo (-δ) 0,
            eig k (S k (s, q)) < speed k (s, q) ∧ speed k (s, q) < eig k q) ∧
      (∀ k, 0 ≤ fderiv ℝ (eig k) q₀ (r k q₀)) := by
  obtain ⟨r, eig, S, speed, hreg, hspec, hzero, hRH, horient⟩ :=
    exists_joint_shock_family hflux hhyper
  have hflows (k : Fin m) := PDE.Analysis.ODE.exists_local_flow_of_contDiffAt (hreg k).1
  choose R hR₀ hR hRzero hflow using hflows
  have hT (k : Fin m) :
      ContDiffAt ℝ 1 (fun p ↦ if p.1 ≤ 0 then S k p else R k p) (0, q₀) := by
    apply PDE.Analysis.contDiffAt_one_if_fst_le 0 (hreg k).2.2.1 (hR k)
    have hnear := (continuousAt_snd :
      ContinuousAt (Prod.snd : ℝ × ℝ^m → ℝ^m) (0, q₀)).tendsto.eventually (hzero.and (hRzero k))
    filter_upwards [hnear] with p hp hp₀
    rw [show p = (0, p.2) from Prod.ext hp₀ rfl]
    exact ⟨(hp.1 k).1.trans hp.2.1.symm, (hp.1 k).2.2.1.fderiv.trans hp.2.2.fderiv.symm⟩
  refine ⟨r, eig, S, speed, R,
    fun k ↦ ⟨(hreg k).1, (hreg k).2.1, (hreg k).2.2.1, (hreg k).2.2.2, hR k, hT k⟩, hspec, ?_,
    ?_, ?_, horient⟩
  · have hTnear (k : Fin m) : ∀ᶠ q in 𝓝 q₀,
          ContDiffAt ℝ 1 (fun p ↦ if p.1 ≤ 0 then S k p else R k p) (0, q) :=
      (continuousAt_const.prodMk continuousAt_id) ((hT k).eventually (by simp))
    filter_upwards [hzero, eventually_all.mpr hRzero, eventually_all.mpr hTnear] with q hSq hRq hTq
    intro k
    obtain ⟨hS₀q, hspeed₀q, hdS, hhalf⟩ := hSq k
    obtain ⟨hR₀q, hdR⟩ := hRq k
    exact ⟨hS₀q, hR₀q, hspeed₀q, hdS, hdR, (hTq k).hasStrictFDerivAt'
      (PDE.Analysis.hasFDerivAt_if_of_eq (fun p : ℝ × ℝ^m ↦ p.1 ≤ 0)
        hdS hdR (hS₀q.trans hR₀q.symm)) one_ne_zero, hhalf⟩
  · filter_upwards [hRH, eventually_all.mpr hflow] with p hp hflowp
    exact fun k ↦ ⟨(hp k).1, (hp k).2, hflowp k⟩
  · intro k hpos
    obtain ⟨hS₀q, _hspeed₀q, hdS, hhalf⟩ := hzero.self_of_nhds k
    have htanS : HasDerivAt (fun s ↦ S k (s, q₀)) (r k q₀) 0 := by
      simpa [Function.comp_def] using hdS.comp_hasDerivAt (0 : ℝ)
        ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) q₀))
    have htanR : HasDerivAt (fun s ↦ R k (s, q₀)) (r k q₀) 0 := by
      simpa only [hR₀ k] using (hflow k).self_of_nhds
    obtain ⟨δ₁, hδ₁, hmono⟩ := exists_uniform_speed_expansion (hreg k).2.1 (hR k) (hR₀ k) htanR hpos
    obtain ⟨δ₂, hδ₂, hcompress⟩ := exists_uniform_shock_compression
      (hreg k).2.1 (hreg k).2.2.1 (hreg k).2.2.2
      (hzero.mono fun q hq ↦ ⟨(hq k).1, (hq k).2.1⟩) htanS hhalf hpos
    exact ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun q hq ↦
      ⟨(hmono q (ball_subset_ball (min_le_left _ _) hq)).mono
        (Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)), fun s hs ↦
      hcompress q (ball_subset_ball (min_le_right _ _) hq) s
        ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) hs.1, hs.2⟩⟩⟩

open Classical in
/-- A `C²` strictly hyperbolic flux whose ordered families are genuinely
nonlinear or linearly degenerate has a local elementary wave family.
The shock and flow carriers are retained, with their regularity and exact
equations, for constructing uniformly bounded self-similar fans. No wave
curves, admissibility inequalities, or smooth eigenframe are inputs. -/
theorem exists_local_elementary_wave_family {m : ℕ} {flux : ℝ^m → ℝ^m} (hflux : ContDiff ℝ 2 flux)
    (hhyper : ∀ q, IsStrictlyHyperbolicAt flux q)
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
          0 < fderiv ℝ (fields k).speed q₀ ((fields k).rightEigenvector q₀)) := by
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
      (hTreg k).congr_of_eventuallyEq (hWT.mono fun _ h ↦ h k)⟩, hz, ?_, hpositive⟩
  filter_upwards [hWT, hflow, eventually_all.mpr hflowC] with p hp hFp hCp
  exact fun k ↦ ⟨hp k, (hFp k).1, hCp k⟩

end PDE.Hyperbolic.ConservationLaw.System
