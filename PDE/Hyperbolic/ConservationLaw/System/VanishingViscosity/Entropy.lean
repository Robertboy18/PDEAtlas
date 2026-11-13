/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.EntropyWeak
public import PDE.DistributionTheory.Convex.Composition
public import PDE.Analysis.Integration.BoundedComposition
public import PDE.DistributionTheory.TestFunction.NonnegativeTesting
import PDE.DistributionTheory.TestFunction.IntegrationByParts

/-!
# Entropy inequalities from viscous equations

A classical viscous solution satisfies a weak convex-chain inequality for every
`C¹` convex entropy pair. Both derivatives in the viscosity defect fall
on the smooth test. Thus a bounded almost everywhere limit obeys the entropy
inequality.

`ConvexEntropyPair.neg_integral_entropyWeakIntegrand_le` is the inequality of step 2 of the
proof of Evans, §11.4.2, Theorem 2, and `satisfiesEntropyInequality_of_vanishingViscosity` is
the entropy half of that theorem: a bounded almost everywhere limit (32) of solutions of the
viscous problems (31) satisfies the entropy inequalities (29). Evans computes (33)-(34) for a
smooth pair, which uses `D²Φ`, and treats other pairs by approximation. For `C¹` convex pairs
we use instead the inequality `∫ φ DΦ(u) u_xx ≤ ∫ Φ(u) φ_xx` for tests `φ ≥ 0`, so no
approximation of the pair is needed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.2, equations (25)-(26) and (28)-(34), Theorem 2 and
  steps 1-2 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.System

variable {m : ℕ}

/-- The viscosity defect for a `C¹` convex entropy pair. The state is `C²`
only on the open domain, and the equation uses its coordinate derivatives. -/
theorem ConvexEntropyPair.neg_integral_entropyWeakIntegrand_le {flux : ℝ^m → ℝ^m}
    (E : ConvexEntropyPair flux) {U : Opens ℝ^2} {u : ℝ^2 → ℝ^m} {ε : ℝ} (hε : 0 ≤ ε)
    (hu : ContDiffOn ℝ 2 u U) (hpde : ∀ p ∈ U, fluxResidual flux u p = ε • (∂[1] (∂[1] u)) p)
    (φ : 𝓓(U, ℝ)) (hφ : ∀ p, 0 ≤ φ p) :
    -(∫ p, E.entropy (u p) * (∂[0] (φ : ℝ^2 → ℝ)) p + E.entropyFlux (u p) *
      (∂[1] (φ : ℝ^2 → ℝ)) p) ≤ ε * ∫ p, E.entropy (u p) * (∂[1] (∂[1] (φ : ℝ^2 → ℝ))) p := by
  let ψ : 𝓓^{1}(U, ℝ) :=
    .mk φ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport φ.tsupport_subset
  have hchain := PDE.DistributionTheory.integral_mul_fderiv_second_le_of_convex
    E.entropy_contDiff E.entropy_convex U.isOpen hu
    (φ.contDiff.of_le (by simp)) φ.hasCompactSupport φ.tsupport_subset hφ
    (EuclideanSpace.single 1 (1 : ℝ) : ℝ^2)
  have hres (p : ℝ^2) (hp : p ∈ U) : entropyResidual E.toEntropyPair u p =
      ε * fderiv ℝ E.entropy (u p) ((∂[1] (∂[1] u)) p) := by
    have hd := (hu.contDiffAt (U.isOpen.mem_nhds hp)).differentiableAt (by norm_num)
    rw [E.toEntropyPair.entropyResidual_eq_fderiv_quasilinearResidual hd,
      ← fluxResidual_eq_quasilinearResidual (E.flux_differentiable (u p)) hd,
      hpde p hp, map_smul, smul_eq_mul]
  calc
    _ = ∫ p, φ p * entropyResidual E.toEntropyPair u p :=
      (integral_mul_entropyResidual_eq_neg_entropyWeakIntegrand_on E.toEntropyPair
        (hu.of_le (by norm_num)) ψ).symm
    _ = ε * ∫ p, φ p * fderiv ℝ E.entropy (u p)
        ((∂[1] (∂[1] u)) p) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun p ↦ ?_)
      dsimp only
      by_cases hp : p ∈ U
      · rw [hres p hp]
        ring
      · simp [image_eq_zero_of_notMem_tsupport (fun hs ↦ hp (φ.tsupport_subset hs))]
    _ ≤ _ := mul_le_mul_of_nonneg_left hchain hε

/-- A bounded almost everywhere limit of classical viscous solutions satisfies
all convex entropy inequalities. No derivative bounds or regularized entropy
pairs are hypotheses. The viscosity can tend to zero along any countably generated filter. -/
theorem satisfiesEntropyInequality_of_vanishingViscosity {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] [l.NeBot] {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2} {u : ι → ℝ^2 → ℝ^m}
    {v : ℝ^2 → ℝ^m} {ε : ι → ℝ} {M : ℝ} (hε : ∀ᶠ i in l, 0 ≤ ε i) (hεlim : Tendsto ε l (𝓝 0))
    (hu : ∀ᶠ i in l, ContDiffOn ℝ 2 (u i) U)
    (hpde : ∀ᶠ i in l, ∀ p ∈ U, fluxResidual flux (u i) p = ε i • (∂[1] (∂[1] (u i))) p)
    (hM : ∀ᶠ i in l, ∀ᵐ p ∂volume.restrict U, ‖u i p‖ ≤ M)
    (hlim : ∀ᵐ p ∂volume.restrict U, Tendsto (fun i ↦ u i p) l (𝓝 (v p))) :
    SatisfiesEntropyInequality flux U v := by
  have hm : ∀ᶠ i in l, AEStronglyMeasurable (u i) (volume.restrict U) :=
    hu.mono fun _ hi ↦ hi.continuousOn.aestronglyMeasurable U.isOpen.measurableSet
  obtain ⟨hvm, hvM⟩ := aestronglyMeasurable_and_ae_norm_le_of_tendsto hm hM hlim
  intro E
  have hη := locallyIntegrableOn_of_locallyIntegrable_restrict
    (locallyIntegrable_comp_of_ae_bound hvm hvM E.entropy_contDiff.continuous)
  have hq := locallyIntegrableOn_of_locallyIntegrable_restrict
    (locallyIntegrable_comp_of_ae_bound hvm hvM E.entropyFlux_contDiff.continuous)
  refine ⟨hη, hq, fun ψ hψ ↦
    TestFunction.nonneg_integral_mul_partialDeriv_of_smooth hη hq 0 1 (fun φ hφ ↦ ?_) ψ hψ⟩
  let φ₁ : 𝓓^{1}(U, ℝ) :=
    .mk φ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport φ.tsupport_subset
  have hpair {f : ℝ^m → ℝ} (hf : Continuous f) {a : ℝ^2 → ℝ}
      (ha : Integrable a) (haU : ∀ p ∉ U, a p = 0) :
      Tendsto (fun i ↦ ∫ p, f (u i p) * a p) l (𝓝 (∫ p, f (v p) * a p)) := by
    have heq (w : ℝ^2 → ℝ^m) :
        (∫ p in U, a p • f (w p)) = ∫ p, f (w p) * a p := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp ↦ by simp [haU p hp])]
      simp only [smul_eq_mul, mul_comm]
    simpa only [heq] using tendsto_integral_smul_comp_of_ae_bound hm hM hlim hf ha.restrict
  have htime := hpair E.entropy_contDiff.continuous (φ₁.integrable_partialDeriv 0)
    (fun p hp ↦ φ₁.partialDeriv_eq_zero_of_notMem hp 0)
  have hspace := hpair E.entropyFlux_contDiff.continuous (φ₁.integrable_partialDeriv 1)
    (fun p hp ↦ φ₁.partialDeriv_eq_zero_of_notMem hp 1)
  have hsnd : ContDiff ℝ 1 (∂[1] (φ : ℝ^2 → ℝ)) :=
    contDiff_partialDeriv_of_succ (m := 1) (φ.contDiff.of_le (by simp))
  have hsc : HasCompactSupport (∂[1] (φ : ℝ^2 → ℝ)) :=
    φ.hasCompactSupport.fderiv_apply ℝ (EuclideanSpace.single 1 (1 : ℝ))
  have hsecond := hpair E.entropy_contDiff.continuous
    (PDE.DistributionTheory.integrable_partialDeriv_of_hasCompactSupport 1 hsnd hsc)
    (fun p hp ↦ by
      have hz : (φ : ℝ^2 → ℝ) =ᶠ[𝓝 p] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hp (φ.tsupport_subset h))
      have hd : (∂[1] (φ : ℝ^2 → ℝ)) =ᶠ[𝓝 p] 0 := by
        filter_upwards [hz.fderiv (𝕜 := ℝ)] with x hx
        simp [partialDeriv, hx]
      simp [partialDeriv, hd.fderiv_eq])
  have hi (i : ι) (hi : ContDiffOn ℝ 2 (u i) U) :
      Integrable (fun p ↦ E.entropy (u i p) * (∂[0] (φ : ℝ^2 → ℝ)) p) ∧
      Integrable (fun p ↦ E.entropyFlux (u i p) * (∂[1] (φ : ℝ^2 → ℝ)) p) :=
    ⟨φ₁.integrable_mul_partialDeriv
      ((E.entropy_contDiff.continuous.comp_continuousOn hi.continuousOn).locallyIntegrableOn
        U.isOpen.measurableSet) 0, φ₁.integrable_mul_partialDeriv
        ((E.entropyFlux_contDiff.continuous.comp_continuousOn hi.continuousOn).locallyIntegrableOn
          U.isOpen.measurableSet) 1⟩
  have hsum : Tendsto (fun i ↦ ∫ p, E.entropy (u i p) * (∂[0] (φ : ℝ^2 → ℝ)) p +
      E.entropyFlux (u i p) * (∂[1] (φ : ℝ^2 → ℝ)) p) l
      (𝓝 (∫ p, E.entropy (v p) * (∂[0] (φ : ℝ^2 → ℝ)) p +
        E.entropyFlux (v p) * (∂[1] (φ : ℝ^2 → ℝ)) p)) := by
    have hvt : Integrable (fun p ↦ E.entropy (v p) * (∂[0] (φ : ℝ^2 → ℝ)) p) :=
      φ₁.integrable_mul_partialDeriv hη 0
    have hvx : Integrable (fun p ↦ E.entropyFlux (v p) * (∂[1] (φ : ℝ^2 → ℝ)) p) :=
      φ₁.integrable_mul_partialDeriv hq 1
    rw [integral_add hvt hvx]
    exact (htime.add hspace).congr'
      (hu.mono fun i hi' ↦ (integral_add (hi i hi').1 (hi i hi').2).symm)
  have hz : Tendsto (fun i ↦ ε i * ∫ p,
      E.entropy (u i p) * (∂[1] (∂[1] (φ : ℝ^2 → ℝ))) p) l (𝓝 0) := by
    simpa using hεlim.mul hsecond
  have hineq := le_of_tendsto_of_tendsto hsum.neg hz (by
    filter_upwards [hε, hu, hpde] with i hiε hiu hipde using
      E.neg_integral_entropyWeakIntegrand_le hiε hiu hipde φ hφ)
  linarith

end PDE.Hyperbolic.ConservationLaw.System
