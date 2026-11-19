/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.EnergyLimit
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.LipschitzEnergy
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Cutoff
import PDE.DistributionTheory.TestFunction.CompactCutoff

/-!
# Physical energy of local strong, globally weak limits

Spatial cutoff convergence yields almost-everywhere subsequences on each compact ball. Coupled weak
lower semicontinuity and Fatou retain the full energy budget on that ball. Exhaustion then proves
global integrability of the original potential and the physical-energy inequality, without a growth
restriction. This is the energy inequality (3) of Theorem 1 of Evans, §12.3.1, obtained as in step 6
of its proof from lower semicontinuity and Fatou's lemma.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.1, Theorem 1, equation (3), and step 6 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Topology InnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert Distributions
open PDE.Analysis (primitive continuous_primitive)

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- The bilinear form for half the sum of gradient and kinetic energies. -/
def quadraticEnergyForm (n : ℕ) :
    (H¹(ℝ^n) × DerivLp n 2 univ) →L[ℝ] StrongDual ℝ (H¹(ℝ^n) × DerivLp n 2 univ) :=
  (1 / 2 : ℝ) •
    ((gradientForm n).bilinearComp (ContinuousLinearMap.fst _ _ _)
      (ContinuousLinearMap.fst _ _ _) +
    (innerSL ℝ).bilinearComp (ContinuousLinearMap.snd _ _ _)
      (ContinuousLinearMap.snd _ _ _))

/-- The diagonal is the quadratic part of the massless physical energy. -/
theorem quadraticEnergyForm_self {n : ℕ} (z : H¹(ℝ^n) × DerivLp n 2 univ) :
    quadraticEnergyForm n z z = (1 / 2 : ℝ) * (gradientForm n z.1 z.1 + ‖z.2‖ ^ 2) := by
  change (1 / 2 : ℝ) * (gradientForm n z.1 z.1 + inner ℝ z.2 z.2) = _
  rw [real_inner_self_eq_norm_sq]

/-- The quadratic energy form is symmetric. -/
theorem quadraticEnergyForm_symmetric {n : ℕ} (z w : H¹(ℝ^n) × DerivLp n 2 univ) :
    quadraticEnergyForm n z w = quadraticEnergyForm n w z := by
  change (1 / 2 : ℝ) * (gradientForm n z.1 w.1 + inner ℝ z.2 w.2) =
    (1 / 2 : ℝ) * (gradientForm n w.1 z.1 + inner ℝ w.2 z.2)
  simp only [gradientForm_apply, real_inner_comm w.2 z.2]
  congr 2
  exact Finset.sum_congr rfl fun i _ ↦ real_inner_comm _ _

/-- Positivity does not require a Poincaré inequality on the whole space. -/
theorem quadraticEnergyForm_nonneg {n : ℕ} (z : H¹(ℝ^n) × DerivLp n 2 univ) :
    0 ≤ quadraticEnergyForm n z z := by
  rw [quadraticEnergyForm_self]
  exact mul_nonneg (by norm_num)
    (add_nonneg (General.Nonlinearity.gradientForm_nonneg z.1) (sq_nonneg _))

/-- Weak convergence of both energy variables and strong spatial-cutoff
convergence retain the full physical-energy bound of expanding sign-preserving
truncations. Integrability of the original potential is proved in the conclusion. -/
theorem physicalEnergy_le_of_truncated_weak_local_limit {n : ℕ} {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ}
    {K : ℕ → NNReal} (hf : Continuous f) (hs : ∀ z, 0 ≤ z * f z)
    (hg : ∀ i, LipschitzWith (K i) (g i)) (hsg : ∀ i z, 0 ≤ z * g i z) {r : ℕ → ℝ}
    (hagree : ∀ i, EqOn (g i) f (Metric.closedBall 0 (r i))) (hr : Tendsto r atTop atTop)
    {u : ℕ → H¹(ℝ^n) × DerivLp n 2 univ} {z : H¹(ℝ^n) × DerivLp n 2 univ}
    (hq : ∀ ell : StrongDual ℝ H¹(ℝ^n), Tendsto (fun i ↦ ell (u i).1) atTop (𝓝 (ell z.1)))
    (hv : ∀ ell : StrongDual ℝ (DerivLp n 2 univ),
      Tendsto (fun i ↦ ell (u i).2) atTop (𝓝 (ell z.2)))
    (hcut : ∀ χ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^n)), ℝ), Tendsto
      (fun i ↦ (energyTriple n).inclusion (cutoffCLM χ (u i).1)) atTop
      (𝓝 ((energyTriple n).inclusion (cutoffCLM χ z.1))))
    {E : ℝ} (he : ∀ i, physicalEnergy (g i) (u i) ≤ E) :
    Integrable (fun y ↦ primitive f ((energyTriple n).inclusion z.1 y))
      (domainMeasure n univ) ∧ physicalEnergy f z ≤ E := by
  have hweak (ell : StrongDual ℝ (H¹(ℝ^n) × DerivLp n 2 univ)) :
      Tendsto (fun i ↦ ell (u i)) atTop (𝓝 (ell z)) := by
    have h := (hq (ell.comp (ContinuousLinearMap.inl _ _ _))).add
      (hv (ell.comp (ContinuousLinearMap.inr _ _ _)))
    change Tendsto (fun i ↦ ell ((u i).1, 0) + ell (0, (u i).2)) atTop
      (𝓝 (ell (z.1, 0) + ell (0, z.2))) at h
    simpa only [← map_add, Prod.mk_add_mk, add_zero, zero_add] using h
  have hFi (i : ℕ) := integrable_potential_of_lipschitz (hg i)
    (reaction_zero (hg i).continuous (hsg i)) ((energyTriple n).inclusion (u i).1)
  have hlocal (s : Set (ℝ^n)) (hscompact : IsCompact s) :
      Integrable (fun y ↦ primitive f ((energyTriple n).inclusion z.1 y))
        ((domainMeasure n univ).restrict s) ∧
      (∫ y in s, primitive f ((energyTriple n).inclusion z.1 y) ∂domainMeasure n univ)
        ≤ E - quadraticEnergyForm n z z := by
    obtain ⟨χ, _, hχ, _, _⟩ :=
      TestFunction.exists_eq_one_on_compact isOpen_univ hscompact (subset_univ s)
    obtain ⟨κ, hκ, hae⟩ := (tendstoInMeasure_of_tendsto_Lp (hcut χ)).exists_seq_tendsto_ae
    have huc : ∀ᵐ y ∂domainMeasure n univ, ∀ i : ℕ,
        (energyTriple n).inclusion (cutoffCLM χ (u (κ i)).1) y =
          χ.toFun y * (energyTriple n).inclusion (u (κ i)).1 y :=
      ae_all_iff.mpr fun i ↦ cutoffCLM_base_apply_ae χ (u (κ i)).1
    have hvc : ∀ᵐ y ∂domainMeasure n univ, (energyTriple n).inclusion (cutoffCLM χ z.1) y =
          χ.toFun y * (energyTriple n).inclusion z.1 y := cutoffCLM_base_apply_ae χ z.1
    have hpoint : ∀ᵐ y ∂(domainMeasure n univ).restrict s,
        Tendsto (fun i ↦ (energyTriple n).inclusion (u (κ i)).1 y) atTop
          (𝓝 ((energyTriple n).inclusion z.1 y)) := by
      filter_upwards [hae.filter_mono (ae_mono Measure.restrict_le_self),
        huc.filter_mono (ae_mono Measure.restrict_le_self),
        hvc.filter_mono (ae_mono Measure.restrict_le_self),
        ae_restrict_mem hscompact.measurableSet] with y hy hiy hzy hys
      simpa only [hiy, hzy, hχ y hys, one_mul] using hy
    have henergy := quadratic_add_integral_le_of_weak_ae_limit (quadraticEnergyForm n)
      quadraticEnergyForm_symmetric quadraticEnergyForm_nonneg
      (fun ell ↦ (hweak ell).comp hκ.tendsto_atTop)
      (fun i ↦ (hFi (κ i)).mono_measure Measure.restrict_le_self)
      (fun i ↦ Eventually.of_forall fun y ↦ primitive_nonneg (hg (κ i)).continuous (hsg (κ i)) _)
      (C := E) (G := fun y ↦ primitive f ((energyTriple n).inclusion z.1 y))
      (fun i ↦ by
        calc
          _ ≤ quadraticEnergyForm n (u (κ i)) (u (κ i)) +
              ∫ y, primitive (g (κ i)) ((energyTriple n).inclusion (u (κ i)).1 y)
                ∂domainMeasure n univ := add_le_add le_rfl (setIntegral_le_integral (hFi (κ i))
              (Eventually.of_forall fun y ↦ primitive_nonneg (hg (κ i)).continuous (hsg (κ i)) _))
          _ = physicalEnergy (g (κ i)) (u (κ i)) := by
            rw [quadraticEnergyForm_self, physicalEnergy]
          _ ≤ E := he (κ i))
      (by
        filter_upwards [hpoint] with y hy
        exact tendsto_reaction_of_expanding_agreement (continuous_primitive hf)
          (fun i ↦ potential_eqOn_of_eqOn_closedBall (hagree (κ i))) (hr.comp hκ.tendsto_atTop) hy)
    exact ⟨henergy.1, by linarith [henergy.2]⟩
  have hglobal := integrable_and_integral_le_of_exhaustion
    (s := fun i : ℕ ↦ Metric.closedBall (0 : ℝ^n) i)
    (fun i j hij ↦ Metric.closedBall_subset_closedBall (Nat.cast_le.mpr hij))
    (Metric.iUnion_closedBall_nat (0 : ℝ^n)) ((continuous_primitive hf).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable ((energyTriple n).inclusion z.1)))
    (Eventually.of_forall fun y ↦ primitive_nonneg hf hs _)
    (fun i ↦ (hlocal _ (isCompact_closedBall _ _)).1)
    (fun i ↦ (hlocal _ (isCompact_closedBall _ _)).2)
  refine ⟨hglobal.1, ?_⟩
  change (1 / 2 : ℝ) * (gradientForm n z.1 z.1 + ‖z.2‖ ^ 2) + _ ≤ E
  rw [← quadraticEnergyForm_self]
  linarith [hglobal.2]

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
