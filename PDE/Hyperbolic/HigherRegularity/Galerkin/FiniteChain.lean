/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Basic
public import PDE.Hyperbolic.WeakWave.Galerkin.BochnerRealization
import PDE.Hyperbolic.Variational.GelfandGalerkin.FiniteTimeDerivative.Approximation
import PDE.Hyperbolic.Variational.GelfandGalerkin.FiniteTimeDerivative.Compactness
import PDE.Hyperbolic.Variational.GelfandGalerkin.FiniteTimeDerivative.UniformBounds

/-!
# Evans's finite differentiated Galerkin chain

We compose the construction, uniform-energy, and compactness stages
of Evans Section 7.2.3. Compatible ambient initial data and a coherent
forcing chain generate finite-dimensional differentiated trajectories; the
energy estimate supplies dimension-independent bounds; one common weak
limit then gives the complete ambient weak-wave chain.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, proofs of Theorems 5(ii) and 6.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.Variational.GelfandGalerkin

open PDE.Analysis.Evolution
open scoped ENNReal

/--
Evans Section 7.2.3: construction through compactness.

The assumptions are the basis-free compatibility equations for the finite
ambient initial jet, Ritz orthogonality of the trial projections, and the
common structural hypotheses used in the wave-energy estimate. The
Galerkin trajectories and all three bounded approximation families are
constructed in the proof.
-/
theorem exists_finiteWeakWaveChain_of_compatibleData {m : ℕ} {V H : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {a b : ℝ} (T : GelfandTriple (V := V) (H := H)) (A : V →L[ℝ] StrongDual ℝ V)
    (Sseq : ℕ → Submodule ℝ V) [hfinite : ∀ k, FiniteDimensional ℝ (Sseq k)]
    {K : NNReal}
    (P : ∀ k, StableTrialProjection T (Sseq k) K)
    (hdenseEnergy : ∀ v : V, ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ k in Filter.atTop, ∃ w : Sseq k,
      ‖v - (w : V)‖ < epsilon)
    (hdensePivot : ∀ h : H, ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ k in Filter.atTop, ∃ w : Sseq k,
      ‖h - T.inclusion (w : V)‖ < epsilon)
    (dualForcing : Fin (m + 1) → ℝ → StrongDual ℝ V) (pivotForcing : Fin (m + 1) → ℝ → H)
    (ell : Fin (m + 1) → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (hEll : ∀ r : Fin (m + 1),
      (ell r : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Set.Ioc a b)] dualForcing r)
    (q : Fin (m + 1) → V) (p : Fin (m + 1) → H) (hab : a < b)
    (MA : NNReal)
    (hAbound : ∀ t ∈ Set.Icc a b, ‖A‖ ≤ MA)
    (hforcingIntegrable : IntegrableOn (dualForcing (Fin.last m)) (Set.Icc a b) volume)
    (hforcingAC : ∀ r : Fin m, AbsolutelyContinuousOnInterval (dualForcing r.succ) a b)
    (hforcingDeriv : ∀ r : Fin m, ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
      HasDerivAt (dualForcing r.succ) (dualForcing r.castSucc t) t)
    (hadjacent : ∀ r : Fin m, p r.succ = T.inclusion (q r.castSucc))
    (hcompatibility : ∀ r : Fin m, dualForcing r.succ a - A (q r.succ) =
      T.pivotToDual (p r.castSucc))
    (hRitz : ∀ k, ∀ r : Fin m, ∀ w : Sseq k,
      A (q r.succ - ((P k).energyProjection (q r.succ) : V)) (w : V) = 0)
    (hdualForcing : ∀ r : Fin (m + 1), ∀ᵐ t ∂volume.restrict (Set.Ioc a b), dualForcing r t =
      T.pivotToDual (pivotForcing r t))
    (hforcingSq : ∀ r : Fin (m + 1),
      IntervalIntegrable (fun t ↦ (1 / 2 : ℝ) * ‖pivotForcing r t‖ ^ 2) volume a b)
    (G c : ℝ)
    (hforcingBudget : ∀ r : Fin (m + 1), ∀ t ∈ Set.Icc a b,
      (∫ s in a..t, (1 / 2 : ℝ) * ‖pivotForcing r s‖ ^ 2) ≤ G)
    (hc : 0 < c) (hA_symmetric : ∀ v w : V, A v w = A w v)
    (hcoercive : ∀ v : V, c * ‖v‖ ^ 2 ≤ A v v) :
    ∃ (u : Fin (m + 1) →
          Lp V 2 (volume.restrict (Set.Ioc a b)))
        (velocity : Fin (m + 1) →
          Lp H 2 (volume.restrict (Set.Ioc a b)))
        (acceleration : Fin (m + 1) →
          Lp (StrongDual ℝ V) 2
            (volume.restrict (Set.Ioc a b))),
      (∀ r : Fin (m + 1),
        Hyperbolic.Variational.IsGelfandWeakWaveSolution
          T (fun _ ↦ A) (ell r)
          (u r) (velocity r) (acceleration r) (q r) (p r)) ∧
      (∀ r : Fin m,
        T.inclusion.compLpL 2 (volume.restrict (Set.Ioc a b))
            (u r.castSucc) =
          velocity r.succ) ∧
      (∀ r : Fin m,
        T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b))
            (velocity r.castSucc) =
          acceleration r.succ) ∧
      MemLp (fun t ↦ u (0 : Fin (m + 1)) t) (⊤ : ENNReal)
        (volume.restrict (Set.Ioc a b)) ∧
      MemLp (fun t ↦ velocity (0 : Fin (m + 1)) t) (⊤ : ENNReal)
        (volume.restrict (Set.Ioc a b)) := by
  have hAmeas : AEStronglyMeasurable (fun _ : ℝ ↦ A) (volume.restrict (Set.Icc a b)) := by fun_prop
  let : NormedAddCommGroup (StrongDual ℝ V) :=
    ContinuousLinearMap.toNormedAddCommGroup (E := V) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
  obtain ⟨_Uoriginal, q0, p0, U, _hUoriginal, hinitial, hderivative⟩ :=
    exists_finiteTimeDerivativeApproximation T Sseq P (A + 0) dualForcing hab.le
      hforcingIntegrable MA
      (by simpa only [add_zero] using hAbound) hforcingAC hforcingDeriv q p hadjacent
      (fun r ↦ by simpa only [add_zero] using hcompatibility r)
      (fun k r w ↦ by simpa only [add_zero] using hRitz k r w)
  let energyBound : ℝ :=
    ((∑ j : Fin (m + 1), ((1 / 2 : ℝ) * ‖p j‖ ^ 2 + (1 / 2 : ℝ) * ‖A‖ * (K * ‖q j‖) ^ 2)) + G) *
      Real.exp ((2 + (0 : ℝ) ^ 2 / c) * (b - a))
  let displacementSqBound : ℝ := ((2 / c) * energyBound) * (b - a)
  have hG : 0 ≤ G := by simpa using hforcingBudget (Fin.last m) a ⟨le_rfl, hab.le⟩
  have henergyBound : 0 ≤ energyBound := by positivity
  have huniform (k : ℕ) :=
    finiteTimeDerivativeFamily_uniformBounds T (Sseq k) (P k) A (0 : V →L[ℝ] StrongDual ℝ V)
      dualForcing pivotForcing q p (q0 k) (p0 k) (U k) (hinitial k) hab.le hdualForcing
      hforcingSq G c 0 hforcingBudget hc hA_symmetric hcoercive (fun v w ↦ by simp)
  have hAmeasIoc : AEStronglyMeasurable (fun _ : ℝ ↦ A + 0) (volume.restrict (Set.Ioc a b)) :=
    aestronglyMeasurable_const
  have hAboundIoc : ∀ᵐ _t ∂volume.restrict (Set.Ioc a b), ‖A + 0‖ ≤ (MA : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [add_zero] using hAbound t (Set.Ioc_subset_Icc_self ht)
  have huNorm (r : Fin (m + 1)) (k : ℕ) :
      ‖(U k r).displacementLp hab.le‖ ≤ Real.sqrt displacementSqBound :=
    Real.le_sqrt_of_sq_le ((huniform k).2.2.2.1 r)
  obtain ⟨u, velocity, acceleration, hwave, hdisplacementLink, haccelerationLink, huTop,
      hvelocityTop, -, -⟩ :=
    exists_finiteWeakWaveChain_of_bounded_finiteTimeDerivativeFamily T (fun _ : ℝ ↦ A + 0)
      hAmeasIoc (MA : ℝ) MA.2 hAboundIoc P
      (StableTrialProjection.tendsto_energyProjection_of_eventually_approximable P hdenseEnergy)
      dualForcing ell hEll q0 p0 U hab q p
      (fun r ↦ (StableTrialProjection.tendsto_energyProjection_of_eventually_approximable P
        hdenseEnergy (q r)).congr fun k ↦ congrArg Subtype.val (hinitial k r).1.symm)
      (fun r ↦ (StableTrialProjection.tendsto_inclusion_projection_of_eventually_approximable P
        hdensePivot (p r)).congr fun k ↦ by rw [(hinitial k r).2])
      (fun r ↦ isBounded_range_of_norm_sq_le _ (C := displacementSqBound) (by positivity)
        fun k ↦ (huniform k).2.2.2.1 r)
      (fun r ↦ isBounded_range_of_norm_sq_le (C := (2 * energyBound) * (b - a)) _
        (by positivity) fun k ↦ (huniform k).2.2.2.2 r)
      (fun r ↦ isBounded_iff_forall_norm_le.2 ⟨K * (‖ell r‖ + MA * Real.sqrt displacementSqBound),
        Set.forall_mem_range.2 fun k ↦
        ((U k r).norm_accelerationLp_le_stable (P k) hab.le (ell r) hAmeasIoc MA.2
          hAboundIoc).trans (mul_le_mul_of_nonneg_left
            (add_le_add le_rfl (mul_le_mul_of_nonneg_left (huNorm r k) MA.2)) K.2)⟩)
      (fun _ ↦ Real.sqrt displacementSqBound) huNorm (Real.sqrt ((2 / c) * energyBound))
      (Real.sqrt (2 * energyBound)) (fun k ↦ (huniform k).2.1 0)
      (fun k ↦ (huniform k).2.2.1 0) (fun r k ↦ (hderivative k r).2.2.2.1)
      (fun r k ↦ (hderivative k r).2.2.2.2)
  exact ⟨u, velocity, acceleration, by simpa only [add_zero] using hwave, hdisplacementLink,
    haccelerationLink, huTop, hvelocityTop⟩

end Hyperbolic.Variational.GelfandGalerkin
