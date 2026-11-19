/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Basic
import PDE.Hyperbolic.Variational.GelfandGalerkin.FiniteTimeDerivative.Approximation
import PDE.Hyperbolic.Variational.GelfandGalerkin.FiniteTimeDerivative.Compactness
import PDE.Hyperbolic.Variational.GelfandGalerkin.FiniteTimeDerivative.UniformBounds
public import PDE.Hyperbolic.WeakWave.Galerkin.BochnerRealization

/-!
# Higher wave regularity with nonsymmetric lower-order terms

Evans, §7.2.3, proves higher time regularity for the wave equation by differentiating the
finite-dimensional Galerkin equations and applying one dimension-independent
energy estimate at every derivative level.  The spatial operator need not be
symmetric: in the energy estimate Evans separates it into a symmetric uniformly elliptic
principal part and a bounded lower-order remainder (§7.2.2, equations (22)-(24)).

We carry that decomposition through the complete differentiated
Galerkin construction and compactness passage.  For

`B = A + R`,

only `A` is assumed symmetric and coercive.  The remainder satisfies the
mixed energy bound

`|R v w| <= L_R * ‖v‖_V * ‖J w‖_H`,

which is the estimate used to absorb lower-order work by Young's
inequality and Grönwall's lemma.  The conclusion is a finite chain of weak
waves for the full, generally nonsymmetric operator `A + R`, together with
the adjacent time-derivative identities and essential bounds for the base
displacement and velocity.

The construction also assumes Ritz orthogonality for the full operator
`A + R` on the initial jet entries used in the compatibility recurrence.
The stable pivot projections need not satisfy this condition automatically;
Ritz orthogonality for `A` alone does not suffice. Density gives convergence
of the projected initial data once these compatibility conditions hold.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, proof of Theorem 2, equations (20)-(25), and §7.2.3,
  proof of Theorem 5, step 2, equations (53)-(55).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.Variational.GelfandGalerkin

open PDE.Analysis.Evolution
open scoped ENNReal

/--
Evans Section 7.2.3: differentiated Galerkin limit with bounded
nonsymmetric lower-order terms.

Let the autonomous wave operator split as `B = A + R`.  The principal part
`A` is symmetric and coercive on the energy space, while `R` is allowed to
be nonsymmetric and is controlled in the mixed `V x H` norm. Stable dense
trial projections, compatible ambient initial data, a coherent forcing chain,
and the uniform forcing budget generate a finite chain of ambient weak-wave
solutions for the full operator `A + R`, provided `hRitz` holds:

`(A + R) (q r.succ - P_k (q r.succ)) w = 0`

for every trial level `k`, adjacent jet index `r`, and test `w` in that trial
space. Here `P_k` is the restriction of the stable pivot projection to `V`.
This full-operator condition is separate from stability and density.

All finite-dimensional trajectories, their uniform bounds, and their common
weak limit are constructed in the proof.  In particular, no limiting weak
wave or higher-regularity conclusion is included among the hypotheses.
-/
theorem exists_finiteWeakWaveChain_of_compatibleData_nonsymmetric {m : ℕ} {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {a b : ℝ} (T : GelfandTriple (V := V) (H := H))
    (A R : V →L[ℝ] StrongDual ℝ V) (Sseq : ℕ → Submodule ℝ V)
    [hfinite : ∀ k, FiniteDimensional ℝ (Sseq k)]
    {K : NNReal} (P : ∀ k, StableTrialProjection T (Sseq k) K)
    (hdenseEnergy : ∀ v : V, ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ k in Filter.atTop, ∃ w : Sseq k,
      ‖v - (w : V)‖ < epsilon)
    (hdensePivot : ∀ h : H, ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ k in Filter.atTop, ∃ w : Sseq k,
      ‖h - T.inclusion (w : V)‖ < epsilon)
    (dualForcing : Fin (m + 1) → ℝ → StrongDual ℝ V) (pivotForcing : Fin (m + 1) → ℝ → H)
    (ell : Fin (m + 1) → Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)))
    (hEll : ∀ r : Fin (m + 1),
      (ell r : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Set.Ioc a b)] dualForcing r)
    (q : Fin (m + 1) → V) (p : Fin (m + 1) → H) (hab : a < b)
    (hforcingIntegrable : IntegrableOn (dualForcing (Fin.last m)) (Set.Icc a b) volume)
    (hforcingAC : ∀ r : Fin m, AbsolutelyContinuousOnInterval (dualForcing r.succ) a b)
    (hforcingDeriv : ∀ r : Fin m, ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
      HasDerivAt (dualForcing r.succ) (dualForcing r.castSucc t) t)
    (hadjacent : ∀ r : Fin m, p r.succ = T.inclusion (q r.castSucc))
    (hcompatibility : ∀ r : Fin m, dualForcing r.succ a - (A + R) (q r.succ) =
      T.pivotToDual (p r.castSucc))
    (hRitz : ∀ k, ∀ r : Fin m, ∀ w : Sseq k,
      (A + R) (q r.succ - ((P k).energyProjection (q r.succ) : V)) (w : V) = 0)
    (hdualForcing : ∀ r : Fin (m + 1), ∀ᵐ t ∂volume.restrict (Set.Ioc a b), dualForcing r t =
      T.pivotToDual (pivotForcing r t))
    (hforcingSq : ∀ r : Fin (m + 1),
      IntervalIntegrable (fun t ↦ (1 / 2 : ℝ) * ‖pivotForcing r t‖ ^ 2) volume a b)
    (G c LR : ℝ)
    (hforcingBudget : ∀ r : Fin (m + 1), ∀ t ∈ Set.Icc a b,
      (∫ s in a..t, (1 / 2 : ℝ) * ‖pivotForcing r s‖ ^ 2) ≤ G)
    (hc : 0 < c) (hA_symmetric : ∀ v w : V, A v w = A w v)
    (hcoercive : ∀ v : V, c * ‖v‖ ^ 2 ≤ A v v)
    (hRbound : ∀ v w : V, |R v w| ≤ LR * ‖v‖ * ‖T.inclusion w‖) :
    ∃ (u : Fin (m + 1) →
          Lp V 2 (volume.restrict (Set.Ioc a b)))
        (velocity : Fin (m + 1) →
          Lp H 2 (volume.restrict (Set.Ioc a b)))
        (acceleration : Fin (m + 1) →
          Lp (StrongDual ℝ V) 2
            (volume.restrict (Set.Ioc a b))),
      (∀ r : Fin (m + 1),
        Hyperbolic.Variational.IsGelfandWeakWaveSolution
          T (fun _ ↦ A + R) (ell r)
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
        (volume.restrict (Set.Ioc a b)) ∧
      ∃ E : ℝ,
        E =
          ((∑ j : Fin (m + 1),
              ((1 / 2 : ℝ) * ‖p j‖ ^ 2 +
                (1 / 2 : ℝ) * ‖A‖ * (K * ‖q j‖) ^ 2)) + G) *
            Real.exp ((2 + LR ^ 2 / c) * (b - a)) ∧
        (∀ᵐ t ∂volume.restrict (Set.Ioc a b),
          ‖u (0 : Fin (m + 1)) t‖ ≤ Real.sqrt ((2 / c) * E)) ∧
        (∀ᵐ t ∂volume.restrict (Set.Ioc a b),
          ‖velocity (0 : Fin (m + 1)) t‖ ≤ Real.sqrt (2 * E)) := by
  let B : V →L[ℝ] StrongDual ℝ V := A + R
  let MB : NNReal := ⟨‖B‖, norm_nonneg B⟩
  obtain ⟨_Uoriginal, q0, p0, U, _hUoriginal, hinitial, hderivative⟩ :=
    exists_finiteTimeDerivativeApproximation T Sseq P B dualForcing hab.le
      hforcingIntegrable MB (fun _ _ ↦ le_rfl) hforcingAC
      hforcingDeriv q p hadjacent hcompatibility hRitz
  let energyBound : ℝ :=
    ((∑ j : Fin (m + 1), ((1 / 2 : ℝ) * ‖p j‖ ^ 2 + (1 / 2 : ℝ) * ‖A‖ * (K * ‖q j‖) ^ 2)) + G) *
      Real.exp ((2 + LR ^ 2 / c) * (b - a))
  let displacementSqBound : ℝ := ((2 / c) * energyBound) * (b - a)
  have hG : 0 ≤ G := by simpa using hforcingBudget (Fin.last m) a ⟨le_rfl, hab.le⟩
  have henergyBound : 0 ≤ energyBound := by positivity
  have huniform (k : ℕ) :=
    finiteTimeDerivativeFamily_uniformBounds T (Sseq k) (P k) A R dualForcing pivotForcing q p
      (q0 k) (p0 k) (U k) (hinitial k) hab.le hdualForcing hforcingSq G c LR hforcingBudget hc
      hA_symmetric hcoercive hRbound
  have hBmeasIoc : AEStronglyMeasurable (fun _ : ℝ ↦ B) (volume.restrict (Set.Ioc a b)) :=
    aestronglyMeasurable_const
  have hBboundIoc : ∀ᵐ _t ∂volume.restrict (Set.Ioc a b), ‖B‖ ≤ (MB : ℝ) :=
    .of_forall fun _ ↦ le_rfl
  have huNorm (r : Fin (m + 1)) (k : ℕ) :
      ‖(U k r).displacementLp hab.le‖ ≤ Real.sqrt displacementSqBound :=
    Real.le_sqrt_of_sq_le ((huniform k).2.2.2.1 r)
  obtain ⟨u, velocity, acceleration, hwave, hdisplacementLink, haccelerationLink, huTop,
      hvelocityTop, huBound, hvelocityBound⟩ :=
    exists_finiteWeakWaveChain_of_bounded_finiteTimeDerivativeFamily T (fun _ : ℝ ↦ B) hBmeasIoc
      (MB : ℝ) MB.2 hBboundIoc P
      (StableTrialProjection.tendsto_energyProjection_of_eventually_approximable P hdenseEnergy)
      dualForcing ell hEll q0 p0 U hab q p
      (fun r ↦ (StableTrialProjection.tendsto_energyProjection_of_eventually_approximable P
        hdenseEnergy (q r)).congr fun k ↦ congrArg Subtype.val (hinitial k r).1.symm)
      (fun r ↦ (StableTrialProjection.tendsto_inclusion_projection_of_eventually_approximable P
        hdensePivot (p r)).congr fun k ↦ by rw [(hinitial k r).2])
      (fun r ↦ isBounded_range_of_norm_sq_le _ (by positivity) fun k ↦ (huniform k).2.2.2.1 r)
      (fun r ↦ isBounded_range_of_norm_sq_le (C := (2 * energyBound) * (b - a)) _
        (by positivity) fun k ↦ (huniform k).2.2.2.2 r)
      (fun r ↦ isBounded_iff_forall_norm_le.2 ⟨K * (‖ell r‖ + MB * Real.sqrt displacementSqBound),
        Set.forall_mem_range.2 fun k ↦
        ((U k r).norm_accelerationLp_le_stable (P k) hab.le (ell r) hBmeasIoc MB.2
          hBboundIoc).trans (mul_le_mul_of_nonneg_left
            (add_le_add le_rfl (mul_le_mul_of_nonneg_left (huNorm r k) MB.2)) K.2)⟩)
      (fun _ ↦ Real.sqrt displacementSqBound) huNorm (Real.sqrt ((2 / c) * energyBound))
      (Real.sqrt (2 * energyBound)) (fun k ↦ (huniform k).2.1 0) (fun k ↦ (huniform k).2.2.1 0)
      (fun r k ↦ (hderivative k r).2.2.2.1) (fun r k ↦ (hderivative k r).2.2.2.2)
  exact ⟨u, velocity, acceleration, hwave, hdisplacementLink, haccelerationLink, huTop,
    hvelocityTop, energyBound, rfl, huBound, hvelocityBound⟩

end Hyperbolic.Variational.GelfandGalerkin
