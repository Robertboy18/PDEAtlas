/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.EllipticInduction.SpatialLift
import PDE.Hyperbolic.HigherRegularity.EllipticInduction.InductionStep
import PDE.Hyperbolic.HigherRegularity.EllipticInduction.OrderOneTimeJet

/-!
# Finite differentiated-wave induction

Evans proves higher regularity for the wave equation (Evans, §7.2.3,
Theorem 6) by induction on the number of time derivatives: the differentiated
equation `(u_t)_tt + L(u_t) = f_t` is handled by the induction hypothesis, and
the original equation, rewritten as the elliptic problem `Lu = f - u_tt`,
then gains two spatial derivatives.  We assemble the spatial
induction step of `EllipticInduction.InductionStep` over a finite chain
of autonomous weak waves.  Starting from the most differentiated wave, for
which only `L∞_t H¹₀` and `L∞_t L²` bounds are needed, it constructs the full
Sobolev time jet for the original displacement.

## Main results

* `exists_sobolevTimeJet_of_finiteWeakWaveChain`: from `m + 1` weak waves
  indexed in reverse derivative order (`Fin.last m` is the original equation),
  linked by the adjacent velocity and acceleration identities and with `L∞`
  bounds at index `0`, produce an essentially bounded order-`m + 1` Sobolev
  time jet whose head represents the original displacement and whose first
  derivative is the original velocity.  The elliptic input is
  `HasHigherSolutionLift` at every order `r < m` for the coercive Dirichlet
  solution operator of `A`.

## Implementation notes

The induction is on `m`.  The step restricts every family along `castSucc`,
applies the hypothesis to the differentiated chain, and identifies the head
and first derivative of the resulting jet with the original velocity and
acceleration through the link identities, so that the original weak wave is
in the form required by
`exists_spatialHigherTop_of_weakWave_induction`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorem 6 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory

namespace Hyperbolic

namespace HigherRegularity

open SobolevSpace
open SobolevSpace.GraphSpace
open PDE.Analysis.Evolution
open PDE.Analysis.Variational
open scoped ENNReal

variable {n m : ℕ} {Omega : Set (ℝ^n)} {t0 t1 : ℝ}

/--
Evans, §7.2.3, Theorem 6: finite differentiated-wave induction.

Index a finite autonomous weak-wave chain in reverse derivative order:
index `0` is the most differentiated wave and `Fin.last m` is the original
wave.  Each successor wave has the previous displacement as its velocity and
the previous pivot velocity as its acceleration.  The forcing at index `r`
is supplied with the exact order-`r` Sobolev time jet needed by the spatial
induction step.

Starting from the `L∞` bounds on the most differentiated displacement and
velocity, this theorem constructs the full order-`m+1` solution jet.  Every
adjacent entry is a proved weak time derivative, every entry has its Evans
essential bound, the top spatial representative is identified with the
original weak displacement, and its first derivative is the original pivot
velocity.
-/
theorem exists_sobolevTimeJet_of_finiteWeakWaveChain (ht : t0 < t1) (hOmegaOpen : IsOpen Omega)
    (A : H¹₀(Omega) →L[ℝ] StrongDual ℝ (H¹₀(Omega)))
    (hA : @IsCoercive (H¹₀(Omega)) inferInstance inferInstance A)
    (hreg : ∀ r : Fin m, HasHigherSolutionLift (n := n) (Omega := Omega) r.1
      (coerciveDirichletSolutionOperator A hA))
    (forcing : (r : Fin (m + 1)) → SobolevTimeJet n r.1 Omega t0 t1)
    (u : Fin (m + 1) → Lp (H¹₀(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (velocity : Fin (m + 1) → Lp (DerivLp n 2 Omega) 2 (volume.restrict (Set.Ioc t0 t1)))
    (acceleration : Fin (m + 1) →
      Lp (StrongDual ℝ (H¹₀(Omega))) 2 (volume.restrict (Set.Ioc t0 t1)))
    (q0 : Fin (m + 1) → H¹₀(Omega)) (p0 : Fin (m + 1) → DerivLp n 2 Omega)
    (hWave : ∀ r : Fin (m + 1), Hyperbolic.Variational.IsGelfandWeakWaveSolution
      (SobolevSpace.GraphSpace.h10L2GelfandTriple hOmegaOpen) (fun _ ↦ A)
      (dirichletLoadTimeLp hOmegaOpen (forcing r).head) (u r) (velocity r) (acceleration r) (q0 r)
      (p0 r))
    (hvelocityLink : ∀ r : Fin m, (fun t ↦ (SobolevSpace.GraphSpace.h10L2GelfandTriple
      hOmegaOpen).inclusion ((u r.castSucc : ℝ → H¹₀(Omega)) t))
      =ᵐ[(volume.restrict (Set.Ioc t0 t1))] fun t ↦ (velocity r.succ : ℝ → DerivLp n 2 Omega) t)
    (haccelerationLink : ∀ r : Fin m, (fun t ↦ (SobolevSpace.GraphSpace.h10L2GelfandTriple
      hOmegaOpen).pivotToDual ((velocity r.castSucc : ℝ → DerivLp n 2 Omega) t))
      =ᵐ[(volume.restrict (Set.Ioc t0 t1))] fun t ↦
      (acceleration r.succ : ℝ → StrongDual ℝ (H¹₀(Omega))) t)
    (huTop : MemLp (fun t ↦ (u (0 : Fin (m + 1)) : ℝ → H¹₀(Omega)) t) (⊤ : ℝ≥0∞)
      (volume.restrict (Set.Ioc t0 t1)))
    (hvelocityTop : MemLp (fun t ↦ (velocity (0 : Fin (m + 1)) : ℝ → DerivLp n 2 Omega) t)
      (⊤ : ℝ≥0∞) (volume.restrict (Set.Ioc t0 t1))) :
    ∃ solution : SobolevTimeJet n (m + 1) Omega t0 t1,
      ((fun t ↦ wkpBaseCoordinateCLM (n := n) (m := m + 1) (p := 2) (Ω := Omega)
            ((solution.head : ℝ → W^{(m + 1),2}(Omega)) t))
        =ᵐ[(volume.restrict (Set.Ioc t0 t1))]
        fun t ↦ wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Omega)
          (h10SubtypeL (n := n) (Ω := Omega) ((u (Fin.last m) : ℝ → H¹₀(Omega)) t))) ∧
      baseCoordinateTimeLp solution.timeDerivative.head = velocity (Fin.last m) ∧
      solution.IsEssentiallyBounded := by
  induction m with
  | zero =>
    exact exists_orderOneSobolevTimeJet_of_weakWave hOmegaOpen (fun _ ↦ A) _ (u 0) (velocity 0)
      (acceleration 0) (q0 0) (p0 0) (hWave 0) huTop hvelocityTop
  | succ m ih =>
    obtain ⟨duJet, hduBase, hdvelocityBase, hduTop⟩ := ih (hreg := fun r ↦ hreg r.castSucc)
      (forcing := fun r ↦ forcing r.castSucc) (u := fun r ↦ u r.castSucc)
      (velocity := fun r ↦ velocity r.castSucc) (acceleration := fun r ↦ acceleration r.castSucc)
      (q0 := fun r ↦ q0 r.castSucc) (p0 := fun r ↦ p0 r.castSucc)
      (hWave := fun r ↦ hWave r.castSucc)
      (hvelocityLink := fun r ↦ by simpa using hvelocityLink r.castSucc)
      (haccelerationLink := fun r ↦ by simpa using haccelerationLink r.castSucc)
      (huTop := by simpa using huTop) (hvelocityTop := by simpa using hvelocityTop)
    have hvelocityEq : baseCoordinateTimeLp duJet.head = velocity (Fin.last (m + 1)) := by
      refine Lp.ext ?_
      filter_upwards [baseCoordinateTimeLp_apply_ae duJet.head, hduBase,
        hvelocityLink (Fin.last m)] with t hbase hdu hvelocity
      rw [hbase, hdu]
      exact hvelocity
    have haccelerationEq : dirichletLoadTimeLp hOmegaOpen duJet.timeDerivative.head =
        acceleration (Fin.last (m + 1)) := by
      refine Lp.ext ?_
      filter_upwards [dirichletLoadTimeLp_apply_ae hOmegaOpen duJet.timeDerivative.head,
        baseCoordinateTimeLp_apply_ae duJet.timeDerivative.head,
        haccelerationLink (Fin.last m)] with t hload hbase hacceleration
      rw [hload]
      change (SobolevSpace.GraphSpace.h10L2GelfandTriple hOmegaOpen).pivotToDual
          (wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega)
            (duJet.timeDerivative.head t)) = acceleration (Fin.last (m + 1)) t
      rw [← hbase, hdvelocityBase]
      exact hacceleration
    have hOriginal := hWave (Fin.last (m + 1))
    rw [← hvelocityEq, ← haccelerationEq] at hOriginal
    obtain ⟨_, _, solution, hsolutionDerivative, _, _, hsolutionBase, hsolutionRegularity, _⟩ :=
      exists_spatialHigherTop_of_weakWave_induction (m := m) ht hOmegaOpen A hA
        (hreg (Fin.last m)) (forcing (Fin.last (m + 1))) duJet hduTop (u (Fin.last (m + 1)))
        (q0 (Fin.last (m + 1))) (p0 (Fin.last (m + 1))) hOriginal
    exact ⟨solution, hsolutionBase, hsolutionDerivative ▸ hvelocityEq, hsolutionRegularity⟩

end HigherRegularity

end Hyperbolic
