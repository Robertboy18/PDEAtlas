/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.TrialProjection
public import PDE.Hyperbolic.HigherRegularity.Compatibility.Conditions
public import PDE.Hyperbolic.HigherRegularity.Data.Forcing
public import PDE.Hyperbolic.HigherRegularity.EllipticInduction.SpatialLift
import PDE.Hyperbolic.HigherRegularity.Data.Initial
import PDE.Hyperbolic.HigherRegularity.EllipticInduction.FiniteChain
import PDE.Hyperbolic.HigherRegularity.Galerkin.FiniteChain
import PDE.Hyperbolic.Variational.GelfandGalerkin.FiniteTimeDerivative.Energy

/-!
# Evans's higher-regularity wave existence theorem

We specialize the differentiated Galerkin limit to compatible
Sobolev wave data, then apply the finite weak-wave induction from Evans,
PDE, §7.2.3.  The result is the symmetric-coercive case of Evans's higher
regularity theorem (Theorem 6 there): compatible data `g ∈ H^{m+1}`,
`h ∈ H^m`, `∂ₜᵏ f ∈ L²_t H^{m-k}` produce a weak wave whose displacement is
represented by an essentially bounded order-`m+1` Sobolev time jet, that is,
`∂ₜᵏ u ∈ L∞_t H^{m+1-k}` for `0 ≤ k ≤ m+1`.

## Main results

* `WaveProblemData.IsCompatible.exists_finiteWeakWaveChain`: the Galerkin
  construction.  Compatible data give the differentiated chain of weak waves
  `∂ₜʳ u`, `r ≤ m`, with the prescribed initial values, the adjacent velocity
  and acceleration links, and `L∞` bounds on the most differentiated pair.
  The Dirichlet forcing representatives, compatibility values, uniform
  estimates, and common weak limit are all produced inside the proof.
* `WaveProblemData.IsCompatible.exists_regularWeakWave_of_stableGalerkinScheme`:
  the chain is fed to `exists_sobolevTimeJet_of_finiteWeakWaveChain`, giving
  the weak wave for the original data together with its Sobolev time jet.

## Implementation notes

The spatial operator `A` is assumed symmetric and coercive on `H¹₀`, and the
Galerkin scheme (stable trial projections, density, Ritz orthogonality) and
the elliptic lift `HasHigherSolutionLift` are explicit hypotheses.  Nonsymmetric
lower-order terms are treated in `Galerkin.Nonsymmetric`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorem 6 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.HigherRegularity

open PDE.Analysis.Evolution
open SobolevSpace
open SobolevSpace.GraphSpace
open scoped ENNReal

variable {n m : ℕ} {Omega : Set (ℝ^n)} {t0 t1 : ℝ}

private theorem compLpL_apply_ae_eq_of_eq
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    {mu : Measure ℝ} (L : E →L[ℝ] F) {f : Lp E 2 mu} {g : Lp F 2 mu}
    (h : L.compLpL 2 mu f = g) : (fun t ↦ L (f t)) =ᵐ[mu] fun t ↦ g t :=
  (L.coeFn_compLpL f).symm.trans <| .of_eq <| congrArg (fun z : Lp F 2 mu ↦ (z : ℝ → F)) h

/-- Witness structure for the finite differentiated weak-wave chain.

The displacement, velocity, and acceleration families share the same index and
must satisfy adjacent-link and endpoint boundedness laws. Bundling those
witnesses keeps the assembly lemma readable;
`WaveProblemData.IsCompatible.exists_finiteWeakWaveChain` states the same mathematical data as
an existential statement. -/
private structure FiniteWeakWaveChainWitness
    (D : WaveProblemData n m Omega t0 t1) (hOmegaOpen : IsOpen Omega)
    (A : H¹₀(Omega) →L[ℝ] StrongDual ℝ (H¹₀(Omega)))
    (q : Fin (m + 1) → H¹₀(Omega)) (p : Fin (m + 1) → DerivLp n 2 Omega) where
  u : Fin (m + 1) → Lp (H¹₀(Omega)) 2 (volume.restrict (Set.Ioc t0 t1))
  velocity : Fin (m + 1) → Lp (DerivLp n 2 Omega) 2 (volume.restrict (Set.Ioc t0 t1))
  acceleration : Fin (m + 1) →
    Lp (StrongDual ℝ (H¹₀(Omega))) 2 (volume.restrict (Set.Ioc t0 t1))
  wave :
    ∀ r : Fin (m + 1),
      Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hOmegaOpen) (fun _ ↦ A)
        (dirichletLoadTimeLp hOmegaOpen (D.forcing.iteratedTimeDerivative r).head)
        (u r) (velocity r) (acceleration r) (q r) (p r)
  displacementLink :
    ∀ r : Fin m,
      (fun t ↦ (h10L2GelfandTriple hOmegaOpen).inclusion ((u r.castSucc : ℝ → H¹₀(Omega)) t))
        =ᵐ[volume.restrict (Set.Ioc t0 t1)] fun t ↦ (velocity r.succ : ℝ → DerivLp n 2 Omega) t
  accelerationLink :
    ∀ r : Fin m,
      (fun t ↦ (h10L2GelfandTriple hOmegaOpen).pivotToDual
          ((velocity r.castSucc : ℝ → DerivLp n 2 Omega) t))
        =ᵐ[volume.restrict (Set.Ioc t0 t1)]
          fun t ↦ (acceleration r.succ : ℝ → StrongDual ℝ (H¹₀(Omega))) t
  displacementBound :
    MemLp (fun t ↦ (u (0 : Fin (m + 1)) : ℝ → H¹₀(Omega)) t) (⊤ : ENNReal)
      (volume.restrict (Set.Ioc t0 t1))
  velocityBound :
    MemLp (fun t ↦ (velocity (0 : Fin (m + 1)) : ℝ → DerivLp n 2 Omega) t) (⊤ : ENNReal)
      (volume.restrict (Set.Ioc t0 t1))

private theorem exists_finite_weak_wave_chain_witness (D : WaveProblemData n m Omega t0 t1)
    (hOmegaOpen : IsOpen Omega) (A : H¹₀(Omega) →L[ℝ] StrongDual ℝ (H¹₀(Omega)))
    (Sseq : ℕ → Submodule ℝ (H¹₀(Omega))) [hfinite : ∀ k, FiniteDimensional ℝ (Sseq k)]
    {c G : ℝ} {K : NNReal}
    (P : ∀ k, StableTrialProjection (h10L2GelfandTriple hOmegaOpen) (Sseq k) K)
    (hdenseEnergy : ∀ v : H¹₀(Omega), ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ k in Filter.atTop, ∃ w :
      Sseq k, ‖v - (w : H¹₀(Omega))‖ < epsilon)
    (hdensePivot : ∀ h : DerivLp n 2 Omega, ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ k in Filter.atTop, ∃ w :
      Sseq k, ‖h - (h10L2GelfandTriple hOmegaOpen).inclusion (w : H¹₀(Omega))‖ < epsilon)
    (dualForcing : Fin (m + 1) → ℝ → StrongDual ℝ (H¹₀(Omega)))
    (hforcingRepresents : ∀ r : Fin (m + 1), (dirichletLoadTimeLp hOmegaOpen
      (D.forcing.iteratedTimeDerivative r).head : ℝ → StrongDual ℝ (H¹₀(Omega)))
      =ᵐ[volume.restrict (Set.Ioc t0 t1)] dualForcing r)
    (hforcingAdjacent : ∀ r : Fin m, AbsolutelyContinuousOnInterval (dualForcing r.succ) t0 t1 ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1),
      HasDerivAt (dualForcing r.succ) (dualForcing r.castSucc t) t)
    (hforcingPivot : ∀ r : Fin (m + 1), ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1), dualForcing r t =
      (h10L2GelfandTriple hOmegaOpen).pivotToDual
      (baseCoordinateTimeLp (D.forcing.iteratedTimeDerivative r).head t))
    (hforcingSq : ∀ r : Fin (m + 1), IntervalIntegrable (fun t ↦
      (1 / 2 : ℝ) * ‖baseCoordinateTimeLp (D.forcing.iteratedTimeDerivative r).head t‖ ^ 2) volume
      t0 t1)
    (hforcingBudget : ∀ r : Fin (m + 1), ∀ t ∈ Set.Icc t0 t1,
      (∫ s in t0..t,
      (1 / 2 : ℝ) * ‖baseCoordinateTimeLp (D.forcing.iteratedTimeDerivative r).head s‖ ^ 2) ≤ G)
    (q : Fin (m + 1) → H¹₀(Omega)) (p : Fin (m + 1) → DerivLp n 2 Omega)
    (hadjacent : ∀ r : Fin m, p r.succ = (h10L2GelfandTriple hOmegaOpen).inclusion (q r.castSucc))
    (hcompatibility : ∀ r : Fin m, dualForcing r.succ t0 - A (q r.succ) =
      (h10L2GelfandTriple hOmegaOpen).pivotToDual (p r.castSucc))
    (hRitz : ∀ k, ∀ v : H¹₀(Omega), ∀ w : Sseq k,
      A (v - ((P k).energyProjection v : H¹₀(Omega))) (w : H¹₀(Omega)) = 0)
    (hc : 0 < c) (hA_symmetric : ∀ v w : H¹₀(Omega), A v w = A w v)
    (hcoercive : ∀ v : H¹₀(Omega), c * ‖v‖ ^ 2 ≤ A v v) :
    Nonempty (FiniteWeakWaveChainWitness D hOmegaOpen A q p) := by
  obtain ⟨u, velocity, acceleration, hWave, hdisplacementLink, haccelerationLink, huTop,
      hvelocityTop⟩ :=
    Hyperbolic.Variational.GelfandGalerkin.exists_finiteWeakWaveChain_of_compatibleData
      (hfinite := hfinite)
      (h10L2GelfandTriple hOmegaOpen) A Sseq P hdenseEnergy hdensePivot dualForcing
      (fun r t ↦ baseCoordinateTimeLp (D.forcing.iteratedTimeDerivative r).head t)
      (fun r ↦ dirichletLoadTimeLp hOmegaOpen (D.forcing.iteratedTimeDerivative r).head)
      hforcingRepresents q p D.time_lt
      (⟨‖A‖, norm_nonneg A⟩ : NNReal) (fun _ _ ↦ by change ‖A‖ ≤ ‖A‖; exact le_rfl)
      (D.forcing.integrableOn_dirichletLoadForcing hOmegaOpen D.time_lt.le dualForcing
        hforcingRepresents (Fin.last m))
      (fun r ↦ (hforcingAdjacent r).1) (fun r ↦ (hforcingAdjacent r).2)
      hadjacent hcompatibility (fun k r w ↦ hRitz k (q r.succ) w) hforcingPivot hforcingSq G c
      hforcingBudget hc hA_symmetric hcoercive
  exact ⟨⟨u, velocity, acceleration, hWave,
    fun r ↦ compLpL_apply_ae_eq_of_eq (h10L2GelfandTriple hOmegaOpen).inclusion
      (hdisplacementLink r),
    fun r ↦ compLpL_apply_ae_eq_of_eq (h10L2GelfandTriple hOmegaOpen).pivotToDual
      (haccelerationLink r), huTop, hvelocityTop⟩⟩

/--
Evans Section 7.2.3: compatible data produce the differentiated weak-wave
chain.

The forcing representatives, compatibility values, Galerkin trajectories,
uniform estimates, and common weak limit are all constructed in the proof.
-/
theorem WaveProblemData.IsCompatible.exists_finiteWeakWaveChain
    (D : WaveProblemData n m Omega t0 t1) (hOmegaOpen : IsOpen Omega)
    (A : H¹₀(Omega) →L[ℝ] StrongDual ℝ (H¹₀(Omega)))
    (spatialOperator : ∀ r : ℕ, W^{(r + 2),2}(Omega) →L[ℝ] W^{r,2}(Omega))
    (hD : D.IsCompatible A spatialOperator)
    (Sseq : ℕ → Submodule ℝ (H¹₀(Omega)))
    [hfinite : ∀ k, FiniteDimensional ℝ (Sseq k)]
    {c : ℝ} {K : NNReal}
    (P : ∀ k, StableTrialProjection (h10L2GelfandTriple hOmegaOpen) (Sseq k) K)
    (hdenseEnergy : ∀ v : H¹₀(Omega), ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k in Filter.atTop, ∃ w : Sseq k, ‖v - (w : H¹₀(Omega))‖ < epsilon)
    (hdensePivot : ∀ h : DerivLp n 2 Omega, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k in Filter.atTop, ∃ w : Sseq k,
        ‖h - (h10L2GelfandTriple hOmegaOpen).inclusion (w : H¹₀(Omega))‖ < epsilon)
    (hc : 0 < c) (hA_symmetric : ∀ v w : H¹₀(Omega), A v w = A w v)
    (hcoercive : ∀ v : H¹₀(Omega), c * ‖v‖ ^ 2 ≤ A v v)
    (hRitz : ∀ k, ∀ v : H¹₀(Omega), ∀ w : Sseq k,
      A (v - ((P k).energyProjection v : H¹₀(Omega))) (w : H¹₀(Omega)) = 0) :
    ∃ (q : Fin (m + 1) → H¹₀(Omega)) (p : Fin (m + 1) → DerivLp n 2 Omega)
        (u : Fin (m + 1) → Lp (H¹₀(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
        (velocity : Fin (m + 1) → Lp (DerivLp n 2 Omega) 2 (volume.restrict (Set.Ioc t0 t1)))
        (acceleration : Fin (m + 1) →
          Lp (StrongDual ℝ (H¹₀(Omega))) 2 (volume.restrict (Set.Ioc t0 t1))),
      h10SubtypeL (n := n) (Ω := Omega) (q (Fin.last m)) =
        lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (by omega : 1 ≤ m + 1) D.displacement ∧
      p (Fin.last m) = wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega) D.velocity ∧
      (∀ r : Fin m, p r.succ = (h10L2GelfandTriple hOmegaOpen).inclusion (q r.castSucc)) ∧
      (∀ r : Fin (m + 1),
      Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hOmegaOpen) (fun _ ↦ A)
        (dirichletLoadTimeLp hOmegaOpen (D.forcing.iteratedTimeDerivative r).head)
        (u r) (velocity r) (acceleration r) (q r) (p r)) ∧
      (∀ r : Fin m,
      (fun t ↦ (h10L2GelfandTriple hOmegaOpen).inclusion ((u r.castSucc : ℝ → H¹₀(Omega)) t))
        =ᵐ[volume.restrict (Set.Ioc t0 t1)] fun t ↦ (velocity r.succ : ℝ → DerivLp n 2 Omega) t) ∧
      (∀ r : Fin m,
      (fun t ↦ (h10L2GelfandTriple hOmegaOpen).pivotToDual
          ((velocity r.castSucc : ℝ → DerivLp n 2 Omega) t))
        =ᵐ[volume.restrict (Set.Ioc t0 t1)]
          fun t ↦ (acceleration r.succ : ℝ → StrongDual ℝ (H¹₀(Omega))) t) ∧
      MemLp (fun t ↦ (u (0 : Fin (m + 1)) : ℝ → H¹₀(Omega)) t) (⊤ : ENNReal)
      (volume.restrict (Set.Ioc t0 t1)) ∧
      MemLp (fun t ↦ (velocity (0 : Fin (m + 1)) : ℝ → DerivLp n 2 Omega) t) (⊤ : ENNReal)
      (volume.restrict (Set.Ioc t0 t1)) := by
  -- Destructure with `Exists.elim` and ascribe the witness type: `rcases` and
  -- implicit-argument inference against this large goal are expensive enough
  -- to exhaust the default heartbeat budget.
  refine (D.forcing.exists_dirichletLoadForcingChain_with_uniformBudget hOmegaOpen
    D.time_lt).elim fun dualForcing hforcingChain ↦ ?_
  refine hforcingChain.elim fun G hforcing ↦ ?_
  obtain ⟨hforcingRepresents, hforcingAdjacent, hforcingPivot, hforcingSq, _hG,
    hforcingBudget⟩ := hforcing
  obtain ⟨q, p, hqOriginal, hpOriginal, hadjacent, hcompatibility⟩ :=
    hD.exists_ambientInitialDataFamily D hOmegaOpen A spatialOperator dualForcing
      hforcingRepresents hforcingAdjacent
  exact (exists_finite_weak_wave_chain_witness (hfinite := hfinite)
      D hOmegaOpen A Sseq P hdenseEnergy hdensePivot dualForcing hforcingRepresents
      hforcingAdjacent hforcingPivot hforcingSq hforcingBudget q p hadjacent hcompatibility hRitz
      hc hA_symmetric hcoercive :
      Nonempty (FiniteWeakWaveChainWitness D hOmegaOpen A q p)).elim fun chain ↦
    ⟨q, p, chain.u, chain.velocity, chain.acceleration, hqOriginal, hpOriginal, hadjacent,
      chain.wave, chain.displacementLink, chain.accelerationLink, chain.displacementBound,
      chain.velocityBound⟩

/--
Symmetric-coercive specialization of Evans, §7.2.3, Theorem 6.

Compatible problem data and the higher elliptic Dirichlet lift produce a
weak wave with the prescribed initial values and an essentially bounded
order-`m+1` Sobolev time jet representing its displacement and velocity.

The spatial operator is symmetric and coercive, and the stable Galerkin scheme,
Ritz orthogonality, and elliptic lift are explicit hypotheses.
-/
theorem WaveProblemData.IsCompatible.exists_regularWeakWave_of_stableGalerkinScheme
    (D : WaveProblemData n m Omega t0 t1) (hOmegaOpen : IsOpen Omega)
    (A : H¹₀(Omega) →L[ℝ] StrongDual ℝ (H¹₀(Omega)))
    (spatialOperator : ∀ r : ℕ, W^{(r + 2),2}(Omega) →L[ℝ] W^{r,2}(Omega))
    (hD : D.IsCompatible A spatialOperator)
    (Sseq : ℕ → Submodule ℝ (H¹₀(Omega)))
    [hfinite : ∀ k, FiniteDimensional ℝ (Sseq k)]
    {c : ℝ} {K : NNReal}
    (P : ∀ k, StableTrialProjection (h10L2GelfandTriple hOmegaOpen) (Sseq k) K)
    (hdenseEnergy : ∀ v : H¹₀(Omega), ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k in Filter.atTop, ∃ w : Sseq k, ‖v - (w : H¹₀(Omega))‖ < epsilon)
    (hdensePivot : ∀ h : DerivLp n 2 Omega, ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ k in Filter.atTop, ∃ w : Sseq k,
        ‖h - (h10L2GelfandTriple hOmegaOpen).inclusion (w : H¹₀(Omega))‖ < epsilon)
    (hc : 0 < c) (hA_symmetric : ∀ v w : H¹₀(Omega), A v w = A w v)
    (hcoercive : ∀ v : H¹₀(Omega), c * ‖v‖ ^ 2 ≤ A v v)
    (hRitz : ∀ k, ∀ v : H¹₀(Omega), ∀ w : Sseq k,
      A (v - ((P k).energyProjection v : H¹₀(Omega))) (w : H¹₀(Omega)) = 0)
    (hreg : ∀ r : Fin m,
      HasHigherSolutionLift (n := n) (Omega := Omega) r.1 (coerciveDirichletSolutionOperator A
        ⟨c, hc, fun v ↦ by simpa only [pow_two, mul_assoc] using hcoercive v⟩)) :
    ∃ (q0 : H¹₀(Omega)) (p0 : DerivLp n 2 Omega)
        (u : Lp (H¹₀(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
        (velocity : Lp (DerivLp n 2 Omega) 2 (volume.restrict (Set.Ioc t0 t1)))
        (acceleration : Lp (StrongDual ℝ (H¹₀(Omega))) 2 (volume.restrict (Set.Ioc t0 t1)))
        (solution : SobolevTimeJet n (m + 1) Omega t0 t1),
      h10SubtypeL (n := n) (Ω := Omega) q0 =
        lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (by omega : 1 ≤ m + 1) D.displacement ∧
      p0 = wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega) D.velocity ∧
      Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hOmegaOpen) (fun _ ↦ A)
        (dirichletLoadTimeLp hOmegaOpen D.forcing.head) u velocity acceleration q0 p0 ∧
      ((fun t ↦ wkpBaseCoordinateCLM (n := n) (m := m + 1) (p := 2) (Ω := Omega)
            ((solution.head : ℝ → W^{(m + 1),2}(Omega)) t))
        =ᵐ[volume.restrict (Set.Ioc t0 t1)]
        fun t ↦ wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Omega)
          (h10SubtypeL (n := n) (Ω := Omega) ((u : ℝ → H¹₀(Omega)) t))) ∧
      baseCoordinateTimeLp solution.timeDerivative.head = velocity ∧
      solution.IsEssentiallyBounded := by
  obtain ⟨q, p, u, velocity, acceleration, hqOriginal, hpOriginal, _hadjacent, hWave,
      hdisplacementLink, haccelerationLink, huTop, hvelocityTop⟩ :=
    hD.exists_finiteWeakWaveChain (hfinite := hfinite) D hOmegaOpen A
      spatialOperator Sseq P hdenseEnergy hdensePivot hc hA_symmetric hcoercive hRitz
  obtain ⟨solution, hsolutionBase, hsolutionVelocity, hsolutionBound⟩ :=
    exists_sobolevTimeJet_of_finiteWeakWaveChain D.time_lt hOmegaOpen A
      ⟨c, hc, fun v ↦ by simpa only [pow_two, mul_assoc] using hcoercive v⟩ hreg
      (fun r ↦ D.forcing.iteratedTimeDerivative r) u velocity acceleration q p hWave
      hdisplacementLink haccelerationLink huTop hvelocityTop
  have h := hWave (Fin.last m)
  rw [SobolevTimeJet.iteratedTimeDerivative_last] at h
  exact ⟨q (Fin.last m), p (Fin.last m), u (Fin.last m), velocity (Fin.last m),
    acceleration (Fin.last m), solution, hqOriginal, hpOriginal, h, hsolutionBase,
    hsolutionVelocity, hsolutionBound⟩

end Hyperbolic.HigherRegularity
