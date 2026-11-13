/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Basic
public import PDE.Hyperbolic.Variational.Spectral.Evolution

/-!
# Bounded wave operators constructed from spectral evolution

The spectral limit supplies a trajectory for every energy datum. Its
coordinates follow the finite-dimensional wave evolution exactly. Completeness
of the pivot basis then proves linearity in the data and the group law in time.
Conservation of energy gives a bound independent of time.

Restricting this group to nonnegative times gives a
`StronglyContinuousSemigroup`.
-/

@[expose] public section

noncomputable section

namespace Hyperbolic.Variational

open Filter Set
open scoped Topology InnerProductSpace BigOperators

variable {ι V H : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A spectral coordinate records the pivot displacement and velocity
coefficients of an energy state. -/
def waveCoordinate (J : V →L[ℝ] H) (basis : ι → H) (i : ι) :
    V × H →L[ℝ] ℝ × ℝ :=
  ((innerSL ℝ (basis i)).comp (J.comp (ContinuousLinearMap.fst ℝ V H))).prod
    ((innerSL ℝ (basis i)).comp (ContinuousLinearMap.snd ℝ V H))

/-- The two entries are the displacement and velocity coefficients. -/
@[simp]
theorem waveCoordinate_apply (J : V →L[ℝ] H) (basis : ι → H) (i : ι) (x : V × H) :
    waveCoordinate J basis i x = (⟪basis i, J x.1⟫_ℝ, ⟪basis i, x.2⟫_ℝ) :=
  rfl

/-- A complete pivot basis separates energy states when the inclusion is
injective. The displacement space need not carry an inner product. -/
theorem waveCoordinates_injective (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (basis : HilbertBasis ι ℝ H) :
    Function.Injective (fun x : V × H ↦ fun i ↦ waveCoordinate J basis i x) := by
  intro x y h
  apply Prod.ext
  · apply hJ
    apply basis.repr.injective
    apply lp.ext
    funext i
    simpa only [basis.repr_apply_apply, waveCoordinate_apply] using congrArg Prod.fst (congrFun h i)
  · apply basis.repr.injective
    apply lp.ext
    funext i
    simpa only [basis.repr_apply_apply, waveCoordinate_apply] using congrArg Prod.snd (congrFun h i)

/-- An included mode has exactly its independently evolved coefficient pair
in a finite spectral trajectory. -/
theorem waveCoordinate_finiteSpectralWave (J : V →L[ℝ] H) (basis : ι → H)
    (hbasis : Orthonormal ℝ basis) (lambda : ι → ℝ) (e : ι → V) (he : ∀ i, J (e i) = basis i)
    (s : Finset ι) (data : ι → ℝ × ℝ) {i : ι} (hi : i ∈ s) (t : ℝ) :
    waveCoordinate J basis i (finiteSpectralDisplacement lambda e s data t,
      J (finiteSpectralVelocity lambda e s data t)) = waveModeEvolution (lambda i) t (data i) := by
  apply Prod.ext
  · simpa only [waveCoordinate_apply, finiteSpectralDisplacement, map_sum, map_smul, he]
      using hbasis.inner_right_sum (fun j ↦ (waveModeEvolution (lambda j) t (data j)).1) hi
  · simpa only [waveCoordinate_apply, finiteSpectralVelocity, map_sum, map_smul, he]
      using hbasis.inner_right_sum (fun j ↦ (waveModeEvolution (lambda j) t (data j)).2) hi

/-- Every coordinate of a strong spectral limit agrees with the corresponding
scalar wave. A fixed mode occurs in all sufficiently large truncations. -/
theorem waveCoordinate_eq_of_tendsto_finiteSpectralWave (J : V →L[ℝ] H) (basis : HilbertBasis ℕ ℝ H)
    (lambda : ℕ → ℝ) (e : ℕ → V) (he : ∀ i, J (e i) = basis i) (data : ℕ → ℝ × ℝ) {t : ℝ}
    {x : V × H}
    (hx : Tendsto (fun n ↦ (finiteSpectralDisplacement lambda e (Finset.range n) data t,
      J (finiteSpectralVelocity lambda e (Finset.range n) data t))) atTop (𝓝 x))
    (i : ℕ) :
    waveCoordinate J basis i x = waveModeEvolution (lambda i) t (data i) := by
  have heventually : ∀ᶠ n : ℕ in atTop, waveCoordinate J basis i
        (finiteSpectralDisplacement lambda e (Finset.range n) data t,
          J (finiteSpectralVelocity lambda e (Finset.range n) data t)) =
        waveModeEvolution (lambda i) t (data i) := by
    filter_upwards [eventually_gt_atTop i] with n hn
    exact waveCoordinate_finiteSpectralWave J basis basis.orthonormal
      lambda e he (Finset.range n) data (Finset.mem_range.mpr hn) t
  exact tendsto_nhds_unique (((waveCoordinate J basis i).continuous.tendsto x).comp hx)
    (tendsto_const_nhds.congr' (Filter.Eventually.mono heventually fun _ h ↦ h.symm))

variable [CompleteSpace V] [CompleteSpace H]

/-- A complete weak eigenbasis constructs a uniformly bounded, strongly
continuous group of wave operators on `V × H`. The operators are obtained from
the spectral limits, and their group law follows from the coefficient
equations. -/
theorem exists_waveSolutionOperators_of_weakEigenbasis (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hsymm : ∀ v w, B v w = B w v) {c : ℝ} (hc : 0 < c) (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤ B v v)
    (J : V →L[ℝ] H) (hJ : Function.Injective J) (basis : HilbertBasis ℕ ℝ H) (lambda : ℕ → ℝ)
    (hlambda : ∀ i, 0 ≤ lambda i) (e : ℕ → V) (he : ∀ i, J (e i) = basis i)
    (hweak : ∀ i w, B (e i) w = lambda i * ⟪basis i, J w⟫_ℝ) :
    ∃ W : ℝ → (V × H →L[ℝ] V × H),
      (∀ x, Continuous (fun t ↦ W t x)) ∧
      W 0 = ContinuousLinearMap.id ℝ (V × H) ∧
      (∀ s t, W (s + t) = (W s).comp (W t)) ∧
      (∀ t x, autonomousWaveEnergy B (W t x) = autonomousWaveEnergy B x) ∧
      (∀ t i x, waveCoordinate J basis i (W t x) =
        waveModeEvolution (lambda i) t (waveCoordinate J basis i x)) ∧
      (∀ x : V × H, TendstoUniformlyOn (fun n t ↦
        (finiteSpectralDisplacement lambda e (Finset.range n)
          (fun i ↦ (⟪basis i, J x.1⟫_ℝ, ⟪basis i, x.2⟫_ℝ)) t,
          J (finiteSpectralVelocity lambda e (Finset.range n)
            (fun i ↦ (⟪basis i, J x.1⟫_ℝ, ⟪basis i, x.2⟫_ℝ)) t)))
        (fun t ↦ W t x) atTop univ) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ t, ‖W t‖ ≤ C := by
  classical
  choose U hUcontinuous hUlimit hUzero hUenergy using fun x : V × H ↦
    exists_global_continuous_energy_wave_of_weakEigenbasis
      B hsymm hc hcoercive J hJ basis lambda hlambda e he hweak x.1 x.2
  have hcoordinate (x : V × H) (t : ℝ) (i : ℕ) : waveCoordinate J basis i (U x t) =
        waveModeEvolution (lambda i) t (waveCoordinate J basis i x) :=
    waveCoordinate_eq_of_tendsto_finiteSpectralWave J basis lambda e he
      (fun i ↦ (⟪basis i, J x.1⟫_ℝ, ⟪basis i, x.2⟫_ℝ)) ((hUlimit x).tendsto_at (mem_univ t)) i
  have hadd (t : ℝ) (x y : V × H) : U (x + y) t = U x t + U y t := by
    apply waveCoordinates_injective J hJ basis
    funext i
    simp only [hcoordinate, map_add]
  have hsmul (t r : ℝ) (x : V × H) : U (r • x) t = r • U x t := by
    apply waveCoordinates_injective J hJ basis
    funext i
    simp only [hcoordinate, map_smul]
  have htime (s t : ℝ) (x : V × H) : U x (s + t) = U (U x t) s := by
    apply waveCoordinates_injective J hJ basis
    funext i
    simp only [hcoordinate, waveModeEvolution_add, ContinuousLinearMap.comp_apply]
  obtain ⟨C, hC, hbound⟩ := exists_pos_norm_le_of_autonomousWaveEnergy_le (H := H) B hc hcoercive
  have hnorm (t : ℝ) (x : V × H) : ‖U x t‖ ≤ C * ‖x‖ := hbound _ _ (hUenergy x t).le
  let L (t : ℝ) : V × H →ₗ[ℝ] V × H :=
    { toFun := fun x ↦ U x t
      map_add' := hadd t
      map_smul' := hsmul t }
  let W (t : ℝ) : V × H →L[ℝ] V × H := (L t).mkContinuous C (hnorm t)
  refine ⟨W, hUcontinuous, ?_, ?_, ?_, ?_, hUlimit, C, hC, ?_⟩
  · exact ContinuousLinearMap.ext fun x ↦ hUzero x
  · exact fun s t ↦ ContinuousLinearMap.ext fun x ↦ htime s t x
  · exact fun t x ↦ hUenergy x t
  · exact fun t i x ↦ hcoordinate x t i
  · exact fun t ↦ LinearMap.mkContinuous_norm_le (L t) hC.le (hnorm t)

/-- Restricting the constructed wave group to nonnegative time gives a
strongly continuous semigroup with exact energy conservation and a uniform
operator bound. The spectral coordinate formula identifies its action. -/
theorem exists_waveSemigroup_of_weakEigenbasis (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hsymm : ∀ v w, B v w = B w v) {c : ℝ} (hc : 0 < c) (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤ B v v)
    (J : V →L[ℝ] H) (hJ : Function.Injective J) (basis : HilbertBasis ℕ ℝ H) (lambda : ℕ → ℝ)
    (hlambda : ∀ i, 0 ≤ lambda i) (e : ℕ → V) (he : ∀ i, J (e i) = basis i)
    (hweak : ∀ i w, B (e i) w = lambda i * ⟪basis i, J w⟫_ℝ) :
    ∃ S : PDE.Analysis.Evolution.StronglyContinuousSemigroup (V × H),
      (∀ t x, autonomousWaveEnergy B (S t x) = autonomousWaveEnergy B x) ∧
      (∀ t i x, waveCoordinate J basis i (S t x) =
        waveModeEvolution (lambda i) (t : ℝ) (waveCoordinate J basis i x)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ t, ‖S t‖ ≤ C := by
  obtain ⟨W, hcontinuous, hzero, hadd, henergy, hcoordinate, _, C, hC, hbound⟩ :=
    exists_waveSolutionOperators_of_weakEigenbasis
      B hsymm hc hcoercive J hJ basis lambda hlambda e he hweak
  let S : PDE.Analysis.Evolution.StronglyContinuousSemigroup (V × H) :=
    { toMonoidHom :=
        { toFun := fun t ↦ W (t.toAdd : ℝ)
          map_one' := by
            change W 0 = 1
            simpa only [ContinuousLinearMap.one_def] using hzero
          map_mul' := by
            intro s t
            change W ((s.toAdd + t.toAdd : NNReal) : ℝ) = W (s.toAdd : ℝ) * W (t.toAdd : ℝ)
            simpa only [NNReal.coe_add, ContinuousLinearMap.mul_def] using
              hadd (s.toAdd : ℝ) (t.toAdd : ℝ) }
      continuous_toPointwise := by
        refine PointwiseConvergenceCLM.continuous_of_continuous_eval fun x ↦ ?_
        change Continuous (fun t : Multiplicative NNReal ↦ W (t.toAdd : ℝ) x)
        exact (hcontinuous x).comp (by
          change Continuous (fun t : NNReal ↦ (t : ℝ))
          fun_prop) }
  exact ⟨S, fun t x ↦ henergy (t : ℝ) x,
    fun t i x ↦ hcoordinate (t : ℝ) i x, C, hC, fun t ↦ hbound (t : ℝ)⟩

end Hyperbolic.Variational
