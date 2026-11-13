/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.Symmetry

/-!
# The symmetry sectors are closed

The even and odd axisymmetric sectors are closed subspaces, both in the solenoidal zero-boundary
space on a ball and in the whole-space `H¹` velocity space. The argument is the same for all
four. Each symmetry condition is an almost-everywhere identity
`L u(M y) = N u(y)` with linear maps `L`, `N` and a measure-preserving `M`. If `u_k → u` in
`L²`, a subsequence converges almost everywhere, also after composition with `M`, and the
identity passes to the limit (`isClosed_setOf_isEvenAxisymmetric`,
`isClosed_setOf_isOddAxisymmetric`). The zero extension `ballField ρ` and the representative
`Stationary.representative` are continuous into `L²(ℝ^3; ℝ^3)`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set SobolevSpace SobolevSpace.GraphSpace
open PDE.CoordinateSystems (axialRotation equatorialReflection
  measurePreserving_equatorialReflection)
open scoped ENNReal Topology Sobolev SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

variable {X : Type*} [TopologicalSpace X] [SequentialSpace X]

/-- For a family of fields that is sequentially continuous into `L²`, an almost-everywhere
identity `L u(M y) = N u(y)` with continuous linear `L`, `N` and quasi-measure-preserving `M`
defines a closed set of parameters. -/
theorem isClosed_setOf_ae_comp_eq (F : X → ℝ^3 → ℝ^3)
    (hF : ∀ (x : ℕ → X) (a : X), Tendsto x atTop (𝓝 a) →
      Tendsto (fun k ↦ eLpNorm (F (x k) - F a) 2 volume) atTop (𝓝 0))
    (L N : ℝ^3 →L[ℝ] ℝ^3) (M : ℝ^3 → ℝ^3)
    (hM : QuasiMeasurePreserving M volume volume) :
    IsClosed {x | (fun y ↦ L (F x (M y))) =ᵐ[volume] fun y ↦ N (F x y)} := by
  refine IsSeqClosed.isClosed fun x a hx hxa ↦ ?_
  have hmeasure : TendstoInMeasure volume (fun k ↦ F (x k)) atTop (F a) :=
    tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (hF x a hxa)
  obtain ⟨ns, -, hae⟩ := hmeasure.exists_seq_tendsto_ae
  have hall : ∀ᵐ y ∂volume, ∀ k, L (F (x k) (M y)) = N (F (x k) y) :=
    ae_all_iff.mpr fun k ↦ hx k
  filter_upwards [hae, hM.ae hae, hall] with y hy hMy hyall
  have h1 := (L.continuous.tendsto _).comp hMy
  simp only [Function.comp_def, hyall] at h1
  exact tendsto_nhds_unique h1 ((N.continuous.tendsto _).comp hy)

/-- Even axisymmetry is a closed condition along a family that is sequentially continuous
into `L²`. -/
theorem isClosed_setOf_isEvenAxisymmetric (F : X → ℝ^3 → ℝ^3)
    (hF : ∀ (x : ℕ → X) (a : X), Tendsto x atTop (𝓝 a) →
      Tendsto (fun k ↦ eLpNorm (F (x k) - F a) 2 volume) atTop (𝓝 0)) :
    IsClosed {x | IsEvenAxisymmetric (F x)} := by
  have h := (isClosed_iInter fun θ : ℝ ↦ isClosed_setOf_ae_comp_eq F hF
      (axialRotation θ).toContinuousLinearEquiv.toContinuousLinearMap
      (ContinuousLinearMap.id ℝ _) _
      (axialRotation θ).symm.measurePreserving.quasiMeasurePreserving).inter
    (isClosed_setOf_ae_comp_eq F hF
      equatorialReflection.toContinuousLinearEquiv.toContinuousLinearMap
      (ContinuousLinearMap.id ℝ _) _ measurePreserving_equatorialReflection.quasiMeasurePreserving)
  convert h using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  exact Iff.rfl

/-- Odd axisymmetry is a closed condition along a family that is sequentially continuous
into `L²`. -/
theorem isClosed_setOf_isOddAxisymmetric (F : X → ℝ^3 → ℝ^3)
    (hF : ∀ (x : ℕ → X) (a : X), Tendsto x atTop (𝓝 a) →
      Tendsto (fun k ↦ eLpNorm (F (x k) - F a) 2 volume) atTop (𝓝 0)) :
    IsClosed {x | IsOddAxisymmetric (F x)} := by
  have h := (isClosed_iInter fun θ : ℝ ↦ isClosed_setOf_ae_comp_eq F hF
      (axialRotation θ).toContinuousLinearEquiv.toContinuousLinearMap
      (ContinuousLinearMap.id ℝ _) _
      (axialRotation θ).symm.measurePreserving.quasiMeasurePreserving).inter
    (isClosed_setOf_ae_comp_eq F hF
      equatorialReflection.toContinuousLinearEquiv.toContinuousLinearMap
      (-ContinuousLinearMap.id ℝ _) _ measurePreserving_equatorialReflection.quasiMeasurePreserving)
  convert h using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  exact Iff.rfl

omit [SequentialSpace X] in
/-- Sequential continuity into `L²` of a family given by a continuous map into an `L²` space,
up to almost-everywhere equality. -/
private theorem tendsto_eLpNorm_of_ae_eq_Lp {μ : Measure (ℝ^3)} (F : X → ℝ^3 → ℝ^3)
    (T : X → Lp (ℝ^3) 2 μ) (hT : Continuous T) (hFT : ∀ x, F x =ᵐ[μ] T x)
    (x : ℕ → X) (a : X) (hxa : Tendsto x atTop (𝓝 a)) :
    Tendsto (fun k ↦ eLpNorm (F (x k) - F a) 2 μ) atTop (𝓝 0) := by
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun k ↦ T (x k)) (T a)).mp
    ((hT.tendsto a).comp hxa)
  refine h.congr fun k ↦ eLpNorm_congr_ae ?_
  filter_upwards [hFT (x k), hFT a] with y h1 h2
  simp only [Pi.sub_apply, h1, h2]

/-! ### Sectors on a ball -/

/-- The zero extension to `ℝ^3` agrees almost everywhere with the zero extension of the `L²`
class on the ball, so its `L²` distances are those on the ball. -/
private theorem tendsto_eLpNorm_ballField (ρ : ℝ) {Y : Type*} [TopologicalSpace Y]
    (f : Y → H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) (hf : Continuous f) (x : ℕ → Y) (a : Y)
    (hxa : Tendsto x atTop (𝓝 a)) :
    Tendsto (fun k ↦ eLpNorm (ballField ρ (f (x k)) - ballField ρ (f a)) 2 volume)
      atTop (𝓝 0) := by
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
    (fun k ↦ ZeroBoundaryVectorSpace.toLp (f (x k))) (ZeroBoundaryVectorSpace.toLp (f a))).mp
    (((ZeroBoundaryVectorSpace.toLp.continuous.comp hf).tendsto a).comp hxa)
  refine h.congr fun k ↦ ?_
  rw [ballField, ballField, ← Set.indicator_sub',
    eLpNorm_indicator_eq_eLpNorm_restrict Metric.isOpen_ball.measurableSet.nullMeasurableSet]

/-- The even sector on a ball is closed. -/
theorem evenSector_isClosed (ρ : ℝ) :
    IsClosed (evenSector ρ : Set (IncompressibleFlow.SolenoidalSpace
      (ZeroBoundaryVectorSpace.divergence (n := 3) (Ω := Metric.ball (0 : ℝ^3) ρ)))) :=
  isClosed_setOf_isEvenAxisymmetric _ fun x a hxa ↦
    tendsto_eLpNorm_ballField ρ _ continuous_subtype_val x a hxa

/-- The odd sector on a ball is closed. -/
theorem oddSector_isClosed (ρ : ℝ) :
    IsClosed (oddSector ρ : Set (IncompressibleFlow.SolenoidalSpace
      (ZeroBoundaryVectorSpace.divergence (n := 3) (Ω := Metric.ball (0 : ℝ^3) ρ)))) :=
  isClosed_setOf_isOddAxisymmetric _ fun x a hxa ↦
    tendsto_eLpNorm_ballField ρ _ continuous_subtype_val x a hxa

/-! ### Sectors of whole-space `H¹` velocities -/

/-- The Euclidean-valued `L²` class of the representative of a whole-space `H¹` velocity. -/
private def representativeLp :
    PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)) →L[ℝ] Lp (ℝ^3) 2 (domainMeasure 3 univ) :=
  Lp.euclideanTuple.comp
    ((PiLp.continuousLinearEquiv 2 ℝ _).toContinuousLinearMap.comp Stationary.massCLM)

/-- The representative is a representative of `representativeLp`. -/
private theorem representative_ae_eq_representativeLp (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) :
    Stationary.representative w =ᵐ[volume] representativeLp w := by
  have h := Lp.euclideanTuple_apply_ae (μ := domainMeasure 3 univ)
    (fun i ↦ Stationary.massCLM w i)
  simp only [domainMeasure, Measure.restrict_univ] at h
  filter_upwards [h] with x hx
  ext i
  exact (hx i).symm

/-- `L²` convergence of representatives along convergent sequences of velocities. -/
private theorem tendsto_eLpNorm_representative (x : ℕ → PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)))
    (a : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) (hxa : Tendsto x atTop (𝓝 a)) :
    Tendsto (fun k ↦ eLpNorm (Stationary.representative (x k) - Stationary.representative a)
      2 volume) atTop (𝓝 0) := by
  have h := tendsto_eLpNorm_of_ae_eq_Lp (μ := domainMeasure 3 univ)
    Stationary.representative representativeLp representativeLp.continuous
    (fun w ↦ by
      simp only [domainMeasure, Measure.restrict_univ]
      exact representative_ae_eq_representativeLp w) x a hxa
  simpa only [domainMeasure, Measure.restrict_univ] using h

/-- The even whole-space sector is closed. -/
theorem evenSectorH1_isClosed :
    IsClosed (evenSectorH1 : Set (PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)))) :=
  isClosed_setOf_isEvenAxisymmetric _ tendsto_eLpNorm_representative

/-- The odd whole-space sector is closed. -/
theorem oddSectorH1_isClosed :
    IsClosed (oddSectorH1 : Set (PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)))) :=
  isClosed_setOf_isOddAxisymmetric _ tendsto_eLpNorm_representative

end NavierStokes.Nonuniqueness
