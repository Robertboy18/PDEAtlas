/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.SmoothFamilies
public import PDE.Fluid.Boussinesq.HalfPlane.WithPast
public import PDE.Fluid.Boussinesq.VorticityStream.DynamicRescaling
public import PDE.Fluid.Boussinesq.VorticityStream.DynamicRescaling.PhysicalRates
public import PDE.Fluid.Boussinesq.VorticityStream.OriginJetFamilies
public import PDE.FDeriv.PartialDeriv.Dilation
public import PDE.Analysis.Calculus.Deriv.ContDiffOne
import PDE.Fluid.Boussinesq.VorticityStream.DynamicRescaling.Calculus
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# The normalized dynamic rescaling of a half-plane Boussinesq solution

Chen and Hou fix the rates of the dynamic rescaling by the normalization (2.9),
`c_l = 2 θ̃_xx(0)/ω̃_x(0)` and `c_ω = c_l/2 + ũ_x(0)`, in terms of the rescaled solution. For a
physical solution whose trace `ω_x(0, t)` does not vanish we fix the rates in physical time instead
(`normalizedRescaling`) and obtain the normalized rescaled solution `normalizedSolution k Q J`. It
solves the rescaled system (2.8) and satisfies the normalization (2.9) at every rescaled time.

The setting (`IsNormalizationSetting`): `Q` is a regular solution of order `k ≥ 3` on an open set
of times `J₀`, its representative `P = canonicalOf k Q` is the physical solution, and `J ⊆ J₀` is
an open interval around `0` on which `ω_x(0, t) ≠ 0`.

## Main results

* `IsNormalizationSetting.satisfiesDynamicRescaledSystemOn`: the rescaled system on `τ(J)`.
* `IsNormalizationSetting.regularity`: classical regularity of the rescaled fields.
* `IsNormalizationSetting.normalization`: the normalization (2.9) at every rescaled time.
* `IsNormalizationSetting.continuousOn_spatialRate`, `continuousOn_vorticityRate`.

## How it works

The rescaled traces are `ω̃_x(0) = C_ω C_l ω_x(0)`, `θ̃_xx(0) = C_θ C_l² θ_xx(0)` and
`ũ_x(0) = C_ω u_x(0)` at the physical time (`vorticityXAtOrigin_dynamicallyRescaledFields`,
`temperatureXXAtOrigin_dynamicallyRescaledFields`,
`tangentialVelocityXAtOrigin_dynamicallyRescaledFields`). Since `C_θ C_l = C_ω²`, the normalization
forces `c_l = C_ω a` and `c_ω = C_ω b` (`rates_eq_of_normalization`) with

```text
a = 2 θ_xx(0)/ω_x(0),   b = θ_xx(0)/ω_x(0) + u_x(0)
```

evaluated at the physical time (`physicalSpatialRate`, `physicalVorticityRate`). We take
`normalizedRescaling` to be `DynamicRescalingData.ofPhysicalRates` with these rates, so
`IsNormalizationSetting.normalization` is a direct computation with the three traces. The scale laws
hold by `DynamicRescalingData.satisfiesDynamicRescalingLawsAt_ofPhysicalRates`, and the forward
change of variables `dynamicallyRescaledFields_satisfySystemOn` turns the classical physical
solution into a solution of the rescaled system.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.1, (2.4)-(2.9).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Set Filter PDE.Analysis IncompressibleFlow
open PDE.Representations.Similarity
open scoped Topology ENNReal

namespace Boussinesq

set_option linter.missingDocs true

/-- The dilation rate `2 θ_xx(0)/ω_x(0)` of the normalization (2.9) as a function of the physical
time. -/
def physicalSpatialRate (fields : VorticityStreamFields) (t : ℝ) : ℝ :=
  2 * temperatureXXAtOrigin fields t / vorticityXAtOrigin fields t

/-- The vorticity rate `θ_xx(0)/ω_x(0) + u_x(0)` of the normalization (2.9) as a function of the
physical time. -/
def physicalVorticityRate (fields : VorticityStreamFields) (t : ℝ) : ℝ :=
  temperatureXXAtOrigin fields t / vorticityXAtOrigin fields t +
    tangentialVelocityXAtOrigin fields t

/-- The normalized dynamic rescaling of `fields` on the physical times `J`: the rescaling with
the rates `physicalSpatialRate` and `physicalVorticityRate` of the physical time. -/
def normalizedRescaling (fields : VorticityStreamFields) (J : Set ℝ) : DynamicRescalingData :=
  DynamicRescalingData.ofPhysicalRates J (physicalSpatialRate fields)
    (physicalVorticityRate fields)

/-- **The vorticity trace of a dynamically rescaled field**:
`ω̃_x(0, σ) = C_ω C_l ω_x(0, t(σ))`. -/
theorem vorticityXAtOrigin_dynamicallyRescaledFields (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (σ : ℝ)
    (hd : DifferentiableAt ℝ (fun y ↦ fields.vorticity y (data.physicalTime σ)) 0) :
    vorticityXAtOrigin (dynamicallyRescaledFields data fields) σ =
      data.vorticityScale σ * data.spatialScale σ *
        vorticityXAtOrigin fields (data.physicalTime σ) := by
  change (∂[0] (fun x ↦ data.vorticityScale σ *
    fields.vorticity (data.spatialScale σ • x) (data.physicalTime σ))) 0 = _
  rw [PDE.partialDeriv_const_mul_comp_smul 0 (f := fun y ↦ fields.vorticity y (data.physicalTime σ))
    _ _ (by rwa [smul_zero]), smul_zero]
  rfl

/-- **The temperature trace of a dynamically rescaled field**:
`θ̃_xx(0, σ) = C_θ C_l² θ_xx(0, t(σ))`. -/
theorem temperatureXXAtOrigin_dynamicallyRescaledFields (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (σ : ℝ)
    (hθ : ContDiff ℝ 2 (fun y ↦ fields.temperature y (data.physicalTime σ))) :
    temperatureXXAtOrigin (dynamicallyRescaledFields data fields) σ =
      data.temperatureScale σ * data.spatialScale σ * data.spatialScale σ *
        temperatureXXAtOrigin fields (data.physicalTime σ) := by
  have hθ1 : ContDiff ℝ 1 (∂[0] (fun y ↦ fields.temperature y (data.physicalTime σ))) :=
    PDE.contDiff_partialDeriv_of_succ (m := 1) hθ
  have hfirst : (fun y ↦ (∂[0] (fun x ↦
      (dynamicallyRescaledFields data fields).temperature x σ)) y) =
      fun y ↦ data.temperatureScale σ * data.spatialScale σ *
        (∂[0] (fun x ↦ fields.temperature x (data.physicalTime σ))) (data.spatialScale σ • y) := by
    funext y
    change (∂[0] (fun x ↦ data.temperatureScale σ *
      fields.temperature (data.spatialScale σ • x) (data.physicalTime σ))) y = _
    exact PDE.partialDeriv_const_mul_comp_smul 0 _ _ (hθ.differentiable (by norm_num) _)
  change (∂[0] (fun y ↦ (∂[0] (fun x ↦
    (dynamicallyRescaledFields data fields).temperature x σ)) y)) 0 = _
  rw [hfirst, PDE.partialDeriv_const_mul_comp_smul 0 _ _
    (hθ1.differentiable (by norm_num) _), smul_zero]
  rfl

/-- **The strain of a dynamically rescaled field**: `ũ_x(0, σ) = C_ω u_x(0, t(σ))`. -/
theorem tangentialVelocityXAtOrigin_dynamicallyRescaledFields (data : DynamicRescalingData)
    (fields : VorticityStreamFields) (σ : ℝ) (hL : data.spatialScale σ ≠ 0)
    (hψ : ContDiff ℝ 2 (fun y ↦ fields.streamFunction y (data.physicalTime σ))) :
    tangentialVelocityXAtOrigin (dynamicallyRescaledFields data fields) σ =
      data.vorticityScale σ * tangentialVelocityXAtOrigin fields (data.physicalTime σ) := by
  have hu : Differentiable ℝ
      (fun y ↦ vorticityStreamVelocity fields y (data.physicalTime σ) 0) :=
    (((contDiff_piLp (p := (2 : ENNReal))).1
      (contDiff_planarStreamVelocity _ hψ) 0).differentiable (by norm_num))
  have hvel : (fun x ↦ vorticityStreamVelocity (dynamicallyRescaledFields data fields) x σ 0) =
      fun x ↦ data.vorticityScale σ / data.spatialScale σ *
        vorticityStreamVelocity fields (data.spatialScale σ • x) (data.physicalTime σ) 0 := by
    funext x
    rw [vorticityStreamVelocity_dynamicallyRescaledFields data _ x σ
        ((hψ.differentiable (by norm_num)) _)]
    simp [dynamicSimilarityPoint, smul_eq_mul]
  change (∂[0] (fun x ↦ vorticityStreamVelocity (dynamicallyRescaledFields data fields) x σ 0)) 0
    = _
  rw [hvel, PDE.partialDeriv_const_mul_comp_smul 0 _ _ (hu _), smul_zero]
  change data.vorticityScale σ / data.spatialScale σ * data.spatialScale σ *
    tangentialVelocityXAtOrigin fields (data.physicalTime σ) = _
  field_simp

/-- **The rates of a normalized dynamic rescaling in physical time.** If the dynamically rescaled
fields satisfy the normalization (2.9) at `σ` and the scales satisfy `C_θ C_l = C_ω²` with
`C_ω, C_l ≠ 0`, then `c_l = C_ω a` and `c_ω = C_ω b` with the physical rates `a`, `b` at the
physical time `t(σ)`. -/
theorem rates_eq_of_normalization (data : DynamicRescalingData) (fields : VorticityStreamFields)
    {cl cw cθ : ℝ → ℝ} (σ : ℝ)
    (hnorm : SatisfiesRescalingNormalizationAt (dynamicallyRescaledFields data fields) cl cw cθ σ)
    (hC : data.vorticityScale σ ≠ 0) (hL : data.spatialScale σ ≠ 0)
    (hsource : data.temperatureScale σ * data.spatialScale σ = data.vorticityScale σ ^ 2)
    (hω : DifferentiableAt ℝ (fun y ↦ fields.vorticity y (data.physicalTime σ)) 0)
    (hθ : ContDiff ℝ 2 (fun y ↦ fields.temperature y (data.physicalTime σ)))
    (hψ : ContDiff ℝ 2 (fun y ↦ fields.streamFunction y (data.physicalTime σ))) :
    cl σ = data.vorticityScale σ * physicalSpatialRate fields (data.physicalTime σ) ∧
      cw σ = data.vorticityScale σ * physicalVorticityRate fields (data.physicalTime σ) := by
  have h1 := vorticityXAtOrigin_dynamicallyRescaledFields data fields σ hω
  have h2 := temperatureXXAtOrigin_dynamicallyRescaledFields data fields σ hθ
  have h3 := tangentialVelocityXAtOrigin_dynamicallyRescaledFields data fields σ hL hψ
  have hw : vorticityXAtOrigin fields (data.physicalTime σ) ≠ 0 := by
    intro h0
    apply hnorm.vorticity_x_at_origin_ne_zero
    rw [h1, h0, mul_zero]
  have hθs : data.temperatureScale σ = data.vorticityScale σ ^ 2 / data.spatialScale σ := by
    rw [← hsource]
    field_simp
  have hcl : cl σ = data.vorticityScale σ * physicalSpatialRate fields (data.physicalTime σ) := by
    rw [hnorm.spatial_rate_eq, h1, h2, hθs, physicalSpatialRate]
    field_simp
  refine ⟨hcl, ?_⟩
  rw [hnorm.vorticity_rate_eq, hcl, h3, physicalVorticityRate, physicalSpatialRate]
  field_simp

namespace HalfPlane

/-- The normalized rescaled solution: the dynamic rescaling `normalizedRescaling` of the
representative `canonicalOf k Q` on the physical times `J`. -/
def normalizedSolution (k : ℕ) (Q : VorticityStreamFields) (J : Set ℝ) : VorticityStreamFields :=
  dynamicallyRescaledFields (normalizedRescaling (canonicalOf k Q) J) (canonicalOf k Q)

/-- The rescaled times `τ(J)` of the normalized rescaling. -/
def normalizedTimes (k : ℕ) (Q : VorticityStreamFields) (J : Set ℝ) : Set ℝ :=
  DynamicRescalingData.rescaledClock (physicalVorticityRate (canonicalOf k Q)) '' J

/-- The setting of the normalized rescaling: `Q` is a regular solution of order `k ≥ 3` with
`0 < α < 1` on an open set of times `J₀`, and `J ⊆ J₀` is an open interval around `0` on which the
trace `ω_x(0, t)` of the representative `canonicalOf k Q` does not vanish. -/
structure IsNormalizationSetting (k : ℕ) (Q : VorticityStreamFields) (α : ℝ)
    (J₀ J : Set ℝ) : Prop where
  /-- The order is at least three. -/
  three_le : 3 ≤ k
  /-- The Hölder exponent is positive. -/
  alpha_pos : 0 < α
  /-- The Hölder exponent is less than one. -/
  alpha_lt_one : α < 1
  /-- `Q` is a regular solution of order `k` on `J₀`. -/
  regular : IsRegularSolutionOfOn k Q J₀ α
  /-- The times `J₀` form an open set. -/
  isOpen_domain : IsOpen J₀
  /-- The times `J` form an open set. -/
  isOpen : IsOpen J
  /-- The times `J` form an interval. -/
  ordConnected : J.OrdConnected
  /-- The interval `J` contains `0`. -/
  zero_mem : (0 : ℝ) ∈ J
  /-- `J ⊆ J₀`. -/
  subset : J ⊆ J₀
  /-- The trace `ω_x(0, t)` does not vanish on `J`. -/
  trace_ne_zero : ∀ t ∈ J, vorticityXAtOrigin (canonicalOf k Q) t ≠ 0

namespace IsNormalizationSetting

variable {k : ℕ} {Q : VorticityStreamFields} {α : ℝ} {J₀ J : Set ℝ}
  (h : IsNormalizationSetting k Q α J₀ J)
include h

/-- The order `k` is at least one. -/
theorem one_le : 1 ≤ k := by have := h.three_le; omega

/-- The representative is a regular solution of order `k` on `J₀`. -/
theorem regular_canonicalOf : IsRegularSolutionOfOn k (canonicalOf k Q) J₀ α :=
  h.regular.canonicalOf h.one_le h.isOpen_domain.uniqueDiffOn

/-- The representative is a classical solution on `J₀`. -/
theorem classical : IsClassicalVorticityStreamSolutionOn (canonicalOf k Q) J₀ :=
  h.regular_canonicalOf.toIsSolutionOn.classical

/-- The physical dilation rate is continuous on `J`. -/
theorem continuousOn_physicalSpatialRate :
    ContinuousOn (physicalSpatialRate (canonicalOf k Q)) J :=
  (continuousOn_const.mul ((h.regular.continuousOn_temperatureXXAtOrigin h.one_le).mono
    h.subset)).div ((h.regular.continuousOn_vorticityXAtOrigin h.one_le).mono h.subset)
    h.trace_ne_zero

/-- The physical vorticity rate is continuous on `J`. -/
theorem continuousOn_physicalVorticityRate :
    ContinuousOn (physicalVorticityRate (canonicalOf k Q)) J :=
  (((h.regular.continuousOn_temperatureXXAtOrigin h.one_le).mono h.subset).div
    ((h.regular.continuousOn_vorticityXAtOrigin h.one_le).mono h.subset) h.trace_ne_zero).add
    ((h.regular.continuousOn_tangentialVelocityXAtOrigin h.one_le h.isOpen_domain h.alpha_pos
      h.alpha_lt_one).mono h.subset)

/-- The rescaled times `τ(J)` form an open set. -/
theorem isOpen_normalizedTimes : IsOpen (normalizedTimes k Q J) :=
  DynamicRescalingData.isOpen_image_rescaledClock h.isOpen h.ordConnected h.zero_mem
    h.continuousOn_physicalVorticityRate

/-- The rescaled times `τ(J)` contain `0`. -/
theorem zero_mem_normalizedTimes : (0 : ℝ) ∈ (normalizedTimes k Q J) :=
  ⟨0, h.zero_mem, DynamicRescalingData.rescaledClock_zero _⟩

omit h in
/-- The clock maps the rescaled times into `J`. -/
theorem physicalTime_mem {σ : ℝ} (hσ : σ ∈ (normalizedTimes k Q J)) :
    (normalizedRescaling (canonicalOf k Q) J).physicalTime σ ∈ J :=
  DynamicRescalingData.physicalTime_ofPhysicalRates_mem hσ

/-- The scale laws at every rescaled time of `τ(J)`. -/
theorem satisfiesDynamicRescalingLawsAt {σ : ℝ} (hσ : σ ∈ (normalizedTimes k Q J)) :
    SatisfiesDynamicRescalingLawsAt (normalizedRescaling (canonicalOf k Q) J) σ :=
  DynamicRescalingData.satisfiesDynamicRescalingLawsAt_ofPhysicalRates h.isOpen h.ordConnected
    h.zero_mem h.continuousOn_physicalSpatialRate h.continuousOn_physicalVorticityRate hσ

/-- **The rescaled system.** The normalized rescaled solution solves the rescaled equations, the
Poisson equation and the Dirichlet condition at the times of `τ(J)`. -/
theorem satisfiesDynamicRescaledSystemOn :
    SatisfiesDynamicRescaledSystemOn (normalizedRescaling (canonicalOf k Q) J) (canonicalOf k Q)
      (normalizedTimes k Q J) :=
  dynamicallyRescaledFields_satisfySystemOn _ _ J₀ _ h.isOpen_domain h.classical
    (fun _ hσ ↦ h.satisfiesDynamicRescalingLawsAt hσ) fun _ hσ ↦ h.subset (physicalTime_mem hσ)

/-- The clock is `C¹` on `τ(J)`. -/
theorem contDiffOn_physicalTime :
    ContDiffOn ℝ 1 (normalizedRescaling (canonicalOf k Q) J).physicalTime (normalizedTimes k Q J) :=
  PDE.contDiffOn_one_of_hasDerivAt h.isOpen_normalizedTimes
    (fun _ hσ ↦ (h.satisfiesDynamicRescalingLawsAt hσ).physicalTime_hasDerivAt)
    fun _ hσ ↦ (h.satisfiesDynamicRescalingLawsAt hσ).vorticityScale_hasDerivAt.continuousAt
      |>.continuousWithinAt

/-- The vorticity scale is continuous on `τ(J)`. -/
theorem continuousOn_vorticityScale :
    ContinuousOn (normalizedRescaling (canonicalOf k Q) J).vorticityScale (normalizedTimes k Q J) :=
  fun _ hσ ↦ (h.satisfiesDynamicRescalingLawsAt hσ).vorticityScale_hasDerivAt.continuousAt
    |>.continuousWithinAt

/-- The spatial scale is continuous on `τ(J)`. -/
theorem continuousOn_spatialScale :
    ContinuousOn (normalizedRescaling (canonicalOf k Q) J).spatialScale (normalizedTimes k Q J) :=
  fun _ hσ ↦ (h.satisfiesDynamicRescalingLawsAt hσ).spatialScale_hasDerivAt.continuousAt
    |>.continuousWithinAt

/-- The temperature scale is continuous on `τ(J)`. -/
theorem continuousOn_temperatureScale :
    ContinuousOn (normalizedRescaling (canonicalOf k Q) J).temperatureScale
      (normalizedTimes k Q J) :=
  fun _ hσ ↦ (h.satisfiesDynamicRescalingLawsAt hσ).temperatureScale_hasDerivAt.continuousAt
    |>.continuousWithinAt

/-- The dilation rate is continuous on `τ(J)`. -/
theorem continuousOn_spatialRate :
    ContinuousOn (normalizedRescaling (canonicalOf k Q) J).spatialRate (normalizedTimes k Q J) :=
  DynamicRescalingData.continuousOn_spatialRate_ofPhysicalRates h.isOpen h.ordConnected h.zero_mem
    h.continuousOn_physicalSpatialRate h.continuousOn_physicalVorticityRate

/-- The vorticity rate is continuous on `τ(J)`. -/
theorem continuousOn_vorticityRate :
    ContinuousOn (normalizedRescaling (canonicalOf k Q) J).vorticityRate (normalizedTimes k Q J) :=
  DynamicRescalingData.continuousOn_vorticityRate_ofPhysicalRates h.isOpen h.ordConnected
    h.zero_mem h.continuousOn_physicalVorticityRate

/-- The vorticity scale is `C¹` on `τ(J)`. -/
theorem contDiffOn_vorticityScale :
    ContDiffOn ℝ 1 (normalizedRescaling (canonicalOf k Q) J).vorticityScale
      (normalizedTimes k Q J) :=
  PDE.contDiffOn_one_of_hasDerivAt h.isOpen_normalizedTimes
    (fun _ hσ ↦ (h.satisfiesDynamicRescalingLawsAt hσ).vorticityScale_hasDerivAt)
    (h.continuousOn_vorticityRate.mul h.continuousOn_vorticityScale)

/-- The spatial scale is `C¹` on `τ(J)`. -/
theorem contDiffOn_spatialScale :
    ContDiffOn ℝ 1 (normalizedRescaling (canonicalOf k Q) J).spatialScale (normalizedTimes k Q J) :=
  PDE.contDiffOn_one_of_hasDerivAt h.isOpen_normalizedTimes
    (fun _ hσ ↦ (h.satisfiesDynamicRescalingLawsAt hσ).spatialScale_hasDerivAt)
    (h.continuousOn_spatialRate.neg.mul h.continuousOn_spatialScale)

/-- The temperature scale is `C¹` on `τ(J)`. -/
theorem contDiffOn_temperatureScale :
    ContDiffOn ℝ 1 (normalizedRescaling (canonicalOf k Q) J).temperatureScale
      (normalizedTimes k Q J) :=
  PDE.contDiffOn_one_of_hasDerivAt h.isOpen_normalizedTimes
    (fun _ hσ ↦ (h.satisfiesDynamicRescalingLawsAt hσ).temperatureScale_hasDerivAt)
    ((h.continuousOn_spatialRate.add (continuousOn_const.mul h.continuousOn_vorticityRate)).mul
      h.continuousOn_temperatureScale)

/-- A dynamic pullback of a field jointly `C¹` on `ℝ² × J₀` is jointly `C¹` on `ℝ² × τ(J)`. -/
theorem contDiffOn_dynamicPullback {f : ℝ^2 → ℝ → ℝ} {A : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 (fun p : ℝ^2 × ℝ ↦ f p.1 p.2) (univ ×ˢ J₀))
    (hA : ContDiffOn ℝ 1 A (normalizedTimes k Q J)) :
    ContDiffOn ℝ 1 (fun p : ℝ^2 × ℝ ↦ dynamicPullback f A
      (normalizedRescaling (canonicalOf k Q) J).spatialScale
      (normalizedRescaling (canonicalOf k Q) J).physicalTime p.1 p.2)
      (univ ×ˢ (normalizedTimes k Q J)) := by
  set D := normalizedRescaling (canonicalOf k Q) J
  have hsnd : ContDiffOn ℝ 1 (fun p : ℝ^2 × ℝ ↦ p.2) (univ ×ˢ (normalizedTimes k Q J)) :=
    contDiff_snd.contDiffOn
  have hmaps : MapsTo (fun p : ℝ^2 × ℝ ↦ p.2) (univ ×ˢ (normalizedTimes k Q J))
      (normalizedTimes k Q J) :=
    fun p hp ↦ hp.2
  have hg : ContDiffOn ℝ 1 (fun p : ℝ^2 × ℝ ↦ (D.spatialScale p.2 • p.1, D.physicalTime p.2))
      (univ ×ˢ (normalizedTimes k Q J)) :=
    ((h.contDiffOn_spatialScale.comp hsnd hmaps).smul contDiff_fst.contDiffOn).prodMk
      (h.contDiffOn_physicalTime.comp hsnd hmaps)
  have hgmaps : MapsTo (fun p : ℝ^2 × ℝ ↦ (D.spatialScale p.2 • p.1, D.physicalTime p.2))
      (univ ×ˢ (normalizedTimes k Q J)) (univ ×ˢ J₀) := fun p hp ↦
    ⟨mem_univ _, h.subset (physicalTime_mem hp.2)⟩
  exact (hA.comp hsnd hmaps).smul (hf.comp hg hgmaps)

/-- **Classical regularity** of the normalized rescaled solution on `τ(J)`. -/
theorem regularity :
    HasClassicalVorticityStreamRegularityOn (normalizedSolution k Q J) (normalizedTimes k Q J) := by
  set D := normalizedRescaling (canonicalOf k Q) J
  have hreg := h.classical.regularity
  have hω := h.contDiffOn_dynamicPullback hreg.vorticity_contDiffOn h.contDiffOn_vorticityScale
  have hθ := h.contDiffOn_dynamicPullback hreg.temperature_contDiffOn
    h.contDiffOn_temperatureScale
  have hopen : IsOpen (univ ×ˢ (normalizedTimes k Q J) : Set (ℝ^2 × ℝ)) :=
    isOpen_univ.prod h.isOpen_normalizedTimes
  have htime {F : ℝ^2 × ℝ → ℝ} (hF : ContDiffOn ℝ 1 F (univ ×ˢ (normalizedTimes k Q J))) {x : ℝ^2}
      {σ : ℝ} (hσ : σ ∈ (normalizedTimes k Q J)) : DifferentiableAt ℝ (fun s ↦ F (x, s)) σ :=
    ((hF.contDiffAt (hopen.mem_nhds ⟨mem_univ x, hσ⟩)).differentiableAt (by norm_num)).comp σ
      (by fun_prop)
  refine
    { vorticity_contDiffOn := hω
      temperature_contDiffOn := hθ
      vorticity_differentiableAt_time := fun hσ ↦ htime hω hσ
      temperature_differentiableAt_time := fun hσ ↦ htime hθ hσ
      streamFunction_spatial_contDiff := fun {σ} hσ ↦ ?_ }
  have hψ := hreg.streamFunction_spatial_contDiff (h.subset (physicalTime_mem hσ))
  exact contDiff_const.mul (hψ.comp (contDiff_const_smul _))

/-- The slices of the representative at the clock times are `C¹`. -/
theorem contDiff_vorticity {σ : ℝ} (hσ : σ ∈ normalizedTimes k Q J) :
    ContDiff ℝ 1 (fun y ↦ (canonicalOf k Q).vorticity y
      ((normalizedRescaling (canonicalOf k Q) J).physicalTime σ)) :=
  h.classical.regularity.vorticity_spatial_contDiff (h.subset (physicalTime_mem hσ))

/-- **The vorticity trace of the rescaled solution**: `ω̃_x(0, σ) = C_ω C_l ω_x(0, t(σ))`. -/
theorem vorticityXAtOrigin_normalizedSolution {σ : ℝ} (hσ : σ ∈ normalizedTimes k Q J) :
    vorticityXAtOrigin (normalizedSolution k Q J) σ =
      (normalizedRescaling (canonicalOf k Q) J).vorticityScale σ *
        (normalizedRescaling (canonicalOf k Q) J).spatialScale σ *
        vorticityXAtOrigin (canonicalOf k Q)
          ((normalizedRescaling (canonicalOf k Q) J).physicalTime σ) :=
  vorticityXAtOrigin_dynamicallyRescaledFields _ _ σ
    ((h.contDiff_vorticity hσ).differentiable (by norm_num) 0)

/-- **The temperature trace of the rescaled solution**:
`θ̃_xx(0, σ) = C_θ C_l² θ_xx(0, t(σ))`. -/
theorem temperatureXXAtOrigin_normalizedSolution {σ : ℝ} (hσ : σ ∈ normalizedTimes k Q J) :
    temperatureXXAtOrigin (normalizedSolution k Q J) σ =
      (normalizedRescaling (canonicalOf k Q) J).temperatureScale σ *
        (normalizedRescaling (canonicalOf k Q) J).spatialScale σ *
        (normalizedRescaling (canonicalOf k Q) J).spatialScale σ *
        temperatureXXAtOrigin (canonicalOf k Q)
          ((normalizedRescaling (canonicalOf k Q) J).physicalTime σ) := by
  obtain ⟨R, N, hRN⟩ := h.regular.exists_isHolderDataOf (h.subset (physicalTime_mem hσ))
  exact temperatureXXAtOrigin_dynamicallyRescaledFields _ _ σ
    (hRN.contDiff_canonicalOf_temperature.of_le (by exact_mod_cast (show 2 ≤ k + 1 by
      have := h.three_le; omega)))

/-- **The strain of the rescaled solution**: `ũ_x(0, σ) = C_ω u_x(0, t(σ))`. -/
theorem tangentialVelocityXAtOrigin_normalizedSolution {σ : ℝ}
    (hσ : σ ∈ normalizedTimes k Q J) :
    tangentialVelocityXAtOrigin (normalizedSolution k Q J) σ =
      (normalizedRescaling (canonicalOf k Q) J).vorticityScale σ *
        tangentialVelocityXAtOrigin (canonicalOf k Q)
          ((normalizedRescaling (canonicalOf k Q) J).physicalTime σ) :=
  tangentialVelocityXAtOrigin_dynamicallyRescaledFields _ _ σ
    (h.satisfiesDynamicRescalingLawsAt hσ).spatialScale_pos.ne'
    (h.classical.regularity.streamFunction_spatial_contDiff (h.subset (physicalTime_mem hσ)))

/-- **The normalization (2.9)** holds at every rescaled time of `τ(J)` for the rates of the
normalized rescaling. -/
theorem normalization {σ : ℝ} (hσ : σ ∈ normalizedTimes k Q J) :
    SatisfiesRescalingNormalizationAt (normalizedSolution k Q J)
      (normalizedRescaling (canonicalOf k Q) J).spatialRate
      (normalizedRescaling (canonicalOf k Q) J).vorticityRate
      (normalizedRescaling (canonicalOf k Q) J).temperatureRate σ := by
  have hw : vorticityXAtOrigin (canonicalOf k Q)
      ((normalizedRescaling (canonicalOf k Q) J).physicalTime σ) ≠ 0 :=
    h.trace_ne_zero _ (physicalTime_mem hσ)
  have hC : (normalizedRescaling (canonicalOf k Q) J).vorticityScale σ ≠ 0 :=
    (DynamicRescalingData.physicalVorticityScale_pos _ _).ne'
  have hL : (normalizedRescaling (canonicalOf k Q) J).spatialScale σ ≠ 0 :=
    (DynamicRescalingData.physicalSpatialScale_pos _ _).ne'
  have hθs : (normalizedRescaling (canonicalOf k Q) J).temperatureScale σ =
      (normalizedRescaling (canonicalOf k Q) J).vorticityScale σ ^ 2 /
        (normalizedRescaling (canonicalOf k Q) J).spatialScale σ := rfl
  have hcl : (normalizedRescaling (canonicalOf k Q) J).spatialRate σ =
      (normalizedRescaling (canonicalOf k Q) J).vorticityScale σ *
        physicalSpatialRate (canonicalOf k Q)
          ((normalizedRescaling (canonicalOf k Q) J).physicalTime σ) := rfl
  have hcw : (normalizedRescaling (canonicalOf k Q) J).vorticityRate σ =
      (normalizedRescaling (canonicalOf k Q) J).vorticityScale σ *
        physicalVorticityRate (canonicalOf k Q)
          ((normalizedRescaling (canonicalOf k Q) J).physicalTime σ) := rfl
  have h1 := h.vorticityXAtOrigin_normalizedSolution hσ
  have h2 := h.temperatureXXAtOrigin_normalizedSolution hσ
  have h3 := h.tangentialVelocityXAtOrigin_normalizedSolution hσ
  refine ⟨?_, ?_, ?_, rfl⟩
  · rw [h1]
    exact mul_ne_zero (mul_ne_zero hC hL) hw
  · rw [hcl, h1, h2, hθs, physicalSpatialRate]
    field_simp
  · rw [hcw, hcl, h3, physicalVorticityRate, physicalSpatialRate]
    field_simp

/-- The clock is continuous on `τ(J)`. -/
theorem continuousOn_physicalTime :
    ContinuousOn (normalizedRescaling (canonicalOf k Q) J).physicalTime (normalizedTimes k Q J) :=
  h.contDiffOn_physicalTime.continuousOn

/-- The dilations `x ↦ C_l(σ) x` form a smooth family on `τ(J)`. -/
theorem isSmoothFamilyOn_dilation (m : ℕ) :
    IsSmoothFamilyOn m (fun σ (x : ℝ^2) ↦
      (normalizedRescaling (canonicalOf k Q) J).spatialScale σ • x) (normalizedTimes k Q J) :=
  isSmoothFamilyOn_id.smul_continuousOn h.continuousOn_spatialScale

/-- A dynamic pullback of a smooth family on `J₀` is a smooth family on `τ(J)`. -/
theorem isSmoothFamilyOn_dynamicPullback {m : ℕ} {f : ℝ^2 → ℝ → ℝ} {A : ℝ → ℝ}
    (hf : IsSmoothFamilyOn m (fun s x ↦ f x s) J₀) (hA : ContinuousOn A (normalizedTimes k Q J)) :
    IsSmoothFamilyOn m (fun σ x ↦ dynamicPullback f A
      (normalizedRescaling (canonicalOf k Q) J).spatialScale
      (normalizedRescaling (canonicalOf k Q) J).physicalTime x σ) (normalizedTimes k Q J) :=
  (((hf.comp_time h.continuousOn_physicalTime fun _ hσ ↦ h.subset (physicalTime_mem hσ)).comp
    (h.isSmoothFamilyOn_dilation m)).smul_continuousOn hA).congr fun _ _ ↦ rfl

/-- The vorticity of the normalized rescaled solution is a smooth family of order `k`. -/
theorem isSmoothFamilyOn_vorticity :
    IsSmoothFamilyOn k (fun σ x ↦ (normalizedSolution k Q J).vorticity x σ)
      (normalizedTimes k Q J) :=
  h.isSmoothFamilyOn_dynamicPullback (h.regular.isSmoothFamilyOn_canonicalOf_vorticity h.one_le)
    h.continuousOn_vorticityScale

/-- The temperature of the normalized rescaled solution is a smooth family of order `k + 1`. -/
theorem isSmoothFamilyOn_temperature :
    IsSmoothFamilyOn (k + 1) (fun σ x ↦ (normalizedSolution k Q J).temperature x σ)
      (normalizedTimes k Q J) :=
  h.isSmoothFamilyOn_dynamicPullback h.regular.isSmoothFamilyOn_canonicalOf_temperature
    h.continuousOn_temperatureScale

/-- The velocity family of the normalized rescaled solution:
`C_ω(σ) C_l(σ)⁻¹ V(t(σ))(C_l(σ) x)` with the extended velocity `V` of the physical solution. -/
def normalizedVelocity (k : ℕ) (Q : VorticityStreamFields) (J : Set ℝ) (σ : ℝ) (x : ℝ^2) :
    ℝ^2 :=
  ((normalizedRescaling (canonicalOf k Q) J).vorticityScale σ /
      (normalizedRescaling (canonicalOf k Q) J).spatialScale σ) •
    extendedVelocity (k + 1)
      (fun y ↦ Q.vorticity y ((normalizedRescaling (canonicalOf k Q) J).physicalTime σ))
      ((normalizedRescaling (canonicalOf k Q) J).spatialScale σ • x)

/-- The velocity family is a smooth family of order `k + 1`. -/
theorem isSmoothFamilyOn_normalizedVelocity :
    IsSmoothFamilyOn (k + 1) (normalizedVelocity k Q J) (normalizedTimes k Q J) :=
  ((((h.regular.isSmoothFamilyOn_extendedVelocity h.isOpen_domain h.alpha_pos
    h.alpha_lt_one).comp_time h.continuousOn_physicalTime
      fun _ hσ ↦ h.subset (physicalTime_mem hσ)).comp
    (h.isSmoothFamilyOn_dilation (k + 1))).smul_continuousOn
    (h.continuousOn_vorticityScale.div h.continuousOn_spatialScale fun _ _ ↦
      (DynamicRescalingData.physicalSpatialScale_pos _ _).ne')).congr fun _ _ ↦ rfl

/-- On the open upper half-plane the velocity family is the velocity of the normalized rescaled
solution. -/
theorem normalizedVelocity_eq {σ : ℝ} (hσ : σ ∈ normalizedTimes k Q J) {x : ℝ^2}
    (hx : x ∈ upperHalfPlane) :
    normalizedVelocity k Q J σ x = vorticityStreamVelocity (normalizedSolution k Q J) x σ := by
  set D := normalizedRescaling (canonicalOf k Q) J
  have ht := h.subset (physicalTime_mem hσ)
  have hψ := h.classical.regularity.streamFunction_spatial_contDiff ht
  have hL : 0 < D.spatialScale σ := DynamicRescalingData.physicalSpatialScale_pos _ _
  have hLx : 0 ≤ (D.spatialScale σ • x) 1 := by
    rw [PiLp.smul_apply, smul_eq_mul]
    exact mul_nonneg hL.le (le_of_lt (show 0 < x 1 from hx))
  rw [show normalizedSolution k Q J = dynamicallyRescaledFields D (canonicalOf k Q) from rfl,
    vorticityStreamVelocity_dynamicallyRescaledFields D _ x σ
      ((hψ.differentiable (by norm_num)) _), normalizedVelocity,
    h.regular.extendedVelocity_eq h.one_le h.isOpen_domain.uniqueDiffOn ht hLx]
  rfl

/-- At rescaled times `σ ≥ 0` of `τ(J)` the physical time is nonnegative. -/
theorem physicalTime_nonneg {σ : ℝ} (hσ : σ ∈ normalizedTimes k Q J) (hσ0 : 0 ≤ σ) :
    0 ≤ (normalizedRescaling (canonicalOf k Q) J).physicalTime σ := by
  have hmono := DynamicRescalingData.strictMonoOn_rescaledClock h.isOpen h.ordConnected h.zero_mem
    h.continuousOn_physicalVorticityRate
  rw [← hmono.le_iff_le h.zero_mem (physicalTime_mem hσ),
    DynamicRescalingData.rescaledClock_zero]
  exact (DynamicRescalingData.rescaledClock_physicalTime_ofPhysicalRates
      (a := physicalSpatialRate (canonicalOf k Q)) hσ).symm ▸ hσ0

omit h in
/-- The coordinate reflection commutes with dilations. -/
theorem coordinateReflection_smul (c : ℝ) (x : ℝ^2) :
    PDE.Common.coordinateReflection (0 : Fin 2) (c • x) =
      c • PDE.Common.coordinateReflection (0 : Fin 2) x :=
  (PDE.Common.coordinateReflectionLinearIsometryEquiv (0 : Fin 2)).map_smul c x

/-- **The slices of the normalized rescaled solution** have the regularity and symmetry used by
the jet computations at the origin, at the rescaled times `σ ≥ 0` where the physical slices are in
the symmetry class. -/
theorem isOriginJetSliceAt {σ : ℝ} (hσ : σ ∈ normalizedTimes k Q J)
    (hsym : IsReflectionSymmetric
      (fun x ↦ Q.vorticity x ((normalizedRescaling (canonicalOf k Q) J).physicalTime σ))
      (fun x ↦ Q.temperature x ((normalizedRescaling (canonicalOf k Q) J).physicalTime σ))) :
    IsOriginJetSliceAt (normalizedSolution k Q J) σ := by
  set D := normalizedRescaling (canonicalOf k Q) J
  set t := D.physicalTime σ
  have ht := h.subset (physicalTime_mem hσ)
  have hL : 0 < D.spatialScale σ := DynamicRescalingData.physicalSpatialScale_pos _ _
  have hS := h.regular.toIsSolutionOn
  have hLx {x : ℝ^2} (hx : 0 ≤ x 1) : 0 ≤ (D.spatialScale σ • x) 1 := by
    rw [PiLp.smul_apply, smul_eq_mul]
    exact mul_nonneg hL.le hx
  -- the physical stream function on the closed half-plane
  obtain ⟨R, N, hRN⟩ := h.regular.exists_isHolderDataOf ht
  have hG : ContDiffOn ℝ (k + 1) (fun y ↦ (canonicalOf k Q).streamFunction y t)
      {y | 0 ≤ y 1} := by
    refine (contDiffOn_halfSpaceGreenPotential hRN.vorticity_contDiffOn
      fun y hy hyR ↦ (hRN.eq_zero y hy hyR).1).congr fun y hy ↦ ?_
    rw [canonicalOf_streamFunction_of_nonneg hy, hS.stream t ht y hy]
  have hPω (x : ℝ^2) : (canonicalOf k Q).vorticity (tangentialReflection x) t =
      -(canonicalOf k Q).vorticity x t :=
    canonicalOf_vorticity_tangentialReflection (fun y hy ↦ hsym.vorticity_odd y hy) x
  have hPθ (x : ℝ^2) : (canonicalOf k Q).temperature (tangentialReflection x) t =
      (canonicalOf k Q).temperature x t :=
    canonicalOf_temperature_tangentialReflection (fun y hy ↦ hsym.temperature_even y hy) x
  have hPψ (x : ℝ^2) : (canonicalOf k Q).streamFunction (tangentialReflection x) t =
      -(canonicalOf k Q).streamFunction x t :=
    hS.canonicalOf_streamFunction_tangentialReflection ht (fun y hy ↦ hsym.vorticity_odd y hy) x
  have hR (x : ℝ^2) : PDE.Common.coordinateReflection (0 : Fin 2) (D.spatialScale σ • x) =
      tangentialReflection (D.spatialScale σ • x) := rfl
  refine
    { vorticity := (h.isSmoothFamilyOn_vorticity.contDiff hσ).of_le
        (by exact_mod_cast h.three_le)
      temperature := (h.isSmoothFamilyOn_temperature.contDiff hσ).of_le
        (by exact_mod_cast (show 4 ≤ k + 1 by have := h.three_le; omega))
      stream := h.regularity.streamFunction_spatial_contDiff hσ
      jetStream := ⟨?_, fun x _ ↦ ?_, fun x hx ↦ ?_⟩
      vorticity_odd := fun x _ ↦ ?_
      temperature_even := fun x _ ↦ ?_
      temperature_axis := fun x hx hx0 ↦ ?_
      poisson := fun x hx ↦ h.satisfiesDynamicRescaledSystemOn.2.1 hx hσ }
  · change ContDiffOn ℝ 4 (fun x ↦ D.vorticityScale σ / D.spatialScale σ ^ 2 *
      (canonicalOf k Q).streamFunction (D.spatialScale σ • x) t) _
    exact (contDiffOn_const.mul (hG.comp (contDiff_const_smul _).contDiffOn
      fun y hy ↦ hLx hy)).of_le (by exact_mod_cast (show 4 ≤ k + 1 by have := h.three_le; omega))
  · change D.vorticityScale σ / D.spatialScale σ ^ 2 * (canonicalOf k Q).streamFunction
      (D.spatialScale σ • PDE.Common.coordinateReflection (0 : Fin 2) x) t =
      -1 * (D.vorticityScale σ / D.spatialScale σ ^ 2 *
        (canonicalOf k Q).streamFunction (D.spatialScale σ • x) t)
    rw [← coordinateReflection_smul, hR, hPψ]
    ring
  · change D.vorticityScale σ / D.spatialScale σ ^ 2 *
      (canonicalOf k Q).streamFunction (D.spatialScale σ • x) t = 0
    have hb : D.spatialScale σ • x = horizontalBoundaryPoint ((D.spatialScale σ • x) 0) := by
      ext i
      fin_cases i <;> simp [horizontalBoundaryPoint, hx]
    rw [hb, h.classical.zero_streamFunction_boundary _ ht, mul_zero]
  · change D.vorticityScale σ • (canonicalOf k Q).vorticity
      (D.spatialScale σ • PDE.Common.coordinateReflection (0 : Fin 2) x) t =
      -1 * (D.vorticityScale σ • (canonicalOf k Q).vorticity (D.spatialScale σ • x) t)
    rw [← coordinateReflection_smul, hR, hPω, smul_eq_mul, smul_eq_mul]
    ring
  · change D.temperatureScale σ • (canonicalOf k Q).temperature
      (D.spatialScale σ • PDE.Common.coordinateReflection (0 : Fin 2) x) t =
      1 * (D.temperatureScale σ • (canonicalOf k Q).temperature (D.spatialScale σ • x) t)
    rw [← coordinateReflection_smul, hR, hPθ, one_mul]
  · change D.temperatureScale σ • (canonicalOf k Q).temperature (D.spatialScale σ • x) t = 0
    have hLx' := hLx (le_of_lt (show 0 < x 1 from hx))
    rw [canonicalOf_temperature_of_nonneg hLx',
      hsym.temperature_axis _ (by simp [hx0]) hLx', smul_zero]

/-- The temperature rate of the normalized rescaling is continuous on `τ(J)`. -/
theorem continuousOn_temperatureRate :
    ContinuousOn (normalizedRescaling (canonicalOf k Q) J).temperatureRate
      (normalizedTimes k Q J) :=
  (h.continuousOn_spatialRate.add (continuousOn_const.mul h.continuousOn_vorticityRate)).congr
    fun _ _ ↦ rfl

/-- **The evolution of the origin jets** of the normalized rescaled solution at the rescaled times
of `τ(J)` where the physical slices are in the symmetry class. -/
theorem hasOriginJetEvolutionAt {σ : ℝ} (hσ : σ ∈ normalizedTimes k Q J)
    (hsym : IsReflectionSymmetric
      (fun x ↦ Q.vorticity x ((normalizedRescaling (canonicalOf k Q) J).physicalTime σ))
      (fun x ↦ Q.temperature x ((normalizedRescaling (canonicalOf k Q) J).physicalTime σ))) :
    HasOriginJetEvolutionAt (normalizedSolution k Q J)
      (normalizedRescaling (canonicalOf k Q) J).spatialRate
      (normalizedRescaling (canonicalOf k Q) J).vorticityRate
      (normalizedRescaling (canonicalOf k Q) J).temperatureRate σ :=
  hasOriginJetEvolutionAt_of_isSmoothFamilyOn h.isOpen_normalizedTimes h.continuousOn_spatialRate
    h.continuousOn_vorticityRate h.continuousOn_temperatureRate
    (h.isSmoothFamilyOn_vorticity.mono h.three_le)
    (h.isSmoothFamilyOn_temperature.mono (by have := h.three_le; omega))
    (h.isSmoothFamilyOn_normalizedVelocity.mono (by have := h.three_le; omega))
    (fun _ hs _ hx ↦ h.normalizedVelocity_eq hs hx) h.regularity
    h.satisfiesDynamicRescaledSystemOn.1 hσ (h.isOriginJetSliceAt hσ hsym)

omit h in
/-- The rescaled slices are dilations of the physical slices with the vorticity amplitude. -/
theorem vorticity_normalizedSolution (σ : ℝ) (x : ℝ^2) :
    (normalizedSolution k Q J).vorticity x σ =
      (normalizedRescaling (canonicalOf k Q) J).vorticityScale σ *
        (canonicalOf k Q).vorticity ((normalizedRescaling (canonicalOf k Q) J).spatialScale σ • x)
          ((normalizedRescaling (canonicalOf k Q) J).physicalTime σ) := rfl

omit h in
/-- The rescaled slices are dilations of the physical slices with the temperature amplitude. -/
theorem temperature_normalizedSolution (σ : ℝ) (x : ℝ^2) :
    (normalizedSolution k Q J).temperature x σ =
      (normalizedRescaling (canonicalOf k Q) J).temperatureScale σ *
        (canonicalOf k Q).temperature
          ((normalizedRescaling (canonicalOf k Q) J).spatialScale σ • x)
          ((normalizedRescaling (canonicalOf k Q) J).physicalTime σ) := rfl

omit h in
/-- The rescaled stream function is a dilation of the physical one. -/
theorem streamFunction_normalizedSolution (σ : ℝ) (x : ℝ^2) :
    (normalizedSolution k Q J).streamFunction x σ =
      (normalizedRescaling (canonicalOf k Q) J).vorticityScale σ /
          (normalizedRescaling (canonicalOf k Q) J).spatialScale σ ^ 2 *
        (canonicalOf k Q).streamFunction
          ((normalizedRescaling (canonicalOf k Q) J).spatialScale σ • x)
          ((normalizedRescaling (canonicalOf k Q) J).physicalTime σ) := rfl

/-- The initial values: at rescaled time zero the normalized rescaled solution is the physical
solution at time zero. -/
theorem normalizedSolution_zero (x : ℝ^2) :
    (normalizedSolution k Q J).vorticity x 0 = (canonicalOf k Q).vorticity x 0 ∧
      (normalizedSolution k Q J).temperature x 0 = (canonicalOf k Q).temperature x 0 ∧
      (normalizedSolution k Q J).streamFunction x 0 = (canonicalOf k Q).streamFunction x 0 := by
  have h0 := DynamicRescalingData.physicalTime_ofPhysicalRates_zero
    (a := physicalSpatialRate (canonicalOf k Q)) h.isOpen h.ordConnected h.zero_mem
    h.continuousOn_physicalVorticityRate
  simp [normalizedSolution, dynamicallyRescaledFields, rescaledVorticity, rescaledTemperature,
    rescaledStreamFunction, dynamicPullback, normalizedRescaling,
    DynamicRescalingData.ofPhysicalRates, dynamicSimilarityPoint] at h0 ⊢
  simp [h0]

/-- The rescaled time is continuous on `J`. -/
theorem continuousOn_rescaledClock :
    ContinuousOn (DynamicRescalingData.rescaledClock (physicalVorticityRate (canonicalOf k Q))) J :=
  fun _ ht ↦ (DynamicRescalingData.hasStrictDerivAt_rescaledClock h.isOpen h.ordConnected
    h.zero_mem h.continuousOn_physicalVorticityRate ht).hasDerivAt.continuousAt.continuousWithinAt

/-- The rescaled times `τ(J)` form an interval. -/
theorem ordConnected_normalizedTimes : (normalizedTimes k Q J).OrdConnected :=
  (h.ordConnected.isPreconnected.image _ h.continuousOn_rescaledClock).ordConnected

/-- The trace `ω̃_x(0, σ)` is continuous on `τ(J)`. -/
theorem continuousOn_vorticityXAtOrigin :
    ContinuousOn (vorticityXAtOrigin (normalizedSolution k Q J)) (normalizedTimes k Q J) :=
  IsSmoothFamilyOn.continuousOn_iteratedPartialDeriv_apply [0]
    (h.isSmoothFamilyOn_vorticity.mono h.one_le) 0

/-- The trace `θ̃_xx(0, σ)` is continuous on `τ(J)`. -/
theorem continuousOn_temperatureXXAtOrigin :
    ContinuousOn (temperatureXXAtOrigin (normalizedSolution k Q J)) (normalizedTimes k Q J) :=
  IsSmoothFamilyOn.continuousOn_iteratedPartialDeriv_apply [0, 0]
    (h.isSmoothFamilyOn_temperature.mono (show 2 ≤ k + 1 by have := h.three_le; omega)) 0

/-- **The traces are constant.** If the physical slices are in the symmetry class at the
nonnegative times of `J`, the traces `ω̃_x(0, σ)` and `θ̃_xx(0, σ)` of the normalized rescaled
solution keep their initial values at the rescaled times `σ ≥ 0` of `τ(J)`. -/
theorem traces_eq
    (hsym : ∀ t ∈ J, 0 ≤ t →
      IsReflectionSymmetric (fun x ↦ Q.vorticity x t) (fun x ↦ Q.temperature x t))
    {σ : ℝ} (hσ : σ ∈ normalizedTimes k Q J) (hσ0 : 0 ≤ σ) :
    vorticityXAtOrigin (normalizedSolution k Q J) σ =
        vorticityXAtOrigin (normalizedSolution k Q J) 0 ∧
      temperatureXXAtOrigin (normalizedSolution k Q J) σ =
        temperatureXXAtOrigin (normalizedSolution k Q J) 0 := by
  have hsub : Icc 0 σ ⊆ normalizedTimes k Q J :=
    h.ordConnected_normalizedTimes.out h.zero_mem_normalizedTimes hσ
  have hmem {s : ℝ} (hs : s ∈ Ioo 0 σ) : s ∈ normalizedTimes k Q J :=
    hsub (Ioo_subset_Icc_self hs)
  exact eqOn_traces_of_normalization
    (fun s hs ↦ h.hasOriginJetEvolutionAt (hmem hs)
      (hsym _ (physicalTime_mem (hmem hs)) (h.physicalTime_nonneg (hmem hs) hs.1.le)))
    (fun s hs ↦ h.normalization (hmem hs)) (h.continuousOn_vorticityXAtOrigin.mono hsub)
    (h.continuousOn_temperatureXXAtOrigin.mono hsub) σ ⟨hσ0, le_rfl⟩

/-- **The dilation rate is constant** at the rescaled times `σ ≥ 0` of `τ(J)`. -/
theorem spatialRate_eq
    (hsym : ∀ t ∈ J, 0 ≤ t →
      IsReflectionSymmetric (fun x ↦ Q.vorticity x t) (fun x ↦ Q.temperature x t))
    {σ : ℝ} (hσ : σ ∈ normalizedTimes k Q J) (hσ0 : 0 ≤ σ) :
    (normalizedRescaling (canonicalOf k Q) J).spatialRate σ =
      (normalizedRescaling (canonicalOf k Q) J).spatialRate 0 := by
  rw [(h.normalization hσ).spatial_rate_eq,
    (h.normalization h.zero_mem_normalizedTimes).spatial_rate_eq, (h.traces_eq hsym hσ hσ0).1,
    (h.traces_eq hsym hσ hσ0).2]

end IsNormalizationSetting

/-- The rescaled life span of the normalized rescaling: the supremum of the rescaled times
`σ ≥ 0` of `τ(J)`. -/
def normalizedLifeSpan (k : ℕ) (Q : VorticityStreamFields) (J : Set ℝ) : ℝ≥0∞ :=
  ⨆ σ ∈ normalizedTimes k Q J ∩ Ici 0, ENNReal.ofReal σ

namespace IsNormalizationSetting

variable {k : ℕ} {Q : VorticityStreamFields} {α : ℝ} {J₀ J : Set ℝ}
  (h : IsNormalizationSetting k Q α J₀ J)
include h

/-- The rescaled life span is the set of rescaled times `σ ≥ 0` of `τ(J)`. -/
theorem lifeSpan_normalizedLifeSpan :
    lifeSpan (normalizedLifeSpan k Q J) = normalizedTimes k Q J ∩ Ici 0 := by
  ext σ
  constructor
  · rintro ⟨hσ0, hσT⟩
    obtain ⟨σ', ⟨hσ', hσ'0⟩, hlt⟩ := lt_biSup_iff.mp hσT
    have hσσ' : σ < σ' := (ENNReal.ofReal_lt_ofReal_iff'.mp hlt).1
    exact ⟨h.ordConnected_normalizedTimes.out h.zero_mem_normalizedTimes hσ' ⟨hσ0, hσσ'.le⟩,
      hσ0⟩
  · rintro ⟨hσ, hσ0⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 h.isOpen_normalizedTimes σ hσ
    have hmem : σ + ε / 2 ∈ normalizedTimes k Q J := hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith)
    refine ⟨hσ0, lt_of_lt_of_le ?_ (le_iSup₂_of_le (σ + ε / 2)
      ⟨hmem, show 0 ≤ σ + ε / 2 by simp at hσ0; linarith⟩ le_rfl)⟩
    exact (ENNReal.ofReal_lt_ofReal_iff (by simp at hσ0; linarith)).2 (by linarith)

/-- The rescaled life span is positive. -/
theorem normalizedLifeSpan_pos : 0 < normalizedLifeSpan k Q J := by
  have h0 : (0 : ℝ) ∈ lifeSpan (normalizedLifeSpan k Q J) := by
    rw [h.lifeSpan_normalizedLifeSpan]
    exact ⟨h.zero_mem_normalizedTimes, le_rfl⟩
  exact pos_of_mem_lifeSpan h0

end IsNormalizationSetting

end HalfPlane

end Boussinesq
