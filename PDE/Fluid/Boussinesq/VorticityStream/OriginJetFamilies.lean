/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.VorticityStream.OriginJetEvolution
public import PDE.Analysis.Calculus.SmoothFamilyEvolution

/-!
# The origin jets of solutions whose slices form smooth families

Consider a classical solution of the rescaled equations (2.8) on an open set of times `J` with
rates continuous on `J`, whose vorticity and temperature slices are smooth families of orders
three and four (`C³`/`C⁴` in space, spatial derivatives jointly continuous in space and time) and
whose velocity agrees on the open upper half-plane with a smooth family `V` of order three. Then the
origin jets evolve by the jet equations at every time of `J` at which the slices have the symmetry
and regularity of `IsOriginJetSliceAt` (`hasOriginJetEvolutionAt_of_isSmoothFamilyOn`).

The right sides of the two equations extend to the whole plane as the tendency families
`c_ω ω + ∂ₓθ - (c_l x + V)·∇ω` and `c_θ θ - (c_l x + V)·∇θ`, which are smooth families. The
equations give the time derivatives of the fields on the open half-plane, so
`IsSmoothFamilyOn.hasDerivAt_iteratedPartialDeriv` gives the time derivatives of the jets at the
boundary point `0` as the jets of the tendencies there, which `IsOriginJetSliceAt` identifies as
limits from the half-plane. Only continuity in time of the spatial derivatives is used: this is the
regularity that local well-posedness in Hölder spaces provides.

## Main results

* `Boussinesq.isSmoothFamilyOn_vorticityTendency`, `isSmoothFamilyOn_temperatureTendency`.
* `Boussinesq.hasOriginJetEvolutionAt_of_isSmoothFamilyOn`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.1, (2.8) and footnote 3,
  and Section 4.2.1, (4.12).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Filter Set PDE PDE.Common PDE.Analysis IncompressibleFlow
open PDE (laplacian advectiveDerivative)
open scoped Topology

namespace Boussinesq

set_option linter.missingDocs true

/-- The right side `c_ω ω + ∂ₓθ - (c_l x + V)·∇ω` of the rescaled vorticity equation with the
velocity `V s`, as a family of functions on the whole plane. -/
def vorticityTendencyFamily (fields : VorticityStreamFields) (cl cw : ℝ → ℝ)
    (V : ℝ → ℝ^2 → ℝ^2) (s : ℝ) (y : ℝ^2) : ℝ :=
  cw s * fields.vorticity y s + (∂[0] (fun z ↦ fields.temperature z s)) y -
    fderiv ℝ (fun z ↦ fields.vorticity z s) y (cl s • y + V s y)

/-- The right side `c_θ θ - (c_l x + V)·∇θ` of the rescaled temperature equation with the
velocity `V s`, as a family of functions on the whole plane. -/
def temperatureTendencyFamily (fields : VorticityStreamFields) (cl cθ : ℝ → ℝ)
    (V : ℝ → ℝ^2 → ℝ^2) (s : ℝ) (y : ℝ^2) : ℝ :=
  cθ s * fields.temperature y s - fderiv ℝ (fun z ↦ fields.temperature z s) y (cl s • y + V s y)

variable {fields : VorticityStreamFields} {cl cw cθ : ℝ → ℝ} {J : Set ℝ}
  {V : ℝ → ℝ^2 → ℝ^2} {m : ℕ}

/-- The transport field `c_l x + V` is a smooth family when `c_l` is continuous. -/
theorem isSmoothFamilyOn_transport (hcl : ContinuousOn cl J) (hV : IsSmoothFamilyOn m V J) :
    IsSmoothFamilyOn m (fun s y ↦ cl s • y + V s y) J :=
  (isSmoothFamilyOn_id.smul_continuousOn hcl).add hV

/-- The vorticity tendency is a smooth family of order `m` when the vorticity and the temperature
are smooth families of order `m + 1` and the velocity of order `m`. -/
theorem isSmoothFamilyOn_vorticityTendency (hcl : ContinuousOn cl J) (hcw : ContinuousOn cw J)
    (hω : IsSmoothFamilyOn (m + 1) (fun s x ↦ fields.vorticity x s) J)
    (hθ : IsSmoothFamilyOn (m + 1) (fun s x ↦ fields.temperature x s) J)
    (hV : IsSmoothFamilyOn m V J) :
    IsSmoothFamilyOn m (vorticityTendencyFamily fields cl cw V) J := by
  have h1 : IsSmoothFamilyOn m (fun s y ↦ cw s • fields.vorticity y s) J :=
    (hω.mono (Nat.le_succ m)).smul_continuousOn hcw
  have h2 : IsSmoothFamilyOn m (fun s y ↦ (∂[0] (fun z ↦ fields.temperature z s)) y) J :=
    ((isSmoothFamilyOn_succ_iff.mp hθ).2.2.clm_comp
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))).congr
      fun _ _ ↦ rfl
  have h3 := (isSmoothFamilyOn_succ_iff.mp hω).2.2.bilinear
    (ContinuousLinearMap.id ℝ (ℝ^2 →L[ℝ] ℝ)) (isSmoothFamilyOn_transport hcl hV)
  exact ((h1.add h2).sub h3).congr fun _ _ ↦ rfl

/-- The temperature tendency is a smooth family of order `m` when the temperature is a smooth
family of order `m + 1` and the velocity of order `m`. -/
theorem isSmoothFamilyOn_temperatureTendency (hcl : ContinuousOn cl J) (hcθ : ContinuousOn cθ J)
    (hθ : IsSmoothFamilyOn (m + 1) (fun s x ↦ fields.temperature x s) J)
    (hV : IsSmoothFamilyOn m V J) :
    IsSmoothFamilyOn m (temperatureTendencyFamily fields cl cθ V) J := by
  have h1 : IsSmoothFamilyOn m (fun s y ↦ cθ s • fields.temperature y s) J :=
    (hθ.mono (Nat.le_succ m)).smul_continuousOn hcθ
  have h3 := (isSmoothFamilyOn_succ_iff.mp hθ).2.2.bilinear
    (ContinuousLinearMap.id ℝ (ℝ^2 →L[ℝ] ℝ)) (isSmoothFamilyOn_transport hcl hV)
  exact (h1.sub h3).congr fun _ _ ↦ rfl

/-- The value at the origin of a derivative word of a `C^k` function that agrees on the open
upper half-plane with a function whose word has the limit `L` from the half-plane is `L`. -/
theorem iteratedPartialDeriv_eq_of_tendsto (l : List (Fin 2)) {G R : ℝ^2 → ℝ} {L : ℝ}
    (hG : ContDiff ℝ l.length G) (hGR : EqOn G R upperHalfPlane)
    (hL : Tendsto (iteratedPartialDeriv l R) (𝓝[upperHalfPlane] 0) (𝓝 L)) :
    iteratedPartialDeriv l G 0 = L := by
  have h1 := tendsto_iteratedPartialDeriv_of_contDiff hG l le_rfl
  have h2 : Tendsto (iteratedPartialDeriv l G) (𝓝[upperHalfPlane] 0) (𝓝 L) := by
    refine hL.congr' (eventually_nhdsWithin_of_forall fun y hy ↦ ?_)
    exact ((eventuallyEq_of_mem (isOpen_upperHalfPlane.mem_nhds hy) hGR).iteratedPartialDeriv
      l).eq_of_nhds.symm
  have := neBot_upperHalfPlane
  exact tendsto_nhds_unique h1 h2

/-- **The jet evolution from smooth spatial families.** Let `fields` be a classical solution of
the rescaled equations with rates continuous on an open set of times `J`, whose vorticity and
temperature are smooth families of orders three and four on `J` and whose velocity agrees on the
open upper half-plane with a smooth family `V` of order three. At every `t ∈ J` where the slices
have the regularity and symmetry of `IsOriginJetSliceAt`, the origin jets evolve by the jet
equations. -/
theorem hasOriginJetEvolutionAt_of_isSmoothFamilyOn (hJ : IsOpen J)
    (hcl : ContinuousOn cl J) (hcw : ContinuousOn cw J) (hcθ : ContinuousOn cθ J)
    (hω : IsSmoothFamilyOn 3 (fun s x ↦ fields.vorticity x s) J)
    (hθ : IsSmoothFamilyOn 4 (fun s x ↦ fields.temperature x s) J)
    (hV : IsSmoothFamilyOn 3 V J)
    (hVeq : ∀ s ∈ J, ∀ x ∈ upperHalfPlane, V s x = vorticityStreamVelocity fields x s)
    (hreg : HasClassicalVorticityStreamRegularityOn fields J)
    (heq : SatisfiesRescaledScalarEquationsOn fields cl cw cθ upperHalfPlane J)
    {t : ℝ} (ht : t ∈ J) (hslice : IsOriginJetSliceAt fields t) :
    HasOriginJetEvolutionAt fields cl cw cθ t := by
  have h0 : (0 : ℝ^2) ∈ closure upperHalfPlane := by
    rw [closure_upperHalfPlane]
    simp
  have hGω : IsSmoothFamilyOn 2 (vorticityTendencyFamily fields cl cw V) J :=
    isSmoothFamilyOn_vorticityTendency hcl hcw hω (hθ.mono (by norm_num)) (hV.mono (by norm_num))
  have hGθ : IsSmoothFamilyOn 3 (temperatureTendencyFamily fields cl cθ V) J :=
    isSmoothFamilyOn_temperatureTendency hcl hcθ hθ hV
  have hdω : ∀ s ∈ J, ∀ y ∈ upperHalfPlane, HasDerivAt (fun r ↦ fields.vorticity y r)
      (vorticityTendencyFamily fields cl cw V s y) s := by
    intro s hs y hy
    convert (hreg.vorticity_differentiableAt_time (x := y) hs).hasDerivAt using 1
    have := heq.1 hs hy
    simp only [rescaledTransportVelocity, advectiveDerivative] at this
    simp only [vorticityTendencyFamily, hVeq s hs y hy]
    linarith
  have hdθ : ∀ s ∈ J, ∀ y ∈ upperHalfPlane, HasDerivAt (fun r ↦ fields.temperature y r)
      (temperatureTendencyFamily fields cl cθ V s y) s := by
    intro s hs y hy
    convert (hreg.temperature_differentiableAt_time (x := y) hs).hasDerivAt using 1
    have := heq.2 hs hy
    simp only [rescaledTransportVelocity, advectiveDerivative] at this
    simp only [temperatureTendencyFamily, hVeq s hs y hy]
    linarith
  have hRω : EqOn (vorticityTendencyFamily fields cl cw V t)
      (rescaledVorticityTendency (cl t) (cw t) (fun x ↦ fields.vorticity x t)
        (∂[0] (fun x ↦ fields.temperature x t)) (fun x ↦ fields.streamFunction x t))
      upperHalfPlane := fun y hy ↦ by
    simp only [vorticityTendencyFamily, rescaledVorticityTendency, advectiveDerivative,
      hVeq t ht y hy, vorticityStreamVelocity]
  have hRθ : EqOn (temperatureTendencyFamily fields cl cθ V t)
      (rescaledTemperatureTendency (cl t) (cθ t) (fun x ↦ fields.temperature x t)
        (fun x ↦ fields.streamFunction x t)) upperHalfPlane := fun y hy ↦ by
    simp only [temperatureTendencyFamily, rescaledTemperatureTendency, advectiveDerivative,
      hVeq t ht y hy, vorticityStreamVelocity]
  have hjω (l : List (Fin 2)) (hl : l.length ≤ 2) :=
    IsSmoothFamilyOn.hasDerivAt_iteratedPartialDeriv l hJ isOpen_upperHalfPlane
      (hω.mono (by omega)) (hGω.mono hl) hdω ht h0
  have hjθ (l : List (Fin 2)) (hl : l.length ≤ 3) :=
    IsSmoothFamilyOn.hasDerivAt_iteratedPartialDeriv l hJ isOpen_upperHalfPlane
      (hθ.mono (by omega)) (hGθ.mono hl) hdθ ht h0
  refine ⟨hslice.jetStream, ?_, ?_, ?_, ?_⟩
  · have h := hjω [0] (by norm_num)
    rwa [iteratedPartialDeriv_eq_of_tendsto [0] ((hGω.contDiff ht).of_le (by norm_num)) hRω
      (hslice.tendsto_vorticityX (cl t) (cw t))] at h
  · have h := hjθ [0, 0] (by norm_num)
    rwa [iteratedPartialDeriv_eq_of_tendsto [0, 0] ((hGθ.contDiff ht).of_le (by norm_num)) hRθ
      (hslice.tendsto_temperatureXX (cl t) (cθ t))] at h
  · have h := hjω [0, 1] (by norm_num)
    rwa [iteratedPartialDeriv_eq_of_tendsto [0, 1] ((hGω.contDiff ht).of_le (by norm_num)) hRω
      (hslice.tendsto_vorticityXY (cl t) (cw t))] at h
  · have h := hjθ [0, 1, 0] (by norm_num)
    rwa [iteratedPartialDeriv_eq_of_tendsto [0, 1, 0] ((hGθ.contDiff ht).of_le (by norm_num)) hRθ
      (hslice.tendsto_temperatureXYX (cl t) (cθ t))] at h

end Boussinesq
