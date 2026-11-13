/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.VorticityStream.OriginJets
public import PDE.Fluid.Boussinesq.VorticityStream.Normalization
public import PDE.FDeriv.SpaceTime.Iterated
public import PDE.Analysis.Evolution.ODE.Linear.OffCountable

/-!
# Evolution of the origin jets of a rescaled Boussinesq solution

Consider a solution of the dynamically rescaled Boussinesq equations
`ω_t + (c_l x + u)·∇ω = c_ω ω + θ_x` and `θ_t + (c_l x + u)·∇θ = c_θ θ` on the open upper
half-plane, with velocity `u = ∇^⊥ψ` and rates `c_l`, `c_ω`, `c_θ` depending on time, and write
`u_x(0)` for the horizontal derivative of the horizontal velocity at the origin. If the solution is
jointly `C³` (vorticity) and `C⁴` (temperature) in space-time at `(0, t)` and has the symmetry of
Chen and Hou and a stream function `C⁴` up to the boundary, then the jets `ω_x(0, t)`, `θ_xx(0, t)`,
`ω_xy(0, t)` and `θ_xyx(0, t)` are differentiable in `t`, with

* `d/dt ω_x(0) = (c_ω - c_l - u_x(0)) ω_x(0) + θ_xx(0)`,
* `d/dt θ_xx(0) = (c_θ - 2 c_l - 2 u_x(0)) θ_xx(0)`,
* `d/dt ω_xy(0) = (c_ω - 2 c_l) ω_xy(0) - ω_x(0)² + θ_xyx(0)`,
* `d/dt θ_xyx(0) = (c_θ - 3 c_l - u_x(0)) θ_xyx(0) - 2 ω_x(0) θ_xx(0)`.

The first two are the trace ODEs in footnote 3 of Chen and Hou, Part I. The last two are their
(4.12), which has `2 c_ω - 2 c_l` in place of `c_θ - 3 c_l` by their relation `c_θ = c_l + 2 c_ω`.
Under their normalization (2.9) the first two right sides vanish, so `ω_x(0)` and `θ_xx(0)` are
constant in time (`eqOn_traces_of_normalization`).

## Main definitions

* `IsOriginJetSliceAt`: the regularity and symmetry of one time slice used by the jet computations.
* `IsOriginJetRegularAt`: these together with joint regularity of the vorticity and the temperature
  at `(0, t)`.
* `HasOriginJetEvolutionAt`: the four jet equations at time `t` with a stream function `C⁴` up to
  the boundary, the form in which the jet evolution is used.
* `vorticityXYAtOrigin`, `temperatureXYXAtOrigin`: the mixed jets `ω_xy(0, t)` and `θ_xyx(0, t)`.

## Main results

* `hasDerivAt_iteratedPartialDeriv_of_tendsto`: the time derivative of a jet at the origin is the
  limit from the half-plane of the same jet of the right side.
* `IsOriginJetSliceAt.tendsto_vorticityX`, `IsOriginJetSliceAt.tendsto_vorticityXY`,
  `IsOriginJetSliceAt.tendsto_temperatureXX`, `IsOriginJetSliceAt.tendsto_temperatureXYX`: these
  limits, computed from one time slice.
* `IsOriginJetRegularAt.hasDerivAt_vorticityXAtOrigin`,
  `IsOriginJetRegularAt.hasDerivAt_temperatureXXAtOrigin`,
  `IsOriginJetRegularAt.hasDerivAt_vorticityXYAtOrigin`,
  `IsOriginJetRegularAt.hasDerivAt_temperatureXYXAtOrigin`: the four equations.
* `IsOriginJetRegularAt.hasOriginJetEvolutionAt`: joint regularity gives `HasOriginJetEvolutionAt`.
* `eqOn_traces_of_normalization`: under the normalization, `ω_x(0, t)` and `θ_xx(0, t)` are constant
  on `[0, t₀]`.

## How it works

The equations hold only on the open upper half-plane, so their jets cannot be evaluated at the
origin directly. Joint `C^{j+1}` regularity at `(0, t)` lets us differentiate a jet `∂^l f(0, s)` of
length `j` in `s` (`hasDerivAt_iteratedPartialDeriv_timeSlice_of_contDiffAt`); the derivative is the
same jet of `∂_t f`, which is continuous at the origin. On the half-plane near the origin `∂_t f`
equals the right side `R`, so the jet of `R` tends to this value from the half-plane, and uniqueness
of limits gives `hasDerivAt_iteratedPartialDeriv_of_tendsto`. To compute the limits of the jets of
the right sides in one time slice we expand them by the product rule on the half-plane and pass to
the limit term by term (`tendsto_partialDeriv_vorticityTendency`,
`tendsto_mixedDeriv_vorticityTendency`): `ψ_xy` tends to `-u_x(0)`
(`IsOriginJetSliceAt.tendsto_ux`), the Poisson equation gives `ψ_xyy → -ω_x(0)`
(`IsOriginJetSliceAt.tendsto_uxy`), and the symmetry of `ω` and `ψ` and the vanishing of the
coordinates at the origin send the other terms to `0`. For the temperature we first replace `∂ₓ` of
the right side by the right side of the equation of `η = θ_x`
(`IsOriginJetSliceAt.eqOn_partialDeriv_temperatureTendency`). Under the normalization the first two
derivatives vanish on `(0, t₀)`, and with continuity on `[0, t₀]` the traces are constant
(`PDE.Analysis.Evolution.eqOn_const_of_hasDerivAt_zero`).

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.1, (2.8)-(2.10) and
  footnote 3, and Section 4.2.1, (4.12).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Filter Set PDE PDE.Common IncompressibleFlow
open PDE (laplacian advectiveDerivative)
open scoped Topology

namespace Boussinesq

set_option linter.missingDocs true

/-- **Time derivatives of origin jets from the equation on the half-plane.** If `f` is jointly
`C^{j + 1}` at `(0, t)` for a word of length `j`, `∂_t f = R` near the origin on the open upper
half-plane, and the word of derivatives of `R` has the limit `L` at the origin from the
half-plane, then `t ↦ ∂^word f(0, t)` has the derivative `L` at `t`. -/
theorem hasDerivAt_iteratedPartialDeriv_of_tendsto (l : List (Fin 2)) (f : ℝ^2 × ℝ → ℝ) {t : ℝ}
    {R : ℝ^2 → ℝ} (hf : ContDiffAt ℝ (l.length + 1 : ℕ) f (0, t))
    (hR : ∀ᶠ y in 𝓝 0, y ∈ upperHalfPlane → HasDerivAt (fun s ↦ f (y, s)) (R y) t)
    {L : ℝ} (hL : Tendsto (iteratedPartialDeriv l R) (𝓝[upperHalfPlane] 0) (𝓝 L)) :
    HasDerivAt (fun s ↦ iteratedPartialDeriv l (fun y ↦ f (y, s)) 0) L t := by
  have h0 := hasDerivAt_iteratedPartialDeriv_timeSlice_of_contDiffAt l f 0 t hf
  set g : ℝ^2 → ℝ := fun y ↦ deriv (fun s ↦ f (y, s)) t
  set Φ : ℝ^2 × ℝ → ℝ := fun q ↦ iteratedPartialDeriv l (fun z ↦ f (z, q.2)) q.1
  have hΦ : ContDiffAt ℝ 1 Φ (0, t) :=
    contDiffAt_iteratedPartialDeriv_prod_spaceSlice l f 1 (0, t) (by simpa [add_comm] using hf)
  -- the jet of `g` is continuous at the origin
  have hnear : ∀ᶠ y in 𝓝 (0 : ℝ^2), iteratedPartialDeriv l g y =
      fderiv ℝ Φ (y, t) ((0 : ℝ^2), (1 : ℝ)) := by
    have hfy := (continuousAt_id.prodMk continuousAt_const).eventually
      (hf.eventually (by simp))
    have hΦy := (continuousAt_id.prodMk continuousAt_const).eventually
      (hΦ.eventually (by simp))
    filter_upwards [hfy, hΦy] with y hy hΦy'
    have h1 := hasDerivAt_iteratedPartialDeriv_timeSlice_of_contDiffAt l f y t hy
    have hinsert : HasDerivAt (fun s : ℝ ↦ (y, s)) ((0 : ℝ^2), (1 : ℝ)) t :=
      (hasDerivAt_const (x := t) (c := y)).prodMk (hasDerivAt_id t)
    have h2 := ((hΦy'.differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt t hinsert
    exact h1.unique h2
  have hcont : ContinuousAt (iteratedPartialDeriv l g) 0 := by
    refine ContinuousAt.congr ?_ (Filter.EventuallyEq.symm hnear)
    have := (hΦ.fderiv_right (m := 0) (by norm_num)).continuousAt
    have hc := ContinuousAt.comp (g := fderiv ℝ Φ) (f := fun y : ℝ^2 ↦ (y, t)) (x := 0) this
      (by fun_prop)
    exact hc.clm_apply continuousAt_const
  -- on the half-plane near the origin, `g = R`, so their jets agree
  obtain ⟨V, hV, hVR⟩ := hR.exists_mem
  obtain ⟨W, hWV, hWo, hW0⟩ := mem_nhds_iff.1 hV
  have hgR : EqOn g R (W ∩ upperHalfPlane) := fun y hy ↦ (hVR y (hWV hy.1) hy.2).deriv
  have hopen : IsOpen (W ∩ upperHalfPlane) := hWo.inter isOpen_upperHalfPlane
  have hjet : ∀ y ∈ W ∩ upperHalfPlane, iteratedPartialDeriv l g y = iteratedPartialDeriv l R y :=
    fun y hy ↦ ((eventuallyEq_of_mem (hopen.mem_nhds hy) hgR).iteratedPartialDeriv l).eq_of_nhds
  have hlim : Tendsto (iteratedPartialDeriv l R) (𝓝[upperHalfPlane] 0)
      (𝓝 (iteratedPartialDeriv l g 0)) := by
    refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    have : W ∩ upperHalfPlane ∈ 𝓝[upperHalfPlane] (0 : ℝ^2) := by
      rw [inter_comm]
      exact inter_mem_nhdsWithin _ (hWo.mem_nhds hW0)
    filter_upwards [this] with y hy
    exact hjet y hy
  have := neBot_upperHalfPlane
  rw [tendsto_nhds_unique hlim hL] at h0
  exact h0

/-- The mixed jet `ω_xy(0, t)` of the vorticity. -/
def vorticityXYAtOrigin (fields : VorticityStreamFields) (t : ℝ) : ℝ :=
  (∂[0] (∂[1] (fun x ↦ fields.vorticity x t))) 0

/-- The mixed jet `θ_xyx(0, t) = ∂ₓ∂ᵧθ_x(0, t)` of the temperature. -/
def temperatureXYXAtOrigin (fields : VorticityStreamFields) (t : ℝ) : ℝ :=
  (∂[0] (∂[1] (∂[0] (fun x ↦ fields.temperature x t)))) 0

/-- The regularity and symmetry of the slices at time `t` used by the jet computations at the
origin: the slices `C³`/`C⁴`/`C²` in space, the stream function `C⁴` up to the boundary, odd and
zero on the boundary, the vorticity odd, the temperature even and zero on the vertical axis, and
`-Δψ = ω` on the open upper half-plane. -/
structure IsOriginJetSliceAt (fields : VorticityStreamFields) (t : ℝ) : Prop where
  /-- The vorticity slice is `C³`. -/
  vorticity : ContDiff ℝ 3 (fun x ↦ fields.vorticity x t)
  /-- The temperature slice is `C⁴`. -/
  temperature : ContDiff ℝ 4 (fun x ↦ fields.temperature x t)
  /-- The stream function slice is `C²`. -/
  stream : ContDiff ℝ 2 (fun x ↦ fields.streamFunction x t)
  /-- The stream function is `C⁴` up to the boundary, odd and zero on the boundary. -/
  jetStream : IsJetStream (fun x ↦ fields.streamFunction x t)
  /-- The vorticity is odd in `x₁`. -/
  vorticity_odd : IsReflectionEigenfunctionOn upperHalfPlane 0 (-1) (fun x ↦ fields.vorticity x t)
  /-- The temperature is even in `x₁`. -/
  temperature_even : IsReflectionEigenfunctionOn upperHalfPlane 0 1 (fun x ↦ fields.temperature x t)
  /-- The temperature vanishes on the vertical axis. -/
  temperature_axis : ∀ x ∈ upperHalfPlane, x 0 = 0 → fields.temperature x t = 0
  /-- The Poisson equation. -/
  poisson : ∀ x ∈ upperHalfPlane,
    -laplacian (fun y ↦ fields.streamFunction y t) x = fields.vorticity x t

/-- The slice regularity and symmetry of `IsOriginJetSliceAt` together with joint `C³`/`C⁴`
regularity of the vorticity and temperature at `(0, t)`. -/
structure IsOriginJetRegularAt (fields : VorticityStreamFields) (t : ℝ) : Prop
    extends IsOriginJetSliceAt fields t where
  /-- Joint `C³` regularity of the vorticity at `(0, t)`. -/
  vorticity_joint : ContDiffAt ℝ 3 (fun p : ℝ^2 × ℝ ↦ fields.vorticity p.1 p.2) (0, t)
  /-- Joint `C⁴` regularity of the temperature at `(0, t)`. -/
  temperature_joint : ContDiffAt ℝ 4 (fun p : ℝ^2 × ℝ ↦ fields.temperature p.1 p.2) (0, t)

/-- The limit at the origin from the half-plane of a derivative word of a `C^k` function is its
value. -/
theorem tendsto_iteratedPartialDeriv_of_contDiff {g : ℝ^2 → ℝ} {k : ℕ} (hg : ContDiff ℝ k g)
    (l : List (Fin 2)) (hl : l.length ≤ k) :
    Tendsto (iteratedPartialDeriv l g) (𝓝[upperHalfPlane] 0)
      (𝓝 (iteratedPartialDeriv l g 0)) := by
  have h := contDiffOn_iteratedPartialDeriv isOpen_univ l (m := 0)
    ((hg.of_le (by exact_mod_cast (by omega : l.length + 0 ≤ k))).contDiffOn)
  exact ((h.continuousOn.continuousAt (by simp)).tendsto).mono_left nhdsWithin_le_nhds

/-- `u_x(0) = -ψ_xy(0)`. -/
theorem tangentialVelocityXAtOrigin_eq (fields : VorticityStreamFields) (t : ℝ) :
    tangentialVelocityXAtOrigin fields t =
      -(∂[0] (∂[1] (fun x ↦ fields.streamFunction x t))) 0 := by
  have : (fun x ↦ vorticityStreamVelocity fields x t 0) =
      fun x ↦ -(∂[1] (fun y ↦ fields.streamFunction y t)) x := by
    funext x
    simp [vorticityStreamVelocity, planarStreamVelocity]
  rw [tangentialVelocityXAtOrigin, this, partialDeriv_neg_fun]

namespace IsOriginJetSliceAt

variable {fields : VorticityStreamFields} {t : ℝ} (h : IsOriginJetSliceAt fields t)
include h

/-- The vorticity slice is a `C³` field odd in `x₁`. -/
theorem oddVorticity : IsOddJetField 3 (fun x ↦ fields.vorticity x t) :=
  ⟨IsSmoothToBoundary.of_contDiffOn h.vorticity.contDiffOn, h.vorticity_odd⟩

/-- The temperature slice is a `C⁴` field even in `x₁` and zero on the vertical axis. -/
theorem evenTemperature : IsEvenAxisJetField 4 (fun x ↦ fields.temperature x t) :=
  ⟨IsSmoothToBoundary.of_contDiffOn h.temperature.contDiffOn, h.temperature_even,
    h.temperature_axis⟩

/-- `ψ_xy → -u_x(0)` at the origin from the open upper half-plane. -/
theorem tendsto_ux : Tendsto (∂[0] (∂[1] (fun x ↦ fields.streamFunction x t)))
    (𝓝[upperHalfPlane] 0) (𝓝 (-tangentialVelocityXAtOrigin fields t)) := by
  rw [tangentialVelocityXAtOrigin_eq, neg_neg]
  exact tendsto_iteratedPartialDeriv_of_contDiff h.stream [0, 1] (by simp)

/-- `ψ_xyy → -ω_x(0)` at the origin from the open upper half-plane. -/
theorem tendsto_uxy : Tendsto (∂[0] (∂[1] (∂[1] (fun x ↦ fields.streamFunction x t))))
    (𝓝[upperHalfPlane] 0) (𝓝 (-vorticityXAtOrigin fields t)) :=
  h.jetStream.tendsto_stream_xyy h.poisson
    (tendsto_iteratedPartialDeriv_of_contDiff h.vorticity [0] (by simp))

/-- The jet `∂ₓR_ω(0)` of the vorticity tendency with the rates `c_l`, `c_ω`, as a limit from the
half-plane: `(c_ω - c_l - u_x(0)) ω_x(0) + θ_xx(0)`. -/
theorem tendsto_vorticityX (cl cw : ℝ) :
    Tendsto (∂[0] (rescaledVorticityTendency cl cw (fun x ↦ fields.vorticity x t)
        (∂[0] (fun x ↦ fields.temperature x t)) (fun x ↦ fields.streamFunction x t)))
      (𝓝[upperHalfPlane] 0)
      (𝓝 ((cw - cl - tangentialVelocityXAtOrigin fields t) * vorticityXAtOrigin fields t +
        temperatureXXAtOrigin fields t)) :=
  tendsto_partialDeriv_vorticityTendency cl cw (h.oddVorticity.mono (by norm_num))
    ((h.evenTemperature.partialDeriv_zero (k := 3)).smooth.mono (by norm_num)) h.jetStream
    (tendsto_iteratedPartialDeriv_of_contDiff h.vorticity [0] (by simp))
    (tendsto_iteratedPartialDeriv_of_contDiff h.temperature [0, 0] (by simp)) h.tendsto_ux

/-- The jet `∂ₓ∂ᵧR_ω(0)` of the vorticity tendency, as a limit from the half-plane:
`(c_ω - 2 c_l) ω_xy(0) - ω_x(0)² + θ_xyx(0)`. -/
theorem tendsto_vorticityXY (cl cw : ℝ) :
    Tendsto (∂[0] (∂[1] (rescaledVorticityTendency cl cw (fun x ↦ fields.vorticity x t)
        (∂[0] (fun x ↦ fields.temperature x t)) (fun x ↦ fields.streamFunction x t))))
      (𝓝[upperHalfPlane] 0)
      (𝓝 ((cw - 2 * cl) * vorticityXYAtOrigin fields t - vorticityXAtOrigin fields t ^ 2 +
        temperatureXYXAtOrigin fields t)) := by
  have hL := tendsto_mixedDeriv_vorticityTendency cl cw h.oddVorticity
    ((h.evenTemperature.partialDeriv_zero (k := 3)).smooth.mono (by norm_num)) h.jetStream
    (tendsto_iteratedPartialDeriv_of_contDiff h.vorticity [0] (by simp))
    (tendsto_iteratedPartialDeriv_of_contDiff h.vorticity [0, 1] (by simp))
    (tendsto_iteratedPartialDeriv_of_contDiff h.temperature [0, 1, 0] (by simp)) h.tendsto_ux
    h.tendsto_uxy
  convert hL using 2
  rw [sq]
  rfl

/-- `∂ₓR_θ = R_η(θ_x, θ_y)` near the origin for the solution slice. -/
theorem eqOn_partialDeriv_temperatureTendency (cl cθ : ℝ) :
    EqOn (∂[0] (rescaledTemperatureTendency cl cθ (fun x ↦ fields.temperature x t)
        (fun x ↦ fields.streamFunction x t)))
      (rescaledEtaTendency cl cθ (∂[0] (fun x ↦ fields.temperature x t))
        (∂[1] (fun x ↦ fields.temperature x t)) (fun x ↦ fields.streamFunction x t))
      upperHalfPlane := fun _ hx ↦
  partialDeriv_temperatureTendency_eq cl cθ ((h.temperature.of_le (by norm_num)).contDiffOn)
    (h.jetStream.smooth.contDiffOn.of_le (by norm_num)) hx

/-- The jet `∂ₓ²R_θ(0)` of the temperature tendency, as a limit from the half-plane:
`(c_θ - 2 c_l - 2 u_x(0)) θ_xx(0)`. -/
theorem tendsto_temperatureXX (cl cθ : ℝ) :
    Tendsto (iteratedPartialDeriv [0, 0] (rescaledTemperatureTendency cl cθ
        (fun x ↦ fields.temperature x t) (fun x ↦ fields.streamFunction x t)))
      (𝓝[upperHalfPlane] 0)
      (𝓝 ((cθ - 2 * cl - 2 * tangentialVelocityXAtOrigin fields t) *
        temperatureXXAtOrigin fields t)) := by
  have hL := tendsto_partialDeriv_etaTendency cl cθ
    (h.evenTemperature.partialDeriv_zero (k := 3) |>.mono (by norm_num))
    (h.evenTemperature.partialDeriv_one (k := 3) |>.mono (by norm_num)) h.jetStream
    (tendsto_iteratedPartialDeriv_of_contDiff h.temperature [0, 0] (by simp)) h.tendsto_ux
  exact hL.congr' (eventuallyEq_nhdsWithin_of_eqOn
    (eqOn_partialDeriv isOpen_upperHalfPlane (h.eqOn_partialDeriv_temperatureTendency _ _)
      0).symm)

/-- The jet `∂ₓ∂ᵧ∂ₓR_θ(0)` of the temperature tendency, as a limit from the half-plane:
`(c_θ - 3 c_l - u_x(0)) θ_xyx(0) - 2 ω_x(0) θ_xx(0)`. -/
theorem tendsto_temperatureXYX (cl cθ : ℝ) :
    Tendsto (iteratedPartialDeriv [0, 1, 0] (rescaledTemperatureTendency cl cθ
        (fun x ↦ fields.temperature x t) (fun x ↦ fields.streamFunction x t)))
      (𝓝[upperHalfPlane] 0)
      (𝓝 ((cθ - 3 * cl - tangentialVelocityXAtOrigin fields t) * temperatureXYXAtOrigin fields t -
        2 * vorticityXAtOrigin fields t * temperatureXXAtOrigin fields t)) := by
  have hL := tendsto_mixedDeriv_etaTendency cl cθ
    (h.evenTemperature.partialDeriv_zero (k := 3))
    (h.evenTemperature.partialDeriv_one (k := 3) |>.mono (by norm_num)) h.jetStream
    (tendsto_iteratedPartialDeriv_of_contDiff h.temperature [0, 0] (by simp))
    (tendsto_iteratedPartialDeriv_of_contDiff h.temperature [0, 1, 0] (by simp)) h.tendsto_ux
    h.tendsto_uxy
  exact hL.congr' (eventuallyEq_nhdsWithin_of_eqOn
    (eqOn_partialDeriv isOpen_upperHalfPlane (eqOn_partialDeriv isOpen_upperHalfPlane
      (h.eqOn_partialDeriv_temperatureTendency _ _) 1) 0).symm)

end IsOriginJetSliceAt

/-- **The evolution of the origin jets** of a solution of the rescaled equations with the rates
`c_l`, `c_ω`, `c_θ` at the time `t`: the stream function is `C⁴` up to the boundary, odd and zero on
the boundary, and the jets `ω_x(0)`, `θ_xx(0)`, `ω_xy(0)`, `θ_xyx(0)` have the time derivatives

* `d/dt ω_x(0) = (c_ω - c_l - u_x(0)) ω_x(0) + θ_xx(0)`,
* `d/dt θ_xx(0) = (c_θ - 2 c_l - 2 u_x(0)) θ_xx(0)`,
* `d/dt ω_xy(0) = (c_ω - 2 c_l) ω_xy(0) - ω_x(0)² + θ_xyx(0)`,
* `d/dt θ_xyx(0) = (c_θ - 3 c_l - u_x(0)) θ_xyx(0) - 2 ω_x(0) θ_xx(0)`.

Joint space-time regularity at `(0, t)` gives it (`IsOriginJetRegularAt.hasOriginJetEvolutionAt`),
and so do slices whose spatial derivatives are jointly continuous in space and time
(`hasOriginJetEvolutionAt_of_isSmoothFamilyOn`), the form in which local well-posedness provides
it. -/
structure HasOriginJetEvolutionAt (fields : VorticityStreamFields) (cl cw cθ : ℝ → ℝ) (t : ℝ) :
    Prop where
  /-- The stream function is `C⁴` up to the boundary, odd and zero on the boundary. -/
  jetStream : IsJetStream (fun x ↦ fields.streamFunction x t)
  /-- The vorticity trace equation. -/
  vorticityX : HasDerivAt (vorticityXAtOrigin fields)
    ((cw t - cl t - tangentialVelocityXAtOrigin fields t) * vorticityXAtOrigin fields t +
      temperatureXXAtOrigin fields t) t
  /-- The temperature trace equation. -/
  temperatureXX : HasDerivAt (temperatureXXAtOrigin fields)
    ((cθ t - 2 * cl t - 2 * tangentialVelocityXAtOrigin fields t) *
      temperatureXXAtOrigin fields t) t
  /-- The mixed vorticity jet equation. -/
  vorticityXY : HasDerivAt (vorticityXYAtOrigin fields)
    ((cw t - 2 * cl t) * vorticityXYAtOrigin fields t - vorticityXAtOrigin fields t ^ 2 +
      temperatureXYXAtOrigin fields t) t
  /-- The mixed temperature jet equation. -/
  temperatureXYX : HasDerivAt (temperatureXYXAtOrigin fields)
    ((cθ t - 3 * cl t - tangentialVelocityXAtOrigin fields t) * temperatureXYXAtOrigin fields t -
      2 * vorticityXAtOrigin fields t * temperatureXXAtOrigin fields t) t

namespace IsOriginJetRegularAt

variable {fields : VorticityStreamFields} {t : ℝ} (h : IsOriginJetRegularAt fields t)
include h

/-- The vorticity equation gives `∂_t ω = R_ω` near the origin on the half-plane. -/
theorem eventually_hasDerivAt_vorticity (cl cw : ℝ → ℝ)
    (heq : SatisfiesRescaledVorticityEquationAtTime fields cl cw upperHalfPlane t) :
    ∀ᶠ y in 𝓝 0, y ∈ upperHalfPlane → HasDerivAt (fun s ↦ fields.vorticity y s)
      (rescaledVorticityTendency (cl t) (cw t) (fun x ↦ fields.vorticity x t)
        (∂[0] (fun x ↦ fields.temperature x t)) (fun x ↦ fields.streamFunction x t) y) t := by
  have hnear := (continuousAt_id.prodMk continuousAt_const).eventually
    (h.vorticity_joint.eventually (by simp))
  filter_upwards [hnear] with y hy hyH
  have hd : DifferentiableAt ℝ (fun s ↦ fields.vorticity y s) t :=
    (hy.differentiableAt (by norm_num)).comp t (by fun_prop)
  convert hd.hasDerivAt using 1
  have := heq hyH
  simp only [rescaledVorticityTendency]
  have hV : (fun z ↦ rescaledTransportVelocity fields cl z t) =
      fun z ↦ cl t • z + planarStreamVelocity (fun x ↦ fields.streamFunction x t) z := rfl
  rw [hV] at this
  linarith

/-- The temperature equation gives `∂_t θ = R_θ` near the origin on the half-plane. -/
theorem eventually_hasDerivAt_temperature (cl cθ : ℝ → ℝ)
    (heq : SatisfiesRescaledTemperatureEquationAtTime fields cl cθ upperHalfPlane t) :
    ∀ᶠ y in 𝓝 0, y ∈ upperHalfPlane → HasDerivAt (fun s ↦ fields.temperature y s)
      (rescaledTemperatureTendency (cl t) (cθ t) (fun x ↦ fields.temperature x t)
        (fun x ↦ fields.streamFunction x t) y) t := by
  have hnear := (continuousAt_id.prodMk continuousAt_const).eventually
    (h.temperature_joint.eventually (by simp))
  filter_upwards [hnear] with y hy hyH
  have hd : DifferentiableAt ℝ (fun s ↦ fields.temperature y s) t :=
    (hy.differentiableAt (by norm_num)).comp t (by fun_prop)
  convert hd.hasDerivAt using 1
  have := heq hyH
  simp only [rescaledTemperatureTendency]
  have hV : (fun z ↦ rescaledTransportVelocity fields cl z t) =
      fun z ↦ cl t • z + planarStreamVelocity (fun x ↦ fields.streamFunction x t) z := rfl
  rw [hV] at this
  linarith

/-- **The vorticity trace ODE**: `d/dt ω_x(0) = (c_ω - c_l - u_x(0)) ω_x(0) + θ_xx(0)`. -/
theorem hasDerivAt_vorticityXAtOrigin (cl cw : ℝ → ℝ)
    (heq : SatisfiesRescaledVorticityEquationAtTime fields cl cw upperHalfPlane t) :
    HasDerivAt (vorticityXAtOrigin fields)
      ((cw t - cl t - tangentialVelocityXAtOrigin fields t) * vorticityXAtOrigin fields t +
        temperatureXXAtOrigin fields t) t :=
  hasDerivAt_iteratedPartialDeriv_of_tendsto [0] (fun p ↦ fields.vorticity p.1 p.2)
    (h.vorticity_joint.of_le (by norm_num)) (h.eventually_hasDerivAt_vorticity cl cw heq)
    (h.toIsOriginJetSliceAt.tendsto_vorticityX (cl t) (cw t))

/-- **The mixed vorticity jet ODE**: `d/dt ω_xy(0) = (c_ω - 2 c_l) ω_xy(0) - ω_x(0)² +
θ_xyx(0)`. -/
theorem hasDerivAt_vorticityXYAtOrigin (cl cw : ℝ → ℝ)
    (heq : SatisfiesRescaledVorticityEquationAtTime fields cl cw upperHalfPlane t) :
    HasDerivAt (vorticityXYAtOrigin fields)
      ((cw t - 2 * cl t) * vorticityXYAtOrigin fields t - vorticityXAtOrigin fields t ^ 2 +
        temperatureXYXAtOrigin fields t) t :=
  hasDerivAt_iteratedPartialDeriv_of_tendsto [0, 1] (fun p ↦ fields.vorticity p.1 p.2)
    h.vorticity_joint (h.eventually_hasDerivAt_vorticity cl cw heq)
    (h.toIsOriginJetSliceAt.tendsto_vorticityXY (cl t) (cw t))

/-- **The temperature trace ODE**: `d/dt θ_xx(0) = (c_θ - 2 c_l - 2 u_x(0)) θ_xx(0)`. -/
theorem hasDerivAt_temperatureXXAtOrigin (cl cθ : ℝ → ℝ)
    (heq : SatisfiesRescaledTemperatureEquationAtTime fields cl cθ upperHalfPlane t) :
    HasDerivAt (temperatureXXAtOrigin fields)
      ((cθ t - 2 * cl t - 2 * tangentialVelocityXAtOrigin fields t) *
        temperatureXXAtOrigin fields t) t :=
  hasDerivAt_iteratedPartialDeriv_of_tendsto [0, 0] (fun p ↦ fields.temperature p.1 p.2)
    (h.temperature_joint.of_le (by norm_num)) (h.eventually_hasDerivAt_temperature cl cθ heq)
    (h.toIsOriginJetSliceAt.tendsto_temperatureXX (cl t) (cθ t))

/-- **The mixed temperature jet ODE**: `d/dt θ_xyx(0) = (c_θ - 3 c_l - u_x(0)) θ_xyx(0) -
2 ω_x(0) θ_xx(0)`. -/
theorem hasDerivAt_temperatureXYXAtOrigin (cl cθ : ℝ → ℝ)
    (heq : SatisfiesRescaledTemperatureEquationAtTime fields cl cθ upperHalfPlane t) :
    HasDerivAt (temperatureXYXAtOrigin fields)
      ((cθ t - 3 * cl t - tangentialVelocityXAtOrigin fields t) * temperatureXYXAtOrigin fields t -
        2 * vorticityXAtOrigin fields t * temperatureXXAtOrigin fields t) t :=
  hasDerivAt_iteratedPartialDeriv_of_tendsto [0, 1, 0] (fun p ↦ fields.temperature p.1 p.2)
    h.temperature_joint (h.eventually_hasDerivAt_temperature cl cθ heq)
    (h.toIsOriginJetSliceAt.tendsto_temperatureXYX (cl t) (cθ t))

/-- Joint regularity at `(0, t)` and the rescaled equations at `t` give the evolution of the
origin jets. -/
theorem hasOriginJetEvolutionAt (cl cw cθ : ℝ → ℝ)
    (hω : SatisfiesRescaledVorticityEquationAtTime fields cl cw upperHalfPlane t)
    (hθ : SatisfiesRescaledTemperatureEquationAtTime fields cl cθ upperHalfPlane t) :
    HasOriginJetEvolutionAt fields cl cw cθ t where
  jetStream := h.jetStream
  vorticityX := h.hasDerivAt_vorticityXAtOrigin cl cw hω
  temperatureXX := h.hasDerivAt_temperatureXXAtOrigin cl cθ hθ
  vorticityXY := h.hasDerivAt_vorticityXYAtOrigin cl cw hω
  temperatureXYX := h.hasDerivAt_temperatureXYXAtOrigin cl cθ hθ

end IsOriginJetRegularAt

/-- **The normalization freezes the traces**: for a normalized solution whose origin jets evolve by
the jet equations on `(0, t₀)` (`HasOriginJetEvolutionAt`) and whose traces are continuous on
`[0, t₀]`, `ω_x(0, t)` and `θ_xx(0, t)` are constant on `[0, t₀]`. -/
theorem eqOn_traces_of_normalization {fields : VorticityStreamFields} {cl cw cθ : ℝ → ℝ}
    {t₀ : ℝ} (hjet : ∀ t ∈ Ioo 0 t₀, HasOriginJetEvolutionAt fields cl cw cθ t)
    (hnorm : ∀ t ∈ Ioo 0 t₀, SatisfiesRescalingNormalizationAt fields cl cw cθ t)
    (hω : ContinuousOn (vorticityXAtOrigin fields) (Icc 0 t₀))
    (hθ : ContinuousOn (temperatureXXAtOrigin fields) (Icc 0 t₀)) :
    ∀ t ∈ Icc 0 t₀, vorticityXAtOrigin fields t = vorticityXAtOrigin fields 0 ∧
      temperatureXXAtOrigin fields t = temperatureXXAtOrigin fields 0 := by
  have h1 := PDE.Analysis.Evolution.eqOn_const_of_hasDerivAt_zero hω fun t ht ↦ by
    have := (hjet t ht).vorticityX
    rwa [vorticity_trace_ode_rhs_eq_zero_of_normalization fields cl cw cθ t (hnorm t ht)] at this
  have h2 := PDE.Analysis.Evolution.eqOn_const_of_hasDerivAt_zero hθ fun t ht ↦ by
    have := (hjet t ht).temperatureXX
    have hz := temperature_trace_ode_rhs_eq_zero_of_normalization fields cl cw cθ t (hnorm t ht)
    rw [show cθ t - 2 * cl t - 2 * tangentialVelocityXAtOrigin fields t =
      cθ t - 2 * (cl t + tangentialVelocityXAtOrigin fields t) by ring, hz] at this
    exact this
  exact fun t ht ↦ ⟨h1 t ht, h2 t ht⟩

end Boussinesq
