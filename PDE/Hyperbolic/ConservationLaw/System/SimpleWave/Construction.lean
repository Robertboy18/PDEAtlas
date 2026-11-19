/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Characteristics.LocalData
public import PDE.Hyperbolic.ConservationLaw.System.SimpleWave
public import PDE.Hyperbolic.ConservationLaw.System.SimpleWave.IntegralCurve

/-!
# Local simple waves constructed from the flux and scalar data

At a strictly hyperbolic state of a C² flux, an ordered characteristic field
has a C² integral curve `R`. For C¹ scalar data `g` with `g(x₀) = 0`, invert
the characteristics

`x = y + t * characteristicSpeed flux k (R (g y))`.

The solution is `u(t,x) = R(g(ξ(t,x)))`, where `ξ` is the constructed inverse
footpoint. It is C¹, solves the conservative system, and attains the initial
data `R ∘ g` continuously. The theorem gives a positive local lifespan and
strict ordering of characteristics on an interval of initial labels.

Only the flux germ at the base state and the data germ at `x₀` are used.
The initial vector data are the scalar profile along the constructed integral
curve; an arbitrary vector profile need not be a simple wave.

The solution is a `k`-simple wave of Evans, §11.2.1, (3)-(6), with `v = R`. Its phase `g ∘ ξ`
solves the scalar law (7), and we solve that law by its straight characteristics, as in
Example 5 of §3.2.5.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.1, equations (3)-(9); §3.2.5(b), Example 5,
  equations (56)-(61).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Metric Set PDE.Common
open scoped Topology

namespace PDE.Hyperbolic.ConservationLaw.System

open Scalar

/-- A C² flux germ at a strictly hyperbolic state and C¹ scalar data construct a
local classical simple wave for any ordered characteristic family.

The curve, characteristic footpoint, spacetime neighborhood, and positive
lifespan are all outputs. The spatial Jacobian and strict ordering certify
noncrossing, and the characteristic formula identifies the transported data. -/
theorem exists_local_simple_wave {m : ℕ} {flux : ℝ^m → ℝ^m} {q₀ : ℝ^m}
    (hflux : ContDiffAt ℝ 2 flux q₀) (hhyper : IsStrictlyHyperbolicAt flux q₀) (k : Fin m)
    {g : ℝ → ℝ} {x₀ : ℝ} (hg : ContDiffAt ℝ 1 g x₀) (hg₀ : g x₀ = 0) :
    ∃ R : ℝ → ℝ^m, ∃ ε T δ : ℝ, ∃ U : Set (ℝ^2), ∃ ξ : ℝ^2 → ℝ,
      let a := characteristicSpeed flux k ∘ R
      let φ := g ∘ ξ
      let u := simpleWave R φ
      0 < ε ∧ 0 < T ∧ 0 < δ ∧ R 0 = q₀ ∧
      ContDiffOn ℝ 2 R (Ioo (-ε) ε) ∧ ContDiffOn ℝ 1 a (Ioo (-ε) ε) ∧
      (∀ s ∈ Ioo (-ε) ε,
        IsStrictlyHyperbolicAt flux (R s) ∧
        Module.End.HasEigenvector (fderiv ℝ flux (R s)).toLinearMap
          (characteristicSpeed flux k (R s)) (deriv R s)) ∧
      IsOpen U ∧ !₂[0, x₀] ∈ U ∧ ContDiffOn ℝ 1 ξ U ∧
      ContDiffOn ℝ 1 φ U ∧ ContDiffOn ℝ 1 u U ∧
      MapsTo φ U (Ioo (-ε) ε) ∧ ConservationFootRelationOn a g ξ U ∧
      (∀ p ∈ U, (∂[0] φ) p + a (φ p) * (∂[1] φ) p = 0) ∧
      IsClassicalSolutionOn flux U u ∧
      (∀ x, !₂[0, x] ∈ U →
        u !₂[0, x] = R (g x) ∧
        Tendsto (fun t : ℝ ↦ u !₂[t, x]) (𝓝 0) (𝓝 (R (g x)))) ∧
      (∀ t, |t| < T →
        StrictMonoOn (conservationCharPosition a g t) (ball x₀ δ) ∧
        ∀ x ∈ ball x₀ δ,
          HasDerivAt (conservationCharPosition a g t)
            (1 + t * deriv a (g x) * deriv g x) x ∧
          0 < 1 + t * deriv a (g x) * deriv g x ∧
          !₂[t, conservationCharPosition a g t x] ∈ U ∧
          ξ !₂[t, conservationCharPosition a g t x] = x ∧
          u !₂[t, conservationCharPosition a g t x] = R (g x)) ∧
      ∀ p : ℝ^2, |p 0| < T → |p 1 - x₀| < δ → p ∈ U := by
  obtain ⟨r, R, ε, hε, hR₀, _, hR, ha, hcurve⟩ :=
    exists_local_characteristic_integral_curve hflux hhyper k
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
  have ha₀ : ContDiffAt ℝ 1 (characteristicSpeed flux k ∘ R) (g x₀) :=
    hg₀ ▸ ha.contDiffAt (isOpen_Ioo.mem_nhds hzero)
  obtain ⟨U, ξ, T, δ, hU, hpU, hT, hδ, hlocal, hinitial, hchars, hrect⟩ :=
    exists_local_characteristics_of_contDiffAt ha₀ hg
      (show Ioo (-ε) ε ∈ 𝓝 (g x₀) from hg₀ ▸ isOpen_Ioo.mem_nhds hzero)
  let φ := g ∘ ξ
  let u := simpleWave R φ
  have hstate (p : ℝ^2) (hp : p ∈ U) : φ p ∈ Ioo (-ε) ε := (hlocal p hp).2.2.1
  have hφ (p : ℝ^2) (hp : p ∈ U) : ContDiffAt ℝ 1 φ p := (hlocal p hp).2.1
  have hu (p : ℝ^2) (hp : p ∈ U) : ContDiffAt ℝ 1 u p :=
    ((hR.contDiffAt (isOpen_Ioo.mem_nhds (hstate p hp))).of_le (by norm_num)).comp p (hφ p hp)
  have heigen (s : ℝ) (hs : s ∈ Ioo (-ε) ε) :
      Module.End.HasEigenvector (fderiv ℝ flux (R s)).toLinearMap
        (characteristicSpeed flux k (R s)) (deriv R s) :=
    (hcurve s hs).2.1.deriv ▸ (hcurve s hs).2.2
  refine ⟨R, ε, T, δ, U, ξ, hε, hT, hδ, hR₀, hR, ha,
    fun s hs ↦ ⟨(hcurve s hs).1, heigen s hs⟩, hU, hpU, fun p hp ↦ (hlocal p hp).1.contDiffWithinAt,
    fun p hp ↦ (hφ p hp).contDiffWithinAt, fun p hp ↦ (hu p hp).contDiffWithinAt, hstate,
    fun p hp ↦ (hlocal p hp).2.2.2.1, fun p hp ↦ (hlocal p hp).2.2.2.2, ?_, fun x hx ↦ ?_,
    fun t ht ↦ ⟨(hchars t ht).1, fun x hx ↦ ?_⟩, hrect⟩
  · exact ⟨fun p hp ↦ (hu p hp).differentiableAt_one,
      fun p hp ↦ (hcurve _ (hstate p hp)).1.1, fun p hp ↦ fluxResidual_simpleWave_eq_zero
      (speed := characteristicSpeed flux k ∘ R) (hcurve _ (hstate p hp)).1.1
      ((hR.contDiffAt (isOpen_Ioo.mem_nhds (hstate p hp))).differentiableAt (by norm_num))
      (hφ p hp).differentiableAt_one
      (by
        simpa only [curveTangent, Function.comp_def, φ, ContinuousLinearMap.coe_coe] using
          (heigen _ (hstate p hp)).apply_eq_smul) (hlocal p hp).2.2.2.2⟩
  · have hinit : u !₂[0, x] = R (g x) := congrArg R (hinitial x hx)
    exact ⟨hinit, hinit ▸ (hu _ hx).continuousAt.tendsto.comp
      (by fun_prop : ContinuousAt (fun t : ℝ ↦ !₂[t, x]) 0).tendsto⟩
  · obtain ⟨hd, hpos, hp, hξ⟩ := (hchars t ht).2 x hx
    exact ⟨hd, hpos, hp, hξ, congrArg (fun y ↦ R (g y)) hξ⟩

end PDE.Hyperbolic.ConservationLaw.System
