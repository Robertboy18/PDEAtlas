/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.Characteristics.Equation
public import
  PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.LocalExistence.AutomaticCharacteristicFlow
public import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.LocalExistence.CharacteristicFlow
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import PDE.FDeriv.Operators

/-!
# Local classical solutions from characteristic flows

We build the local classical solution of Evans, §3.2.4, Theorem 2, from a regular
characteristic flow. The noncharacteristic condition gives an invertible
derivative at the basepoint, and the inverse function theorem supplies local
coordinates. The contact identity identifies `Du` with the momentum in
these coordinates. Since both momentum and inverse coordinates are `C¹`,
the solution is `C²`. The boundary trace also retains the initial momentum
as the solution's gradient. `SmoothConstruction` constructs the required flow
from boundary and value data.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.4, Lemma 2, Theorem 2, equations (37)-(41).
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

open PDE (SpaceTime)

namespace NonlinearFirstOrder

noncomputable section

open scoped Topology RealInnerProductSpace NNReal
open Set

variable {k : ℕ}

section LocalExistence

variable {F : SpaceTime k → ℝ → SpaceTime k → ℝ}
  {boundary : ℝ^k → SpaceTime k} {data : ℝ^k → ℝ}
  {initialGradient : ℝ^k → SpaceTime k}

/-- Evans, §3.2.4: local existence from a regular characteristic flow.

Given compatible boundary gradients, a noncharacteristic basepoint, and
the regular characteristic flow of (31), there are open neighborhoods
`W₀` of the boundary parameter and `V` of the boundary point together with
a `C²` function `u` such that

* `F(Du,u,x)=0` on `V`,
* `u(boundary(y))=data(y)` and `Du(boundary(y))=initialGradient(y)` for `y∈W₀`, and
* every point of `V` lies in the requested ambient domain `Ω`.

Both the residual and `Du = p` are derived from the characteristic and first-variation ODEs. The
identity `Du = p ∘ coords` then gives a `C¹` derivative, hence the `C²` regularity in Evans's
Theorem 2. This theorem takes a regular characteristic flow as input; `SmoothConstruction`
constructs that flow from boundary and value data. -/
theorem exists_local_classicalSolution_of_characteristicFlow
    (Ω : Set (SpaceTime k)) (flow : LocalCharacteristicFlow F boundary data initialGradient)
    (hF : ContDiff ℝ 1 (phaseFunction (n := k + 1) F)) (y0 : ℝ^k) (hy0 : y0 ∈ flow.W)
    (hcompat : ∀ y ∈ flow.W, IsCompatibleInitialGradientAt F boundary data y (initialGradient y))
    (hnonchar : IsNoncharacteristicAt F boundary y0 (initialGradient y0) (data y0))
    (hposition : ∀ q ∈ flow.W ×ˢ Ioo (-(flow.ε : ℝ)) (flow.ε : ℝ), flow.xmap q ∈ Ω) :
    ∃ W₀ : Set (ℝ^k), IsOpen W₀ ∧ y0 ∈ W₀ ∧
      ∃ V : Set (SpaceTime k), IsOpen V ∧ boundary y0 ∈ V ∧ V ⊆ Ω ∧
        ∃ u : SpaceTime k → ℝ, ContDiffOn ℝ 2 u V ∧
          IsClassicalSolution (n := k + 1) { F := F, domain := V } u ∧
          ∀ y ∈ W₀, boundary y ∈ V ∧ u (boundary y) = data y ∧
            ∇ u (boundary y) = initialGradient y := by
  obtain ⟨e0, he0⟩ := hnonchar
  have hq0 : (y0, (0 : ℝ)) ∈ flow.W ×ˢ Ioo (-(flow.ε : ℝ)) flow.ε := ⟨hy0, flow.zero_mem_time⟩
  have hx0 : HasFDerivAt flow.xmap (e0 : (ℝ^k × ℝ) →L[ℝ] SpaceTime k) (y0, 0) :=
    he0 ▸ flow.hasFDerivAt_xmap_initial hy0
  have hx0C := flow.x_contDiff.contDiffAt (flow.box_open.mem_nhds hq0)
  -- The inverse-function chart of `xmap`, restricted to the box points where `D xmap` is
  -- invertible; `chart.symm` gives the characteristic coordinates.
  let chart := (hx0C.toOpenPartialHomeomorph flow.xmap hx0 one_ne_zero).restrOpen
    ((flow.W ×ˢ Ioo (-(flow.ε : ℝ)) flow.ε) ∩
      fderiv ℝ flow.xmap ⁻¹' range ((↑) : ((ℝ^k × ℝ) ≃L[ℝ] SpaceTime k) → _))
    ((flow.x_contDiff.continuousOn_fderiv_of_isOpen flow.box_open le_rfl).isOpen_inter_preimage
      flow.box_open ContinuousLinearEquiv.isOpen)
  have hsrc {q} (hq : q ∈ chart.source) : q ∈ flow.W ×ˢ Ioo (-(flow.ε : ℝ)) flow.ε ∧
      ∃ L : (ℝ^k × ℝ) ≃L[ℝ] SpaceTime k, HasFDerivAt flow.xmap (L : (ℝ^k × ℝ) →L[ℝ] _) q := by
    obtain ⟨-, hq, L, hL⟩ := hq
    exact ⟨hq, L, hL ▸ (flow.differentiableAt_xmap hq).hasFDerivAt⟩
  let u : SpaceTime k → ℝ := fun x ↦ flow.zmap (chart.symm x)
  -- In these coordinates the contact identity gives `Du = p`.
  have hu {x} (hx : x ∈ chart.target) :
      HasFDerivAt u (InnerProductSpace.toDual ℝ _ (flow.pmap (chart.symm x))) x ∧
        ContDiffAt ℝ 1 chart.symm x := by
    obtain ⟨hq, L, hL⟩ := hsrc (chart.map_target hx)
    refine ⟨((flow.differentiableAt_zmap hq).hasFDerivAt.comp x
      (chart.hasFDerivAt_symm hx hL)).congr_fderiv ?_, chart.contDiffAt_symm hx hL
        (flow.x_contDiff.contDiffAt (flow.box_open.mem_nhds hq))⟩
    ext v
    rw [ContinuousLinearMap.comp_apply,
      flow.fderiv_zmap_eq_inner_fderiv_xmap hq.1 (hcompat _ hq.1) hq.2, hL.fderiv]
    simp
  have hbox {x} (hx : x ∈ chart.target) := (hsrc (chart.map_target hx)).1
  have hright {x} (hx : x ∈ chart.target) : flow.xmap (chart.symm x) = x := chart.right_inv hx
  have hgrad {x} (hx : x ∈ chart.target) : ∇ u x = flow.pmap (chart.symm x) :=
    (hasGradientAt_iff_hasFDerivAt.2 (hu hx).1).gradient
  have htrace (y) (hy : (y, (0 : ℝ)) ∈ chart.source) : boundary y ∈ chart.target ∧
      u (boundary y) = data y ∧ ∇ u (boundary y) = initialGradient y := by
    have hyW := (hsrc hy).1.1
    have htarget : boundary y ∈ chart.target := flow.x_initial y hyW ▸ chart.map_source hy
    have hcoords : chart.symm (boundary y) = (y, 0) := flow.x_initial y hyW ▸ chart.left_inv hy
    refine ⟨htarget, ?_, ?_⟩
    · simp [u, hcoords, flow.z_initial y hyW]
    · rw [hgrad htarget, hcoords, flow.p_initial y hyW]
  have hsrc0 : (y0, (0 : ℝ)) ∈ chart.source :=
    ⟨hx0C.mem_toOpenPartialHomeomorph_source hx0 one_ne_zero, hq0, e0, hx0.fderiv.symm⟩
  refine ⟨(fun y ↦ (y, (0 : ℝ))) ⁻¹' chart.source, chart.open_source.preimage (by fun_prop),
    hsrc0, chart.target, chart.open_target, (htrace y0 hsrc0).1,
    fun x hx ↦ hright hx ▸ hposition _ (hbox hx), u, fun x hx ↦ ?_,
    fun x hx ↦ ⟨(hu hx).1.differentiableAt, ?_⟩, htrace⟩
  · have hp := (flow.p_contDiff.contDiffAt (flow.box_open.mem_nhds (hbox hx))).comp x (hu hx).2
    exact (contDiffAt_succ_iff_hasFDerivAt (n := 1).2 ⟨_, ⟨_, chart.open_target.mem_nhds hx,
      fun w hw ↦ (hu hw).1⟩,
        (InnerProductSpace.toDual ℝ _).contDiff.contDiffAt.comp x hp⟩).contDiffWithinAt
  · rw [hgrad hx]
    simpa [u, hright hx] using
      flow.residual_eq_zero hF (hbox hx).1 (hcompat _ (hbox hx).1) (hbox hx).2

end LocalExistence

end

end NonlinearFirstOrder
