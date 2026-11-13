/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.PairedRepresentation
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Area.PairedWeighted
import PDE.Analysis.Calculus.EndpointQuotient

/-!
# Interior normal limits of the Green gradient

For a weakly harmonic `H¹` corrector `φ` continuous on the closure with boundary values `Φ(y - x)`,
`exists_green_representation_with_inward_gradient_of_corrector` gives an `L²` density `q` with
`u(x) = ∫ q u dS - ∫ G Δu`, where `G = greenKernel x φ`, that also describes the gradient of `G`
near the boundary: at almost every boundary point `y`, `∇G(y - t ν(y)) → -q(y) ν(y)` as `t → 0⁺`.
`exists_green_representation_with_normal_derivative_of_local_graph` constructs the corrector on a
bounded open C¹ graph domain, shows that `G` is continuous on the closure minus `x` and vanishes on
the boundary, and adds that `-q(y)` is the derivative of `s ↦ G(y + s ν(y))` at `s = 0` within
`s ≤ 0`. This is Evans's formula (28) in §2.2.4(a) with `∂G/∂ν = -q` obtained as a limit from
inside.

The paired surface-kernel limit identifies the inward gradient of the Green kernel almost everywhere
on the boundary, and the paired `C²` remainder has the same gradient limit from either side and
cancels. The density is chosen once for the corrector, before the boundary point or normal
parameter.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(a), the definition of Green's function for the region
  `U` and the representation formula (28), p. 34.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PotentialTheory.GreenFunction.Domain

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Boundary SobolevSpace.Trace.C1
open SobolevSpace.Boundary.Geometry.SurfaceMeasure
open scoped ENNReal Gradient Sobolev Topology

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
variable [H : C1ExtensionAtlas (m + 1) Ω]

/-- The inward gradient of a Green kernel has an almost-everywhere normal
limit given by a surface L² density. Only C¹ graph geometry is used. -/
theorem exists_green_representation_with_inward_gradient_of_corrector
    (hm : 1 ≤ m) (hgraph : HasC1GraphBoundary Ω)
    {x : ℝ^(m + 1)} (hx : x ∈ Ω)
    (U : H¹(Ω)) {φ : ℝ^(m + 1) → ℝ}
    (hrep : baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] φ)
    (hcφ : ContinuousOn φ (closure Ω))
    (hbφ : EqOn φ (fun y ↦ fundamentalSolution (m + 1) (y - x)) (frontier Ω))
    (hweak : ∀ t : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) U)
        (derivCoordCLM i t)) = 0) :
    ∃ q : BoundaryL2 (Ω := Ω),
      (∀ (u : ℝ^(m + 1) → ℝ) (hu : ContDiffUpToBoundary 2 u Ω),
        ContinuousOn u (closure Ω) →
        Integrable (fun y ↦ q y * u y) (surfaceMeasure Ω) ∧
        IntegrableOn (fun y ↦ greenKernel x φ y * PDE.laplacian u y) Ω ∧
        u x = (∫ y, q y * u y ∂surfaceMeasure Ω) -
          ∫ y in Ω, greenKernel x φ y * PDE.laplacian u y) ∧
      ∀ᵐ y ∂surfaceMeasure Ω,
      ∀ hy : y ∈ frontier Ω,
        Tendsto
          (fun t : ℝ ↦ gradient (greenKernel x φ) (y - t • outwardUnitNormal ⟨y, hy⟩))
          (𝓝[>] 0) (𝓝 (-(q y • outwardUnitNormal ⟨y, hy⟩))) ∧
        ∀ᶠ t : ℝ in 𝓝[>] 0,
          DifferentiableAt ℝ (greenKernel x φ) (y - t • outwardUnitNormal ⟨y, hy⟩) := by
  let : Fact (0 < m + 1) := ⟨by omega⟩
  obtain ⟨q, R, hR, hformula, hpair⟩ :=
    exists_paired_gradient_greenKernel_of_corrector hm hgraph hx U hrep hcφ hbφ hweak
  have hq : Integrable (q : ℝ^(m + 1) → ℝ) (surfaceMeasure Ω) :=
    (Lp.memLp q).integrable (by norm_num)
  have hcR : Continuous (gradient R) :=
    (InnerProductSpace.toDual ℝ (ℝ^(m + 1))).symm.continuous.comp
      (hR.continuous_fderiv (by norm_num))
  refine ⟨q, hformula, ?_⟩
  filter_upwards
    [ae_tendsto_integral_paired_gradient_fundamentalSolution_smul hm hq] with y hy
  intro hyfront
  let ν := outwardUnitNormal (Ω := Ω) ⟨y, hyfront⟩
  have hin : Tendsto (fun t : ℝ ↦ y - t • ν) (𝓝[>] 0) (𝓝 y) :=
    (Continuous.tendsto' (by fun_prop) 0 y (by simp)).mono_left nhdsWithin_le_nhds
  have hout : Tendsto (fun t : ℝ ↦ y + t • ν) (𝓝[>] 0) (𝓝 y) :=
    (Continuous.tendsto' (by fun_prop) 0 y (by simp)).mono_left nhdsWithin_le_nhds
  have hlim := (((hy hyfront).add ((hcR.tendsto y).comp hin)).sub
    ((hcR.tendsto y).comp hout)).neg
  have hfinal := hlim.congr' ((hpair ⟨y, hyfront⟩).mono fun _ ht ↦ ht.2.symm)
  exact ⟨by simpa only [add_sub_cancel_right] using hfinal,
    (hpair ⟨y, hyfront⟩).mono fun _ ht ↦ ht.1⟩

omit H in
/-- A bounded C¹ graph domain has a Green kernel whose inward gradient
and outward one-sided normal derivative are represented by the same surface
L² density that occurs in its Green formula. -/
theorem exists_green_representation_with_normal_derivative_of_local_graph
    (hn : 2 ≤ m + 1) (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω) {x : ℝ^(m + 1)} (hx : x ∈ Ω) :
    letI : C1ExtensionAtlas (m + 1) Ω := hgraph.c1ExtensionAtlas hopen hbounded
    ∃ φ : ℝ^(m + 1) → ℝ, ∃ q : BoundaryL2 (Ω := Ω),
      LaplacianEquation.IsHarmonicPDE (m + 1) φ Ω ∧
      ContinuousOn φ (closure Ω) ∧
      EqOn φ (fun y ↦ fundamentalSolution (m + 1) (y - x)) (frontier Ω) ∧
      ContinuousOn (greenKernel x φ) (closure Ω \ {x}) ∧
      EqOn (greenKernel x φ) 0 (frontier Ω) ∧
      (∀ (u : ℝ^(m + 1) → ℝ) (hu : ContDiffUpToBoundary 2 u Ω),
        ContinuousOn u (closure Ω) →
        Integrable (fun y ↦ q y * u y) (surfaceMeasure Ω) ∧
        IntegrableOn (fun y ↦ greenKernel x φ y * PDE.laplacian u y) Ω ∧
        u x = (∫ y, q y * u y ∂surfaceMeasure Ω) -
          ∫ y in Ω, greenKernel x φ y * PDE.laplacian u y) ∧
      ∀ᵐ y ∂surfaceMeasure Ω, ∀ hy : y ∈ frontier Ω,
        Tendsto
          (fun t : ℝ ↦ gradient (greenKernel x φ) (y - t • outwardUnitNormal ⟨y, hy⟩))
          (𝓝[>] 0) (𝓝 (-(q y • outwardUnitNormal ⟨y, hy⟩))) ∧
        HasDerivWithinAt
          (fun s : ℝ ↦ greenKernel x φ (y + s • outwardUnitNormal ⟨y, hy⟩))
          (-q y) (Iic 0) 0 := by
  let : C1ExtensionAtlas (m + 1) Ω := hgraph.c1ExtensionAtlas hopen hbounded
  let : Fact (0 < m + 1) := ⟨by omega⟩
  obtain ⟨U, φ, hrep, hh, hc, hb, hw⟩ :=
    exists_harmonic_corrector_of_local_graph hn hopen hbounded hgraph hx
  obtain ⟨q, hformula, hgradient⟩ :=
    exists_green_representation_with_inward_gradient_of_corrector
      (by omega) hgraph hx U hrep hc hb hw
  have hzero : EqOn (greenKernel x φ) 0 (frontier Ω) := fun y hy ↦ by
    simp only [greenKernel, hb hy, sub_self, Pi.zero_apply]
  have hΦ {y : ℝ^(m + 1)} (hyx : y ≠ x) :
      ContinuousAt (fun z ↦ fundamentalSolution (m + 1) (z - x)) y :=
    (contDiffAt_fundamentalSolution (m + 1) (y - x) (sub_ne_zero.mpr hyx)).continuousAt.comp
      (f := fun z : ℝ^(m + 1) ↦ z - x) (continuousAt_id.sub continuousAt_const)
  have hcontinuous : ContinuousOn (greenKernel x φ) (closure Ω \ {x}) := fun y hy ↦
    (hΦ hy.2).continuousWithinAt.sub ((hc y hy.1).mono sdiff_subset)
  refine ⟨φ, q, hh, hc, hb, hcontinuous, hzero, hformula, ?_⟩
  filter_upwards [hgradient] with y hy
  intro hyfront
  obtain ⟨hlim, hdiff⟩ := hy hyfront
  let ν := outwardUnitNormal (Ω := Ω) ⟨y, hyfront⟩
  let k : ℝ → ℝ := fun t ↦ greenKernel x φ (y - t • ν)
  let k' : ℝ → ℝ := fun t ↦ inner ℝ (gradient (greenKernel x φ) (y - t • ν)) (-ν)
  have hd : ∀ᶠ t : ℝ in 𝓝[>] 0, HasDerivAt k (k' t) t := by
    filter_upwards [hdiff] with t ht
    have hray : HasDerivAt (fun s : ℝ ↦ y - s • ν) (-ν) t := by
      simpa only [one_smul, zero_sub, Pi.sub_apply, id_eq] using
        (hasDerivAt_const t y).fun_sub ((hasDerivAt_id t).smul_const ν)
    exact ht.hasGradientAt.hasFDerivAt.comp_hasDerivAt t hray
  have htrace : Tendsto k' (𝓝[>] 0) (𝓝 (q y)) := by
    simpa only [k', ν, inner_neg_neg, real_inner_smul_left,
      real_inner_self_eq_norm_sq, norm_outwardUnitNormal, one_pow, mul_one] using
        hlim.inner (𝕜 := ℝ) (tendsto_const_nhds (x := -ν))
  have hyx : y ≠ x := fun heq ↦ (hopen.frontier_eq ▸ hyfront).2 (heq ▸ hx)
  have hcG : ContinuousWithinAt (greenKernel x φ) (closure Ω) y :=
    (hΦ hyx).continuousWithinAt.sub (hc y (frontier_subset_closure hyfront))
  have hin : Tendsto (fun t : ℝ ↦ y - t • ν) (𝓝[>] 0) (𝓝 y) :=
    (Continuous.tendsto' (by fun_prop) 0 y (by simp)).mono_left nhdsWithin_le_nhds
  have hinClosure : Tendsto (fun t : ℝ ↦ y - t • ν)
      (𝓝[>] 0) (𝓝[closure Ω] y) :=
    tendsto_nhdsWithin_iff.mpr ⟨hin,
      (eventually_normal_approach_mem (Ω := Ω) ⟨y, hyfront⟩).mono
        fun _ ht ↦ subset_closure ht.1⟩
  have hck : ContinuousWithinAt k (Ici 0) 0 := by
    apply continuousWithinAt_Ioi_iff_Ici.mp
    simpa only [ContinuousWithinAt, k, zero_smul, sub_zero, Function.comp_def] using
      hcG.tendsto.comp hinClosure
  have hright := PDE.Analysis.Calculus.hasDerivWithinAt_Ici_of_derivative_trace hck hd htrace
  have hmap : MapsTo (fun s : ℝ ↦ -s) (Iic 0) (Ici 0) := fun s hs ↦ neg_nonneg.mpr hs
  refine ⟨hlim, ?_⟩
  simpa only [Function.comp_def, Pi.neg_apply, id_eq, mul_neg_one, k,
    neg_smul, sub_neg_eq_add] using
      hright.comp_of_eq 0 (hasDerivWithinAt_id (0 : ℝ) (Iic 0)).neg hmap (neg_zero.symm)

end PotentialTheory.GreenFunction.Domain
