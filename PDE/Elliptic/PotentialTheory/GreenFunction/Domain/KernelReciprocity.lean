/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.NewtonRepresentation
import PDE.Elliptic.PotentialTheory.FundamentalSolution.Similarity
import PDE.Analysis.Calculus.LocalExtension.Support
import PDE.DistributionTheory.TestFunction.IntegrationByParts
import PDE.FDeriv.Laplacian.Congruence

/-!
# Reciprocity of the fundamental-solution boundary flux

For distinct poles `x, y` in a bounded open domain with C¹ graph boundary,
`integral_kernel_cross_normalFlux_eq_zero` proves that the antisymmetric boundary flux
`Φ(z - x) ∂_ν Φ(z - y) - Φ(z - y) ∂_ν Φ(z - x)` is integrable with integral zero. Evans's proof of
§2.2.4(a), Theorem 13, applies Green's identity to `G(x, ·)` and `G(y, ·)` on
`U - [B(x, ε) ∪ B(y, ε)]`, his (31), and the poles contribute `G(y, x)` and `G(x, y)`; the same
two-pole computation for `Φ(· - x)` and `Φ(· - y)` gives this lemma, which `symmetry_of_correctors`
uses. We prove it without ε-balls or boundary limits.

## How it works

We replace `Φ(· - y)` by a smooth compactly supported `V` that agrees with it on the closure of `Ω`
outside a small ball about `y` (`ContDiffOn.exists_contDiff_compactSupport_eqOn_annulus`). A smooth
function `a` with compact support in `Ω \ {x}` that equals `Φ(· - x)` near `y` evaluates the volume
term: integration by parts and the pole identity
`PotentialTheory.integral_fundamentalSolution_sub_mul_laplacian` give
`∫_Ω Φ(z - x) ΔV(z) dz = -Φ(y - x)`. The Newton representation `newton_representation` of `V` at `x`
then gives `Φ(x - y) = ∫ (Φ(z - x) ∂_ν Φ(z - y) - Φ(z - y) ∂_ν Φ(z - x)) dS + Φ(y - x)`, and the
integral vanishes because the fundamental solution is even
(`PotentialTheory.fundamentalSolution_eq_of_norm_eq`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(a), Theorem 13 (Symmetry of Green's function) and its
  proof, (31), pp. 35-36.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (laplacian)

namespace PotentialTheory.GreenFunction.Domain

open Filter Set MeasureTheory SobolevSpace SobolevSpace.Boundary
open SobolevSpace.Trace.C1 Geometry.SurfaceMeasure
open scoped Topology Gradient

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : C1ExtensionAtlas (m + 1) Ω]

/-- The antisymmetric normal flux of two distinct interior fundamental poles
has zero total boundary integral. -/
theorem integral_kernel_cross_normalFlux_eq_zero
    (hn : 2 ≤ m + 1) (hgraph : HasC1GraphBoundary Ω)
    {x y : ℝ^(m + 1)} (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y) :
    let Kx := fun z ↦ fundamentalSolution (m + 1) (z - x)
    let Ky := fun z ↦ fundamentalSolution (m + 1) (z - y)
    Integrable (fun z ↦ Kx z * normalFlux (Ω := Ω) (∇ Ky) z -
      Ky z * normalFlux (Ω := Ω) (∇ Kx) z) (surfaceMeasure Ω) ∧
      (∫ z, Kx z * normalFlux (Ω := Ω) (∇ Ky) z -
        Ky z * normalFlux (Ω := Ω) (∇ Kx) z ∂surfaceMeasure Ω) = 0 := by
  let Kx := fun z ↦ fundamentalSolution (m + 1) (z - x)
  let Ky := fun z ↦ fundamentalSolution (m + 1) (z - y)
  have hK {p z : ℝ^(m + 1)} (hz : z ≠ p) :
      ContDiffAt ℝ 2 (fun w ↦ fundamentalSolution (m + 1) (w - p)) z := by
    simpa only [one_smul] using
      (contDiffAt_fundamentalSolution_smul_sub (m + 1) zero_lt_one p z hz).of_le (by simp)
  have hlap {p z : ℝ^(m + 1)} (hz : z ≠ p) :
      laplacian (fun w ↦ fundamentalSolution (m + 1) (w - p)) z = 0 := by
    simpa only [one_smul] using
      laplacian_fundamentalSolution_smul_sub_eq_zero (m + 1) zero_lt_one p z hz
  have hKx : ContDiffOn ℝ 2 Kx (Ω \ {x}) := fun z hz ↦
    (hK (by simpa only [mem_singleton_iff] using hz.2)).contDiffWithinAt
  obtain ⟨a, ha, hac, has, hnear⟩ :=
    hKx.exists_contDiff_tsupport_subset_eventuallyEq
      (hΩ.isOpen.sdiff isClosed_singleton) ⟨hy, by simpa using hxy.symm⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hΩ.isOpen.mem_nhds hy) (inter_mem hnear (isOpen_ne.mem_nhds hxy.symm)))
  have hsmall {z : ℝ^(m + 1)} (hz : z ∈ Metric.ball y r) :
      z ∈ Ω ∧ Kx z = a z ∧ z ≠ x := hball hz
  obtain ⟨M, _, hbound⟩ := hΩ.bounded.isCompact_closure.isBounded.subset_ball_lt 0 y
  have hM : 0 < M := by simpa using hbound (subset_closure hy)
  have hkernel : ContDiffOn ℝ 2 (fundamentalSolution (m + 1)) ({0}ᶜ) := fun z hz ↦
    ((contDiffAt_fundamentalSolution (m + 1) z hz).of_le (by simp)).contDiffWithinAt
  obtain ⟨A, hA, _, heqA⟩ :=
    hkernel.exists_contDiff_compactSupport_eqOn_annulus (half_pos hr)
      (by linarith : 0 < M + 1)
  let V := fun z ↦ A (z - y)
  have hV : ContDiff ℝ 2 V := hA.comp (contDiff_id.sub contDiff_const)
  have hVc : ContDiffUpToBoundary 2 V Ω :=
    ContDiffUpToBoundary.of_contDiff hV hΩ.bounded
  have hupper {z : ℝ^(m + 1)} (hz : z ∈ closure Ω) : ‖z - y‖ < M + 1 := by
    linarith [show ‖z - y‖ < M by simpa [dist_eq_norm] using hbound hz]
  have hgerm {z : ℝ^(m + 1)} (hlo : r / 2 < ‖z - y‖)
      (hhi : ‖z - y‖ < M + 1) : V =ᶠ[𝓝 z] Ky := by
    have hopen : IsOpen {w : ℝ^(m + 1) | r / 2 < ‖w - y‖ ∧ ‖w - y‖ < M + 1} :=
      isOpen_Ioo.preimage ((continuous_id.sub continuous_const).norm)
    filter_upwards [hopen.mem_nhds ⟨hlo, hhi⟩] with w hw
    exact heqA (w - y) hw.1.le hw.2.le
  have halap {z : ℝ^(m + 1)} (hz : z ∈ Metric.ball y r) : laplacian a z = 0 := by
    have heq : EqOn a Kx (Metric.ball y r) := fun w hw ↦ (hsmall hw).2.1.symm
    rw [EuclideanLaplacian.laplacian_congr_nhds
      (heq.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz))]
    exact hlap (hsmall hz).2.2
  have haoff {z : ℝ^(m + 1)} (hz : z ∉ Ω) : a =ᶠ[𝓝 z] fun _ ↦ 0 :=
    notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (has h).1)
  have hvlarge {z : ℝ^(m + 1)} (hz : z ∈ Ω) (hrz : r ≤ ‖z - y‖) :
      V z = Ky z ∧ laplacian V z = 0 := by
    have hg := hgerm (lt_of_lt_of_le (half_lt_self hr) hrz) (hupper (subset_closure hz))
    refine ⟨hg.eq_of_nhds, ?_⟩
    rw [EuclideanLaplacian.laplacian_congr_nhds hg]
    refine hlap fun heq ↦ ?_
    simp only [heq, sub_self, norm_zero] at hrz
    linarith
  have hweight : (∫ z in Ω, Kx z * laplacian V z) = -Kx y := by
    calc
      (∫ z in Ω, Kx z * laplacian V z) = ∫ z in Ω, a z * laplacian V z := by
        refine setIntegral_congr_fun hΩ.isOpen.measurableSet fun z hz ↦ ?_
        by_cases hzr : ‖z - y‖ < r
        · rw [(hsmall (by simpa [Metric.mem_ball, dist_eq_norm])).2.1]
        · rw [(hvlarge hz (not_lt.mp hzr)).2, mul_zero, mul_zero]
      _ = ∫ z, a z * laplacian V z :=
        setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun z hz ↦ by rw [(haoff hz).eq_of_nhds, zero_mul])
      _ = ∫ z, laplacian a z * V z :=
        PDE.DistributionTheory.integral_mul_laplacian_eq V ha hV hac
      _ = ∫ z, Ky z * laplacian a z := by
        refine integral_congr_ae (.of_forall fun z ↦ ?_)
        dsimp only
        by_cases hz : z ∈ Ω
        · by_cases hzr : ‖z - y‖ < r
          · rw [halap (by simpa [Metric.mem_ball, dist_eq_norm]), zero_mul, mul_zero]
          · rw [(hvlarge hz (not_lt.mp hzr)).1, mul_comm]
        · rw [EuclideanLaplacian.laplacian_congr_nhds (haoff hz), PDE.laplacian_const,
            zero_mul, mul_zero]
      _ = -a y := integral_fundamentalSolution_sub_mul_laplacian hn ha hac y
      _ = -Kx y := congrArg Neg.neg hnear.eq_of_nhds.symm
  have hfar {z : ℝ^(m + 1)} (hz : z ∈ frontier Ω ∨ z = x) : r ≤ ‖z - y‖ := by
    by_contra! hzr
    have h := hsmall (show z ∈ Metric.ball y r by simpa [Metric.mem_ball, dist_eq_norm])
    rcases hz with hz | rfl
    · exact (hΩ.isOpen.frontier_eq ▸ hz).2 h.1
    · exact h.2.2 rfl
  have hsurface : (fun z ↦ Kx z *
      normalFlux (Ω := Ω) (hVc.of_le (show 1 ≤ 2 by omega)).completedGradient z -
        V z * normalFlux (Ω := Ω) (∇ Kx) z) =ᵐ[surfaceMeasure Ω]
      fun z ↦ Kx z * normalFlux (Ω := Ω) (∇ Ky) z -
        Ky z * normalFlux (Ω := Ω) (∇ Kx) z := by
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with z hz
    have hg := hgerm (lt_of_lt_of_le (half_lt_self hr) (hfar (Or.inl hz)))
      (hupper (frontier_subset_closure hz))
    simp only [normalFlux_eq_inner _ hz]
    rw [(hVc.of_le (show 1 ≤ 2 by omega)).completedGradient_eq_gradient_extension
        hΩ.isOpen (hV.of_le (by norm_num)) (fun _ _ ↦ rfl) (frontier_subset_closure hz),
      hg.gradient_eq, hg.eq_of_nhds]
  obtain ⟨_, hb, heq⟩ := newton_representation hn hgraph hVc hV.continuous.continuousOn hx
  refine ⟨hb.congr hsurface, ?_⟩
  have hvx := hgerm (lt_of_lt_of_le (half_lt_self hr) (hfar (Or.inr rfl)))
    (hupper (subset_closure hx))
  rw [integral_congr_ae hsurface, hweight, hvx.eq_of_nhds] at heq
  linarith [show Ky x = Kx y from fundamentalSolution_eq_of_norm_eq (norm_sub_rev x y)]

end PotentialTheory.GreenFunction.Domain
