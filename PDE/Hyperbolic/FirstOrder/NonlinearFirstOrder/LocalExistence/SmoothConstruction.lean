/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.LocalExistence.ClassicalSolution
import PDE.Analysis.Calculus.LocalExtension
import PDE.Analysis.ODE.SmoothDependence.InitialData
import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.LocalExistence.CharacteristicFamily
import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.LocalExistence.InitialMomentum

/-!
# Local C² solutions from constructed characteristics

For `F(Du,u,x)=0`, a globally C² Hamiltonian has a C¹ characteristic vector
field. Its constructed flow and state derivative give a C¹ family
from compatible C¹ boundary, value, and momentum fields. The variational
equation and residual preservation imply contact transport. After restricting
to the requested open ambient domain, the noncharacteristic condition gives
inverse characteristic coordinates. In these coordinates `Du` is the C¹
momentum field, so the solution is C².

The final theorem starts with local C² boundary and value data, one
compatible noncharacteristic base momentum, and a Hamiltonian that is C²
only near this initial phase point. A cutoff gives a global representative
of its germ. The implicit function theorem constructs a C¹ momentum field
for that representative, and the characteristic construction gives a C²
solution with the prescribed base gradient. Continuity of `(Du,u,x)` lets
us shrink the solution neighborhood to where the two Hamiltonians agree.
Uniqueness is in `LocalExistence.Uniqueness`.

The construction is that of Evans, §3.2.3, Lemma 1, and §3.2.4, Lemma 2 and Theorem 2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.3, Lemma 1; §3.2.4, Lemma 2, Theorem 2.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

open PDE (SpaceTime)

noncomputable section

open Filter Metric Set
open scoped NNReal RealInnerProductSpace Topology

namespace NonlinearFirstOrder

variable {k : ℕ}

/-- Construct a local C² classical solution from local compatible C¹ boundary,
value, and momentum fields for a globally C² Hamiltonian.

The general ODE construction identifies the boundary derivative of
the C¹ characteristic family. Its variational equation proves contact
transport without exchanging second derivatives of the initial fields.
The momentum in inverse characteristic coordinates is C¹, giving a C² solution.
The gradient trace records the supplied initial momentum along the boundary. -/
theorem exists_local_classicalSolution_of_contDiff_two (Ω : Set (SpaceTime k)) (hΩ : IsOpen Ω)
    (F : SpaceTime k → ℝ → SpaceTime k → ℝ) (hF : ContDiff ℝ 2 (phaseFunction (n := k + 1) F))
    (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ) (initialGradient : ℝ^k → SpaceTime k)
    (W : Set (ℝ^k)) (hW : IsOpen W) (y0 : ℝ^k) (hy0 : y0 ∈ W)
    (hboundary : ContDiffOn ℝ 1 boundary W) (hdata : ContDiffOn ℝ 1 data W)
    (hgradient : ContDiffOn ℝ 1 initialGradient W) (hbase : boundary y0 ∈ Ω)
    (hcompat : ∀ y ∈ W, IsCompatibleInitialGradientAt F boundary data y (initialGradient y))
    (hnonchar : IsNoncharacteristicAt F boundary y0 (initialGradient y0) (data y0)) :
    ∃ W₀ : Set (ℝ^k), IsOpen W₀ ∧ y0 ∈ W₀ ∧
      ∃ V : Set (SpaceTime k), IsOpen V ∧ boundary y0 ∈ V ∧ V ⊆ Ω ∧
        ∃ u : SpaceTime k → ℝ,
          ContDiffOn ℝ 2 u V ∧
          IsClassicalSolution (n := k + 1) { F := F, domain := V } u ∧
          ∀ y ∈ W₀, boundary y ∈ V ∧ u (boundary y) = data y ∧
            ∇ u (boundary y) = initialGradient y := by
  let initial : ℝ^k → SpaceTime k × (ℝ × SpaceTime k) :=
    characteristicInitialState boundary data initialGradient
  have hi : ContDiffOn ℝ 1 initial W := hgradient.prodMk (hdata.prodMk hboundary)
  obtain ⟨U, hU, hyU, hUW, T, hT, curve, hcurve, hflow⟩ :=
    PDE.Analysis.ODE.exists_local_contDiff_one_family_with_initialData
      (characteristicVectorField F) (contDiff_characteristicVectorField F hF) initial W hW hi y0 hy0
  let box : Set (ℝ^k × ℝ) := U ×ˢ Ioo (-T) T
  let q0 : ℝ^k × ℝ := (y0, 0)
  let coefficient : ℝ^k × ℝ → ℝ := fun q ↦ characteristicDz F (curve q)
  have hzero : (0 : ℝ) ∈ Ioo (-T) T := ⟨neg_lt_zero.mpr hT, hT⟩
  have hq0 : q0 ∈ box := ⟨hyU, hzero⟩
  have hboxOpen : IsOpen box := hU.prod isOpen_Ioo
  have hcurveAt : ContDiffAt ℝ 1 curve q0 := hcurve.contDiffAt (hboxOpen.mem_nhds hq0)
  have hcoefficientAt : ContinuousAt coefficient q0 :=
    ((contDiff_characteristicDz F hF).contDiffAt.comp q0 hcurveAt).continuousAt
  have hxAt : ContinuousAt (fun q ↦ (curve q).2.2) q0 := hcurveAt.continuousAt.snd.snd
  have hxbase : (curve q0).2.2 ∈ Ω := (hflow y0 hyU).1 ▸ hbase
  have hgoodN : (({q : ℝ^k × ℝ | ‖coefficient q‖ < ‖coefficient q0‖ + 1} ∩
        {q : ℝ^k × ℝ | (curve q).2.2 ∈ Ω}) ∩ box) ∈ 𝓝 q0 :=
    inter_mem (inter_mem (hcoefficientAt.norm (Iio_mem_nhds (lt_add_one ‖coefficient q0‖)))
      (hxAt (hΩ.mem_nhds hxbase))) (hboxOpen.mem_nhds hq0)
  obtain ⟨UY, hUY, UT, hUT, hproduct⟩ := mem_nhds_prod_iff.mp hgoodN
  obtain ⟨W₁, hW₁sub, hW₁open, hyW₁⟩ := _root_.mem_nhds_iff.mp hUY
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.mem_nhds_iff.mp (inter_mem hUT (Ioo_mem_nhds (neg_lt_zero.mpr hT) hT))
  have htimeSub : Ioo (-δ) δ ⊆ UT ∩ Ioo (-T) T := by
    simpa [Real.ball_eq_Ioo] using hball
  have hzeroδ : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hW₁U : W₁ ⊆ U := fun y hy ↦
    (hproduct (show (y, (0 : ℝ)) ∈ UY ×ˢ UT from ⟨hW₁sub hy, (htimeSub hzeroδ).1⟩)).2.1
  have hsub : W₁ ×ˢ Ioo (-δ) δ ⊆ U ×ˢ Ioo (-T) T := fun yt hyt ↦ ⟨hW₁U hyt.1, (htimeSub hyt.2).2⟩
  let contactBound : ℝ≥0 := ⟨‖coefficient q0‖ + 1, by positivity⟩
  have hDzBound : ∀ y ∈ W₁, ∀ s ∈ Ioo (-δ) δ, ‖valueDerivative (n := k + 1) F
          (curve (y, s)).1 (curve (y, s)).2.1 (curve (y, s)).2.2‖ ≤
            contactBound := fun y hy s hs ↦ by
    rw [← characteristicDz_eq_DzF F (hF.differentiable (by norm_num)) (curve (y, s))]
    exact (hproduct (show (y, s) ∈ UY ×ˢ UT from ⟨hW₁sub hy, (htimeSub hs).1⟩)).1.1.le
  let regular : LocalCharacteristicFlow F boundary data initialGradient :=
    LocalCharacteristicFlow.ofContDiffOneCharacteristicFamily
      F boundary data initialGradient W₁ hW₁open ⟨δ, hδ⟩ curve hF (hcurve.mono hsub)
      (fun y hy ↦ (hflow y (hW₁U hy)).1)
      (fun y hy s hs ↦ ((hflow y (hW₁U hy)).2 s (htimeSub hs).2).1)
      (fun y hy dy s hs ↦ ((hflow y (hW₁U hy)).2 s (htimeSub hs).2).2 dy)
      (fun y hy ↦ hcompat y (hUW (hW₁U hy))) contactBound hDzBound
  exact exists_local_classicalSolution_of_characteristicFlow
    Ω regular (hF.of_le (by norm_num)) y0 hyW₁ (fun y hy ↦ hcompat y (hUW (hW₁U hy))) hnonchar
    (fun q hq ↦ (hproduct ⟨hW₁sub hq.1, (htimeSub hq.2).1⟩).1.2)

/-- Local C² boundary and value data give a C² classical solution for a
Hamiltonian that is C² only near the compatible noncharacteristic initial phase.

A global representative of the Hamiltonian's germ supplies the constructed
momentum field and flow. Its solution has `Du(boundary(y0))=p0`. Continuity of
`(Du,u,x)` then gives a smaller open solution neighborhood on which the
representative agrees with the original Hamiltonian. The boundary neighborhood
is also restricted, retaining its value trace and the requested ambient domain.
This is a local existence theorem, with no uniqueness conclusion. -/
theorem exists_local_classicalSolution_of_contDiff_two_boundary_data (Ω : Set (SpaceTime k))
    (hΩ : IsOpen Ω) (F : SpaceTime k → ℝ → SpaceTime k → ℝ) (boundary : ℝ^k → SpaceTime k)
    (data : ℝ^k → ℝ) (W : Set (ℝ^k)) (hW : IsOpen W) (hboundary : ContDiffOn ℝ 2 boundary W)
    (hdata : ContDiffOn ℝ 2 data W) (y0 : ℝ^k) (hy0 : y0 ∈ W) (p0 : SpaceTime k)
    (hF : ContDiffAt ℝ 2 (phaseFunction (n := k + 1) F) (p0, (data y0, boundary y0)))
    (hbase : boundary y0 ∈ Ω) (hcompat : IsCompatibleInitialGradientAt F boundary data y0 p0)
    (hnonchar : IsNoncharacteristicAt F boundary y0 p0 (data y0)) :
    ∃ W₀ : Set (ℝ^k), IsOpen W₀ ∧ y0 ∈ W₀ ∧
      ∃ V : Set (SpaceTime k), IsOpen V ∧ boundary y0 ∈ V ∧ V ⊆ Ω ∧
        ∃ u : SpaceTime k → ℝ,
          ContDiffOn ℝ 2 u V ∧
          IsClassicalSolution (n := k + 1) { F := F, domain := V } u ∧
          ∇ u (boundary y0) = p0 ∧
          ∀ y ∈ W₀, boundary y ∈ V ∧ u (boundary y) = data y := by
  obtain ⟨G, hG, _, heq⟩ := hF.exists_contDiff_compactSupport_eventuallyEq
  let FG : SpaceTime k → ℝ → SpaceTime k → ℝ := fun p z x ↦ G (p, (z, x))
  have hFG : ContDiff ℝ 2 (phaseFunction FG) := hG
  have heqFG : phaseFunction F =ᶠ[𝓝 (p0, (data y0, boundary y0))] phaseFunction FG := heq
  have hvalue : F p0 (data y0) (boundary y0) = FG p0 (data y0) (boundary y0) := heqFG.eq_of_nhds
  have hcompatFG : IsCompatibleInitialGradientAt FG boundary data y0 p0 :=
    ⟨hvalue.symm.trans hcompat.1, hcompat.2⟩
  have hpFG : momentumGradient F p0 (data y0) (boundary y0) =
      momentumGradient FG p0 (data y0) (boundary y0) :=
    momentumGradient_eq_of_phaseFunction_eventuallyEq F FG p0 (data y0) (boundary y0) heqFG
  have hnoncharFG : IsNoncharacteristicAt FG boundary y0 p0 (data y0) := by
    simpa only [IsNoncharacteristicAt, characteristicInitialDerivative, hpFG] using hnonchar
  obtain ⟨U, hU, hyU, hUW, initialGradient, hp, hpbase, hcompatible, _⟩ :=
    exists_local_compatible_initialGradient 1 (by norm_num) FG (hFG.of_le (by norm_num))
      boundary data W hW hboundary hdata y0 hy0 p0 hcompatFG hnoncharFG
  obtain ⟨W₁, hW₁, hyW₁, V, hV, hxV, hVΩ, u, hu, hclassical, hgradientTrace⟩ :=
    exists_local_classicalSolution_of_contDiff_two Ω hΩ FG hFG
      boundary data initialGradient U hU y0 hyU
      ((hboundary.of_le (by norm_num)).mono hUW)
      ((hdata.of_le (by norm_num)).mono hUW) hp hbase hcompatible (hpbase ▸ hnoncharFG)
  have hp0 : ∇ u (boundary y0) = p0 := ((hgradientTrace y0 hyW₁).2.2).trans hpbase
  have htrace : ∀ y ∈ W₁, boundary y ∈ V ∧ u (boundary y) = data y :=
    fun y hy ↦ ⟨(hgradientTrace y hy).1, (hgradientTrace y hy).2.1⟩
  obtain ⟨N, hNsub, hN, hqN⟩ := _root_.mem_nhds_iff.mp heqFG
  let phaseU : SpaceTime k → SpaceTime k × (ℝ × SpaceTime k) := fun x ↦ (∇ u x, (u x, x))
  have hphaseBase : phaseU (boundary y0) = (p0, (data y0, boundary y0)) := by
    simp only [phaseU, hp0, (htrace y0 hyW₁).2]
  have hDu : ContinuousAt (fderiv ℝ u) (boundary y0) :=
    (hu.continuousOn_fderiv_of_isOpen hV (by norm_num)).continuousAt (hV.mem_nhds hxV)
  have hgradient : ContinuousAt (∇ u) (boundary y0) :=
    (InnerProductSpace.toDual ℝ (SpaceTime k)).symm.continuous.continuousAt.comp hDu
  have huAt : ContinuousAt u (boundary y0) := (hu.contDiffAt (hV.mem_nhds hxV)).continuousAt
  have hphaseAt : ContinuousAt phaseU (boundary y0) :=
    hgradient.prodMk (huAt.prodMk continuousAt_id)
  have hphaseN : phaseU ⁻¹' N ∈ 𝓝 (boundary y0) := hphaseAt (hphaseBase ▸ hN.mem_nhds hqN)
  obtain ⟨V₀, hV₀sub, hV₀, hxV₀⟩ := _root_.mem_nhds_iff.mp (inter_mem (hV.mem_nhds hxV) hphaseN)
  let W₀ : Set (ℝ^k) := (W ∩ boundary ⁻¹' V₀) ∩ W₁
  have hW₀ : IsOpen W₀ := (hboundary.continuousOn.isOpen_inter_preimage hW hV₀).inter hW₁
  have hyW₀ : y0 ∈ W₀ := ⟨⟨hy0, hxV₀⟩, hyW₁⟩
  have hV₀V : V₀ ⊆ V := fun x hx ↦ (hV₀sub hx).1
  have hclassicalF : IsClassicalSolution (n := k + 1) { F := F, domain := V₀ } u := fun x hx ↦
    ⟨(hclassical x (hV₀V hx)).1, Eq.trans (hNsub (hV₀sub hx).2) (hclassical x (hV₀V hx)).2⟩
  exact ⟨W₀, hW₀, hyW₀, V₀, hV₀, hxV₀, hV₀V.trans hVΩ, u, hu.mono hV₀V, hclassicalF, hp0,
    fun y hy ↦ ⟨hy.1.2, (htrace y hy.2).2⟩⟩

end NonlinearFirstOrder

end
