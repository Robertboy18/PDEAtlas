/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.ImplicitFunction.Stationary
public import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.CompleteIntegral.Basic
public import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.Characteristics.Envelope

/-!
# Construction of nondegenerate stationary envelopes

At a stationary parameter with invertible parameter Hessian, the implicit
function theorem constructs a locally unique C¹ selector. Composing the
solution family with this selector gives a C² classical solution. Its
derivative is the spatial derivative of the selected member of the family;
the parameter contribution vanishes by the derived stationarity equation.
This derivative identity supplies the extra derivative of the envelope.

Only local nondegeneracy is needed. The result applies to an arbitrary number
of parameters, and in particular to complete integrals. The envelope is the one of Evans,
§3.1.2, equations (10)-(13), and the classical equation is his Theorem 1; there the selector
`φ` is assumed, while here it comes from the invertible parameter Hessian.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.1.2, Theorem 1, equations (10)-(13).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology Gradient

namespace NonlinearFirstOrder

variable {n m : ℕ} [Fact (0 < n)]

/-- The envelope and its selector are constructed from a stationary base
point and the invertibility of the parameter Hessian. All regularity,
stationarity, and classical PDE conclusions are derived. -/
theorem exists_local_stationary_envelope {U : Set (ℝ^n)} {A : Set (ℝ^m)} {F : ℝ^n → ℝ → ℝ^n → ℝ}
    {u : ℝ^n → ℝ^m → ℝ} {x₀ : ℝ^n} {a₀ : ℝ^m} (hU : IsOpen U) (hA : IsOpen A) (hx₀ : x₀ ∈ U)
    (ha₀ : a₀ ∈ A) (hu : ContDiffOn ℝ 2 (fun q : ℝ^n × ℝ^m ↦ u q.1 q.2) (U ×ˢ A))
    (hsol : ∀ a ∈ A, IsClassicalSolution { F := F, domain := U } (fun x ↦ u x a))
    (hstationary : fderiv ℝ (u x₀) a₀ = 0)
    (hessian : (fderiv ℝ (fun a ↦ fderiv ℝ (u x₀) a) a₀).IsInvertible) :
    ∃ (V : Set (ℝ^n)) (φ : ℝ^n → ℝ^m),
      IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧ φ x₀ = a₀ ∧ MapsTo φ V A ∧
      ContDiffOn ℝ 1 φ V ∧
      (∀ x ∈ V, fderiv ℝ (u x) (φ x) = 0) ∧
      ContDiffOn ℝ 2 (fun x ↦ u x (φ x)) V ∧
      (∀ x ∈ V, fderiv ℝ (fun y ↦ u y (φ y)) x =
        fderiv ℝ (fun y ↦ u y (φ x)) x) ∧
      IsClassicalSolution { F := F, domain := V } (fun x ↦ u x (φ x)) ∧
      (∀ᶠ q : ℝ^n × ℝ^m in 𝓝 (x₀, a₀),
        fderiv ℝ (u q.1) q.2 = 0 ↔ φ q.1 = q.2) := by
  have hu₀ : ContDiffAt ℝ 2 (fun q : ℝ^n × ℝ^m ↦ u q.1 q.2) (x₀, a₀) :=
    hu.contDiffAt ((hU.prod hA).mem_nhds ⟨hx₀, ha₀⟩)
  obtain ⟨φ, hφ₀, hφ, hstat, hunique⟩ :=
    PDE.Analysis.exists_stationary_selector hu₀ hstationary hessian
  have hφA : ∀ᶠ x in 𝓝 x₀, φ x ∈ A :=
    hφ.continuousAt (by simpa only [hφ₀] using hA.mem_nhds ha₀)
  have hnear : ∀ᶠ x in 𝓝 x₀,
      x ∈ U ∧ φ x ∈ A ∧ ContDiffAt ℝ 1 φ x ∧ fderiv ℝ (u x) (φ x) = 0 := by
    filter_upwards [hU.mem_nhds hx₀, hφA, hφ.eventually (by simp), hstat] with x hx hA hφ hs
    exact ⟨hx, hA, hφ, hs⟩
  obtain ⟨V, hVnear, hV, hxV⟩ := mem_nhds_iff.mp hnear
  have hVU : V ⊆ U := fun x hx ↦ (hVnear hx).1
  have hVA : MapsTo φ V A := fun x hx ↦ (hVnear hx).2.1
  have hφV : ContDiffOn ℝ 1 φ V := fun x hx ↦ (hVnear hx).2.2.1.contDiffWithinAt
  have hstatV : ∀ x ∈ V, fderiv ℝ (u x) (φ x) = 0 := fun x hx ↦ (hVnear hx).2.2.2
  have huV : ContDiffOn ℝ 1 (fun q : ℝ^n × ℝ^m ↦ u q.1 q.2) (V ×ˢ A) :=
    (hu.of_le (by norm_num)).mono (prod_mono hVU Subset.rfl)
  have henv : ContDiffOn ℝ 1 (fun x ↦ u x (φ x)) V :=
    fun x hx ↦ ((huV.contDiffAt ((hV.prod hA).mem_nhds ⟨hx, hVA hx⟩)).comp x
      (contDiffAt_id.prodMk (hVnear hx).2.2.1)).contDiffWithinAt
  have hderiv : ∀ x ∈ V, fderiv ℝ (fun y ↦ u y (φ y)) x = fderiv ℝ (fun y ↦ u y (φ x)) x :=
    fun x hx ↦ PDE.Analysis.fderiv_stationary_envelope
      (huV.contDiffAt ((hV.prod hA).mem_nhds ⟨hx, hVA hx⟩)).differentiableAt_one
      (hVnear hx).2.2.1.differentiableAt_one (hstatV x hx)
  have hDx : ContDiffOn ℝ 1 (fun x ↦ (fderiv ℝ (fun q : ℝ^n × ℝ^m ↦ u q.1 q.2) (x, φ x)).comp
        (ContinuousLinearMap.inl ℝ (ℝ^n) (ℝ^m))) V :=
    ((hu.fderiv_of_isOpen (hU.prod hA) (by norm_num)).comp
      (contDiffOn_id.prodMk hφV) (fun _ hx ↦ ⟨hVU hx, hVA hx⟩)).clm_comp contDiffOn_const
  have henv₂ : ContDiffOn ℝ 2 (fun x ↦ u x (φ x)) V := by
    apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) hV).2
    refine ⟨henv.differentiableOn (by simp), by simp, hDx.congr fun x hx ↦ ?_⟩
    have hdu : DifferentiableAt ℝ (fun q : ℝ^n × ℝ^m ↦ u q.1 q.2) (x, φ x) :=
      (huV.contDiffAt ((hV.prod hA).mem_nhds ⟨hx, hVA hx⟩)).differentiableAt_one
    have hslice : HasFDerivAt (fun y : ℝ^n ↦ u y (φ x))
        ((fderiv ℝ (fun q : ℝ^n × ℝ^m ↦ u q.1 q.2) (x, φ x)).comp
          (ContinuousLinearMap.inl ℝ (ℝ^n) (ℝ^m))) x := by
      have hfull := hdu.hasFDerivAt
      have hinl := hasFDerivAt_prodMk_left (𝕜 := ℝ) x (φ x)
      exact hfull.comp x hinl
    exact (hderiv x hx).trans hslice.fderiv
  refine ⟨V, φ, hV, hxV, hVU, hφ₀, hVA, hφV, hstatV, henv₂, hderiv, ?_, hunique⟩
  · apply envelope_isClassicalSolution hV hA huV hφV hVA
    · exact fun a ha x hx ↦ (hsol a ha x (hVU hx)).2
    · exact hstatV

/-- In particular a nondegenerate stationary member of a complete integral
has a local classical envelope. The complete-integral rank condition is
certified separately from the Hessian condition for this branch. -/
theorem IsCompleteIntegral.exists_local_envelope {pde : Equation n} {A : Set (ℝ^n)}
    {u : ℝ^n → ℝ^n → ℝ} (hcomplete : IsCompleteIntegral pde A u) {x₀ a₀ : ℝ^n}
    (hx₀ : x₀ ∈ pde.domain) (ha₀ : a₀ ∈ A) (hstationary : fderiv ℝ (u x₀) a₀ = 0)
    (hessian : (fderiv ℝ (fun a ↦ fderiv ℝ (u x₀) a) a₀).IsInvertible) :
    ∃ (V : Set (ℝ^n)) (φ : ℝ^n → ℝ^n),
      IsOpen V ∧ x₀ ∈ V ∧ V ⊆ pde.domain ∧ φ x₀ = a₀ ∧ MapsTo φ V A ∧
      ContDiffOn ℝ 1 φ V ∧
      (∀ x ∈ V, fderiv ℝ (u x) (φ x) = 0) ∧
      ContDiffOn ℝ 2 (fun x ↦ u x (φ x)) V ∧
      (∀ x ∈ V, fderiv ℝ (fun y ↦ u y (φ y)) x =
        fderiv ℝ (fun y ↦ u y (φ x)) x) ∧
      IsClassicalSolution { pde with domain := V } (fun x ↦ u x (φ x)) ∧
      (∀ᶠ q : ℝ^n × ℝ^n in 𝓝 (x₀, a₀),
        fderiv ℝ (u q.1) q.2 = 0 ↔ φ q.1 = q.2) :=
  exists_local_stationary_envelope hcomplete.isOpen_domain hcomplete.isOpen_parameter hx₀ ha₀
    hcomplete.contDiffOn hcomplete.classical hstationary hessian

end NonlinearFirstOrder
