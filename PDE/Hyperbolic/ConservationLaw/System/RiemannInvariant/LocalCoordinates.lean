/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import PDE.Analysis.ODE.FlowBox.TwoFields
public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.Ordered
public import PDE.Hyperbolic.ConservationLaw.System.RiemannInvariant

/-!
# Local construction of two Riemann invariant coordinates

A C² flux germ at a strictly hyperbolic state has C¹ local eigenvector fields:
the Jacobian is C¹ and the normalized eigenbranches are analytic functions of the
operator. Flow boxes construct a scalar invariant for each field. Their differentials
are transverse, so their pair gives a local C¹ change of state coordinates with a C¹
inverse.

Evans, §11.3.1, notes that for two equations a function constant along the rarefaction curve
`Rᵢ`, as in (3), is a Riemann invariant, and then uses the pair (4) as new state coordinates.
We construct such a pair near a strictly hyperbolic state and prove that it is a change of
coordinates. The first invariant is constant along the first right eigenfield and is
transported with the second speed. The regularity is C¹ from a C² flux germ.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.3.1, definition of Riemann invariants, equations
  (2)-(4).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Gradient Topology

namespace PDE.Hyperbolic.ConservationLaw.System

/-- In a two-dimensional eigenbasis, a covector annihilating one basis vector
is a left eigencovector for the other eigenvalue. -/
theorem covector_eigenvalue_of_annihilate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : Module.Basis (Fin 2) ℝ E) (A : E →L[ℝ] E) (speed : Fin 2 → ℝ)
    (hA : ∀ i, A (b i) = speed i • b i) (l : E →L[ℝ] ℝ) (i : Fin 2) (hl : l (b i) = 0) (z : E) :
    l (A z) = speed i.rev * l z := by
  have heq : (l.comp A).toLinearMap = (speed i.rev • l).toLinearMap := b.ext fun j ↦ by
    change l (A (b j)) = speed i.rev * l (b j)
    rw [hA j, map_smul]
    by_cases hij : j = i
    · subst j
      simp [hl]
    · obtain rfl : j = i.rev := by fin_cases i <;> fin_cases j <;> simp_all
      rfl
  exact DFunLike.congr_fun heq z

/-- A C² flux germ and strict hyperbolicity at one state construct local C¹
Riemann invariant coordinates, with a C¹ inverse and nonzero transverse gradients.
The fields and invariant functions are outputs of the construction.

`w i` annihilates the `i`th ordered right eigenfield. Its differential is a nonzero
left eigencovector for `characteristicSpeed flux i.rev`; thus the speed indices swap. -/
theorem exists_local_riemann_invariant_coordinates {flux : ℝ^2 → ℝ^2} {q₀ : ℝ^2}
    (hflux : ContDiffAt ℝ 2 flux q₀) (hhyper : IsStrictlyHyperbolicAt flux q₀) :
    ∃ w : Fin 2 → ℝ^2 → ℝ, ∃ r : Fin 2 → ℝ^2 → ℝ^2,
      ∃ c : OpenPartialHomeomorph (ℝ^2) (ℝ × ℝ),
        (∀ q, c q = (w 0 q, w 1 q)) ∧ q₀ ∈ c.source ∧ c q₀ = 0 ∧
        ContDiffOn ℝ 1 c c.source ∧ ContDiffOn ℝ 1 c.symm c.target ∧
        (∀ i, ContDiffOn ℝ 1 (w i) c.source ∧ ContDiffOn ℝ 1 (r i) c.source) ∧
        ∀ q ∈ c.source, IsStrictlyHyperbolicAt flux q ∧
          ∀ i, Module.End.HasEigenvector (fderiv ℝ flux q).toLinearMap
              (characteristicSpeed flux i q) (r i q) ∧
            fderiv ℝ (w i) q (r i q) = 0 ∧
            fderiv ℝ (w i) q (r i.rev q) ≠ 0 ∧ ∇ (w i) q ≠ 0 ∧
            ∀ z, fderiv ℝ (w i) q (fderiv ℝ flux q z) =
              characteristicSpeed flux i.rev q * fderiv ℝ (w i) q z := by
  obtain ⟨horder, b, hb⟩ := characteristicSpeed_spec hhyper
  obtain ⟨ψ, hbase, U, hU, hAU, hframe⟩ :=
    PDE.Analysis.Calculus.SimpleEigenpair.exists_local_spectral_frame
      b (fderiv ℝ flux q₀) (fun i ↦ characteristicSpeed flux i q₀) hb horder
  let r : Fin 2 → ℝ^2 → ℝ^2 := fun i q ↦ (ψ i (fderiv ℝ flux q)).1
  have hD : ContDiffAt ℝ 1 (fderiv ℝ flux) q₀ := hflux.fderiv_right le_rfl
  have hr (i : Fin 2) : ContDiffAt ℝ 1 (r i) q₀ :=
    ((((hframe _ hAU).2.1 i).1.of_le (by simp)).comp q₀ hD).fst
  have hrbase (i : Fin 2) : r i q₀ = b i := congrArg Prod.fst (hbase i)
  let e : (ℝ × ℝ) ≃L[ℝ] ℝ^2 :=
    (b.equivFun.trans (LinearEquiv.finTwoArrow ℝ ℝ)).toContinuousLinearEquiv.symm
  have he₀ : r 0 q₀ = e (1, 0) :=
    hrbase 0 ▸ e.symm.injective (by simp [e, LinearEquiv.finTwoArrow])
  have he₁ : r 1 q₀ = e (0, 1) :=
    hrbase 1 ▸ e.symm.injective (by simp [e, LinearEquiv.finTwoArrow])
  obtain ⟨a, hqa, hazero, ha, hai, hann⟩ :=
    PDE.Analysis.ODE.exists_invariant_coordinates_of_transverse (hr 0) (hr 1) e he₀ he₁
  have hnear : ∀ᶠ q in 𝓝 q₀, IsStrictlyHyperbolicAt flux q ∧ (∀ i, ContDiffAt ℝ 1 (r i) q ∧
        Module.End.HasEigenvector (fderiv ℝ flux q).toLinearMap
          (characteristicSpeed flux i q) (r i q)) ∧
      ∃ bq : Module.Basis (Fin 2) ℝ (ℝ^2), ∀ i, bq i = r i q := by
    filter_upwards [hflux.eventually (by simp), hD.eventually (by simp),
      hD.continuousAt.eventually (hU.mem_nhds hAU)] with q hfluxq hDq hqU
    obtain ⟨hord, hvec, bq, hbq⟩ := hframe _ hqU
    have hcanonical := characteristicSpeed_eq_of_eigenbasis bq hord
      (fun i ↦ by rw [hbq i]; exact (hvec i).2.1.apply_eq_smul)
    exact ⟨⟨hfluxq.differentiableAt (by simp), bq, _, hord.injective,
      fun i ↦ by rw [hbq i]; exact (hvec i).2.1⟩, fun i ↦
        ⟨(((hvec i).1.of_le (by simp)).comp q hDq).fst, congrFun hcanonical i ▸ (hvec i).2.1⟩,
      bq, hbq⟩
  obtain ⟨V, hVsub, hV, hqV⟩ := mem_nhds_iff.mp hnear
  let c := a.restrOpen V hV
  let w : Fin 2 → ℝ^2 → ℝ := ![fun q ↦ (a q).1, fun q ↦ (a q).2]
  have hw (i : Fin 2) : ContDiffOn ℝ 1 (w i) c.source := by
    fin_cases i
    exacts [ha.fst.mono inter_subset_left, ha.snd.mono inter_subset_left]
  refine ⟨w, r, c, fun _ ↦ rfl, ⟨hqa, hqV⟩, hazero, ha.mono inter_subset_left,
    fun p hp ↦ (hai p hp.1).mono fun _ h ↦ h.1,
    fun i ↦ ⟨hw i, fun q hq ↦ ((hVsub hq.2).2.1 i).1.contDiffWithinAt⟩, fun q hq ↦ ?_⟩
  obtain ⟨hhyp, hfields, bq, hbq⟩ := hVsub hq.2
  obtain ⟨hann₀, hann₁, htrans₀, htrans₁⟩ := hann q hq.1
  have hanni (i : Fin 2) : fderiv ℝ (w i) q (r i q) = 0 := by
    fin_cases i
    exacts [hann₀, hann₁]
  have htrans (i : Fin 2) : fderiv ℝ (w i) q (r i.rev q) ≠ 0 := by
    fin_cases i
    exacts [htrans₀, htrans₁]
  exact ⟨hhyp, fun i ↦ ⟨(hfields i).2, hanni i, htrans i,
    fun hz ↦ htrans i (by rw [← inner_gradient_left, hz, inner_zero_left]),
    covector_eigenvalue_of_annihilate bq (fderiv ℝ flux q) (fun j ↦ characteristicSpeed flux j q)
      (fun j ↦ by rw [hbq j]; exact (hfields j).2.apply_eq_smul)
      (fderiv ℝ (w i) q) i (by rw [hbq i]; exact hanni i)⟩⟩

/-- The constructed invariant coordinates diagonalize every classical solution whose
states stay in the chart source. Each scalar equation uses the opposite ordered speed.
The same chart works for all such solutions. -/
theorem exists_local_riemann_invariant_diagonalization {flux : ℝ^2 → ℝ^2} {q₀ : ℝ^2}
    (hflux : ContDiffAt ℝ 2 flux q₀) (hhyper : IsStrictlyHyperbolicAt flux q₀) :
    ∃ w : Fin 2 → ℝ^2 → ℝ, ∃ c : OpenPartialHomeomorph (ℝ^2) (ℝ × ℝ),
      (∀ q, c q = (w 0 q, w 1 q)) ∧ q₀ ∈ c.source ∧ c q₀ = 0 ∧
      ContDiffOn ℝ 1 c c.source ∧ ContDiffOn ℝ 1 c.symm c.target ∧
      (∀ i, ContDiffOn ℝ 1 (w i) c.source) ∧
      (∀ q ∈ c.source, ∀ i, ∇ (w i) q ≠ 0) ∧
      ∀ (U : Set (ℝ^2)) (u : ℝ^2 → ℝ^2),
        IsClassicalSolutionOn flux U u → MapsTo u U c.source →
        ∀ p ∈ U, ∀ i,
          (∂[0] (w i ∘ u)) p +
            characteristicSpeed flux i.rev (u p) * (∂[1] (w i ∘ u)) p = 0 := by
  obtain ⟨w, r, c, hpair, hq, hzero, hc, hci, hreg, hspec⟩ :=
    exists_local_riemann_invariant_coordinates hflux hhyper
  refine ⟨w, c, hpair, hq, hzero, hc, hci, fun i ↦ (hreg i).1,
    fun q hq i ↦ ((hspec q hq).2 i).2.2.2.1, fun U u hu hmap p hp i ↦ ?_⟩
  have hw : DifferentiableAt ℝ (w i) (u p) :=
    ((hreg i).1.contDiffAt (c.open_source.mem_nhds (hmap hp))).differentiableAt_one
  exact Quasilinear.riemannInvariant_transport (hu.differentiableAt p hp) hw
    (hu.quasilinear.residual_eq_zero p hp) (((hspec (u p) (hmap hp)).2 i).2.2.2.2)
    ⟨1, (one_smul ℝ (fderiv ℝ (w i) (u p))).symm⟩

end PDE.Hyperbolic.ConservationLaw.System
