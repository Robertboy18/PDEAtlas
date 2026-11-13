/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.Perron.Envelope

/-!
# A maximal subsolution between barriers

Take the supremum of all upper semicontinuous subsolutions between two
ordered barriers, and then regularize it from above. The envelope theorem
makes this a subsolution. Upper semicontinuity of the upper barrier keeps
the regularized envelope below it, so the envelope belongs to its own
defining family and dominates every member.

Only the lower barrier needs a differential inequality in this step.
The supersolution property of an upper barrier enters the separate bump
argument.

The envelope is the function `W` of (4.2) in Crandall, Ishii and Lions, and the argument is the
start of their proof of Theorem 4.1.

## References

* M. G. Crandall, H. Ishii and P.-L. Lions, *User's guide to viscosity solutions of second order
  partial differential equations*, Bull. Amer. Math. Soc. 27 (1992), 1-67, §4, Theorem 4.1,
  equation (4.2), and its proof.
  <https://doi.org/10.1090/S0273-0979-1992-00266-5>
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi.Perron

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- There is a greatest upper semicontinuous viscosity subsolution between
an upper semicontinuous subsolution and an ordered upper semicontinuous
barrier. It is constructed by regularizing the supremum of the whole
admissible family. -/
theorem exists_greatest_subsolution_between {H : E → E → ℝ} {U : Set (E × ℝ)} {l b : E × ℝ → ℝ}
    (hH : Continuous (fun q : E × E ↦ H q.1 q.2)) (hl : UpperSemicontinuousOn l U)
    (hlsub : IsSpatialViscositySubsolution H U l) (hb : UpperSemicontinuousOn b U)
    (hlb : ∀ x ∈ U, l x ≤ b x) :
    ∃ u : E × ℝ → ℝ, UpperSemicontinuousOn u U ∧
      IsSpatialViscositySubsolution H U u ∧
      (∀ x ∈ U, l x ≤ u x ∧ u x ≤ b x) ∧
      ∀ v : E × ℝ → ℝ, UpperSemicontinuousOn v U →
        IsSpatialViscositySubsolution H U v →
        (∀ x ∈ U, l x ≤ v x ∧ v x ≤ b x) → ∀ x ∈ U, v x ≤ u x := by
  let A := {v : E × ℝ → ℝ // UpperSemicontinuousOn v U ∧
    IsSpatialViscositySubsolution H U v ∧ ∀ x ∈ U, l x ≤ v x ∧ v x ≤ b x}
  let i₀ : A := ⟨l, hl, hlsub, fun x hx ↦ ⟨le_rfl, hlb x hx⟩⟩
  have : Nonempty A := ⟨i₀⟩
  let v : A → E × ℝ → ℝ := fun i ↦ i.1
  let u : E × ℝ → ℝ := fun x ↦ limsup (fun y ↦ ⨆ i, v i y) (𝓝[U] x)
  have hbound : ∀ x ∈ U, ∃ c, ∀ᶠ y in 𝓝[U] x, ∀ i, v i y ≤ c := by
    intro x hx
    refine ⟨b x + 1, ?_⟩
    filter_upwards [hb x hx (b x + 1) (lt_add_one _), self_mem_nhdsWithin] with y hy hyU i
    exact (i.property.2.2 y hyU).2.trans hy.le
  have hle : ∀ x ∈ U, ∀ i, v i x ≤ u x :=
    fun x hx i ↦ PDE.le_limsup_ciSup_nhdsWithin (v := v) hx (hbound x hx) i
  have hu : UpperSemicontinuousOn u U := PDE.upperSemicontinuousOn_limsup_nhdsWithin
      (fun x hx ↦ PDE.isBoundedUnder_ciSup (hbound x hx))
  have husub : IsSpatialViscositySubsolution H U u :=
    isSpatialViscositySubsolution_limsup_ciSup (v := v) hH
      (fun i ↦ i.property.1) (fun i ↦ i.property.2.1) hbound
  refine ⟨u, hu, husub, ?_, ?_⟩
  · intro x hx
    refine ⟨hle x hx i₀, ?_⟩
    apply PDE.limsup_nhdsWithin_le_of_upperSemicontinuousWithinAt hx (hb x hx)
    filter_upwards [self_mem_nhdsWithin] with y hy using ciSup_le fun i ↦ (i.property.2.2 y hy).2
  · exact fun w hw hwsub hwb x hx ↦ hle x hx ⟨w, hw, hwsub, hwb⟩

end HamiltonJacobi.Perron
