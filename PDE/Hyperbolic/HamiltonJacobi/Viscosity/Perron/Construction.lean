/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.Perron.Maximal
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.Perron.Bump

/-!
# Perron's envelope between continuous barriers

For a continuous position-dependent Hamiltonian and ordered continuous
subsolution and supersolution barriers, the upper regularized supremum of
all admissible subsolutions is a subsolution. Its lower regularization is
a supersolution. Both remain between the barriers.

The family, its maximality, and the supersolution property are constructed
by the preceding envelope and bump theorems. This result does not require
a comparison principle. Equality of the two regularizations, and hence
continuity, requires a comparison theorem applicable to this
semicontinuous pair.

These are the two steps in the proof of Theorem 4.1 of Crandall, Ishii and Lions, Lemma 4.2 and
Lemma 4.4, without the comparison hypothesis of that theorem. As their notes on §4 explain,
Perron's method needs no comparison in the formulation of Ishii, where solutions need not be
continuous.

## References

* M. G. Crandall, H. Ishii and P.-L. Lions, *User's guide to viscosity solutions of second order
  partial differential equations*, Bull. Amer. Math. Soc. 27 (1992), 1-67, §4, Theorem 4.1 and
  its proof, and the notes on §4.
  <https://doi.org/10.1090/S0273-0979-1992-00266-5>
* H. Ishii, *Perron's method for Hamilton-Jacobi equations*, Duke Math. J. 55 (1987), 369-384.
  <https://doi.org/10.1215/S0012-7094-87-05521-9>
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi.Perron

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Ordered continuous viscosity barriers produce a Perron envelope whose
upper representative is a subsolution and whose lower regularization is
a supersolution. The ordering includes both representatives. -/
theorem exists_perron_envelope_between {H : E → E → ℝ} {U : Set (E × ℝ)} {l b : E × ℝ → ℝ}
    (hH : Continuous (fun q : E × E ↦ H q.1 q.2)) (hl : ContinuousOn l U) (hb : ContinuousOn b U)
    (hlsub : IsSpatialViscositySubsolution H U l) (hbsuper : IsSpatialViscositySupersolution H U b)
    (hlb : ∀ x ∈ U, l x ≤ b x) :
    ∃ u : E × ℝ → ℝ, UpperSemicontinuousOn u U ∧
      IsSpatialViscositySubsolution H U u ∧
      LowerSemicontinuousOn (fun x ↦ liminf u (𝓝[U] x)) U ∧
      IsSpatialViscositySupersolution H U (fun x ↦ liminf u (𝓝[U] x)) ∧
      ∀ x ∈ U, l x ≤ liminf u (𝓝[U] x) ∧
        liminf u (𝓝[U] x) ≤ u x ∧ u x ≤ b x := by
  obtain ⟨u, hu, husub, hub, hmax⟩ := exists_greatest_subsolution_between hH
    hl.upperSemicontinuousOn hlsub hb.upperSemicontinuousOn hlb
  have hbound : ∀ x ∈ U, IsBoundedUnder (· ≥ ·) (𝓝[U] x) u := by
    intro x hx
    refine ⟨l x - 1, ?_⟩
    change ∀ᶠ y in 𝓝[U] x, l x - 1 ≤ u y
    filter_upwards [hl.lowerSemicontinuousOn x hx (l x - 1) (sub_one_lt _),
      self_mem_nhdsWithin] with y hy hyU
    exact hy.le.trans (hub y hyU).1
  have hsuper := isSpatialViscositySupersolution_liminf_of_maximal hH hu husub hbound
    hb.lowerSemicontinuousOn hbsuper (fun x hx ↦ (hub x hx).2) (fun w hw hwsub hwb ↦ hmax w hw hwsub
      (fun x hx ↦ ⟨(hub x hx).1.trans (hwb x hx).1, (hwb x hx).2⟩))
  refine ⟨u, hu, husub, PDE.lowerSemicontinuousOn_liminf_nhdsWithin hbound, hsuper, fun x hx ↦ ?_⟩
  refine ⟨?_, PDE.liminf_nhdsWithin_le hx (hbound x hx), (hub x hx).2⟩
  apply PDE.le_liminf_nhdsWithin_of_lowerSemicontinuousWithinAt hx (hl.lowerSemicontinuousOn x hx)
  filter_upwards [self_mem_nhdsWithin] with y hy using (hub y hy).1

end HamiltonJacobi.Perron
