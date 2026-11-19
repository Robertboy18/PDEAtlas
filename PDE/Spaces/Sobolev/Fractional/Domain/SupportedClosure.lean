/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.SupportedClosure.Space

/-!
# Orthogonal projection onto the supported closure

The supported closure of `Ω` in `H^s(ℝ^n)`, its generators and its inclusions are defined in
`SupportedClosure.Space`. Here the inclusions compose along inclusions of support sets, and the
orthogonal projection from whole-space `H^s` is the best approximation by the supported closure.

`SupportedClosure.CompactApproximation` identifies this subspace with the closure of
smooth compactly supported functions whose support lies in `Ω`. For open `Ω` it is
therefore the space `\widetilde H^s(Ω)`, the closure of `C_c^∞(Ω)` in `H^s(ℝ^n)`
(McLean, *Strongly Elliptic Systems and Boundary Integral Equations*).
Comparison with an intrinsic `H^s_0(Ω)` space or with the kernel of a trace
operator requires hypotheses on `Ω` and depends on the exponent `s`.

## Main definitions

* `SobolevSpace.Fractional.HsSupportedClosureSpace.orthogonalProjection`: the
  orthogonal projection from whole-space `H^s`.

## Main statements

* `SobolevSpace.Fractional.HsSupportedClosureSpace.inclusionCLM_comp`:
  support-set inclusions are functorial.
* `SobolevSpace.Fractional.HsSupportedClosureSpace.orthogonalProjection_eq_iff`:
  the projection is characterized by its orthogonal residual.
* `SobolevSpace.Fractional.HsSupportedClosureSpace.
  norm_sub_coe_orthogonalProjection_eq_iInf`: the projection is a best
  approximation in the ambient `H^s` norm.

## References

* W. McLean, *Strongly Elliptic Systems and Boundary Integral Equations*, Cambridge University
  Press, 2000, for the spaces `H^s(Ω)` and `\widetilde H^s(Ω)`.
-/

@[expose] public section

open TemperedDistribution MeasureTheory
open scoped BesselPotentialSpace ENNReal SchwartzMap

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)}

open BesselPotentialSpace

namespace HsSupportedClosureSpace

/-- The inclusion along `Ω ⊆ Ω` is the identity. -/
@[simp]
theorem inclusionCLM_refl :
    inclusionCLM (n := n) (s := s) (Ω₁ := Ω) (Ω₂ := Ω) (fun _ hu ↦ hu) =
      ContinuousLinearMap.id ℂ (HsSupportedClosureSpace n s Ω) := by
  ext u
  rfl

/-- Supported-closure inclusions compose according to inclusion of support sets. -/
theorem inclusionCLM_comp {Ω₁ Ω₂ Ω₃ : Set (ℝ^n)}
    (h₁₂ : Ω₁ ⊆ Ω₂) (h₂₃ : Ω₂ ⊆ Ω₃) :
    inclusionCLM (n := n) (s := s) h₂₃ ∘L inclusionCLM h₁₂ =
      inclusionCLM (h₁₂.trans h₂₃) := by
  ext u
  rfl

/-- Inclusion sends a supported Schwartz element on `Ω₁` to the same Schwartz function
on `Ω₂`. -/
@[simp]
theorem inclusionCLM_ofSchwartz {Ω₁ Ω₂ : Set (ℝ^n)} (h : Ω₁ ⊆ Ω₂)
    (φ : 𝓢(ℝ^n, ℂ)) (hφ : tsupport φ.toFun ⊆ Ω₁) :
    inclusionCLM (n := n) (s := s) h (ofSchwartz φ hφ) =
      ofSchwartz φ (hφ.trans h) := by
  apply Subtype.ext
  rfl

/-- Every supported-closure element can be approximated in `H^s` by the
complex span of supported Schwartz functions. -/
theorem exists_span_approx (u : HsSupportedClosureSpace n s Ω) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ v ∈ Submodule.span ℂ (schwartzSupportedInSet n s Ω),
      ‖toHs n s Ω u - v‖ < ε :=
  (mem_hsSupportedClosureSubmodule_iff (toHs n s Ω u)).mp u.prop ε hε

/-- Orthogonal projection from whole-space `H^s` onto the supported closure. -/
noncomputable def orthogonalProjection (n : ℕ) (s : ℝ) (Ω : Set (ℝ^n)) :
    H^{s}(ℝ^n) →L[ℂ] HsSupportedClosureSpace n s Ω :=
  (hsSupportedClosureSubmodule n s Ω).orthogonalProjectionOnto

/-- The orthogonal projection fixes every element of the supported closure. -/
@[simp]
theorem orthogonalProjection_coe (u : HsSupportedClosureSpace n s Ω) :
    orthogonalProjection n s Ω (u : H^{s}(ℝ^n)) = u :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self u

/-- Projecting an element of a smaller supported closure onto a larger one is
the canonical support-set inclusion. -/
@[simp]
theorem orthogonalProjection_coe_of_subset {Ω₁ Ω₂ : Set (ℝ^n)}
    (h : Ω₁ ⊆ Ω₂) (u : HsSupportedClosureSpace n s Ω₁) :
    orthogonalProjection n s Ω₂ (u : H^{s}(ℝ^n)) = inclusionCLM h u := by
  simpa only [coe_inclusionCLM] using
    orthogonalProjection_coe (n := n) (s := s) (Ω := Ω₂) (inclusionCLM h u)

/-- For nested support sets, projecting first onto the larger closure does not
change the subsequent projection onto the smaller closure. -/
theorem orthogonalProjection_comp_of_subset
    {Ω₁ Ω₂ : Set (ℝ^n)} (h : Ω₁ ⊆ Ω₂) (u : H^{s}(ℝ^n)) :
    orthogonalProjection n s Ω₁
        (orthogonalProjection n s Ω₂ u : H^{s}(ℝ^n)) =
      orthogonalProjection n s Ω₁ u :=
  (hsSupportedClosureSubmodule n s Ω₁).orthogonalProjectionOnto_starProjection_of_le
    (hsSupportedClosureSubmodule_mono h) u

/-- Orthogonal projection has operator norm at most one. -/
theorem norm_orthogonalProjection_le :
    ‖orthogonalProjection n s Ω‖ ≤ 1 :=
  (hsSupportedClosureSubmodule n s Ω).orthogonalProjectionOnto_norm_le

/-- Orthogonal projection does not increase the `H^s` norm. -/
theorem norm_orthogonalProjection_apply_le (u : H^{s}(ℝ^n)) :
    ‖orthogonalProjection n s Ω u‖ ≤ ‖u‖ :=
  (hsSupportedClosureSubmodule n s Ω).norm_orthogonalProjectionOnto_apply_le u

/-- The residual after supported-closure projection is orthogonal to the subspace. -/
theorem sub_coe_orthogonalProjection_mem_orthogonal (u : H^{s}(ℝ^n)) :
    u - (orthogonalProjection n s Ω u : H^{s}(ℝ^n)) ∈
      (hsSupportedClosureSubmodule n s Ω)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal u

/-- The orthogonal projection is characterized by its orthogonal residual. -/
theorem orthogonalProjection_eq_iff {u : H^{s}(ℝ^n)}
    {v : HsSupportedClosureSpace n s Ω} :
    orthogonalProjection n s Ω u = v ↔
      u - (v : H^{s}(ℝ^n)) ∈ (hsSupportedClosureSubmodule n s Ω)ᗮ := by
  constructor
  · rintro rfl
    exact sub_coe_orthogonalProjection_mem_orthogonal u
  · intro huv
    apply Subtype.ext
    exact Submodule.eq_starProjection_of_mem_orthogonal v.prop huv

/-- The projection is a best approximation in the ambient `H^s` norm. -/
theorem norm_sub_coe_orthogonalProjection_eq_iInf (u : H^{s}(ℝ^n)) :
    ‖u - (orthogonalProjection n s Ω u : H^{s}(ℝ^n))‖ =
      ⨅ v : HsSupportedClosureSpace n s Ω, ‖u - (v : H^{s}(ℝ^n))‖ :=
  (hsSupportedClosureSubmodule n s Ω).starProjection_minimal u

/-- Every ambient `H^s` element splits into its supported projection and an
orthogonal residual. -/
theorem orthogonal_decomposition (u : H^{s}(ℝ^n)) :
    (orthogonalProjection n s Ω u : H^{s}(ℝ^n)) +
        (u - (orthogonalProjection n s Ω u : H^{s}(ℝ^n))) =
      u := by
  abel

/-- Testing the orthogonal projection against the supported closure leaves the
inner product unchanged. -/
@[simp]
theorem inner_coe_orthogonalProjection (u : H^{s}(ℝ^n))
    (v : HsSupportedClosureSpace n s Ω) :
    inner ℂ (orthogonalProjection n s Ω u : H^{s}(ℝ^n)) (v : H^{s}(ℝ^n)) =
      inner ℂ u (v : H^{s}(ℝ^n)) :=
  (hsSupportedClosureSubmodule n s Ω).inner_orthogonalProjectionOnto_eq_of_mem_right v u

end HsSupportedClosureSpace

end SobolevSpace.Fractional
