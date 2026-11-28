/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.InnerProductSpace.Complexification.Operator
public import PDE.Analysis.Operator.Resolvent.Spectrum

/-!
# The complexification of a partial operator

A real unbounded operator `B`, for example a first-order differential operator on real `L²` with
domain `H¹`, has to act on `H + iH` before it can be compared with the generator of a
complex-linear semigroup. Its complexification `LinearPMap.complexify B` has as domain the `z`
whose real and imaginary parts are in the domain of `B`, and it acts by
`B z = B z.re + i B z.im`. Complex linearity is the computation
`(a + ib)(x + iy) = (ax - by) + i(ay + bx)` with the real linearity of `B`. The graph is the set
of pairs whose real parts and whose imaginary parts are in the graph of `B`, and for a bounded
operator defined everywhere the construction is the complexification of bounded operators. The
generator of a complexified semigroup is the complexification of the real generator
(`StronglyContinuousSemigroup.generator_complexify`). Closed operators are not treated: that the
complexification of a closed operator is closed is not stated.

## Main results

* `LinearPMap.complexify`: the complex-linear complexification of every partial operator on a
  real inner product space, with its domain `mem_domain_complexify_iff`.
* `LinearPMap.mem_graph_complexify_iff`: `(z, w)` is in its graph exactly when `(z.re, w.re)`
  and `(z.im, w.im)` are in the graph of `B`.
* `LinearPMap.complexify_toPMap_top`: for every bounded operator `T`, the complexification of
  `T` as an operator defined everywhere is `Complexification.complexify T`.
-/

@[expose] public noncomputable section

open PDE.Analysis PDE.Analysis.Complexification

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **The complexification of a partial operator** `B` on a real inner product space `H`. On
`H + iH` its domain is the set of `z` whose real and imaginary parts are in the domain of `B`,
and it acts on the real and on the imaginary part. -/
def complexify (B : H →ₗ.[ℝ] H) : Complexification H →ₗ.[ℂ] Complexification H where
  domain :=
    { carrier := {z | z.re ∈ B.domain ∧ z.im ∈ B.domain}
      add_mem' := fun hz hw ↦ ⟨B.domain.add_mem hz.1 hw.1, B.domain.add_mem hz.2 hw.2⟩
      zero_mem' := ⟨B.domain.zero_mem, B.domain.zero_mem⟩
      smul_mem' := fun c _ hz ↦
        ⟨B.domain.sub_mem (B.domain.smul_mem c.re hz.1) (B.domain.smul_mem c.im hz.2),
          B.domain.add_mem (B.domain.smul_mem c.re hz.2) (B.domain.smul_mem c.im hz.1)⟩ }
  toFun :=
    { toFun := fun z ↦ Complexification.mk (B ⟨z.1.re, z.2.1⟩) (B ⟨z.1.im, z.2.2⟩)
      map_add' := fun z w ↦ Complexification.ext
        (B.map_add ⟨z.1.re, z.2.1⟩ ⟨w.1.re, w.2.1⟩) (B.map_add ⟨z.1.im, z.2.2⟩ ⟨w.1.im, w.2.2⟩)
      map_smul' := fun c z ↦ by
        have hre : B ⟨(c • z).1.re, (c • z).2.1⟩ =
            c.re • B ⟨z.1.re, z.2.1⟩ - c.im • B ⟨z.1.im, z.2.2⟩ := by
          rw [← B.map_smul, ← B.map_smul, ← B.map_sub]
          rfl
        have him : B ⟨(c • z).1.im, (c • z).2.2⟩ =
            c.re • B ⟨z.1.im, z.2.2⟩ + c.im • B ⟨z.1.re, z.2.1⟩ := by
          rw [← B.map_smul, ← B.map_smul, ← B.map_add]
          rfl
        exact Complexification.ext hre him }

/-- The domain of the complexification: real and imaginary part in the real domain. -/
theorem mem_domain_complexify_iff {B : H →ₗ.[ℝ] H} {z : Complexification H} :
    z ∈ B.complexify.domain ↔ z.re ∈ B.domain ∧ z.im ∈ B.domain :=
  Iff.rfl

/-- **The graph of the complexification**: `(z, w)` is in it exactly when the real parts and
the imaginary parts are in the graph of the real operator. -/
theorem mem_graph_complexify_iff {B : H →ₗ.[ℝ] H} {z w : Complexification H} :
    (z, w) ∈ B.complexify.graph ↔ (z.re, w.re) ∈ B.graph ∧ (z.im, w.im) ∈ B.graph := by
  constructor
  · intro h
    obtain ⟨u, rfl, rfl⟩ := (mem_graph_iff _).mp h
    have hu := mem_domain_complexify_iff.mp u.2
    exact ⟨B.mem_graph ⟨u.1.re, hu.1⟩, B.mem_graph ⟨u.1.im, hu.2⟩⟩
  · rintro ⟨hre, him⟩
    have hx₁ := mem_domain_of_mem_graph hre
    have hx₂ := mem_domain_of_mem_graph him
    refine (mem_graph_iff _).mpr
      ⟨⟨z, mem_domain_complexify_iff.mpr ⟨hx₁, hx₂⟩⟩, rfl, ?_⟩
    exact Complexification.ext ((image_iff hx₁).mpr hre).symm ((image_iff hx₂).mpr him).symm

/-- **For a bounded operator, defined everywhere, the complexification of partial operators is
the complexification of bounded operators.** -/
theorem complexify_toPMap_top (T : H →L[ℝ] H) :
    (T.toLinearMap.toPMap ⊤).complexify =
      (Complexification.complexify T).toLinearMap.toPMap ⊤ := by
  refine eq_of_eq_graph ?_
  ext ⟨z, w⟩
  rw [mem_graph_complexify_iff, mem_graph_toPMap_top, mem_graph_toPMap_top,
    mem_graph_toPMap_top]
  exact ⟨fun h ↦ Complexification.ext h.1 h.2, fun h ↦ ⟨congrArg re h, congrArg im h⟩⟩

end LinearPMap
