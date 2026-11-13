/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Quotients by kernels of continuous linear maps

Let `T : E →L[ℝ] F` be a continuous linear map. For a normed source, the quotient `E / ker T`
embeds injectively into `F` through `T`. For a complete inner-product source,
every quotient class additionally has a unique representative in `(ker T)ᗮ`.
That representative preserves the quotient norm and minimizes the norm among
all vectors with the same value under `T`.

Trace spaces use this to obtain canonical minimal-energy extensions without choosing a
separate extension formula: for the trace operator `T : H¹(Ω) → L²(∂Ω)`, the representative
of the class of `u` is the extension of `Tu` into `Ω` of least `H¹` norm.

## Main results

* `map`, `congr`: functoriality of the quotient along a continuous linear map
  (or equivalence) of sources compatible with the kernels.
* `representative T`: for a complete inner-product source, the orthogonal
  representative `E ⧸ ker T →L[ℝ] E`, with `mk_representative`,
  `norm_representative` (it is an isometry onto `(ker T)ᗮ`),
  `norm_representative_le_of_apply_eq` (norm minimality) and
  `representative_eq_of_mem_orthogonal` (uniqueness).
* `norm_map_le`, `norm_map_le_opNorm`: operator-norm bounds for induced maps.

## Implementation notes

The orthogonal representative is the projection theorem for the closed subspace `ker T`, which
Mathlib packages as the isometry `Submodule.quotientEquivOrthogonal` between `E ⧸ ker T` and
`(ker T)ᗮ`; `representative` composes it with the inclusion of `(ker T)ᗮ`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Universitext, Springer, 2011, Chapter 5. <https://doi.org/10.1007/978-0-387-70914-7>
-/

@[expose] public section

set_option linter.missingDocs true

noncomputable section


namespace ContinuousLinearMap.KernelQuotient

section Normed

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The closed kernel of a continuous linear map between real normed spaces. -/
def closedKernel (T : E →L[ℝ] F) : ClosedSubmodule ℝ E where
  toSubmodule := T.ker
  isClosed' := T.isClosed_ker

/-- The kernel of a continuous linear map is closed. -/
instance (T : E →L[ℝ] F) :
    IsClosed (T.ker : Set E) :=
  T.isClosed_ker

end Normed

section Congr

variable {E E' F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']

/--
The map between kernel quotients induced by a continuous linear map that
sends the first kernel into the second.
-/
def map
    (T : E →L[ℝ] F) (T' : E' →L[ℝ] F')
    (e : E →L[ℝ] E')
    (hker : ∀ x, T x = 0 → T' (e x) = 0) :
    (E ⧸ T.ker) →L[ℝ] (E' ⧸ T'.ker) :=
  T.ker.liftQL
    (T'.ker.mkQL.comp e)
    (by
      intro x hx
      change Submodule.Quotient.mk (e x) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      change T' (e x) = 0
      change T x = 0 at hx
      exact hker x hx)

/-- The induced kernel-quotient map sends a quotient class to the class of its image. -/
@[simp]
theorem map_mk
    (T : E →L[ℝ] F) (T' : E' →L[ℝ] F')
    (e : E →L[ℝ] E')
    (hker : ∀ x, T x = 0 → T' (e x) = 0)
    (x : E) :
    map T T' e hker (Submodule.Quotient.mk x) = Submodule.Quotient.mk (e x) :=
  rfl

/--
A continuous linear equivalence that identifies two kernels descends to a
continuous linear equivalence of the corresponding kernel quotients.
-/
def congr
    (T : E →L[ℝ] F) (T' : E' →L[ℝ] F')
    (e : E ≃L[ℝ] E')
    (hker : ∀ x, T x = 0 ↔ T' (e x) = 0) :
    (E ⧸ T.ker) ≃L[ℝ] (E' ⧸ T'.ker) :=
  let eForward : E →L[ℝ] E' := e.toContinuousLinearMap
  let eBackward : E' →L[ℝ] E := e.symm.toContinuousLinearMap
  have hforward : ∀ x, T x = 0 → T' (eForward x) = 0 := by
    intro x hx
    change T' (e x) = 0
    exact (hker x).mp hx
  have hbackward : ∀ y, T' y = 0 → T (eBackward y) = 0 := by
    intro y hy
    change T (e.symm y) = 0
    apply (hker (e.symm y)).mpr
    simpa using hy
  let forward :=
    map T T' eForward hforward
  let backward :=
    map T' T eBackward hbackward
  ContinuousLinearEquiv.equivOfInverse forward backward
    (by
      intro q
      obtain ⟨x, rfl⟩ :=
        (show Function.Surjective T.ker.mkQL from T.ker.mkQ_surjective) q
      rw [show forward (T.ker.mkQL x) = T'.ker.mkQL (eForward x) by
        exact map_mk T T' eForward hforward x]
      rw [show backward (T'.ker.mkQL (eForward x)) =
          T.ker.mkQL (eBackward (eForward x)) by
        exact map_mk T' T eBackward hbackward (eForward x)]
      simp [eForward, eBackward])
    (by
      intro q
      obtain ⟨y, rfl⟩ :=
        (show Function.Surjective T'.ker.mkQL from T'.ker.mkQ_surjective) q
      rw [show backward (T'.ker.mkQL y) = T.ker.mkQL (eBackward y) by
        exact map_mk T' T eBackward hbackward y]
      rw [show forward (T.ker.mkQL (eBackward y)) =
          T'.ker.mkQL (eForward (eBackward y)) by
        exact map_mk T T' eForward hforward (eBackward y)]
      simp [eForward, eBackward])

/-- The quotient equivalence acts on representatives through the source equivalence. -/
@[simp]
theorem congr_mk
    (T : E →L[ℝ] F) (T' : E' →L[ℝ] F')
    (e : E ≃L[ℝ] E')
    (hker : ∀ x, T x = 0 ↔ T' (e x) = 0)
    (x : E) :
    congr T T' e hker (Submodule.Quotient.mk x) = Submodule.Quotient.mk (e x) :=
  rfl

end Congr

section Hilbert

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The orthogonal, norm-minimizing representative of a kernel-quotient class. -/
def representative (T : E →L[ℝ] F) : (E ⧸ T.ker) →L[ℝ] E :=
  T.ker.orthogonal.subtypeL.comp
    (T.ker.quotientEquivOrthogonal.toLinearIsometry
      |>.toContinuousLinearMap)

/-- Taking the quotient class of the canonical representative is the identity. -/
@[simp]
theorem mk_representative (T : E →L[ℝ] F) (q : E ⧸ T.ker) :
    T.ker.mkQL (representative T q) = q := by
  rw [← T.ker.quotientEquivOrthogonal.injective.eq_iff]
  simp [representative]

/-- The canonical representative preserves the quotient norm. -/
theorem norm_representative (T : E →L[ℝ] F) (q : E ⧸ T.ker) :
    ‖representative T q‖ = ‖q‖ := by
  change ‖T.ker.quotientEquivOrthogonal q‖ = ‖q‖
  exact T.ker.quotientEquivOrthogonal.norm_map q

/-- The canonical representative realizes the value of its quotient class. -/
theorem apply_representative (T : E →L[ℝ] F) (q : E ⧸ T.ker) :
    T (representative T q) = T.ker.liftQL T le_rfl q := by
  exact congrArg (T.ker.liftQL T le_rfl) (mk_representative T q)

/-- The canonical representative is orthogonal to the kernel. -/
theorem representative_mem_orthogonal (T : E →L[ℝ] F) (q : E ⧸ T.ker) :
    representative T q ∈ T.ker.orthogonal :=
  (T.ker.quotientEquivOrthogonal q).2

/--
The canonical representative has minimal norm among vectors with the same
value under the original map.
-/
theorem norm_representative_le_of_apply_eq
    (T : E →L[ℝ] F) (q : E ⧸ T.ker) (x : E)
    (hx : T x = T.ker.liftQL T le_rfl q) :
    ‖representative T q‖ ≤ ‖x‖ := by
  have hclass : T.ker.mkQL x = q := by
    apply LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot T.ker T.toLinearMap le_rfl le_rfl)
    simpa using hx
  rw [norm_representative, ← hclass]
  exact Submodule.Quotient.norm_mk_le T.ker x

/--
The canonical representative is the unique representative of its class that
is orthogonal to the kernel.
-/
theorem representative_eq_of_mem_orthogonal
    (T : E →L[ℝ] F) (q : E ⧸ T.ker) (x : E)
    (hx : x ∈ T.ker.orthogonal)
    (hTx : T x = T.ker.liftQL T le_rfl q) :
    representative T q = x := by
  have hclass : T.ker.mkQL x = q := by
    apply LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot T.ker T.toLinearMap le_rfl le_rfl)
    simpa using hTx
  rw [← hclass]
  change
    (T.ker.quotientEquivOrthogonal
      (Submodule.Quotient.mk x)).1 = x
  exact congrArg Subtype.val
    (T.ker.quotientEquivOrthogonal_mk x hx)

end Hilbert

section MapNorm

variable {E E' F F' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']

/--
The norm of an induced kernel-quotient map is controlled by the corresponding
bound on source representatives.
-/
theorem norm_map_apply_le
    (T : E →L[ℝ] F) (T' : E' →L[ℝ] F')
    (e : E →L[ℝ] E')
    (hker : ∀ x, T x = 0 → T' (e x) = 0)
    {C : ℝ} (he : ∀ x, ‖e x‖ ≤ C * ‖x‖)
    (q : E ⧸ T.ker) :
    ‖map T T' e hker q‖ ≤ C * ‖q‖ := by
  calc
    ‖map T T' e hker q‖ =
        ‖map T T' e hker (T.ker.mkQL (representative T q))‖ := by
      rw [mk_representative]
    _ = ‖T'.ker.mkQL (e (representative T q))‖ :=
      congrArg norm (map_mk T T' e hker (representative T q))
    ‖T'.ker.mkQL (e (representative T q))‖ ≤ ‖e (representative T q)‖ :=
      Submodule.Quotient.norm_mk_le T'.ker _
    _ ≤ C * ‖representative T q‖ := he _
    _ = C * ‖q‖ := by rw [norm_representative]

/-- The operator norm of an induced kernel-quotient map is controlled by a
uniform bound on source representatives. -/
theorem norm_map_le
    (T : E →L[ℝ] F) (T' : E' →L[ℝ] F')
    (e : E →L[ℝ] E')
    (hker : ∀ x, T x = 0 → T' (e x) = 0)
    {C : ℝ} (hC : 0 ≤ C) (he : ∀ x, ‖e x‖ ≤ C * ‖x‖) :
    ‖map T T' e hker‖ ≤ C :=
  (map T T' e hker).opNorm_le_bound hC
    (norm_map_apply_le T T' e hker he)

/-- The induced map between kernel quotients has operator norm at most that of
the map between their source spaces. -/
theorem norm_map_le_opNorm
    (T : E →L[ℝ] F) (T' : E' →L[ℝ] F')
    (e : E →L[ℝ] E')
    (hker : ∀ x, T x = 0 → T' (e x) = 0) :
    ‖map T T' e hker‖ ≤ ‖e‖ :=
  norm_map_le T T' e hker (norm_nonneg e) (ContinuousLinearMap.le_opNorm e)

end MapNorm

end ContinuousLinearMap.KernelQuotient
