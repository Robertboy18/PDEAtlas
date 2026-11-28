/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.EReal.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import PDE.Analysis.Operator.Resolvent.Set
public import PDE.Analysis.Spectral.PseudoResolvent

/-!
# The resolvent set, the spectrum and the resolvent of an unbounded operator

For a partial operator `A` on a normed space over any nontrivially normed field, we define when a
bounded operator `R` is the resolvent `(z - A)⁻¹` (`IsResolventAt`), the resolvent set, the
spectrum, the resolvent itself (`0` off the resolvent set), the generalized eigenspaces
`ker (A - μ)^k` on their natural domains, and, over `ℂ`, the spectral bound. Mathlib has spectra
of elements of an algebra only, while the linearization of the self-similar Navier–Stokes
equations is an unbounded operator on a complex space. For an everywhere defined bounded
operator the definitions are Mathlib's, and for a closed operator on a real Banach space the
resolvent set and the resolvent are the real ones of `PDE.Analysis.Operator.Resolvent.Set`. The
Riesz projection of an unbounded operator (`LinearPMap.isIdempotentElem_rieszProjection_resolvent`)
and the resolvent of a semigroup generator at complex parameters are built on this module. The
parts of the spectrum (point, continuous, residual) are not defined, eigenvalues are handled
through the graph, and the point `0` of the spectrum of `(z₀ - A)⁻¹` is not related to `A`.

## Main results

* `IsResolventAt.unique`, `IsResolventAt.isClosed`: an operator has at most one resolvent at
  `z`, and an operator with a resolvent is closed.
* `IsResolventAt.sub_eq`, `isPseudoResolventOn_resolvent`: two resolvents satisfy the first
  resolvent identity (`sub_eq_smul_mul_of_inverse` of `PDE.Analysis.Operator.Resolvent`), so
  `A.resolvent` is a pseudo-resolvent on the resolvent set.
* `isOpen_resolventSet`, `isClosed_spectrum`, `differentiableOn_resolvent`,
  `hasDerivAt_resolvent`: on a Banach space the resolvent set is open, and the resolvent is
  holomorphic there with derivative `-(z - A)⁻²`.
* `mem_resolventSet_resolvent_iff`, `spectrum_resolvent_sdiff_zero`: away from `0`, the spectrum
  of the bounded operator `(z₀ - A)⁻¹` is `{(z₀ - z)⁻¹ : z ∈ σ(A)}`.
* `IsResolventAt.bijective`, `mem_resolventSet_iff_bijective`: for a closed operator on a Banach
  space, `z` is in the resolvent set exactly when `z - A` is a bijection from the domain onto
  the space.
* `mem_spectrum_of_mem_graph_smul`: an eigenvalue is in the spectrum.
* `IsResolventAt.map_mem_graph`, `IsResolventAt.commute_of_map_mem_graph`: a bounded operator
  commutes with one resolvent exactly when it maps the graph of `A` into itself, and then it
  commutes with every resolvent.
* `IsResolventAt.eq_of_le`: an operator with a resolvent has no proper extension with the same
  resolvent point.
* `IsResolventAtOn`: resolvents relative to a bounded operator `P`, `(z - A) L = P`; they add
  (`IsResolventAtOn.isResolventAt_add`) and satisfy the resolvent identity
  (`IsResolventAtOn.sub_eq`).
* `resolventSet_toPMap_top`, `resolvent_toPMap_top`, `genEigenspace_toPMap_top`: for an
  everywhere defined operator, Mathlib's resolvent set, resolvent and generalized eigenspaces.
* `realResolventSet_eq_resolventSet`, `realResolvent_eq_resolvent`: for a closed operator on a
  real Banach space, these are the real resolvent set and the real resolvent.

## How it works

A bounded `R` is the resolvent of `A` at `z` when it is a two-sided inverse of `z - A`: `R y`
lies in the domain with `A (R y) = z R y - y` for every `y`, and `R (z x - A x) = x` for every
`x` in the domain. Both conditions are stated with the graph of `A`. Closedness is not part of
the definition, because an operator with one resolvent is closed: its graph is
`{(x, y) | R (z x - y) = x}`. For a closed operator on a Banach space, a bijective `z - A` has a
bounded inverse by the closed graph theorem. If `|w - z| ‖R‖ < 1`, then `1 + (w - z) R` is
invertible and `R (1 + (w - z) R)⁻¹` is the resolvent at `w`, so the resolvent set is open. A
bounded resolvent `B = (z₀ - A)⁻¹` carries the whole spectrum of `A`: for `μ ≠ 0`,
`μ - B = μ (z₀ - μ⁻¹ - A) B`, so `μ` is in the spectrum of `B` exactly when `z₀ - μ⁻¹` is in the
spectrum of `A`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.4.1, Definitions (i) and (ii) of the resolvent set and
  the resolvent operator, p. 437, and Theorem 3(i), (12)-(13), p. 438.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE.Analysis.Spectral

namespace LinearPMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (A : E →ₗ.[𝕜] E)

/-- The bounded operator `R` is the resolvent of `A` at `z`, a two-sided inverse of `z - A`
whose values are in the domain of `A`. -/
structure IsResolventAt (z : 𝕜) (R : E →L[𝕜] E) : Prop where
  /-- `(z - A) R y = y`: the vector `R y` is in the domain and `A (R y) = z R y - y`. -/
  mem_graph : ∀ y, (R y, z • R y - y) ∈ A.graph
  /-- `R (z - A) x = x` for every `x` in the domain: if `A x = y`, then `R (z x - y) = x`. -/
  apply_eq : ∀ ⦃x y⦄, (x, y) ∈ A.graph → R (z • x - y) = x

/-- The resolvent set of `A`: the `z` for which `z - A` has a bounded two-sided inverse with
values in the domain of `A`. -/
def resolventSet : Set 𝕜 := {z | ∃ R, A.IsResolventAt z R}

/-- The spectrum of `A`: the complement of the resolvent set. -/
def spectrum : Set 𝕜 := A.resolventSetᶜ

open Classical in
/-- The resolvent `(z - A)⁻¹` of `A` as a bounded operator; `0` outside the resolvent set. -/
def resolvent (z : 𝕜) : E →L[𝕜] E := if h : z ∈ A.resolventSet then Exists.choose h else 0

variable {A} {z w : 𝕜} {R S : E →L[𝕜] E}

namespace IsResolventAt

/-- The values of a resolvent are in the domain of the operator. -/
theorem mem_domain (h : A.IsResolventAt z R) (y : E) : R y ∈ A.domain :=
  mem_domain_of_mem_graph (h.mem_graph y)

/-- `A (R y) = z R y - y` for every `y`. -/
theorem apply_resolvent (h : A.IsResolventAt z R) (y : E) :
    A ⟨R y, h.mem_domain y⟩ = z • R y - y :=
  ((image_iff (h.mem_domain y)).mpr (h.mem_graph y)).symm

/-- `R (z x - A x) = x` for every `x` in the domain. -/
theorem resolvent_apply (h : A.IsResolventAt z R) (x : A.domain) :
    R (z • (x : E) - A x) = x :=
  h.apply_eq (A.mem_graph x)

/-- The first resolvent identity `R - S = (w - z) R S` for the resolvents `R` at `z` and `S`
at `w`. -/
theorem sub_eq (h : A.IsResolventAt z R) (h' : A.IsResolventAt w S) :
    R - S = (w - z) • (R * S) :=
  sub_eq_smul_mul_of_inverse h.apply_eq h'.mem_graph

/-- An operator has at most one resolvent at `z`. -/
theorem unique (h : A.IsResolventAt z R) (h' : A.IsResolventAt z S) : R = S := by
  have := h.sub_eq h'
  rwa [sub_self, zero_smul, sub_eq_zero] at this

/-- An operator that has a resolvent is closed: its graph is `{(x, y) | R (z x - y) = x}`. -/
theorem isClosed (h : A.IsResolventAt z R) : A.IsClosed := by
  have hgraph : (A.graph : Set (E × E)) = {p | R (z • p.1 - p.2) = p.1} := by
    ext ⟨x, y⟩
    refine ⟨fun hxy ↦ h.apply_eq hxy, fun hxy ↦ ?_⟩
    have hg := h.mem_graph (z • x - y)
    rwa [show R (z • x - y) = x from hxy, sub_sub_cancel] at hg
  change _root_.IsClosed (A.graph : Set (E × E))
  rw [hgraph]
  exact isClosed_eq (R.continuous.comp ((continuous_fst.const_smul z).sub continuous_snd))
    continuous_fst

/-- The resolvent is injective. -/
theorem injective (h : A.IsResolventAt z R) : Function.Injective R := by
  refine (injective_iff_map_eq_zero R).mpr fun y hy ↦ ?_
  have hg := h.mem_graph y
  rw [hy, smul_zero, zero_sub] at hg
  simpa using A.graph_fst_eq_zero_snd hg rfl

/-- The shift `z - A` is a bijection from the domain onto the space when `A` has a resolvent at
`z`. Neither closedness nor completeness is needed for this direction. -/
theorem bijective (h : A.IsResolventAt z R) :
    Function.Bijective (z • A.domain.subtype - A.toFun) := by
  refine ⟨fun x x' hxx' ↦ Subtype.ext ?_, fun y ↦ ⟨⟨R y, h.mem_domain y⟩, ?_⟩⟩
  · have h1 : z • (x : E) - A x = z • (x' : E) - A x' := hxx'
    rw [← h.resolvent_apply x, ← h.resolvent_apply x', h1]
  · change z • R y - A ⟨R y, h.mem_domain y⟩ = y
    rw [h.apply_resolvent, sub_sub_cancel]

/-- **Perturbation of the parameter.** If `R` is the resolvent at `z` and `S` is a two-sided
inverse of `1 + (w - z) R`, then `R S` is the resolvent at `w`. -/
theorem of_inverse (h : A.IsResolventAt z R) (h1 : (1 + (w - z) • R) * S = 1)
    (h2 : S * (1 + (w - z) • R) = 1) : A.IsResolventAt w (R * S) := by
  have hc : R * S = S * R :=
    calc R * S = S * (1 + (w - z) • R) * (R * S) := by rw [h2, one_mul]
      _ = S * (R * ((1 + (w - z) • R) * S)) := by
          simp only [mul_assoc, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
            mul_smul_comm]
      _ = S * R := by rw [h1, mul_one]
  have hS (y : E) : S y + (w - z) • R (S y) = y := by
    simpa using DFunLike.congr_fun h1 y
  refine ⟨fun y ↦ ?_, fun x y hxy ↦ ?_⟩
  · have hg := h.mem_graph (S y)
    have e : z • R (S y) - S y = w • R (S y) - y :=
      calc z • R (S y) - S y = w • R (S y) - (S y + (w - z) • R (S y)) := by module
        _ = w • R (S y) - y := by rw [hS y]
    rwa [e] at hg
  · have h3 : R (w • x - y) = x + (w - z) • R x := by
      rw [show w • x - y = (z • x - y) + (w - z) • x by module, _root_.map_add, _root_.map_smul,
        h.apply_eq hxy]
    rw [hc, mul_apply_eq_comp, h3]
    simpa using DFunLike.congr_fun h2 x

end IsResolventAt

/-- A parameter with a resolvent is in the resolvent set. -/
theorem IsResolventAt.mem_resolventSet (h : A.IsResolventAt z R) : z ∈ A.resolventSet :=
  ⟨R, h⟩

/-- On the resolvent set, `A.resolvent z` is the resolvent of `A` at `z`. -/
theorem isResolventAt_resolvent (hz : z ∈ A.resolventSet) : A.IsResolventAt z (A.resolvent z) := by
  rw [resolvent, dite_eq_left hz]
  exact hz.choose_spec

/-- A resolvent of `A` at `z` is `A.resolvent z`. -/
theorem IsResolventAt.resolvent_eq (h : A.IsResolventAt z R) : A.resolvent z = R :=
  (isResolventAt_resolvent h.mem_resolventSet).unique h

/-- Outside the resolvent set, `A.resolvent z = 0`. -/
theorem resolvent_of_notMem (hz : z ∉ A.resolventSet) : A.resolvent z = 0 := by
  rw [resolvent, dite_eq_right hz]

/-- A parameter is in the spectrum exactly when it is not in the resolvent set. -/
theorem mem_spectrum_iff : z ∈ A.spectrum ↔ z ∉ A.resolventSet := Iff.rfl

/-- The resolvent of an operator satisfies the first resolvent identity on the resolvent set. -/
theorem isPseudoResolventOn_resolvent : IsPseudoResolventOn A.resolvent A.resolventSet :=
  fun _ hz _ hw ↦ (isResolventAt_resolvent hz).sub_eq (isResolventAt_resolvent hw)

/-- Two resolvents of an operator commute. -/
theorem IsResolventAt.commute (h : A.IsResolventAt z R) (h' : A.IsResolventAt w S) :
    Commute R S := by
  rw [← h.resolvent_eq, ← h'.resolvent_eq]
  exact isPseudoResolventOn_resolvent.commute h.mem_resolventSet h'.mem_resolventSet

/-- An operator with a nonempty resolvent set is closed. -/
theorem isClosed_of_mem_resolventSet (hz : z ∈ A.resolventSet) : A.IsClosed :=
  (isResolventAt_resolvent hz).isClosed

/-- The range of the resolvent is the domain of the operator. -/
theorem range_resolvent (hz : z ∈ A.resolventSet) :
    LinearMap.range (A.resolvent z).toLinearMap = A.domain := by
  have h := isResolventAt_resolvent hz
  refine le_antisymm ?_ fun x hx ↦ ⟨z • x - A ⟨x, hx⟩, h.resolvent_apply ⟨x, hx⟩⟩
  rintro _ ⟨y, rfl⟩
  exact h.mem_domain y

/-- An eigenvector of `A` is an eigenvector of the resolvent: if `A x = μ x`, then
`(z - μ) (z - A)⁻¹ x = x`. -/
theorem smul_resolvent_apply_of_mem_graph_smul (hz : z ∈ A.resolventSet) {μ : 𝕜} {x : E}
    (hx : (x, μ • x) ∈ A.graph) : (z - μ) • A.resolvent z x = x := by
  have h := (isResolventAt_resolvent hz).apply_eq hx
  rwa [← sub_smul, _root_.map_smul] at h

/-- An eigenvalue of `A` is in the spectrum of `A`. -/
theorem mem_spectrum_of_mem_graph_smul {μ : 𝕜} {x : E} (hx : (x, μ • x) ∈ A.graph)
    (hx0 : x ≠ 0) : μ ∈ A.spectrum := fun hμ ↦
  hx0 (by simpa using (smul_resolvent_apply_of_mem_graph_smul hμ hx).symm)

/-- **The spectrum of the resolvent.** Let `B` be the resolvent of `A` at `z₀` and `μ ≠ 0`. The
bounded operator `μ - B` is invertible exactly when `z₀ - μ⁻¹` is in the resolvent set of `A`.
Its inverse is `μ⁻¹ (1 + μ⁻¹ (z₀ - μ⁻¹ - A)⁻¹)`, and the resolvent of `A` at `z₀ - μ⁻¹` is
`μ B (μ - B)⁻¹`. -/
theorem IsResolventAt.mem_resolventSet_iff {z₀ μ : 𝕜} {B : E →L[𝕜] E}
    (hB : A.IsResolventAt z₀ B) (hμ : μ ≠ 0) :
    μ ∈ _root_.resolventSet 𝕜 B ↔ z₀ - μ⁻¹ ∈ A.resolventSet := by
  rw [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : E →L[𝕜] E, Q = ↑u⁻¹ := ⟨_, rfl⟩
    have hQ1 : (μ • (1 : E →L[𝕜] E) - B) * Q = 1 := by rw [← hu, hQ]; exact u.mul_inv
    have hQ2 : Q * (μ • (1 : E →L[𝕜] E) - B) = 1 := by rw [← hu, hQ]; exact u.inv_mul
    have hc : B * Q = Q * B :=
      calc B * Q = Q * (μ • (1 : E →L[𝕜] E) - B) * (B * Q) := by rw [hQ2, one_mul]
        _ = Q * (B * ((μ • (1 : E →L[𝕜] E) - B) * Q)) := by
            simp only [mul_assoc, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul,
              mul_one]
        _ = Q * B := by rw [hQ1, mul_one]
    have h1 (y : E) : μ • Q y - B (Q y) = y := by simpa using DFunLike.congr_fun hQ1 y
    have h2 (x : E) : Q (μ • x - B x) = x := by simpa using DFunLike.congr_fun hQ2 x
    refine ⟨μ • (B * Q), fun y ↦ ?_, fun x y hxy ↦ ?_⟩
    · have hg := hB.mem_graph (μ • Q y)
      have e : z₀ • B (μ • Q y) - μ • Q y = (z₀ - μ⁻¹) • (μ • B (Q y)) - y :=
        calc z₀ • B (μ • Q y) - μ • Q y
            = (z₀ - μ⁻¹) • (μ • B (Q y)) - (μ • Q y - (μ⁻¹ * μ) • B (Q y)) := by
              rw [_root_.map_smul]
              module
          _ = (z₀ - μ⁻¹) • (μ • B (Q y)) - y := by rw [inv_mul_cancel₀ hμ, one_smul, h1 y]
      rw [e, ← _root_.map_smul] at hg
      simpa only [_root_.smul_apply, mul_apply_eq_comp, _root_.map_smul] using hg
    · have h3 : B ((z₀ - μ⁻¹) • x - y) = x - μ⁻¹ • B x := by
        rw [show (z₀ - μ⁻¹) • x - y = (z₀ • x - y) - μ⁻¹ • x by module, _root_.map_sub,
          _root_.map_smul, hB.apply_eq hxy]
      rw [hc, _root_.smul_apply, mul_apply_eq_comp, h3, ← _root_.map_smul, smul_sub, smul_smul,
        mul_inv_cancel₀ hμ, one_smul]
      exact h2 x
  · rintro ⟨Rw, hRw⟩
    have e : μ⁻¹ • (B * Rw) = Rw - B := by
      have h := hB.sub_eq hRw
      rw [sub_sub_cancel_left, neg_smul] at h
      rw [← neg_sub, h, neg_neg]
    have key : (μ • (1 : E →L[𝕜] E) - B) * (1 + μ⁻¹ • Rw) = μ • 1 := by
      rw [sub_mul, mul_add, mul_add, mul_one, mul_one, smul_mul_assoc, one_mul, smul_smul,
        mul_inv_cancel₀ hμ, one_smul, mul_smul_comm, e]
      abel
    have hcomm : Commute (μ • (1 : E →L[𝕜] E) - B) (1 + μ⁻¹ • Rw) :=
      ((Commute.one_left _).smul_left μ).sub_left
        ((Commute.one_right _).add_right ((hB.commute hRw).smul_right μ⁻¹))
    refine isUnit_iff_exists.mpr ⟨μ⁻¹ • (1 + μ⁻¹ • Rw), ?_, ?_⟩
    · rw [mul_smul_comm, key, smul_smul, inv_mul_cancel₀ hμ, one_smul]
    · rw [smul_mul_assoc, ← hcomm.eq, key, smul_smul, inv_mul_cancel₀ hμ, one_smul]

/-- **The spectrum of the resolvent.** For `z₀` in the resolvent set of `A` and `μ ≠ 0`, the
bounded operator `μ - (z₀ - A)⁻¹` is invertible exactly when `z₀ - μ⁻¹` is in the resolvent set
of `A`. -/
theorem mem_resolventSet_resolvent_iff {z₀ μ : 𝕜} (hz₀ : z₀ ∈ A.resolventSet) (hμ : μ ≠ 0) :
    μ ∈ _root_.resolventSet 𝕜 (A.resolvent z₀) ↔ z₀ - μ⁻¹ ∈ A.resolventSet :=
  (isResolventAt_resolvent hz₀).mem_resolventSet_iff hμ

/-- **The spectrum of the resolvent.** Away from `0`, the spectrum of the bounded operator
`(z₀ - A)⁻¹` is the image of the spectrum of `A` under `z ↦ (z₀ - z)⁻¹`. -/
theorem spectrum_resolvent_sdiff_zero {z₀ : 𝕜} (hz₀ : z₀ ∈ A.resolventSet) :
    _root_.spectrum 𝕜 (A.resolvent z₀) \ {0} = (fun z ↦ (z₀ - z)⁻¹) '' A.spectrum := by
  ext μ
  constructor
  · rintro ⟨hμ, hμ0⟩
    have hμ0 : μ ≠ 0 := hμ0
    refine ⟨z₀ - μ⁻¹, fun h ↦ hμ ((mem_resolventSet_resolvent_iff hz₀ hμ0).mpr h), ?_⟩
    simp
  · rintro ⟨z, hz, rfl⟩
    have hne : z₀ - z ≠ 0 := sub_ne_zero.mpr fun h ↦ hz (h ▸ hz₀)
    refine ⟨fun h ↦ hz ?_, inv_ne_zero hne⟩
    have := (mem_resolventSet_resolvent_iff hz₀ (inv_ne_zero hne)).mp h
    rwa [inv_inv, sub_sub_cancel] at this

/-- The resolvent of an operator is differentiable within the resolvent set. On a Banach space
the resolvent set is open, and this says that the resolvent is holomorphic. -/
theorem differentiableOn_resolvent : DifferentiableOn 𝕜 A.resolvent A.resolventSet :=
  isPseudoResolventOn_resolvent.differentiableOn

/-- The resolvent of an operator is continuous on the resolvent set. -/
theorem continuousOn_resolvent : ContinuousOn A.resolvent A.resolventSet :=
  isPseudoResolventOn_resolvent.continuousOn

section Complete

variable [CompleteSpace E]

/-- If `R` is the resolvent of `A` at `z` and `|w - z| ‖R‖ < 1`, then `w` is in the resolvent
set of `A`. -/
theorem IsResolventAt.mem_resolventSet_of_norm_lt (h : A.IsResolventAt z R)
    (hw : ‖w - z‖ * ‖R‖ < 1) : w ∈ A.resolventSet := by
  have hu : IsUnit (1 + (w - z) • R) := by
    rw [← sub_neg_eq_add]
    refine IsUnit.one_sub_of_norm_lt_one ?_
    rwa [norm_neg, norm_smul]
  obtain ⟨u, hu⟩ := hu
  exact (h.of_inverse (S := ↑u⁻¹) (by rw [← hu]; exact u.mul_inv)
    (by rw [← hu]; exact u.inv_mul)).mem_resolventSet

/-- The resolvent set of an operator on a Banach space is open. -/
theorem isOpen_resolventSet : IsOpen A.resolventSet := by
  refine Metric.isOpen_iff.mpr fun z hz ↦
    ⟨1 / (‖A.resolvent z‖ + 1), by positivity, fun w hw ↦ ?_⟩
  refine (isResolventAt_resolvent hz).mem_resolventSet_of_norm_lt ?_
  rw [Metric.mem_ball, dist_eq_norm, lt_div_iff₀ (by positivity)] at hw
  nlinarith [norm_nonneg (w - z), norm_nonneg (A.resolvent z)]

/-- The spectrum of an operator on a Banach space is closed. -/
theorem isClosed_spectrum : _root_.IsClosed A.spectrum :=
  isOpen_resolventSet.isClosed_compl

/-- The resolvent of an operator on a Banach space is differentiable at every point of the
resolvent set, with derivative `-(z - A)⁻²`. -/
theorem hasDerivAt_resolvent (hz : z ∈ A.resolventSet) :
    HasDerivAt A.resolvent (-(A.resolvent z * A.resolvent z)) z :=
  isPseudoResolventOn_resolvent.hasDerivAt (isOpen_resolventSet.mem_nhds hz)

end Complete

/-! ### Operators that commute with `A` -/

/-- A bounded operator that commutes with one resolvent of `A` commutes with `A`: it maps the
graph of `A` into itself. -/
theorem IsResolventAt.map_mem_graph (h : A.IsResolventAt z R) (hS : Commute S R) {x y : E}
    (hxy : (x, y) ∈ A.graph) : (S x, S y) ∈ A.graph := by
  have h1 : R (z • S x - S y) = S x := by
    rw [← _root_.map_smul, ← _root_.map_sub, ← mul_apply_eq_comp, ← hS.eq, mul_apply_eq_comp,
      h.apply_eq hxy]
  have hg := h.mem_graph (z • S x - S y)
  rwa [h1, sub_sub_cancel] at hg

/-- A bounded operator that maps the graph of `A` into itself commutes with every resolvent of
`A`. -/
theorem IsResolventAt.commute_of_map_mem_graph (h : A.IsResolventAt z R)
    (hS : ∀ ⦃x y⦄, (x, y) ∈ A.graph → (S x, S y) ∈ A.graph) : Commute S R := by
  refine ContinuousLinearMap.ext fun y ↦ ?_
  have h1 := h.apply_eq (hS (h.mem_graph y))
  have e : z • S (R y) - S (z • R y - y) = S y := by
    rw [_root_.map_sub, _root_.map_smul, sub_sub_cancel]
  rw [e] at h1
  exact h1.symm

/-- A bounded operator that commutes with one resolvent of `A` commutes with all of them. -/
theorem IsResolventAt.commute_of_commute (h : A.IsResolventAt z R) (hS : Commute S R)
    {T : E →L[𝕜] E} (h' : A.IsResolventAt w T) : Commute S T :=
  h'.commute_of_map_mem_graph fun _ _ hxy ↦ h.map_mem_graph hS hxy

/-- **An operator with a resolvent has no proper extension with the same resolvent point.** If
the graph of `A` is contained in the graph of `C` and `z` is in both resolvent sets, then
`A = C`. -/
theorem IsResolventAt.eq_of_le {C : E →ₗ.[𝕜] E} (h : A.IsResolventAt z R)
    {R' : E →L[𝕜] E} (h' : C.IsResolventAt z R') (hle : A ≤ C) : A = C := by
  refine eq_of_eq_graph (le_antisymm (le_graph_of_le hle) fun p hp ↦ ?_)
  obtain ⟨x, y⟩ := p
  have h1 := le_graph_of_le hle (h.mem_graph (z • x - y))
  have h2 := h'.apply_eq h1
  rw [sub_sub_cancel, h'.apply_eq hp] at h2
  have h3 := h.mem_graph (z • x - y)
  rwa [← h2, sub_sub_cancel] at h3

/-! ### Resolvents relative to an operator -/

/-- The bounded operator `L` inverts `z - A` relative to the bounded operator `P`:
`(z - A) L = P`, and `L (z - A) = P` on the domain of `A`. With `P = 1` this is `IsResolventAt`.
For a projection `P` that commutes with `A`, such an `L` with `L P = L` is the resolvent of the
part of `A` in the range of `P`, extended by `0` to the kernel of `P`. -/
structure IsResolventAtOn (A : E →ₗ.[𝕜] E) (z : 𝕜) (P L : E →L[𝕜] E) : Prop where
  /-- `(z - A) L y = P y`: the vector `L y` is in the domain and `A (L y) = z L y - P y`. -/
  mem_graph : ∀ y, (L y, z • L y - P y) ∈ A.graph
  /-- `L (z - A) x = P x` for every `x` in the domain. -/
  apply_eq : ∀ ⦃x y⦄, (x, y) ∈ A.graph → L (z • x - y) = P x

/-- A resolvent relative to the identity is a resolvent. -/
theorem isResolventAtOn_one_iff : A.IsResolventAtOn z 1 R ↔ A.IsResolventAt z R :=
  ⟨fun h ↦ ⟨h.mem_graph, h.apply_eq⟩, fun h ↦ ⟨h.mem_graph, h.apply_eq⟩⟩

namespace IsResolventAtOn

variable {P P₁ P₂ L L₁ L₂ : E →L[𝕜] E}

/-- Relative resolvents add: if `L₁` and `L₂` invert `z - A` relative to `P₁` and `P₂`, then
`L₁ + L₂` inverts it relative to `P₁ + P₂`. For `P₁ + P₂ = 1` the sum is the resolvent. -/
theorem add (h₁ : A.IsResolventAtOn z P₁ L₁) (h₂ : A.IsResolventAtOn z P₂ L₂) :
    A.IsResolventAtOn z (P₁ + P₂) (L₁ + L₂) := by
  refine ⟨fun y ↦ ?_, fun x y hxy ↦ ?_⟩
  · have h := A.graph.add_mem (h₁.mem_graph y) (h₂.mem_graph y)
    have e : z • L₁ y - P₁ y + (z • L₂ y - P₂ y) = z • (L₁ + L₂) y - (P₁ + P₂) y := by
      simp only [_root_.add_apply, smul_add]
      abel
    rwa [Prod.mk_add_mk, e] at h
  · rw [_root_.add_apply, h₁.apply_eq hxy, h₂.apply_eq hxy, _root_.add_apply]

/-- If the two operators that a pair of relative resolvents refers to add up to `1`, the sum of
the relative resolvents is the resolvent. -/
theorem isResolventAt_add (h₁ : A.IsResolventAtOn z P₁ L₁) (h₂ : A.IsResolventAtOn z P₂ L₂)
    (h : P₁ + P₂ = 1) : A.IsResolventAt z (L₁ + L₂) :=
  isResolventAtOn_one_iff.mp (h ▸ h₁.add h₂)

/-- A relative resolvent commutes with the operator it refers to. -/
theorem commute (h : A.IsResolventAtOn z P L) : Commute L P := by
  refine ContinuousLinearMap.ext fun y ↦ ?_
  have h1 := h.apply_eq (h.mem_graph y)
  rwa [sub_sub_cancel] at h1

/-- The first resolvent identity `L - L' = (w - z) L L'` for resolvents relative to the same
`P`, when `L P = L` and `P L' = L'`. -/
theorem sub_eq {L' : E →L[𝕜] E} (h : A.IsResolventAtOn z P L) (h' : A.IsResolventAtOn w P L')
    (hL : L * P = L) (hL' : P * L' = L') : L - L' = (w - z) • (L * L') := by
  refine ContinuousLinearMap.ext fun y ↦ ?_
  have h1 := h.apply_eq (h'.mem_graph y)
  have e : z • L' y - (w • L' y - P y) = P y - (w - z) • L' y := by module
  have e1 : L (P y) = L y := DFunLike.congr_fun hL y
  have e2 : P (L' y) = L' y := DFunLike.congr_fun hL' y
  rw [e, _root_.map_sub, _root_.map_smul, e1, e2] at h1
  simp only [_root_.sub_apply, _root_.smul_apply, mul_apply_eq_comp]
  exact sub_eq_iff_eq_add'.mpr (sub_eq_iff_eq_add.mp h1)

end IsResolventAtOn

/-! ### Generalized eigenspaces -/

/-- The generalized eigenspace `ker (A - μ)^k` of a partial operator, on its natural domain:
`x` is in it when `x, (A - μ) x, …, (A - μ)^(k-1) x` are in the domain of `A` and
`(A - μ)^k x = 0`. -/
def genEigenspace (A : E →ₗ.[𝕜] E) (μ : 𝕜) : ℕ → Submodule 𝕜 E
  | 0 => ⊥
  | k + 1 => (A.graph ⊓ (genEigenspace A μ k).comap
      (LinearMap.snd 𝕜 E E - μ • LinearMap.fst 𝕜 E E)).map (LinearMap.fst 𝕜 E E)

/-- The generalized eigenspace of order `0` is `0`. -/
@[simp]
theorem genEigenspace_zero (A : E →ₗ.[𝕜] E) (μ : 𝕜) : A.genEigenspace μ 0 = ⊥ := rfl

/-- `x` is in `ker (A - μ)^(k+1)` when `x` is in the domain and `(A - μ) x` is in
`ker (A - μ)^k`. -/
theorem mem_genEigenspace_succ {μ : 𝕜} {k : ℕ} {x : E} :
    x ∈ A.genEigenspace μ (k + 1) ↔
      ∃ y, (x, y) ∈ A.graph ∧ y - μ • x ∈ A.genEigenspace μ k := by
  simp only [genEigenspace, Submodule.mem_map, Submodule.mem_inf, Submodule.mem_comap,
    LinearMap.sub_apply, LinearMap.snd_apply, LinearMap.smul_apply, LinearMap.fst_apply,
    Prod.exists, exists_and_right, exists_eq_right]

/-- The generalized eigenspace of order `1` is the eigenspace: `A x = μ x`. -/
theorem mem_genEigenspace_one {μ : 𝕜} {x : E} :
    x ∈ A.genEigenspace μ 1 ↔ (x, μ • x) ∈ A.graph := by
  rw [mem_genEigenspace_succ]
  constructor
  · rintro ⟨y, hxy, hy⟩
    rwa [← sub_eq_zero.mp ((Submodule.mem_bot 𝕜).mp hy)]
  · exact fun h ↦ ⟨μ • x, h, by simp⟩

/-- The generalized eigenspaces increase with the order. -/
theorem genEigenspace_mono (A : E →ₗ.[𝕜] E) (μ : 𝕜) : Monotone (A.genEigenspace μ) := by
  refine monotone_nat_of_le_succ fun k ↦ ?_
  induction k with
  | zero => exact bot_le
  | succ k ih =>
    intro x hx
    obtain ⟨y, hxy, hy⟩ := mem_genEigenspace_succ.mp hx
    exact mem_genEigenspace_succ.mpr ⟨y, hxy, ih hy⟩

/-- A point of the resolvent set has no generalized eigenvectors. -/
theorem genEigenspace_eq_bot_of_mem_resolventSet (hz : z ∈ A.resolventSet) (k : ℕ) :
    A.genEigenspace z k = ⊥ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    refine (Submodule.eq_bot_iff _).mpr fun x hx ↦ ?_
    obtain ⟨y, hxy, hu⟩ := mem_genEigenspace_succ.mp hx
    rw [ih, Submodule.mem_bot, sub_eq_zero] at hu
    have h := smul_resolvent_apply_of_mem_graph_smul hz (hu ▸ hxy)
    rwa [sub_self, zero_smul, eq_comm] at h

/-! ### Bounded operators -/

/-- The graph of an everywhere defined operator `T` is `{(x, T x)}`. -/
theorem mem_graph_toPMap_top {T : E →ₗ[𝕜] E} {x y : E} :
    (x, y) ∈ (T.toPMap ⊤).graph ↔ T x = y := by
  rw [mem_graph_iff]
  exact ⟨by rintro ⟨u, rfl, rfl⟩; rfl, fun h ↦ ⟨⟨x, Submodule.mem_top⟩, rfl, h⟩⟩

/-- For an everywhere defined bounded operator `T`, a resolvent at `z` is a two-sided inverse of
`z - T` in the algebra of bounded operators. -/
theorem isResolventAt_toPMap_top_iff {T : E →L[𝕜] E} :
    (T.toLinearMap.toPMap ⊤).IsResolventAt z R ↔
      (algebraMap 𝕜 (E →L[𝕜] E) z - T) * R = 1 ∧ R * (algebraMap 𝕜 (E →L[𝕜] E) z - T) = 1 := by
  simp only [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.ext_iff, mul_apply_eq_comp,
    _root_.sub_apply, _root_.smul_apply, one_apply_eq_self]
  constructor
  · intro h
    refine ⟨fun y ↦ ?_, fun x ↦ h.apply_eq (mem_graph_toPMap_top.mpr rfl)⟩
    have hy : T (R y) = z • R y - y := mem_graph_toPMap_top.mp (h.mem_graph y)
    rw [hy, sub_sub_cancel]
  · rintro ⟨h1, h2⟩
    refine ⟨fun y ↦ mem_graph_toPMap_top.mpr ?_, fun x y hxy ↦ ?_⟩
    · exact eq_sub_of_add_eq (by rw [add_comm]; exact (sub_eq_iff_eq_add.mp (h1 y)).symm)
    · rw [← mem_graph_toPMap_top.mp hxy]
      exact h2 x

/-- For an everywhere defined bounded operator, the resolvent set is Mathlib's resolvent set of
an element of the algebra of bounded operators. -/
theorem resolventSet_toPMap_top (T : E →L[𝕜] E) :
    (T.toLinearMap.toPMap ⊤).resolventSet = _root_.resolventSet 𝕜 T := by
  ext z
  rw [spectrum.mem_resolventSet_iff, isUnit_iff_exists]
  exact exists_congr fun R ↦ isResolventAt_toPMap_top_iff

/-- For an everywhere defined bounded operator, the resolvent is Mathlib's resolvent of an
element of the algebra of bounded operators. -/
theorem resolvent_toPMap_top (T : E →L[𝕜] E) :
    (T.toLinearMap.toPMap ⊤).resolvent = _root_.resolvent T := by
  ext1 z
  by_cases hz : z ∈ _root_.resolventSet 𝕜 T
  · have hu := spectrum.mem_resolventSet_iff.mp hz
    exact (isResolventAt_toPMap_top_iff.mpr
      ⟨Ring.mul_inverse_cancel _ hu, Ring.inverse_mul_cancel _ hu⟩).resolvent_eq
  · rw [resolvent_of_notMem (by rwa [resolventSet_toPMap_top]), _root_.resolvent,
      Ring.inverse_non_unit _ hz]

/-- For an everywhere defined operator, the generalized eigenspaces are Mathlib's. -/
theorem genEigenspace_toPMap_top (T : E →ₗ[𝕜] E) (μ : 𝕜) (k : ℕ) :
    (T.toPMap ⊤).genEigenspace μ k = Module.End.genEigenspace T μ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    ext x
    rw [mem_genEigenspace_succ, ih, Module.End.mem_genEigenspace_nat,
      Module.End.genEigenspace_nat, pow_succ, LinearMap.mem_ker, mul_apply_eq_comp]
    constructor
    · rintro ⟨y, hxy, hy⟩
      rw [← mem_graph_toPMap_top.mp hxy] at hy
      simpa using hy
    · exact fun h ↦ ⟨T x, mem_graph_toPMap_top.mpr rfl, by simpa using h⟩

/-- An eigenvalue of a bounded operator is in its spectrum. -/
theorem _root_.ContinuousLinearMap.mem_spectrum_of_apply_eq_smul {T : E →L[𝕜] E} {μ : 𝕜}
    {x : E} (hx : T x = μ • x) (hx0 : x ≠ 0) : μ ∈ _root_.spectrum 𝕜 T := fun h ↦
  mem_spectrum_of_mem_graph_smul (A := T.toLinearMap.toPMap ⊤) (mem_graph_toPMap_top.mpr hx) hx0
    (by rwa [resolventSet_toPMap_top])

/-! ### Bijectivity of the shift, and the real resolvent -/

/-- A resolvent is a bounded two-sided inverse of the shift on the domain, written with elements
of the domain instead of the graph: `R y` is in the domain, `R (z x - A x) = x` for `x` in the
domain, and `z R y - A (R y) = y` for every `y`. -/
theorem isResolventAt_iff :
    A.IsResolventAt z R ↔ ∃ hR : ∀ y, R y ∈ A.domain,
      (∀ x : A.domain, R (z • (x : E) - A x) = x) ∧ ∀ y, z • R y - A ⟨R y, hR y⟩ = y := by
  constructor
  · intro h
    exact ⟨h.mem_domain, h.resolvent_apply, fun y ↦ by rw [h.apply_resolvent, sub_sub_cancel]⟩
  · rintro ⟨hR, hl, hr⟩
    refine ⟨fun y ↦ (image_iff (hR y)).mp ?_, fun x y hxy ↦ ?_⟩
    · exact sub_eq_iff_eq_add.mpr (sub_eq_iff_eq_add'.mp (hr y))
    · obtain ⟨u, rfl, rfl⟩ := (mem_graph_iff A).mp hxy
      exact hl u

/-- **The textbook definition of the resolvent set.** For a closed operator on a Banach space,
`z` is in the resolvent set exactly when `z - A` is a bijection from the domain onto the space:
its inverse is bounded by the closed graph theorem. -/
theorem mem_resolventSet_iff_bijective [CompleteSpace E] (hA : A.IsClosed) :
    z ∈ A.resolventSet ↔ Function.Bijective (z • A.domain.subtype - A.toFun) := by
  constructor
  · rintro ⟨R, h⟩
    exact h.bijective
  · intro hbij
    -- the inverse of the shift, as a linear map with a closed graph
    obtain ⟨e, he⟩ : ∃ e : A.domain ≃ₗ[𝕜] E, ∀ x : A.domain, e x = z • (x : E) - A x :=
      ⟨LinearEquiv.ofBijective _ hbij, fun _ ↦ rfl⟩
    obtain ⟨g, hg⟩ : ∃ g : E →ₗ[𝕜] E, ∀ y, g y = (e.symm y : E) :=
      ⟨A.domain.subtype.comp e.symm.toLinearMap, fun _ ↦ rfl⟩
    have hmem (y : E) : (g y, z • g y - y) ∈ A.graph := by
      have h1 := A.mem_graph (e.symm y)
      have h2 : A (e.symm y) = z • (e.symm y : E) - y := by
        have h3 := he (e.symm y)
        rw [e.apply_symm_apply] at h3
        rw [eq_sub_iff_add_eq, add_comm, ← eq_sub_iff_add_eq]
        exact h3
      rwa [h2, ← hg] at h1
    have happ : ∀ ⦃x w⦄, (x, w) ∈ A.graph → g (z • x - w) = x := fun x w hxw ↦ by
      obtain ⟨u, rfl, rfl⟩ := (mem_graph_iff A).mp hxw
      rw [hg, ← he, e.symm_apply_apply]
    have hgraph : (g.graph : Set (E × E)) =
        (fun p : E × E ↦ (p.2, z • p.2 - p.1)) ⁻¹' (A.graph : Set (E × E)) := by
      ext ⟨y, x⟩
      simp only [SetLike.mem_coe, Set.mem_preimage, LinearMap.mem_graph_iff]
      constructor
      · rintro rfl
        exact hmem y
      · intro h
        have h1 := happ h
        rwa [sub_sub_cancel, eq_comm] at h1
    have hclosed : _root_.IsClosed (g.graph : Set (E × E)) := by
      rw [hgraph]
      exact hA.preimage (continuous_snd.prodMk ((continuous_snd.const_smul z).sub continuous_fst))
    exact ⟨ContinuousLinearMap.ofIsClosedGraph hclosed, hmem, happ⟩

section Real

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {B : F →ₗ.[ℝ] F}
  {t : ℝ}

/-- For a closed operator on a real Banach space, the resolvent set is the real resolvent set
`realResolventSet`, defined by bijectivity: the shift is bijective on the domain exactly when it
has a bounded inverse. -/
theorem realResolventSet_eq_resolventSet (hB : B.IsClosed) :
    B.realResolventSet = B.resolventSet :=
  Set.ext fun _ ↦ (mem_resolventSet_iff_bijective hB).symm

/-- For a closed operator on a real Banach space, the resolvent is the real resolvent
`realResolvent`, the bounded inverse built from the closed graph theorem. -/
theorem realResolvent_eq_resolvent (hB : B.IsClosed) (ht : t ∈ B.realResolventSet) :
    B.realResolvent hB ht = B.resolvent t :=
  (IsResolventAt.resolvent_eq (isResolventAt_iff.mpr ⟨B.realResolvent_mem_domain hB ht,
    B.realResolvent_shift hB ht, B.shift_realResolvent hB ht⟩)).symm

end Real

/-! ### The spectral bound -/

section SpectralBound

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- **The spectral bound** `s(A)` of an operator on a complex space: the supremum, in
`[-∞, ∞]`, of the real parts of the points of its spectrum. It is `-∞` when the spectrum is
empty. -/
def spectralBound (A : X →ₗ.[ℂ] X) : EReal :=
  sSup ((fun z : ℂ ↦ (z.re : EReal)) '' A.spectrum)

/-- The real part of a point of the spectrum is at most the spectral bound. -/
theorem re_le_spectralBound {A : X →ₗ.[ℂ] X} {z : ℂ} (hz : z ∈ A.spectrum) :
    (z.re : EReal) ≤ A.spectralBound :=
  le_sSup ⟨z, hz, rfl⟩

end SpectralBound

end LinearPMap
