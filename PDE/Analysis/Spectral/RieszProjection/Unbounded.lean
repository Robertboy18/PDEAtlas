/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import PDE.Analysis.Operator.Resolvent.InvariantSubspace
public import PDE.Analysis.Spectral.RieszProjection.PseudoResolvent

/-!
# The Riesz projection of an unbounded operator

Let `A` be an operator on a complex Banach space and `C(c, r)` a circle in its resolvent set. The
Riesz projection `P = (2πi)⁻¹ ∮ (z - A)⁻¹ dz` maps into the domain of `A`, commutes with `A`, and
is a projection. It fixes the generalized eigenvectors for eigenvalues inside the circle and
kills those for eigenvalues outside. If the circle surrounds no point of the spectrum other than
`c` and `P` has finite rank `k`, the range of `P` is the generalized eigenspace `ker (A - c)^k`.
This is how an isolated eigenvalue of finite multiplicity of a semigroup generator is split off
(`StronglyContinuousSemigroup.IsComplexLinear.exists_spectral_gap`). The two parts of `A`, on
the range and on the kernel of `P`, appear here through resolvents relative to `P` and to `1 - P`
(`LinearPMap.IsResolventAtOn`), which is what the applications use. Their spectra as sets are
known only for bounded operators (`spectrum_rieszInnerPart_eq`, `spectrum_rieszOuterPart_eq`).

## Main results

* `dunfordIntegral_resolvent_mem_graph`, `dunfordIntegral_resolvent_apply_of_mem_graph`: each
  Dunford integral `Φ(g)` maps into the domain, with `A Φ(g) y = Φ(z g) y - ((2πi)⁻¹ ∮ g) y` and
  `Φ(g) A x = Φ(z g) x - ((2πi)⁻¹ ∮ g) x`.
* `rieszProjection_resolvent_mem_domain`, `rieszProjection_resolvent_map_mem_graph`,
  `isIdempotentElem_rieszProjection_resolvent`, `commute_rieszProjection_resolvent`: `P` maps
  into the domain, commutes with `A` and with every bounded operator that commutes with `A`, and
  is a projection for `r > 0`.
* `rieszProjection_resolvent_apply_eq_self_of_mem_genEigenspace`,
  `rieszProjection_resolvent_apply_eq_zero_of_mem_genEigenspace`: `P` fixes `ker (A - μ)^k` for
  `μ` inside the circle and kills it for `μ` outside the closed disc.
* `range_rieszProjection_resolvent_eq_genEigenspace`: for an isolated point `c` of the spectrum
  and a projection of finite rank `k`, the range of `P` is `ker (A - c)^k`.
* `rieszProjection_resolvent_mul_of_disjoint`, `isIdempotentElem_sum_rieszProjection_resolvent`:
  the projections for disjoint closed discs annihilate each other and add up to a projection.
* `isResolventAtOn_dunfordIntegral_of_notMem_closedBall`,
  `isResolventAtOn_neg_dunfordIntegral_of_mem_ball`: `z - A` is invertible relative to `P` for
  `z` outside the closed disc, and relative to `1 - P` for `z` inside the open disc. The points
  of the circle are not covered.
* `closedBall_sdiff_subset_resolventSet`: if the spectrum in a half-plane is a finite set whose
  points are more than `2r` apart and more than `r` from the boundary, the closed discs of radius
  `r` around them, without their centres, lie in the resolvent set.

## How it works

The resolvent of `A` is a pseudo-resolvent on the open resolvent set
(`LinearPMap.isPseudoResolventOn_resolvent`), so idempotence, commutation and the products for
disjoint discs come from `PDE.Analysis.Spectral.RieszProjection.PseudoResolvent`. What is new is
the relation with `A`, and it is algebra. For a point `z₀` of the circle, the domain rule
`Φ(g) = ((2πi)⁻¹ ∮ g) R z₀ + R z₀ Φ((z₀ - z) g)` writes `Φ(g)` as `R z₀` applied to a bounded
operator, so `Φ(g)` maps into the domain, and the two identities above follow. With `g = 1`, the
projection `P` maps into the domain and commutes with `A`. With `g = (z - μ)⁻¹` and `A x = μ x`,
`P x` is the winding number of the circle around `μ` times `x`, so `P` fixes the eigenvectors
inside the circle and kills those outside. Induction on the order does the same for generalized
eigenvectors. If the circle surrounds only `c` and `P` has finite rank, `A` maps the range of `P`
into itself, and an eigenvector there for another eigenvalue would be both fixed and killed by
`P`. On the finite-dimensional range this makes `A - c` nilpotent (`le_iSup_genEigenspace_inf`).
For a bounded operator and the centre `0`, the eigenvector statements are
`rieszInner_apply_eq_self_of_apply_eq_smul` and `rieszInner_apply_eq_zero_of_apply_eq_smul`.
-/

@[expose] public noncomputable section

open Complex Metric Set PDE.Analysis.Spectral
open scoped Real

namespace LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {A : E →ₗ.[ℂ] E} {c μ : ℂ} {r : ℝ} {g : ℂ → ℂ} {x y : E}

/-- `Φ(g)` maps into the domain of `A`, and `A Φ(g) y = Φ(z g) y - ((2πi)⁻¹ ∮ g) y`. -/
theorem dunfordIntegral_resolvent_mem_graph (hr : 0 ≤ r) (hs : sphere c r ⊆ A.resolventSet)
    (hg : ContinuousOn g (sphere c r)) (y : E) :
    (dunfordIntegral A.resolvent c r g y,
      dunfordIntegral A.resolvent c r (fun z ↦ z * g z) y -
        ((2 * π * I)⁻¹ * ∮ z in C(c, r), g z) • y) ∈ A.graph := by
  obtain ⟨z₀, hz₀⟩ := (NormedSpace.sphere_nonempty (x := c)).mpr hr
  have hRc : ContinuousOn A.resolvent (sphere c r) := continuousOn_resolvent.mono hs
  have h1 := dunfordIntegral_eq_smul_add_mul isPseudoResolventOn_resolvent hr hs (hs hz₀) hg
  have h2 : dunfordIntegral A.resolvent c r (fun z ↦ (z₀ - z) * g z) =
      z₀ • dunfordIntegral A.resolvent c r g -
        dunfordIntegral A.resolvent c r (fun z ↦ z * g z) := by
    have hg₁ : ContinuousOn (fun z : ℂ ↦ z₀ * g z) (sphere c r) := continuousOn_const.mul hg
    have hg₂ : ContinuousOn (fun z : ℂ ↦ z * g z) (sphere c r) := continuousOn_id.mul hg
    rw [← dunfordIntegral_const_mul, ← dunfordIntegral_sub hr hRc hg₁ hg₂]
    exact dunfordIntegral_congr hr fun z _ ↦ sub_mul z₀ z (g z)
  rw [h2] at h1
  generalize dunfordIntegral A.resolvent c r g = Φ at h1 ⊢
  generalize dunfordIntegral A.resolvent c r (fun z ↦ z * g z) = Ψ at h1 ⊢
  generalize (2 * π * I)⁻¹ * ∮ z in C(c, r), g z = k at h1 ⊢
  have hΦ : A.resolvent z₀ ((k • (1 : E →L[ℂ] E) + (z₀ • Φ - Ψ)) y) = Φ y := by
    conv_rhs => rw [h1]
    simp only [_root_.add_apply, _root_.smul_apply, _root_.sub_apply, one_apply_eq_self,
      mul_apply_eq_comp, _root_.map_add, _root_.map_smul, _root_.map_sub]
  have hg' := (isResolventAt_resolvent (hs hz₀)).mem_graph
    ((k • (1 : E →L[ℂ] E) + (z₀ • Φ - Ψ)) y)
  have e : z₀ • Φ y - (k • (1 : E →L[ℂ] E) + (z₀ • Φ - Ψ)) y = Ψ y - k • y := by
    simp only [_root_.add_apply, _root_.smul_apply, _root_.sub_apply, one_apply_eq_self]
    abel
  rwa [hΦ, e] at hg'

/-- On the domain of `A`, `Φ(g) A x = Φ(z g) x - ((2πi)⁻¹ ∮ g) x`. -/
theorem dunfordIntegral_resolvent_apply_of_mem_graph (hr : 0 ≤ r)
    (hs : sphere c r ⊆ A.resolventSet) (hg : ContinuousOn g (sphere c r))
    (hxy : (x, y) ∈ A.graph) :
    dunfordIntegral A.resolvent c r g y =
      dunfordIntegral A.resolvent c r (fun z ↦ z * g z) x -
        ((2 * π * I)⁻¹ * ∮ z in C(c, r), g z) • x := by
  obtain ⟨z₀, hz₀⟩ := (NormedSpace.sphere_nonempty (x := c)).mpr hr
  have hc : Commute (dunfordIntegral A.resolvent c r g) (A.resolvent z₀) :=
    (commute_dunfordIntegral hr
      (fun z hz ↦ isPseudoResolventOn_resolvent.commute (hs hz₀) (hs hz)) g).symm
  exact A.mem_graph_snd_inj ((isResolventAt_resolvent (hs hz₀)).map_mem_graph hc hxy)
    (dunfordIntegral_resolvent_mem_graph hr hs hg x) rfl

/-- A bounded operator that maps the graph of `A` into itself commutes with every Dunford
integral of the resolvent of `A`. -/
theorem commute_dunfordIntegral_resolvent (hr : 0 ≤ r) (hs : sphere c r ⊆ A.resolventSet)
    {S : E →L[ℂ] E} (hS : ∀ ⦃x y⦄, (x, y) ∈ A.graph → (S x, S y) ∈ A.graph) (g : ℂ → ℂ) :
    Commute S (dunfordIntegral A.resolvent c r g) :=
  commute_dunfordIntegral hr
    (fun _ hz ↦ (isResolventAt_resolvent (hs hz)).commute_of_map_mem_graph hS) g

/-- **The Riesz projection commutes with what commutes with `A`.** A bounded operator that maps
the graph of `A` into itself commutes with the Riesz projection of `A`. -/
theorem commute_rieszProjection_resolvent (hr : 0 ≤ r) (hs : sphere c r ⊆ A.resolventSet)
    {S : E →L[ℂ] E} (hS : ∀ ⦃x y⦄, (x, y) ∈ A.graph → (S x, S y) ∈ A.graph) :
    Commute S (rieszProjection A.resolvent c r) :=
  commute_dunfordIntegral_resolvent hr hs hS 1

/-- **`A P` is bounded.** The Riesz projection `P` maps into the domain of `A`, and
`A P y = (2πi)⁻¹ ∮ z (z - A)⁻¹ y dz`. -/
theorem rieszProjection_resolvent_mem_graph (hr : 0 ≤ r) (hs : sphere c r ⊆ A.resolventSet)
    (y : E) :
    (rieszProjection A.resolvent c r y, dunfordIntegral A.resolvent c r (fun z ↦ z) y) ∈
      A.graph := by
  have h := dunfordIntegral_resolvent_mem_graph (g := 1) hr hs continuousOn_const y
  have h0 : (∮ _z in C(c, r), (1 : ℂ)) = 0 := by
    simpa using circleIntegral.integral_sub_zpow_of_ne (n := 0) (by norm_num) c c r
  simp only [Pi.one_apply, mul_one, h0, mul_zero, zero_smul, sub_zero] at h
  exact h

/-- The Riesz projection of `A` maps into the domain of `A`. -/
theorem rieszProjection_resolvent_mem_domain (hr : 0 ≤ r) (hs : sphere c r ⊆ A.resolventSet)
    (y : E) : rieszProjection A.resolvent c r y ∈ A.domain :=
  mem_domain_of_mem_graph (rieszProjection_resolvent_mem_graph hr hs y)

/-- **The Riesz projection commutes with `A`**: if `A x = y`, then `A (P x) = P y`. -/
theorem rieszProjection_resolvent_map_mem_graph (hr : 0 ≤ r)
    (hs : sphere c r ⊆ A.resolventSet) (hxy : (x, y) ∈ A.graph) :
    (rieszProjection A.resolvent c r x, rieszProjection A.resolvent c r y) ∈ A.graph := by
  obtain ⟨z₀, hz₀⟩ := (NormedSpace.sphere_nonempty (x := c)).mpr hr
  exact (isResolventAt_resolvent (hs hz₀)).map_mem_graph (commute_rieszProjection hr
    fun z hz ↦ isPseudoResolventOn_resolvent.commute (hs hz₀) (hs hz)).symm hxy

/-- **The Riesz projection of an operator is a projection**, for a circle of positive radius in
the resolvent set. -/
theorem isIdempotentElem_rieszProjection_resolvent (hr : 0 < r)
    (hs : sphere c r ⊆ A.resolventSet) : IsIdempotentElem (rieszProjection A.resolvent c r) :=
  isIdempotentElem_rieszProjection isPseudoResolventOn_resolvent isOpen_resolventSet hr hs

/-- **Projections for disjoint discs annihilate each other.** -/
theorem rieszProjection_resolvent_mul_of_disjoint {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁)
    (h₂ : 0 ≤ r₂) (hs₁ : sphere c₁ r₁ ⊆ A.resolventSet) (hs₂ : sphere c₂ r₂ ⊆ A.resolventSet)
    (hdisj : Disjoint (closedBall c₁ r₁) (closedBall c₂ r₂)) :
    rieszProjection A.resolvent c₁ r₁ * rieszProjection A.resolvent c₂ r₂ = 0 :=
  rieszProjection_mul_rieszProjection_of_disjoint isPseudoResolventOn_resolvent h₁ h₂ hs₁ hs₂
    hdisj

/-- **Projections for disjoint discs add up to a projection.** For finitely many circles of
radius `r` in the resolvent set whose closed discs are pairwise disjoint, the sum of the Riesz
projections is idempotent. -/
theorem isIdempotentElem_sum_rieszProjection_resolvent {Λ : Finset ℂ} (hr : 0 < r)
    (hs : ∀ μ ∈ Λ, sphere μ r ⊆ A.resolventSet)
    (hd : ∀ μ ∈ Λ, ∀ ν ∈ Λ, μ ≠ ν → Disjoint (closedBall μ r) (closedBall ν r)) :
    IsIdempotentElem (∑ μ ∈ Λ, rieszProjection A.resolvent μ r) := by
  rw [IsIdempotentElem, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun μ hμ ↦ ?_
  rw [Finset.sum_eq_single μ]
  · exact (isIdempotentElem_rieszProjection_resolvent hr (hs μ hμ)).eq
  · exact fun ν hν hne ↦ rieszProjection_resolvent_mul_of_disjoint hr.le hr.le (hs μ hμ)
      (hs ν hν) (hd μ hμ ν hν hne.symm)
  · exact fun h ↦ absurd hμ h

/-- **The resolvent relative to the Riesz projection, outside the disc.** For `z` outside the
closed disc, `Φ((z - w)⁻¹)` inverts `z - A` relative to the Riesz projection `P`:
`(z - A) Φ = P` and `Φ (z - A) = P` on the domain. In words: on the range of `P` the operator
has no spectrum outside the closed disc. The two identities are the domain rule for
`g(w) = (z - w)⁻¹`, whose circle integral vanishes because `z` is outside. -/
theorem isResolventAtOn_dunfordIntegral_of_notMem_closedBall (hr : 0 ≤ r)
    (hs : sphere c r ⊆ A.resolventSet) {z : ℂ} (hz : z ∉ closedBall c r) :
    A.IsResolventAtOn z (rieszProjection A.resolvent c r)
      (dunfordIntegral A.resolvent c r fun w ↦ (z - w)⁻¹) := by
  have hzs : z ∉ sphere c r := fun h ↦ hz (sphere_subset_closedBall h)
  have hne : ∀ w ∈ sphere c r, z - w ≠ 0 := fun w hw h ↦ hzs (sub_eq_zero.mp h ▸ hw)
  have hg : ContinuousOn (fun w : ℂ ↦ (z - w)⁻¹) (sphere c r) :=
    (continuousOn_const.sub continuousOn_id).inv₀ hne
  have hRc : ContinuousOn A.resolvent (sphere c r) := continuousOn_resolvent.mono hs
  have hkey := dunfordIntegral_id_mul_sub_inv hr hRc hzs
  have hc : (∮ w in C(c, r), (z - w)⁻¹) = 0 := by
    have h1 : (fun w : ℂ ↦ (z - w)⁻¹) = fun w ↦ (-1 : ℂ) • (w - z)⁻¹ := by
      ext w
      rw [smul_eq_mul, neg_one_mul, ← inv_neg, neg_sub]
    rw [h1, circleIntegral.integral_smul, circleIntegral_sub_inv_of_notMem_closedBall hr hz,
      smul_zero]
  refine ⟨fun y ↦ ?_, fun x y hxy ↦ ?_⟩
  · have h := dunfordIntegral_resolvent_mem_graph hr hs hg y
    rwa [hkey, hc, mul_zero, zero_smul, sub_zero] at h
  · have h := dunfordIntegral_resolvent_apply_of_mem_graph hr hs hg hxy
    rw [hkey, hc, mul_zero, zero_smul, sub_zero, _root_.sub_apply, _root_.smul_apply] at h
    rw [_root_.map_sub, _root_.map_smul, h, sub_sub_cancel]

/-- **The resolvent relative to the complementary projection, inside the disc.** For `z`
inside the open disc, `-Φ((z - w)⁻¹)` inverts `z - A` relative to `1 - P`. In words: on the
kernel of `P` the operator has no spectrum inside the open disc. -/
theorem isResolventAtOn_neg_dunfordIntegral_of_mem_ball (hr : 0 ≤ r)
    (hs : sphere c r ⊆ A.resolventSet) {z : ℂ} (hz : z ∈ ball c r) :
    A.IsResolventAtOn z (1 - rieszProjection A.resolvent c r)
      (-dunfordIntegral A.resolvent c r fun w ↦ (z - w)⁻¹) := by
  have hzs : z ∉ sphere c r := fun h ↦ (mem_ball.mp hz).ne (mem_sphere.mp h)
  have hne : ∀ w ∈ sphere c r, z - w ≠ 0 := fun w hw h ↦ hzs (sub_eq_zero.mp h ▸ hw)
  have hg : ContinuousOn (fun w : ℂ ↦ (z - w)⁻¹) (sphere c r) :=
    (continuousOn_const.sub continuousOn_id).inv₀ hne
  have hRc : ContinuousOn A.resolvent (sphere c r) := continuousOn_resolvent.mono hs
  have hkey := dunfordIntegral_id_mul_sub_inv hr hRc hzs
  have hc : (2 * π * I)⁻¹ * (∮ w in C(c, r), (z - w)⁻¹) = -1 := by
    have h1 : (fun w : ℂ ↦ (z - w)⁻¹) = fun w ↦ (-1 : ℂ) • (w - z)⁻¹ := by
      ext w
      rw [smul_eq_mul, neg_one_mul, ← inv_neg, neg_sub]
    rw [h1, circleIntegral.integral_smul, circleIntegral.integral_sub_inv_of_mem_ball hz,
      smul_eq_mul, mul_left_comm, inv_mul_cancel₀ two_pi_I_ne_zero, mul_one]
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = dunfordIntegral A.resolvent c r fun w ↦ (z - w)⁻¹ := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = rieszProjection A.resolvent c r := ⟨_, rfl⟩
  rw [← hΦ, ← hP] at hkey ⊢
  refine ⟨fun y ↦ ?_, fun x y hxy ↦ ?_⟩
  · have h := dunfordIntegral_resolvent_mem_graph hr hs hg y
    rw [← hΦ, hkey, hc] at h
    have h2 := A.graph.neg_mem h
    have e : -((z • Φ - P) y - (-1 : ℂ) • y) = z • (-Φ) y - (1 - P) y := by
      simp only [_root_.sub_apply, _root_.smul_apply, _root_.neg_apply, one_apply_eq_self]
      module
    rwa [Prod.neg_mk, e] at h2
  · have h := dunfordIntegral_resolvent_apply_of_mem_graph hr hs hg hxy
    rw [← hΦ, hkey, hc] at h
    rw [_root_.neg_apply, _root_.map_sub, _root_.map_smul, h]
    simp only [_root_.sub_apply, _root_.smul_apply, one_apply_eq_self]
    module

/-- On an eigenvector `A x = μ x` with `μ` off the circle, the Riesz projection is
multiplication by the winding number `(2πi)⁻¹ ∮ (z - μ)⁻¹ dz` of the circle around `μ`. -/
theorem rieszProjection_resolvent_apply_of_mem_graph_smul (hr : 0 ≤ r)
    (hs : sphere c r ⊆ A.resolventSet) (hμ : μ ∉ sphere c r) (hx : (x, μ • x) ∈ A.graph) :
    rieszProjection A.resolvent c r x = ((2 * π * I)⁻¹ * ∮ z in C(c, r), (z - μ)⁻¹) • x := by
  have hne : ∀ z ∈ sphere c r, z - μ ≠ 0 := fun z hz h ↦ hμ (sub_eq_zero.mp h ▸ hz)
  have hg : ContinuousOn (fun z : ℂ ↦ (z - μ)⁻¹) (sphere c r) :=
    (continuousOn_id.sub continuousOn_const).inv₀ hne
  have hg₁ : ContinuousOn (fun z : ℂ ↦ z * (z - μ)⁻¹) (sphere c r) := continuousOn_id.mul hg
  have hg₂ : ContinuousOn (fun z : ℂ ↦ μ * (z - μ)⁻¹) (sphere c r) := continuousOn_const.mul hg
  have hRc : ContinuousOn A.resolvent (sphere c r) := continuousOn_resolvent.mono hs
  have h1 := dunfordIntegral_resolvent_apply_of_mem_graph hr hs hg hx
  have h2 : rieszProjection A.resolvent c r =
      dunfordIntegral A.resolvent c r (fun z ↦ z * (z - μ)⁻¹) -
        μ • dunfordIntegral A.resolvent c r (fun z ↦ (z - μ)⁻¹) := by
    rw [← dunfordIntegral_const_mul, ← dunfordIntegral_sub hr hRc hg₁ hg₂]
    exact dunfordIntegral_congr hr fun z hz ↦ by
      rw [Pi.one_apply, ← sub_mul, mul_inv_cancel₀ (hne z hz)]
  rw [h2, _root_.sub_apply, _root_.smul_apply, ← _root_.map_smul, h1, sub_sub_cancel]

/-- The Riesz projection fixes an eigenvector whose eigenvalue is inside the circle. -/
theorem rieszProjection_resolvent_apply_eq_self_of_mem_graph_smul (hr : 0 ≤ r)
    (hs : sphere c r ⊆ A.resolventSet) (hμ : μ ∈ ball c r) (hx : (x, μ • x) ∈ A.graph) :
    rieszProjection A.resolvent c r x = x := by
  rw [rieszProjection_resolvent_apply_of_mem_graph_smul hr hs
    (fun h ↦ (mem_ball.mp hμ).ne (mem_sphere.mp h)) hx,
    circleIntegral.integral_sub_inv_of_mem_ball hμ, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul]

/-- The Riesz projection kills an eigenvector whose eigenvalue is outside the closed disc. -/
theorem rieszProjection_resolvent_apply_eq_zero_of_mem_graph_smul (hr : 0 ≤ r)
    (hs : sphere c r ⊆ A.resolventSet) (hμ : μ ∉ closedBall c r) (hx : (x, μ • x) ∈ A.graph) :
    rieszProjection A.resolvent c r x = 0 := by
  rw [rieszProjection_resolvent_apply_of_mem_graph_smul hr hs
    (fun h ↦ hμ (sphere_subset_closedBall h)) hx,
    circleIntegral_sub_inv_of_notMem_closedBall hr hμ, mul_zero, zero_smul]

/-- **The Riesz projection fixes the generalized eigenvectors inside the circle**: if
`(A - μ)^k x = 0` and `μ` is inside the circle, then `P x = x`. By induction on `k`: the vector
`x - P x` is an eigenvector in the kernel of `P`, which `P` fixes. -/
theorem rieszProjection_resolvent_apply_eq_self_of_mem_genEigenspace (hr : 0 < r)
    (hs : sphere c r ⊆ A.resolventSet) (hμ : μ ∈ ball c r) {k : ℕ}
    (hx : x ∈ A.genEigenspace μ k) : rieszProjection A.resolvent c r x = x := by
  have hP := isIdempotentElem_rieszProjection_resolvent hr hs
  set P := rieszProjection A.resolvent c r
  induction k generalizing x with
  | zero => simp [(Submodule.mem_bot ℂ).mp hx]
  | succ k ih =>
    obtain ⟨y, hxy, hu⟩ := mem_genEigenspace_succ.mp hx
    have hPu : P y - μ • P x = y - μ • x := by
      rw [← _root_.map_smul, ← _root_.map_sub]
      exact ih hu
    have hg : (x - P x, y - P y) ∈ A.graph :=
      A.graph.sub_mem hxy (rieszProjection_resolvent_map_mem_graph hr.le hs hxy)
    have he : y - P y = μ • (x - P x) := by
      rw [smul_sub, sub_eq_sub_iff_sub_eq_sub, hPu]
    rw [he] at hg
    have h1 : P (x - P x) = x - P x :=
      rieszProjection_resolvent_apply_eq_self_of_mem_graph_smul hr.le hs hμ hg
    have h2 : P (x - P x) = 0 := by
      rw [_root_.map_sub, ← mul_apply_eq_comp, hP.eq, sub_self]
    exact (sub_eq_zero.mp (h1.symm.trans h2)).symm

/-- **The Riesz projection kills the generalized eigenvectors outside the circle**: if
`(A - μ)^k x = 0` and `μ` is outside the closed disc, then `P x = 0`. By induction on `k`: the
vector `P x` is an eigenvector in the range of `P`, which `P` kills. -/
theorem rieszProjection_resolvent_apply_eq_zero_of_mem_genEigenspace (hr : 0 < r)
    (hs : sphere c r ⊆ A.resolventSet) (hμ : μ ∉ closedBall c r) {k : ℕ}
    (hx : x ∈ A.genEigenspace μ k) : rieszProjection A.resolvent c r x = 0 := by
  have hP := isIdempotentElem_rieszProjection_resolvent hr hs
  set P := rieszProjection A.resolvent c r
  induction k generalizing x with
  | zero => simp [(Submodule.mem_bot ℂ).mp hx]
  | succ k ih =>
    obtain ⟨y, hxy, hu⟩ := mem_genEigenspace_succ.mp hx
    have hPu : P y = μ • P x := by
      have := ih hu
      rwa [_root_.map_sub, _root_.map_smul, sub_eq_zero] at this
    have hg : (P x, P y) ∈ A.graph := rieszProjection_resolvent_map_mem_graph hr.le hs hxy
    rw [hPu] at hg
    have h1 : P (P x) = 0 :=
      rieszProjection_resolvent_apply_eq_zero_of_mem_graph_smul hr.le hs hμ hg
    rwa [← mul_apply_eq_comp, hP.eq] at h1

/-- The generalized eigenspaces of a point inside the circle are in the range of the Riesz
projection. -/
theorem genEigenspace_le_range_rieszProjection_resolvent (hr : 0 < r)
    (hs : sphere c r ⊆ A.resolventSet) (hμ : μ ∈ ball c r) (k : ℕ) :
    A.genEigenspace μ k ≤ LinearMap.range (rieszProjection A.resolvent c r).toLinearMap :=
  fun x hx ↦ ⟨x, rieszProjection_resolvent_apply_eq_self_of_mem_genEigenspace hr hs hμ hx⟩

/-- **A Riesz projection of finite rank projects onto a generalized eigenspace.** If the circle
`C(c, r)` surrounds no point of the spectrum of `A` other than `c`, and the Riesz projection `P`
has finite rank `k`, then the range of `P` is `ker (A - c)^k`.

The operator `A` maps the range of `P` into itself, so the range is spanned by generalized
eigenvectors of `A` (`le_iSup_genEigenspace_inf`). A generalized eigenvector for a point other
than `c` vanishes: inside the circle that point is in the resolvent set, and outside `P` both
fixes and kills the vector. -/
theorem range_rieszProjection_resolvent_eq_genEigenspace (hr : 0 < r)
    (hiso : closedBall c r \ {c} ⊆ A.resolventSet)
    [FiniteDimensional ℂ (LinearMap.range (rieszProjection A.resolvent c r).toLinearMap)] :
    LinearMap.range (rieszProjection A.resolvent c r).toLinearMap = A.genEigenspace c
      (Module.finrank ℂ (LinearMap.range (rieszProjection A.resolvent c r).toLinearMap)) := by
  have hs : sphere c r ⊆ A.resolventSet := sphere_subset_of_closedBall_sdiff_subset hr hiso
  have hP := isIdempotentElem_rieszProjection_resolvent hr hs
  set P := rieszProjection A.resolvent c r
  have hPV : ∀ v ∈ LinearMap.range P.toLinearMap, P v = v := by
    rintro _ ⟨y, rfl⟩
    exact DFunLike.congr_fun hP.eq y
  have hV : LinearMap.range P.toLinearMap ≤ A.domain := by
    rintro _ ⟨y, rfl⟩
    exact rieszProjection_resolvent_mem_domain hr.le hs y
  have hAV : ∀ ⦃x y⦄, (x, y) ∈ A.graph → x ∈ LinearMap.range P.toLinearMap →
      y ∈ LinearMap.range P.toLinearMap := fun x y hxy hx ↦ by
    have h : (P x, P y) ∈ A.graph := rieszProjection_resolvent_map_mem_graph hr.le hs hxy
    rw [hPV x hx] at h
    exact ⟨y, A.mem_graph_snd_inj h hxy rfl⟩
  refine le_antisymm ((le_iSup_genEigenspace_inf hV hAV).trans (iSup_le fun μ ↦ ?_))
    (genEigenspace_le_range_rieszProjection_resolvent hr hs (mem_ball_self hr) _)
  by_cases hμ : μ = c
  · rw [hμ]
    exact inf_le_left
  · -- no other point has a generalized eigenvector in the range of `P`
    rintro x ⟨hx, hxV⟩
    have hx0 : x = 0 := by
      by_cases hμb : μ ∈ closedBall c r
      · rw [genEigenspace_eq_bot_of_mem_resolventSet (hiso ⟨hμb, hμ⟩)] at hx
        exact (Submodule.mem_bot ℂ).mp hx
      · exact (hPV x hxV).symm.trans
          (rieszProjection_resolvent_apply_eq_zero_of_mem_genEigenspace hr hs hμb hx)
    rw [hx0]
    exact zero_mem _

omit [CompleteSpace E] in
/-- **Isolation of the points of a finite spectral set.** If the spectrum of `A` in the
half-plane `Re z > ω'` is the finite set `Λ`, and the closed discs of radius `r` around the
points of `Λ` lie in the half-plane and are separated, then each of these discs, without its
centre, is in the resolvent set. The hypotheses are three clauses of
`IsComplexLinear.exists_spectral_gap`; the conclusion is the hypothesis of
`range_rieszProjection_resolvent_eq_genEigenspace`. -/
theorem closedBall_sdiff_subset_resolventSet {Λ : Finset ℂ} {ω' : ℝ}
    (hspec : ∀ z : ℂ, ω' < z.re → (z ∈ A.spectrum ↔ z ∈ Λ))
    (hre : ∀ μ ∈ Λ, ω' < μ.re - r) (hdist : ∀ μ ∈ Λ, ∀ ν ∈ Λ, μ ≠ ν → 2 * r < dist μ ν)
    (hμ : μ ∈ Λ) : closedBall μ r \ {μ} ⊆ A.resolventSet := by
  rintro z ⟨hz, hzμ⟩
  by_contra hzρ
  have hzre : ω' < z.re := by
    have h1 : |z.re - μ.re| ≤ r := by
      rw [← Complex.sub_re]
      exact (Complex.abs_re_le_norm (z - μ)).trans (by rwa [← dist_eq_norm])
    have h2 := hre μ hμ
    have h3 := neg_abs_le (z.re - μ.re)
    linarith
  have h1 := hdist z ((hspec z hzre).mp hzρ) μ hμ hzμ
  have h2 : dist z μ ≤ r := hz
  linarith [dist_nonneg.trans h2]

end LinearPMap
