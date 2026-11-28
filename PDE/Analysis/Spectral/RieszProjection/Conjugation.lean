/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Complex.CircleIntegral.Conjugation
public import PDE.Analysis.InnerProductSpace.Complexification.Riesz
public import PDE.Analysis.Evolution.Semigroup.Complex.Generator
public import PDE.Analysis.Spectral.RieszProjection.Unbounded

/-!
# Riesz projections of a real operator under conjugation

An operator `A` on `Complexification H` is real when its graph is invariant under the
conjugation `C`. For a real operator the resolvent set and the spectrum are symmetric about the
real axis, `C (z - A)⁻¹ C = (conj z - A)⁻¹`, and the Riesz projections at conjugate points are
conjugate: `C P_c C = P_{conj c}`. Real solutions built from a pair of conjugate eigenvalues use
this relation between the two projections. The generator of a semigroup that commutes with `C`
is real. Conjugations of a complex Banach space that is not given as a complexification are not
treated.

## Main results

* `map_dunfordIntegral_conj`, `map_rieszProjection_conj`: a conjugate-linear continuous
  equivalence `L` of a complex normed algebra with `L (R z) = R' (conj z)` on the circle
  `C(c, r)` carries the Dunford integrals and the Riesz projection of `R` on `C(c, r)` to those of
  `R'` on `C(conj c, r)`.
* `isResolventAt_conj`, `conj_mem_resolventSet_iff`, `conj_mem_spectrum_iff`,
  `conjOp_resolvent_of_real`: the resolvent of a real operator on a complexified Hilbert space.
* `conjOp_rieszProjection_resolvent`: `C P_c C = P_{conj c}` for a real operator.
* `conj_mem_graph_generator`: the generator of a complex-linear semigroup that commutes with `C`
  is real.

## How it works

Conjugation turns the circle `C(c, r)` into `C(conj c, r)` with the opposite orientation
(`map_circleIntegral_conj_center`), and it changes the sign of `(2πi)⁻¹`. The two signs cancel,
so `L` carries the Dunford integral of `R` on `C(c, r)` to the Dunford integral of `R'` on
`C(conj c, r)`. For a real operator, `C R C` is the resolvent at `conj z` whenever `R` is the
resolvent at `z`, which is the hypothesis with `L = conjOpCLE`. For a bounded operator and the
centre `0` this is `conjOp_rieszInner`. `conjRCLM` is the conjugation as a real-linear bounded
map, so that `HasGeneratorAt.map_of_commute` applies to it.
-/

@[expose] public noncomputable section

open Real MeasureTheory Metric PDE.Analysis.Spectral
open scoped ComplexConjugate

namespace PDE.Analysis

namespace Spectral

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] {R R' : ℂ → 𝔸} {g g' : ℂ → ℂ}
  {c : ℂ} {r : ℝ}

/-- **Dunford integrals under conjugation.** A conjugate-linear continuous equivalence `L` of the
algebra with `L (R z) = R' (conj z)` on the circle `C(c, r)` carries the Dunford integral of `R`
on `C(c, r)` with weight `g` to the Dunford integral of `R'` on `C(conj c, r)` with the weight
`g' (conj z) = conj (g z)`. -/
theorem map_dunfordIntegral_conj {L : 𝔸 ≃L[ℝ] 𝔸}
    (hL : ∀ (a : ℂ) (x : 𝔸), L (a • x) = conj a • L x)
    (hR : ∀ z ∈ sphere c |r|, L (R z) = R' (conj z))
    (hg : ∀ z ∈ sphere c |r|, g' (conj z) = conj (g z)) :
    L (dunfordIntegral R c r g) = dunfordIntegral R' (conj c) r g' := by
  have h := map_circleIntegral_conj_center (f := fun z ↦ g z • R z)
    (g := fun z ↦ g' z • R' z) hL fun z hz ↦ by rw [hL, hR z hz, hg z hz]
  rw [dunfordIntegral, dunfordIntegral, hL, h, smul_neg, ← neg_smul]
  congr 1
  simp [Complex.conj_ofReal, map_ofNat]

/-- **Riesz projections under conjugation**: `L (P_c) = P'_{conj c}` when `L (R z) = R' (conj z)`
on the circle. -/
theorem map_rieszProjection_conj {L : 𝔸 ≃L[ℝ] 𝔸}
    (hL : ∀ (a : ℂ) (x : 𝔸), L (a • x) = conj a • L x)
    (hR : ∀ z ∈ sphere c |r|, L (R z) = R' (conj z)) :
    L (rieszProjection R c r) = rieszProjection R' (conj c) r :=
  map_dunfordIntegral_conj hL hR fun _ _ ↦ (map_one (starRingEnd ℂ)).symm

end Spectral

namespace Complexification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {A : Complexification H →ₗ.[ℂ] Complexification H} {z : ℂ}
  {R : Complexification H →L[ℂ] Complexification H}

/-- **The resolvent of a real operator.** If the graph of `A` is invariant under conjugation
and `R` is the resolvent of `A` at `z`, then `C R C` is the resolvent at `conj z`. -/
theorem isResolventAt_conj
    (hA : ∀ ⦃x y⦄, (x, y) ∈ A.graph → (conjLIE x, conjLIE y) ∈ A.graph)
    (h : A.IsResolventAt z R) : A.IsResolventAt (conj z) (conjOp R) := by
  refine ⟨fun y ↦ ?_, fun x y hxy ↦ ?_⟩
  · have h1 := hA (h.mem_graph (conjLIE y))
    rwa [map_sub, map_smulₛₗ, conjLIE_conjLIE] at h1
  · have h1 := h.apply_eq (hA hxy)
    rw [conjOp_apply, map_sub, map_smulₛₗ, Complex.conj_conj, h1, conjLIE_conjLIE]

/-- The resolvent set of a real operator is symmetric about the real axis. -/
theorem conj_mem_resolventSet_iff
    (hA : ∀ ⦃x y⦄, (x, y) ∈ A.graph → (conjLIE x, conjLIE y) ∈ A.graph) :
    conj z ∈ A.resolventSet ↔ z ∈ A.resolventSet := by
  constructor
  · rintro ⟨R, hR⟩
    have h := isResolventAt_conj hA hR
    rw [Complex.conj_conj] at h
    exact h.mem_resolventSet
  · rintro ⟨R, hR⟩
    exact (isResolventAt_conj hA hR).mem_resolventSet

/-- The spectrum of a real operator is symmetric about the real axis. -/
theorem conj_mem_spectrum_iff
    (hA : ∀ ⦃x y⦄, (x, y) ∈ A.graph → (conjLIE x, conjLIE y) ∈ A.graph) :
    conj z ∈ A.spectrum ↔ z ∈ A.spectrum :=
  not_congr (conj_mem_resolventSet_iff hA)

/-- **Conjugation of the resolvent of a real operator**: `C (z - A)⁻¹ C = (conj z - A)⁻¹`. -/
theorem conjOp_resolvent_of_real
    (hA : ∀ ⦃x y⦄, (x, y) ∈ A.graph → (conjLIE x, conjLIE y) ∈ A.graph) (z : ℂ) :
    conjOp (A.resolvent z) = A.resolvent (conj z) := by
  by_cases hz : z ∈ A.resolventSet
  · exact (isResolventAt_conj hA (LinearPMap.isResolventAt_resolvent hz)).resolvent_eq.symm
  · rw [LinearPMap.resolvent_of_notMem hz,
      LinearPMap.resolvent_of_notMem fun h ↦ hz ((conj_mem_resolventSet_iff hA).mp h), map_zero]

/-- **The Riesz projection at the conjugate point.** For a real operator `A`,
`C P_c C = P_{conj c}`: conjugation carries the Riesz projection of `A` on the circle `C(c, r)`
to the Riesz projection on the circle `C(conj c, r)`. Real solutions built from a pair of
conjugate eigenvalues use this relation between their two projections. Conjugation maps the
resolvent at `z` to the resolvent at `conj z` (`conjOp_resolvent_of_real`), reverses the
orientation of the circle and changes the sign of `(2πi)⁻¹` (`map_rieszProjection_conj`). -/
theorem conjOp_rieszProjection_resolvent
    (hA : ∀ ⦃x y⦄, (x, y) ∈ A.graph → (conjLIE x, conjLIE y) ∈ A.graph) (c : ℂ) (r : ℝ) :
    conjOp (rieszProjection A.resolvent c r) = rieszProjection A.resolvent (conj c) r :=
  map_rieszProjection_conj (L := conjOpCLE) (fun a x ↦ conjOp_smul a x)
    fun z _ ↦ conjOp_resolvent_of_real hA z

/-- The conjugation of the complexification as a real-linear bounded operator. -/
def conjRCLM : Complexification H →L[ℝ] Complexification H where
  toFun := conjLIE
  map_add' := map_add conjLIE
  map_smul' r z := by ext <;> simp
  cont := conjLIE.continuous

/-- `conjRCLM` acts as the conjugation. -/
@[simp]
theorem conjRCLM_apply (x : Complexification H) : conjRCLM x = conjLIE x :=
  rfl

open PDE.Analysis.Evolution in
/-- **The generator of a real semigroup is real.** If a complex-linear semigroup on a
complexified space commutes with the conjugation, the graph of its generator is invariant under
conjugation. -/
theorem conj_mem_graph_generator {T : StronglyContinuousSemigroup (Complexification H)}
    (hT : T.IsComplexLinear) (hC : ∀ t x, conjLIE (T t x) = T t (conjLIE x))
    {x y : Complexification H} (h : (x, y) ∈ hT.generator.graph) :
    (conjLIE x, conjLIE y) ∈ hT.generator.graph :=
  hT.mem_graph_generator_iff.mpr
    ((hT.mem_graph_generator_iff.mp h).map_of_commute (C := conjRCLM) hC)

end Complexification

end PDE.Analysis
