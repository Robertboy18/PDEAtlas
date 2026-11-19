/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.ModifiedHelmholtz

/-!
# Distributional modified Helmholtz equation

The Lax-Milgram construction in `PDE.Elliptic.Variational.ModifiedHelmholtz` is phrased on the
Hilbert space `H¹₀(Ω)`. Tested against compactly supported smooth functions, as in Evans's (7) of
§6.1.2, the equation `-Δu + λu = f` becomes the identity

`∑ᵢ ∫_Ω Dᵢu Dᵢφ + λ ∫_Ω u φ = ∫_Ω f φ`.

`isWeakSolution_iff_isWeakModifiedHelmholtzSolution` proves that the two notions agree. The reverse
implication is not a formal weakening: smooth compactly supported functions are dense in `H¹₀(Ω)`,
and continuity extends the identity to every `H¹₀` test, as in Evans's passage from (7) to the weak
formulation (9). This lets later regularity and spectral arguments state their hypotheses as an
ordinary weak PDE and still use the functional-analytic solver.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.1.2, (7)-(9), p. 314.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Sobolev

@[expose] public section

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open PDE.Analysis.Variational
open scoped Topology NNReal InnerProductSpace

namespace GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

section ModifiedHelmholtz

local notation "L2" => DerivLp n 2 Ω


/-- The tested modified Helmholtz identity on a set.

This relation is used in `isWeakSolution_iff_modifiedHelmholtzTestIdentity`. On a
non-open set the available compactly supported smooth tests can be too small
for it to express an open-domain distributional PDE. The PDE predicate
`IsWeakModifiedHelmholtzSolution` therefore records openness separately.
All products are integrable because the solution coordinates, forcing, test,
and first test derivatives lie in `L²`; hence this relation does not exploit
the fallback value of Mathlib's totalized integral. -/
def ModifiedHelmholtzTestIdentity
    (lam : ℝ) (f : L2) (u : H¹₀(Ω)) : Prop :=
  ∀ φ : TestFunctionOn n Ω,
    (∑ i : Fin n,
      ∫ x, (derivCoordCLM (n := n) (Ω := Ω) i u :
          ℝ^n → ℝ) x * (∂[i] φ.1.toFun) x
        ∂domainMeasure n Ω) +
        lam * ∫ x, (baseCoordCLM (n := n) (Ω := Ω) u :
          ℝ^n → ℝ) x * φ.1.toFun x
          ∂domainMeasure n Ω =
      ∫ x, (f : ℝ^n → ℝ) x * φ.1.toFun x
        ∂domainMeasure n Ω

/-- The distributional weak formulation of the homogeneous-Dirichlet modified
Helmholtz problem `-Δu + λu = f` on an open domain, tested against compactly
supported smooth functions as in Evans's (7) of §6.1.2. -/
structure IsWeakModifiedHelmholtzSolution
    (lam : ℝ) (f : L2) (u : H¹₀(Ω)) : Prop where
  /-- The PDE domain is open. -/
  isOpen : IsOpen Ω
  /-- The modified Helmholtz identity against every compactly supported smooth test. -/
  equation : ModifiedHelmholtzTestIdentity
    (n := n) (Ω := Ω) lam f u

/-- A weak modified Helmholtz solution can be applied directly to a test function. -/
instance {lam : ℝ} {f : L2} {u : H¹₀(Ω)} :
    CoeFun (IsWeakModifiedHelmholtzSolution
      (n := n) (Ω := Ω) lam f u)
      (fun _ ↦ ∀ φ : TestFunctionOn n Ω,
        (∑ i : Fin n,
          ∫ x, (derivCoordCLM (n := n) (Ω := Ω) i u :
              ℝ^n → ℝ) x * (∂[i] φ.1.toFun) x
            ∂domainMeasure n Ω) +
            lam * ∫ x, (baseCoordCLM (n := n) (Ω := Ω) u :
              ℝ^n → ℝ) x * φ.1.toFun x
              ∂domainMeasure n Ω =
          ∫ x, (f : ℝ^n → ℝ) x * φ.1.toFun x
            ∂domainMeasure n Ω) where
  coe h := h.equation

/--
The Hilbert-space weak equation is equivalent to the distributional
modified Helmholtz test identity.

For the nontrivial reverse direction, equality on canonical smooth tests is
promoted to equality on all of `H¹₀(Ω)` by
`denseRange_testFunctionToH10Linear`.
-/
theorem isWeakSolution_iff_modifiedHelmholtzTestIdentity
    (lam : ℝ) (f : L2) (u : H¹₀(Ω)) :
    IsWeakSolution
      (modifiedHelmholtzForm (n := n) (Ω := Ω) lam)
      (loadFunctional (n := n) (Ω := Ω) f) u ↔
      ModifiedHelmholtzTestIdentity (n := n) (Ω := Ω) lam f u := by
  constructor
  · intro hu φ
    have heq := modifiedHelmholtz_weakSolution_equation
      (n := n) (Ω := Ω) lam f hu
      (testFunctionToH10 (n := n) (Ω := Ω) φ)
    simpa only [inner_deriv_testFunction_eq_integral,
      inner_base_testFunction_eq_integral] using heq
  · intro hu
    have htest :
        (modifiedHelmholtzForm (n := n) (Ω := Ω) lam u :
            H¹₀(Ω) → ℝ) ∘
            testFunctionToH10Linear (n := n) (Ω := Ω) =
          (loadFunctional (n := n) (Ω := Ω) f :
            H¹₀(Ω) → ℝ) ∘
            testFunctionToH10Linear (n := n) (Ω := Ω) := by
      funext φ
      have hφ := hu φ
      change modifiedHelmholtzForm (n := n) (Ω := Ω) lam u
          (testFunctionToH10 (n := n) (Ω := Ω) φ) =
        loadFunctional (n := n) (Ω := Ω) f
          (testFunctionToH10 (n := n) (Ω := Ω) φ)
      rw [modifiedHelmholtzForm_apply, dirichletForm_apply, loadFunctional_apply]
      simpa only [inner_deriv_testFunction_eq_integral,
        inner_base_testFunction_eq_integral] using hφ
    have hall :=
      (denseRange_testFunctionToH10Linear
        (n := n) (Ω := Ω)).equalizer
        (modifiedHelmholtzForm (n := n) (Ω := Ω) lam u).continuous
        (loadFunctional (n := n) (Ω := Ω) f).continuous htest
    intro v
    exact congrFun hall v

/-- On an open domain, the Hilbert-space weak equation is
equivalent to the distributional modified Helmholtz predicate. -/
theorem isWeakSolution_iff_isWeakModifiedHelmholtzSolution
    (hΩopen : IsOpen Ω) (lam : ℝ) (f : L2) (u : H¹₀(Ω)) :
    IsWeakSolution
      (modifiedHelmholtzForm (n := n) (Ω := Ω) lam)
      (loadFunctional (n := n) (Ω := Ω) f) u ↔
      IsWeakModifiedHelmholtzSolution (n := n) (Ω := Ω) lam f u := by
  rw [isWeakSolution_iff_modifiedHelmholtzTestIdentity
    (n := n) (Ω := Ω) lam f u]
  exact ⟨fun h ↦ ⟨hΩopen, h⟩, fun h ↦ h.equation⟩

/--
Weak existence and uniqueness for `-Δu + λu = f` on every open
domain when `λ > 0`.

Unlike the unshifted Dirichlet problem, no boundedness or Poincaré hypothesis
is needed: the positive mass term controls the base `L²` coordinate.
-/
theorem IsWeakModifiedHelmholtzSolution.existsUnique
    (hΩopen : IsOpen Ω) (lam : ℝ) (hlam : 0 < lam) (f : L2) :
    ∃! u : H¹₀(Ω),
      IsWeakModifiedHelmholtzSolution (n := n) (Ω := Ω) lam f u := by
  refine ⟨modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f, ?_, ?_⟩
  · exact (isWeakSolution_iff_isWeakModifiedHelmholtzSolution
      (n := n) (Ω := Ω) hΩopen lam f
      (modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f)).1
        (modifiedHelmholtzSolve.isWeakSolution
          (n := n) (Ω := Ω) lam hlam f)
  · intro v hv
    apply (modifiedHelmholtzSolve.isWeakSolution_iff_eq
      (n := n) (Ω := Ω) lam hlam f).mp
    exact (isWeakSolution_iff_isWeakModifiedHelmholtzSolution
      (n := n) (Ω := Ω) hΩopen lam f v).2 hv

/-- The named Lax-Milgram solution satisfies the distributional modified Helmholtz equation. -/
theorem modifiedHelmholtzSolve.isWeakModifiedHelmholtzSolution
    (hΩopen : IsOpen Ω) (lam : ℝ) (hlam : 0 < lam) (f : L2) :
    IsWeakModifiedHelmholtzSolution (n := n) (Ω := Ω) lam f
      (modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f) :=
  (isWeakSolution_iff_isWeakModifiedHelmholtzSolution
    (n := n) (Ω := Ω) hΩopen lam f
    (modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f)).1
      (modifiedHelmholtzSolve.isWeakSolution
        (n := n) (Ω := Ω) lam hlam f)

/-- The zero field solves the zero-forcing distributional modified Helmholtz equation. -/
theorem IsWeakModifiedHelmholtzSolution.zero (hΩopen : IsOpen Ω) (lam : ℝ) :
    IsWeakModifiedHelmholtzSolution (n := n) (Ω := Ω) lam
      (0 : L2) (0 : H¹₀(Ω)) := by
  let B : H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
    modifiedHelmholtzForm (n := n) (Ω := Ω) lam
  rw [← isWeakSolution_iff_isWeakModifiedHelmholtzSolution
    (n := n) (Ω := Ω) hΩopen lam (0 : L2) (0 : H¹₀(Ω))]
  change IsWeakSolution B
    (loadFunctional (n := n) (Ω := Ω) (0 : L2)) (0 : H¹₀(Ω))
  have h := @IsWeakSolution.zero H¹₀(Ω) inferInstance
    inferInstance B
  intro w
  calc
    B 0 w = (0 : StrongDual ℝ H¹₀(Ω)) w := h w
    _ = 0 := rfl
    _ = loadFunctional (n := n) (Ω := Ω) (0 : L2) w := by
      simp only [loadFunctional_apply, inner_zero_left]

/-- Superposition for distributional modified Helmholtz solutions with the same shift `λ`. -/
theorem IsWeakModifiedHelmholtzSolution.add
    (lam : ℝ) {f g : L2} {u v : H¹₀(Ω)}
    (hu : IsWeakModifiedHelmholtzSolution (n := n) (Ω := Ω) lam f u)
    (hv : IsWeakModifiedHelmholtzSolution (n := n) (Ω := Ω) lam g v) :
    IsWeakModifiedHelmholtzSolution (n := n) (Ω := Ω) lam
      (f + g) (u + v) := by
  let B : H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
    modifiedHelmholtzForm (n := n) (Ω := Ω) lam
  rw [← isWeakSolution_iff_isWeakModifiedHelmholtzSolution
    (n := n) (Ω := Ω) hu.isOpen lam (f + g) (u + v)]
  change IsWeakSolution B
    (loadFunctional (n := n) (Ω := Ω) (f + g)) (u + v)
  have hu' : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) f) u := by
    simpa only [B] using
      (isWeakSolution_iff_isWeakModifiedHelmholtzSolution
        (n := n) (Ω := Ω) hu.isOpen lam f u).2 hu
  have hv' : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) g) v := by
    simpa only [B] using
      (isWeakSolution_iff_isWeakModifiedHelmholtzSolution
        (n := n) (Ω := Ω) hv.isOpen lam g v).2 hv
  have h := hu'.add hv'
  intro w
  calc
    B (u + v) w =
        (loadFunctional (n := n) (Ω := Ω) f +
          loadFunctional (n := n) (Ω := Ω) g) w := h w
    _ = loadFunctional (n := n) (Ω := Ω) f w +
          loadFunctional (n := n) (Ω := Ω) g w := rfl
    _ = loadFunctional (n := n) (Ω := Ω) (f + g) w := by
      simp only [loadFunctional_apply, inner_add_left]

/-- Negating a weak modified Helmholtz solution negates its forcing datum. -/
theorem IsWeakModifiedHelmholtzSolution.neg
    (lam : ℝ) {f : L2} {u : H¹₀(Ω)}
    (hu : IsWeakModifiedHelmholtzSolution (n := n) (Ω := Ω) lam f u) :
    IsWeakModifiedHelmholtzSolution (n := n) (Ω := Ω) lam (-f) (-u) := by
  let B : H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
    modifiedHelmholtzForm (n := n) (Ω := Ω) lam
  rw [← isWeakSolution_iff_isWeakModifiedHelmholtzSolution
    (n := n) (Ω := Ω) hu.isOpen lam (-f) (-u)]
  change IsWeakSolution B
    (loadFunctional (n := n) (Ω := Ω) (-f)) (-u)
  have hu' : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) f) u := by
    simpa only [B] using
      (isWeakSolution_iff_isWeakModifiedHelmholtzSolution
        (n := n) (Ω := Ω) hu.isOpen lam f u).2 hu
  have h := hu'.neg
  intro w
  calc
    B (-u) w =
        (-loadFunctional (n := n) (Ω := Ω) f) w := h w
    _ = -loadFunctional (n := n) (Ω := Ω) f w := rfl
    _ = loadFunctional (n := n) (Ω := Ω) (-f) w := by
      simp only [loadFunctional_apply, inner_neg_left]

/-- Difference of weak modified Helmholtz solutions solves the equation with difference forcing. -/
theorem IsWeakModifiedHelmholtzSolution.sub
    (lam : ℝ) {f g : L2} {u v : H¹₀(Ω)}
    (hu : IsWeakModifiedHelmholtzSolution (n := n) (Ω := Ω) lam f u)
    (hv : IsWeakModifiedHelmholtzSolution (n := n) (Ω := Ω) lam g v) :
    IsWeakModifiedHelmholtzSolution (n := n) (Ω := Ω) lam
      (f - g) (u - v) := by
  simpa only [sub_eq_add_neg] using hu.add lam (hv.neg lam)

/-- Real scalar multiplication preserves the weak modified Helmholtz equation. -/
theorem IsWeakModifiedHelmholtzSolution.smul
    (lam : ℝ) {f : L2} {u : H¹₀(Ω)} (c : ℝ)
    (hu : IsWeakModifiedHelmholtzSolution (n := n) (Ω := Ω) lam f u) :
    IsWeakModifiedHelmholtzSolution (n := n) (Ω := Ω) lam
      (c • f) (c • u) := by
  let B : H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
    modifiedHelmholtzForm (n := n) (Ω := Ω) lam
  rw [← isWeakSolution_iff_isWeakModifiedHelmholtzSolution
    (n := n) (Ω := Ω) hu.isOpen lam (c • f) (c • u)]
  change IsWeakSolution B
    (loadFunctional (n := n) (Ω := Ω) (c • f)) (c • u)
  have hu' : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) f) u := by
    simpa only [B] using
      (isWeakSolution_iff_isWeakModifiedHelmholtzSolution
        (n := n) (Ω := Ω) hu.isOpen lam f u).2 hu
  have h := hu'.smul c
  intro w
  calc
    B (c • u) w =
        (c • loadFunctional (n := n) (Ω := Ω) f) w := h w
    _ = c * loadFunctional (n := n) (Ω := Ω) f w := rfl
    _ = loadFunctional (n := n) (Ω := Ω) (c • f) w := by
      simp only [loadFunctional_apply, real_inner_smul_left]

/--
For `λ > 0`, a distributional modified Helmholtz solution is exactly the named
Lax-Milgram solution.  This uniqueness statement lets
regularity arguments replace an arbitrary weak solution by the bounded
solution operator.
-/
theorem IsWeakModifiedHelmholtzSolution.iff_eq_modifiedHelmholtzSolve
    (hΩopen : IsOpen Ω) (lam : ℝ) (hlam : 0 < lam) (f : L2) {u : H¹₀(Ω)} :
    IsWeakModifiedHelmholtzSolution (n := n) (Ω := Ω) lam f u ↔
      u = modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f := by
  exact
    (isWeakSolution_iff_isWeakModifiedHelmholtzSolution
      (n := n) (Ω := Ω) hΩopen lam f u).symm.trans
      (modifiedHelmholtzSolve.isWeakSolution_iff_eq
        (n := n) (Ω := Ω) lam hlam f)

/-- The positive-shift homogeneous weak modified Helmholtz problem has only the zero solution. -/
theorem IsWeakModifiedHelmholtzSolution.zero_iff
    (hΩopen : IsOpen Ω) (lam : ℝ) (hlam : 0 < lam) {u : H¹₀(Ω)} :
    IsWeakModifiedHelmholtzSolution (n := n) (Ω := Ω) lam (0 : L2) u ↔
      u = 0 := by
  rw [IsWeakModifiedHelmholtzSolution.iff_eq_modifiedHelmholtzSolve
    (n := n) (Ω := Ω) hΩopen lam hlam (0 : L2)]
  rw [modifiedHelmholtzSolve_zero (n := n) (Ω := Ω) lam hlam]

/-- The named positive-shift modified Helmholtz solver is additive in the forcing datum. -/
theorem modifiedHelmholtzSolve_add
    (lam : ℝ) (hlam : 0 < lam) (f g : L2) :
    modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam (f + g) =
      modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f +
        modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam g := by
  let B : H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
    modifiedHelmholtzForm (n := n) (Ω := Ω) lam
  have hf : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) f)
      (modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f) := by
    simpa only [B] using
      (modifiedHelmholtzSolve.isWeakSolution
        (n := n) (Ω := Ω) lam hlam f)
  have hg : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) g)
      (modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam g) := by
    simpa only [B] using
      (modifiedHelmholtzSolve.isWeakSolution
        (n := n) (Ω := Ω) lam hlam g)
  have hadd := hf.add hg
  have hweak : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) (f + g))
      (modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f +
        modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam g) := by
    intro w
    calc
      B (modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f +
          modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam g) w =
          (loadFunctional (n := n) (Ω := Ω) f +
            loadFunctional (n := n) (Ω := Ω) g) w := hadd w
      _ = loadFunctional (n := n) (Ω := Ω) f w +
          loadFunctional (n := n) (Ω := Ω) g w := rfl
      _ = loadFunctional (n := n) (Ω := Ω) (f + g) w := by
        simp only [loadFunctional_apply, inner_add_left]
  exact ((modifiedHelmholtzSolve.isWeakSolution_iff_eq
    (n := n) (Ω := Ω) lam hlam (f + g)).1 hweak).symm

/-- The named positive-shift modified Helmholtz solver commutes with real scalar multiplication. -/
theorem modifiedHelmholtzSolve_smul
    (lam : ℝ) (hlam : 0 < lam) (c : ℝ) (f : L2) :
    modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam (c • f) =
      c • modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f := by
  let B : H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
    modifiedHelmholtzForm (n := n) (Ω := Ω) lam
  have hf : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) f)
      (modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f) := by
    simpa only [B] using
      (modifiedHelmholtzSolve.isWeakSolution
        (n := n) (Ω := Ω) lam hlam f)
  have hsmul := hf.smul c
  have hweak : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) (c • f))
      (c • modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f) := by
    intro w
    calc
      B (c • modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f) w =
          (c • loadFunctional (n := n) (Ω := Ω) f) w := hsmul w
      _ = c * loadFunctional (n := n) (Ω := Ω) f w := rfl
      _ = loadFunctional (n := n) (Ω := Ω) (c • f) w := by
        simp only [loadFunctional_apply, real_inner_smul_left]
  exact ((modifiedHelmholtzSolve.isWeakSolution_iff_eq
    (n := n) (Ω := Ω) lam hlam (c • f)).1 hweak).symm

end ModifiedHelmholtz

end GraphSpace

end SobolevSpace
