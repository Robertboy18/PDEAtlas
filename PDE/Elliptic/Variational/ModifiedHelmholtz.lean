/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.QuadraticEnergy
public import PDE.Analysis.Variational.LaxMilgram
public import PDE.Elliptic.Variational.PrincipalForms

/-!
# The modified Helmholtz form

The bilinear form

`B(u,v) = ∫_Ω ∇u · ∇v + λ ∫_Ω u v`

is coercive on `H¹₀(Ω)` for every `λ > 0`, without the Poincaré inequality. We combine the shared
`L²` mass and Dirichlet forms, prove coercivity directly from the `H¹` norm decomposition, and apply
Evans's §6.2.1, Theorem 1 (Lax-Milgram Theorem) to the weak problem `-Δu + λu = f`, `u = 0` on `∂Ω`,
in the sense of (9) in §6.1.2. No boundedness assumption on `Ω` and no Poincaré inequality are
needed. The weak solution is also the unique minimizer of the energy
`J_λ(v) = 1/2 B_λ(v,v) - ℓ_f(v)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.1.2, (8)-(9), p. 314; §6.2.1, Theorem 1 (Lax-Milgram
  Theorem) and its proof, pp. 315-317.
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

/-!
## Modified Helmholtz form and coercivity
-/

/-- The continuous bilinear form `B + lam • M` built from two continuous bilinear forms. -/
noncomputable def addScaledFormsOf
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (B M : V →L[ℝ] V →L[ℝ] ℝ) (lam : ℝ) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ
    (fun u v ↦ B u v + lam * M u v)
    (by
      intro u₁ u₂ v
      simp only [map_add, add_apply]
      ring)
    (by
      intro c u v
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring)
    (by
      intro u v₁ v₂
      simp only [map_add]
      ring)
    (by
      intro c u v
      simp only [map_smul, smul_eq_mul]
      ring)).mkContinuous₂ (‖B‖ + |lam| * ‖M‖) <| by
        intro u v
        calc
          ‖B u v + lam * M u v‖ ≤ ‖B u v‖ + ‖lam * M u v‖ :=
            norm_add_le _ _
          _ ≤ ‖B‖ * ‖u‖ * ‖v‖ +
              |lam| * (‖M‖ * ‖u‖ * ‖v‖) := by
            apply add_le_add (B.le_opNorm₂ u v)
            rw [Real.norm_eq_abs, abs_mul]
            gcongr
            exact M.le_opNorm₂ u v
          _ = (‖B‖ + |lam| * ‖M‖) * ‖u‖ * ‖v‖ := by ring

/-- The weak modified Helmholtz form
`B_λ(u,v) = ∫_Ω ∇u · ∇v + λ ∫_Ω u v` on `H¹₀(Ω)`. -/
noncomputable def modifiedHelmholtzForm (lam : ℝ) : H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
  addScaledFormsOf H¹₀(Ω)
    (dirichletForm (n := n) (Ω := Ω))
    (massFormCLM (n := n) (Ω := Ω)) lam

/-- Unfolding the modified Helmholtz form: the Dirichlet form plus `lam` times the `L²` inner
product of the base coordinates, that is `∫_Ω ∇u · ∇v + lam ∫_Ω u v` in weak form. -/
@[simp]
theorem modifiedHelmholtzForm_apply (lam : ℝ) (u v : H¹₀(Ω)) :
    modifiedHelmholtzForm (n := n) (Ω := Ω) lam u v =
      dirichletForm (n := n) (Ω := Ω) u v +
        lam * ⟪baseCoordCLM (n := n) (Ω := Ω) u,
          baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ := by
  rfl

/-- Symmetry of the modified Helmholtz form. -/
theorem modifiedHelmholtzForm_symm (lam : ℝ) (u v : H¹₀(Ω)) :
    modifiedHelmholtzForm (n := n) (Ω := Ω) lam u v =
      modifiedHelmholtzForm (n := n) (Ω := Ω) lam v u := by
  rw [modifiedHelmholtzForm_apply, modifiedHelmholtzForm_apply,
    dirichletForm_symm (n := n) (Ω := Ω) u v]
  congr 1
  exact congrArg (fun z : ℝ ↦ lam * z) (real_inner_comm _ _)

/-- Diagonal expansion of the modified Helmholtz form into derivative and base-coordinate
squares. -/
theorem modifiedHelmholtzForm_self_eq (lam : ℝ) (u : H¹₀(Ω)) :
    modifiedHelmholtzForm (n := n) (Ω := Ω) lam u u =
      (∑ i : Fin n, ‖derivCoordCLM (n := n) (Ω := Ω) i u‖ ^ 2) +
        lam * ‖baseCoordCLM (n := n) (Ω := Ω) u‖ ^ 2 := by
  rw [modifiedHelmholtzForm_apply,
    dirichletForm_self_eq_sum_norm_sq (n := n) (Ω := Ω) u,
    real_inner_self_eq_norm_sq]

/-- Nonnegativity of the modified Helmholtz form on the diagonal when `λ ≥ 0`. -/
theorem modifiedHelmholtzForm_self_nonneg (lam : ℝ) (hlam : 0 ≤ lam) (u : H¹₀(Ω)) :
    0 ≤ modifiedHelmholtzForm (n := n) (Ω := Ω) lam u u := by
  rw [modifiedHelmholtzForm_self_eq (n := n) (Ω := Ω) lam u]
  exact add_nonneg
    (Finset.sum_nonneg fun _i _hi ↦ sq_nonneg _)
    (mul_nonneg hlam (sq_nonneg _))

/-- A signed mass coefficient lowers a given Dirichlet coercivity modulus
by at most its negative part. -/
theorem modifiedHelmholtzForm_coercive_bound_of_dirichlet
    (lam c : ℝ)
    (hdirichlet : ∀ u : H¹₀(Ω),
      c * ‖u‖ * ‖u‖ ≤
        dirichletForm (n := n) (Ω := Ω) u u)
    (u : H¹₀(Ω)) :
    (c - lam⁻) * ‖u‖ * ‖u‖ ≤
      modifiedHelmholtzForm (n := n) (Ω := Ω) lam u u := by
  let P := baseCoordCLM (n := n) (Ω := Ω)
  have hbaseSq :
      ‖P u‖ * ‖P u‖ ≤ ‖u‖ * ‖u‖ :=
    mul_self_le_mul_self (norm_nonneg _)
      (baseCoordCLM_norm_le (n := n) (Ω := Ω) u)
  have hnegCoeff : -lam⁻ ≤ lam := by
    linarith [posPart_nonneg lam, posPart_sub_negPart lam]
  have hmass :
      -lam⁻ * (‖u‖ * ‖u‖) ≤ lam * (‖P u‖ * ‖P u‖) := by
    calc
      -lam⁻ * (‖u‖ * ‖u‖) ≤
          -lam⁻ * (‖P u‖ * ‖P u‖) :=
        mul_le_mul_of_nonpos_left hbaseSq
          (neg_nonpos.mpr (negPart_nonneg lam))
      _ ≤ lam * (‖P u‖ * ‖P u‖) :=
        mul_le_mul_of_nonneg_right hnegCoeff
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [modifiedHelmholtzForm_apply, real_inner_self_eq_norm_sq, pow_two]
  linarith [hdirichlet u]

/-- A signed modified Helmholtz form remains coercive when the negative part
of its mass coefficient is smaller than a Dirichlet coercivity modulus. -/
theorem modifiedHelmholtzForm_isCoercive_of_negPart_lt
    (lam c : ℝ)
    (hdirichlet : ∀ u : H¹₀(Ω),
      c * ‖u‖ * ‖u‖ ≤
        dirichletForm (n := n) (Ω := Ω) u u)
    (hsmall : lam⁻ < c) :
    IsCoercive
      (modifiedHelmholtzForm (n := n) (Ω := Ω) lam) :=
  ⟨c - lam⁻, sub_pos.mpr hsmall,
    modifiedHelmholtzForm_coercive_bound_of_dirichlet
      (n := n) (Ω := Ω) lam c hdirichlet⟩

/-- For `λ > 0`, the modified Helmholtz form is coercive with constant `min 1 λ`.

Unlike the pure Dirichlet form, this proof uses the positive mass term to control the base
coordinate.  Consequently it applies on every measurable domain and in every dimension. -/
theorem modifiedHelmholtzForm_isCoercive (lam : ℝ) (hlam : 0 < lam) :
    IsCoercive
      (modifiedHelmholtzForm (n := n) (Ω := Ω) lam) := by
  classical
  refine ⟨min 1 lam, lt_min zero_lt_one hlam, ?_⟩
  intro u
  let b : ℝ := ‖baseCoordCLM (n := n) (Ω := Ω) u‖ ^ 2
  let d : ℝ :=
    ∑ i : Fin n, ‖derivCoordCLM (n := n) (Ω := Ω) i u‖ ^ 2
  have hb : 0 ≤ b := by simp [b]
  have hd : 0 ≤ d := by
    exact Finset.sum_nonneg fun _i _hi ↦ sq_nonneg _
  have hnorm : ‖u‖ * ‖u‖ = b + d := by
    have hdecomp := norm_sq_eq_base_sq_add_sum_deriv_sq
      (n := n) (Ω := Ω) u
    simpa only [b, d, pow_two] using hdecomp
  have hform :
      modifiedHelmholtzForm (n := n) (Ω := Ω) lam u u = d + lam * b := by
    simpa only [b, d] using
      modifiedHelmholtzForm_self_eq (n := n) (Ω := Ω) lam u
  have hmin_one : min 1 lam ≤ 1 := min_le_left _ _
  have hmin_lam : min 1 lam ≤ lam := min_le_right _ _
  calc
    min 1 lam * ‖u‖ * ‖u‖ = min 1 lam * (b + d) := by rw [← hnorm]; ring
    _
        = min 1 lam * b + min 1 lam * d := by ring
    _ ≤ lam * b + 1 * d := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hmin_lam hb)
        (mul_le_mul_of_nonneg_right hmin_one hd)
    _ = d + lam * b := by ring
    _ = modifiedHelmholtzForm (n := n) (Ω := Ω) lam u u := hform.symm

/-!
## Existence, uniqueness, and energy
-/

/-- The named Lax-Milgram solver for the weak modified Helmholtz problem. -/
noncomputable def modifiedHelmholtzSolve (lam : ℝ) (hlam : 0 < lam) (f : L2) : H¹₀(Ω) :=
  solve
    (V := H¹₀(Ω))
    (modifiedHelmholtzForm (n := n) (Ω := Ω) lam)
    (modifiedHelmholtzForm_isCoercive (n := n) (Ω := Ω) lam hlam)
    (loadFunctional (n := n) (Ω := Ω) f)

/-- The named modified Helmholtz solver satisfies the weak equation. -/
theorem modifiedHelmholtzSolve.isWeakSolution (lam : ℝ) (hlam : 0 < lam) (f : L2) :
    IsWeakSolution
      (modifiedHelmholtzForm (n := n) (Ω := Ω) lam)
      (loadFunctional (n := n) (Ω := Ω) f)
      (modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f) := by
  simpa [modifiedHelmholtzSolve] using
    solve.isWeakSolution
      (V := H¹₀(Ω))
      (modifiedHelmholtzForm (n := n) (Ω := Ω) lam)
      (modifiedHelmholtzForm_isCoercive (n := n) (Ω := Ω) lam hlam)
      (loadFunctional (n := n) (Ω := Ω) f)

/--
Homogeneous modified Helmholtz data give the zero weak solution.

For `λ > 0`, the modified Helmholtz form is coercive without a bounded-domain
Poincaré hypothesis, so uniqueness immediately identifies the zero-load
Lax-Milgram solution with the zero `H¹₀` field.
-/
theorem modifiedHelmholtzSolve_zero (lam : ℝ) (hlam : 0 < lam) :
    modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam (0 : L2) = 0 := by
  unfold modifiedHelmholtzSolve
  rw [loadFunctional_zero]
  apply solve.zero

/--
Any weak modified Helmholtz solution agrees with the named Lax-Milgram solution.

This is the uniqueness form used in later arguments: after checking the weak
identity, no separate appeal to the abstract solver is needed.
-/
theorem modifiedHelmholtzSolve.isWeakSolution_iff_eq
    (lam : ℝ) (hlam : 0 < lam) (f : L2) {u : H¹₀(Ω)} :
    IsWeakSolution
        (modifiedHelmholtzForm (n := n) (Ω := Ω) lam)
        (loadFunctional (n := n) (Ω := Ω) f)
        u ↔
      u = modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f := by
  constructor
  · intro hu
    exact @IsWeakSolution.eq_solve
      H¹₀(Ω)
      inferInstance
      inferInstance
      inferInstance
      (modifiedHelmholtzForm (n := n) (Ω := Ω) lam)
      (modifiedHelmholtzForm_isCoercive (n := n) (Ω := Ω) lam hlam)
      (loadFunctional (n := n) (Ω := Ω) f)
      u
      hu
  · rintro rfl
    exact modifiedHelmholtzSolve.isWeakSolution (n := n) (Ω := Ω) lam hlam f

/--
For positive `λ`, the homogeneous weak modified Helmholtz problem has only the zero
`H¹₀` solution.
-/
theorem modifiedHelmholtzSolve.isWeakSolution_zero_iff
    (lam : ℝ) (hlam : 0 < lam) {u : H¹₀(Ω)} :
    IsWeakSolution
        (modifiedHelmholtzForm (n := n) (Ω := Ω) lam)
        (loadFunctional (n := n) (Ω := Ω) (0 : L2))
        u ↔
      u = 0 := by
  rw [modifiedHelmholtzSolve.isWeakSolution_iff_eq
    (n := n) (Ω := Ω) lam hlam (0 : L2)]
  rw [modifiedHelmholtzSolve_zero (n := n) (Ω := Ω) lam hlam]

/-- Uniform a priori `H¹₀` estimate for the modified Helmholtz weak solution in terms of the
`L²` datum. -/
theorem modifiedHelmholtzSolve_norm_le (lam : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : L2,
      ‖modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f‖ ≤ C * ‖f‖ := by
  rcases solve.norm_le
      (V := H¹₀(Ω))
      (modifiedHelmholtzForm (n := n) (Ω := Ω) lam)
      (modifiedHelmholtzForm_isCoercive (n := n) (Ω := Ω) lam hlam) with
    ⟨C, hC, hsolve⟩
  refine ⟨C, hC, ?_⟩
  intro f
  exact (hsolve (loadFunctional (n := n) (Ω := Ω) f)).trans <|
    mul_le_mul_of_nonneg_left
      (norm_loadFunctional_le (n := n) (Ω := Ω) f) (le_of_lt hC)

/--
Continuous dependence of the modified Helmholtz weak solution on the forcing term.

This is the Lax-Milgram stability estimate for the coercive form
`∫ ∇u·∇v + λuv`, specialized to the concrete `L²` load.
-/
theorem modifiedHelmholtzSolve_sub_modifiedHelmholtzSolve_norm_le
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ f g : L2,
      ‖modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f -
          modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam g‖ ≤
        C * ‖f - g‖ := by
  rcases solve.norm_sub_le
      (V := H¹₀(Ω))
      (modifiedHelmholtzForm (n := n) (Ω := Ω) lam)
      (modifiedHelmholtzForm_isCoercive (n := n) (Ω := Ω) lam hlam) with
    ⟨C, hC, hsolve⟩
  refine ⟨C, hC, ?_⟩
  intro f g
  have hload :
      ‖loadFunctional (n := n) (Ω := Ω) f -
          loadFunctional (n := n) (Ω := Ω) g‖ ≤ ‖f - g‖ := by
    rw [← loadFunctional_sub (n := n) (Ω := Ω) f g]
    exact norm_loadFunctional_le (n := n) (Ω := Ω) (f - g)
  exact
    (hsolve
      (loadFunctional (n := n) (Ω := Ω) f)
      (loadFunctional (n := n) (Ω := Ω) g)).trans
      (mul_le_mul_of_nonneg_left hload (le_of_lt hC))

/-- The modified Helmholtz energy `J_λ(v) = 1/2 B_λ(v,v) - ℓ_f(v)`. -/
noncomputable def modifiedHelmholtzEnergy (lam : ℝ) (f : L2) (v : H¹₀(Ω)) : ℝ :=
  @energy H¹₀(Ω) inferInstance
    inferInstance
    (modifiedHelmholtzForm (n := n) (Ω := Ω) lam)
    (loadFunctional (n := n) (Ω := Ω) f)
    v

/-- Weak modified Helmholtz solutions minimize the modified Helmholtz energy when `λ ≥ 0`. -/
theorem modifiedHelmholtzEnergy_minimal_of_weakSolution
    (lam : ℝ) (hlam : 0 ≤ lam) (f : L2) {u : H¹₀(Ω)}
    (hu : IsWeakSolution
      (modifiedHelmholtzForm (n := n) (Ω := Ω) lam)
      (loadFunctional (n := n) (Ω := Ω) f)
      u) (v : H¹₀(Ω)) :
    modifiedHelmholtzEnergy (n := n) (Ω := Ω) lam f u ≤
      modifiedHelmholtzEnergy (n := n) (Ω := Ω) lam f v := by
  exact @IsWeakSolution.energy_le
    H¹₀(Ω)
    inferInstance
    inferInstance
    (modifiedHelmholtzForm (n := n) (Ω := Ω) lam)
    (loadFunctional (n := n) (Ω := Ω) f)
    u
    (modifiedHelmholtzForm_symm (n := n) (Ω := Ω) lam)
    (modifiedHelmholtzForm_self_nonneg (n := n) (Ω := Ω) lam hlam)
    hu v

/-- The Lax-Milgram modified Helmholtz solution minimizes the modified Helmholtz energy. -/
theorem modifiedHelmholtzSolve.minimizesEnergy
    (lam : ℝ) (hlam : 0 < lam) (f : L2) (v : H¹₀(Ω)) :
    modifiedHelmholtzEnergy (n := n) (Ω := Ω) lam f
        (modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f) ≤
      modifiedHelmholtzEnergy (n := n) (Ω := Ω) lam f v :=
  modifiedHelmholtzEnergy_minimal_of_weakSolution
    (n := n) (Ω := Ω) lam (le_of_lt hlam) f
    (modifiedHelmholtzSolve.isWeakSolution (n := n) (Ω := Ω) lam hlam f) v

/-- Equality in the modified Helmholtz energy principle occurs exactly at the Lax-Milgram
solution. -/
theorem modifiedHelmholtzEnergy.eq_min_iff
    (lam : ℝ) (hlam : 0 < lam) (f : L2) {v : H¹₀(Ω)} :
    modifiedHelmholtzEnergy (n := n) (Ω := Ω) lam f v =
        modifiedHelmholtzEnergy (n := n) (Ω := Ω) lam f
          (modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f) ↔
      v = modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f := by
  simpa [modifiedHelmholtzEnergy] using
    (@IsWeakSolution.energy_eq_iff
      H¹₀(Ω)
      inferInstance
      inferInstance
      (modifiedHelmholtzForm (n := n) (Ω := Ω) lam)
      (modifiedHelmholtzForm_isCoercive (n := n) (Ω := Ω) lam hlam)
      (loadFunctional (n := n) (Ω := Ω) f)
      (modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f)
      v
      (modifiedHelmholtzForm_symm (n := n) (Ω := Ω) lam)
      (modifiedHelmholtzSolve.isWeakSolution (n := n) (Ω := Ω) lam hlam f))

/-- Strict form of the modified Helmholtz variational principle. -/
theorem modifiedHelmholtzSolve.energy_lt_of_ne
    (lam : ℝ) (hlam : 0 < lam) (f : L2) {v : H¹₀(Ω)}
    (hv : v ≠ modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f) :
    modifiedHelmholtzEnergy (n := n) (Ω := Ω) lam f
        (modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f) <
      modifiedHelmholtzEnergy (n := n) (Ω := Ω) lam f v := by
  have hle := modifiedHelmholtzSolve.minimizesEnergy
    (n := n) (Ω := Ω) lam hlam f v
  exact lt_of_le_of_ne hle (by
    intro hEq
    exact hv ((modifiedHelmholtzEnergy.eq_min_iff
      (n := n) (Ω := Ω) lam hlam f).mp hEq.symm))

/-- The variational characterization for the modified Helmholtz problem: global minimizers of
`J_λ` are exactly weak solutions. -/
theorem modifiedHelmholtzEnergy.minimizer_iff_weakSolution
    (lam : ℝ) (hlam : 0 < lam) (f : L2) {u : H¹₀(Ω)} :
    (∀ v : H¹₀(Ω),
      modifiedHelmholtzEnergy (n := n) (Ω := Ω) lam f u ≤
        modifiedHelmholtzEnergy (n := n) (Ω := Ω) lam f v) ↔
      IsWeakSolution
        (modifiedHelmholtzForm (n := n) (Ω := Ω) lam)
        (loadFunctional (n := n) (Ω := Ω) f)
        u := by
  simpa [modifiedHelmholtzEnergy] using
    (@IsWeakSolution.energy_minimizer_iff
      H¹₀(Ω)
      inferInstance
      inferInstance
      inferInstance
      (modifiedHelmholtzForm (n := n) (Ω := Ω) lam)
      (modifiedHelmholtzForm_isCoercive (n := n) (Ω := Ω) lam hlam)
      (loadFunctional (n := n) (Ω := Ω) f)
      u
      (modifiedHelmholtzForm_symm (n := n) (Ω := Ω) lam))

/-- The Lax-Milgram modified Helmholtz solution is the unique global minimizer of the
modified Helmholtz energy. -/
theorem modifiedHelmholtzSolve.unique_energyMinimizer
    (lam : ℝ) (hlam : 0 < lam) (f : L2) {u : H¹₀(Ω)}
    (hu : ∀ v : H¹₀(Ω),
      modifiedHelmholtzEnergy (n := n) (Ω := Ω) lam f u ≤
        modifiedHelmholtzEnergy (n := n) (Ω := Ω) lam f v) :
    u = modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f := by
  have hEq :
      modifiedHelmholtzEnergy (n := n) (Ω := Ω) lam f u =
        modifiedHelmholtzEnergy (n := n) (Ω := Ω) lam f
          (modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f) :=
    le_antisymm
      (hu (modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f))
      (modifiedHelmholtzSolve.minimizesEnergy (n := n) (Ω := Ω) lam hlam f u)
  exact (modifiedHelmholtzEnergy.eq_min_iff
    (n := n) (Ω := Ω) lam hlam f).mp hEq

/-- The weak modified Helmholtz equation in the derivative and base `L²` coordinates. -/
theorem modifiedHelmholtz_weakSolution_equation
    (lam : ℝ) (f : L2) {u : H¹₀(Ω)}
    (hu : IsWeakSolution
      (modifiedHelmholtzForm (n := n) (Ω := Ω) lam)
      (loadFunctional (n := n) (Ω := Ω) f)
      u) (v : H¹₀(Ω)) :
    (∑ i : Fin n,
        ⟪derivCoordCLM (n := n) (Ω := Ω) i u,
          derivCoordCLM (n := n) (Ω := Ω) i v⟫_ℝ) +
        lam * ⟪baseCoordCLM (n := n) (Ω := Ω) u,
          baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ =
      ⟪f, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ := by
  calc
    _ = modifiedHelmholtzForm (n := n) (Ω := Ω) lam u v := by
      rw [modifiedHelmholtzForm_apply,
        dirichletForm_apply (n := n) (Ω := Ω) u v]
    _ = loadFunctional (n := n) (Ω := Ω) f v := hu v
    _ = _ := loadFunctional_apply (n := n) (Ω := Ω) f v

/-- The Lax-Milgram modified Helmholtz solver satisfies the weak equation against every `H¹₀` test
function. -/
theorem modifiedHelmholtzSolve_equation
    (lam : ℝ) (hlam : 0 < lam) (f : L2) (v : H¹₀(Ω)) :
    (∑ i : Fin n,
        ⟪derivCoordCLM (n := n) (Ω := Ω) i
            (modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f),
          derivCoordCLM (n := n) (Ω := Ω) i v⟫_ℝ) +
        lam * ⟪baseCoordCLM (n := n) (Ω := Ω)
            (modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f),
          baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ =
      ⟪f, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ :=
  modifiedHelmholtz_weakSolution_equation
    (n := n) (Ω := Ω) lam f
    (modifiedHelmholtzSolve.isWeakSolution (n := n) (Ω := Ω) lam hlam f) v

/-- The modified Helmholtz weak equation tested against a compactly supported smooth function. -/
theorem modifiedHelmholtzSolve_equation_testFunction
    (lam : ℝ) (hlam : 0 < lam) (f : L2) (φ : TestFunctionOn n Ω) :
    (∑ i : Fin n,
        ⟪derivCoordCLM (n := n) (Ω := Ω) i
            (modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f),
          derivCoordCLM (n := n) (Ω := Ω) i
            (testFunctionToH10 (n := n) (Ω := Ω) φ)⟫_ℝ) +
        lam * ⟪baseCoordCLM (n := n) (Ω := Ω)
            (modifiedHelmholtzSolve (n := n) (Ω := Ω) lam hlam f),
          baseCoordCLM (n := n) (Ω := Ω)
            (testFunctionToH10 (n := n) (Ω := Ω) φ)⟫_ℝ =
      ⟪f, baseCoordCLM (n := n) (Ω := Ω)
        (testFunctionToH10 (n := n) (Ω := Ω) φ)⟫_ℝ :=
  modifiedHelmholtzSolve_equation
    (n := n) (Ω := Ω) lam hlam f
    (testFunctionToH10 (n := n) (Ω := Ω) φ)

end ModifiedHelmholtz

end GraphSpace

end SobolevSpace
