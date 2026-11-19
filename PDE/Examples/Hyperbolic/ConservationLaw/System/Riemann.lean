/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jacobian.Basic
public import PDE.Hyperbolic.ConservationLaw.System.Riemann.InitialValue
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import PDE.Symbolic.PDEDerivatives

/-!
# A coupled polynomial system and the local Riemann theorem

The polynomial flux `(a²/2, (a+1)b)` has two increasing speeds `a` and `a+1`.
The first family is genuinely nonlinear and the second is linearly degenerate.
Its Jacobian depends on both components, and the first wave changes the second
component even when the prescribed jump changes only the first.

The local Riemann theorem `exists_local_riemann_initialValue_solution` gives, for small
jumps from `(0, 1)` to `(h, 1)`, a bounded self-similar weak solution with strong
initial trace (`exists_coupled_riemann_solution`), for jumps of both signs. The first
shock and the contact wave satisfy explicit Rankine–Hugoniot conditions. The curve
`(s, exp(-s))` has tangent `(1, -exp(-s))` (`hasDerivAt_coupled_rarefaction`); it is a
first-family rarefaction curve by `isIntegralCurve_coupledCurve` in
`PDE.Examples.Hyperbolic.ConservationLaw.System.Rarefaction.Segment`.
-/

@[expose] public section

noncomputable section

namespace PDE.Examples.Hyperbolic.ConservationLaw.System.Riemann

open PDE.Common PDE.Hyperbolic.ConservationLaw PDE.Hyperbolic.ConservationLaw.System
open MeasureTheory
open scoped ContDiff ENNReal Distributions InnerProductSpace

/-- A coupled polynomial system with one nonlinear and one degenerate family. -/
def coupledFlux (q : ℝ^2) : ℝ^2 := !₂[q 0 ^ 2 / 2, (q 0 + 1) * q 1]

/-- The coupled flux is smooth on the whole state space. -/
theorem contDiff_coupledFlux : ContDiff ℝ ∞ coupledFlux := by
  rw [contDiff_piLp]
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun q : ℝ^2 ↦ q 0 ^ 2 / 2)
    cas
  · change ContDiff ℝ ∞ (fun q : ℝ^2 ↦ (q 0 + 1) * q 1)
    cas

/-- The Jacobian matrix of the flux is `!![q₀, 0; q₁, q₀ + 1]`. -/
theorem jacobianMatrix_coupledFlux (q : ℝ^2) :
    PDE.Analysis.jacobianMatrix coupledFlux q =
      !![q 0, 0; q 1, q 0 + 1] := by
  ext i j
  fin_cases i <;> fin_cases j
  · change (∂[0] ((fun y : ℝ^2 ↦ y 0 ^ 2 / 2) : ℝ^2 → ℝ)) q = q 0
    cas
  · change (∂[1] ((fun y : ℝ^2 ↦ y 0 ^ 2 / 2) : ℝ^2 → ℝ)) q = 0
    cas
  · change (∂[0] (fun y : ℝ^2 ↦ (y 0 + 1) * y 1)) q = q 1
    cas
  · change (∂[1] (fun y : ℝ^2 ↦ (y 0 + 1) * y 1)) q = q 0 + 1
    cas

/-- The Jacobian applied to `v` is `(q₀ v₀, q₁ v₀ + (q₀ + 1) v₁)`. -/
theorem fderiv_coupledFlux (q v : ℝ^2) :
    fderiv ℝ coupledFlux q v =
      !₂[q 0 * v 0, q 1 * v 0 + (q 0 + 1) * v 1] := by
  rw [fderiv_apply_eq_sum_smul_partialDeriv]
  ext i
  simp only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hj (j : Fin 2) :
      (∂[j] coupledFlux) q i =
        (!![q 0, 0; q 1, q 0 + 1] : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    rw [← jacobianMatrix_coupledFlux q]
    exact (PDE.Analysis.jacobianMatrix_apply_eq_fderiv
      (contDiff_coupledFlux.differentiable (by simp) q) i j).symm
  rw [hj 0, hj 1]
  fin_cases i
  · change v 0 * q 0 + v 1 * 0 = q 0 * v 0
    cas
  · change v 0 * q 1 + v 1 * (q 0 + 1) = q 1 * v 0 + (q 0 + 1) * v 1
    cas

private def eigenvector (q : ℝ^2) (k : Fin 2) : ℝ^2 :=
  if k = 0 then !₂[1, -q 1] else !₂[0, 1]

private def speed (q : ℝ^2) (k : Fin 2) : ℝ := q 0 + (k.val : ℝ)

private theorem independent_eigenvectors (q : ℝ^2) :
    LinearIndependent ℝ (eigenvector q) := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have hc := congrArg (fun v : ℝ^2 ↦ v 1) h
    norm_num [eigenvector] at hc
  · intro a h
    have hc := congrArg (fun v : ℝ^2 ↦ v 0) h
    norm_num [eigenvector] at hc

private def eigenbasis (q : ℝ^2) : Module.Basis (Fin 2) ℝ (ℝ^2) :=
  basisOfLinearIndependentOfCardEqFinrank (independent_eigenvectors q) (by simp)

private theorem eigenbasis_apply (q : ℝ^2) (k : Fin 2) :
    eigenbasis q k = eigenvector q k :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) k

private theorem eigenvector_equation (q : ℝ^2) (k : Fin 2) :
    fderiv ℝ coupledFlux q (eigenbasis q k) = speed q k • eigenbasis q k := by
  rw [eigenbasis_apply, fderiv_coupledFlux]
  ext i
  fin_cases k <;> fin_cases i <;> norm_num [eigenvector, speed]
  cas

private theorem speed_strictMono (q : ℝ^2) : StrictMono (speed q) := by
  intro i j hij
  exact add_lt_add_right (Nat.cast_lt.mpr hij : (i.val : ℝ) < j.val) _

/-- The flux is strictly hyperbolic at every state. -/
theorem isStrictlyHyperbolicAt_coupledFlux (q : ℝ^2) :
    IsStrictlyHyperbolicAt coupledFlux q :=
  ⟨contDiff_coupledFlux.differentiable (by simp) q,
    eigenbasis q, speed q, (speed_strictMono q).injective,
    fun k ↦ ⟨Module.End.mem_eigenspace_iff.mpr (eigenvector_equation q k),
      (eigenbasis q).ne_zero k⟩⟩

/-- The ordered characteristic speeds are `q₀` and `q₀ + 1`. -/
theorem characteristicSpeed_coupledFlux (k : Fin 2) :
    characteristicSpeed coupledFlux k = fun q ↦ q 0 + (k.val : ℝ) := by
  funext q
  exact congrFun (characteristicSpeed_eq_of_eigenbasis (eigenbasis q)
    (speed_strictMono q) (eigenvector_equation q)) k

private theorem fderiv_speed (q v : ℝ^2) (k : Fin 2) :
    fderiv ℝ (fun q : ℝ^2 ↦ q 0 + (k.val : ℝ)) q v = v 0 := by
  rw [fderiv_apply_eq_sum_partialDeriv_mul, Fin.sum_univ_two]
  have h₀ : (∂[0] (fun q : ℝ^2 ↦ q 0 + (k : ℝ))) q = 1 := by
    cas
  have h₁ : (∂[1] (fun q : ℝ^2 ↦ q 0 + (k : ℝ))) q = 0 := by
    cas
  simp only [h₀, h₁, one_mul, zero_mul, add_zero]

/-- The first family is genuinely nonlinear. -/
theorem isGenuinelyNonlinearFamily_coupledFlux_zero :
    IsGenuinelyNonlinearFamily coupledFlux 0 := by
  intro q
  rw [characteristicSpeed_coupledFlux]
  constructor
  · simp only [Fin.val_zero, Nat.cast_zero]
    cas
  intro v hv
  rw [fderiv_speed]
  intro hzero
  have heq : fderiv ℝ coupledFlux q v = speed q 0 • v := hv.apply_eq_smul
  rw [fderiv_coupledFlux] at heq
  have he := congrArg (fun w : ℝ^2 ↦ w 1) heq
  simp [hzero, speed] at he
  have hvone : v 1 = 0 := by linarith
  apply hv.2
  ext i
  fin_cases i <;> simp [hzero, hvone]

/-- The fast family is linearly degenerate, although its speed varies with the state. -/
theorem isLinearlyDegenerateFamily_coupledFlux_one :
    IsLinearlyDegenerateFamily coupledFlux 1 := by
  intro q
  rw [characteristicSpeed_coupledFlux]
  constructor
  · simp only [Fin.val_one, Nat.cast_one]
    cas
  intro v hv
  rw [fderiv_speed]
  have heq : fderiv ℝ coupledFlux q v = speed q 1 • v := hv.apply_eq_smul
  rw [fderiv_coupledFlux] at heq
  have he := congrArg (fun w : ℝ^2 ↦ w 0) heq
  simp [speed] at he
  linarith

/-- Every ordered family of the coupled flux is genuinely nonlinear or linearly degenerate. -/
theorem family_alternatives_coupledFlux (k : Fin 2) :
    IsGenuinelyNonlinearFamily coupledFlux k ∨
      IsLinearlyDegenerateFamily coupledFlux k := by
  fin_cases k
  · exact Or.inl isGenuinelyNonlinearFamily_coupledFlux_zero
  · exact Or.inr isLinearlyDegenerateFamily_coupledFlux_one

/-- `‖(h, 1) - (0, 1)‖ = |h|`. -/
theorem norm_coupled_jump (h : ℝ) :
    ‖(!₂[h, 1] : ℝ^2) - !₂[0, 1]‖ = |h| := by
  have heq : (!₂[h, 1] : ℝ^2) - !₂[0, 1] = EuclideanSpace.single 0 h := by
    ext i
    fin_cases i <;> simp
  rw [heq, PiLp.norm_single, Real.norm_eq_abs]

/-- There is `δ > 0` such that for `|h| < δ` the Riemann problem from `(0, 1)` to `(h, 1)`
has a bounded self-similar weak solution with strong initial trace, constant outside
the cone `|x| ≤ M t`. -/
theorem exists_coupled_riemann_solution :
    ∃ δ K M : ℝ, 0 < δ ∧ 0 ≤ K ∧ 0 ≤ M ∧
      ∀ h : ℝ, |h| < δ → ∃ u : ℝ^2 → ℝ^2,
        IsWeakInitialValueSolution coupledFlux
          (riemannData !₂[0, 1] !₂[h, 1]) u ∧
        IsWeakSolutionWithInitialTrace coupledFlux
          (riemannData !₂[0, 1] !₂[h, 1]) u ∧
        Measurable u ∧ MemLp u ∞ (volume.restrict forwardHalfSpace) ∧
        (∀ p : ℝ^2, 0 < p 0 → ‖u p‖ ≤ K) ∧
        (∀ c : ℝ, 0 < c → ∀ p, u (c • p) = u p) ∧
        (∀ p : ℝ^2, 0 < p 0 → p 1 < -M * p 0 → u p = !₂[0, 1]) ∧
        (∀ p : ℝ^2, 0 < p 0 → M * p 0 ≤ p 1 → u p = !₂[h, 1]) ∧
        (∀ ψ : 𝓓^{1}((⊤ : TopologicalSpace.Opens ℝ^2), ℝ^2),
          IntegrableOn (fun p ↦ ⟪u p, (∂[0] (ψ : ℝ^2 → ℝ^2)) p⟫_ℝ +
            ⟪coupledFlux (u p), (∂[1] (ψ : ℝ^2 → ℝ^2)) p⟫_ℝ) forwardHalfSpace volume ∧
          Integrable (fun x : ℝ ↦ ⟪riemannData !₂[0, 1] !₂[h, 1] x, ψ !₂[0, x]⟫_ℝ) ∧
          (∫ p in forwardHalfSpace, ⟪u p, (∂[0] (ψ : ℝ^2 → ℝ^2)) p⟫_ℝ +
            ⟪coupledFlux (u p), (∂[1] (ψ : ℝ^2 → ℝ^2)) p⟫_ℝ) +
            ∫ x : ℝ, ⟪riemannData !₂[0, 1] !₂[h, 1] x, ψ !₂[0, x]⟫_ℝ = 0) := by
  obtain ⟨δ, K, M, hδ, hK, hM, hsolve⟩ :=
    exists_local_riemann_initialValue_solution
      (contDiff_coupledFlux.of_le (by simp)) isStrictlyHyperbolicAt_coupledFlux
      family_alternatives_coupledFlux !₂[0, 1]
  refine ⟨δ, K, M, hδ, hK, hM, ?_⟩
  intro h hh
  obtain ⟨_fields, _state, _lo, _hi, _wave, u, _hc, _hf, _hl, _hchain,
    _hwindow, _hsep, _hcone, _hwaves, hu, ht, hm, hL, hb, hs, hl, hr,
    _hformula, hv⟩ := hsolve !₂[h, 1] (by simpa only [norm_coupled_jump] using hh)
  exact ⟨u, hu, ht, hm, hL, hb, hs, hl, hr, hv⟩

/-- The first-family shock from `(0, 1)` to `(h, (1 - h/2)/(1 + h/2))` has speed `h/2`. It
changes the second component. -/
theorem coupled_first_shock_rankineHugoniot (h : ℝ) (hh : 1 + h / 2 ≠ 0) :
    RankineHugoniot coupledFlux !₂[0, 1] !₂[h, (1 - h / 2) / (1 + h / 2)] (h / 2) := by
  ext i
  fin_cases i
  · change h ^ 2 / 2 - 0 ^ 2 / 2 = h / 2 * (h - 0)
    cas
  · change (h + 1) * ((1 - h / 2) / (1 + h / 2)) - (0 + 1) * 1 =
      h / 2 * ((1 - h / 2) / (1 + h / 2) - 1)
    cas using hh

/-- The second, contact wave restores the prescribed second component. -/
theorem coupled_contact_rankineHugoniot (h b : ℝ) :
    RankineHugoniot coupledFlux !₂[h, b] !₂[h, 1] (h + 1) := by
  ext i
  fin_cases i
  · change h ^ 2 / 2 - h ^ 2 / 2 = (h + 1) * (h - h)
    cas
  · change (h + 1) * 1 - (h + 1) * b = (h + 1) * (1 - b)
    cas

/-- The derivative of the curve `s ↦ (s, exp(-s))` is `(1, -exp(-s))`. -/
theorem hasDerivAt_coupled_rarefaction (s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ (!₂[t, Real.exp (-t)] : ℝ^2))
      !₂[1, -Real.exp (-s)] s := by
  have h₀ : HasDerivAt (fun t : ℝ ↦ t) 1 s := by cas
  have h₁ : HasDerivAt (fun t : ℝ ↦ Real.exp (-t)) (-Real.exp (-s)) s := by
    cas
  have hsum := (h₀.smul_const (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))).add
    (h₁.smul_const (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))
  have hf : (fun t : ℝ ↦
      t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
      Real.exp (-t) • EuclideanSpace.single 1 1) =
      fun t ↦ (!₂[t, Real.exp (-t)] : ℝ^2) := by
    funext t
    ext i
    fin_cases i <;> simp
  have hd : (1 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
      -Real.exp (-s) • EuclideanSpace.single 1 1 =
      (!₂[1, -Real.exp (-s)] : ℝ^2) := by
    ext i
    fin_cases i <;> simp
  rw [Pi.add_def, hf, hd] at hsum
  exact hsum

end PDE.Examples.Hyperbolic.ConservationLaw.System.Riemann
