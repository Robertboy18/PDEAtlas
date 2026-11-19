/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ShockCurve.LinearlyDegenerate
public import PDE.Analysis.Calculus.Jacobian.Basic
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import PDE.Symbolic.PDEDerivatives
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# A curved linearly degenerate shock germ

The nonlinear flux `(a, 2b - a²)` has constant speeds one and two, so both families
are linearly degenerate. Its first characteristic curves
`t ↦ (a + t, b + 2at + t²)` are parabolas. By
`exists_local_shock_curves_eq_linearly_degenerate_flow` and
`exists_local_reparametrization_of_linearly_degenerate_integralCurve`, the first shock
curve through `q` is a reparametrization of this parabola, with speed one
(`exists_parabolic_shock_germ`).
-/

@[expose] public noncomputable section

namespace PDE.Examples.Hyperbolic.ConservationLaw.System.ShockCurve.LinearlyDegenerate

open PDE.Common PDE.Hyperbolic.ConservationLaw.System
open Filter Set
open scoped ContDiff Topology

/-- A nonlinear triangular flux with two linearly degenerate families. -/
def flux (q : ℝ^2) : ℝ^2 := !₂[q 0, 2 * q 1 - q 0 ^ 2]

/-- The first characteristic field. -/
def field (q : ℝ^2) : ℝ^2 := !₂[1, 2 * q 0]

/-- The first characteristic curve through an arbitrary state. -/
def curve (q : ℝ^2) (t : ℝ) : ℝ^2 :=
  !₂[q 0 + t, q 1 + 2 * q 0 * t + t ^ 2]

/-- The flux is smooth. -/
theorem contDiff_flux : ContDiff ℝ ∞ flux := by
  rw [contDiff_piLp]
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun q : ℝ^2 ↦ q 0)
    cas
  · change ContDiff ℝ ∞ (fun q : ℝ^2 ↦ 2 * q 1 - q 0 ^ 2)
    cas

/-- The Jacobian matrix of the flux is `!![1, 0; -2q₀, 2]`. -/
theorem jacobianMatrix_flux (q : ℝ^2) :
    PDE.Analysis.jacobianMatrix flux q = !![1, 0; -2 * q 0, 2] := by
  ext i j
  fin_cases i <;> fin_cases j
  · change (∂[0] (fun y : ℝ^2 ↦ y 0)) q = 1
    cas
  · change (∂[1] (fun y : ℝ^2 ↦ y 0)) q = 0
    cas
  · change (∂[0] ((fun y : ℝ^2 ↦ 2 * y 1 - y 0 ^ 2) : ℝ^2 → ℝ)) q = -2 * q 0
    cas
  · change (∂[1] ((fun y : ℝ^2 ↦ 2 * y 1 - y 0 ^ 2) : ℝ^2 → ℝ)) q = 2
    cas

/-- The Jacobian applied to `v` is `(v₀, -2q₀ v₀ + 2v₁)`. -/
theorem fderiv_flux (q v : ℝ^2) :
    fderiv ℝ flux q v = !₂[v 0, -2 * q 0 * v 0 + 2 * v 1] := by
  rw [fderiv_apply_eq_sum_smul_partialDeriv]
  ext i
  simp only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hj (j : Fin 2) :
      (∂[j] flux) q i = (!![1, 0; -2 * q 0, 2] : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    rw [← jacobianMatrix_flux q]
    exact (PDE.Analysis.jacobianMatrix_apply_eq_fderiv
      (contDiff_flux.differentiable (by simp) q) i j).symm
  rw [hj 0, hj 1]
  fin_cases i
  · change v 0 * 1 + v 1 * 0 = v 0
    cas
  · change v 0 * (-2 * q 0) + v 1 * 2 = -2 * q 0 * v 0 + 2 * v 1
    cas

private def eigenvector (q : ℝ^2) (k : Fin 2) : ℝ^2 :=
  if k = 0 then field q else !₂[0, 1]

private theorem independent_eigenvectors (q : ℝ^2) :
    LinearIndependent ℝ (eigenvector q) := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have hc := congrArg (fun v : ℝ^2 ↦ v 1) h
    norm_num [eigenvector] at hc
  · intro a h
    have hc := congrArg (fun v : ℝ^2 ↦ v 0) h
    norm_num [eigenvector, field] at hc

private def eigenbasis (q : ℝ^2) : Module.Basis (Fin 2) ℝ (ℝ^2) :=
  basisOfLinearIndependentOfCardEqFinrank (independent_eigenvectors q) (by simp)

private theorem eigenbasis_apply (q : ℝ^2) (k : Fin 2) :
    eigenbasis q k = eigenvector q k :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) k

private theorem eigenvector_equation (q : ℝ^2) (k : Fin 2) :
    fderiv ℝ flux q (eigenbasis q k) = ((k.val : ℝ) + 1) • eigenbasis q k := by
  rw [eigenbasis_apply, fderiv_flux]
  ext i
  fin_cases k <;> fin_cases i <;> norm_num [eigenvector, field]
  cas

private theorem strictMono_speed : StrictMono (fun k : Fin 2 ↦ (k.val : ℝ) + 1) :=
  fun _ _ h ↦ add_lt_add_of_lt_of_le (Nat.cast_lt.mpr h) le_rfl

/-- The flux is strictly hyperbolic at every state. -/
theorem isStrictlyHyperbolicAt_flux (q : ℝ^2) : IsStrictlyHyperbolicAt flux q :=
  ⟨contDiff_flux.differentiable (by simp) q, eigenbasis q,
    fun k ↦ (k.val : ℝ) + 1, strictMono_speed.injective,
    fun k ↦ ⟨Module.End.mem_eigenspace_iff.mpr (eigenvector_equation q k),
      (eigenbasis q).ne_zero k⟩⟩

/-- The canonical ordered speeds are the constants one and two. -/
theorem characteristicSpeed_flux (k : Fin 2) :
    characteristicSpeed flux k = fun _ ↦ (k.val : ℝ) + 1 := by
  funext q
  exact congrFun (characteristicSpeed_eq_of_eigenbasis (eigenbasis q)
    strictMono_speed (eigenvector_equation q)) k

/-- Both families are linearly degenerate. -/
theorem isLinearlyDegenerateFamily_flux (k : Fin 2) : IsLinearlyDegenerateFamily flux k := by
  intro q
  rw [characteristicSpeed_flux]
  exact ⟨differentiableAt_const _, fun _ _ ↦ by simp⟩

/-- `field q` is an eigenvector of the Jacobian for the first characteristic speed. -/
theorem eigenvector_field (q : ℝ^2) :
    Module.End.HasEigenvector (fderiv ℝ flux q).toLinearMap
      (characteristicSpeed flux 0 q) (field q) := by
  have he := eigenvector_equation q 0
  rw [eigenbasis_apply] at he
  simp only [eigenvector, ite_true, Fin.val_zero, Nat.cast_zero, zero_add] at he
  rw [characteristicSpeed_flux]
  refine ⟨Module.End.mem_eigenspace_iff.mpr (by simpa using he), ?_⟩
  intro h
  have hc := congrArg (fun v : ℝ^2 ↦ v 0) h
  norm_num [field] at hc

/-- The parabolic trajectory starts at the prescribed state. -/
theorem curve_zero (q : ℝ^2) : curve q 0 = q := by
  ext i
  fin_cases i <;> simp [curve]

/-- The parabolic curve is smooth. -/
theorem contDiff_curve (q : ℝ^2) : ContDiff ℝ ∞ (curve q) := by
  rw [contDiff_piLp]
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun t : ℝ ↦ q 0 + t)
    cas
  · change ContDiff ℝ ∞ (fun t : ℝ ↦ q 1 + 2 * q 0 * t + t ^ 2)
    cas

/-- The trajectory satisfies the characteristic ODE. -/
theorem hasDerivAt_curve (q : ℝ^2) (t : ℝ) :
    HasDerivAt (curve q) (field (curve q t)) t := by
  have hd : HasDerivAt
      (fun s : ℝ ↦ ![q 0 + s, q 1 + 2 * q 0 * s + s ^ 2])
      ![1, 2 * (q 0 + t)] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · change HasDerivAt (fun s : ℝ ↦ q 0 + s) 1 t
      cas
    · change HasDerivAt (fun s : ℝ ↦ q 1 + 2 * q 0 * s + s ^ 2) (2 * (q 0 + t)) t
      cas
  exact (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt t hd

/-- The Riemann invariant `b - a²` is constant along the curve. -/
theorem curve_invariant (q : ℝ^2) (t : ℝ) :
    curve q t 1 - (curve q t 0) ^ 2 = q 1 - q 0 ^ 2 := by
  change q 1 + 2 * q 0 * t + t ^ 2 - (q 0 + t) ^ 2 = q 1 - q 0 ^ 2
  cas

/-- Near `q` the first shock curve and the parabolic integral curve agree up to mutually
inverse reparametrizations `α` and `β`, and the shock speed is one. -/
theorem exists_parabolic_shock_germ (q : ℝ^2) :
    ∃ S : ℝ → ℝ^2, ∃ speed α β : ℝ → ℝ, ∃ I : Set ℝ,
      IsOpen I ∧ 0 ∈ I ∧ S 0 = q ∧ speed 0 = 1 ∧
      ContDiffOn ℝ 1 S I ∧ ContDiffOn ℝ 1 speed I ∧
      (∀ s ∈ I, RankineHugoniot flux q (S s) (speed s)) ∧
      α 0 = 0 ∧ β 0 = 0 ∧ ContDiffAt ℝ 1 α 0 ∧ ContDiffAt ℝ 1 β 0 ∧
      (∀ᶠ t in 𝓝 0, curve q t = S (α t) ∧ β (α t) = t) ∧
      (∀ᶠ s in 𝓝 0, α (β s) = s ∧ S s = curve q (β s) ∧ speed s = 1 ∧
        S s 1 - (S s 0) ^ 2 = q 1 - q 0 ^ 2) := by
  obtain ⟨b, S, speed, I, V, _r, _R, _W, hI, hzero, hV, hqV, _hW, _hqW,
      heigen, hcurves, hclass, _⟩ :=
    exists_local_shock_curves_eq_linearly_degenerate_flow
      (contDiff_flux.of_le (by simp)) (isStrictlyHyperbolicAt_flux q)
      (isLinearlyDegenerateFamily_flux 0)
  obtain ⟨β, hα₀, hβ₀, hα, hβ, _hdα, _hne, hforward, hback, hleft⟩ :=
    exists_local_reparametrization_of_linearly_degenerate_integralCurve
      (contDiff_flux.differentiable (by simp)) (isStrictlyHyperbolicAt_flux q)
      (isLinearlyDegenerateFamily_flux 0) b heigen hV hqV
      (fun j ↦ (hcurves j).1) (fun j ↦ (hcurves j).2.1)
      (fun j ↦ ((hcurves j).2.2.2.1.contDiffAt (hI.mem_nhds hzero)).continuousAt)
      (fun j s hs ↦ ((hcurves j).2.2.2.2.2 s hs).2) hclass
      (curve_zero q) ((contDiff_curve q).of_le (by simp)).contDiffAt
      (Filter.Eventually.of_forall (hasDerivAt_curve q))
      (Filter.Eventually.of_forall eigenvector_field)
  refine ⟨S 0, speed 0, fun t ↦ b.equivFun (curve q t - q) 0, β, I,
    hI, hzero, (hcurves 0).1, ?_, (hcurves 0).2.2.1,
    (hcurves 0).2.2.2.1, fun s hs ↦ ((hcurves 0).2.2.2.2.2 s hs).1,
    hα₀, hβ₀, hα, hβ, ?_, ?_⟩
  · simpa only [characteristicSpeed_flux, Fin.val_zero, Nat.cast_zero, zero_add]
      using (hcurves 0).2.1
  · filter_upwards [hforward, hleft] with t ht hl
    exact ⟨ht.1, hl⟩
  · filter_upwards [hback] with s hs
    refine ⟨hs.1, hs.2.1, ?_, ?_⟩
    · simpa only [characteristicSpeed_flux, Fin.val_zero, Nat.cast_zero, zero_add] using hs.2.2
    · rw [hs.2.1]
      exact curve_invariant q (β s)

end PDE.Examples.Hyperbolic.ConservationLaw.System.ShockCurve.LinearlyDegenerate
