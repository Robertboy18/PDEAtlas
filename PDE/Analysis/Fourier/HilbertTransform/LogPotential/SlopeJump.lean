/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.LogPotential.Quadratic
public import CAS.Analysis.Approximation.Splines.PiecewisePolynomial
import CAS.ExactTactic

/-!
# The endpoint jump in an even piecewise quadratic log convolution

Shared nodal values cancel all interior boundary terms. At the origin the reflected
terms cancel each other. The nonzero outer endpoint value leaves a logarithmic ratio.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

namespace PDE.Analysis

open CAS.Analysis

/-- Differentiating the reflected sum retains precisely the outer endpoint jump.
Evaluation points at reflected knots are excluded from this derivative formula. -/
theorem hasDerivAt_even_mesh_log_sum {n : ℕ} (mesh : CAS.Splines.StrictKnotMesh n)
    (p : Fin n → ℝ[X]) (m : Fin (n + 1) → ℝ)
    (hp : ∀ i, (p i).natDegree ≤ 2) (hzero : mesh.knot 0 = 0)
    (hleft : ∀ i, (p i).eval (mesh.panelLeft i) = m i.castSucc)
    (hright : ∀ i, (p i).eval (mesh.panelRight i) = m i.succ)
    (x : ℝ) (hx : ∀ k, x ≠ mesh.knot k) (hneg : ∀ k, -x ≠ mesh.knot k) :
    HasDerivAt
      (fun z ↦ ∑ i : Fin n,
        (polynomialLogPanel (p i) (mesh.panelLeft i) (mesh.panelRight i) z +
          polynomialLogPanel (p i) (mesh.panelLeft i) (mesh.panelRight i) (-z)))
      ((∑ i : Fin n,
          (polynomialLogPanel (p i).derivative (mesh.panelLeft i) (mesh.panelRight i) x -
            polynomialLogPanel (p i).derivative (mesh.panelLeft i) (mesh.panelRight i) (-x))) +
        m (Fin.last n) *
          (Real.log (x + mesh.knot (Fin.last n)) -
            Real.log (x - mesh.knot (Fin.last n)))) x := by
  let A (k : Fin (n + 1)) :=
    m k * (Real.log (x + mesh.knot k) - Real.log (x - mesh.knot k))
  have hd (i : Fin n) :
      HasDerivAt
        (fun z ↦ polynomialLogPanel (p i) (mesh.panelLeft i) (mesh.panelRight i) z +
          polynomialLogPanel (p i) (mesh.panelLeft i) (mesh.panelRight i) (-z))
        ((polynomialLogPanel (p i).derivative (mesh.panelLeft i) (mesh.panelRight i) x -
            polynomialLogPanel (p i).derivative (mesh.panelLeft i) (mesh.panelRight i) (-x)) +
          (A i.succ - A i.castSucc)) x := by
    have h₁ := hasDerivAt_polynomialLogPanel (p i) (hp i)
      (mesh.panelLeft i) (mesh.panelRight i) x (hx i.castSucc) (hx i.succ)
    have h₂ := (hasDerivAt_polynomialLogPanel (p i) (hp i)
      (mesh.panelLeft i) (mesh.panelRight i) (-x) (hneg i.castSucc) (hneg i.succ)).comp
        x (hasDerivAt_neg x)
    convert h₁.add h₂ using 1
    · funext z
      rfl
    · rw [hleft, hright]
      simp only [A, CAS.Splines.StrictKnotMesh.panelLeft,
        CAS.Splines.StrictKnotMesh.panelRight]
      rw [show -x - mesh.knot i.castSucc = -(x + mesh.knot i.castSucc) by cas,
        show -x - mesh.knot i.succ = -(x + mesh.knot i.succ) by cas,
        Real.log_neg_eq_log, Real.log_neg_eq_log]
      ring
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hd i)
  have htelescope : (∑ i : Fin n, (A i.succ - A i.castSucc)) = A (Fin.last n) := by
    have h₁ := Fin.sum_univ_succ A
    have h₂ := Fin.sum_univ_castSucc A
    have h₀ : A 0 = 0 := by simp [A, hzero]
    rw [Finset.sum_sub_distrib]
    linarith
  simpa only [Finset.sum_add_distrib, htelescope, A] using hs

end PDE.Analysis
