/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.HermiteCompactProfile
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import CAS.ExactTactic

/-!
# The natural origin row and interior regularity

At a zero left endpoint the natural first slope row removes the quadratic
coefficient of the first cubic. That cubic is exactly odd, so the compact
odd profile agrees with it on a neighborhood of zero. Together with the
interior slope equations this proves `C²` on the whole open support interval.
Neither the value nor the slope at the final knot enters this interior proof.
-/

@[expose] public section

noncomputable section

open Set
open scoped Polynomial Topology

namespace CAS.Splines

/-- The first Hermite cubic is odd when its value and second derivative at zero vanish.
The natural first slope equation enforces the latter condition exactly. -/
theorem hermitePolynomial_odd_of_natural {h b da db : ℝ} (hh : h ≠ 0)
    (heq : 2 * da + db = 3 * b / h) (x : ℝ) :
    (hermitePolynomial 0 h 0 b da db).eval (-x) =
      -(hermitePolynomial 0 h 0 b da db).eval x := by
  have hquadratic : -3 * (0 : ℝ) + 3 * b - h * (2 * da + db) = 0 := by
    rw [heq]
    cas using hh
  simp only [hermitePolynomial, hquadratic, Polynomial.C_0, zero_mul,
    add_zero, zero_add, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  cas

namespace HermiteData

variable {panels : ℕ}
variable (data : HermiteData (panels + 1)) (mesh : StrictKnotMesh (panels + 1))

/-- The natural first row of the physical slope system, without uniform-grid assumptions. -/
def NaturalOriginRow : Prop :=
  2 * data.slope 0 + data.slope 1 =
    3 * (data.value 1 - data.value 0) / (mesh.panelRight 0 - mesh.panelLeft 0)

/-- The natural first row makes the first panel's physical polynomial exactly odd. -/
theorem first_piece_odd (hmesh : mesh.knot 0 = 0) (hzero : data.value 0 = 0)
    (hnatural : data.NaturalOriginRow mesh) (x : ℝ) :
    ((data.polynomialData mesh).piece 0).eval (-x) =
      -((data.polynomialData mesh).piece 0).eval x := by
  have hleft : mesh.panelLeft 0 = 0 := hmesh
  have hh := (sub_pos.mpr (mesh.panelLeft_lt_panelRight 0)).ne'
  have heq : 2 * data.slope 0 + data.slope 1 =
      3 * data.value 1 / (mesh.panelRight 0 - mesh.panelLeft 0) := by
    simpa only [NaturalOriginRow, hzero, sub_zero] using hnatural
  have h := hermitePolynomial_odd_of_natural hh heq x
  have hfirst : (0 : Fin (panels + 1)).castSucc = 0 := rfl
  have hnext : (0 : Fin (panels + 1)).succ = 1 := rfl
  simpa only [polynomialData, hfirst, hnext, hleft, hzero] using h

/-- Around zero the compact odd profile is a single physical cubic. -/
theorem compactOddProfile_eventuallyEq_first_piece (hmesh : mesh.knot 0 = 0)
    (hzero : data.value 0 = 0) (hnatural : data.NaturalOriginRow mesh) :
    data.compactOddProfile mesh =ᶠ[𝓝 0] ((data.polynomialData mesh).piece 0).eval := by
  have hleft : mesh.panelLeft 0 = 0 := hmesh
  have hright : 0 < mesh.panelRight 0 := by
    simpa only [hleft] using mesh.panelLeft_lt_panelRight 0
  have hlast : mesh.panelRight 0 ≤ mesh.knot (Fin.last (panels + 1)) :=
    mesh.strictMono_knot.monotone (Fin.le_last _)
  have hpos {y : ℝ} (hy : y ∈ Icc 0 (mesh.panelRight 0)) :
      data.compactOddProfile mesh y = ((data.polynomialData mesh).piece 0).eval y := by
    rw [data.compactOddProfile_eq_assembled mesh hmesh hzero ⟨hy.1, hy.2.trans hlast⟩]
    exact data.assembledEvaluator_eq_piece mesh 0 (by simpa only [hleft] using hy)
  filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hright) hright] with x hx
  rcases le_or_gt 0 x with hxpos | hxneg
  · exact hpos ⟨hxpos, hx.2.le⟩
  · have hy : -x ∈ Icc 0 (mesh.panelRight 0) := by
      constructor <;> linarith [hx.1]
    have h := hpos hy
    rw [data.compactOddProfile_neg mesh, data.first_piece_odd mesh hmesh hzero hnatural] at h
    exact neg_injective h

/-- The compact profile is smooth through the origin when the natural first row holds.
This is a local polynomial statement, stronger than only `C²` at that point. -/
theorem contDiffAt_compactOddProfile_zero (hmesh : mesh.knot 0 = 0)
    (hzero : data.value 0 = 0) (hnatural : data.NaturalOriginRow mesh) (n : ℕ) :
    ContDiffAt ℝ n (data.compactOddProfile mesh) 0 := by
  have hp : ContDiff ℝ n ((data.polynomialData mesh).piece 0).eval := by
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using
      ((data.polynomialData mesh).piece 0).contDiff_aeval (𝕜 := ℝ) n
  exact hp.contDiffAt.congr_of_eventuallyEq
    (data.compactOddProfile_eventuallyEq_first_piece mesh hmesh hzero hnatural)

/-- The exact interior equations and natural first row give `C²` on `(-L,L)`,
including the origin and every interior mesh junction. No final-slope constraint is used. -/
theorem contDiffOn_two_compactOddProfile (hmesh : mesh.knot 0 = 0)
    (hzero : data.value 0 = 0) (heq : data.C2SlopeEquations mesh)
    (hnatural : data.NaturalOriginRow mesh) :
    ContDiffOn ℝ 2 (data.compactOddProfile mesh)
      (Ioo (-(mesh.knot (Fin.last (panels + 1)))) (mesh.knot (Fin.last (panels + 1)))) := by
  intro x hx
  rcases lt_trichotomy x 0 with hneg | rfl | hpos
  · exact (data.contDiffAt_two_compactOddProfile_neg mesh heq
      ⟨hx.1, hneg⟩).contDiffWithinAt
  · exact (data.contDiffAt_compactOddProfile_zero mesh hmesh hzero hnatural 2).contDiffWithinAt
  · exact (data.contDiffAt_two_compactOddProfile_pos mesh heq
      ⟨hpos, hx.2⟩).contDiffWithinAt

end HermiteData
end CAS.Splines
