/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.HermiteAssembly
public import PDE.Analysis.Calculus.CompactOddExtension
public import PDE.Spaces.Sobolev.Calculus.LipschitzCompactSupport
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Compact odd profiles from finite Hermite data

A nonempty strict mesh starting at zero and zero endpoint values produce a
continuous, globally Lipschitz, compactly supported odd function.
The data's endpoint slopes are unrestricted. The resulting function has a
global `H¹` representative with the almost-everywhere classical derivative
as its weak derivative.

The exact interior slope equations give `C²` away from zero and the exterior
endpoints. Adding the natural first row gives `C²` through the origin. At the
two exterior endpoints the profile need not be `C¹`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped NNReal Topology Sobolev
open PDE.Analysis.Calculus
open SobolevSpace.GraphSpace

namespace CAS.Splines.HermiteData

variable {panels : ℕ}
variable (data : HermiteData (panels + 1)) (mesh : StrictKnotMesh (panels + 1))

/-- The assembled positive-half interpolant, oddly reflected and extended by zero
when its endpoint values vanish. The positive support radius is the last knot. -/
def compactOddProfile : ℝ → ℝ :=
  compactOddExtension (data.assembledEvaluator mesh) (mesh.knot (Fin.last (panels + 1)))

/-- A nonempty strict mesh starting at zero has positive last knot. -/
theorem last_knot_pos (hmesh : mesh.knot 0 = 0) :
    0 < mesh.knot (Fin.last (panels + 1)) := by
  rw [← hmesh]
  exact mesh.strictMono_knot (show (0 : ℕ) < panels + 1 by omega)

/-- The assembled function has the supplied zero at the origin. -/
theorem assembledEvaluator_zero (hmesh : mesh.knot 0 = 0) (hzero : data.value 0 = 0) :
    data.assembledEvaluator mesh 0 = 0 := by
  have h := data.assembledEvaluator_knot mesh (Nat.succ_pos _) 0
  simpa only [hmesh, hzero] using h

/-- The positive half is the assembled Hermite function, including its endpoints. -/
theorem compactOddProfile_eq_assembled (hmesh : mesh.knot 0 = 0)
    (hzero : data.value 0 = 0) {x : ℝ}
    (hx : x ∈ Icc 0 (mesh.knot (Fin.last (panels + 1)))) :
    data.compactOddProfile mesh x = data.assembledEvaluator mesh x :=
  compactOddExtension_eq_of_mem_Icc (data.assembledEvaluator_zero mesh hmesh hzero) hx

/-- Every closed positive panel is evaluated by its own physical Hermite polynomial. -/
theorem compactOddProfile_eq_piece (hmesh : mesh.knot 0 = 0)
    (hzero : data.value 0 = 0) (panel : Fin (panels + 1)) {x : ℝ}
    (hx : x ∈ Icc (mesh.panelLeft panel) (mesh.panelRight panel)) :
    data.compactOddProfile mesh x = ((data.polynomialData mesh).piece panel).eval x := by
  have hleft : 0 ≤ mesh.panelLeft panel := by
    rw [← hmesh]
    exact mesh.strictMono_knot.monotone (Fin.zero_le _)
  have hright : mesh.panelRight panel ≤ mesh.knot (Fin.last (panels + 1)) :=
    mesh.strictMono_knot.monotone (Fin.le_last _)
  rw [data.compactOddProfile_eq_assembled mesh hmesh hzero
    ⟨hleft.trans hx.1, hx.2.trans hright⟩]
  exact data.assembledEvaluator_eq_piece mesh panel hx

/-- The physical polynomial derivative is the derivative within each closed panel,
including the one-sided derivative at either exterior endpoint. -/
theorem hasDerivWithinAt_compactOddProfile_panel (hmesh : mesh.knot 0 = 0)
    (hzero : data.value 0 = 0) (panel : Fin (panels + 1)) {x : ℝ}
    (hx : x ∈ Icc (mesh.panelLeft panel) (mesh.panelRight panel)) :
    HasDerivWithinAt (data.compactOddProfile mesh)
      (polynomialJet 1 ((data.polynomialData mesh).piece panel) x)
      (Icc (mesh.panelLeft panel) (mesh.panelRight panel)) x := by
  have hp := ((data.polynomialData mesh).piece panel).hasDerivWithinAt
    (s := Icc (mesh.panelLeft panel) (mesh.panelRight panel)) x
  simpa only [polynomialJet, Function.iterate_one] using
    hp.congr_of_mem (fun y hy ↦ data.compactOddProfile_eq_piece mesh hmesh hzero panel hy) hx

/-- All positive-half knots have their prescribed data values. -/
theorem compactOddProfile_knot (hmesh : mesh.knot 0 = 0)
    (hzero : data.value 0 = 0) (node : Fin (panels + 2)) :
    data.compactOddProfile mesh (mesh.knot node) = data.value node := by
  rw [data.compactOddProfile_eq_assembled mesh hmesh hzero,
    data.assembledEvaluator_knot mesh (Nat.succ_pos _) node]
  constructor
  · rw [← hmesh]
    exact mesh.strictMono_knot.monotone (Fin.zero_le _)
  · exact mesh.strictMono_knot.monotone (Fin.le_last _)

/-- The assembled compact profile is odd. -/
@[simp]
theorem compactOddProfile_neg (x : ℝ) :
    data.compactOddProfile mesh (-x) = -data.compactOddProfile mesh x :=
  compactOddExtension_neg _ _ _

/-- The compact odd profile vanishes at the origin. -/
@[simp]
theorem compactOddProfile_zero : data.compactOddProfile mesh 0 = 0 :=
  compactOddExtension_zero _ _

/-- The compact profile vanishes on both exterior rays, including the boundary points. -/
theorem compactOddProfile_eq_zero (hmesh : mesh.knot 0 = 0)
    (hzero : data.value 0 = 0) (hend : data.value (Fin.last (panels + 1)) = 0)
    {x : ℝ} (hx : mesh.knot (Fin.last (panels + 1)) ≤ |x|) :
    data.compactOddProfile mesh x = 0 := by
  apply compactOddExtension_eq_zero_of_le_abs (last_knot_pos mesh hmesh).le
    (data.assembledEvaluator_zero mesh hmesh hzero) _ hx
  rw [data.assembledEvaluator_knot mesh (Nat.succ_pos _), hend]

/-- The Lipschitz property needs neither a zero endpoint slope nor a slope-system assumption. -/
theorem exists_lipschitzWith_compactOddProfile (hmesh : mesh.knot 0 = 0) :
    ∃ K : ℝ≥0, LipschitzWith K (data.compactOddProfile mesh) :=
  exists_lipschitzWith_compactOddExtension (last_knot_pos mesh hmesh).le
    (data.contDiff_assembledEvaluator mesh).contDiffOn

/-- In particular the odd assembled profile is globally continuous. -/
theorem continuous_compactOddProfile (hmesh : mesh.knot 0 = 0) :
    Continuous (data.compactOddProfile mesh) :=
  (data.exists_lipschitzWith_compactOddProfile mesh hmesh).choose_spec.continuous

/-- Zero endpoint values give compact support, regardless of the endpoint slopes. -/
theorem hasCompactSupport_compactOddProfile (hmesh : mesh.knot 0 = 0)
    (hzero : data.value 0 = 0) (hend : data.value (Fin.last (panels + 1)) = 0) :
    HasCompactSupport (data.compactOddProfile mesh) := by
  apply hasCompactSupport_compactOddExtension (last_knot_pos mesh hmesh).le
    (data.assembledEvaluator_zero mesh hmesh hzero)
  rw [data.assembledEvaluator_knot mesh (Nat.succ_pos _), hend]

/-- The classical derivative, defined almost everywhere, is the global weak derivative.
This includes the interfaces at the origin, all mesh knots, and both exterior endpoints. -/
theorem hasWeakTimeDerivativeOn_compactOddProfile (hmesh : mesh.knot 0 = 0)
    (hzero : data.value 0 = 0) (hend : data.value (Fin.last (panels + 1)) = 0) :
    PDE.Analysis.Evolution.HasWeakTimeDerivativeOn univ (data.compactOddProfile mesh)
      (deriv (data.compactOddProfile mesh)) :=
  hasWeakTimeDerivativeOn_of_lipschitzWith_compactSupport
    (data.exists_lipschitzWith_compactOddProfile mesh hmesh).choose_spec
    (data.hasCompactSupport_compactOddProfile mesh hmesh hzero hend)

/-- The compact odd profile as a global `H¹` graph-space element. -/
def compactOddProfileH1 (hmesh : mesh.knot 0 = 0)
    (hzero : data.value 0 = 0) (hend : data.value (Fin.last (panels + 1)) = 0) :
    W^{1,2}(ℝ^1) :=
  mkW12OfLipschitzCompactSupport
    (data.exists_lipschitzWith_compactOddProfile mesh hmesh).choose_spec
    (data.hasCompactSupport_compactOddProfile mesh hmesh hzero hend)

/-- The two coordinates of the `H¹` element are almost everywhere the profile and its
classical derivative. -/
theorem compactOddProfileH1_apply_ae (hmesh : mesh.knot 0 = 0)
    (hzero : data.value 0 = 0) (hend : data.value (Fin.last (panels + 1)) = 0)
    (a : DerivIndex 1 1) :
    (((data.compactOddProfileH1 mesh hmesh hzero hend : WkpAmbientOn 1 1 2 univ)
      a : DerivLp 1 2 univ) : ℝ^1 → ℝ) =ᵐ[volume]
      w11Rows (data.compactOddProfile mesh) (deriv (data.compactOddProfile mesh)) a :=
  mkW12OfLipschitzCompactSupport_apply_ae _ _ a

/-- Exact interior slope equations give `C²` at every strictly positive interior point,
including all positive interior knots. -/
theorem contDiffAt_two_compactOddProfile_pos (heq : data.C2SlopeEquations mesh) {x : ℝ}
    (hx : x ∈ Ioo 0 (mesh.knot (Fin.last (panels + 1)))) :
    ContDiffAt ℝ 2 (data.compactOddProfile mesh) x :=
  contDiffAt_compactOddExtension hx (data.contDiff_two_assembledEvaluator mesh heq).contDiffAt

/-- The reflected interior has the same `C²` regularity. -/
theorem contDiffAt_two_compactOddProfile_neg (heq : data.C2SlopeEquations mesh) {x : ℝ}
    (hx : x ∈ Ioo (-(mesh.knot (Fin.last (panels + 1)))) 0) :
    ContDiffAt ℝ 2 (data.compactOddProfile mesh) x :=
  contDiffAt_compactOddExtension_neg hx (data.contDiff_two_assembledEvaluator mesh heq).contDiffAt

end CAS.Splines.HermiteData
