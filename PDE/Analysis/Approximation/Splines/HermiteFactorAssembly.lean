/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.HermiteFactorControls

/-!
# Factor certificates for assembled Hermite profiles

At every point in the open support, including interior knots, the derivative
of the compact odd profile agrees with the derivative of any containing panel.
Thus Bernstein certificates for a panel polynomial apply to the profile and its
classical derivative. Differentiability at the exterior endpoints is not needed.
-/

@[expose] public section

noncomputable section

open Set

namespace CAS.Splines.HermiteData

variable {panels : ℕ}

/-- Interior classical derivatives agree with either adjacent closed panel.
Shared first jets suffice; no second-derivative slope equations are needed. -/
theorem deriv_compactOddProfile_eq_panel
    (data : HermiteData (panels + 1)) (mesh : StrictKnotMesh (panels + 1))
    (hmesh : mesh.knot 0 = 0) (hzero : data.value 0 = 0)
    (i : Fin (panels + 1)) {x : ℝ}
    (hx : x ∈ Ioo 0 (mesh.knot (Fin.last (panels + 1))))
    (hpanel : x ∈ Icc (mesh.panelLeft i) (mesh.panelRight i)) :
    deriv (data.compactOddProfile mesh) x =
      polynomialJet 1 ((data.polynomialData mesh).piece i) x := by
  have hf : DifferentiableAt ℝ (data.compactOddProfile mesh) x :=
    (PDE.Analysis.Calculus.contDiffAt_compactOddExtension hx
      (data.contDiff_assembledEvaluator mesh).contDiffAt).differentiableAt (by norm_num)
  exact (uniqueDiffOn_Icc (mesh.panelLeft_lt_panelRight i) x hpanel).eq_deriv _
    hf.hasDerivAt.hasDerivWithinAt
    (data.hasDerivWithinAt_compactOddProfile_panel mesh hmesh hzero i hpanel)

/-- A closed-panel control certificate gives strict sign for the weighted derivative
factor of the compact profile, including a shared knot. -/
theorem factor_compactOddProfile_neg_of_controls
    (data : HermiteData (panels + 1)) (mesh : StrictKnotMesh (panels + 1))
    (hmesh : mesh.knot 0 = 0) (hzero : data.value 0 = 0)
    (κ center : ℝ) (i : Fin (panels + 1)) {x : ℝ}
    (hx : x ∈ Ioo 0 (mesh.knot (Fin.last (panels + 1))))
    (hpanel : x ∈ Icc (mesh.panelLeft i) (mesh.panelRight i))
    (hnonpos : ∀ k, hermiteFactorControl κ (mesh.panelLeft i - center)
      (mesh.panelRight i - mesh.panelLeft i) (data.value i.castSucc) (data.value i.succ)
      (data.slope i.castSucc) (data.slope i.succ) k ≤ 0)
    (hstrict :
      hermiteFactorControl κ (mesh.panelLeft i - center)
        (mesh.panelRight i - mesh.panelLeft i) (data.value i.castSucc) (data.value i.succ)
        (data.slope i.castSucc) (data.slope i.succ) 0 < 0 ∨
      hermiteFactorControl κ (mesh.panelLeft i - center)
        (mesh.panelRight i - mesh.panelLeft i) (data.value i.castSucc) (data.value i.succ)
        (data.slope i.castSucc) (data.slope i.succ) 3 < 0)
    (hleft : x = mesh.panelLeft i →
      hermiteFactorControl κ (mesh.panelLeft i - center)
        (mesh.panelRight i - mesh.panelLeft i) (data.value i.castSucc) (data.value i.succ)
        (data.slope i.castSucc) (data.slope i.succ) 0 < 0)
    (hright : x = mesh.panelRight i →
      hermiteFactorControl κ (mesh.panelLeft i - center)
        (mesh.panelRight i - mesh.panelLeft i) (data.value i.castSucc) (data.value i.succ)
        (data.slope i.castSucc) (data.slope i.succ) 3 < 0) :
    data.compactOddProfile mesh x - κ * (x - center) * deriv (data.compactOddProfile mesh) x
      < 0 := by
  rw [data.compactOddProfile_eq_piece mesh hmesh hzero i hpanel,
    data.deriv_compactOddProfile_eq_panel mesh hmesh hzero i hx hpanel]
  refine hermitePolynomial_factor_neg_of_controls
    κ center (mesh.panelLeft i) (mesh.panelRight i - mesh.panelLeft i)
    (data.value i.castSucc) (data.value i.succ) (data.slope i.castSucc) (data.slope i.succ)
    (sub_pos.mpr (mesh.panelLeft_lt_panelRight i)) ?_ hnonpos hstrict hleft ?_
  · simpa only [add_sub_cancel] using hpanel
  · simpa only [add_sub_cancel] using hright

end CAS.Splines.HermiteData
