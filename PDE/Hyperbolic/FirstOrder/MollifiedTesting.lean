/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.TransportTesting
public import PDE.Spaces.Sobolev.Approximation.Mollification.ProductH1
public import PDE.Spaces.Sobolev.Approximation.Mollification.TransportTime

/-!
# Mollifying the original transport distribution

For each coefficient entry, the mollified transport distribution is
`-Dεⱼ(a u) + Jε((∂ⱼa)u)`. Summing these rows gives the vector-valued
velocity. Self-adjointness of the standard mollifier identifies its pairing
with an L² vector with the original distribution tested on a mollified H¹
vector.

The time-dependent velocity is Bochner L² under base-coefficient continuity
on the closed interval and uniform bounds on the indicated spatial
derivatives.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace

namespace PDE.Hyperbolic.FirstOrder

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation

open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ}

local notation "D" => DerivLp n 2 univ
local notation "H" => PiLp 2 (fun _ : Fin m ↦ D)
local notation "V" => PiLp 2 (fun _ : Fin m ↦ H¹(ℝ^n))

/-- The mollification of `-∑ⱼ Aʲ ∂ⱼu`, defined for L² states by the
weak product rule. The differentiated coefficient is its Sobolev coordinate. -/
def mollifiedTransportDrift (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) (u : H) : H :=
  WithLp.toLp 2 (fun p ↦ ∑ j, ∑ q,
    (-mollifierDerivativeRowCLM μ hε j
        (((A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) • u q) +
      mollifierRowCLM μ hε
        (((A j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) • u q)))

/-- Product mollification with the standard even kernel is self-adjoint on L². -/
theorem inner_transportBase_mollifierProductH1CLM_left {ε : ℝ} (hε : 0 < ε) (u v : H) :
    ⟪transportBaseCLM (mollifierProductH1CLM (standardMollifier n) hε u), v⟫_ℝ =
      ⟪u, transportBaseCLM (mollifierProductH1CLM (standardMollifier n) hε v)⟫_ℝ := by
  classical
  simp only [PiLp.inner_apply, transportBaseCLM_apply, mollifierProductH1CLM_apply,
    mollifierH1CLM_base]
  apply Finset.sum_congr rfl
  intro p _
  exact inner_standardMollifierRowCLM_left hε (u p) (v p)

/-- The original distribution tested on the mollified H¹ vector equals the
pairing with the mollified transport velocity. -/
theorem inner_mollifiedTransportDrift {ε : ℝ} (hε : 0 < ε)
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) (u v : H) :
    ⟪mollifiedTransportDrift (standardMollifier n) hε A u, v⟫_ℝ =
      transportTestFunctional A (mollifierProductH1CLM (standardMollifier n) hε v) u := by
  classical
  rw [transportTestFunctional_apply]
  simp only [mollifiedTransportDrift, PiLp.inner_apply,
    sum_inner, mollifierProductH1CLM_apply, mollifierH1CLM_base, mollifierH1CLM_derivative]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro q _
  exact inner_mollified_transport_row hε (A j p q) j (u q) (v p)

/-- The mollified vector transport velocity is Bochner L² for every Bochner
L² input. Base coefficients are continuous on Icc; the divergence-coordinate
derivatives need only satisfy the displayed uniform bound. -/
theorem memLp_mollifiedTransportDrift (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b, ∀ j p q,
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L)
    {u : ℝ → H} (hu : MemLp u 2 (volume.restrict (Ioc a b))) :
    MemLp (fun t ↦ mollifiedTransportDrift μ hε (A t) (u t)) 2 (volume.restrict (Ioc a b)) := by
  classical
  let P (q : Fin m) : H →L[ℝ] D := PiLp.proj 2 (fun _ : Fin m ↦ D) q
  let row := fun (p : Fin m) t ↦ ∑ j : Fin n, ∑ q : Fin m, (-mollifierDerivativeRowCLM μ hε j
        (((A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) • u t q) + mollifierRowCLM μ hε
        (((A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) • u t q))
  have hrow (p : Fin m) : MemLp (row p) 2 (volume.restrict (Ioc a b)) := by
    dsimp only [row]
    apply memLp_finsetSum
    intro j _
    apply memLp_finsetSum
    intro q _
    exact memLp_mollified_transport_row μ hε hab (fun t ↦ A t j p q)
      (hA j p q) j L (fun t ht ↦ hL t ht j p q) ((P q).comp_memLp' hu)
  let I (p : Fin m) : D →L[ℝ] H :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ D)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin m ↦ D) p)
  have hsum (w : Fin m → D) : (∑ p, I p (w p)) = WithLp.toLp 2 w :=
    ContinuousLinearMap.sum_comp_single ℝ (fun _ : Fin m ↦ D)
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ D)).symm.toContinuousLinearMap w
  have h := memLp_finsetSum (Finset.univ : Finset (Fin m)) (fun p _ ↦ (I p).comp_memLp' (hrow p))
  simpa only [Function.comp_apply, hsum, row, mollifiedTransportDrift] using h

end PDE.Hyperbolic.FirstOrder
