/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.MollifiedTesting

/-!
# Commuting transport with spatial mollification

The mollified distribution differs from transport of the mollified state by
`a Dεu - Dε(a u) + Jε((∂a)u)`, summed over the spatial and component indices.
We prove that identity and construct its Bochner L² class.

The class tends to zero along every positive scale sequence tending to zero.
At each time, the spatial commutator converges strongly on L². A uniform
bound on the spatial coefficient derivatives gives a common L² majorant
proportional to the state norm, so dominated convergence applies in time.
The fixed-scale coefficient argument supplies measurability. Finite sums
and the component injections give the vector result. No time continuity
of weak spatial coefficient derivatives is assumed.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace Topology

namespace PDE.Hyperbolic.FirstOrder

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation

open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ} {a b : ℝ}

local notation "D" => DerivLp n 2 univ
local notation "H" => PiLp 2 (fun _ : Fin m ↦ D)
local notation "V" => PiLp 2 (fun _ : Fin m ↦ H¹(ℝ^n))
local notation "ν" => volume.restrict (Ioc a b)

/-- The finite-system residual between mollifying the original transport
and transporting the mollified state. All coefficient derivatives are the
weak Sobolev coordinates. -/
def transportCommutator (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) (u : H) : H :=
  WithLp.toLp 2 (fun p ↦ ∑ j, ∑ q,
    mollifierTransportCommutatorCLM μ hε (A j p q) j (u q))

/-- Mollifying the original weak drift equals the original drift of the
mollified H¹ state plus the transport commutator. -/
theorem mollifiedTransportDrift_eq_transportDrift_add (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) (u : H) :
    mollifiedTransportDrift μ hε A u =
      transportDrift A (mollifierProductH1CLM μ hε u) + transportCommutator μ hε A u := by
  classical
  refine PiLp.ext fun p ↦ ?_
  simp only [mollifiedTransportDrift, transportDrift, transportCommutator,
    WithLp.ofLp_add, WithLp.ofLp_toLp, Pi.add_apply]
  change (∑ j : Fin n, ∑ q : Fin m, _) =
    -(∑ j : Fin n, ∑ q : Fin m, _) + ∑ j : Fin n, ∑ q : Fin m, _
  simp only [mollifierProductH1CLM_apply, mollifierH1CLM_derivative,
    mollifierTransportCommutatorCLM_apply, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  abel

/-- Construct the Bochner L² classes of the commutators and prove their
strong convergence to zero. The common bound controls the sum of all spatial
derivative norms of each coefficient entry. -/
theorem exists_transportCommutatorLp_sequence (μ : Mollifier n) (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k)
    (hε0 : Tendsto ε atTop (𝓝 0)) (hab : a ≤ b)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b, ∀ j p q,
      (∑ l : Fin n, ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)‖) ≤ L)
    (u : Lp H 2 ν) :
    ∃ R : ℕ → Lp H 2 ν, (∀ k, (R k : ℝ → H) =ᵐ[ν] fun t ↦ transportCommutator μ (hε k) (A t)
      (u t)) ∧ Tendsto R atTop (𝓝 0) := by
  classical
  let P (q : Fin m) : H →L[ℝ] D := PiLp.proj 2 (fun _ : Fin m ↦ D) q
  let I (p : Fin m) : D →L[ℝ] H :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ D)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin m ↦ D) p)
  let T := Fin m × Fin n × Fin m
  let r (k : ℕ) (i : T) : ℝ → D := fun t ↦
    mollifierTransportCommutatorCLM μ (hε k) (A t i.2.1 i.1 i.2.2) i.2.1 (u t i.2.2)
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) (j : Fin n) (p q : Fin m) :
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L :=
    (Finset.single_le_sum (fun l _ ↦ norm_nonneg
      ((A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)))
      (Finset.mem_univ j)).trans (hL t ht j p q)
  have hr (k : ℕ) (i : T) : MemLp (r k i) 2 ν := memLp_mollifierTransportCommutatorCLM μ (hε k) hab
      (fun t ↦ A t i.2.1 i.1 i.2.2) (hA i.2.1 i.1 i.2.2) i.2.1 L
      (fun t ht ↦ hderiv t ht i.2.1 i.1 i.2.2) ((P i.2.2).comp_memLp u)
  let Q (k : ℕ) (i : T) : Lp D 2 ν := (hr k i).toLp (r k i)
  let F (k : ℕ) (i : T) : Lp H 2 ν := (I i.1).compLpL 2 ν (Q k i)
  let R (k : ℕ) : Lp H 2 ν := ∑ i : T, F k i
  have hQzero (i : T) : Tendsto (fun k ↦ Q k i) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have he := tendsto_eLpNorm_mollifierTransportCommutatorCLM μ ε hε hε0 hab
      (fun t ↦ A t i.2.1 i.1 i.2.2) (hA i.2.1 i.1 i.2.2) L
      (fun t ht ↦ hL t ht i.2.1 i.1 i.2.2) i.2.1
      (show (1 : ℝ≥0∞) ≤ 2 by norm_num) (by norm_num) ((P i.2.2).comp_memLp u)
    have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he
    convert hreal using 1 <;>
      simp only [Q, Lp.norm_toLp, ENNReal.toReal_zero, Function.comp_apply, r, P, PiLp.proj_apply]
    funext k
    rfl
  have hFzero (i : T) : Tendsto (fun k ↦ F k i) atTop (𝓝 0) := by
    have h := ((I i.1).compLpL 2 ν).continuous.continuousAt.tendsto.comp (hQzero i)
    convert h using 1 <;> simp only [map_zero, F]
    funext k
    rfl
  have hRzero : Tendsto R atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset T) (fun i _ ↦ hFzero i)
    simpa only [Finset.sum_const_zero] using h
  have hFcoe (k : ℕ) (i : T) : (F k i : ℝ → H) =ᵐ[ν] fun t ↦ I i.1 (r k i t) := by
    filter_upwards [(I i.1).coeFn_compLpL (Q k i), (hr k i).coeFn_toLp] with t hI hQ
    rw [hI, hQ]
  have hsum (w : Fin m → D) : (∑ p, I p (w p)) = WithLp.toLp 2 w :=
    ContinuousLinearMap.sum_comp_single ℝ (fun _ : Fin m ↦ D)
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ D)).symm.toContinuousLinearMap w
  refine ⟨R, ?_, hRzero⟩
  intro k
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.univ : Finset T) (F k),
    ae_all_iff.mpr (hFcoe k)] with t hRt hFt
  change R k t = _
  calc
    _ = ∑ i : T, F k i t := hRt
    _ = ∑ i : T, I i.1 (r k i t) := Finset.sum_congr rfl (fun i _ ↦ hFt i)
    _ = ∑ p : Fin m, I p (∑ j : Fin n, ∑ q : Fin m,
        mollifierTransportCommutatorCLM μ (hε k) (A t j p q) j (u t q)) := by
      simp only [T, r, Fintype.sum_prod_type, map_sum]
    _ = transportCommutator μ (hε k) (A t) (u t) := hsum _

end PDE.Hyperbolic.FirstOrder
