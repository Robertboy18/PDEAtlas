/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Classical.ContinuousEmbedding
public import PDE.Spaces.Sobolev.Fractional.Integer.Energy

/-!
# A real function with finite Sobolev energy of every order is smooth

A real function `u ∈ L²(ℝⁿ)` is only a class modulo null sets. If its energy `E_k` is finite for
every integer `k`, the class contains a `C^∞` function, in every dimension. No bounds for the
derivatives of that function are given here.
`SobolevSpace.GraphSpace.contDiff_continuousRepresentative_of_forall_wkpSpace` reaches the same
conclusion for `n > 0` from graph spaces: there the class lies in every `W^{m,2}(ℝⁿ)`, and the
smooth function is the canonical continuous representative.

## Main results

* `exists_hsSpaceReal_of_besselEnergy_lt_top`: a real `g ∈ L²(ℝⁿ; ℂ)` with finite energy of order
  `k` is the `L²` representative of an element of the real space `H^k`. This is
  `exists_toL2Fun_eq_of_besselEnergy_lt_top` for real functions.
* `exists_contDiff_ae_eq_of_forall_besselEnergy_lt_top`: a real `u ∈ L²(ℝⁿ)` with finite energy
  of every integer order is almost everywhere equal to a `C^∞` function.

## How it works

For each `k` the function is the `L²` representative of an element of `H^k`, and for
`k > n/2 + r` the Sobolev embedding gives a `C^r` function in its class
(`HsSpaceReal.contDiff_c1Representative_of_order`, `HsSpaceReal.c1Representative_ae_eq`). Two
continuous functions that agree almost everywhere are equal, so these functions do not depend on
`k`, and one of them is `C^r` for every `r`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter FourierTransform BesselPotentialSpace SobolevSpace.GraphSpace
open TemperedDistribution
open scoped ENNReal NNReal BesselPotentialSpace Sobolev SchwartzMap ContDiff

namespace SobolevSpace.Fractional

variable {n : ℕ}

/-- **A real `L²` function with finite energy of order `k` is in the real space `H^k`.** -/
theorem exists_hsSpaceReal_of_besselEnergy_lt_top {k : ℕ} (g : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (hg : IsRealL2 g) (h : besselEnergy (k : ℝ) (fun _ : Unit ↦ g) < ⊤) :
    ∃ F : HsSpaceReal n (k : ℝ), toL2Fun (Nat.cast_nonneg k) F.1 = g := by
  obtain ⟨u, hL2⟩ := exists_toL2Fun_eq_of_besselEnergy_lt_top (Nat.cast_nonneg k) g h
  have hreal : IsRealL2 (toL2Fun (Nat.cast_nonneg k) u) := by
    rw [hL2]
    exact hg
  exact ⟨HsSpaceReal.ofPhysical (Nat.cast_nonneg k) _ hreal, hL2⟩

/-- **A real `L²` function with finite Sobolev energy of every integer order has a `C^∞`
representative.** The energies are those of the complexified function. The proof takes the
continuous representative of `u` as an element of `H^k`, `k > n/2 + 1`, which does not depend on
`k`. -/
theorem exists_contDiff_ae_eq_of_forall_besselEnergy_lt_top (u : DerivLp n 2 Set.univ)
    (h : ∀ k : ℕ, besselEnergy (k : ℝ) (fun _ : Unit ↦ complexifyL2CLM n u) < ⊤) :
    ∃ v : ℝ^n → ℝ, ContDiff ℝ ∞ v ∧ v =ᵐ[volume] (u : ℝ^n → ℝ) := by
  choose F hF using fun k ↦ exists_hsSpaceReal_of_besselEnergy_lt_top (complexifyL2CLM n u)
    (isRealL2_complexifyL2CLM u) (h k)
  -- the orders above the threshold of the embedding
  have hthr (r : ℕ) : (n : ℝ) < 2 * (((r + n + 2 : ℕ) : ℝ) - 1) := by
    push_cast
    linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hthr' (r : ℕ) : (n : ℝ) < 2 * (((r + n + 2 : ℕ) : ℝ) - r) := by
    push_cast
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  -- each representative is `u` almost everywhere
  have hae (r : ℕ) : (F (r + n + 2)).c1Representative (hthr r) =ᵐ[volume] (u : ℝ^n → ℝ) := by
    filter_upwards [(F (r + n + 2)).c1Representative_ae_eq (hthr r) (Nat.cast_nonneg _),
      HsSpaceReal.toL2FunCLM_apply_ae (Nat.cast_nonneg _) (F (r + n + 2)),
      complexifyL2CLM_ae u] with x h1 h2 h3
    rw [h1, h2, hF, h3, Complex.ofReal_re]
  have hcont (r : ℕ) : Continuous ((F (r + n + 2)).c1Representative (hthr r)) :=
    ((F (r + n + 2)).contDiff_c1Representative (hthr r)).continuous
  refine ⟨(F (0 + n + 2)).c1Representative (hthr 0), contDiff_infty.2 fun r ↦ ?_, hae 0⟩
  have heq : (F (0 + n + 2)).c1Representative (hthr 0) =
      (F (r + n + 2)).c1Representative (hthr r) :=
    Measure.eq_of_ae_eq ((hae 0).trans (hae r).symm) (hcont 0) (hcont r)
  rw [heq]
  exact (F (r + n + 2)).contDiff_c1Representative_of_order (hthr r) (hthr' r)

end SobolevSpace.Fractional
