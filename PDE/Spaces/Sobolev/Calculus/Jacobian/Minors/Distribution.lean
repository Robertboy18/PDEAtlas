/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Jacobian.Minors.Model
public import PDE.Spaces.Sobolev.Calculus.Jacobian.Minors.Classical
public import PDE.Analysis.MeasureTheory.Lp.WeakConvergence.TestProducts
import PDE.Spaces.Sobolev.Approximation.Density.OpenDomain
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Distribution identities for Sobolev minors

The tested minor of degree `m + 1` is a sum of fluxes involving one value and
minors of degree `m`. We first prove the identity for smooth representatives
using Piola cancellation, then pass to arbitrary graphs by
Meyers–Serrin approximation and strong continuity of the minors.

The domain is merely open. The exponent hypotheses express exactly the Hölder
pairing used by the formula; there is no boundary or divergence premise.

`testFunctionPairing_wkpJacobianMinorLp` is the Sobolev form (48) of identity (47) in the proof of
Evans's lemma on weak continuity of determinants (§8.2.4(b)), for a minor of degree `m + 1` and
`p ≥ m + 1`. Evans passes from (47) to (48) by an approximation argument that he does not write out;
our approximation is `Approximation.OpenDomain.dense_smooth` (Meyers–Serrin). With the signs
`(-1)^j`, the lower minors are the cofactors of the first row.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.4(b), proof of the Lemma (Weak continuity of
  determinants), steps 2-3, (47)-(48), p. 477.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set TopologicalSpace PDE.Analysis
open scoped ENNReal Topology Distributions Matrix.Norms.Elementwise Sobolev

namespace SobolevSpace.GraphSpace

variable {m n : ℕ} {Ω : Opens (ℝ^n)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (1 ≤ p / ENNReal.ofReal (m : ℝ))]
    [Fact (1 ≤ p / ENNReal.ofReal ((m + 1 : ℕ) : ℝ))]
    [ENNReal.HolderTriple p (p / ENNReal.ofReal (m : ℝ))
      (p / ENNReal.ofReal ((m + 1 : ℕ) : ℝ))]

local notation "μΩ" => domainMeasure n Ω
local notation "ρ" => p / ENNReal.ofReal ((m + 1 : ℕ) : ℝ)

/-- Integration by parts for a minor of degree `m + 1 ≥ 2`: for `0 < m`, `p ≠ ∞` with
`p ≥ m + 1` (the exponent instances of the section), `U : Fin (m + 1) → W^{1,p}(Ω)` and a test
function `φ`, the pairing of `φ` with the minor `M_σ(U)` is
`-∑_j (-1)^j ∫ (∂_{σ j} φ) U_0 M_{σ ∘ j.succAbove}(U ∘ Fin.succ) dx`. The `j`th lower minor deletes
the first row and the column `j`. -/
theorem testFunctionPairing_wkpJacobianMinorLp
    (hm : 0 < m) (hp : p ≠ ∞) (σ : Fin (m + 1) → Fin n)
    (U : Fin (m + 1) → W^{1,p}(Ω)) (φ : 𝓓(Ω, ℝ)) :
    Lp.testFunctionPairing Ω φ (wkpJacobianMinorLp σ U) =
      -∑ j : Fin (m + 1), (-1 : ℝ) ^ (j : ℕ) *
        Lp.testProductPairing Ω (r := ρ)
          (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single (σ j) (1 : ℝ)) φ)
          (wkpBaseCoordinateCLM (U 0))
          (wkpJacobianMinorLp (σ ∘ j.succAbove) (U ∘ Fin.succ)) := by
  let ψ (j : Fin (m + 1)) : 𝓓(Ω, ℝ) :=
    _root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single (σ j) (1 : ℝ)) φ
  let L (V : Fin (m + 1) → W^{1,p}(Ω)) : ℝ :=
    Lp.testFunctionPairing Ω φ (wkpJacobianMinorLp σ V)
  let R (V : Fin (m + 1) → W^{1,p}(Ω)) : ℝ :=
    -∑ j : Fin (m + 1), (-1 : ℝ) ^ (j : ℕ) *
      Lp.testProductPairing Ω (r := ρ) (ψ j)
        (wkpBaseCoordinateCLM (V 0))
        (wkpJacobianMinorLp (σ ∘ j.succAbove) (V ∘ Fin.succ))
  have hL : Continuous L :=
    (Lp.testFunctionPairing Ω φ).continuous.comp
      (continuous_wkpJacobianMinorLp (Nat.succ_pos m) hp σ)
  have hR : Continuous R := (continuous_finsetSum _ fun j _ ↦ continuous_const.mul
    (((Lp.testProductPairing Ω (r := ρ) (ψ j)).continuous.comp
      (wkpBaseCoordinateCLM.continuous.comp (continuous_apply 0))).clm_apply
      ((continuous_wkpJacobianMinorLp hm hp (σ ∘ j.succAbove)).comp
        (continuous_pi fun i ↦ continuous_apply i.succ)))).neg
  have hd (i : Fin (m + 1)) :=
    mem_closure_iff_seq_limit.mp
      (Approximation.OpenDomain.dense_smooth (n := n) (k := 1) Ω.isOpen hp (U i))
  choose V hV hlim using hd
  have hseq : Tendsto (fun k i ↦ V i k) atTop (𝓝 U) :=
    tendsto_pi_nhds.mpr hlim
  change L U = R U
  refine (isClosed_eq hL hR).mem_of_tendsto hseq (.of_forall fun a ↦ ?_)
  change L (fun i ↦ V i a) = R (fun i ↦ V i a)
  choose f hf hbase using fun i ↦ hV i a
  let g : ℝ^n → ℝ^(m + 1) := fun x ↦ WithLp.toLp 2 (fun i ↦ f i x)
  have hg : ContDiffOn ℝ 2 g Ω :=
    (contDiffOn_piLp 2).mpr fun i ↦ (hf i).of_le (by simp)
  have hcoords : ∀ᵐ x ∂μΩ, ∀ i j,
      wkpCoordinateCLM (singleDerivIndex n (σ j)) (V i a) x =
        (∂[σ j] (fun y ↦ g y i)) x :=
    ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦
      wkpCoordinate_ae_eq_partialDeriv_of_contDiffOn Ω.isOpen (V i a)
        ((hf i).of_le (by simp)) (hbase i) (σ j)
  have hminor := wkpJacobianMinorLp_ae_eq_of_contDiffOn Ω.isOpen σ (fun i ↦ V i a)
    (hg.of_le (by norm_num)) hbase
  have hlower (j : Fin (m + 1)) :
      wkpJacobianMinorLp (σ ∘ j.succAbove) ((fun i ↦ V i a) ∘ Fin.succ) =ᵐ[μΩ]
        fun x ↦ (((jacobianMatrix g x).submatrix id σ).submatrix
          Fin.succ j.succAbove).det := by
    filter_upwards [coeFn_wkpJacobianMinorLp (σ ∘ j.succAbove)
      ((fun i ↦ V i a) ∘ Fin.succ), hcoords] with x hx hd
    rw [hx]
    exact congrArg Matrix.det (Matrix.ext fun i b ↦ hd i.succ (j.succAbove b))
  let Φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport, subset_univ _⟩
  have hΦ : tsupport Φ.toFun ⊆ (Ω : Set (ℝ^n)) := φ.tsupport_subset
  have hclass :=
    integral_det_jacobianMatrix_submatrix_mul_test Ω.isOpen hg σ 0 Φ hΦ
  have hleft : L (fun i ↦ V i a) =
      ∫ x, ((jacobianMatrix g x).submatrix id σ).det * Φ x ∂μΩ := by
    dsimp only [L]
    rw [Lp.testFunctionPairing_apply]
    exact integral_congr_ae (hminor.mono fun x hx ↦ by dsimp only; rw [hx]; rfl)
  have hflux (j : Fin (m + 1)) :
      (-1 : ℝ) ^ (j : ℕ) *
          Lp.testProductPairing Ω (r := ρ) (ψ j) (wkpBaseCoordinateCLM (V 0 a))
            (wkpJacobianMinorLp (σ ∘ j.succAbove) ((fun i ↦ V i a) ∘ Fin.succ)) =
        ∫ x, g x 0 * ((jacobianMatrix g x).submatrix id σ).adjugate j 0 *
          (∂[σ j] Φ.toFun) x ∂μΩ := by
    rw [Lp.testProductPairing_apply, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hbase 0, hlower j] with x hb hl
    change (-1 : ℝ) ^ (j : ℕ) *
      (baseRepresentative (V 0 a) x * _ * ψ j x) = _
    rw [hb, hl, Matrix.adjugate_fin_succ_eq_det_submatrix]
    simp only [Fin.val_zero, zero_add, Fin.succAbove_zero]
    have hψ : ψ j x = (∂[σ j] Φ.toFun) x := by
      rw [testFunction_lineDerivCLM_apply]
      rfl
    rw [hψ]
    change _ = f 0 x * _ * _
    ring
  rw [hleft, hclass]
  exact congrArg Neg.neg (Finset.sum_congr rfl fun j _ ↦ (hflux j).symm)

end SobolevSpace.GraphSpace
