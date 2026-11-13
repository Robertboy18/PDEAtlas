/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
public import PDE.Spaces.Sobolev.GraphSpace.Norms
public import PDE.Elliptic.Variational.DivergenceForm

/-!
# Lower-order terms and energy estimates

We add the first- and zeroth-order terms of Evans's divergence-form operator (2) in §6.1.1 to the
operator-valued principal part of `PDE.Elliptic.Variational.DivergenceForm`. On `H^1_0(Ω)` the form
is

`B(u,v) = sum_ij <A_ij D_j u, D_i v> + sum_i <b_i D_i u, v> + <c u, v>`,

Evans's bilinear form (8) of §6.1.2 when the coefficients act by multiplication. The lower-order
coefficients are bounded operators on `L^2(Ω)`. This includes bounded pointwise multipliers, while
keeping the energy argument independent of representative-level measurability details. The load

`F(v) = <f_0,v> + sum_i <f_i,D_i v>`

is the pairing of `f_0 - div f` with `v` in problem (10) of §6.1.2, and every element of `H^{-1}`
has this form (`exists_generalizedLoad_representation`, Evans's §5.9.1, Theorem 1). Uniform
principal ellipticity and explicit operator-norm bounds on `b_i` and `c` give Gårding's inequality.
Adding the resulting mass shift makes the form coercive, so Lax-Milgram supplies the unique weak
solution.

## How it works

In step 2 of the proof of §6.2.2, Theorem 2 (Energy estimates), Evans bounds the first-order term
with Cauchy's inequality with `ε`, which gives `θ/2 ∫|Du|² ≤ B[u,u] + C ∫u²`, and then uses
Poincaré's inequality to reach the `H¹₀` norm. We make the constant explicit: the same inequality,
with `ε` chosen from `alpha` and `beta`, gives the mass constant `gardingMass alpha beta gamma`,
equal to `n * beta ^ 2 / (2 * alpha) + gamma` (`lowerOrderForm_self_lower_bound`,
`fullDivergenceForm_garding`). Instead of Poincaré's inequality, `coerciveShift` adds the further
mass `alpha / 2`, so that the shifted form controls `alpha / 2` times the squared `H¹` norm
(`shiftedDivergenceForm_isCoercive`). This needs no boundedness of `Ω`. Every larger shift has the
same constant (`shiftedDivergenceForm_isCoercive_of_coerciveShift_le`), which is the uniformity in
`μ ≥ γ` of Evans's §6.2.2, Theorem 3.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.1, Theorem 1 (Characterization of H⁻¹), pp. 299-300;
  §6.1.1, (2), p. 312; §6.1.2, (8), (10) and the definition of a weak solution of (10), pp. 314-315;
  §6.2.2, Theorem 2 (Energy estimates), Theorem 3 (First Existence Theorem for weak solutions) and
  their proofs, pp. 318-319.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Sobolev

@[expose] public section

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open scoped Topology NNReal InnerProductSpace

namespace GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}


section Forms

local notation "L2" => DerivLp n 2 Ω
local notation "Ambient" => WkpAmbientOn n 1 2 Ω

/-- The bilinear lower-order expression, as a bilinear map, for abstract derivative and
base coordinate maps `D` and `P`. -/
def lowerOrderFormLinOf
    (V : Type*) [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
    (D : Fin n → V →L[ℝ] L2) (P : V →L[ℝ] L2)
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (c : L2 →L[ℝ] L2) :
    V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun u v ↦
      (∑ i : Fin n,
        inner ℝ (b i (D i u)) (P v)) + inner ℝ (c (P u)) (P v))
    (by
      intro u1 u2 v
      classical
      simp [Finset.sum_add_distrib, inner_add_left]
      ring)
    (by
      intro r u v
      classical
      simp only [map_smul, real_inner_smul_left]
      rw [← Finset.mul_sum]
      ring)
    (by
      intro u v1 v2
      classical
      simp [Finset.sum_add_distrib, inner_add_right]
      ring)
    (by
      intro r u v
      classical
      simp only [map_smul, real_inner_smul_right]
      rw [← Finset.mul_sum]
      ring)

/-- The lower-order form uses only the base-coordinate norm of its test argument.
For Sobolev coordinates this is the `H¹₀ × L²` estimate needed in wave energy
estimates; the coefficients may be arbitrary bounded operators on `L²`. -/
theorem norm_lowerOrderFormLinOf_apply_le_base
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (D : Fin n → V →L[ℝ] L2) (hD : ∀ i u, ‖D i u‖ ≤ ‖u‖)
    (P : V →L[ℝ] L2) (hP : ∀ u, ‖P u‖ ≤ ‖u‖)
    (b : Fin n → DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)
    (c : DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω) (u v : V) :
    ‖lowerOrderFormLinOf V D P b c u v‖ ≤
      ((∑ i : Fin n, ‖b i‖) + ‖c‖) * ‖u‖ * ‖P v‖ := by
  classical
  have hb (i : Fin n) :
      ‖inner ℝ (b i (D i u)) (P v)‖ ≤ ‖b i‖ * ‖u‖ * ‖P v‖ := by
    calc
      _ ≤ ‖b i (D i u)‖ * ‖P v‖ := norm_inner_le_norm _ _
      _ ≤ (‖b i‖ * ‖D i u‖) * ‖P v‖ :=
        mul_le_mul_of_nonneg_right ((b i).le_opNorm _) (norm_nonneg _)
      _ ≤ ‖b i‖ * ‖u‖ * ‖P v‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hD i u) (norm_nonneg _)) (norm_nonneg _)
  have hc :
      ‖inner ℝ (c (P u)) (P v)‖ ≤ ‖c‖ * ‖u‖ * ‖P v‖ := by
    calc
      _ ≤ ‖c (P u)‖ * ‖P v‖ := norm_inner_le_norm _ _
      _ ≤ (‖c‖ * ‖P u‖) * ‖P v‖ :=
        mul_le_mul_of_nonneg_right (c.le_opNorm _) (norm_nonneg _)
      _ ≤ ‖c‖ * ‖u‖ * ‖P v‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hP u) (norm_nonneg _)) (norm_nonneg _)
  change ‖(∑ i : Fin n, inner ℝ (b i (D i u)) (P v)) +
    inner ℝ (c (P u)) (P v)‖ ≤ _
  calc
    _ ≤ (∑ i : Fin n, ‖inner ℝ (b i (D i u)) (P v)‖) +
        ‖inner ℝ (c (P u)) (P v)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) le_rfl)
    _ ≤ (∑ i : Fin n, ‖b i‖ * ‖u‖ * ‖P v‖) +
        ‖c‖ * ‖u‖ * ‖P v‖ :=
      add_le_add (Finset.sum_le_sum fun i _ ↦ hb i) hc
    _ = ((∑ i : Fin n, ‖b i‖) + ‖c‖) * ‖u‖ * ‖P v‖ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring

/-- The lower-order bilinear form as a continuous bilinear map, given norm bounds on the
coordinate maps `D` and `P`. -/
def lowerOrderFormOf
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (D : Fin n → V →L[ℝ] L2) (hD : ∀ i u, ‖D i u‖ ≤ ‖u‖)
    (P : V →L[ℝ] L2) (hP : ∀ u, ‖P u‖ ≤ ‖u‖)
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (c : L2 →L[ℝ] L2) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  (lowerOrderFormLinOf (n := n) (Ω := Ω) V D P b c).mkContinuous₂
    ((∑ i : Fin n, ‖b i‖) + ‖c‖) <| by
      intro u v
      exact (norm_lowerOrderFormLinOf_apply_le_base V D hD P hP b c u v).trans
        (mul_le_mul_of_nonneg_left (hP v) (by positivity))


/-- The continuous first- and zeroth-order part of the divergence-form bilinear form. -/
def lowerOrderForm
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (c : L2 →L[ℝ] L2) :
    H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
  lowerOrderFormOf (n := n) (Ω := Ω) H¹₀(Ω)
    (fun i ↦ derivCoordCLM (n := n) (Ω := Ω) i)
    (derivCoordCLM_norm_le (n := n) (Ω := Ω))
    (baseCoordCLM (n := n) (Ω := Ω))
    (baseCoordCLM_norm_le (n := n) (Ω := Ω)) b c

/-- Unfolding the lower-order form: `∑ᵢ ⟪bᵢ ∂ᵢu, v⟫_{L²} + ⟪c u, v⟫_{L²}`, with `u` and `v`
read through the derivative and base `L²` coordinates of `H¹₀(Ω)`. -/
@[simp]
theorem lowerOrderForm_apply
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (c : L2 →L[ℝ] L2)
    (u v : H¹₀(Ω)) :
    lowerOrderForm (n := n) (Ω := Ω) b c u v =
      (∑ i : Fin n,
        inner ℝ (b i (derivCoordCLM (n := n) (Ω := Ω) i u))
          (baseCoordCLM (n := n) (Ω := Ω) v)) +
      inner ℝ (c (baseCoordCLM (n := n) (Ω := Ω) u))
        (baseCoordCLM (n := n) (Ω := Ω) v) := by
  rfl

/-- The full bounded divergence-form bilinear form, including lower-order terms: Evans's
(8) in §6.1.2 with operator coefficients. -/
def fullDivergenceForm
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (c : L2 →L[ℝ] L2) :
    H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
  let principal : H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
    variableCoeffForm (n := n) (Ω := Ω) A
  let lower : H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
    lowerOrderForm (n := n) (Ω := Ω) b c
  principal + lower

/-- The full form is the principal part plus the lower-order terms:
`B(u,v) = ∑ᵢⱼ ⟪Aᵢⱼ ∂ⱼu, ∂ᵢv⟫ + ∑ᵢ ⟪bᵢ ∂ᵢu, v⟫ + ⟪c u, v⟫`, the weak form of
`-∂ᵢ(aᵢⱼ ∂ⱼu) + bᵢ ∂ᵢu + c u`. -/
@[simp]
theorem fullDivergenceForm_apply
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (c : L2 →L[ℝ] L2)
    (u v : H¹₀(Ω)) :
    fullDivergenceForm (n := n) (Ω := Ω) A b c u v =
      (∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (A i j (derivCoordCLM (n := n) (Ω := Ω) j u))
          (derivCoordCLM (n := n) (Ω := Ω) i v)) +
      (∑ i : Fin n,
        inner ℝ (b i (derivCoordCLM (n := n) (Ω := Ω) i u))
        (baseCoordCLM (n := n) (Ω := Ω) v)) +
      inner ℝ (c (baseCoordCLM (n := n) (Ω := Ω) u))
        (baseCoordCLM (n := n) (Ω := Ω) v) := by
  simp [fullDivergenceForm, add_assoc]

/-- The mass-shifted form `B_μ[u,v] = B[u,v] + μ (u,v)` to which Lax-Milgram is applied in
Evans's §6.2.2, Theorem 3. -/
def shiftedDivergenceForm
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (c : L2 →L[ℝ] L2)
    (lambda : ℝ) : H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
  fullDivergenceForm (n := n) (Ω := Ω) A b
    (c + lambda • ContinuousLinearMap.id ℝ L2)

/-- Replacing `c` by `c + lambda • id` adds the mass term `lambda * ⟪u, v⟫_{L²}` to the full
form. This is the form `B_μ` of `L_μ = L + μ` in the proof of Evans's §6.2.2, Theorem 3. -/
@[simp]
theorem shiftedDivergenceForm_apply
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (c : L2 →L[ℝ] L2)
    (lambda : ℝ) (u v : H¹₀(Ω)) :
    shiftedDivergenceForm (n := n) (Ω := Ω) A b c lambda u v =
      fullDivergenceForm (n := n) (Ω := Ω) A b c u v +
        lambda * inner ℝ (baseCoordCLM (n := n) (Ω := Ω) u)
          (baseCoordCLM (n := n) (Ω := Ω) v) := by
  rw [shiftedDivergenceForm, fullDivergenceForm_apply, fullDivergenceForm_apply]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left]
  ring

end Forms

section Load

local notation "L2" => DerivLp n 2 Ω
local notation "Ambient" => WkpAmbientOn n 1 2 Ω

/-- The `H^{-1}`-style load represented by `f_0 - div (f_i)`. -/
def generalizedLoad (f0 : L2) (f : Fin n → L2) : StrongDual ℝ H¹₀(Ω) :=
  loadFunctional (n := n) (Ω := Ω) f0 +
    ∑ i : Fin n, (innerSL ℝ (f i)).comp
      (derivCoordCLM (n := n) (Ω := Ω) i)

/-- Evaluating the generalized load: `F(v) = ⟪f₀, v⟫_{L²} + ∑ᵢ ⟪fᵢ, ∂ᵢv⟫_{L²}`, the pairing of
the distribution `f₀ - ∑ᵢ ∂ᵢfᵢ` against `v`. -/
@[simp]
theorem generalizedLoad_apply (f0 : L2) (f : Fin n → L2) (v : H¹₀(Ω)) :
    generalizedLoad (n := n) (Ω := Ω) f0 f v =
      inner ℝ f0 (baseCoordCLM (n := n) (Ω := Ω) v) +
        ∑ i : Fin n,
          inner ℝ (f i) (derivCoordCLM (n := n) (Ω := Ω) i v) := by
  simp [generalizedLoad, loadFunctional_apply]

/-- The generalized load of zero data is the zero functional. -/
@[simp]
theorem generalizedLoad_zero :
    generalizedLoad (n := n) (Ω := Ω) (0 : L2) (0 : Fin n → L2) = 0 := by
  ext v
  simp [generalizedLoad]

/-- Pointwise continuity of the generalized load. -/
theorem norm_generalizedLoad_apply_le (f0 : L2) (f : Fin n → L2) (v : H¹₀(Ω)) :
    ‖generalizedLoad (n := n) (Ω := Ω) f0 f v‖ ≤
      (‖f0‖ + ∑ i : Fin n, ‖f i‖) * ‖v‖ := by
  classical
  rw [generalizedLoad_apply]
  calc
    ‖inner ℝ f0 (baseCoordCLM (n := n) (Ω := Ω) v) +
        ∑ i : Fin n,
          inner ℝ (f i) (derivCoordCLM (n := n) (Ω := Ω) i v)‖
        ≤ ‖inner ℝ f0 (baseCoordCLM (n := n) (Ω := Ω) v)‖ +
          ∑ i : Fin n,
            ‖inner ℝ (f i) (derivCoordCLM (n := n) (Ω := Ω) i v)‖ := by
              exact (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ ‖f0‖ * ‖v‖ + ∑ i : Fin n, ‖f i‖ * ‖v‖ := by
      apply add_le_add
      · calc
          ‖inner ℝ f0 (baseCoordCLM (n := n) (Ω := Ω) v)‖
              ≤ ‖f0‖ * ‖baseCoordCLM (n := n) (Ω := Ω) v‖ := by
                simpa [Real.norm_eq_abs] using abs_real_inner_le_norm f0
                  (baseCoordCLM (n := n) (Ω := Ω) v)
          _ ≤ ‖f0‖ * ‖v‖ := mul_le_mul_of_nonneg_left
                (baseCoordCLM_norm_le (n := n) (Ω := Ω) v) (norm_nonneg f0)
      · exact Finset.sum_le_sum fun i _ ↦ by
          calc
            ‖inner ℝ (f i) (derivCoordCLM (n := n) (Ω := Ω) i v)‖
                ≤ ‖f i‖ * ‖derivCoordCLM (n := n) (Ω := Ω) i v‖ := by
                  simpa [Real.norm_eq_abs] using abs_real_inner_le_norm (f i)
                    (derivCoordCLM (n := n) (Ω := Ω) i v)
            _ ≤ ‖f i‖ * ‖v‖ := mul_le_mul_of_nonneg_left
                  (derivCoordCLM_norm_le (n := n) (Ω := Ω) i v)
                  (norm_nonneg (f i))
    _ = (‖f0‖ + ∑ i : Fin n, ‖f i‖) * ‖v‖ := by
      rw [← Finset.sum_mul]
      ring

/-- Operator-norm continuity of the generalized load. -/
theorem norm_generalizedLoad_le (f0 : L2) (f : Fin n → L2) :
    ‖generalizedLoad (n := n) (Ω := Ω) f0 f‖ ≤
      ‖f0‖ + ∑ i : Fin n, ‖f i‖ := by
  exact (generalizedLoad (n := n) (Ω := Ω) f0 f).opNorm_le_bound
    (add_nonneg (norm_nonneg f0) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))
    (norm_generalizedLoad_apply_le (n := n) (Ω := Ω) f0 f)

/-- Every functional in `H⁻¹(Ω) = (H¹₀(Ω))*` has the `f⁰ - div f`
representation of Evans's §5.9.1, Theorem 1(i).

The proof first extends `ell` isometrically to the ambient base-gradient
product and takes its Riesz representative `w = (w₀, w₁, ..., wₙ)`. It then
sets `f⁰ = w₀` and `fⁱ = wᵢ`. These are independent coordinates of the
ambient representative; no assertion is made that `fⁱ` is a weak derivative
of `f⁰`. The resulting generalized load equals `ell`, and the coordinate
squares add up exactly to the squared dual norm. -/
theorem exists_generalizedLoad_representation
    (ell : StrongDual ℝ H¹₀(Ω)) :
    ∃ (f0 : L2) (f : Fin n → L2),
      generalizedLoad (n := n) (Ω := Ω) f0 f = ell ∧
      ‖f0‖ ^ 2 + ∑ i : Fin n, ‖f i‖ ^ 2 = ‖ell‖ ^ 2 := by
  classical
  obtain ⟨ellH1, hellH1, hnormH1⟩ :=
    exists_extension_norm_eq
      (h10Submodule (n := n) (Ω := Ω)) ell
  obtain ⟨ellAmbient, hellAmbient, hnormAmbient⟩ :=
    exists_extension_norm_eq
      (wkpSubmoduleOn
        (n := n) (k := 1) (p := (2 : ℝ≥0∞)) (Ω := Ω)) ellH1
  let w : Ambient :=
    (InnerProductSpace.toDual ℝ Ambient).symm ellAmbient
  let f0 : L2 := w (baseIndex n 1)
  let f : Fin n → L2 :=
    fun i ↦ w (singleDerivIndex (n := n) i)
  refine ⟨f0, f, ?_, ?_⟩
  · ext v
    rw [generalizedLoad_apply]
    let vAmbient : Ambient := ((h10SubtypeL (n := n) (Ω := Ω) v : H¹(Ω)) : Ambient)
    change inner ℝ (w (baseIndex n 1)) (vAmbient (baseIndex n 1)) +
        ∑ i : Fin n, inner ℝ (w (singleDerivIndex (n := n) i))
          (vAmbient (singleDerivIndex (n := n) i)) = ell v
    calc
      _ = inner ℝ w vAmbient := (ambient_inner_eq_base_add_sum_deriv (n := n) (Ω := Ω) w _).symm
      _ = ellAmbient vAmbient := by simp [w]
      _ = ellH1 (h10SubtypeL (n := n) (Ω := Ω) v) := by
        simpa [vAmbient] using hellAmbient (h10SubtypeL (n := n) (Ω := Ω) v)
      _ = ell v := hellH1 v
  · change ‖w (baseIndex n 1)‖ ^ 2 + ∑ i : Fin n, ‖w (singleDerivIndex (n := n) i)‖ ^ 2 =
        ‖ell‖ ^ 2
    rw [← ambient_norm_sq_eq_base_sq_add_sum_deriv_sq (n := n) (Ω := Ω) w]
    exact congrArg (· ^ 2) (((InnerProductSpace.toDual ℝ Ambient).symm.norm_map ellAmbient).trans
      (hnormAmbient.trans hnormH1))

end Load

section Garding

local notation "L2" => DerivLp n 2 Ω

/-- Explicit uniform bounds used to control the lower-order terms. -/
def LowerOrderBounds
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (c : L2 →L[ℝ] L2)
    (beta gamma : ℝ) : Prop :=
  0 ≤ beta ∧ 0 ≤ gamma ∧ (∀ i, ‖b i‖ ≤ beta) ∧ ‖c‖ ≤ gamma

/-- The mass constant lost in Gårding's inequality. -/
def gardingMass (alpha beta gamma : ℝ) : ℝ :=
  (n : ℝ) * beta ^ 2 / (2 * alpha) + gamma

/-- A canonical shift which leaves coercivity constant `alpha / 2`. -/
def coerciveShift (alpha beta gamma : ℝ) : ℝ :=
  gardingMass (n := n) alpha beta gamma + alpha / 2

private theorem young_product_le {alpha beta x y : ℝ}
    (halpha : 0 < alpha) :
    beta * x * y ≤ alpha / 2 * x ^ 2 + beta ^ 2 / (2 * alpha) * y ^ 2 := by
  rw [← sub_nonneg, show alpha / 2 * x ^ 2 + beta ^ 2 / (2 * alpha) * y ^ 2 - beta * x * y =
    (alpha * x - beta * y) ^ 2 / (2 * alpha) by field_simp; ring]
  positivity

/-- Lower-order terms are relatively bounded by half the principal energy plus a mass term. -/
theorem lowerOrderForm_self_lower_bound
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (c : L2 →L[ℝ] L2)
    {alpha beta gamma : ℝ} (halpha : 0 < alpha)
    (hbc : LowerOrderBounds (n := n) (Ω := Ω) b c beta gamma)
    (u : H¹₀(Ω)) :
    -(alpha / 2 * dirichletForm (n := n) (Ω := Ω) u u +
        gardingMass (n := n) alpha beta gamma *
          ‖baseCoordCLM (n := n) (Ω := Ω) u‖ ^ 2) ≤
      lowerOrderForm (n := n) (Ω := Ω) b c u u := by
  rcases hbc with ⟨hbeta, hgamma, hb, hc⟩
  set y := ‖baseCoordCLM (n := n) (Ω := Ω) u‖
  have hbyoung (i : Fin n) :
      -(alpha / 2 * ‖derivCoordCLM (n := n) (Ω := Ω) i u‖ ^ 2 + beta ^ 2 / (2 * alpha) * y ^ 2) ≤
        inner ℝ (b i (derivCoordCLM (n := n) (Ω := Ω) i u)) (baseCoordCLM (n := n) (Ω := Ω) u) := by
    refine (neg_le_neg (young_product_le halpha)).trans (neg_le_of_abs_le ?_)
    calc _ ≤ ‖b i (derivCoordCLM (n := n) (Ω := Ω) i u)‖ * y := abs_real_inner_le_norm _ _
      _ ≤ beta * ‖derivCoordCLM (n := n) (Ω := Ω) i u‖ * y := by
        gcongr
        exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hb i)
  have hcinner : -(gamma * y ^ 2) ≤
      inner ℝ (c (baseCoordCLM (n := n) (Ω := Ω) u)) (baseCoordCLM (n := n) (Ω := Ω) u) := by
    refine neg_le_of_abs_le ((abs_real_inner_le_norm _ _).trans ?_)
    calc _ ≤ ‖c‖ * y * y := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ gamma * y ^ 2 := by rw [mul_assoc, ← sq]; gcongr
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hbyoung i
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  rw [lowerOrderForm_apply, dirichletForm_self_eq_sum_norm_sq, gardingMass]
  linarith [show ((n : ℝ) * beta ^ 2 / (2 * alpha) + gamma) * y ^ 2 =
    n * (beta ^ 2 / (2 * alpha) * y ^ 2) + gamma * y ^ 2 by ring]

/-- Gårding's inequality for the full divergence-form bilinear form. This is the estimate
`θ/2 ∫|Du|² ≤ B[u,u] + C ∫u²` of step 2 of the proof of Evans's §6.2.2, Theorem 2
(Energy estimates), before Poincaré's inequality is applied. -/
theorem fullDivergenceForm_garding
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (c : L2 →L[ℝ] L2)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hbc : LowerOrderBounds (n := n) (Ω := Ω) b c beta gamma)
    (u : H¹₀(Ω)) :
    alpha / 2 * dirichletForm (n := n) (Ω := Ω) u u ≤
      fullDivergenceForm (n := n) (Ω := Ω) A b c u u +
        gardingMass (n := n) alpha beta gamma *
          ‖baseCoordCLM (n := n) (Ω := Ω) u‖ ^ 2 := by
  have hlower := lowerOrderForm_self_lower_bound
    (n := n) (Ω := Ω) b c hA.1 hbc u
  have hprincipal := hA.2 u
  rw [fullDivergenceForm_apply]
  rw [variableCoeffForm_apply] at hprincipal
  rw [lowerOrderForm_apply] at hlower
  linarith

/-- Explicit lower bound for the canonically shifted form. -/
theorem shiftedDivergenceForm_coercive_bound
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (c : L2 →L[ℝ] L2)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hbc : LowerOrderBounds (n := n) (Ω := Ω) b c beta gamma)
    (u : H¹₀(Ω)) :
    alpha / 2 * ‖u‖ * ‖u‖ ≤
      shiftedDivergenceForm (n := n) (Ω := Ω) A b c
        (coerciveShift (n := n) alpha beta gamma) u u := by
  have hg := fullDivergenceForm_garding
    (n := n) (Ω := Ω) A b c hA hbc u
  have hdecomp := norm_sq_eq_base_sq_add_sum_deriv_sq
    (n := n) (Ω := Ω) u
  have hnorm : ‖u‖ * ‖u‖ =
      ‖baseCoordCLM (n := n) (Ω := Ω) u‖ ^ 2 +
        dirichletForm (n := n) (Ω := Ω) u u := by
    rw [dirichletForm_self_eq_sum_norm_sq]
    simpa only [pow_two] using hdecomp
  rw [shiftedDivergenceForm_apply, real_inner_self_eq_norm_sq]
  dsimp [coerciveShift]
  calc
    alpha / 2 * ‖u‖ * ‖u‖ = (alpha / 2) * (‖u‖ * ‖u‖) := by ring
    _ =
        alpha / 2 * (‖baseCoordCLM (n := n) (Ω := Ω) u‖ ^ 2 +
          dirichletForm (n := n) (Ω := Ω) u u) := by
      rw [hnorm]
    _ ≤ fullDivergenceForm (n := n) (Ω := Ω) A b c u u +
        (gardingMass (n := n) alpha beta gamma + alpha / 2) *
          ‖baseCoordCLM (n := n) (Ω := Ω) u‖ ^ 2 := by
      linarith

/-- Every mass shift at least as large as the canonical coercive shift has
the same `alpha / 2` coercivity lower bound. -/
theorem shiftedDivergenceForm_coercive_bound_of_coerciveShift_le
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (c : L2 →L[ℝ] L2)
    {alpha beta gamma mu : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hbc : LowerOrderBounds (n := n) (Ω := Ω) b c beta gamma)
    (hmu : coerciveShift (n := n) alpha beta gamma ≤ mu)
    (u : H¹₀(Ω)) :
    alpha / 2 * ‖u‖ * ‖u‖ ≤
      shiftedDivergenceForm (n := n) (Ω := Ω) A b c mu u u := by
  have hcanonical :=
    shiftedDivergenceForm_coercive_bound
      (n := n) (Ω := Ω) A b c hA hbc u
  have hmass :
      0 ≤ ‖baseCoordCLM (n := n) (Ω := Ω) u‖ ^ 2 :=
    sq_nonneg _
  apply hcanonical.trans
  rw [shiftedDivergenceForm_apply, shiftedDivergenceForm_apply,
    real_inner_self_eq_norm_sq]
  exact add_le_add_right (mul_le_mul_of_nonneg_right hmu hmass) _

/-- The canonical mass shift makes the full form coercive with constant `alpha / 2`. -/
theorem shiftedDivergenceForm_isCoercive
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (c : L2 →L[ℝ] L2)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hbc : LowerOrderBounds (n := n) (Ω := Ω) b c beta gamma) :
    IsCoercive
      (shiftedDivergenceForm (n := n) (Ω := Ω) A b c
        (coerciveShift (n := n) alpha beta gamma)) :=
  ⟨alpha / 2, div_pos hA.1 (by norm_num),
    shiftedDivergenceForm_coercive_bound
      (n := n) (Ω := Ω) A b c hA hbc⟩

/-- Every mass shift at or above the canonical threshold makes the full form
coercive with constant `alpha / 2`. This is the uniformity in `μ ≥ γ` of
Evans's §6.2.2, Theorem 3. -/
theorem shiftedDivergenceForm_isCoercive_of_coerciveShift_le
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (c : L2 →L[ℝ] L2)
    {alpha beta gamma mu : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hbc : LowerOrderBounds (n := n) (Ω := Ω) b c beta gamma)
    (hmu : coerciveShift (n := n) alpha beta gamma ≤ mu) :
    IsCoercive
      (shiftedDivergenceForm (n := n) (Ω := Ω) A b c mu) :=
  ⟨alpha / 2, div_pos hA.1 (by norm_num),
    shiftedDivergenceForm_coercive_bound_of_coerciveShift_le
      (n := n) (Ω := Ω) A b c hA hbc hmu⟩

end Garding

end GraphSpace

end SobolevSpace
