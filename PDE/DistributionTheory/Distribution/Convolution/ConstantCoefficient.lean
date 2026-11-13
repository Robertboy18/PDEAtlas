/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.Distribution.Operator.FundamentalSolution
public import PDE.DistributionTheory.Distribution.Support.ConstantCoefficient
public import PDE.DistributionTheory.Distribution.Convolution
import PDE.DistributionTheory.Distribution.Convolution.Derivative

/-!
# Constant-coefficient operators and compact-carrier convolution

A constant-coefficient differential operator `P(∂) = ∑ᵢ aᵢ ∂_{m_{i,1}} ⋯ ∂_{m_{i,order i}}`,
written here as `PDE.Analysis.constantCoeffLineDerivCLM a order m`, is a finite linear
combination of iterated directional derivatives. Since a single directional derivative
commutes with the convolution of compactly carried distributions in either factor
(`PDE.DistributionTheory.Distribution.Convolution.Derivative`), so does every such operator:

`P(∂)(S * T) = (P(∂) S) * T = S * (P(∂) T)`.

As a consequence, if `P(∂) G = δ₀` and `G` is compactly carried, then
`P(∂)(G * T) = (P(∂) G) * T = δ₀ * T = T` for every compactly carried `T`.

For scalar distributions on the whole finite-dimensional real space, the compact-carrier
hypothesis is restrictive. Informally, complexify `G` and test against exponentials, using a
cutoff equal to one near its carrier and the origin. The equation gives
`p(ζ) G(exp(-ζ)) = 1` for every complex covector `ζ`, where
`p(ζ) = ∑ᵢ aᵢ ∏ⱼ ζ(mᵢⱼ)` is the effective scalar symbol. Thus `p` has no complex zeros.
In positive dimension, a nonconstant complex polynomial has a zero, so `p` must be a
nonzero constant. In dimension zero it is already constant, and the same equation makes it
nonzero. Consequently the effective operator is `c id` and `G = c⁻¹ δ₀`, with `c ≠ 0`.
This does not force the supplied entries of `order` to vanish: zero directions and
cancellation can eliminate positive-order summands.

The exponential argument is also the usual Fourier-Laplace argument for compactly supported
distributions in the Paley-Wiener-Schwartz theorem. In particular, operators with nonconstant
effective scalar symbols, such as the usual Laplacian, heat and wave operators, cannot have
compactly carried fundamental solutions. Neither can a single `∂ᵥ`, including `v = 0`.
Their fundamental solutions enter convolution formulas through the construction in which only
the other factor is compactly carried; see Hörmander, Chapter IV, or Friedlander and Joshi,
Chapter 5, for the argument with one compactly supported factor.

## Main results

* `iteratedLineDerivOp_convolution_left`, `iteratedLineDerivOp_convolution_right`: an iterated
  directional derivative of any finite order passes onto either factor of a convolution.
* `constantCoeffLineDerivCLM_convolution_left`, `constantCoeffLineDerivCLM_convolution_right`:
  the same for a finite constant-coefficient operator.
* `IsFundamentalSolutionAt.constantCoeff_convolution_eq`: `P(∂)(G * T) = T` when `G` is a
  compactly carried fundamental solution with pole at the origin and `T` is compactly carried.

## Implementation notes

The compact-carrier proofs for the derived factors (`hS.constantCoeffLineDerivCLM`, and so on)
are passed explicitly because `convolution` takes the carrier proofs as arguments. The
operator statements reduce to the derivative statements after fixing a common pair of cutoffs
via `convolution_eq_convolutionWithCutoff_tensorProduct`, since `convolutionWithCutoff` is
linear in each factor for a fixed cutoff.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Classics in
  Mathematics, Springer, 2003, Chapter IV, "Convolution".
  <https://doi.org/10.1007/978-3-642-61497-2_5>
* F. G. Friedlander and M. Joshi, *Introduction to the Theory of Distributions*, 2nd ed.,
  Cambridge University Press, 1998, Chapter 5, "Convolution".
-/

@[expose] public section

open Set TopologicalSpace
open scoped BigOperators Distributions

noncomputable section

namespace Distribution

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Iterated directional differentiation commutes with compact-carrier
convolution in the left factor. -/
theorem iteratedLineDerivOp_convolution_left
    {n : ℕ}
    (m : Fin n → E)
    (S T : 𝓓'((⊤ : Opens E), ℝ))
    (hS : HasCompactCarrier S)
    (hT : HasCompactCarrier T) :
    LineDeriv.iteratedLineDerivOp m (convolution S T hS hT) =
      convolution (LineDeriv.iteratedLineDerivOp m S) T
        (hS.iteratedLineDerivOp m) hT := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [LineDeriv.iteratedLineDerivOp_succ_left]
      rw [ih (Fin.tail m)]
      rw [lineDerivOp_eq_lineDerivCLM]
      rw [lineDerivCLM_convolution_left]
      simp only [LineDeriv.iteratedLineDerivOp_succ_left,
        lineDerivOp_eq_lineDerivCLM]

/-- Iterated directional differentiation commutes with compact-carrier
convolution in the right factor. -/
theorem iteratedLineDerivOp_convolution_right
    {n : ℕ}
    (m : Fin n → E)
    (S T : 𝓓'((⊤ : Opens E), ℝ))
    (hS : HasCompactCarrier S)
    (hT : HasCompactCarrier T) :
    LineDeriv.iteratedLineDerivOp m (convolution S T hS hT) =
      convolution S (LineDeriv.iteratedLineDerivOp m T)
        hS (hT.iteratedLineDerivOp m) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [LineDeriv.iteratedLineDerivOp_succ_left]
      rw [ih (Fin.tail m)]
      rw [lineDerivOp_eq_lineDerivCLM]
      rw [lineDerivCLM_convolution_right]
      simp only [LineDeriv.iteratedLineDerivOp_succ_left,
        lineDerivOp_eq_lineDerivCLM]

private theorem convolutionWithCutoff_sum_smul_left
    {N : ℕ}
    (a : Fin N → ℝ)
    (U : Fin N → 𝓓'((⊤ : Opens E), ℝ))
    (T : 𝓓'((⊤ : Opens E), ℝ))
    (χ : 𝓓((⊤ : Opens (E × E)), ℝ)) :
    convolutionWithCutoff (∑ i, a i • U i) T χ =
      ∑ i, a i • convolutionWithCutoff (U i) T χ := by
  simp [convolutionWithCutoff, tensorProduct]

private theorem tensorProduct_sum_smul_right
    {N : ℕ}
    (a : Fin N → ℝ)
    (S : 𝓓'((⊤ : Opens E), ℝ))
    (U : Fin N → 𝓓'((⊤ : Opens E), ℝ)) :
    tensorProduct S (∑ i, a i • U i) =
      ∑ i, a i • tensorProduct S (U i) := by
  ext Φ
  rw [tensorProduct_apply]
  have hfamily :
      TestFunction.applyDistributionToSliceRight (∑ i, a i • U i) Φ =
        ∑ i, a i • TestFunction.applyDistributionToSliceRight (U i) Φ := by
    ext x
    simp
  rw [hfamily, map_sum]
  simp [tensorProduct_apply]

private theorem convolutionWithCutoff_sum_smul_right
    {N : ℕ}
    (a : Fin N → ℝ)
    (S : 𝓓'((⊤ : Opens E), ℝ))
    (U : Fin N → 𝓓'((⊤ : Opens E), ℝ))
    (χ : 𝓓((⊤ : Opens (E × E)), ℝ)) :
    convolutionWithCutoff S (∑ i, a i • U i) χ =
      ∑ i, a i • convolutionWithCutoff S (U i) χ := by
  simp [convolutionWithCutoff, tensorProduct_sum_smul_right]

/-- A finite constant-coefficient differential operator commutes with
compact-carrier convolution in the left factor. -/
theorem constantCoeffLineDerivCLM_convolution_left
    {N : ℕ}
    (a : Fin N → ℝ)
    (order : Fin N → ℕ)
    (m : ∀ i, Fin (order i) → E)
    (S T : 𝓓'((⊤ : Opens E), ℝ))
    (hS : HasCompactCarrier S)
    (hT : HasCompactCarrier T) :
    PDE.Analysis.constantCoeffLineDerivCLM
        (X := 𝓓'((⊤ : Opens E), ℝ)) a order m
        (convolution S T hS hT) =
      convolution
        (PDE.Analysis.constantCoeffLineDerivCLM
          (X := 𝓓'((⊤ : Opens E), ℝ)) a order m S)
        T (hS.constantCoeffLineDerivCLM a order m) hT := by
  rcases hS with ⟨K, hK, hSK⟩
  rcases hT with ⟨L, hL, hTL⟩
  obtain ⟨χ, -, -, hχ, -⟩ :=
    TestFunction.exists_eq_one_on_compact_finiteDimensional
      isOpen_univ hK (subset_univ _)
  obtain ⟨ψ, -, -, hψ, -⟩ :=
    TestFunction.exists_eq_one_on_compact_finiteDimensional
      isOpen_univ hL (subset_univ _)
  let hPS : HasCompactCarrier
      (PDE.Analysis.constantCoeffLineDerivCLM
        (X := 𝓓'((⊤ : Opens E), ℝ)) a order m S) :=
    ⟨K, hK, hSK.constantCoeffLineDerivCLM a order m⟩
  rw [convolution_eq_convolutionWithCutoff_tensorProduct
    (PDE.Analysis.constantCoeffLineDerivCLM
      (X := 𝓓'((⊤ : Opens E), ℝ)) a order m S)
    T hPS ⟨L, hL, hTL⟩
    hK hL (hSK.constantCoeffLineDerivCLM a order m) hTL
    χ ψ hχ hψ]
  rw [PDE.Analysis.constantCoeffLineDerivCLM_apply]
  rw [PDE.Analysis.constantCoeffLineDerivCLM_apply]
  rw [convolutionWithCutoff_sum_smul_left]
  apply Finset.sum_congr rfl
  intro i _hi
  congr 1
  calc
    LineDeriv.iteratedLineDerivOp (m i)
        (convolution S T ⟨K, hK, hSK⟩ ⟨L, hL, hTL⟩) =
        convolution (LineDeriv.iteratedLineDerivOp (m i) S) T
          ⟨K, hK, hSK.iteratedLineDerivOp (m i)⟩
          ⟨L, hL, hTL⟩ := by
      simpa using iteratedLineDerivOp_convolution_left
        (m i) S T ⟨K, hK, hSK⟩ ⟨L, hL, hTL⟩
    _ = convolutionWithCutoff (LineDeriv.iteratedLineDerivOp (m i) S) T
          (TestFunction.tensorProduct χ ψ) := by
      exact convolution_eq_convolutionWithCutoff_tensorProduct
        (LineDeriv.iteratedLineDerivOp (m i) S) T
        ⟨K, hK, hSK.iteratedLineDerivOp (m i)⟩
        ⟨L, hL, hTL⟩
        hK hL (hSK.iteratedLineDerivOp (m i)) hTL
        χ ψ hχ hψ

/-- A finite constant-coefficient differential operator commutes with
compact-carrier convolution in the right factor. -/
theorem constantCoeffLineDerivCLM_convolution_right
    {N : ℕ}
    (a : Fin N → ℝ)
    (order : Fin N → ℕ)
    (m : ∀ i, Fin (order i) → E)
    (S T : 𝓓'((⊤ : Opens E), ℝ))
    (hS : HasCompactCarrier S)
    (hT : HasCompactCarrier T) :
    PDE.Analysis.constantCoeffLineDerivCLM
        (X := 𝓓'((⊤ : Opens E), ℝ)) a order m
        (convolution S T hS hT) =
      convolution S
        (PDE.Analysis.constantCoeffLineDerivCLM
          (X := 𝓓'((⊤ : Opens E), ℝ)) a order m T)
        hS (hT.constantCoeffLineDerivCLM a order m) := by
  rcases hS with ⟨K, hK, hSK⟩
  rcases hT with ⟨L, hL, hTL⟩
  obtain ⟨χ, -, -, hχ, -⟩ :=
    TestFunction.exists_eq_one_on_compact_finiteDimensional
      isOpen_univ hK (subset_univ _)
  obtain ⟨ψ, -, -, hψ, -⟩ :=
    TestFunction.exists_eq_one_on_compact_finiteDimensional
      isOpen_univ hL (subset_univ _)
  let hPT : HasCompactCarrier
      (PDE.Analysis.constantCoeffLineDerivCLM
        (X := 𝓓'((⊤ : Opens E), ℝ)) a order m T) :=
    ⟨L, hL, hTL.constantCoeffLineDerivCLM a order m⟩
  rw [convolution_eq_convolutionWithCutoff_tensorProduct
    S
    (PDE.Analysis.constantCoeffLineDerivCLM
      (X := 𝓓'((⊤ : Opens E), ℝ)) a order m T)
    ⟨K, hK, hSK⟩ hPT
    hK hL hSK (hTL.constantCoeffLineDerivCLM a order m)
    χ ψ hχ hψ]
  rw [PDE.Analysis.constantCoeffLineDerivCLM_apply]
  rw [PDE.Analysis.constantCoeffLineDerivCLM_apply]
  rw [convolutionWithCutoff_sum_smul_right]
  apply Finset.sum_congr rfl
  intro i _hi
  congr 1
  calc
    LineDeriv.iteratedLineDerivOp (m i)
        (convolution S T ⟨K, hK, hSK⟩ ⟨L, hL, hTL⟩) =
        convolution S (LineDeriv.iteratedLineDerivOp (m i) T)
          ⟨K, hK, hSK⟩
          ⟨L, hL, hTL.iteratedLineDerivOp (m i)⟩ := by
      simpa using iteratedLineDerivOp_convolution_right
        (m i) S T ⟨K, hK, hSK⟩ ⟨L, hL, hTL⟩
    _ = convolutionWithCutoff S (LineDeriv.iteratedLineDerivOp (m i) T)
          (TestFunction.tensorProduct χ ψ) := by
      exact convolution_eq_convolutionWithCutoff_tensorProduct
        S (LineDeriv.iteratedLineDerivOp (m i) T)
        ⟨K, hK, hSK⟩
        ⟨L, hL, hTL.iteratedLineDerivOp (m i)⟩
        hK hL hSK (hTL.iteratedLineDerivOp (m i))
        χ ψ hχ hψ

/-- If `P(∂) G = δ₀` with `G` compactly carried, then `P(∂)(G * T) = T` for every compactly
carried `T`. This proves the convolution identity under the stated hypotheses; the informal
restriction on the effective scalar symbol is discussed in the module documentation. -/
theorem IsFundamentalSolutionAt.constantCoeff_convolution_eq
    {N : ℕ}
    (a : Fin N → ℝ)
    (order : Fin N → ℕ)
    (m : ∀ i, Fin (order i) → E)
    (G T : 𝓓'((⊤ : Opens E), ℝ))
    (hG : HasCompactCarrier G)
    (hT : HasCompactCarrier T)
    (hfund : IsFundamentalSolutionAt
      (PDE.Analysis.constantCoeffLineDerivCLM
        (X := 𝓓'((⊤ : Opens E), ℝ)) a order m)
      G 0) :
    PDE.Analysis.constantCoeffLineDerivCLM
        (X := 𝓓'((⊤ : Opens E), ℝ)) a order m
        (convolution G T hG hT) =
      T := by
  rw [constantCoeffLineDerivCLM_convolution_left]
  have hfundEq :
    PDE.Analysis.constantCoeffLineDerivCLM
        (X := 𝓓'((⊤ : Opens E), ℝ)) a order m G =
      delta 0 :=
    hfund.eq
  simpa only [hfundEq] using
    convolution_delta_zero_left T hT

end Distribution
