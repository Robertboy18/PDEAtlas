/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Elliptic.ModifiedHelmholtz
import Blueprint.Commands.Figures
import PDE.Analysis.Fredholm.CompactAdjoint
import PDE.Analysis.Fredholm.Nullity
import PDE.Analysis.Fredholm.WeakForm.Alternative
import PDE.Analysis.Fredholm.WeakForm.Solvability
import PDE.Analysis.Spectral.CompactOperator
import PDE.Elliptic.Variational.FredholmAlternative
import PDE.Elliptic.Variational.WeakSpectrum
import PDE.Elliptic.Variational.ClassicalDirichletEigenfunction
import PDE.Elliptic.Variational.ClassicalDivergenceEigenfunction
import PDE.Elliptic.Variational.Eigenfunction.Full.Principal
import PDE.Elliptic.Variational.OrderedDirichletSpectrum

/-!
# Fredholm alternative and weak spectrum

The compact-operator route to Fredholm solvability and weak spectra.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
-- Verso directive attributes cannot be split across lines, while blank lines
-- delimit Markdown paragraphs and display blocks inside the enclosing command.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Fredholm Alternative and Weak Spectrum" =>

:::group "elliptic.fredholm"
Fredholm alternative and spectrum
:::

:::group "elliptic.compact_spectrum"
Spectrum of a compact operator
:::

# From a coercive shift to the Fredholm alternative

Inverting a coercive shift turns a lower-order elliptic equation into
$`(I-K)u=g` with $`K` compact, so the theory begins with compact operators on
a Hilbert space and their adjoints.

An orthonormal eigenbasis needs symmetry in addition to compactness: for a
symmetric form,
the spectral basis theorem
builds one from a compact map with dense range into the pivot space.

:::theorem "analysis.compact_adjoint" (parent := "elliptic.fredholm") (lean := "PDE.Analysis.isCompactOperator_adjoint")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "323-324"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "725-727"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%
Schauder's theorem for real or complex Hilbert spaces states

$$`
K:H_1\to H_2\ \text{compact}
\quad\Longrightarrow\quad
K^*:H_2\to H_1\ \text{compact}.
`

Here $`K^*` is Mathlib's Hilbert adjoint of the bounded linear map $`K`.
:::

:::proof "analysis.compact_adjoint"
Approximate the compact operator in operator norm by finite-rank maps.  Their
adjoints are finite-rank and hence compact; preservation of the operator norm
by the adjoint and closedness of the compact-operator class pass compactness to
the limiting adjoint.
:::

Compactness of the adjoint is what makes the Fredholm theory symmetric between
an operator and its adjoint. For a compact perturbation of the identity, both
kernels are eigenspaces at a nonzero eigenvalue of a compact operator, hence
finite-dimensional, and their dimensions agree.

:::theorem "analysis.fredholm.index_zero" (parent := "elliptic.fredholm") (lean := "PDE.Analysis.finrank_ker_eq_adjoint_ker_compact") (uses := "analysis.compact_adjoint")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "725-727"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a compact operator $`K:H\to H` on a real Hilbert space $`H`,

$$`
\dim\ker(K-I)=\dim\ker(K^*-I).
`

Both kernels are finite-dimensional eigenspaces at the nonzero eigenvalue
$`1`.  The equality is the index-zero assertion for a compact perturbation
of the identity.
:::

:::proof "analysis.fredholm.index_zero"
Put $`S=I-K`, $`N=\ker S`, and $`M=\ker S^*`. Both kernels are
finite-dimensional. If $`\dim N<\dim M`, choose an injective, nonsurjective
linear map $`A_0:N\to M`. Extend it to a finite-rank operator $`A:H\to H`
by first projecting orthogonally onto $`N`. Since
$`M=(\operatorname{range}S)^\perp`, the equation $`(S-A)x=0` forces
$`Sx=Ax=0`. Thus $`x\in N` and $`A_0x=0`, so injectivity of $`A_0` gives
$`x=0`.

The operator $`K+A` is compact, so the compact Fredholm alternative makes
$`T=I-(K+A)=S-A` surjective. Choose $`y\in M` outside the range of $`A_0`
and solve $`Tx=y`. Then $`Sx=Ax+y` lies in both $`\operatorname{range}S`
and $`M`, hence is zero. It follows that $`x\in N` and
$`y=-Ax=A_0(-x)`, contradicting the choice of $`y`. Therefore
$`\dim M\leq\dim N`. Applying the same argument to $`K^*` gives the
reverse inequality.
:::

The elliptic application is phrased in terms of bilinear forms rather than
operators. If a form $`B` becomes coercive after adding a multiple of a
compact mass form $`M`, composing $`B` on the left with the shifted inverse
gives a compact perturbation of the identity. The index-zero theorem then
transfers to the kernels of $`B` and of its adjoint form $`B^*(u,v)=B(v,u)`.

:::theorem "analysis.fredholm.weak_nullity" (parent := "elliptic.fredholm") (lean := "PDE.Analysis.finiteDimensional_ker_form, PDE.Analysis.finiteDimensional_ker_adjointForm_of_compact_mass, PDE.Analysis.finrank_ker_form_eq_ker_adjointForm_of_compact_mass") (uses := "analysis.compact_adjoint, analysis.fredholm.index_zero")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "323-324"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`B`, $`B_\gamma`, and $`M` be continuous forms on a real Hilbert space
$`V`, with

$$`
B_\gamma(u,v)=B(u,v)+\gamma M(u,v).
`

If $`B_\gamma` is coercive and $`M` is compact, then the primal and adjoint
homogeneous spaces

$$`
N=\ker B,\qquad N^*=\ker B^*
`

are finite-dimensional and have equal dimension:

$$`
\dim N=\dim N^*<\infty.
`
:::

:::proof "analysis.fredholm.weak_nullity" (uses := "analysis.compact_adjoint, analysis.fredholm.index_zero")
Compose the weak operator on the left with the shifted inverse to obtain
$`I-K`, with $`K` compact. This preserves the primal kernel. After Riesz
identification, the Hilbert-space representative of $`B` factors as
$`T=Q(I-K)` with $`Q` invertible. Then $`T^*=(I-K)^*Q^*`, so the invertible
map $`Q^*` identifies $`\ker T^*` with $`\ker((I-K)^*)`. The compact
index-zero theorem gives finiteness and equality of the two nullities.
:::

Equality of the two nullities describes the homogeneous problems. The
solvability criterion describes the range of $`B`: closedness of the range of a
compact perturbation of the identity, combined with the orthogonal
decomposition of a Hilbert space, identifies the solvable loads as those
annihilated by the adjoint kernel.

:::theorem "analysis.fredholm.adjoint_solvability" (parent := "elliptic.fredholm") (lean := "PDE.Analysis.exists_isWeakSolution_iff_forall_adjoint_homogeneous_orthogonal_of_compact_mass") (uses := "analysis.compact_adjoint, analysis.fredholm.weak_nullity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "323-324"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`B:V\times V\to\mathbb R` be a continuous weak form that becomes
coercive after adding a compact mass term, and let $`F\in V^*`. Then

$$`
\bigl[\exists u\in V,\ \forall v\in V,\ B(u,v)=F(v)\bigr]
\iff
\bigl[\forall w\in V,\
  (\forall v\in V,\ B(v,w)=0)\Rightarrow F(w)=0\bigr].
`

Thus solvability is exactly orthogonality of the load to every homogeneous
solution of the adjoint weak problem.
:::

:::proof "analysis.fredholm.adjoint_solvability" (uses := "analysis.compact_adjoint, analysis.fredholm.weak_nullity")
Composing the original weak operator on the left with the shifted inverse
gives a compact perturbation of the identity. Closed range and the Hilbert-space
range-orthogonality criterion then identify solvability with orthogonality to
the adjoint kernel.
:::

Under the same hypotheses of a coercive shift by a compact mass form, the two
preceding results combine into a dichotomy. If the adjoint kernel is
trivial every load is admissible, and then equality of nullities makes the
primal kernel trivial as well, so the solution is unique; if the primal kernel
is nontrivial, uniqueness fails outright.

:::theorem "analysis.fredholm.exact_alternative" (parent := "elliptic.fredholm") (lean := "PDE.Analysis.fredholmAlternative_weak_solution_exactlyOne") (uses := "analysis.fredholm.index_zero")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "322-324"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`V` be a real Hilbert space and let $`B` be a bounded bilinear form on
$`V`. Suppose there are a real number $`\lambda` and a bounded bilinear form
$`M` whose associated operator $`V\to V^*` is compact such that the shifted
form $`B+\lambda M` is coercive. Then exactly one of the following branches
holds:

$$`
\exists u\ne0,\ \forall v,\ B(u,v)=0,
`

or

$$`
\forall F\in V^*,\ \exists!\,u\in V,\ \forall v,\ B(u,v)=F(v).
`

The two branches are mutually exclusive.
:::

:::proof "analysis.fredholm.exact_alternative"
The zero-index theorem gives $`\dim\ker T=\dim\ker T^*`. If the kernel is
trivial, bijectivity of the continuous Fredholm map follows from surjectivity
(range is closed plus trivial cokernel). If the kernel is nontrivial,
uniqueness fails. The two cases are mutually exclusive because a nontrivial
kernel element is a nonzero homogeneous solution.
:::

The Fredholm alternative concerns a single form. Letting the mass parameter
vary produces a family, and the exceptional parameters are read as
eigenvalues of one compact operator. The properties of the weak spectrum
therefore reduce to the spectral theory of compact operators, beginning with
the behaviour of sequences of distinct eigenvalues.

:::theorem "analysis.compact_spectrum.accumulation" (parent := "elliptic.compact_spectrum") (lean := "PDE.Analysis.distinct_eigenvalues_tendsto_zero")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "727"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`K` be compact on a real Hilbert space. If $`(\lambda_j)` is an
injective sequence of nonzero real eigenvalues and
$`\lambda_j\to\lambda`, then

$$`\lambda=0.`

This is the sequential accumulation statement in Evans's compact-spectrum
theorem.
:::

:::proof "analysis.compact_spectrum.accumulation"
Choose eigenvectors for the distinct eigenvalues and form their increasing
finite-dimensional invariant spans.  Riesz's lemma supplies uniformly
separated vectors in those spans.  If the eigenvalues converged to a nonzero
limit, compactness of $`K` would give a convergent subsequence after reciprocal
rescaling, contradicting the separation estimate.
:::

The accumulation statement is sequential. Since every eigenvalue is bounded in
absolute value by the operator norm, an infinite set of eigenvalues outside
$`(-\varepsilon,\varepsilon)` would contain a convergent injective sequence
with nonzero limit, which the accumulation theorem forbids.

:::theorem "analysis.compact_spectrum.finite_away_zero" (parent := "elliptic.compact_spectrum") (lean := "PDE.Analysis.finite_eigenvalues_norm_ge") (uses := "analysis.compact_spectrum.accumulation")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "727"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For every $`\varepsilon>0`, a compact operator $`K` has only finitely many
real eigenvalues away from zero:

$$`
\left\{\lambda\in\mathbb R:
  |\lambda|\geq\varepsilon,\
  \exists v\ne0,\ Kv=\lambda v\right\}
\quad\text{is finite}.
`
:::

:::proof "analysis.compact_spectrum.finite_away_zero" (uses := "analysis.compact_spectrum.accumulation")
Every eigenvalue lies in the closed interval determined by the operator norm.
An infinite set bounded away from zero would therefore have a convergent
injective subsequence whose limit is nonzero, contradicting the preceding
accumulation theorem.
:::

Countability follows by exhausting the nonzero eigenvalues with the finite
sets $`\{|\lambda|\ge1/(k+1)\}`. Together with the accumulation theorem, this
is all that the weak-spectrum results extract from compactness.

:::theorem "analysis.compact_spectrum.countable" (parent := "elliptic.compact_spectrum") (lean := "PDE.Analysis.countable_nonzero_eigenvalues") (uses := "analysis.compact_spectrum.finite_away_zero")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "727"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a compact operator $`K`, the nonzero real point spectrum

$$`
\sigma_{\mathrm p}(K)\setminus\{0\}
=\left\{\lambda\ne0:\exists v\ne0,\ Kv=\lambda v\right\}
`

is countable.
:::

:::proof "analysis.compact_spectrum.countable" (uses := "analysis.compact_spectrum.finite_away_zero")
Write the nonzero spectrum as the countable union of the finite sets on which
the absolute value is at least $`1/(k+1)`.
:::

For the elliptic application the compact operator must be produced from the
PDE. The Gårding shift adds a multiple of the
$`L^2` mass form to the full divergence form, so the abstract hypothesis of a
compact mass form becomes a statement about the inclusion
$`H^1_0(\Omega)\hookrightarrow L^2(\Omega)`.

An example on $`(0,\pi)` shows which norm gains compactness. Set
$`v_k(x)=\sin(kx)/k` for positive integers $`k`. Then

$$`
\|v_k\|_{L^2}^2=\frac{\pi}{2k^2},
\qquad
\|v_k'\|_{L^2}^2=\frac{\pi}{2}.
`

The oscillations become finer, but a bounded gradient budget forces their
height down. These functions converge to zero in $`L^2`, while their
gradients remain separated in $`L^2`. Rellich gives convergence of the
states in the weaker norm; it does not make bounded sets compact in
$`H^1_0`. The compact mass operator uses precisely that loss of a
derivative.

:::theorem "elliptic.fredholm.compact_mass" (parent := "elliptic.fredholm") (lean := "SobolevSpace.GraphSpace.isCompactOperator_massFormCLM_of_bounded")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "286-289"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a measurable bounded domain, the Sobolev mass operator on
$`H^1_0(\Omega)` is compact. This is the operator form of the bounded-domain
Rellich embedding into $`L^2`.
:::

:::proof "elliptic.fredholm.compact_mass"
The mass form is the square-integrable inner product restricted to the
zero-trace Sobolev space. Its associated operator factors through the
canonical inclusion into square-integrable functions, which is compact by the
Rellich–Kondrachov theorem on bounded domains. A bounded sequence in the
Sobolev graph norm therefore has a subsequence converging in the
square-integrable norm, making the mass operator compact.
:::

Combining compactness of the mass operator with the abstract alternative gives
the Fredholm alternative for the original, unshifted divergence form. The
hypothesis is coercivity of some shift $`B+\lambda M`, exactly what Gårding's
inequality provides for $`\lambda\ge\mu_0`; the conclusion is about $`B`
itself, and no symmetry of $`B` is assumed.

To keep track of what the shift changes, write $`A:V\to V^*` for the
operator of $`B`, $`Mu=(u,\cdot)_{L^2}`, and $`A_\gamma=A+\gamma M`
for a coercive shift. Applying its bounded inverse gives

$$`
Au=F
\quad\Longleftrightarrow\quad
u-\underbrace{\gamma A_\gamma^{-1}M}_{K}u=A_\gamma^{-1}F.
`

The inverse supplies boundedness and the mass operator supplies compactness.
Why can the remaining obstruction have only finitely many independent
directions? If $`\ker(I-K)` were infinite-dimensional, choose an orthonormal
sequence $`e_j` in it. Then $`Ke_j=e_j`, whose pairwise distances are
$`\sqrt2`; that contradicts compactness of $`K`. The load must also
annihilate every adjoint null vector $`v`, since
$`F(v)=B(u,v)=0`. The Fredholm solvability theorem says that these are all
the compatibility conditions.

:::theorem "elliptic.fredholm.alternative" (parent := "elliptic.fredholm") (lean := "SobolevSpace.GraphSpace.fullDivergenceForm.fredholmAlternative_of_bounded") (uses := "elliptic.weak_solution, analysis.fredholm.exact_alternative")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "322-324"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega` be measurable and bounded, and let $`B` be the full
operator-valued divergence form on $`H_0^1(\Omega)`, assembled from bounded
operators $`A_{ij}`, $`b_i`, and $`c` on the derivative-coordinate
$`L^2` space. Assume that for some $`\lambda\in\mathbb R`,

$$`B(u,u)+\lambda\lVert u\rVert_{L^2(\Omega)}^2
\geq c_0\lVert u\rVert_{H^1_0(\Omega)}^2`

with $`c_0>0`. Then exactly one branch holds: either

$$`\exists u\ne0,\quad B(u,v)=0\quad\text{for every }v\in H_0^1(\Omega),`

or every $`F\in H^{-1}(\Omega)` admits a unique $`u\in H_0^1(\Omega)`
with $`B(u,v)=F(v)` for all test fields $`v`.

Openness of $`\Omega` is not needed. Local $`L^\infty` coefficients are the
case in which $`A_{ij}`, $`b_i`, and $`c` are multiplication operators.
:::

:::proof "elliptic.fredholm.alternative" (uses := "elliptic.lax_milgram, elliptic.fredholm.compact_mass, analysis.fredholm.exact_alternative")
Invert the shifted coercive form by Lax–Milgram.  The unshifted equation
becomes identity minus a compact mass perturbation.  The abstract Fredholm
alternative gives the mutually exclusive kernel-or-surjectivity dichotomy,
while bounded-domain
Rellich compactness supplies the required compact mass operator.
:::

The alternative decides solvability for one form. Replacing $`B` by
$`B-\lambda M` and letting $`\lambda` vary turns the question into a spectral
one. Its vocabulary is the pencil, its weak eigenfunctions, and the set of
parameters at which the alternative falls into its first branch.

:::definition "elliptic.spectrum.weak_pencil" (parent := "elliptic.fredholm") (lean := "SobolevSpace.Weak.pencilForm, SobolevSpace.Weak.IsWeakEigenfunction, SobolevSpace.Weak.weakSpectrum, SobolevSpace.Weak.weakEigenspace")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "323-325"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For continuous forms $`B,M:V\to V^*`, the pencil at the real parameter
$`\lambda` is

$$`
P_\lambda=B-\lambda M.
`

A weak eigenfunction is a nonzero $`u\in V` satisfying

$$`
B(u,v)=\lambda M(u,v)\qquad(\forall v\in V).
`

The weak spectrum $`\sigma_{\mathrm w}(B,M)` is the set of parameters
admitting such a field, while the weak eigenspace is the full kernel
$`E_\lambda=\ker P_\lambda`, including zero.
:::

A single shifted solution operator $`R=B_\gamma^{-1}M` controls every
parameter at once. The eigenvalue equation $`B(u,\cdot)=\lambda M(u,\cdot)` is
equivalent to $`B_\gamma(u,\cdot)=(\gamma+\lambda)M(u,\cdot)`, and inverting
the coercive form reads this as an eigenvector equation for $`R` with
eigenvalue $`(\gamma+\lambda)^{-1}`.

:::theorem "elliptic.spectrum.compact_reduction" (parent := "elliptic.fredholm") (lean := "SobolevSpace.Weak.isCompactOperator_spectralSolutionOperator, SobolevSpace.Weak.spectralSolutionOperator, SobolevSpace.Weak.add_ne_zero_of_isWeakEigenfunction, SobolevSpace.Weak.isWeakEigenfunction_iff_hasEigenvector_spectralSolutionOperator") (uses := "elliptic.spectrum.weak_pencil")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "323-325"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Suppose

$$`
B_\gamma=B+\gamma M
`

is coercive and $`M` is compact.  The single shifted solution operator

$$`
R=B_\gamma^{-1}M:V\to V
`

is compact. Coercivity excludes $`\gamma+\lambda=0` for every weak
eigenvalue. For parameters satisfying $`\gamma+\lambda\ne0`, the reciprocal
substitution gives the equivalence

$$`
u\text{ is a weak eigenfunction at }\lambda
\quad\Longleftrightarrow\quad
Ru=(\gamma+\lambda)^{-1}u,\quad u\ne0.
`
:::

:::proof "elliptic.spectrum.compact_reduction"
The coercive Lax–Milgram inverse is bounded, so composing it with the compact
mass operator gives a compact map.  Expanding
$`B_\gamma=B+\gamma M` converts the weak eigenvalue identity into
$`B_\gamma u=(\gamma+\lambda)Mu`; uniqueness of the shifted solve then gives
the displayed eigenvector equation, and the same calculation reverses.
:::

The reduction transfers the two kinds of compact-operator information
separately. Finite multiplicity is the nullity statement applied to the
pencil, which for each fixed $`\lambda` is itself a form with a coercive shift
by the same compact mass, namely $`(B-\lambda M)+(\gamma+\lambda)M=B_\gamma`.

:::theorem "elliptic.spectrum.finite_multiplicity" (parent := "elliptic.fredholm") (lean := "SobolevSpace.Weak.finiteDimensional_weakEigenspace") (uses := "elliptic.spectrum.weak_pencil, analysis.fredholm.weak_nullity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "323-325"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For the weak pencil $`B-\lambda M`, define

$$`
E_\lambda
=\left\{u\in V:\forall v\in V,\ B(u,v)=\lambda M(u,v)\right\}.
`

If $`B` admits a coercive shift and the mass operator $`M` is compact, then
$`\dim E_\lambda<\infty` for every $`\lambda\in\mathbb R`.
:::

:::proof "elliptic.spectrum.finite_multiplicity" (uses := "analysis.fredholm.weak_nullity")
Rewrite the eigenspace as the kernel of a compact perturbation of the
coercive shifted operator.  Fredholm theory makes that kernel
finite-dimensional.
:::

Countability and accumulation, on the other hand, are read off the compact
operator $`R`. The reciprocal map $`\lambda\mapsto(\gamma+\lambda)^{-1}` is
injective on the weak spectrum and lands in the nonzero point spectrum of
$`R`, which is countable.

:::theorem "elliptic.spectrum.countable" (parent := "elliptic.fredholm") (lean := "SobolevSpace.Weak.weakSpectrum_countable") (uses := "analysis.compact_spectrum.countable, elliptic.spectrum.compact_reduction")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "323-325"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For an abstract real weak form admitting a coercive shift and compact mass
operator, the exceptional set

$$`
\sigma_{\mathrm w}(B,M)
=\left\{\lambda\in\mathbb R:E_\lambda\ne\{0\}\right\}
`

is countable.
:::

:::proof "elliptic.spectrum.countable"
Translate each weak spectral parameter by the coercive shift and take its
reciprocal. This gives an injection into the nonzero eigenvalues of the compact
shifted solution operator, whose nonzero spectrum is countable.
:::

The same reciprocal substitution converts a convergent injective sequence of
weak eigenvalues into a convergent injective sequence of nonzero eigenvalues
of $`R`. Compactness forces the limit of the reciprocals to be zero, whereas
the reciprocals of a sequence with finite limit different from $`-\gamma`
converge to a nonzero number; the value $`-\gamma` itself is excluded by a
norm bound.

:::theorem "elliptic.spectrum.no_finite_accumulation" (parent := "elliptic.fredholm") (lean := "SobolevSpace.Weak.weakSpectrum_has_no_finite_injective_limit") (uses := "analysis.compact_spectrum.accumulation, elliptic.spectrum.compact_reduction")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "323-325"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Under the same hypotheses, if $`\lambda_j\in\sigma_{\mathrm w}(B,M)` are
pairwise distinct, there is no $`\lambda\in\mathbb R` for which

$$`\lambda_j\longrightarrow\lambda.`

Thus the weak spectrum has no finite accumulation point.
:::

:::proof "elliptic.spectrum.no_finite_accumulation"
For every weak eigenvalue, the compact-reduction equation gives the norm
bound

$$`
1\leq |\gamma+\lambda_j|\,\lVert R\rVert.
`

Passing to a hypothetical limit first rules out the singular value
$`\lambda=-\gamma`.  The reciprocals
$`(\gamma+\lambda_j)^{-1}` then form an injective convergent sequence of
nonzero eigenvalues of the compact operator $`R`.  Compact spectral theory
forces their limit to be zero, contradicting the fact that the finite
non-singular limit has a nonzero reciprocal.
:::

Absence of finite accumulation points has an immediate consequence for
monotone sequences. A strictly increasing sequence of weak eigenvalues is
injective, so it cannot converge; being monotone, it must then be unbounded.

:::theorem "elliptic.spectrum.increasing_eigenvalues_diverge" (parent := "elliptic.fredholm") (lean := "SobolevSpace.Weak.strictMono_weakEigenvalues_tendsto_atTop") (uses := "elliptic.spectrum.no_finite_accumulation")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "323-325"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Under the same shifted-coercive and compact-mass hypotheses, every strictly
increasing sequence of weak eigenvalues satisfies

$$`
\lambda_j\longrightarrow+\infty.
`
:::

:::proof "elliptic.spectrum.increasing_eigenvalues_diverge"
A strictly increasing real sequence that failed to tend to $`+\infty` would
be bounded above.  Monotone convergence would then give a finite limit, in
contradiction with the absence of finite injective spectral accumulation.
:::

Finally, the Fredholm alternative applied to the pencil $`B-\lambda M`
characterizes the complement of the weak spectrum. Absence of a weak
eigenfunction at $`\lambda` is triviality of the kernel of the pencil, and for
a form with a coercive shift by a compact mass this is equivalent to unique
solvability for every dual load.

:::theorem "elliptic.spectrum.solvability_off_spectrum" (parent := "elliptic.fredholm") (lean := "SobolevSpace.Weak.unique_pencil_solution_iff_notMem_weakSpectrum") (uses := "elliptic.spectrum.weak_pencil")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "323-325"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Under the shifted-coercive and compact-mass hypotheses,

$$`
\lambda\notin\sigma_{\mathrm w}(B,M)
\iff
\forall F\in V^*,\ \exists!\,u\in V,\
\forall v\in V,\ B(u,v)-\lambda M(u,v)=F(v).
`

So absence of a homogeneous weak eigenfunction is equivalent to unique
solvability of the inhomogeneous pencil for every continuous dual load.
:::

:::proof "elliptic.spectrum.solvability_off_spectrum" (uses := "elliptic.spectrum.finite_multiplicity, elliptic.fredholm.alternative")
Apply the Fredholm dichotomy to the shifted pencil.  Absence from the weak
spectrum is exactly triviality of the homogeneous kernel; the alternative
then gives existence and uniqueness for every load, and the converse follows
by testing the zero load.
:::

# Dirichlet eigenvalues and the first eigenfunction

For a symmetric, uniformly elliptic Dirichlet problem on a bounded domain,
the form is coercive on $`H^1_0(\Omega)`
by Poincaré's inequality, the embedding into $`L^2` is compact by Rellich's
theorem, and symmetry makes the solution operator self-adjoint. The spectral
theorem for compact self-adjoint operators then gives an orthonormal basis of
eigenfunctions, as in {Informal.citet "evans-2010"}[] §6.5.1. The min–max
formula below characterizes every eigenvalue.

:::theorem "elliptic.spectrum.ordered_basis" (parent := "elliptic.fredholm") (lean := "SobolevSpace.GraphSpace.exists_ordered_hilbertBasis_variableCoeff_eigenfunctions, SobolevSpace.GraphSpace.exists_ordered_hilbertBasis_weakDivergence_eigenfunctions") (uses := "elliptic.spectrum.weak_pencil, elliptic.spectrum.increasing_eigenvalues_diverge")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§6.5.1"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n\ge1` and let $`\Omega\subset\mathbb R^n` be nonempty, open, and
bounded. Let $`B` be the Dirichlet form of symmetric, uniformly elliptic
coefficients (bounded operators on $`L^2`, or measurable $`L^\infty`
functions). There are an orthonormal basis $`(w_k)_{k\ge0}` of
$`L^2(\Omega)`, functions $`u_k\in H^1_0(\Omega)` with $`u_k=w_k` in
$`L^2`, and numbers

$$`0<\lambda_0\le\lambda_1\le\lambda_2\le\cdots\to\infty,`

such that each $`u_k` is a weak Dirichlet eigenfunction with eigenvalue
$`\lambda_k`, and

$$`\lambda_k=\min\Bigl\{\,r:\ \exists W\subseteq H^1_0(\Omega),\ \dim W=k+1,
\ B(v,v)\le r\lVert v\rVert_{L^2}^2\ \ \forall v\in W\Bigr\}.`

No regularity of $`\partial\Omega` and no connectedness is assumed. The
indexing starts at $`0`, so $`\lambda_0` is the first eigenvalue.
:::

:::proof "elliptic.spectrum.ordered_basis" (uses := "elliptic.spectrum.compact_reduction")
Since $`\Omega` is open and nonempty it has positive measure, so
$`L^2(\Omega)` is infinite-dimensional. Poincaré's inequality makes $`B`
coercive, Rellich's theorem makes $`H^1_0\to L^2` compact, and the embedding
has dense range. An abstract theorem for a symmetric coercive form with a
compact dense embedding produces the ordered basis. Its eigenvalues increase to
infinity, and the $`k`-th is the least uniform Rayleigh bound on
$`(k+1)`-dimensional subspaces, attained on the span of the first $`k+1`
eigenfunctions. For $`L^\infty` coefficients the weak eigenvalue equation is
rewritten as the divergence-form equation with load $`\lambda_kw_k`.
:::

The unit square is the example to keep in mind. There the eigenfunctions are
$`\sin(j\pi x)\sin(k\pi y)` with eigenvalues $`\pi^2(j^2+k^2)`, which the
figure orders and draws.

{leanpde_figure "dirichlet-eigenfunctions"}

Only the first eigenfunction keeps one sign. Every later one changes sign,
since it is orthogonal in $`L^2` to the positive first one. Multiplicities
appear as soon as the square's symmetry allows: $`5\pi^2` belongs to both
$`(1,2)` and $`(2,1)`, and every combination of the two is again an
eigenfunction, with a different nodal set. The Lean theorems are stated for
general domains, and they prove the shape of the picture: an ordered,
unbounded list and, for the local operators on connected domains considered
below, a simple first eigenvalue with a positive eigenfunction.

For local, symmetric, uniformly elliptic coefficients on a nonempty bounded
open domain in positive dimension, the principal form attains its least
Rayleigh value. Let $`u` be a
minimizer with unit $`L^2` norm. Replacing $`u` by $`|u|` preserves its norm
and its quadratic energy: the weak gradient changes sign on the negative
set, and both factors in the quadratic form change sign together. The
minimization argument then gives a nonnegative weak eigenfunction.

Strict positivity needs one more piece of analysis. A Sobolev function is an
almost-everywhere equivalence class, so a claim about its value at each point
must first identify a representative. Interior elliptic regularity constructs
a $`C^2` function $`f` representing $`u`. Expanding the divergence equation gives

$$`
-\sum_{i,j}a_{ij}\partial_{ij}f
-\sum_j\left(\sum_i\partial_i a_{ij}\right)\partial_j f
=\lambda f.
`

The derivatives of $`a` produce the drift in the classical matrix operator.
Continuity turns the almost-everywhere nonnegativity of $`u` into
nonnegativity of $`f` throughout the open domain. It also turns the
almost-everywhere ellipticity bound into a pointwise bound. The strong maximum
principle then applies: on a connected domain, a nonzero nonnegative
eigenfunction is positive at every point.

:::theorem "elliptic.spectrum.first_dirichlet" (parent := "elliptic.fredholm") (lean := "SobolevSpace.GraphSpace.exists_pos_first_dirichlet_eigenfunction, SobolevSpace.GraphSpace.eq_smul_of_first_dirichlet_eigenfunctions_of_pos_dimension") (uses := "elliptic.spectrum.ordered_basis, elliptic.maximum.matrix_strong")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§6.5.1"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`n\ge1` and let $`\Omega` be a nonempty, bounded, open, connected
set. There are $`\lambda>0`, $`u\in H^1_0(\Omega)` with
$`\lVert u\rVert_{L^2}=1`, and a function $`f` equal to $`u` almost
everywhere, such that $`u` is a weak Dirichlet eigenfunction of $`-\Delta`
with eigenvalue $`\lambda`, the number $`\lambda` is the least value of
$`\int|\nabla v|^2/\int v^2` over $`v\in H^1_0(\Omega)\setminus\{0\}`, and

$$`f\in C^2(\Omega),\qquad -\Delta f=\lambda f\ \text{ and }\ f>0\ \text{ in }\Omega.`

Any two weak eigenfunctions for this least Rayleigh value are multiples of each
other.
:::

:::proof "elliptic.spectrum.first_dirichlet" (uses := "elliptic.spectrum.ordered_basis, elliptic.maximum.matrix_strong")
Compactness of $`H^1_0\to L^2` gives a unit minimizer of the Rayleigh
quotient, and the minimizer is a weak eigenfunction. Replace it by $`|u|`,
which has the same energy and mass and so is again a minimizer. Interior
regularity gives a $`C^2` representative $`f\ge0` with
$`-\Delta f=\lambda f\ge0`, and the strong maximum principle for
superharmonic functions on the connected set $`\Omega` makes $`f>0`. To show
that $`\lambda` is simple, apply the same argument to $`|w|`: every nonzero
eigenfunction $`w` has a representative with no zeros in $`\Omega`. Given
eigenfunctions $`u` and $`v`, pick a point $`x_0` and a constant $`c` with
$`v(x_0)=c\,u(x_0)`. Then $`v-cu` is an eigenfunction or zero, and it
vanishes at $`x_0`, so it is zero.
:::

For variable coefficients, the interior bootstrap needs bounded weak
derivatives of the coefficients through an order that grows with the
dimension, and their first derivatives identify the drift. The boundary may be
irregular: the zero boundary condition is encoded by $`u\in H^1_0(\Omega)`,
and the positivity conclusion concerns points inside $`\Omega`.

:::theorem "elliptic.spectrum.first_divergence" (parent := "elliptic.fredholm") (lean := "SobolevSpace.GraphSpace.exists_pos_first_weakDivergence_eigenfunction") (uses := "elliptic.spectrum.ordered_basis, elliptic.maximum.matrix_strong")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§6.5.1"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega` be nonempty, bounded, open, and connected in $`\mathbb R^n`,
$`n\ge1`, and let $`a_{ij}` be globally Lipschitz, $`C^1` at points of
$`\Omega`, a.e. symmetric and uniformly elliptic, with restrictions in
$`W^{m+1,\infty}(\Omega)` for some $`m` with $`3+\lfloor n/2\rfloor\le m+2`.
Then the least Rayleigh value $`\lambda>0` of
$`\int a_{ij}\partial_iv\,\partial_jv/\int v^2` over $`H^1_0(\Omega)` is
attained by a unit eigenfunction $`u`. It has a representative $`f` that is
$`C^2` and positive in $`\Omega`, and satisfies

$$`-\sum_{i,j}a_{ij}\partial_{ij}f-\sum_j\Bigl(\sum_i\partial_ia_{ij}\Bigr)\partial_jf
=\lambda f\quad\text{in }\Omega.`
:::

:::proof "elliptic.spectrum.first_divergence" (uses := "elliptic.spectrum.ordered_basis, elliptic.maximum.matrix_strong")
The argument of {bpref "elliptic.spectrum.first_dirichlet"}[the Laplacian
case] applies with the matrix operator in place of $`-\Delta`, after the
interior bootstrap and the expansion of the divergence into the matrix
operator with drift.
:::

With smooth coefficients and a smooth boundary the first eigenvalue controls
the whole complex spectrum, even when the operator has a drift and is not
symmetric. This is {Informal.citet "evans-2010"}[] §6.5.2, Theorem 3. Here the
eigenfunction is smooth up to the boundary and vanishes there.

:::theorem "elliptic.spectrum.principal_eigenpair" (parent := "elliptic.fredholm") (lean := "SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients.exists_principal_eigenpair") (uses := "elliptic.spectrum.first_divergence")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "§6.5.2"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega` be bounded, open, and connected with $`C^k` graph boundary for
every $`k`. Let $`L` have smooth coefficients, a symmetric principal part
with ellipticity constant $`\alpha>0`, a drift, and a potential $`c\ge0`.
There are $`r>0` and $`z\in C^\infty(\overline\Omega)` with $`z=0` on
$`\partial\Omega`, $`z>0` in $`\Omega`, $`Lz=rz` in $`\Omega`, and
$`\lVert z\rVert_{L^2}=1`, such that:

* $`z` represents a weak Dirichlet eigenfunction $`u\in H^1_0\cap H^2`
  for $`r`;
* every real weak eigenfunction for $`r` is a multiple of $`u`, and every
  complex one is a complex multiple of $`u`;
* every complex weak eigenvalue $`\lambda` of $`L` satisfies
  $`r\le\operatorname{Re}\lambda`.
:::

:::proof "elliptic.spectrum.principal_eigenpair" (uses := "elliptic.spectrum.first_divergence")
Since $`c\ge0`, the Dirichlet problem for $`L` has a compact inverse on
$`L^2` that maps nonnegative functions to nonnegative functions. An interior
subeigenvector and Schaefer's fixed point theorem give a normalized
nonnegative eigenvector. Elliptic regularity up to the smooth boundary makes
it smooth on $`\overline\Omega` with zero boundary values, and the strong
maximum principle makes it positive inside. Shifting the potential, the same
construction gives a positive eigenfunction of the formal adjoint with the same
eigenvalue $`r`. Testing a complex eigenfunction against this positive weight
and comparing moduli gives $`r+s\le|\lambda+s|` for every $`s\ge0`, and
letting $`s\to\infty` gives $`r\le\operatorname{Re}\lambda`. Every nonzero
real eigenfunction for $`r` has a representative with no zeros, so a
combination vanishing at one point vanishes identically, which is geometric
simplicity. A complex eigenfunction for the real value $`r` splits into two
real ones.
:::
