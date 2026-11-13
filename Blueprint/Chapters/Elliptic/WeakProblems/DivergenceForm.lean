/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Elliptic.WeakProblems.Dirichlet
import PDE.Elliptic.Variational.DivergenceForm
import PDE.Elliptic.Variational.DivergenceSolution
import PDE.Elliptic.Variational.PrincipalForms

/-!
# Principal divergence-form problems

Operator-valued principal forms, their pointwise coefficient specialization,
integrated coercivity, and weak existence and uniqueness for uniformly elliptic
divergence-form equations.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
-- Directive attributes are single-line syntax; blank lines delimit rendered paragraphs.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

set_option linter.hashCommand false in
#doc (Manual) "Principal Divergence-Form Problems" =>

# Principal forms and ellipticity

The principal divergence-form equation replaces the identity matrix in
Poisson's equation by a coefficient field:

$$`-D_i\!\left(a^{ij}D_j u\right)=f.`

We first represent the coefficients as a finite matrix of bounded
operators on $`L^2(\Omega)`.  Pointwise multiplication by an
$`L^\infty` matrix field recovers the local PDE model, while the
operator-valued form is also meaningful for bounded nonlocal coefficients.

Almost-everywhere pointwise ellipticity of the matrix field is integrated against the weak gradient.
That produces coercivity of the principal form after Poincaré controls the
$`L^2` coordinate.  Lax–Milgram then constructs the unique element of
$`H^1_0(\Omega)`, and the smooth-test bridge identifies its variational
equation with the displayed divergence-form PDE.

Each hypothesis has one job: measurability and
essential boundedness define the multiplication operators, ellipticity
controls the gradient, boundedness of the domain supplies Poincaré, and
openness supplies compactly supported smooth test functions.

:::definition "elliptic.divergence.form" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.variableCoeffForm")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "314"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The principal divergence-form bilinear form contracts the weak gradients of
the trial and test functions against a matrix of bounded operators on
$`L^2(\Omega)`. Pointwise multiplication operators give an $`L^\infty`
coefficient matrix; arbitrary bounded operators give nonlocal coefficients.
:::

For any matrix of bounded operators the form $`B_A` is bounded, but nothing so
far gives it a lower bound. The Lax–Milgram argument only ever sees the
quadratic form $`B_A(u,u)` on $`H^1_0(\Omega)`, so the weakest usable
ellipticity hypothesis is stated directly at that level, as a comparison with
the Dirichlet form.

:::definition "elliptic.divergence.integrated_ellipticity" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.IntegratedElliptic") (uses := "elliptic.divergence.form, elliptic.dirichlet.form")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "312-313"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
An operator-valued coefficient matrix is integrated-uniformly elliptic with
constant $`\alpha>0` when its principal quadratic form dominates
$`\alpha` times the Dirichlet form on every $`H^1_0` field.  This is exactly
the energy inequality needed by the abstract coercivity argument.
:::

The pointwise ellipticity hypothesis constrains the matrix $`a(x)` for almost
every $`x` and every direction $`\xi`. It only makes
sense for multiplication operators, which is why it is a separate definition
rather than a special case of the integrated one.

:::definition "elliptic.divergence.ae_ellipticity" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.AEUniformlyElliptic")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "312-313"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For a measurable $`L^\infty` matrix field $`a`, Evans's pointwise condition
requires a single $`\alpha>0` such that, for almost every $`x` and every
$`\xi\in\mathbb R^n`, one has

$$`\alpha |\xi|^2\le \sum_{i,j}a_{ij}(x)\xi_j\xi_i.`

The matrix need not be symmetric: only its symmetric part contributes to this
quadratic inequality, and the coercivity result below applies to nonsymmetric
coefficients satisfying the same condition.
:::

The two notions are compatible in the expected direction. Choosing
$`\xi=\nabla u(x)` in the pointwise inequality and integrating over $`\Omega`
recovers the integrated inequality for the multiplication realization, with
the same constant $`\alpha`.

:::theorem "elliptic.divergence.ae_implies_integrated" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.integratedElliptic_multiplication_of_ae") (uses := "elliptic.divergence.ae_ellipticity, elliptic.divergence.integrated_ellipticity")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "312-314"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Almost-everywhere pointwise ellipticity of an $`L^\infty` matrix field
implies integrated ellipticity of its multiplication-operator realization.
:::

:::proof "elliptic.divergence.ae_implies_integrated"
Apply the pointwise matrix inequality to the measurable vector of weak
derivatives and integrate.  Hölder integrability of each coefficient-gradient
product justifies the finite sums and integrals.
:::

The integrated hypothesis feeds the Hilbert-space theory, while the PDE
reading of the problem needs the concrete $`L^\infty` coefficients and
compactly supported smooth tests. As for Poisson's equation, the
distributional predicate carries the openness of $`\Omega` with it.

:::definition "elliptic.divergence.weak_solution" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.IsWeakDivergenceSolution") (uses := "elliptic.divergence.form")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "314-315"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For an open measurable domain, $`a^{ij}\in L^\infty(\Omega)`,
$`f\in L^2(\Omega)`, and $`u\in H^1_0(\Omega)`, the weak-solution predicate
stores the openness of $`\Omega` and records

$$`\sum_{i,j=1}^n\int_\Omega
  a^{ij}(x)D_j u(x)D_i\varphi(x)\,dx
  =\int_\Omega f(x)\varphi(x)\,dx`

for every $`\varphi\in C_c^\infty(\Omega)`. This is the concrete
distributional equation for $`-D_i(a^{ij}D_j u)=f`. A separate density
theorem identifies it with the operator-valued variational identity tested
against every $`v\in H^1_0(\Omega)`.
:::

Coercivity is proved at the operator-valued level from the integrated
hypothesis alone. The ellipticity constant $`\alpha` only compares $`B_A` with
the Dirichlet form, so the bounded-domain Poincaré inequality is still needed,
exactly as for the Dirichlet form itself, to control the base $`L^2`
coordinate.

:::theorem "elliptic.divergence.coercive" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.variableCoeffForm_isCoercive") (uses := "elliptic.divergence.integrated_ellipticity, elliptic.dirichlet.coercive, sobolev.poincare")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "318-320"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`A=(A_{ij})` be a matrix of bounded operators on $`L^2(\Omega)`. On a
bounded measurable domain in positive dimension, suppose $`A` is
integrated-uniformly elliptic: for some $`\alpha>0`,

$$`\alpha B_\Omega(u,u)\le B_A(u,u)
  \qquad\text{for every }u\in H^1_0(\Omega).`

Then the variable-coefficient form satisfies
$`B_A(u,u)\ge c\lVert u\rVert_{H^1_0}^2` for some $`c>0`. For a pointwise
$`L^\infty` coefficient matrix, the preceding almost-everywhere-to-integrated
theorem supplies this hypothesis from Evans's pointwise ellipticity condition.
:::

:::proof "elliptic.divergence.coercive" (uses := "elliptic.dirichlet.coercive")
Integrated ellipticity bounds the operator-valued principal form below by
$`\alpha` times the Dirichlet form. The bounded-domain Poincaré estimate makes
the Dirichlet form coercive for the full graph-space norm, and multiplication
of the two positive constants gives the result.
:::

:::theorem "elliptic.divergence.exists_unique" (parent := "elliptic.weak_theory") (lean := "SobolevSpace.GraphSpace.IsWeakDivergenceSolution.existsUnique_of_ae") (uses := "elliptic.divergence.weak_solution, elliptic.divergence.ae_implies_integrated, elliptic.divergence.coercive, elliptic.lax_milgram")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "314-320"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega` be open, measurable, and bounded with $`n\ge1`. If
$`a\in L^\infty` is uniformly elliptic almost everywhere, then every
$`f\in L^2(\Omega)` admits exactly one $`u\in H^1_0(\Omega)` satisfying

$$`-D_i(a^{ij}D_j u)=f\quad\text{weakly on }\Omega.`
:::

:::proof "elliptic.divergence.exists_unique" (uses := "elliptic.lax_milgram, elliptic.divergence.coercive")
Represent the coefficient field by its bounded multiplication operators,
deduce coercivity from almost-everywhere ellipticity, apply Lax–Milgram, and
translate the Hilbert-space equation back to the concrete weak integral
identity.
:::
