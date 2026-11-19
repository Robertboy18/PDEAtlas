/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Hyperbolic.NonlinearWaves
import PDE.Hyperbolic.Classical.CanonicalForm2D.Wave

/-!
# Canonical hyperbolic form

Null covectors and the canonical form of a two-variable hyperbolic principal
symbol.
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
#doc (Manual) "Two-Variable Canonical Form" =>

For a second-order equation in two variables, hyperbolicity is encoded by the
principal quadratic form. Its two characteristic directions are the
covectors on which that form vanishes. Choosing two independent null covectors
as a basis of the cotangent space removes the two pure terms from the
*principal symbol* and leaves one nonzero mixed term. The statement is
pointwise linear algebra.

The final sum-and-difference change of variables converts that mixed
derivative into the familiar difference of two pure second derivatives. At
the level of principal symbols, this is the algebraic reason a general
two-variable hyperbolic operator resembles the wave operator.

:::group "hyperbolic.canonical_form_2d"
Canonical form in two dimensions
:::

:::definition "hyperbolic.canonical_form_2d.principal_symbol" (parent := "hyperbolic.canonical_form_2d") (lean := "Hyperbolic.CanonicalForm2D.PrincipalPart.determinant, Hyperbolic.CanonicalForm2D.PrincipalPart.IsHyperbolic, Hyperbolic.CanonicalForm2D.PrincipalPart.quadratic, Hyperbolic.CanonicalForm2D.PrincipalPart.mixed, Hyperbolic.CanonicalForm2D.principalExpression")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "418-420"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For the symmetric principal matrix

$$`
A=\begin{pmatrix}a^{11}&a^{12}\\a^{12}&a^{22}\end{pmatrix},
`

hyperbolicity means
$`\det A=a^{11}a^{22}-(a^{12})^2<0`. The associated quadratic and polarized
forms are

$$`
Q_A(\xi)=a^{11}\xi_1^2+2a^{12}\xi_1\xi_2+a^{22}\xi_2^2,
\qquad
M_A(\xi,\eta)=a^{11}\xi_1\eta_1+
a^{12}(\xi_1\eta_2+\xi_2\eta_1)+a^{22}\xi_2\eta_2.
`

The mixed form is the transformed off-diagonal matrix coefficient.
:::

A negative determinant makes the quadratic form $`Q_A` indefinite and
nondegenerate, so its null cone in the two-dimensional cotangent space is a
pair of distinct lines.

:::theorem "hyperbolic.canonical_form_2d.characteristic_covectors" (parent := "hyperbolic.canonical_form_2d") (lean := "Hyperbolic.CanonicalForm2D.PrincipalPart.exists_independent_characteristicCovectors") (uses := "hyperbolic.canonical_form_2d.principal_symbol")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "419-420"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Every hyperbolic symmetric principal part has real covectors $`\xi,\eta` such
that

$$`
Q_A(\xi)=Q_A(\eta)=0,\qquad
M_A(\xi,\eta)\ne0,\qquad
\det(\xi,\eta)\ne0.
`
:::

:::proof "hyperbolic.canonical_form_2d.characteristic_covectors"
When $`a^{11}\ne0`, the negative determinant makes the characteristic
quadratic have two distinct real slopes; the corresponding covectors are
independent null directions. Polarization shows their mixed pairing cannot
vanish, since two independent null vectors with zero pairing would make the
whole quadratic form zero. When $`a^{11}=0`, explicit coordinate covectors
give the same conclusions.
:::

Expressing the principal part in a basis of two characteristic covectors sets
the transformed pure coefficients $`b^{11}` and $`b^{22}` to zero, so the
principal expression collapses to $`2b^{12}w_{y_1y_2}`, with $`b^{12}` the
transformed mixed coefficient, that is, the pairing $`M_A(\xi,\eta)` just
shown to be nonzero.

:::theorem "hyperbolic.canonical_form_2d.wave_symbol" (parent := "hyperbolic.canonical_form_2d") (lean := "Hyperbolic.CanonicalForm2D.mixedPrincipalExpression_to_wave") (uses := "hyperbolic.canonical_form_2d.principal_symbol")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "420"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`z(y)=(y_1+y_2,y_1-y_2)` and assume $`w` is $`C^2` near $`z(y)`.
The chain rule and equality of mixed partials give

$$`
\partial_{y_1}\partial_{y_2}(w\circ z)(y)
  =w_{z_1z_1}(z(y))-w_{z_2z_2}(z(y)).
`

Multiplying by the mixed coefficient turns the remaining principal expression
into

$$`
2b^{12}\bigl(w_{z_1z_1}-w_{z_2z_2}\bigr).
`

The nonzero factor $`2b^{12}` is kept; dividing by it gives the wave
operator.
:::

:::proof "hyperbolic.canonical_form_2d.wave_symbol"
Set the new wave coordinates to $`z_1=y_1+y_2` and $`z_2=y_1-y_2`, where
$`y_1,y_2` are the characteristic variables. Expanding both second
derivatives, the equal mixed partials cancel the cross terms and the surviving
pure terms have opposite signs. Multiplication by the original mixed
coefficient gives the displayed factor.
:::

# Constructing coordinates for the full equation

For variable coefficients, choosing null covectors separately at each point
does not yet produce coordinate functions; the coordinates come from first
integrals of the characteristic fields.

:::theorem "hyperbolic.canonical_form_2d.local_chart" (parent := "hyperbolic.canonical_form_2d") (lean := "Hyperbolic.CanonicalForm2D.exists_characteristic_chart, Hyperbolic.CanonicalForm2D.exists_canonical_equation") (uses := "hyperbolic.canonical_form_2d.characteristic_covectors")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "Chapter 7, two-variable hyperbolic canonical form"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 } }] }
%%%
Suppose the three principal coefficients are $`C^2` near $`x_0` and
$`\det A(x_0)<0`. There is a local coordinate map
$`e:x\mapsto(\xi,\eta)`, with open source containing $`x_0`, whose map and
inverse are $`C^2`. On its source,

$$`
Q_A(D\xi)=Q_A(D\eta)=0,\qquad M=M_A(D\xi,D\eta)\ne0.
`

For the full nondivergence-form operator

$$`Lu=\sum_{i,j}a^{ij}\partial_i\partial_j u+\sum_i b^i\partial_i u+cu,`

put $`w=u\circ e^{-1}`. At each source point where $`u` is $`C^2`, the
equation $`Lu=f` is equivalent to

$$`
w_{\xi\eta}+\frac{L_0\xi}{2M}w_\xi
 +\frac{L_0\eta}{2M}w_\eta+\frac{c}{2M}w=\frac{f}{2M},
\qquad L_0=\sum_{i,j}a^{ij}\partial_i\partial_j+\sum_i b^i\partial_i.
`

All coefficients on the right are evaluated at $`e^{-1}(\xi,\eta)`.
The drift $`b` and potential $`c` are arbitrary functions; only the principal
coefficients carry a regularity hypothesis.
:::

:::proof "hyperbolic.canonical_form_2d.local_chart"
A fixed linear shear provides a noncharacteristic initial line, including
when the original $`a^{11}` vanishes. The two characteristic ODEs construct
$`C^2` first integrals with independent differentials. The inverse function
theorem supplies the chart; shrinking its source keeps the mixed coefficient
nonzero. The second-order chain rule gives the transformed principal terms
and the additional drift $`L_0\xi,L_0\eta`. Dividing by $`2M` gives the
stated equivalence with the full equation.
:::

:::theorem "hyperbolic.canonical_form_2d.full_wave_change" (parent := "hyperbolic.canonical_form_2d") (lean := "Hyperbolic.CanonicalForm2D.linearOperator_comp_characteristic_to_wave") (uses := "hyperbolic.canonical_form_2d.local_chart, hyperbolic.canonical_form_2d.wave_symbol")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    citation := "Chapter 7, two-variable hyperbolic canonical form"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 } }] }
%%%
For a $`C^2` characteristic map $`(\xi,\eta)` and $`C^2` function
$`W(z_1,z_2)`, set $`z_1=\xi+\eta`, $`z_2=\xi-\eta`. With $`M` and $`L_0` as
in the {bpref "hyperbolic.canonical_form_2d.local_chart"}[local chart theorem],
the full operator satisfies the composition identity

$$`
L\bigl(W(\xi+\eta,\xi-\eta)\bigr)
=2M(W_{z_1z_1}-W_{z_2z_2})
 +(L_0\xi+L_0\eta)W_{z_1}
 +(L_0\xi-L_0\eta)W_{z_2}+cW.
`

The derivatives of $`W` are evaluated in the new coordinates. Thus the
mixed-to-wave change retains the drift and potential as well as the
principal part.
:::

:::proof "hyperbolic.canonical_form_2d.full_wave_change"
Apply the full second-order composition formula to the characteristic map.
The null-coordinate identities eliminate both pure characteristic terms.
The sum-and-difference chain rule converts the mixed term into the difference
of pure second derivatives and converts the two first derivatives into their
sum and difference. The zeroth-order term is unchanged by composition.
:::
