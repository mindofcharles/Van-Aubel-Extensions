# Van Aubel Extensions

A structural formulation of Van Aubel's theorem through complex structures on real vector spaces, together with a Lean 4 formalization, randomized numerical checks, and a self-contained interactive demonstration.

The mathematical sources of truth for this repository are three completed notes:

- [Van Aubel as a Complex-Structure Identity](paper/van-aubel-complex-structure-identity.md);
- [Edge-Operator Realizations and Rigidity of the Van Aubel Center Identity](paper/van-aubel-edge-operator-realizations-and-rigidity.md);
- [Complex-Affine Naturality and Transfer of the Van Aubel Center Construction](paper/van-aubel-complex-affine-naturality-and-transfer.md).

[![DOI](https://zenodo.org/badge/1346334286.svg)](https://doi.org/10.5281/zenodo.22100009)

> [!NOTE]
> It is still a work in progress, and no work is ever truly complete. I am continuing to refine and improve it. \
> I also have several new research findings, which I am currently organizing and preparing for release.

> [!TIP]
> If you notice any issues or have any suggestions and have the time, \
> please leave them in the Issues section. Thank you.

I would like to express my sincere gratitude to **GPT**. **GPT** cross-validated my conclusions, provided many valuable suggestions, and collaborated with me in developing the Lean 4 formalization for this project.

The Lean development formalizes the following results:

- the central identity;
- the intrinsic affine and vector-coordinate edge-operator classifications;
- sign, orthogonal, and sharp real-dimension-two rigidity;
- pairwise-distinct nonorthogonal exceptional families in every complex dimension at least two;
- complex-affine naturality of centers, full identities, and possibly degenerate squares;
- metric transport and isometry criteria;
- recursive complex-affine term normal forms and universal transfer;
- explicit counterexamples separating algebraic transport from metric preservation.

(The expository category-theory packaging is intentionally outside Lean; all non-categorical theorem and counterexample claims are mirrored.)

## The central identity

Let $V$ be a real vector space, and let $J \colon V \to V$ be a linear map satisfying:

$$
J^2 = -I.
$$

Choose one sign $\varepsilon \in \{-1,+1\}$, and for a directed edge $XY$ define:

$$
M_{XY} = X + \frac{(Y-X)+\varepsilon J(Y-X)}{2}.
$$

Given four ordered points $A,B,C,D$, put:

$$
P=M_{AB}, \qquad Q=M_{BC}, \qquad R=M_{CD}, \qquad S=M_{DA}.
$$

Then:

$$
R-P=\varepsilon J(S-Q).
$$

This identity is affine-algebraic and needs only $J^2=-I$.

If $V$ is an inner-product space and $J$ is orthogonal, it immediately gives the metric conclusions:

$$
{\lVert R-P\rVert}=\lVert S-Q\rVert, \qquad \langle R-P,S-Q\rangle=0.
$$

Thus the two segments joining opposite centers have equal length and perpendicular directions.

In an oriented Euclidean plane, this specializes to the classical Van Aubel theorem.

## Scope and results

The construction and its formalization cover:

- arbitrary ordered quadruples, including coincident, collinear, degenerate, and non-coplanar configurations;
- vector-space and affine-space versions of the center identity;
- the square construction and its metric consequences for orthogonal complex structures;
- the classical oriented two-dimensional theorem;
- the square formed by the side midpoints of the four centers;
- existence of orthogonal complex structures exactly in even-dimensional finite-dimensional real inner-product spaces;
- a precise transfer principle for complex-affine coefficient identities;
- rigidity when independently chosen edge operators are orthogonal;
- rigidity of independently chosen edge signs on a nonzero real vector space;
- an explicit nonorthogonal exceptional family in real dimension $4$;
- concrete higher-dimensional behavior, including perpendicular but disjoint affine lines.

For the central identity, the same operator $J$ and the same sign $\varepsilon$ are used on all four directed edges.

Orthogonality is required only for the equal-length and perpendicularity conclusions, not for the algebraic identity itself.

## Lean formalization

The project is pinned to Lean `v4.33.1` and mathlib `v4.33.1`.

Install [elan](https://lean-lang.org), then build from the Lean project directory:

```bash
cd lean
lake build
```

The public umbrella module preserves a single import path:

```lean
import VanAubelExtensions

#check VanAubelExtensions.vanAubelIdentity
#check VanAubelExtensions.affineVanAubelIdentity
#check VanAubelExtensions.vanAubelTheorem
#check VanAubelExtensions.nonempty_orthogonalComplexStructure_iff_even
#check VanAubelExtensions.complexCoefficientIdentity_transfer
#check VanAubelExtensions.affineUniversalOperatorIdentity_iff_parametrized
#check VanAubelExtensions.universalOperatorIdentity_rigidity_of_finrank_two
#check VanAubelExtensions.ComplexAffineTerm.evalAffine_transfer_from_affineComplexLine
#check VanAubelExtensions.exceptional_family_in_every_complex_dimension_ge_two
```

The current development builds without `sorry`, `admit`, or project-defined axioms.

### Module guide

| Module | Contents |
| --- | --- |
| [`Basic`](lean/VanAubelExtensions/Basic.lean) | Orthogonal complex structures and their elementary properties |
| [`CenterIdentity`](lean/VanAubelExtensions/CenterIdentity.lean) | Linear and affine center constructions and the central identity |
| [`SquareGeometry`](lean/VanAubelExtensions/SquareGeometry.lean) | Squares on directed edges, square naturality and degeneration, target metric re-realization, isometry criteria, and the planar theorem |
| [`Dimension`](lean/VanAubelExtensions/Dimension.lean) | Standard even-dimensional structures and the dimension characterization |
| [`Rigidity`](lean/VanAubelExtensions/Rigidity.lean) | Intrinsic affine and vector four-operator parametrizations, complex-structure classification, sign and orthogonal rigidity, and sharp dimension-two rigidity |
| [`MidpointSquare`](lean/VanAubelExtensions/MidpointSquare.lean) | The derived square formed from center-side midpoints |
| [`ComplexAffineTransfer`](lean/VanAubelExtensions/ComplexAffineTransfer.lean) | Complex scalar action, center and identity naturality, recursive affine-term syntax and normal forms, coefficient uniqueness, and universal transfer |
| [`Examples`](lean/VanAubelExtensions/Examples.lean) | Incidence and metric counterexamples, the pairwise-distinct `ℂ²` exceptional family, and its extension to every complex dimension at least two |

[`lean/VanAubelExtensions.lean`](lean/VanAubelExtensions.lean) imports all of these modules and is the recommended entry point.

## Numerical consistency checks

The NumPy verifier tests both signs, several even dimensions, randomly conjugated orthogonal complex structures, and explicit degenerate configurations.

It checks the vector identity, equality of norms, and orthogonality.

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r verify/requirements.txt
python verify/verify_van_aubel.py
```

The dimensions, number of trials, seed, and tolerance are configurable:

```bash
python verify/verify_van_aubel.py \
  --dimensions 2 4 8 \
  --trials 1000 \
  --seed 42 \
  --tolerance 1e-10
```

These randomized checks are supplementary consistency tests, while the Lean development is the formal proof.

## Interactive demonstration

Open [`simple_demo/van-aubel-multidimensional-lab.html`](simple_demo/van-aubel-multidimensional-lab.html) in a browser.

The standalone page supports draggable planar configurations, both orientation signs, degenerate examples, and experiments in multiple even dimensions.

It does not load external scripts, fonts, stylesheets, or other remote resources.

The same HTML file is both the editable source and the directly distributable standalone page.

## Citation

If you use this work, please cite mindofcharles and the project *Van-Aubel-Extensions*.

Machine-readable citation metadata, including the author ORCID, is available in [`CITATION.cff`](CITATION.cff).

## License

This repository has two licensed components:

- Lean 4 Source Code, Executable Scripts, Interactive Demonstration, and Project Configuration are licensed under the [Apache License 2.0](LICENSE_apache-2.0.txt);
- mathematical notes, research articles, and Markdown documentation are licensed under [Creative Commons Attribution 4.0 International](LICENSE_cc-by-4.0.txt).

See [`LICENSE.txt`](LICENSE.txt) and [`NOTICE.txt`](NOTICE.txt) for the repository-level licensing notice.
