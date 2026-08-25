# Complex-Affine Naturality and Transfer of the Van Aubel Center Construction

## Abstract

The Van Aubel center construction is a complex-affine operation once a real vector space is equipped with a complex structure. This note develops that observation in three distinct forms. First, individual edge centers and the four-center identity are natural under arbitrary complex-affine maps. Second, every expression built from fixed complex-affine combinations has a coefficient normal form, so universal equality on the complex affine line implies equality in every complex affine space. Third, the construction and identity admit a precise formulation by natural transformations in the category of complex affine spaces. The note also separates algebraic transport from metric preservation and records the geometric, metric, conjugate-linear, incidence, and nonlinear statements that do not follow from the affine-term transfer theorem.

---

## 1. The Complex-Affine Setting

The underlying center identity and its Euclidean interpretation are developed in [*Van Aubel as a Complex-Structure Identity*](van-aubel-complex-structure-identity.md). The classification of alternative edge-operator realizations is developed separately in [*Edge-Operator Realizations and Rigidity of the Van Aubel Center Identity*](van-aubel-edge-operator-realizations-and-rigidity.md). The present note isolates the naturality and transfer theory common to those realizations.

Let $V$ be a real vector space and let

$$
J:V\longrightarrow V
$$

be real-linear with

$$
J^2=-I.
$$

Define complex scalar multiplication by

$$
(a+ib)v=av+bJv.
$$

The relation $J^2=-I$ supplies the multiplication law because

$$
(aI+bJ)(cI+dJ)
=(ac-bd)I+(ad+bc)J.
$$

Thus $V$ is a complex vector space, with multiplication by $i$ represented by $J$.

A **complex affine space** $(E,V,J)$ is a real affine space $E$ modeled on such a vector space. If complex coefficients

$$
\lambda_1,\ldots,\lambda_q
$$

satisfy

$$
\sum_{r=1}^q\lambda_r=1,
$$

then the affine combination

$$
\sum_{r=1}^q\lambda_rX_r
$$

is intrinsic: after choosing an origin it has the displayed coordinate form, and the condition on the coefficient sum makes the resulting point independent of that origin.

Fix

$$
\varepsilon\in\{+1,-1\}
$$

and put

$$
\alpha_\varepsilon=\frac{1+\varepsilon i}{2}.
$$

For a directed edge $XY$, define its center by

$$
M_\varepsilon^J(X,Y)
=X+\frac{(Y-X)+\varepsilon J(Y-X)}{2}.
$$

Through the complex scalar action induced by $J$, this becomes

$$
\boxed{
M_\varepsilon^J(X,Y)
=X+\alpha_\varepsilon(Y-X)}.
$$

After choosing an origin, the same point has the complex-affine normal form

$$
\boxed{
M_\varepsilon^J(X,Y)
=(1-\alpha_\varepsilon)X+\alpha_\varepsilon Y}.
$$

The two coefficients sum to $1$, so this coordinate expression is intrinsic in the affine sense just described.

---

## 2. Naturality of Individual Edge Centers

Let $(E,V,J)$ and $(E',W,K)$ be complex affine spaces. An affine map

$$
F:E\longrightarrow E'
$$

has a real-linear part

$$
T:V\longrightarrow W
$$

characterized by

$$
F(X+v)=F(X)+T(v).
$$

The map $F$ is **complex affine** precisely when

$$
\boxed{TJ=KT}.
$$

Equivalently, $T$ is complex-linear for the complex structures defined by $J$ and $K$.

### Theorem 1: naturality of the center construction

For every complex-affine map $F$ and every $X,Y\in E$,

$$
\boxed{
F\bigl(M_\varepsilon^J(X,Y)\bigr)
=M_\varepsilon^K\bigl(F(X),F(Y)\bigr)}.
$$

### Proof

Using the linear part $T$ of $F$ and the intertwining relation $TJ=KT$,

$$
\begin{aligned}
F\bigl(M_\varepsilon^J(X,Y)\bigr)
&=F(X)
  +\frac{T(Y-X)+\varepsilon TJ(Y-X)}{2} \\
&=F(X)
  +\frac{(F(Y)-F(X))
  +\varepsilon K(F(Y)-F(X))}{2} \\
&=M_\varepsilon^K\bigl(F(X),F(Y)\bigr).
\end{aligned}
$$

No injectivity, surjectivity, or metric assumption is used. $\square$

Applying Theorem 1 to four directed edges shows that the four-center construction

$$
(A,B,C,D)\longmapsto(P,Q,R,S)
$$

commutes with every complex-affine map.

### Edge parallelograms and squares

Let

$$
u=Y-X.
$$

The four vertices associated with the edge are

$$
X,\qquad
Y,\qquad
Y+\varepsilon Ju,\qquad
X+\varepsilon Ju.
$$

Their images under $F$ are

$$
\begin{aligned}
F(X),\qquad
F(Y),\qquad
F(Y)+\varepsilon K(Tu),\qquad
F(X)+\varepsilon K(Tu).
\end{aligned}
$$

Thus the edge parallelogram defined by $J$ is carried to the corresponding edge parallelogram defined by $K$. If $K$ is orthogonal and $Tu\neq0$, the image is a $K$-square in the real plane

$$
\operatorname{span}\{Tu,K(Tu)\}.
$$

If $Tu=0$, then $F(X)=F(Y)$ and the image degenerates to a single point. If $J$ is orthogonal as well, the source parallelogram is itself a square. Hence a complex-affine map between orthogonal realizations sends each constructed square to a square that may be degenerate, even when the map is not an isometry.

---

## 3. Naturality of the Four-Center Identity

Given $A,B,C,D\in E$, put

$$
\begin{aligned}
P&=M_\varepsilon^J(A,B), &
Q&=M_\varepsilon^J(B,C), \\
R&=M_\varepsilon^J(C,D), &
S&=M_\varepsilon^J(D,A).
\end{aligned}
$$

Let

$$
A'=F(A),\qquad B'=F(B),\qquad
C'=F(C),\qquad D'=F(D),
$$

and construct $P',Q',R',S'$ from these four target points using $K$. By Theorem 1,

$$
P'=F(P),\qquad Q'=F(Q),\qquad
R'=F(R),\qquad S'=F(S).
$$

### Theorem 2: naturality of the center identity

If

$$
R-P=\varepsilon J(S-Q),
$$

then

$$
\boxed{R'-P'=\varepsilon K(S'-Q')}.
$$

### Proof

The difference of two images under an affine map is obtained by applying its linear part to the source difference. Therefore,

$$
\begin{aligned}
R'-P'
&=F(R)-F(P) \\
&=T(R-P) \\
&=\varepsilon TJ(S-Q) \\
&=\varepsilon KT(S-Q) \\
&=\varepsilon K\bigl(F(S)-F(Q)\bigr) \\
&=\varepsilon K(S'-Q').
\end{aligned}
$$

This proves the target relation. $\square$

The theorem is a **pointwise naturality statement**. It transports the identity for a fixed source quadruple to the image quadruple. If $F$ is not surjective, naturality alone says nothing about target quadruples outside the image of $F$. The universal center identity in the target is established independently by its coefficient formula, not by assuming that a particular map $F$ reaches every target point.

---

## 4. Algebraic Transport and Metric Preservation

Three different claims should be kept separate:

1. the center construction and identity are transported algebraically;
2. the image configuration has a square and metric interpretation in the target;
3. numerical distances and inner products are preserved from source to target.

They require different hypotheses.

### 4.1 Algebraic transport

The relation

$$
TJ=KT
$$

is sufficient for Theorems 1 and 2. It does not require an inner product on either space and does not require $T$ to be injective or surjective.

### 4.2 Metric re-realization in the target

If $K$ is orthogonal, every target vector $w$ satisfies

$$
|Kw|=|w|,
\qquad
\langle Kw,w\rangle=0.
$$

Consequently, the transported relation

$$
R'-P'=\varepsilon K(S'-Q')
$$

implies

$$
|R'-P'|=|S'-Q'|,
\qquad
\langle R'-P',S'-Q'\rangle=0.
$$

These are metric facts newly realized in the target. They do not assert that the corresponding target lengths equal the source lengths.

For example, on $\mathbb C$ with its standard complex structure, the map

$$
T(z)=2z
$$

is complex-linear and sends every constructed square to a square, but it doubles every nonzero length.

### 4.3 Preservation of source metric data

To preserve all distances between source points, $T$ must be an isometric embedding:

$$
|T(v)|=|v|
\qquad
\text{for every }v\in V.
$$

By real polarization, this is equivalent to preserving all inner products of displacement vectors. Since $T$ is already complex-linear, it is then a complex-linear isometric embedding. If it is also surjective, it is a complex-linear isometric isomorphism, or a unitary isomorphism when the orthogonal complex structures are viewed through their associated Hermitian inner products.

### 4.4 Why source orthogonality is insufficient

The equation $J^2=-I$ alone does not control a given metric. For $a>0$ with $a\neq1$, define on $\mathbb R^2$

$$
J_a(x,y)=(-ay,x/a).
$$

Then

$$
J_a^2=-I,
$$

but

$$
|J_a(1,0)|=\frac1a\neq1
$$

and

$$
\langle(1,1),J_a(1,1)\rangle
=-a+\frac1a\neq0.
$$

There is also a direct example in which the source structure is orthogonal while the target structure is not. Let

$$
J_0(x,y)=(-y,x),
\qquad
T(x,y)=(2x,y),
$$

and put

$$
K=TJ_0T^{-1}.
$$

Then

$$
K(x,y)=(-2y,x/2),
\qquad
TJ_0=KT.
$$

The source structure $J_0$ is orthogonal, whereas $K=J_2$ is not. Thus complex-affine naturality transports the algebraic construction, but orthogonality in the source alone cannot supply a target-space metric interpretation.

---

## 5. Normal Forms for Complex-Affine Terms

Fix point variables

$$
X_1,\ldots,X_m.
$$

A **complex-affine term** is built recursively as follows:

- each variable $X_j$ is a term;
- if $t_1,\ldots,t_q$ are terms and fixed coefficients
  $\lambda_1,\ldots,\lambda_q\in\mathbb C$ satisfy

  $$
  \sum_{r=1}^q\lambda_r=1,
  $$

  then

  $$
  \sum_{r=1}^q\lambda_rt_r
  $$

  is a term.

All coefficients are fixed independently of the input points.

### Theorem 3: affine-term normal form

Every complex-affine term has a normal form

$$
\boxed{
t(X_1,\ldots,X_m)
=\sum_{j=1}^m c_jX_j,
\qquad
\sum_{j=1}^m c_j=1,}
$$

where $c_1,\ldots,c_m\in\mathbb C$ depend only on the term.

The coefficient vector is unique in the universal sense: if two normal forms agree for all inputs in the complex affine line $\mathbb C$, then their corresponding coefficients are equal.

### Proof

Existence follows by structural induction. A variable $X_j$ has the $j$th unit coefficient vector, whose entries sum to $1$. Suppose terms $t_r$ have normal forms

$$
t_r=\sum_{j=1}^m c_{rj}X_j,
\qquad
\sum_{j=1}^m c_{rj}=1.
$$

If

$$
t=\sum_{r=1}^q\lambda_rt_r,
\qquad
\sum_{r=1}^q\lambda_r=1,
$$

then

$$
\begin{aligned}
t
&=\sum_{r=1}^q\lambda_r
  \sum_{j=1}^m c_{rj}X_j \\
&=\sum_{j=1}^m
  \left(\sum_{r=1}^q\lambda_rc_{rj}\right)X_j.
\end{aligned}
$$

The new coefficients sum to

$$
\begin{aligned}
\sum_{j=1}^m\sum_{r=1}^q\lambda_rc_{rj}
&=\sum_{r=1}^q\lambda_r
  \sum_{j=1}^m c_{rj} \\
&=\sum_{r=1}^q\lambda_r \\
&=1.
\end{aligned}
$$

This proves existence.

For universal uniqueness, suppose

$$
\sum_{j=1}^m c_jX_j
=\sum_{j=1}^m d_jX_j
$$

for every $(X_1,\ldots,X_m)\in\mathbb C^m$. Choose $0$ as origin. For each $j$, set $X_j=1$ and set all other variables equal to $0$. The resulting equality is

$$
c_j=d_j.
$$

Thus the coefficient vectors agree. $\square$

---

## 6. The Universal Affine-Term Transfer Theorem

The normal form gives a transfer principle that is different from transport along a particular map.

### Theorem 4: universal complex-affine transfer

For two complex-affine terms $t$ and $s$ in the same point variables, the following are equivalent:

1. $t=s$ for every input in the complex affine line $\mathbb C$;
2. $t$ and $s$ have the same coefficient vector;
3. $t=s$ for every input in every complex affine space.

### Proof

Theorem 3 proves that the first condition forces equality of the coefficient vectors. Equal coefficient vectors plainly define the same affine combination in every complex affine space, so the second condition implies the third. The third condition implies the first by taking the complex affine space to be $\mathbb C$. $\square$

The theorem says precisely:

> A universal identity genuinely expressible as an equality of complex-affine terms is dimension-free and is determined entirely by its fixed complex coefficients.

### Vector-valued identities

A point-valued affine normal form has coefficient sum $1$. A vector-valued expression obtained from differences of point terms has coefficient sum $0$. Such a sum is also independent of the choice of origin, because translating every point by the same vector contributes the coefficient sum times that translation vector.

Thus vector identities are covered by the same coefficient method after both sides are moved into the translation vector space.

### The Van Aubel identity as a coefficient identity

For

$$
\alpha=\alpha_\varepsilon
=\frac{1+\varepsilon i}{2},
$$

the four centers are

$$
\begin{aligned}
P&=(1-\alpha)A+\alpha B, &
Q&=(1-\alpha)B+\alpha C, \\
R&=(1-\alpha)C+\alpha D, &
S&=(1-\alpha)D+\alpha A.
\end{aligned}
$$

Relative to the ordered variables $(A,B,C,D)$, the coefficient vector of $R-P$ is

$$
\bigl(-(1-\alpha),-\alpha,1-\alpha,\alpha\bigr).
$$

The coefficient vector of $\varepsilon i(S-Q)$ is

$$
\bigl(
\varepsilon i\alpha,
-\varepsilon i(1-\alpha),
-\varepsilon i\alpha,
\varepsilon i(1-\alpha)
\bigr).
$$

The defining value of $\alpha$ gives

$$
\varepsilon i\alpha=-(1-\alpha),
\qquad
\varepsilon i(1-\alpha)=\alpha.
$$

Hence the two coefficient vectors agree, proving

$$
\boxed{R-P=\varepsilon i(S-Q)}
$$

in every complex affine space. Under the real description $iv=Jv$, this is

$$
\boxed{R-P=\varepsilon J(S-Q)}.
$$

This calculation isolates the dimension-free algebraic content of the Van Aubel center identity.

### Pointwise naturality versus universal transfer

The two mechanisms should not be conflated:

- **Pointwise naturality** uses a particular complex-affine map $F:E\to E'$ and transports an equality from a source tuple to its image tuple.
- **Universal transfer** compares coefficient vectors. It needs no map between the two spaces and establishes an identity for every tuple in every complex affine space.

Surjectivity matters if one tries to deduce a universal target statement solely from a particular map. It plays no role in the coefficient theorem.

---

## 7. Limits of the Transfer Principle

Theorem 4 applies only to identities genuinely constructed from fixed complex-affine combinations. It does not automatically transfer every statement that can be drawn in a plane.

- **Order, sidedness, and exterior regions.** A notion such as the exterior side of a directed edge is not intrinsic to an abstract complex affine space and has no direct higher-dimensional affine-term interpretation.

- **Incidence and intersection.** The existence or uniqueness of an intersection point is an existential statement, not an equality of fixed-coefficient affine terms. In $\mathbb R^4$, for example,

  $$
  \ell_1=\{te_1:t\in\mathbb R\},
  \qquad
  \ell_2=\{e_3+se_2:s\in\mathbb R\}
  $$

  have perpendicular direction vectors but are disjoint.

- **Complex conjugation.** A bare complex vector space has no canonical conjugation. Conjugate-linear constructions require additional real-form data or a specified conjugation, together with morphisms that preserve that data.

- **Norms and angles.** Equalities involving norms, inner products, or angles require metric structure. Algebraic transport yields a relation involving the target complex structure, but metric conclusions require that target structure to be orthogonal.

- **Nonlinear operations.** Normalization, products of input-dependent coordinates, variable ratios, and coefficients determined by the input points are not complex-affine terms with fixed coefficients.

- **Rank, independence, and dimension-dependent assertions.** Linear independence, nondegeneracy, and dimension bounds are not coefficient equalities. They require separate arguments and may be destroyed by noninjective maps.

For a nonzero edge vector $u$, the vectors $u$ and $Ju$ are real-linearly independent, so the construction selects the real plane

$$
\operatorname{span}\{u,Ju\}.
$$

This plane is intrinsic once $J$ is chosen, but its metric square interpretation and its relation to ambient intersections remain additional geometric information.

---

## 8. Categorical Formulation

The preceding naturality statements can be organized in one category without changing their mathematical content.

Let $\mathbf{CAff}$ be the category whose objects are complex affine spaces and whose morphisms are complex-affine maps. For every positive integer $m$, let

$$
\mathcal P_m:\mathbf{CAff}\longrightarrow\mathbf{CAff}
$$

be the power functor

$$
\mathcal P_m(E)=E^m,
\qquad
\mathcal P_m(F)=F^m.
$$

### 8.1 The four-center natural transformation

For each object $(E,V,J)$, define

$$
\mathcal C_{\varepsilon,E}:E^4\longrightarrow E^4
$$

by

$$
\mathcal C_{\varepsilon,E}(A,B,C,D)=(P,Q,R,S),
$$

where the four centers are constructed using $J$ and $\varepsilon$. Each component $\mathcal C_{\varepsilon,E}$ is a complex-affine map because each of its four coordinates is a fixed complex-affine combination. Theorem 1 says exactly that these components form a natural transformation

$$
\boxed{
\mathcal C_\varepsilon:
\mathcal P_4\Longrightarrow\mathcal P_4}.
$$

Indeed, for every complex-affine $F:E\to E'$, the naturality square is the identity

$$
F^4\circ\mathcal C_{\varepsilon,E}
=\mathcal C_{\varepsilon,E'}\circ F^4.
$$

### 8.2 The translation-space functor

Let $\mathbf{CVec}$ be the category of complex vector spaces and complex-linear maps. Define

$$
\mathcal V:\mathbf{CAff}\longrightarrow\mathbf{CVec}
$$

by sending a complex affine space to its complex translation vector space and a complex-affine map to its complex-linear part.

Let

$$
\iota:\mathbf{CVec}\longrightarrow\mathbf{CAff}
$$

regard a complex vector space as its underlying affine space, and set

$$
\widetilde{\mathcal V}
=\iota\circ\mathcal V.
$$

For every $E$, the difference map

$$
d_E:E\times E\longrightarrow\widetilde{\mathcal V}(E),
\qquad
d_E(X,Y)=Y-X,
$$

is complex affine. These maps form a natural transformation

$$
\boxed{
d:\mathcal P_2\Longrightarrow\widetilde{\mathcal V}},
$$

because an affine map with complex-linear part $T$ satisfies

$$
d_{E'}\bigl(F(X),F(Y)\bigr)
=F(Y)-F(X)
=T(Y-X)
=\widetilde{\mathcal V}(F)\bigl(d_E(X,Y)\bigr).
$$

Multiplication by $i$ on each translation space defines a natural endomorphism

$$
\mathfrak i:
\widetilde{\mathcal V}
\Longrightarrow
\widetilde{\mathcal V},
$$

since every complex-linear map commutes with multiplication by $i$.

### 8.3 The identity as equality of natural transformations

Compose the four-center transformation with the relevant coordinate projections and the difference transformation. For

$$
\mathcal C_{\varepsilon,E}(A,B,C,D)=(P,Q,R,S),
$$

define

$$
\Phi_E(A,B,C,D)=R-P
$$

and

$$
\Psi_E(A,B,C,D)=\varepsilon J(S-Q).
$$

The constructions above show that

$$
\Phi,\Psi:
\mathcal P_4
\Longrightarrow
\widetilde{\mathcal V}
$$

are natural transformations. The Van Aubel center identity is exactly the equality

$$
\boxed{\Phi=\Psi}.
$$

Equivalently, one may avoid the explicit translation-space codomain by rewriting the vector relation as the point-valued equation

$$
R=P+\varepsilon J(S-Q).
$$

The categorical formulation clarifies the types of the objects involved and packages the commuting constructions. It is not a substitute for the elementary center calculation or the coefficient proof, and it does not strengthen those results.

---

## 9. Final Perspective

The Van Aubel center construction exhibits two complementary forms of dimension-free behavior:

$$
\text{complex-affine naturality}
\qquad\text{and}\qquad
\text{coefficient-based universal transfer}.
$$

Naturality describes how the construction behaves along a particular complex-affine map. The affine-term theorem describes when a fixed-coefficient identity holds in every complex affine space, whether or not any map between two chosen spaces is available. Orthogonal complex structures then supply a metric realization of the transported algebra, while isometric or unitary hypotheses are needed to preserve numerical metric data between spaces.

The categorical language records these relationships as natural transformations in $\mathbf{CAff}$. The coefficient normal form supplies the actual universal transfer mechanism, and the explicit scope restrictions mark the boundary between complex-affine algebra and additional geometry.
