# Van Aubel as a Complex-Structure Identity

## 1. Structural Viewpoint

The purpose of this note is not primarily to move Van Aubel's theorem from the plane into a higher-dimensional Euclidean space. The main point is that the familiar planar phenomenon is governed by a more basic algebraic structure.

Let $V$ be a real vector space and let

$$
J:V\longrightarrow V
$$

be a linear operator satisfying

$$
J^2=-I.
$$

Then $V$ becomes a complex vector space if multiplication by $i$ is defined by

$$
iv=Jv.
$$

More generally,

$$
(a+ib)v=av+bJv
$$

for $a,b\in\mathbb R$ and $v\in V$.

Indeed,

$$
(aI+bJ)(cI+dJ)
=(ac-bd)I+(ad+bc)J.
$$

Thus the assignment $a+ib\mapsto aI+bJ$ respects addition and multiplication and sends $1$ to $I$. Together with the real vector-space operations, this verifies the complex scalar-multiplication axioms.

The central identity of this note is

$$
\boxed{R-P=\varepsilon J(S-Q)}.
$$

At this algebraic level, the identity requires only $J^2=-I$. If $V$ is additionally equipped with an inner product for which $J$ is orthogonal, then $J$ acts as a quarter-turn on every $J$-invariant real two-plane. The usual equal-length and perpendicularity conclusions of Van Aubel's theorem then follow from the single vector identity above.

Thus the logical order is:

$$
\text{complex structure}
\;\Longrightarrow\;
\text{center identity}
\;\Longrightarrow\;
\text{metric consequences}.
$$

The classical planar theorem is the canonical two-dimensional realization of this structure, rather than the sole setting in which the identity makes sense.

---

## 2. The Algebraic Center Construction

Let $E$ be an affine space modeled on $V$. Differences of points in $E$ are vectors in $V$, and vectors in $V$ act on points of $E$ by translation.

Fix one sign

$$
\varepsilon\in\{+1,-1\}.
$$

For a directed edge $XY$, put

$$
u=Y-X.
$$

Using the same operator $J$ and the same sign $\varepsilon$, consider the four points

$$
X,\qquad
Y,\qquad
Y+\varepsilon Ju,\qquad
X+\varepsilon Ju.
$$

They form a parallelogram whose center is

$$
M_{XY}
=X+\frac{(Y-X)+\varepsilon J(Y-X)}{2}.
$$

At this stage no inner product is needed. When $J$ is orthogonal, this parallelogram is a square; that geometric interpretation will be established in Section 4.

Let

$$
A,B,C,D\in E
$$

be any four ordered points. They need not be distinct or coplanar. Define

$$
P=M_{AB},\qquad
Q=M_{BC},\qquad
R=M_{CD},\qquad
S=M_{DA}.
$$

The theorem below assumes that the same $J$ and the same $\varepsilon$ are used on all four edges. Arbitrary mixed choices generally destroy the identity, but this hypothesis should not be read as an unrestricted rigidity claim. The exact rigidity question is formulated by assigning a real-linear operator $L$ to an edge and writing

$$
M_L(X,Y)
=X+\frac{(Y-X)+L(Y-X)}{2}.
$$

The companion note [*Edge-Operator Realizations and Rigidity of the Van Aubel Center Identity*](van-aubel-edge-operator-realizations-and-rigidity.md) classifies every quadruple of edge operators that produces a fixed target relation universally. Three consequences are relevant here. First, fix a target sign $\delta\in\{+1,-1\}$ and a complex structure $J$ on a nonzero real vector space $V$. If independently chosen signs $\varepsilon_k\in\{+1,-1\}$ on the four edges satisfy

$$
R-P=\delta J(S-Q)
$$

for every ordered quadruple, then all four signs equal $\delta$. Second, if a fixed target $K$ and the four edge operators are orthogonal complex structures, the universal relation $R-P=K(S-Q)$ forces every edge operator to equal $K$. Third, in finite dimensions and without orthogonality, nonconstant complex-structure realizations exist beginning in real dimension four, whereas real dimension two remains rigid. The nonzero assumption is needed only for sign rigidity: on the zero vector space all sign choices are indistinguishable. The universal quantifier is essential throughout, since a special quadruple may satisfy an accidental mixed relation.

---

## 3. The Complex-Structure Center Identity

### Theorem

Let $E$ be an affine space modeled on a real vector space $V$, and let $J:V\to V$ be linear with

$$
J^2=-I.
$$

For the four centers defined above,

$$
\boxed{R-P=\varepsilon J(S-Q)}.
$$

### Proof

Introduce the two diagonal vectors

$$
x=C-A,
\qquad
y=D-B.
$$

Choose an arbitrary origin in $E$ and temporarily identify points of $E$ with their position vectors in $V$. Every final expression is a difference of points, so the calculation is independent of this choice.

From the definitions,

$$
P=\frac{A+B+\varepsilon J(B-A)}{2}
$$

and

$$
R=\frac{C+D+\varepsilon J(D-C)}{2}.
$$

Therefore,

$$
\begin{aligned}
2(R-P)
&=x+y+\varepsilon J(y-x) \\
&=(I-\varepsilon J)x+(I+\varepsilon J)y.
\end{aligned}
$$

Similarly,

$$
Q=\frac{B+C+\varepsilon J(C-B)}{2}
$$

and

$$
S=\frac{D+A+\varepsilon J(A-D)}{2},
$$

so

$$
\begin{aligned}
2(S-Q)
&=y-x-\varepsilon J(x+y) \\
&=-(I+\varepsilon J)x+(I-\varepsilon J)y.
\end{aligned}
$$

Since $\varepsilon^2=1$ and $J^2=-I$,

$$
\begin{aligned}
\varepsilon J(I-\varepsilon J)&=I+\varepsilon J, \\
\varepsilon J(I+\varepsilon J)&=-(I-\varepsilon J).
\end{aligned}
$$

Applying $\varepsilon J$ to the formula for $2(S-Q)$ gives

$$
\begin{aligned}
2\varepsilon J(S-Q)
&=-\varepsilon J(I+\varepsilon J)x
  +\varepsilon J(I-\varepsilon J)y \\
&=(I-\varepsilon J)x+(I+\varepsilon J)y \\
&=2(R-P).
\end{aligned}
$$

Hence

$$
\boxed{R-P=\varepsilon J(S-Q)}.
$$

The proof uses only affine linear operations, the common operator $J$, and the relation $J^2=-I$.

---

## 4. Orthogonal Complex Structures and Squares

Now suppose that $V$ is a real inner-product space and that $J$ is orthogonal:

$$
\langle Ju,Jv\rangle=\langle u,v\rangle
\qquad
\text{for all }u,v\in V.
$$

Together with $J^2=-I$, this makes $J$ an **orthogonal complex structure**. Since

$$
v=-J(Jv),
$$

orthogonality and the symmetry of the real inner product give

$$
\begin{aligned}
\langle Jv,v\rangle
&=-\langle Jv,J(Jv)\rangle \\
&=-\langle v,Jv\rangle \\
&=-\langle Jv,v\rangle,
\end{aligned}
$$

and hence

$$
\boxed{\langle Jv,v\rangle=0}.
$$

Orthogonality also gives

$$
\boxed{|Jv|=|v|}.
$$

Thus $v$ and $Jv$ are perpendicular and have the same length. For a nonzero edge vector $u$, the parallelogram from Section 2 is therefore a square in the affine plane

$$
X+\operatorname{span}\{u,Ju\}.
$$

If $u=0$, all four vertices coincide. Treating this as a degenerate square keeps the construction valid without requiring distinct vertices.

The center identity now yields

$$
\begin{aligned}
|R-P|
&=|\varepsilon J(S-Q)| \\
&=|S-Q|
\end{aligned}
$$

and

$$
\begin{aligned}
\langle R-P,S-Q\rangle
&=\varepsilon\langle J(S-Q),S-Q\rangle \\
&=0.
\end{aligned}
$$

Therefore,

$$
\boxed{|R-P|=|S-Q|}
$$

and

$$
\boxed{\langle R-P,S-Q\rangle=0}.
$$

These are not two unrelated coincidences: both are metric shadows of the stronger relation

$$
R-P=\varepsilon J(S-Q).
$$

If one vector is zero, then both are zero. The inner-product statement remains valid, although zero-length segments should not be described as meeting at a right angle.

---

## 5. The Classical Planar Van Aubel Theorem

In an oriented Euclidean plane, there is a unique orthogonal complex structure $J$ compatible with the orientation; it rotates every vector counterclockwise through $90^\circ$. Indeed, for a positively oriented orthonormal basis $e_1,e_2$, orthogonality and $J^2=-I$ imply that $Je_1$ is one of the two unit vectors perpendicular to $e_1$. Compatibility with the orientation forces

$$
Je_1=e_2,
$$

and then $J^2=-I$ gives

$$
Je_2=-e_1.
$$

These values determine $J$ uniquely.

For a simple planar quadrilateral whose vertices $A,B,C,D$ are listed in boundary order, one fixed sign places all four squares on the exterior sides of the directed edges. If $J$ is the counterclockwise quarter-turn and the boundary is traversed counterclockwise, the interior lies locally to the left of each directed edge, so the exterior construction uses $\varepsilon=-1$. For clockwise traversal it uses $\varepsilon=+1$. Here “exterior” means the side locally opposite the polygon interior; for a concave quadrilateral an exterior square may still overlap another part of the figure. The algebraic identity itself does not require simplicity, distinct vertices, or an exterior-side convention.

In this setting the center identity becomes

$$
\overrightarrow{PR}=\varepsilon J\overrightarrow{QS}.
$$

It immediately implies the traditional Van Aubel conclusions

$$
|\overline{PR}|=|\overline{QS}|
$$

and

$$
\overline{PR}\perp\overline{QS}.
$$

Hence the classical theorem is the real two-dimensional, or complex one-dimensional, manifestation of the complex-structure center identity. The point is not merely that the theorem survives in higher dimensions. Rather, its two planar metric conclusions originate from one structural equation involving multiplication by $i$.

Under the identification

$$
V=\mathbb R^2\cong\mathbb C,
$$

the equation is simply

$$
\boxed{\overrightarrow{PR}=\varepsilon i\,\overrightarrow{QS}}.
$$

---

## 6. A Derived $J$-Parallelogram from the Four Centers

The main identity produces another natural algebraic configuration that is not part of the original construction. Its Euclidean square interpretation requires the additional assumption that $J$ is orthogonal.

Let $U_1,U_2,U_3,U_4$ be the midpoints of the four successive sides of the center quadrilateral $PQRS$:

$$
\begin{aligned}
U_1&=P+\frac{Q-P}{2}, &
U_2&=Q+\frac{R-Q}{2}, \\
U_3&=R+\frac{S-R}{2}, &
U_4&=S+\frac{P-S}{2}.
\end{aligned}
$$

Each formula is intrinsic: the fraction is a vector, which then acts on the preceding point by translation.

By the midpoint construction,

$$
U_2-U_1=\frac{R-P}{2}
$$

and

$$
U_3-U_2=\frac{S-Q}{2}.
$$

The center identity therefore gives

$$
\boxed{U_2-U_1=\varepsilon J(U_3-U_2)}.
$$

Equivalently,

$$
U_3-U_2=-\varepsilon J(U_2-U_1).
$$

Moreover, direct calculation from the midpoint definitions gives

$$
\begin{aligned}
U_3-U_4
&=\frac{R+S}{2}-\frac{S+P}{2}
=\frac{R-P}{2}
=U_2-U_1, \\
U_4-U_1
&=\frac{S+P}{2}-\frac{P+Q}{2}
=\frac{S-Q}{2}
=U_3-U_2.
\end{aligned}
$$

Thus $U_1U_2U_3U_4$ is a parallelogram. If

$$
a=U_2-U_1,
\qquad
b=U_3-U_2,
$$

are its successive adjacent side vectors, then

$$
b=-\varepsilon Ja,
$$

or equivalently $a=\varepsilon Jb$. We call this algebraic configuration a $J$-parallelogram. Without an inner product and the orthogonality of $J$, the operator $J$ should not be interpreted as a metric quarter-turn. If $J$ is orthogonal, then $a$ and $b$ are perpendicular and have the same length, so $U_1U_2U_3U_4$ is a square, possibly degenerate.

This conclusion is a direct structural consequence of the identity: the four original centers generate a new $J$-parallelogram through their side midpoints and, in the orthogonal setting, a new square.

---

## 7. Even-Dimensional Euclidean Realizations

The algebraic identity is formulated for any real vector space already equipped with an operator $J$ satisfying $J^2=-I$. In finite dimensions, the existence of such an operator forces the real dimension to be even.

If $\dim_{\mathbb R}V=m$, then

$$
\begin{aligned}
(\det J)^2
&=\det(J^2) \\
&=\det(-I) \\
&=(-1)^m.
\end{aligned}
$$

The left-hand side is nonnegative, so $m$ cannot be odd.

Conversely, every even-dimensional Euclidean space admits an orthogonal complex structure. Given an orthonormal basis

$$
e_1,e_2,\ldots,e_{2n},
$$

define

$$
Je_{2k-1}=e_{2k},
\qquad
Je_{2k}=-e_{2k-1}
$$

for $k=1,\ldots,n$. Then $J^2=-I$ and $J$ is orthogonal. On $\mathbb R^{2n}$ this is

$$
J(x_1,x_2,\ldots,x_{2n-1},x_{2n})
=(-x_2,x_1,\ldots,-x_{2n},x_{2n-1}).
$$

This fact supplies many higher-dimensional realizations of the same structure, but it is not the conceptual starting point of the theorem.

There is also an important distinction between dimension two and higher even dimensions. In an oriented Euclidean plane, the metric and orientation determine $J$ uniquely. In real dimension $2n\geq4$, this is no longer true. To see this explicitly, take the orthonormal basis above to be positively oriented and let $J$ be the displayed standard complex structure. Define $J'$ by

$$
J'\big|_{\operatorname{span}\{e_1,e_2,e_3,e_4\}}
=-J\big|_{\operatorname{span}\{e_1,e_2,e_3,e_4\}},
\qquad
J'\big|_{\operatorname{span}\{e_5,\ldots,e_{2n}\}}
=J\big|_{\operatorname{span}\{e_5,\ldots,e_{2n}\}}.
$$

For $n=2$, the second summand is absent. The operator $J'$ is orthogonal, satisfies $(J')^2=-I$, and differs from $J$. Reversing $J$ on each of the first two real two-dimensional blocks changes the induced orientation twice, so $J'$ and $J$ induce the same orientation. Thus the metric and orientation do not determine a unique complex structure in higher even dimensions.

The effect of changing the complex structure on an edge is measured exactly by

$$
M^{J}_{XY}-M^{J'}_{XY}
=\frac{\varepsilon}{2}(J-J')(Y-X).
$$

Consequently, if an edge vector $u=Y-X$ satisfies $Ju\neq J'u$, the two center constructions, and hence the two squares on that edge, are different.

---

## 8. Complex-Affine Naturality and Transfer

The relation $J^2=-I$ makes $V$ a complex vector space. Put

$$
\alpha_\varepsilon=\frac{1+\varepsilon i}{2}.
$$

The center construction then has the intrinsic complex-affine form

$$
M_\varepsilon^J(X,Y)
=X+\alpha_\varepsilon(Y-X).
$$

After choosing an origin, this may be written as

$$
M_\varepsilon^J(X,Y)
=(1-\alpha_\varepsilon)X+\alpha_\varepsilon Y.
$$

The coefficients sum to $1$, so the point is independent of that choice of origin.

Now let $(E,V,J)$ and $(E',W,K)$ be complex affine spaces, and let $F:E\to E'$ be affine with linear part $T:V\to W$ satisfying

$$
TJ=KT.
$$

Then the center construction is natural:

$$
\boxed{
F\bigl(M_\varepsilon^J(X,Y)\bigr)
=M_\varepsilon^K\bigl(F(X),F(Y)\bigr)}.
$$

Applying this equality on all four edges transports the center identity pointwise. If $P',Q',R',S'$ are the centers of the image quadruple, then

$$
\begin{aligned}
R'-P'
&=T(R-P) \\
&=\varepsilon TJ(S-Q) \\
&=\varepsilon K(S'-Q').
\end{aligned}
$$

No injectivity, surjectivity, or metric preservation is required. This is a pointwise statement: without surjectivity, a particular map does not by itself establish an identity for arbitrary target quadruples.

There is also a distinct universal transfer principle. Every point-valued expression built from fixed complex-affine combinations has a normal form

$$
t(X_1,\ldots,X_m)
=\sum_{j=1}^m c_jX_j,
\qquad
\sum_{j=1}^m c_j=1.
$$

Structural induction gives existence. If two such expressions agree for every input in the complex affine line $\mathbb C$, setting one variable at a time to $1$ and the others to $0$ shows that their coefficient vectors agree. Hence they agree in every complex affine space. Vector identities obtained from differences are covered by the corresponding coefficient-sum-$0$ normal forms.

The pointwise naturality theorem, the full normal-form proof, the distinction between algebraic transport and metric preservation, the limits of the transfer method, and the categorical formulation in $\mathbf{CAff}$ are developed in the companion note [*Complex-Affine Naturality and Transfer of the Van Aubel Center Construction*](van-aubel-complex-affine-naturality-and-transfer.md).

Metric conclusions still require separate hypotheses. In the target, $K$ must be orthogonal to turn the transported $K$-relation into equal-length and perpendicularity statements. The relation $J^2=-I$ alone is insufficient: for $a>0$ with $a\neq1$,

$$
J_a(x,y)=(-ay,x/a)
$$

satisfies $J_a^2=-I$, but

$$
|J_a(1,0)|=\frac1a\neq1,
\qquad
\langle(1,1),J_a(1,1)\rangle
=-a+\frac1a\neq0.
$$

To preserve all source distances rather than merely obtain a new metric realization in the target, $T$ must be a complex-linear isometric embedding; if it is surjective, it is a complex-linear isometric isomorphism, unitary in the orthogonal complex setting.

The transfer theorem applies only to fixed-coefficient complex-affine identities. Exterior regions, intersection assertions, complex conjugation without additional real structure, norms and angles, and nonlinear operations require separate arguments. For example, in $\mathbb R^4$ the lines $\ell_1=\{te_1:t\in\mathbb R\}$ and $\ell_2=\{e_3+se_2:s\in\mathbb R\}$ have perpendicular direction vectors but are disjoint. For a nonzero edge vector $u$, the relation $J^2=-I$ does at least imply that $u$ and $Ju$ are real-linearly independent: otherwise $Ju=\lambda u$ would give $-u=\lambda^2u$. Thus $J$ selects the real plane $\operatorname{span}\{u,Ju\}$, although its metric and ambient incidence properties are additional data.

Van Aubel's theorem is a particularly clean instance of the transfer viewpoint: its center relation is a fixed-coefficient complex-affine identity, and orthogonality supplies its Euclidean interpretation.

---

## 9. Final Formulation

> **Complex-structure center identity.**
>
> Let $E$ be an affine space modeled on a real vector space $V$, and let $J:V\to V$ be linear with $J^2=-I$. Let $A,B,C,D$ be any four ordered points of $E$, with coincidences allowed. Fix $\varepsilon\in\{+1,-1\}$, and on each directed edge $XY$ use the center
>
> $$
> M_{XY}=X+\frac{(Y-X)+\varepsilon J(Y-X)}{2}.
> $$
>
> If
>
> $$
> P=M_{AB},\qquad Q=M_{BC},\qquad
> R=M_{CD},\qquad S=M_{DA},
> $$
>
> then
>
> $$
> \boxed{R-P=\varepsilon J(S-Q)}.
> $$

If $V$ carries an inner product and $J$ is orthogonal, the four edge constructions are squares and

$$
\boxed{|R-P|=|S-Q|},
\qquad
\boxed{\langle R-P,S-Q\rangle=0}.
$$

The classical Van Aubel theorem is the canonical planar instance obtained from an oriented Euclidean plane. Higher even-dimensional examples are further realizations of the same complex-structure identity; orthogonality supplies its Euclidean square interpretation and its metric consequences.
