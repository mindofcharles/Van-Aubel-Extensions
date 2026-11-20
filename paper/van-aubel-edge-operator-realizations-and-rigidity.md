# Edge-Operator Realizations and Rigidity of the Van Aubel Center Identity

## Abstract

The Van Aubel center identity is usually constructed by applying the same signed complex structure to all four directed edges. This note classifies all quadruples of real-linear edge operators that realize a fixed target complex structure in the identity for every ordered quadruple of points. The complete family is parametrized by one endomorphism $N$. Requiring all four edge operators to be complex structures is equivalent to requiring that $N$ be square-zero and complex-antilinear. Independently chosen signs are rigid on every nonzero real vector space, and independently chosen orthogonal complex structures are rigid on every real inner-product space. In finite dimensions, nonconstant families without orthogonality exist beginning in real dimension four, while real dimension two remains rigid. The note also gives the configuration-dependent defect, the sixteen mixed-sign loci and their dimensions, a characterization for common edge operators, rank and unitary normal forms of the exceptional parameter, and an exact operator-norm formula.

---

## 1. The Realization Problem

The companion note [*Van Aubel as a Complex-Structure Identity*](van-aubel-complex-structure-identity.md) establishes the center relation

$$
R-P=\varepsilon J(S-Q)
$$

when the same complex structure $J$, satisfying $J^2=-I$, and the same sign $\varepsilon\in\{+1,-1\}$ are used on all four directed edges. The purpose here is to determine exactly how much freedom remains if the four edges are allowed to use different linear operators.

Let $E$ be an affine space modeled on a real vector space $V$. For a real-linear endomorphism

$$
L\in\operatorname{End}_{\mathbb R}(V),
$$

define

$$
M_L(X,Y)
=X+\frac{(Y-X)+L(Y-X)}{2}.
$$

This construction is affine: differences such as $Y-X$ are vectors in $V$, and the resulting vector acts on the point $X$ by translation. The signed complex-structure construction is the special case

$$
L=\varepsilon J,
\qquad
J^2=-I.
$$

Allow four potentially different edge operators and put

$$
P=M_{L_1}(A,B),\qquad
Q=M_{L_2}(B,C),\qquad
R=M_{L_3}(C,D),\qquad
S=M_{L_4}(D,A).
$$

Fix a target complex structure

$$
K\in\operatorname{End}_{\mathbb R}(V),
\qquad
K^2=-I.
$$

We call $(L_1,L_2,L_3,L_4)$ a **universal edge-operator realization of $K$** if

$$
\boxed{R-P=K(S-Q)}
$$

for every ordered quadruple $A,B,C,D\in E$. Coincident points and all other degenerate configurations are allowed. The universal quantifier is essential: a particular quadruple may satisfy the relation accidentally even when its edge operators do not form a universal realization.

No inner product is assumed in the general classification.

---

## 2. Complete Algebraic Classification

### Theorem 1: universal edge-operator realizations

Let $K^2=-I$. The identity

$$
R-P=K(S-Q)
$$

holds for every $A,B,C,D\in E$ if and only if there is a unique endomorphism

$$
N\in\operatorname{End}_{\mathbb R}(V)
$$

such that

$$
\boxed{
\begin{aligned}
L_1&=K-KN, \\
L_2&=K+N, \\
L_3&=K+KN, \\
L_4&=K-N.
\end{aligned}}
$$

Here and below, juxtaposition denotes composition, so $KN=K\circ N$.

### Proof

Choose an arbitrary origin in $E$ and temporarily regard points as position vectors in $V$. Since the final expressions are differences of points, the calculation is independent of that choice. From

$$
2M_L(X,Y)=(I-L)X+(I+L)Y,
$$

we obtain

$$
\begin{aligned}
2(R-P)
={}&(-I+L_1)A+(-I-L_1)B \\
&+(I-L_3)C+(I+L_3)D
\end{aligned}
$$

and

$$
\begin{aligned}
2(S-Q)
={}&(I+L_4)A+(-I+L_2)B \\
&+(-I-L_2)C+(I-L_4)D.
\end{aligned}
$$

Because the identity is required for every $A,B,C,D$, comparison of the four operator coefficients gives

$$
\begin{aligned}
-I+L_1&=K(I+L_4), \\
-I-L_1&=K(-I+L_2), \\
 I-L_3&=K(-I-L_2), \\
 I+L_3&=K(I-L_4).
\end{aligned}
$$

Adding the first two equations and using $K^{-1}=-K$ yields

$$
L_2+L_4=2K.
$$

Consequently, the endomorphism

$$
N=L_2-K=K-L_4
$$

is forced. The first and third coefficient equations then give

$$
L_1=K-KN
$$

and

$$
L_3=K+KN.
$$

This proves necessity and uniqueness. Conversely, substituting the four displayed formulas for $L_1,L_2,L_3,L_4$ into the coefficient equations verifies all four equations, and hence the universal identity. $\square$

The theorem shows that the space of universal edge-operator realizations of $K$ is parametrized without restriction by the single real-linear endomorphism $N$. The common realization

$$
L_1=L_2=L_3=L_4=K
$$

corresponds to $N=0$.

---

## 3. Rigidity of Independently Chosen Signs

The first consequence concerns the original situation in which every edge uses the same complex structure but may be assigned its own sign.

### Theorem 2: sign rigidity

Let $V$ be nonzero, let $J^2=-I$, and choose

$$
\delta,\varepsilon_1,\varepsilon_2,
\varepsilon_3,\varepsilon_4\in\{+1,-1\}.
$$

Put

$$
K=\delta J,
\qquad
L_k=\varepsilon_kJ
$$

for $k=1,2,3,4$. Then

$$
R-P=\delta J(S-Q)
$$

holds for every ordered quadruple if and only if

$$
\boxed{
\varepsilon_1=\varepsilon_2
=\varepsilon_3=\varepsilon_4=\delta}.
$$

### Proof

Theorem 1 gives

$$
L_2+L_4=2K,
$$

and therefore

$$
(\varepsilon_2+\varepsilon_4)J=2\delta J.
$$

Since $J$ is invertible and $V$ is nonzero, this forces

$$
\varepsilon_2=\varepsilon_4=\delta.
$$

It follows that

$$
N=L_2-K=0.
$$

The classification formulas now give

$$
L_1=L_3=K,
$$

so $\varepsilon_1=\varepsilon_3=\delta$ as well. Conversely, if all four signs equal $\delta$, then all four edge operators equal $K$, which is the realization $N=0$ from Theorem 1. $\square$

The nonzero hypothesis is needed only to distinguish scalar multiples of the identity. On the zero vector space all sign choices define the same operator. For a single fixed configuration in a nonzero space, mixed signs may still satisfy accidental relations; the theorem is a universal rigidity statement.

---

## 4. Realizations by Complex Structures

We now require each edge operator itself to be a complex structure:

$$
L_k^2=-I
\qquad
\text{for }k=1,2,3,4.
$$

This additional condition sharply restricts the parameter $N$ but does not always force it to vanish.

### Theorem 3: complex-structure realizations

Under the parametrization of Theorem 1, all four relations $L_k^2=-I$ hold if and only if

$$
\boxed{N^2=0}
$$

and

$$
\boxed{KN+NK=0}.
$$

Equivalently, $N$ is a square-zero complex-antilinear endomorphism of the complex vector space defined by $K$.

### Proof

The conditions for $L_2=K+N$ and $L_4=K-N$ to be complex structures are

$$
(K+N)^2=-I
$$

and

$$
(K-N)^2=-I.
$$

Since $K^2=-I$, these equations are respectively equivalent to

$$
KN+NK+N^2=0
$$

and

$$
-(KN+NK)+N^2=0.
$$

Adding and subtracting them gives

$$
N^2=0,
\qquad
KN+NK=0.
$$

This proves necessity. Conversely, these two relations immediately imply

$$
(K\pm N)^2=-I.
$$

They also give

$$
KNK=N,
\qquad
(KN)^2=N^2=0.
$$

Hence

$$
\begin{aligned}
(K\pm KN)^2
&=K^2\pm(K^2N+KNK)+(KN)^2 \\
&=-I.
\end{aligned}
$$

Thus $L_1=K-KN$ and $L_3=K+KN$ are complex structures as well. $\square$

With complex multiplication defined by $iv=Kv$, the relation

$$
NK=-KN
$$

is exactly complex antilinearity. The possible failure of rigidity is therefore controlled precisely by square-zero complex-antilinear endomorphisms.

---

## 5. Orthogonal Rigidity

Suppose now that $V$ is a real inner-product space. A complex structure $L$ is **orthogonal** if

$$
\langle Lu,Lv\rangle=\langle u,v\rangle
$$

for all $u,v\in V$.

### Theorem 4: orthogonal complex-structure rigidity

Assume that

$$
K,L_1,L_2,L_3,L_4
$$

are orthogonal complex structures on the same real inner-product space. If

$$
R-P=K(S-Q)
$$

holds for every ordered quadruple, then

$$
\boxed{L_1=L_2=L_3=L_4=K}.
$$

### Proof

By Theorem 1,

$$
L_2+L_4=2K.
$$

For every $v\in V$,

$$
L_2v+L_4v=2Kv.
$$

All three operators are isometries, so

$$
\begin{aligned}
4|v|^2
&=|L_2v+L_4v|^2 \\
&=2|v|^2+2\langle L_2v,L_4v\rangle.
\end{aligned}
$$

Therefore,

$$
\langle L_2v,L_4v\rangle=|v|^2
=|L_2v|\,|L_4v|.
$$

Equality in Cauchy--Schwarz gives

$$
L_2v=L_4v.
$$

Their sum is $2Kv$, so

$$
L_2v=L_4v=Kv
$$

for every $v$. Hence $L_2=L_4=K$ and $N=L_2-K=0$. Theorem 1 then gives

$$
L_1=L_3=K.
$$

Thus all four edge complex structures equal the target structure. $\square$

Orthogonality therefore removes all of the algebraic flexibility described by Theorem 3.

---

## 6. Nonorthogonal Realizations and the Sharp Dimension Threshold

The preceding rigidity theorem fails without orthogonality. The failure is not merely formal: there are explicit nonconstant universal realizations by genuine complex structures.

### 6.1 An explicit family on $\mathbb C^2$

Let

$$
V=\mathbb C^2
$$

be regarded as a real vector space, and define the standard complex structure

$$
K(z_1,z_2)=(iz_1,iz_2).
$$

Let

$$
N(z_1,z_2)=(\overline{z_2},0).
$$

The map $N$ is real-linear and complex-antilinear. Directly,

$$
N^2=0
$$

and

$$
KN+NK=0.
$$

Indeed,

$$
KN(z_1,z_2)=(i\overline{z_2},0),
\qquad
NK(z_1,z_2)=(-i\overline{z_2},0).
$$

Theorem 3 therefore shows that

$$
\begin{aligned}
L_1&=K-KN, \\
L_2&=K+N, \\
L_3&=K+KN, \\
L_4&=K-N
\end{aligned}
$$

are all complex structures and, by Theorem 1, satisfy

$$
R-P=K(S-Q)
$$

for every ordered quadruple. The operators $N$ and $KN$ are nonzero and real-linearly independent: evaluating them at $(0,1)$ gives $(1,0)$ and $(i,0)$, respectively. Hence the four $L_k$ are distinct.

This realization is not orthogonal for the standard Hermitian norm. In particular,

$$
L_2(0,1)=(1,i),
$$

whose norm is $\sqrt2$, whereas $(0,1)$ has norm $1$.

The same construction works in every complex dimension $n\geq2$: on $\mathbb C^n$, take the standard $K$ and define

$$
N(z_1,z_2,\ldots,z_n)
=(\overline{z_2},0,\ldots,0).
$$

Thus nonorthogonal non-rigidity occurs in every finite real dimension $2n\geq4$.

### 6.2 Rigidity in real dimension two

The threshold above is sharp. In complex dimension one, identify the complex vector space defined by $K$ with $\mathbb C$. Every complex-antilinear real-linear endomorphism has the form

$$
N(z)=a\overline z
$$

for some $a\in\mathbb C$. It follows that

$$
N^2(z)=|a|^2z.
$$

Consequently, the condition $N^2=0$ forces $a=0$ and hence $N=0$. By Theorem 3, every universal realization by complex structures on a real two-dimensional space therefore satisfies

$$
L_1=L_2=L_3=L_4=K,
$$

even without orthogonality.

The first nonorthogonal exceptional families thus occur in complex dimension two, equivalently real dimension four.

---

## 7. Configuration-Dependent Defects

Orient the four boundary edges cyclically:

$$
u_1=B-A,\qquad
u_2=C-B,\qquad
u_3=D-C,\qquad
u_4=A-D.
$$

Then

$$
u_1+u_2+u_3+u_4=0.
\tag{7.1}
$$

For arbitrary $L_1,\ldots,L_4$ and target $K$, define

$$
\Delta=(R-P)-K(S-Q).
$$

### Lemma 5: cyclic defect

One has

$$
\boxed{
2\Delta
=(K-L_1)u_1
+(I+KL_2)u_2
+(L_3-K)u_3
-(I+KL_4)u_4.}
\tag{7.2}
$$

### Proof

Direct expansion gives

$$
2(R-P)=(I-L_1)u_1+2u_2+(I+L_3)u_3
$$

and

$$
2(S-Q)=(I-L_2)u_2+2u_3+(I+L_4)u_4.
$$

Subtracting the $K$-multiple gives a first expression for $2\Delta$. Replacing zero by

$$
(K-I)(u_1+u_2+u_3+u_4)
$$

and collecting terms yields (7.2). $\square$

This formula is useful beyond signs: it is the local, configuration-dependent version of the four coefficient equations used in the universal classification.

### Independently chosen signs

Fix one complex structure $J$, a target sign $\delta\in\{+1,-1\}$, and set $K=\delta J$. Choose edge signs

$$
L_k=\varepsilon_kJ,
\qquad
\varepsilon_k\in\{+1,-1\}.
$$

Let

$$
t_k=\frac{1-\delta\varepsilon_k}{2}\in\{0,1\}.
$$

Thus $t_k=1$ exactly when edge $k$ uses the sign opposite to the target sign.

### Theorem 6: exact mixed-sign criterion

For every ordered quadruple,

$$
\boxed{
\Delta
=t_2u_2-t_4u_4
+\delta J(t_1u_1-t_3u_3).}
\tag{7.3}
$$

Consequently,

$$
R-P=\delta J(S-Q)
$$

holds accidentally if and only if the right side of (7.3) vanishes.

### Proof

In (7.2), use $K=\delta J$, $L_k=\varepsilon_kJ$, and $J^2=-I$. Then

$$
\begin{aligned}
K-L_1&=2\delta t_1J,\\
I+KL_2&=2t_2I,\\
L_3-K&=-2\delta t_3J,\\
-(I+KL_4)&=-2t_4I.
\end{aligned}
$$

Divide by two. $\square$

---

## 8. The Sixteen Mixed-Sign Loci

Let

$$
\mathcal M=\{k:t_k=1\}
$$

be the mismatch set. The complete table is:

| Mismatch set $\mathcal M$ | Necessary and sufficient condition |
|---|---|
| $\varnothing$ | No condition; the identity is universal |
| $\{1\}$ | $u_1=0$ |
| $\{2\}$ | $u_2=0$ |
| $\{3\}$ | $u_3=0$ |
| $\{4\}$ | $u_4=0$ |
| $\{1,2\}$ | $u_2=-\delta Ju_1$ |
| $\{2,3\}$ | $u_2=\delta Ju_3$ |
| $\{3,4\}$ | $u_4=-\delta Ju_3$ |
| $\{4,1\}$ | $u_4=\delta Ju_1$ |
| $\{1,3\}$ | $u_1=u_3$ |
| $\{2,4\}$ | $u_2=u_4$ |
| $\{1,2,3\}$ | $u_2+\delta J(u_1-u_3)=0$ |
| $\{2,3,4\}$ | $u_2-u_4-\delta Ju_3=0$ |
| $\{3,4,1\}$ | $-u_4+\delta J(u_1-u_3)=0$ |
| $\{4,1,2\}$ | $u_2-u_4+\delta Ju_1=0$ |
| $\{1,2,3,4\}$ | $u_2-u_4+\delta J(u_1-u_3)=0$ |

Several qualitative facts are now immediate:

- A single wrong sign can work only if the corresponding edge collapses.
- Two adjacent wrong signs require a relation of the form $u_j=\pm\delta Ju_i$ between two edge vectors.
- Two opposite wrong signs require equality of the two correspondingly oriented edge vectors.
- Three or four wrong signs impose one mixed complex-linear relation.

When all four signs are wrong, the construction itself obeys

$$
R-P=-\delta J(S-Q).
$$

If it also obeys the target relation with $+\delta J$, then necessarily

$$
\boxed{R=P\quad\text{and}\quad S=Q.}
\tag{8.1}
$$

Thus the last row of the table is equivalently the simultaneous collapse of the two opposite-center vectors.

### Dimension of the mixed-sign loci

Use the complex scalar action $(a+ib)v=av+bJv$ and assume $1\le n=\dim_{\mathbb C}V<\infty$. Modulo translation, a quadrilateral is determined freely by $u_1,u_2,u_3\in V$, with

$$
u_4=-u_1-u_2-u_3.
$$

Substitution into (7.3) gives a complex-linear map $F_{\mathcal M}:V^3\to V$:

$$
F_{\mathcal M}(u_1,u_2,u_3)
=(t_4I+\delta t_1J)u_1
+(t_2+t_4)u_2
+(t_4I-\delta t_3J)u_3.
\tag{8.2}
$$

### Theorem 7: codimension of each nonempty mismatch locus

If $\mathcal M\ne\varnothing$, then $F_{\mathcal M}$ is surjective. Therefore

$$
\boxed{
\dim_{\mathbb C}\ker F_{\mathcal M}=2n.}
\tag{8.3}
$$

Equivalently:

- modulo translations, every nonempty mismatch locus has complex codimension $n$ in the space of all quadrilaterals;
- in point coordinates $E^4$, after choosing an origin, it has complex dimension $3n$ inside the ambient dimension $4n$;
- over the reals, its codimension is $2n$.

### Proof

For real $a,b$, the operator

$$
aI+bJ
$$

is invertible whenever $(a,b)\ne(0,0)$, because

$$
(aI+bJ)(aI-bJ)=(a^2+b^2)I.
$$

If $\mathcal M$ is nonempty, at least one of the three coefficients in (8.2) is a nonzero operator of this form. Holding the other two variables at zero shows that $F_{\mathcal M}$ is surjective. Rank-nullity then gives (8.3). $\square$

#### Consequence

For any probability distribution on point quadruples that is absolutely continuous with respect to Lebesgue measure, a fixed nonempty mismatch pattern succeeds with probability zero. Accidental identities are plentiful as algebraic families, but nongeneric.

---

## 9. A Common Edge Operator

Fix an oriented Euclidean plane with quarter-turn $J$. A parallelogram erected on a directed edge with vector $u$ and a fixed directly similar second side has side vector

$$
Lu=(aI+bJ)u
$$

for constants $a,b\in\mathbb R$. Its four vertices can be written

$$
X,\quad Y,\quad Y+Lu,\quad X+Lu,
$$

and its center is exactly

$$
X+\frac{u+Lu}{2}=M_L(X,Y).
$$

Thus the common-operator specialization of the current framework includes centers of four fixed directly similar parallelograms.

### The universal common-operator relation

The common-operator calculation applies in any real affine space $E$ modeled on $V$. Let $L$ be a real-linear endomorphism used on all four edges. Put

$$
x=C-A,\qquad y=D-B.
$$

Direct expansion gives

$$
\boxed{
\begin{aligned}
2(R-P)&=(I-L)x+(I+L)y,\\
2(S-Q)&=-(I+L)x+(I-L)y.
\end{aligned}}
\tag{9.1}
$$

### Theorem 8: characterization by a fixed relating operator

There exists a real-linear endomorphism $H$ such that

$$
R-P=H(S-Q)
\tag{9.2}
$$

for every $A,B,C,D$ if and only if

$$
\boxed{L^2=-I.}
\tag{9.3}
$$

In that case, the relating operator is forced to be

$$
\boxed{H=L.}
\tag{9.4}
$$

### Proof

The vectors $x$ and $y$ are independent variables. Comparing their coefficients in (9.1)--(9.2) gives

$$
H(I-L)=I+L,
\qquad
H(I+L)=-(I-L).
\tag{9.5}
$$

Adding these equations gives $2H=2L$, hence $H=L$. Substituting into the first equation yields

$$
L-L^2=I+L,
$$

so $L^2=-I$. Conversely, if $L^2=-I$, then $H=L$ satisfies both equations in (9.5), hence (9.2). $\square$

### Corollary 9: planar square orientations

In an oriented Euclidean plane, let $L=aI+bJ$. If $L^2=-I$, then

$$
(a^2-b^2)I+2abJ=-I.
$$

The operators $I$ and $J$ are real-linearly independent, so

$$
2ab=0,
\qquad
a^2-b^2=-1.
$$

The only real solutions are

$$
\boxed{a=0,\qquad b=\pm1.}
$$

Therefore, among the centers of four fixed directly similar parallelograms, the exact universal relation (9.2) singles out the two orientations of the square construction.

---

## 10. Normal Forms of the Exceptional Parameter

Throughout this section, $V$ has finite complex dimension $n$ with respect to $K$, and $N$ is complex-antilinear with $N^2=0$.

### Proposition 10: kernel, image, and rank bound

Both $\ker N$ and $\operatorname{im}N$ are complex subspaces of $V$, and

$$
\operatorname{im}N\subseteq\ker N.
$$

Consequently, if

$$
r=\dim_{\mathbb C}\operatorname{im}N,
$$

then

$$
\boxed{0\le r\le \left\lfloor\frac n2\right\rfloor.}
\tag{10.1}
$$

### Proof

If $Nv=0$, then

$$
N(Kv)=-KNv=0,
$$

so $\ker N$ is $K$-invariant. If $w=Nv$, then

$$
Kw=N(-Kv),
$$

so $\operatorname{im}N$ is also $K$-invariant. The equation $N^2=0$ gives

$$
\operatorname{im}N\subseteq\ker N.
$$

Regard $N$ as a complex-linear map $\overline V\to V$, where the conjugate vector space $\overline V$ has scalar multiplication

$$
\lambda\mathbin{\cdot_{\overline V}}v:=\overline\lambda v.
$$

This complex-linear map has the same kernel and image as the underlying additive map $N:V\to V$. Moreover, $\dim_{\mathbb C}\overline V=n$, and a conjugation of scalar multiplication does not change the complex dimension of the kernel. Complex rank-nullity therefore gives

$$
\dim_{\mathbb C}\ker N=n-r.
$$

The inclusion therefore implies $r\le n-r$, which is (10.1). $\square$

This immediately explains the planar rigidity: if $n=1$, then $r=0$, hence $N=0$. Nontrivial exceptional families first occur for $n=2$, or real dimension four.

### Complex-linear changes of coordinates

The natural coordinate changes that preserve $K$ are the invertible complex-linear maps $G$. They act on $N$ by

$$
N\longmapsto GNG^{-1}.
$$

In matrix language this is consimilarity, because a conjugate-linear map has the form $z\mapsto A\overline z$.

### Theorem 11: rank normal form

For every square-zero conjugate-linear map $N$ of complex rank $r$, there is a complex basis

$$
u_1,\ldots,u_r,
w_1,\ldots,w_{n-2r},
v_1,\ldots,v_r
$$

such that

$$
\boxed{
Nv_j=u_j,\qquad
Nu_j=0,\qquad
Nw_k=0.}
\tag{10.2}
$$

Thus two such maps on $V$ are conjugate by a complex-linear automorphism if and only if they have the same complex rank. Every rank in the interval (10.1) occurs on $V$.

### Proof

Choose a complex basis $u_1,\ldots,u_r$ of $\operatorname{im}N$. For each $j$, choose $v_j$ with $Nv_j=u_j$. Since the image lies in the kernel, extend

$$
u_1,\ldots,u_r
$$

to a complex basis

$$
u_1,\ldots,u_r,w_1,\ldots,w_{n-2r}
$$

of $\ker N$.

The displayed $n$ vectors are independent. Indeed, if

$$
\sum_j a_jv_j+k=0,
\qquad k\in\ker N,
$$

then applying $N$ gives

$$
\sum_j \overline{a_j}u_j=0,
$$

so every $a_j=0$, followed by $k=0$. The action of $N$ is therefore exactly (10.2).

Any two maps of rank $r$ have the same displayed model, so mapping one adapted basis to the other conjugates the maps. Conversely, rank is invariant under conjugacy. To realize a prescribed $r$, define (10.2) on a complex basis. $\square$

#### Matrix block

On one active complex two-plane with coordinates $z_uu+z_vv$, the normalized map is

$$
N(z_u,z_v)=(\overline{z_v},0).
\tag{10.3}
$$

Hence the entire map is a direct sum of $r$ such blocks and a zero block of complex dimension $n-2r$.

### Unitary changes of coordinates

Now suppose that $K$ is orthogonal and that $V$ carries the corresponding Hermitian inner product. Complex-linear unitary maps are a smaller coordinate-change group, so rank no longer contains all information.

### Theorem 12: unitary singular-value normal form

Let $N:V\to V$ be a square-zero conjugate-linear map of rank $r$. There is an orthonormal basis

$$
u_1,\ldots,u_r,
w_1,\ldots,w_{n-2r},
v_1,\ldots,v_r
$$

and uniquely determined positive numbers, up to ordering,

$$
\sigma_1,\ldots,\sigma_r>0
$$

such that

$$
\boxed{
Nv_j=\sigma_j u_j,\qquad
Nu_j=Nw_k=0.}
\tag{10.4}
$$

For $N=0$, one has $r=0$, the positive singular-value multiset is empty, and the basis consists only of the $w_k$. Two square-zero conjugate-linear maps on the same Hermitian space $V$ are unitarily conjugate if and only if their multisets of positive singular values agree.

### Proof

Put

$$
U=\operatorname{im}N,
\qquad
W=\ker N\cap U^\perp,
\qquad
M=(\ker N)^\perp.
$$

All three are complex subspaces, and

$$
V=U\oplus W\oplus M
$$

orthogonally. The restriction

$$
N|_M:M\longrightarrow U
$$

is injective because $M\cap\ker N=0$. It is surjective because, if $u=Nx$, the orthogonal decomposition $x=k+m$ with $k\in\ker N$ and $m\in M$ gives $u=Nm$. Thus it is a conjugate-linear bijection between two $r$-dimensional Hermitian spaces.

Regard it as a complex-linear map from the conjugate space $\overline M$ to $U$ and apply the ordinary singular-value decomposition. This produces orthonormal bases $v_j$ of $M$ and $u_j$ of $U$ with

$$
Nv_j=\sigma_j u_j.
$$

Complete with any orthonormal basis of $W$. The singular values are invariant under unitary conjugacy. Conversely, two adapted orthonormal bases with the same singular values are carried to one another by a complex-linear unitary map, which conjugates the two operators. $\square$

---

## 11. Exact Metric Distortion

The normal form gives more than the qualitative statement that nonzero $N$ is impossible in the orthogonal theorem.

### Corollary 13: length distortion and exact operator norm

Assume that the complex dimension is finite and positive and that the Hermitian metric is compatible with $K$, as in Theorem 12. All operator norms below are for the underlying real-linear maps. For $N\ne0$, put $\sigma_{\max}=\max_j\sigma_j$; for $N=0$, put $\sigma_{\max}=0$.

For every active vector $v_j$ in (10.4), the four operators in Theorem 1 satisfy

$$
\begin{aligned}
L_1v_j&=Kv_j-\sigma_jKu_j,\\
L_2v_j&=Kv_j+\sigma_ju_j,\\
L_3v_j&=Kv_j+\sigma_jKu_j,\\
L_4v_j&=Kv_j-\sigma_ju_j.
\end{aligned}
$$

Because $u_j$ and $v_j$ are orthonormal complex directions,

$$
\boxed{\|L_kv_j\|^2=1+\sigma_j^2\quad(k=1,2,3,4).}
\tag{11.1}
$$

Thus, when $N\ne0$, none of the four $L_k$ is orthogonal. The canonical test directions give the lower bound

$$
\|L_k\|_{\mathrm{op}}
\ge \sqrt{1+\sigma_{\max}^2}.
$$

The exact norm, including the case $N=0$, is

$$
\boxed{
\|L_k\|_{\mathrm{op}}
=\frac{\sqrt{\sigma_{\max}^2+4}+\sigma_{\max}}{2}
\quad(k=1,2,3,4).}
\tag{11.2}
$$

### Proof of the exact norm

The orthogonal decomposition in Theorem 12 splits $V$ into active complex two-planes $\mathbb Cu_j\oplus\mathbb Cv_j$ and the remaining subspace $W$. Every $L_k$ preserves this decomposition. On $W$, it agrees with the isometry $K$.

On an active block with singular value $\sigma>0$, use coordinates in which

$$
K=iI,
\qquad
N(z_u,z_v)=(\sigma\overline{z_v},0).
$$

The four edge operators have the factorizations

$$
L_1=K(I-N),\qquad
L_2=K(I-iN),\qquad
L_3=K(I+N),\qquad
L_4=K(I+iN).
$$

Since $K$ is an isometry, it suffices to compute the norm of $I+aN$ for $a\in\{-1,-i,1,i\}$. Conjugating the second coordinate in both domain and codomain changes this map into

$$
(z_u,z_v)\longmapsto(z_u+a\sigma z_v,z_v).
$$

Unitary changes of phase then reduce its norm calculation to

$$
S_\sigma=
\begin{pmatrix}
1&\sigma\\
0&1
\end{pmatrix}.
$$

All of these domain and codomain changes preserve the underlying real norm. The Gram matrix is

$$
S_\sigma^*S_\sigma=
\begin{pmatrix}
1&\sigma\\
\sigma&1+\sigma^2
\end{pmatrix},
$$

with largest eigenvalue

$$
\lambda_+(\sigma)
=\frac{2+\sigma^2+\sigma\sqrt{\sigma^2+4}}2
=\left(\frac{\sqrt{\sigma^2+4}+\sigma}{2}\right)^2.
$$

Thus every $L_k$ has block norm $(\sqrt{\sigma^2+4}+\sigma)/2$. This expression is increasing for $\sigma\ge0$, so taking the maximum over the orthogonal blocks gives (11.2). If $N=0$, every $L_k=K$ has norm $1$ on the nonzero space $V$, also as given by (11.2). $\square$

For example, $\sigma_{\max}=1$ gives the exact norm $(1+\sqrt5)/2$, whereas the canonical-vector lower bound is $\sqrt2$. The singular values therefore determine both the length distortion on the canonical test directions and the largest length distortion of every exceptional edge structure.

---

## 12. Formal Verification

The Lean development is organized under [`lean/VanAubelExtensions/`](../lean/VanAubelExtensions/). The following table matches the mathematical statements with their formal counterparts. Each Lean statement records its own hypotheses.

| Paper result | Lean declarations | Module |
|---|---|---|
| Theorem 1: unique four-operator parametrization | `universalOperatorIdentity_parametrization`, `affineUniversalOperatorIdentity_parametrization`, `affineUniversalOperatorIdentity_iff_parametrized` | [`Rigidity`](../lean/VanAubelExtensions/Rigidity.lean) |
| Theorem 2: sign rigidity | `universalOperatorIdentity_sign_iff` | [`Rigidity`](../lean/VanAubelExtensions/Rigidity.lean) |
| Theorem 3: square-zero antilinear criterion | `parametrized_all_complexStructures_iff` | [`Rigidity`](../lean/VanAubelExtensions/Rigidity.lean) |
| Theorem 4: orthogonal rigidity | `orthogonalOperatorIdentity_rigidity` | [`Rigidity`](../lean/VanAubelExtensions/Rigidity.lean) |
| Section 6: dimension-two rigidity and exceptional examples | `universalOperatorIdentity_rigidity_of_finrank_two`, `exceptional_family_in_every_complex_dimension_ge_two` | [`Rigidity`](../lean/VanAubelExtensions/Rigidity.lean), [`Examples`](../lean/VanAubelExtensions/Examples.lean) |
| Lemma 5: cyclic defect | `operatorDefect_cyclic`, `affineOperatorDefect_cyclic` | [`OperatorDefect`](../lean/VanAubelExtensions/OperatorDefect.lean) |
| Theorem 6: mixed-sign formula | `mismatchOfSign_bit`, `operatorDefect_mixedSigns`, `affineOperatorDefect_mixedSigns` | [`MixedSigns`](../lean/VanAubelExtensions/MixedSigns.lean) |
| Section 8: all sixteen conditions | `mismatchVector_eq_zero_iff`, `mixedSigns_centerIdentity_iff` | [`MixedSigns`](../lean/VanAubelExtensions/MixedSigns.lean) |
| Theorem 7: locus dimensions and codimension | `mismatchLocusMap_eq_operatorDefect`, `mismatchPointLocusMap_eq_operatorDefect`, `mismatchLocus_finrank`, `mismatchPointLocus_finrank`, `mismatchLocus_real_codimension` | [`MixedSigns`](../lean/VanAubelExtensions/MixedSigns.lean) |
| Section 8: measure-zero consequence | `mismatchPointLocus_haar_zero`, `mismatchPointLocus_absolutelyContinuous_zero` | [`MixedSignMeasure`](../lean/VanAubelExtensions/MixedSignMeasure.lean) |
| Theorem 8: common-operator characterization | `universalCommonOperatorIdentity_iff`, `affineUniversalCommonOperatorIdentity_iff` | [`OperatorDefect`](../lean/VanAubelExtensions/OperatorDefect.lean) |
| Corollary 9: signed square operators | `similarParallelogram_complexStructure_iff` | [`OperatorDefect`](../lean/VanAubelExtensions/OperatorDefect.lean) |
| Proposition 10: image, kernel, and rank bound | `AntilinearMap.range_le_ker`, `AntilinearMap.rank_bound` | [`ExceptionalNormalForms`](../lean/VanAubelExtensions/ExceptionalNormalForms.lean) |
| Theorem 11: rank normal form and classification | `AntilinearMap.exists_rank_normalForm`, `AntilinearMap.conjugate_iff_rank_eq`, `exists_squareZero_antilinear_of_rank` | [`ExceptionalNormalForms`](../lean/VanAubelExtensions/ExceptionalNormalForms.lean) |
| Theorem 12: unitary normal form and classification | `AntilinearMap.exists_unitaryNormalForm`, `ExceptionalUnitaryNormalForm.coefficientValues_unique`, `AntilinearMap.unitary_conjugate_iff` | [`ExceptionalMetric`](../lean/VanAubelExtensions/ExceptionalMetric.lean), [`ExceptionalUnitaryClassification`](../lean/VanAubelExtensions/ExceptionalUnitaryClassification.lean) |
| Corollary 13: active-vector distortion and exact real operator norm | `exceptionalEdgeReal_active_norm_sq`, `exceptionalEdgeReal_norm` | [`ExceptionalNorm`](../lean/VanAubelExtensions/ExceptionalNorm.lean) |

Lean indexes the four edges by `Fin 4`, starting at zero. Its indices $0,1,2,3$ correspond to the paper's edges $1,2,3,4$. Boolean mismatch bits encode the real signs through `mismatchEdgeSign`; `mismatchOfSign_bit` identifies those bits with the formula used in Theorem 6. The locus-map equalities identify the linear kernels with the defects of the actual center configurations.

The rank and unitary normal forms are stated in complex vector spaces, with antilinear maps bundled as semilinear maps over complex conjugation. [`ComplexStructureSpace`](../lean/VanAubelExtensions/ComplexStructureSpace.lean) supplies the complex action induced by a real operator $K$; `real_exceptional_rank_normalForm` gives the corresponding rank normal form directly from the real edge-operator data. The rank bound is expressed as $2r\le n$, equivalent to (10.1).

The metric results use a Hermitian space and its underlying real norm, with $K$ represented by multiplication by $i$. The unitary classification compares the multisets of positive square roots of Gram eigenvalues. The norm theorem uses the maximum positive block coefficient, with value zero when $N=0$, and assumes a nonzero ambient space as in Section 11.

From the `lean/` directory, run:

```bash
lake build
lake env lean CheckAxioms.lean
```

[`CheckAxioms.lean`](../lean/CheckAxioms.lean) lists the transitive axiom dependencies of the headline statements, including the classification, dimension, measure, and metric results.

## References

- Y. P. Hong and R. A. Horn, [*A canonical form for matrices under consimilarity*](https://doi.org/10.1016/0024-3795%2888%2990324-2), *Linear Algebra and its Applications* 102 (1988), 143–168.
