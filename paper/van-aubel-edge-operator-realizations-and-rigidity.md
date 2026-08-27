# Edge-Operator Realizations and Rigidity of the Van Aubel Center Identity

## Abstract

The Van Aubel center identity is usually constructed by applying the same signed complex structure to all four directed edges. This note classifies all quadruples of real-linear edge operators that realize a fixed target complex structure in the identity for every ordered quadruple of points. The complete family is parametrized by one endomorphism $N$. Requiring all four edge operators to be complex structures is equivalent to requiring that $N$ be square-zero and complex-antilinear. Independently chosen signs are rigid on every nonzero real vector space, and independently chosen orthogonal complex structures are rigid on every real inner-product space. In finite dimensions, nonconstant families without orthogonality exist beginning in real dimension four, while real dimension two remains rigid.

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

## 7. Final Perspective

The universal Van Aubel center relation admits the following realization classification. For a fixed target complex structure $K$, every quadruple of real-linear edge operators producing

$$
R-P=K(S-Q)
$$

for all ordered quadruples is determined by one arbitrary real-linear endomorphism $N$ through

$$
\boxed{
\begin{aligned}
L_1&=K-KN, &
L_2&=K+N, \\
L_3&=K+KN, &
L_4&=K-N.
\end{aligned}}
$$

Within this family:

- independently chosen signs are rigid on nonzero spaces;
- all four edge operators are complex structures exactly when $N$ is square-zero and complex-antilinear;
- orthogonality forces $N=0$ and hence a common complex structure on all four edges;
- in finite dimensions, nonzero parameters without orthogonality occur from real dimension four onward, while real dimension two remains rigid.

The standard Van Aubel construction is the common realization corresponding to $N=0$. The classification states which hypotheses make that realization unique and where nonorthogonal alternatives begin.
