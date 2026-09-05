**AI disclosure.** This proof was generated with OpenAI's GPT-5.6 Pro and ChatGPT Work. The argument below is fully formalized in Lean 4/Mathlib ([certificate and manuscript](https://github.com/sebastienpalcoux/sqrt6-kissing-bound)); it has not undergone independent human mathematical review.

Yes. With the natural correction
\[
\alpha_*:=\sup_{n\ge1}\tau_n^{1/n}
\]
to the parenthetical formula in the question, one has \(\alpha_*=\sqrt6\).

**Theorem.** For every integer \(n\ge1\),
\[
\tau_n\le(\sqrt6)^n.
\]
Consequently, the smallest positive \(\alpha\) such that \(\tau_n\le\alpha^n\) in every dimension is \(\sqrt6\).

**Proof.** A kissing configuration is a finite set \(X\subset\mathbb R^n\) of unit vectors with \(\langle x,z\rangle\le1/2\) for distinct members. Write \(N=|X|\), \(s=\sqrt3\), \(a=s/2\), and let \(V_n\) denote the volume of the open unit ball \(B_n\).

**Volume packing.** The open cones
\[
C_x=\{y:\langle x,y\rangle>a\|y\|\}\qquad(x\in X)
\]
are pairwise disjoint. Indeed, a common direction would give a unit vector \(u\) and decompositions \(x=bu+p\), \(z=cu+r\), with \(p,r\perp u\), \(b,c>a\), and \(\|p\|,\|r\|<1/2\). Cauchy–Schwarz would then imply
\[
\langle x,z\rangle=bc+\langle p,r\rangle
\ge bc-\|p\|\|r\|>\frac12.
\]
Thus, if a measurable body \(K\subset C_e\cap B_n\) about a fixed unit axis \(e\) has volume \(q\), its orthogonal images about the vectors of \(X\) give
\[
Nq\le V_n. \tag{1}
\]

For \(n\ge2\), use orthogonal coordinates \((t,v)\in\mathbb R\times\mathbb R^{n-1}\) about \(e\). The cone condition becomes \(t>0\), \(3\|v\|^2<t^2\). Fubini's theorem gives the profile formula
\[
\operatorname{vol}\{(t,v):b<t<c,\ \|v\|<g(t)\}
=V_{n-1}\int_b^c g(t)^{n-1}\,dt \tag{2}
\]
for continuous nonnegative profiles \(g\).

**The bicone.** Take the union of the two bodies
\[
L_n=\{(t,v):0<t<a,\ \|v\|<t/s\},
\qquad
U_n=\{(t,v):a<t<1,\ \|v\|<(2+s)(1-t)\}.
\]
Both lie in \(C_e\cap B_n\). For the lower body this follows from
\(3\|v\|^2<t^2\) and \(t^2+\|v\|^2<4t^2/3<1\).
For the upper profile \(h(t)=(2+s)(1-t)\), one has
\[
s h(t)<t,\qquad h(t)^2<1-t^2\quad(a<t<1):
\]
the first comparison is an equality at \(a\) and compares a decreasing affine function with \(t\); the second follows from
\((2+s)^2(1-a)=1+a\) and hence \((2+s)^2(1-t)<1+t\).

The two profile integrals in (2) are respectively
\[
\frac{s}{n2^n},\qquad \frac{2-s}{n2^n}.
\]
Their sum is \(1/(n2^{n-1})\), so (1) gives
\[
N\le n2^{n-1}\frac{V_n}{V_{n-1}}. \tag{3}
\]

The standard unit-ball volume formula gives
\[
V_{d+2}=\frac{2\pi}{d+2}V_d,
\]
and in particular
\[
\begin{gathered}
V_1=2,\quad V_2=\pi,\quad V_3=4\pi/3,\quad V_4=\pi^2/2,\\
V_5=8\pi^2/15,\quad V_6=\pi^3/6,\quad V_7=16\pi^3/105.
\end{gathered}
\]
Since \(V_6/V_5=5\pi/16<1\) and \(V_7/V_6=32/35<1\), the recurrence proves \(V_n\le V_{n-1}\) for all \(n\ge6\): if the comparison holds two dimensions earlier, then
\[
V_n=\frac{2\pi}{n}V_{n-2}
\le\frac{2\pi}{n}V_{n-3}
\le\frac{2\pi}{n-1}V_{n-3}=V_{n-1}.
\]
Also
\[
n2^{n-1}\le(\sqrt6)^n\qquad(n\ge6).
\]
To verify this last inequality, check \(n=6,7\) directly and then use
\(4n\le6(n-2)\) to pass from \(n-2\) to \(n\). Thus (3) proves the desired bound for every \(n\ge6\).

The bicone also handles dimensions two and five:
\[
n=2:\quad N\le2\pi<7\ \Longrightarrow\ N\le6,
\]
\[
n=5:\quad N\le256/3<86\ \Longrightarrow\ N\le85<36\sqrt6.
\]
These comparisons use \(\pi<22/7\) and \(85^2<36^2\cdot6\).

**Dimension three.** Retain \(L_3\) and replace the upper body by the profile
\[
g(t)=\sqrt{1-t^2}\qquad(a<t<1).
\]
It lies inside the unit ball; since \(t>a\), one also has
\(3g(t)^2=3(1-t^2)<t^2\), so it lies inside the cone. The combined volume is
\[
q=\pi\left(\frac{s}{24}+\int_a^1(1-t^2)\,dt\right)
=\frac{(2-s)\pi}{3}.
\]
As \(s<26/15\), this is greater than \(4\pi/45=V_3/15\). Equation (1) yields \(N<15\), hence
\[
N\le14<6\sqrt6=(\sqrt6)^3.
\]

**Dimension four.** Retain \(L_4\), and use the polynomial upper profile
\[
p(t)=(1-t)(14t+2-6s)\qquad(a<t<1).
\]
Here \(p(t)\ge0\) on \([a,1]\). To check that the body lies inside the ball, put
\[
Q(t)=196t^2-(140+70s)t-48+74s.
\]
The identities
\[
1-t^2-p(t)^2=(1-t)(t-a)Q(t),
\]
\[
Q(t)=4s-6+(t-a)\bigl(196(t+a)-140-70s\bigr)
\]
show that \(p(t)^2\le1-t^2\) on \([a,1]\): indeed \(s>3/2\), and the expression in parentheses is at least \(126s-140>0\). Since \(t>a\), containment in the ball again implies containment in the cone.

Expanding the polynomial and integrating gives
\[
\int_a^1 p(t)^3\,dt=\frac{33169-19150s}{40}.
\]
For a compact way to check the evaluation, set \(\delta=1-a\), \(A=16-6s\), and substitute \(u=1-t\). The integral becomes
\[
\int_0^\delta u^3(A-14u)^3\,du
=\frac{A^3\delta^4}{4}-\frac{42A^2\delta^5}{5}
+98A\delta^6-392\delta^7;
\]
substitute \(\delta=1-s/2\) and use \(s^2=3\).

Adding the lower profile integral \(s/64\), the combined body has volume \(q=TV_3\), where
\[
T=\frac{265352-153195s}{320}.
\]
Since \(1351^2-3\cdot780^2=1\), we have \(s<1351/780\), whence
\[
T>\frac{541}{16640}>\frac{33}{1036}
=\frac3{296}\frac{22}{7}>\frac{3\pi}{296}.
\]
Therefore
\[
q>\frac{3\pi}{296}\frac{4\pi}{3}
=\frac{\pi^2}{74}=\frac{V_4}{37}.
\]
Equation (1) yields \(N<37\), and integrality gives
\[
N\le36=(\sqrt6)^4.
\]

Finally, in dimension one there are only two unit vectors, so \(N\le2<\sqrt6\). We have bounded every finite kissing configuration in every positive dimension. The nonempty set of realizable cardinalities is consequently a bounded set of natural numbers, and therefore has an attained maximum \(\tau_n\) satisfying the same bound.

The regular hexagon with vertices
\[
\begin{gathered}
(1,0),\quad (\tfrac12,\tfrac{s}{2}),\quad (-\tfrac12,\tfrac{s}{2}),\\
(-1,0),\quad (-\tfrac12,-\tfrac{s}{2}),\quad (\tfrac12,-\tfrac{s}{2})
\end{gathered}
\]
is a six-point kissing configuration. Hence \(\tau_2=6\), so any positive universal base satisfies \(6\le\alpha^2\), or \(\alpha\ge\sqrt6\). This proves optimality and the supremum formula. \(\square\)

The Lean certificate includes the cone and body constructions, all volume computations and numerical comparisons, the attained maximum, and the explicit hexagon. It uses only the standard foundational axioms `propext`, `Classical.choice`, and `Quot.sound`. Reproduction instructions and the complete exposition are in the linked repository.
