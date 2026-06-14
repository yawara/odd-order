# Bender–Glauberman Lemma 13.6 の「we can assume」部分の検証メモ

対象箇所は Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, Lemma 13.6 の次の段階である。

- \(A=M_\sigma\) と書く。
- \(E\) は \(A\) の補群で、\(E=E_1E_2E_3\)、\(E'=[E,E]\)。
- \(q\in\sigma(M)\)、\(q\notin\beta(M)\)。
- \(X\in\mathcal E_q^1(C_A(E_1))\) は固定された位数 \(q\) の部分群で、\(X\nleq A'\)。
- Lemma 12.19 により、\(E'\) は \(A\) の Hall \(\beta(M)'\)-部分群を中心化する。

検証後の結論は次の通り。

> 元の固定された \(X\) は、仮定からは \(E_1\)-不変、実際には \(E_1\) によって中心化されるだけであり、一般には \(E'\)-不変でも \(E\)-不変でもない。  
> それでも、補群 \(E\) を \(M_\sigma\) 内の適当な共役で取り替えることにより、同じ固定された \(X\) について
> \[
> E\leq N_M(S),\qquad X\leq S\leq C_{M_\sigma}(E')
> \]
> を満たす Sylow \(q\)-部分群 \(S\in\operatorname{Syl}_q(M_\sigma)\) を仮定してよい。

---

## 1. 使う事実

### Proposition 1.5（coprime action の Hall 補題）

\(G\) が可解群、\(A\) が \((|A|,|G|)=1\) を満たす作用群、\(\pi\) が素数集合のとき、以下を使う。

1. \(A\) は \(G\) のある Hall \(\pi\)-部分群を固定する。
2. 任意の \(A\)-不変な \(\pi\)-部分群は、ある \(A\)-不変 Hall \(\pi\)-部分群に含まれる。
3. 二つの \(A\)-不変 Hall \(\pi\)-部分群は、\(C_G(A)\) の元で共役である。

ここでは \(\pi=\{q\}\) として使う。

### Lemma 12.19

\(E'\) は \(A=M_\sigma\) の Hall \(\beta(M)'\)-部分群を中心化する。

したがって \(q\notin\beta(M)\) なら、その Hall \(\beta(M)'\)-部分群は \(A\) の Sylow \(q\)-部分群を含む。よって \(C_A(E')\) は \(A\) の full \(q\)-part を含む。

### Lemma 13.6 直前の reduction

Lemma 13.6 の証明では、Corollary 12.14 と Theorem 13.5 により、次を仮定してよい。

\[
q\notin\beta(M),\qquad X\nleq A',\qquad P=E_1,
\]

特に

\[
X\leq C_A(E_1).
\]

---

## 2. まず \(E'\)-centralized かつ \(E\)-invariant な Sylow \(q\)-部分群を選ぶ

Lemma 12.19 から、\(E'\) が中心化する Hall \(\beta(M)'\)-部分群 \(H\leq A\) が存在する。\(q\notin\beta(M)\) なので、\(H\) は \(A\) の Sylow \(q\)-部分群を含む。したがって

\[
C_A(E')
\]

は \(A\) の full \(q\)-part を含む。

また、\(E'\lhd E\) なので、\(C_A(E')\) は \(E\)-不変である。ここで Proposition 1.5(a) を、\(E\) の \(C_A(E')\) への作用に適用する。すると \(E\)-不変な Sylow \(q\)-部分群

\[
S_0\in\operatorname{Syl}_q(C_A(E'))
\]

を選べる。\(C_A(E')\) は \(A\) の full \(q\)-part を含むので、これは同時に

\[
S_0\in\operatorname{Syl}_q(A)
\]

でもある。従って

\[
E\leq N_M(S_0),
\qquad
S_0\leq C_A(E').
\]

この段階ではまだ固定された \(X\) が \(S_0\) に入っているとは限らない。

---

## 3. 固定された \(X\) を Sylow \(q\)-部分群に入れる

\(X\leq C_A(E_1)\) なので、\(X\) は \(E_1\)-不変な \(q\)-部分群である。そこで Proposition 1.5(b) を、\(E_1\) の \(A\) への作用に適用する。すると、\(X\) を含む \(E_1\)-不変 Sylow \(q\)-部分群

\[
S_1\in\operatorname{Syl}_q(A),
\qquad
X\leq S_1
\]

が存在する。

一方、上で選んだ \(S_0\) は \(E\)-不変なので、特に \(E_1\)-不変である。したがって \(S_0\) と \(S_1\) は、\(E_1\)-不変 Sylow \(q\)-部分群である。Proposition 1.5(c) を \(E_1\) の作用に適用すると、ある

\[
c\in C_A(E_1)
\]

が存在して

\[
S_1^c=S_0.
\]

よって

\[
X^c\leq S_0\leq C_A(E').
\]

しかも \(c\in C_A(E_1)\) なので、\(X^c\) も依然として \(E_1\) を中心化する。

---

## 4. 「固定された \(X\)」を保つための補群の取り替え

上の議論だけだと、\(S_0\) に入るのは \(X\) ではなく \(X^c\) である。固定された \(X\) を文字通り保つには、\(X\) ではなく補群を共役で取り替える。

\[
\widetilde E=E^{c^{-1}},
\qquad
\widetilde S=S_0^{c^{-1}}.
\]

ここで \(c\in A=M_\sigma\) であり \(A\lhd M\) なので、\(\widetilde E\) は依然として \(A\) の補群である。さらに \(c\in C_A(E_1)\) だから

\[
\widetilde E_1=E_1^{c^{-1}}=E_1.
\]

したがって、固定された \(X\leq C_A(E_1)\) という条件はそのまま残る。

また、

\[
\widetilde E'=(E')^{c^{-1}}.
\]

そして、\(E\) が \(S_0\) を正規化していたことから、\(\widetilde E\) は \(\widetilde S\) を正規化する。さらに \(S_0\leq C_A(E')\) から

\[
\widetilde S=S_0^{c^{-1}}\leq C_A((E')^{c^{-1}})=C_A(\widetilde E').
\]

最後に、\(X^c\leq S_0\) なので

\[
X\leq S_0^{c^{-1}}=\widetilde S.
\]

従って

\[
\widetilde E\leq N_M(\widetilde S),
\qquad
X\leq \widetilde S\leq C_A(\widetilde E').
\]

\((\widetilde E,\widetilde S)\) を改めて \((E,S)\) と書けば、Lemma 13.6 の本文の形

\[
E\leq N_M(S),
\qquad
X\leq S\leq C_{M_\sigma}(E')
\]

が得られる。

---

## 5. \(X\) の不変性について

この議論から分かることは次である。

\[
\boxed{X\text{ は仮定からは }E_1\text{-不変であるだけで、一般には }E'\text{-不変でも }E\text{-不変でもない。}}
\]

実際、仮定は

\[
X\leq C_A(E_1)
\]

であり、これは \(E_1\) が \(X\) の各元を中心化することを意味する。しかし \(E'\) や \(E\) が \(X\) を正規化する、まして中心化する、という結論はここからは出ない。

Lemma 13.6 の「we can assume」は、固定された \(X\) に追加の不変性を仮定しているのではない。正しくは次の二段階である。

1. \(E'\) が中心化する、かつ \(E\)-不変な Sylow \(q\)-部分群 \(S_0\) を選ぶ。
2. \(E_1\)-Hall 共役性により、\(X\) を含む \(E_1\)-不変 Sylow \(q\)-部分群を \(S_0\) に合わせる。その際の共役元 \(c\) は \(C_A(E_1)\) に取れるため、補群 \(E\) を \(E^{c^{-1}}\) に取り替えても \(E_1\) は変わらない。

これが、固定された \(X\) を保ったまま

\[
X\leq S\leq C_A(E')
\]

を仮定できる理由である。

---

## 6. 検証後の最終形

厳密には、本文の一文

> by Proposition 1.5, we can assume that \(E\) normalizes \(S\) and that \(X\subseteq S\subseteq C_{M_\sigma}(E')\)

は、次の省略形である。

1. Lemma 12.19 と \(q\notin\beta(M)\) から、\(C_{M_\sigma}(E')\) は Sylow \(q\)-部分群を含む。
2. Proposition 1.5(a) から、そこに \(E\)-不変な Sylow \(q\)-部分群 \(S_0\) を取れる。
3. \(X\leq C_{M_\sigma}(E_1)\) なので、Proposition 1.5(b) から \(X\) を含む \(E_1\)-不変 Sylow \(q\)-部分群 \(S_1\) を取れる。
4. Proposition 1.5(c) から、\(S_1^c=S_0\) となる \(c\in C_{M_\sigma}(E_1)\) が存在する。
5. \(E\) を \(E^{c^{-1}}\)、\(S_0\) を \(S_0^{c^{-1}}\) に置き換えて改名する。

この改名後、固定された \(X\) について

\[
E\leq N_M(S),
\qquad
X\leq S\leq C_{M_\sigma}(E')
\]

が成立する。

---

## 参照箇所

- Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, Chapter I, Proposition 1.5: coprime action による Hall 部分群の存在・包含・共役性。
- 同書 Chapter III, Lemma 12.19: \(E'\) が Hall \(\beta(M)'\)-部分群を中心化すること。
- 同書 Chapter III, Theorem 13.5: \(E_1\) が \(M_\sigma\) に prime manner で作用し、Lemma 13.6 で \(P=E_1\) としてよいこと。
- 同書 Chapter III, Lemma 13.6: 問題の “we can assume” の箇所。
