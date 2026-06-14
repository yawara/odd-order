# Bender–Glauberman Lemma 13.6 の末尾の検証メモ

## 結論

前回の結論は正しい。ただし、末尾の圧縮された一文

\[
A=A_0\times [A,E_1]\text{ centralizes }X
\]

は、**Theorem 13.4 を \([A,E_1]\) に適用しているわけではない**。\([A,E_1]\) が \(X\) を中心化する理由は別で、Lemma 13.6 の直前の行で得られている

\[
X\le S\le C_{M_\sigma}(E')
\]

を使う。したがって

\[
[A,E_1]\le E'\le C_E(X)
\]

となり、\([A,E_1]\) が \(X\) を中心化する。

## 原文で確認した要点

Bender–Glauberman, *Local Analysis for the Odd Order Theorem* の該当箇所では、Lemma 13.6 の proof 内で、Theorem 12.13 と Proposition 1.5 を使って、\(E\) が Sylow \(q\)-subgroup \(S\) を正規化し、かつ

\[
X\le S\le C_{M_\sigma}(E')
\]

となるように取れることが述べられている。その後で \(p\in\tau_2(M)\), \(A\in\mathcal E_p^2(E)\) を取り、

\[
A\lhd E,\qquad C_{M_\sigma}(A)=1 \tag{13.1}
\]

を Corollary 12.6(a) と Theorem 12.5(d) から得ている。

Theorem 13.4 は

\[
\ell\in\tau_1(M),\quad P_1\in\mathcal E_\ell^1(E),\quad r\in\pi(E),\quad R\in\mathcal E_r^1(C_E(P_1))
\]

に対して

\[
C_{M_\sigma}(P_1)\le C_{M_\sigma}(R)
\]

を与える形で使われる。

Proposition 1.6(d) は、可解群 \(G\) とそれに互いに素な位数で作用する operator group \(A\) について、\(G\) がアーベルなら

\[
G=C_G(A)\times [G,A]
\]

を与える。ここでは \(G=A\), operator group を \(E_1\) として使う。

## 詳細な復元

### 1. まず \(A_0=C_A(E_1)\) が \(X\) を中心化する

\(A_0=C_A(E_1)\) とおく。

\(A_0\) の任意の 1 次元部分群、つまり order \(p\) の部分群を

\[
R\le A_0,\qquad R\in\mathcal E_p^1(E)
\]

とする。また、\(E_1\neq 1\) なので、ある素数 \(\ell\in\tau_1(M)\) と

\[
P_1\in\mathcal E_\ell^1(E_1)
\]

を取る。

\(R\le A_0=C_A(E_1)\) だから

\[
R\le C_E(P_1).
\]

したがって Theorem 13.4 を \(P=P_1\), \(R=R\) に適用でき、

\[
C_{M_\sigma}(P_1)\le C_{M_\sigma}(R)
\]

を得る。一方、Lemma 13.6 の設定で \(X\le C_{M_\sigma}(E_1)\) なので、特に

\[
X\le C_{M_\sigma}(P_1).
\]

よって

\[
X\le C_{M_\sigma}(R).
\]

\(R\le A_0\) は任意であり、\(A_0\) はその order \(p\) の部分群で生成されるので、

\[
[A_0,X]=1.
\]

ここで Theorem 13.4 が直接カバーしているのは \(A_0\) の各 line だけである。

### 2. \([A,E_1]\) が \(X\) を中心化する理由

これは Theorem 13.4 からではない。

まず \(A\lhd E\) なので

\[
[A,E_1]\le A.
\]

また \(A\le E\), \(E_1\le E\) だから、これらの commutator は \(E\) の導来群に入る：

\[
[A,E_1]\le [E,E]=E'.
\]

一方、Lemma 13.6 の proof では既に

\[
X\le C_{M_\sigma}(E')
\]

が得られている。したがって

\[
[[A,E_1],X]=1.
\]

これが moved part \([A,E_1]\) の中心化の本当の理由である。

### 3. \(A=A_0\times[A,E_1]\)

\(A\) は elementary abelian \(p\)-group で、\(E_1\) は \(\tau_1(M)\)-part、\(p\in\tau_2(M)\) であるから

\[
(|E_1|,|A|)=1.
\]

\(A\) はアーベルなので、Proposition 1.6(d) の coprime action decomposition から

\[
A=C_A(E_1)\times[A,E_1]=A_0\times[A,E_1]
\]

を得る。

### 4. 矛盾

上で

\[
[A_0,X]=1,
\qquad
[[A,E_1],X]=1
\]

を得た。したがって

\[
[A,X]=1.
\]

つまり

\[
1\neq X\le C_{M_\sigma}(A).
\]

しかし (13.1) は

\[
C_{M_\sigma}(A)=1
\]

であった。これは矛盾である。

## 重要な注意

\([A,E_1]\) の各 line は一般には \(E_1\) を中心化しない。したがって、これらに Theorem 13.4 を直接適用することはできない。

また、\(E_1\) が \(A\) に faithful に作用していることも矛盾しない。faithful であることは、\([A,E_1]\) が非自明に動かされることを意味するだけであり、\([A,E_1]\) が別の部分群 \(X\) を中心化することを妨げない。ここでの中心化は

\[
[A,E_1]\le E'
\quad\text{and}\quad
X\le C_{M_\sigma}(E')
\]

から来る。

## 圧縮された原文の展開形

原文の

\[
\text{Thus } A=A_0\times[A,E_1]\text{ centralizes }X
\]

は、正確には次の 2 段階を含んでいる：

\[
A_0=C_A(E_1)\le C_E(X)
\quad\text{by Theorem 13.4,}
\]

かつ

\[
[A,E_1]\le E'\le C_E(X)
\quad\text{by the earlier choice }X\le C_{M_\sigma}(E').
\]

したがって

\[
A=A_0\times[A,E_1]\le C_E(X),
\]

すなわち

\[
X\le C_{M_\sigma}(A),
\]

これは (13.1) に反する。

## 参照箇所

- Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, Section 12, pp. 83–84: \(E_1,E_2,E_3\), \(E'= [E,E]\), \(E=E_1E_2E_3\), \(E_3\le E'\) などの基本構造。
- 同 pp. 86–87: Theorem 12.5 と Corollary 12.6。特に \(p\in\tau_2(M)\), \(A\in\mathcal E_p^2(E)\) に対して \(A\lhd E\), \(C_{M_\sigma}(A)=1\)。
- 同 pp. 98–99: Theorem 13.4 と Lemma 13.6。特に Lemma 13.6 の proof 中の \(X\le S\le C_{M_\sigma}(E')\) と、末尾の \(A=A_0\times[A,E_1]\) の箇所。
- 同 p. 5: Proposition 1.6(d), coprime action decomposition \(G=C_G(A)\times[G,A]\) for abelian \(G\).
