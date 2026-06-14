# Bender–Glauberman Lemma 13.8 の二つの省略ステップの展開（再検証版）

対象：Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, Lemma 13.8, §13, p.101。

このメモは、Lemma 13.8 の証明で省略されている二箇所を、Lean 4 形式化に移しやすい粒度で展開するためのものです。記号は BG の標準記号に従い、OCR で `a(M)` と見える箇所は \(\alpha(M)\)、`cr(M)` と見える箇所は \(\sigma(M)\) と読むものとします。

## 0. 再検証で確認した修正点・注意点

1. GAP 1 の「\(Q\) が \(M\) 全体の Sylow 部分群である」という部分は、実際には Uniqueness Theorem そのものではなく、有限 \(q\)-群における normalizer-growth と仮定 (5) から直接従います。Uniqueness Theorem が本質的に使われるのは、その後の \(q\notin\alpha(M)\) です。

2. Lemma 12.18 を Lemma 13.8 の次段で使うには、\(q\in p'\) も必要です。これは仮定 \(C_Q(P)=1\) と \(P\)-不変性から出ます。

3. GAP 2 の Theorem 10.1(b) は、BG 本文の実際の形では「\(p\in\sigma(M)\) で、非自明 \(p\)-部分群 \(X\) を含む \(M\) の共役全体に \(C_G(X)\) が共役作用で推移的に作用する」という主張です。ここでは \(X=Y\)、素数 \(p=t\in\beta(M)\subseteq\alpha(M)\subseteq\sigma(M)\) として使います。

4. 最後の \(r\notin\sigma(M)\) は Lemma 10.12(a) を **役割を入れ替えて** 適用します。すなわち \((M,H)=(M^*,M)\) とし、\(r\in\beta(M^*)\subseteq\alpha(M^*)\) から \(r\notin\sigma(M)\) を得ます。

5. GAP 2 では、明示的には挙げられていない BG Corollary 12.16 を使います。これは \(X=O_s(H)\) を \(M\) の共役の中へ入れるために必要です。

---

# GAP 1 — 最初の Uniqueness step

証明すべき文は次です。

\[
\text{“By (3), (5), and the Uniqueness Theorem, }Q\text{ is a nonidentity Sylow subgroup of }M
\text{ for a prime }q\notin\alpha(M).”}
\]

## 1.1. \(Q\neq 1\)

仮に \(Q=1\) とします。このとき

\[
N_G(Q)=N_G(1)=G.
\]

仮定 (5) より \(N_G(Q)\subseteq M^*\) なので、\(G\subseteq M^*\) となります。しかし \(M^*\) は \(G\) の真の極大部分群です。矛盾。

したがって

\[
Q\neq 1.
\]

従って、仮定 (3) により、ある素数 \(q\) について

\[
Q\in \operatorname{Syl}_q(M\cap M^*)
\]

です。

## 1.2. \(q\neq p\)

後で Lemma 12.18 を使うために \(q\in p'\) を確認しておきます。

仮に \(q=p\) とします。仮定 (2) より

\[
P\le M\cap M^*.
\]

仮定 (3) より \(Q\) は \(P\)-不変なので、積 \(PQ\) は \(M\cap M^*\) の \(p\)-部分群です。しかも \(Q\) は \(M\cap M^*\) の Sylow \(p\)-部分群なので

\[
PQ=Q.
\]

よって \(P\le Q\) です。ところが \(P\) は位数 \(p\) の巡回群なので \(P\) は自分自身を中心化し、従って

\[
1\neq P\le C_Q(P),
\]

となります。これは仮定 (4) の \(C_Q(P)=1\) に反します。

したがって

\[
q\neq p.
\]

## 1.3. \(Q\) は \(M\cap M^*\) だけでなく \(M\) の Sylow \(q\)-部分群である

\(Q\le M\) なので、Sylow 包含により \(Q\le S\) となる

\[
S\in\operatorname{Syl}_q(M)
\]

を取ります。

仮に \(Q<S\) とします。有限 \(q\)-群では、真部分群はその normalizer に真に含まれるので、

\[
Q<N_S(Q).
\]

よって

\[
x\in N_S(Q)\setminus Q
\]

を取れます。このとき

\[
x\in S\le M,
\qquad
x\in N_G(Q).
\]

仮定 (5) より \(N_G(Q)\subseteq M^*\) なので、

\[
x\in M\cap M^*.
\]

さらに \(x\in N_G(Q)\) なので \(\langle Q,x\rangle\) は \(q\)-部分群であり、しかも

\[
Q<\langle Q,x\rangle\le M\cap M^*.
\]

これは \(Q\in\operatorname{Syl}_q(M\cap M^*)\) に反します。従って \(Q=S\) であり、

\[
Q\in\operatorname{Syl}_q(M).
\]

この段階では Uniqueness Theorem は不要です。使っているのは、有限 \(q\)-群における normalizer-growth と仮定 (5) だけです。

## 1.4. \(q\notin\alpha(M)\)

背理法で \(q\in\alpha(M)\) と仮定します。BG §10 の定義より、

\[
\alpha(M)=\{r\in\pi(M)\mid r_r(M)>3\}.
\]

上で \(Q\in\operatorname{Syl}_q(M)\) を示したので、

\[
r(Q)=r_q(M)>3.
\]

従って \(K=Q\) は Theorem 9.6, Uniqueness Theorem の仮定を満たします。

- \(r(K)>2\)：実際には \(r(Q)>3\) だから成立。
- \(r(K)>3\) または \(r(C_G(K))>3\)：前者 \(r(Q)>3\) が成立。

よって \(Q\) は uniquely maximal、すなわち \(Q\) を含む極大部分群は一意です。

一方、仮定 (3) より

\[
Q\le M\cap M^*.
\]

したがって \(Q\le M\) かつ \(Q\le M^*\) です。\(M\) と \(M^*\) はどちらも極大部分群なので、uniqueness により

\[
M=M^*.
\]

これは仮定 (1) の「\(M^*\) は \(M\) と共役でない」に反します。等しければもちろん共役だからです。

従って

\[
q\notin\alpha(M).
\]

## 1.5. Lemma 12.18 へ渡すための形式化用まとめ

ここまでで得た事実は次です。

\[
Q\neq1,
\qquad
Q\in\operatorname{Syl}_q(M),
\qquad
q\neq p,
\qquad
q\notin\alpha(M).
\]

さらに仮定 (5) より \(N_G(Q)\subseteq M^*\) で、\(M^*\) は \(M\) と共役でないので、

\[
\mathcal M(N_G(Q))\neq\{M\}.
\]

これで Lemma 12.18(b) の仮定が満たされます。Lemma 12.18(b) は、\(Q\) が \(M\) の Sylow \(q\)-部分群である場合に

\[
\alpha(M)=\beta(M)
\]

を与え、さらに Lemma 12.18(a) の状況に入ることを保証します。したがって BG 本文の次の行

\[
C_{M_\beta}(P)\neq1,
\qquad
C_{M^*_\beta}(P)\neq1
\]

は、\(M\) 側と \(M^*\) 側へ Lemma 12.18(b) を対称に適用したものです。

---

# GAP 2 — Hall \(H\)、\(F(H)\)、Theorem 10.1(b) の段落

ここでは、Lemma 13.8 の次の段落を展開します。

> Let \(H\) be a Hall \((\beta(M)\cup\beta(M^*))\)-subgroup of \(C_G(P)\) ... By Lemma 10.12(a), \(r\notin\sigma(M)\).

以下、

\[
\theta=\beta(M)\cup\beta(M^*)
\]

と置きます。

## 2.1. Hall \(\theta\)-部分群 \(H\) の存在と conjugacy

まず \(P\neq1\) です。もし \(C_G(P)=G\) なら、\(P\le Z(G)\) です。しかし \(G\) は非可換単純群なので \(Z(G)=1\) であり、\(P\neq1\) に反します。従って

\[
C_G(P)<G.
\]

\(G\) は minimal simple group of odd order なので、すべての真部分群は可解です。よって \(C_G(P)\) は可解です。

BG Proposition 1.5、特に operator group を自明群として適用した Hall の定理により、可解群 \(C_G(P)\) には Hall \(\theta\)-部分群が存在し、任意の \(\theta\)-部分群はある Hall \(\theta\)-部分群に含まれ、Hall \(\theta\)-部分群同士は \(C_G(P)\) 内で共役です。

したがって Hall \(\theta\)-部分群

\[
H\in\operatorname{Hall}_\theta(C_G(P))
\]

を取れます。

## 2.2. \(s\in\beta(M)\) と仮定してよい理由

\(H\) は \(\theta\)-群なので、

\[
\pi(H)\subseteq\theta.
\]

特に

\[
s\in\pi(F(H))
\]

なら

\[
s\in\theta=\beta(M)\cup\beta(M^*).
\]

Lemma 13.8 の仮定とここまでの議論は、

\[
(M,Q)\leftrightarrow(M^*,Q^*)
\]

を入れ替えても不変です。従って、必要なら \(M\) と \(M^*\) を交換して、

\[
s\in\beta(M)
\]

と仮定してよいです。

この交換により、以後の \(t\) は交換後の \(M\) に対する

\[
t\in\pi(F(C_{M_\beta}(P)))
\]

として取り直します。

## 2.3. \(H\supseteq C_{M_\beta}(P)\) と仮定してよい理由

Lemma 12.18(b) を \(M\) 側に適用しているので

\[
C_{M_\beta}(P)\neq1.
\]

これは \(C_G(P)\) の \(\beta(M)\)-部分群、従って \(\theta\)-部分群です。

BG Proposition 1.5(b) により、\(C_{M_\beta}(P)\) は \(C_G(P)\) のある Hall \(\theta\)-部分群 \(H_0\) に含まれます。また Proposition 1.5(c) により、Hall \(\theta\)-部分群は \(C_G(P)\) 内で共役です。

もとの \(H\) をこの \(H_0\) に置き換えてよいです。この置換は Hall \(\theta\)-部分群の \(C_G(P)\)-共役による置換なので、\(s\in\pi(F(H))\) という性質は保存されます。実際、\(H_0=H^c\) なら

\[
F(H_0)=F(H)^c,
\]

なので \(\pi(F(H_0))=\pi(F(H))\) です。

従って以後、

\[
H\supseteq C_{M_\beta}(P)
\]

と仮定します。

## 2.4. \(X=O_s(H)\) と \(Y=O_t(C_{M_\beta}(P))\) は非自明

\(s\in\pi(F(H))\) なので、\(F(H)\) の Sylow \(s\)-部分群は非自明です。\(F(H)\lhd H\) かつ nilpotent なので、その Sylow \(s\)-部分群は \(H\) の正規 \(s\)-部分群です。従って

\[
X=O_s(H)\neq1.
\]

同様に、\(t\in\pi(F(C_{M_\beta}(P)))\) なので

\[
Y=O_t(C_{M_\beta}(P))\neq1.
\]

また

\[
Y\le C_{M_\beta}(P)\le H.
\]

## 2.5. \(X\subseteq M^g\) となる \(g\in G\) の存在

上で \(s\in\beta(M)\) と仮定しています。従って

\[
s\in\beta(M)\subseteq\alpha(M).
\]

\(X=O_s(H)\) は非自明 \(s\)-群なので、\(X\) は非自明 \(\alpha(M)\)-部分群です。

BG Corollary 12.16 を適用すると、任意の非自明 \(\alpha(M)\)-部分群は \(M_\alpha\) の部分群へ共役です。従って、ある \(a\in G\) が存在して

\[
X^a\le M_\alpha\le M.
\]

\(g=a^{-1}\) と置けば

\[
X\le M^g.
\]

これが BG 本文の

\[
X\subseteq M^g\quad\text{for some }g\in G
\]

の正確な根拠です。

## 2.6. 鎖 \(M^g\supseteq N_G(X)\supseteq H\supseteq Y\)

まず \(X=O_s(H)\) は \(H\) の最大正規 \(s\)-部分群なので \(H\) に characteristic です。従って

\[
H\le N_G(X).
\]

次に、\(X\le M^g\) かつ \(X\neq1\) で、素数 \(s\in\beta(M)=\beta(M^g)\) です。従って \(X\) は \(M^g\) の非自明 \(\beta(M^g)\)-部分群です。

BG Proposition 10.14(d) を極大部分群 \(M^g\) に適用すると、

\[
N_G(X)\le M^g.
\]

また 2.4 より \(Y\le H\) です。

従って

\[
M^g\supseteq N_G(X)\supseteq H\supseteq Y.
\]

## 2.7. 鎖 \(M\supseteq N_G(Y)\supseteq C_G(Y)\)

\(Y\le C_{M_\beta}(P)\le M_\beta\le M\) かつ \(Y\neq1\) です。従って \(Y\) は \(M\) の非自明 \(\beta(M)\)-部分群です。

さらに \(Y\le C_{M_\beta}(P)\le C_M(P)\) です。BG Proposition 10.14(d) を \(M\) に適用して、

\[
N_G(Y)\le M.
\]

また中心化する元は正規化するので、常に

\[
C_G(Y)\le N_G(Y).
\]

従って

\[
M\supseteq N_G(Y)\supseteq C_G(Y).
\]

加えて、2.6 の鎖より \(Y\le H\le M^g\) であり、また \(Y\le M\) なので

\[
Y\le M\cap M^g.
\]

## 2.8. Theorem 10.1(b) の適用

ここで \(t\in\pi(F(C_{M_\beta}(P)))\) なので、\(Y=O_t(C_{M_\beta}(P))\) は非自明 \(t\)-群です。また

\[
t\in\beta(M)\subseteq\alpha(M)\subseteq\sigma(M).
\]

従って BG Theorem 10.1(b) を、極大部分群 \(M\)、素数 \(t\in\sigma(M)\)、非自明 \(t\)-部分群 \(Y\) に対して適用できます。

Theorem 10.1(b) は、\(C_G(Y)\) が

\[
\{M^u\mid u\in G,
\; Y\le M^u\}
\]

に共役作用で推移的に作用する、という主張です。

\(M\) と \(M^g\) はどちらもこの集合に属します。従って、ある

\[
h\in C_G(Y)
\]

が存在して

\[
M^g=M^h.
\]

さらに 2.7 より \(C_G(Y)\le M\) なので \(h\in M\) です。従って

\[
M^h=M.
\]

よって

\[
M^g=M.
\]

2.6 の鎖 \(H\le M^g\) と合わせて

\[
H\le M.
\]

これが BG 本文の

\[
M=M^g\supseteq H
\]

です。

## 2.9. \(r\in\beta(M^*)\cap\pi(H)\) が存在する理由

\(M^*\) 側にも Lemma 12.18(b) を対称に適用しているので、

\[
C_{M^*_\beta}(P)\neq1.
\]

これは \(C_G(P)\) の非自明 \(\beta(M^*)\)-部分群です。従って、ある素数

\[
r\in\beta(M^*)
\]

が \(|C_G(P)|\) を割ります。

\(H\) は \(C_G(P)\) の Hall \(\theta\)-部分群で、\(\theta=\beta(M)\cup\beta(M^*)\) です。従って、\(\theta\) に属する素数で \(|C_G(P)|\) を割るものは \(|H|\) も割ります。よって

\[
r\in\pi(H).
\]

従って

\[
\beta(M^*)\cap\pi(H)\neq\varnothing.
\]

このような \(r\) を一つ取ります。

## 2.10. \(r\mid |C_M(P)|\)

2.8 で

\[
H\le M
\]

を示しました。一方、\(H\) は \(C_G(P)\) の部分群として取ったので、

\[
H\le C_G(P).
\]

従って

\[
H\le M\cap C_G(P)=C_M(P).
\]

\(r\in\pi(H)\) なので、直ちに

\[
r\mid |C_M(P)|.
\]

## 2.11. \(r\notin\sigma(M)\)

上で取った \(r\) は

\[
r\in\beta(M^*)\subseteq\alpha(M^*).
\]

仮定 (1) より \(M^*\) は \(M\) と共役でありません。BG Lemma 10.12(a) を、\((M,H)=(M^*,M)\) として適用します。この補題は、非共役な極大部分群に対して

\[
\alpha(M^*)\cap\sigma(M)=\varnothing
\]

を与えます。

従って

\[
r\notin\sigma(M).
\]

これで、BG 本文の

\[
\text{“Take }r\in\beta(M^*)\cap\pi(H).\text{ Then }r\mid |C_M(P)|.\text{ By Lemma 10.12(a), }r\notin\sigma(M).”
\]

までが完全に展開されます。

---

# 3. Lean 形式化向け依存関係リスト

GAP 1 で必要な補題・定理：

1. `normalizer_one_eq_top`: \(N_G(1)=G\)。
2. `proper_maximal_ne_top`: 極大部分群は真部分群。
3. `p_group_normalizer_growth`: 有限 \(p\)-群で \(H<P\) なら \(H<N_P(H)\)。
4. `sylow_containment`: \(Q\le M\) の \(q\)-部分群は \(M\) の Sylow \(q\)-部分群に含まれる。
5. `Theorem_9_6_Uniqueness`: \(r(K)>2\) かつ \(r(K)>3\) または \(r(C_G(K))>3\) なら \(K\) は uniquely maximal。
6. \(\alpha(M)=\{q\mid r_q(M)>3\}\) の定義。
7. Lemma 12.18(b): \(Q\in\operatorname{Syl}_q(M)\) の場合、\(\alpha(M)=\beta(M)\) かつ Lemma 12.18(a) の状況に入る。

GAP 2 で必要な補題・定理：

1. `proper_centralizer_of_nontrivial_subgroup`: \(P\neq1\) なら \(C_G(P)<G\)。
2. minimality of \(G\): 真部分群は可解。
3. BG Proposition 1.5 with trivial operator group: 可解群で Hall 部分群の存在・包含・共役。
4. Lemma 12.18(b), both sides: \(C_{M_\beta}(P)\neq1\), \(C_{M^*_\beta}(P)\neq1\)。
5. Corollary 12.16: 非自明 \(\alpha(M)\)-部分群は \(M_\alpha\) へ共役。
6. Proposition 10.14(d), applied to \(M\) and \(M^g\): 非自明 \(\beta\)-部分群の normalizer containment。
7. Theorem 10.1(b): \(C_G(Y)\)-transitivity on maximal subgroups containing \(Y\), for \(t\in\sigma(M)\)。
8. Lemma 10.12(a), roles swapped: \(r\in\alpha(M^*)\Rightarrow r\notin\sigma(M)\) when \(M^*\) is not conjugate to \(M\)。

---

# 4. 形式化上の短いコメント

- GAP 1 の \(Q\in\operatorname{Syl}_q(M)\) は、BG 本文では Uniqueness Theorem と同じ文に入っていますが、Lean では独立補題に分ける方が自然です。

- \(H\) を `replace H by a conjugate Hall subgroup containing C_{M_\beta}(P)` する箇所では、`s ∈ π(F(H))` が共役で保存されることを別補題にしておくとよいです。

- Theorem 10.1(b) の適用では、\(Y\) が \(t\)-部分群で、\(t\in\beta(M)\subseteq\sigma(M)\) であることを明示的に渡す必要があります。

- \(r\notin\sigma(M)\) の最後の一行は、Lemma 10.12(a) の向きを誤ると証明が通りません。必ず \((M,H)=(M^*,M)\) として適用します。
