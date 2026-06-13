# Bender–Glauberman Theorem 13.4 の欠落箇所の再検証

対象：Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, Theorem 13.4 の証明中の

\[
C_{M_\alpha}(P)\le C_{M_\alpha}(R)
\]

および対称的な包含

\[
C_{M_\alpha}(R)\le C_{M_\alpha}(P)
\]

の導出。

以下では

\[
A:=M_\alpha
\]

と書く。

---

## 0. 結論

欠けている一行は、次の事実を暗黙に使っている。

> Theorem 13.4 の証明の前半は、選んだ素数 `q` について一様である。したがって、
> \(q\in \alpha(M)\) であるような \(PR\)-不変 Sylow \(q\)-部分群
> \(S\le C_{M_\sigma}(P)\) に対して \([S,R]\ne 1\) が起きると、同じ議論により
> \(q\notin\alpha(M)\) が従い、矛盾する。

従って、\(R\) は \(C_{M_\sigma}(P)\) の \(\alpha(M)\)-部分、すなわち

\[
C_{M_\alpha}(P)
\]

を中心化する。これが

\[
C_{M_\alpha}(P)\le C_{M_\alpha}(R)
\]

である。対称的に、BG の議論で既に得られている \(r\in\tau_1(M)\) を用いて同じことを
\((r,R)\) と \((p,P)\) を入れ替えて適用すれば、

\[
C_{M_\alpha}(R)
   \le C_{M_\alpha}(P)
\]

が従う。

この証明は、あなたのリスト (1)--(7) だけに含まれる情報からではなく、Theorem 13.4 の証明の前半で既に使われている「\([S,R]\ne1\Rightarrow q\notin\alpha(M)\)」の導出が `q` について一様である、という事実を使う。

---

## 1. BG の該当部分の構造

Theorem 13.4 は、

\[
p\in\tau_1(M),\qquad P\in\mathcal E_p^1(E),\qquad
r\in\pi(E),\qquad R\in\mathcal E_r^1(C_E(P))
\]

のもとで、任意の

\[
q\in\sigma(M)
\]

および \(PR\)-不変 Sylow \(q\)-部分群

\[
S\in\operatorname{Syl}_q(C_{M_\sigma}(P))
\]

について \([S,R]=1\) を示す形で進む。BG は \(Q=[S,R]\ne1\) と仮定し、

\[
Q=[S,R]\le [M_\sigma\cap M^*,R]
\]

から Corollary 13.2 を用いて

\[
p\in\beta(M^*),\qquad r\in\tau_1(M^*)
\]

を得る。その後 Lemma 12.18(a), Proposition 12.15, Lemma 10.12(a) を通して

\[
q\notin\alpha(M)
\]

を導く。BG の印刷本文では、この直後に

\[
C_A(P)\le C_A(R)
\]

を “we can conclude” としている。

ポイントは、\(q\) が任意の \(\sigma(M)\)-素数だったことである。この前半の議論は、\(q\) がたまたま最終的な反証に使われる素数であることを使っていない。

---

## 2. 一様排除補題

### 補題 1（一様排除）

\(a\in\tau_1(M)\), \(A_0\in\mathcal E_a^1(E)\), \(b\in\pi(E)\),
\(B_0\in\mathcal E_b^1(C_E(A_0))\) とする。さらに \(s\in\sigma(M)\) とし、
\(T\) を \(A_0B_0\)-不変 Sylow \(s\)-部分群

\[
T\in \operatorname{Syl}_s(C_{M_\sigma}(A_0))
\]

とする。このとき

\[
[T,B_0]\ne1
\quad\Longrightarrow\quad
s\notin\alpha(M).
\]

特に、\(s\in\alpha(M)\) なら

\[
[T,B_0]=1.
\]

### 証明

\([T,B_0]\ne1\) と仮定し、

\[
Y=[T,B_0]
\]

とおく。\(a\in\tau_1(M)\) なので、\(N_G(A_0)\) を含む最大部分群を \(M^\dagger\ne M\) に選べる。

\(T\le C_G(A_0)\le M^\dagger\), \(B_0\le C_G(A_0)\le M^\dagger\) だから

\[
1<Y=[T,B_0]
   \le [M_\sigma\cap M^\dagger,B_0].
\]

Theorem 13.4 の本文と同じ Corollary 13.2 の適用により、

\[
a\in\beta(M^\dagger),
\qquad
b\in\tau_1(M^\dagger)
\]

が従う。

また \(T\le M\cap M^\dagger\) であり、\(T\) が非可換なら Theorem 12.13 により一意最大性に反する。従って \(T\) は可換である。よって coprime action により

\[
T=C_T(B_0)\times [T,B_0]
  =C_T(B_0)\times Y,
\]

したがって

\[
C_Y(B_0)=1.
\]

さらに \(A_0\) は \(B_0\) と \(Y\) の双方を中心化する。\(a\in\beta(M^\dagger)\subseteq\alpha(M^\dagger)\) だから

\[
1<A_0\le C_{M^\dagger_\alpha}(B_0Y).
\]

ここで仮に

\[
\mathcal M(N_G(Y))\ne\{M^\dagger\}
\]

なら、Lemma 12.18(a) を \(M^\dagger\) 上で、\(b,B_0,Y\) に適用できる。実際、

- \(b\in\tau_1(M^\dagger)\),
- \(Y\ne1\),
- \(Y\) は \(B_0\)-不変,
- \(C_Y(B_0)=1\),
- \(M^\dagger_\alpha\ne1\),
- \(s\notin\alpha(M^\dagger)\)

である。最後の点は、\(s\in\sigma(M)\) と \(M,M^\dagger\) 非共役性から Lemma 10.12(a) を対称に用いることで従う。

Lemma 12.18(a) は

\[
C_{M^\dagger_\alpha}(B_0Y)=1
\]

を与え、これは上の

\[
1<A_0\le C_{M^\dagger_\alpha}(B_0Y)
\]

に矛盾する。従って

\[
\mathcal M(N_G(Y))=\{M^\dagger\}.
\]

次に Proposition 12.15 を \(M,M^\dagger,X=Y\) に適用する。case (e) は起こらない。なぜなら case (e) では \(M\cap M^\dagger\) が \(M^\dagger_\sigma\) の補元になるが、すでに

\[
1<A_0\le M\cap M^\dagger_\sigma
\]

であるからである。従って case (d) であり、特に

\[
s\in\sigma(M^\dagger).
\]

最後に Lemma 10.12(a) より、非共役な \(M,M^\dagger\) について

\[
\alpha(M)\cap\sigma(M^\dagger)=\varnothing.
\]

よって

\[
s\notin\alpha(M).
\]

補題 1 が証明された。

---

## 3. 欠けている包含の証明

### 命題 2

Theorem 13.4 の状況で、

\[
C_A(P)\le C_A(R).
\]

### 証明

\[
B:=C_A(P)
\]

とおく。\(R\) は \(A=M_\alpha\) を正規化し、かつ \(P\) を中心化するので、\(B\) は \(R\)-不変である。

\(\ell\) を \(|B|\) の任意の素因子とする。すると \(\ell\in\alpha(M)\) である。coprime action により、\(B\) の \(R\)-不変 Sylow \(\ell\)-部分群

\[
B_\ell\in\operatorname{Syl}_\ell(B)
\]

を取れる。

\(B\le C_A(P)\) だから、\(P\) は \(B_\ell\) を中心化する。従って \(B_\ell\) は \(PR\)-不変である。

また \(M_\alpha\) は \(M\) の正規 Hall \(\alpha(M)\)-部分群であり、\(M_\alpha\le M_\sigma\) である。よって \(\ell\in\alpha(M)\) に対して、\(C_{M_\sigma}(P)\) の任意の \(\ell\)-部分群は \(M_\alpha\) に含まれる。したがって

\[
B_\ell\in\operatorname{Syl}_\ell(C_{M_\sigma}(P)).
\]

補題 1 を

\[
a=p,
\quad A_0=P,
\quad b=r,
\quad B_0=R,
\quad s=\ell,
\quad T=B_\ell
\]

に適用する。もし \([B_\ell,R]\ne1\) なら

\[
\ell\notin\alpha(M)
\]

となるが、これは \(\ell\in\alpha(M)\) に反する。従って

\[
[B_\ell,R]=1.
\]

これは \(|B|\) のすべての素因子 \(\ell\) について成り立つ。各 \(B_\ell\) を一つずつ選ぶと、これらは \(B\) の全 Sylow 部分群を含むので、生成する部分群は \(B\) 全体である。ゆえに

\[
[B,R]=1.
\]

すなわち

\[
C_A(P)=B\le C_A(R).
\]

---

## 4. 対称的包含

BG の証明のこの時点では既に

\[
r\in\tau_1(M)
\]

が得られている。またもともと

\[
P\le C_E(R)
\]

である。そこで補題 1 を、\((p,P)\) と \((r,R)\) を入れ替えて適用する。

すなわち、上の命題 2 の証明と同じ議論を

\[
a=r,
\quad A_0=R,
\quad b=p,
\quad B_0=P
\]

として行うと、

\[
C_A(R)\le C_A(P)
\]

が従う。

従って

\[
C_A(P)=C_A(R).
\]

---

## 5. 最後の矛盾

\[
B_0:=C_A(P)=C_A(R)
\]

とおく。

\(S\le C_M(P)\) なので、\(S\) は \(C_A(P)=B_0\) を正規化する。また \(R\) は \(B_0=C_A(R)\) を中心化する。従って交換子

\[
Q=[S,R]
\]

は \(B_0\) を中心化する。すなわち

\[
B_0\le C_A(Q).
\]

よって

\[
C_A(R)=B_0\le C_A(RQ).
\]

逆包含 \(C_A(RQ)\le C_A(R)\) は自明だから

\[
C_A(R)=C_A(RQ).
\]

一方、この時点では

\[
r\in\tau_1(M),
\quad Q\ne1,
\quad C_Q(R)=1,
\quad \mathcal M(N_G(Q))\ne\{M\},
\quad A\ne1,
\quad q\notin\alpha(M)
\]

が成立している。よって Lemma 12.18(a) を \(M\) 上で \((r,R,Q)\) に適用すると、

\[
C_A(R)\ne C_A(RQ)
\]

が従う。実際には

\[
C_A(R)\ne1,
\qquad
C_A(RQ)=1
\]

である。これは直前の等式に矛盾する。

従って仮定

\[
Q=[S,R]\ne1
\]

は不可能であり、\([S,R]=1\) が示される。

---

## 6. あなたの観察の検証

あなたの観察、すなわち

> \(S\) と \(R\) が \(C_{L}(P)\) を正規化し、\(C_L(P)\) が巡回なので、\([S,R]=Q\) が \(C_L(P)\) を中心化する

という部分は正しい。

より正確には、\(\ell\in\alpha(M)\) について \(L\) を \(\langle S,P,R\rangle\)-不変 Sylow \(\ell\)-部分群 of \(A\) とする。coprime action により、

\[
C_L(P)
\]

は \(C_A(P)\) の Sylow \(\ell\)-部分群である。rank bound \(r(C_A(P))\le1\) から、奇数位数なので \(C_L(P)\) は巡回である。\(S\) と \(R\) はこれを正規化するので、\(\operatorname{Aut}(C_L(P))\) が可換であることから

\[
[S,R]=Q
\]

は \(C_L(P)\) を中心化する。

各 \(\ell\) についてこの議論を行うと、\(Q\) は \(C_A(P)\) 全体を中心化する。従って

\[
C_A(P)\cap C_A(R)
   \le C_A(RQ).
\]

Lemma 12.18(a) により \(C_A(RQ)=1\) なので、

\[
C_A(P)
   \cap C_A(R)=1.
\]

これは BG の包含

\[
C_A(P)\le C_A(R)
\]

と両立する。むしろ両方を合わせると

\[
C_A(P)=1
\]

となり、これが最終矛盾に向かう構造の一部である。したがって、観察に本質的な誤りはない。ただし、それだけでは BG の “we can conclude” の包含は出ない。包含を出すには、上の補題 1、すなわち「\(\alpha(M)\)-素数上の失敗は同じ前半議論で排除される」という一様性が必要である。

---

## 7. 荷重仮定の使われ方

### \(p\in\tau_1(M)\)

\(M^\dagger\in\mathcal M(N_G(P))\), \(M^\dagger\ne M\) を選ぶために使う。また Corollary 13.2 を通して

\[
p\in\beta(M^\dagger)
\]

を得るために使う。これにより

\[
1<P\le C_{M^\dagger_\alpha}(RY)
\]

という Lemma 12.18(a) への矛盾が作れる。

### \(r\in\tau_1(M)\)

まず \([S,R]\ne1\) から BG の前半で得られる。これを使って対称的包含

\[
C_A(R)\le C_A(P)
\]

を証明する。また最終段階で Lemma 12.18(a) を \((r,R,Q)\) に適用するためにも必要である。

### \(q\notin\alpha(M)\)

これは仮定ではなく、\([S,R]\ne1\) から導かれる結論である。最終段階の Lemma 12.18(a) において、\(Q\) が \(q\)-部分群であるため必要となる。

### \(q\in\sigma(M)\cap\sigma(M^*)\)

\(q\in\sigma(M^*)\) は Proposition 12.15 の case (e) 排除後に得る。すると非共役な \(M,M^*\) に対して Lemma 10.12(a) を使い、

\[
\alpha(M)\cap\sigma(M^*)=\varnothing
\]

から

\[
q\notin\alpha(M)
\]

を得る。

---

## 8. Lean formalization 向けの圧縮形

形式化では次の補題を切り出すのがよい。

```text
UniformExclusion:
  Let a ∈ τ₁(M), A₀ ∈ E_a¹(E), b ∈ π(E), B₀ ∈ E_b¹(C_E(A₀)).
  Let s ∈ σ(M), and let T ∈ Syl_s(C_{Mσ}(A₀)) be A₀B₀-invariant.
  If [T,B₀] ≠ 1, then s ∉ α(M).
```

これを示したあと、

```text
alpha_fixed_le_fixed:
  under the same hypotheses,
  C_{Mα}(A₀) ≤ C_{Mα}(B₀).
```

を証明する。

証明は：\(C_{M\alpha}(A_0)\) の各 \(B_0\)-不変 Sylow \(s\)-部分群 \(T\) を取り、\(s\in\alpha(M)\) なので `UniformExclusion` の contrapositive から \([T,B_0]=1\)。これを全素因子について行い、Sylow 部分群が全体を生成することから結論する。

Theorem 13.4 の欠落箇所は、これを

```text
(A₀,B₀) = (P,R)
```

と

```text
(A₀,B₀) = (R,P)
```

に適用するだけである。

