# BG §5 "Narrow p-Groups" — 実装前 自己完結サーベイ (2026-05-30)

> **目的**: 別エージェントが BG §5 (`OddOrder/BG/Ch1_Preliminary/S05_NarrowPGroups.lean`, 未作成) を
> **cold start** で実装できる水準の調査。READ-ONLY 調査の成果物 (Lean 未編集)。
> **出典**: `references/bg/local-analysis.mmd` L1789-1967 (printed pp.44-48)。実 mmd 本文を読んで作成。
> 既存 `notes/bg/s05_narrow_pgroups.md` (2026-05-23 audit ベース) を更新・訂正する位置づけ。

---

## 0. エグゼクティブサマリ (先に結論)

1. **§5 原典範囲 = mmd L1789-1967**。7 numbered result: Lem 5.1, Lem 5.2, Thm 5.3, Cor 5.4, Thm 5.5, Thm 5.6, Thm 5.7。**capstone は Theorem 5.5** (narrow p-群の odd solvable 自己同型群の制御) と **Theorem 5.3** (narrow ⟺ `E²∩E*≠∅` の characterization)。Lem 5.1/5.2 が両者の機構的土台。
2. **§5 は §4 の capstone にほぼ全面依存し、現状その capstone が未完**。§5 が使う §4 結果 = Lem 4.5(c), Lem 4.7, Prop 4.4, Thm 4.16, Lem 4.14, Lem 4.17, Thm 4.18。このうち **Lean で完成しているのは無い**(Lem 4.7 は ⇐ のみ `scn3_empty_of_pRank_le_two`、Prop 4.4 は (a) のみ `isSCN_iff_isMaximalAbelianNormal`)。**⇒ §5 は §4 Wave 2 完了が事実上のゲート**。例外: Thm 5.5 が使う **Thm 1.13 (`thompson_critical_omega`) は sorry-free で利用可**、Lem 1.9 (2-step instance) も利用可。
3. **§5 → "§7" は task の framing がややミスリード**。§5 の最初の実 downstream は **§8 (Uniqueness, L2324: "by Lemma 5.1, SCN₃(P)≠∅")** と **§9 (L2629)**。§7 (Transitivity) 自体は `SCN₃(p)` を **仮説として受ける** (Thm 7.6) だけで §5 を cite しない。**§5 が critical path 上にある理由 = Lemma 5.1(a) (rank≥3 ⇒ SCN₃(R)≠∅) が §7-§9 の SCN₃ 機構を「空でない」状態で供給し、Thm 5.5 が §10/§14/§15/App.E の narrow Sylow automorphism 制御を供給するから**。
4. **Gorenstein 行間は §5 本文中で 1 箇所のみ**: Thm 5.5(c) の証明が "**G**, Theorem 5.4.1, p.189" を cite。実体は **Gorenstein "p′-自己同型が odd p-群の Ω₁(P) 上 trivial ⇒ trivial" (Gorenstein 1980 本 mmd の Theorem 3.10 / Theorem 2.4)**。Isaacs 対応の有無は要確認だが、mathlib coprime-stabilizer + Isaacs Ch04 (4.34/4.35/4.36) で代替できる公算が高い。
5. **山場 (scaffold-hoist 誘惑、本物で証明すべき)**: **(A) Lemma 5.2** (rank≥3 narrow の central structure: `|Ω₁(Z(R))|=p`, `Ω₁(Z₂(R))∈E²`, `T=C_R(Ω₁(Z₂(R)))` char index p) と **(B) Theorem 5.5 の rank≥3 分岐** (H_i 降鎖 + Lemma 1.9 stabilization で A/O_p(A) abelian p′ + p′-元 order ∣ p-1)。これらは hard content を未充足仮説に逃がさず、`Ω₁(Z₂(R))` 層・A-invariant chain 層を実装して証明すべき。

---

## 1. 原典範囲 (mmd L1789-1967)

| 区間 | 内容 |
|---|---|
| L1789 | `## 5. Narrow \(p\)-Groups` (節ヘッダ) |
| L1791 | narrow 定義の再掲 (§1 L354 が正本) + 動機 |
| L1793 | Remark: `Z_p ≀ Z_p` が `r(R)=p≥3` の narrow 例 |
| L1795-1806 | **Lemma 5.1** (a)(b) + proof |
| L1808-1836 | **Lemma 5.2** (a)(b)(c) + proof |
| L1838-1873 | **Theorem 5.3** (characterization + (a)-(d)) + proof |
| L1875-1879 | **Corollary 5.4** + proof |
| L1881-1941 | **Theorem 5.5** (a)(b)(c) + proof |
| L1943 | p-length one の定義再掲 |
| L1945-1953 | **Theorem 5.6** (a)-(e) + proof |
| L1955-1967 | **Theorem 5.7** + proof |
| L1969- | `## 6. Additional Results` (§6 開始) |

### mmd 抽出エラー (記録)

- **L1957 に誤った `6. Additional Results` ヘッダが混入** (Thm 5.7 の proof 本体の途中)。本物の §6 ヘッダは L1969 (`**6. Additional Results**`)。Thm 5.7 の proof は L1959-1967 に正しく続く。**§5 の終端は L1967、§6 開始は L1969** が正。L1957 はゴースト見出し。
- L1832 で `(b)` 直後に "We now have (a) and (b)." が改行なく続く (Lemma 5.2 proof の段落結合)。読解上の問題なし。
- inline display math (`\[...\tag{5.x}\]`) は (5.1)-(5.5) のラベルで散在。Lean 化では式番号は docstring へ。
- narrow 定義は §1 L354 に正本: "*a p-group R will be called narrow if it contains no elementary abelian subgroup of order p³ or if it contains a subgroup R₀ of order p and a cyclic subgroup R₁ such that C_R(R₀)=R₀×R₁*"。**π\* on p.845 of FT に対応** (非標準・本書限定の用語)。§5 L1791 の "r(R)≤2 or ..." は informal restatement (r(R)≤2 ⟺ no elem-ab of order p³ は Lem 4.7、非自明)。

---

## 2. 定理・補題 完全リスト (1 行ステートメント)

p は奇素数、R は p-群 (特記なき限り)。`r(·)`=`pRank` 系の `rank`、`m(·)`=elem-ab の F_p 次元。
`E²(R)`=位数 p² の elem-ab、`E*(R)`=極大 elem-ab、`E²∩E*`=「p² だが larger elem-ab に含まれない」。
`Z=Ω₁(Z(R))`, `W=Ω₁(Z₂(R))`, `T=C_R(W)`。

| # | 種別 | ステートメント (何を証明するか) |
|---|---|---|
| **5.1** | Lem | `r(R)≥3` ⇒ **(a)** `SCN₃(R)≠∅`、**(b)** `E∈E²(R)` かつ `E⊴R` ⇒ `E` は `SCN₃(R)` の元に含まれる。 |
| **5.2** | Lem | `r(R)≥3`, `E∈E²(R)∩E*(R)` ⇒ **(a)** `E⊄T`、**(b)** `|Z|=p` かつ `W∈E²(R)`、**(c)** `T char R`, `[R:T]=p`。(narrow の central structure 抽出。Thm 5.3 の (a)(b)(c) の中身。) |
| **5.3** | Thm | `r(R)≥3` ⇒ **R narrow ⟺ `E²(R)∩E*(R)≠∅`**。narrow なら **(a)** `E²∩E*` の元は `T` に含まれない、**(b)** `|Z|=p`, `W∈E²`、**(c)** `T char`, index p、**(d)** `S`位数p で `r(C_R(S))≤2` ⇒ `C_T(S)` cyclic, `S∩R'=S∩T=1`, `C_R(S)=S×C_T(S)`。 |
| **5.4** | Cor | `r(R)≥3` ⇒ **R narrow ⟺ ∃ S 位数p で `r(C_R(S))≤2`**。(Thm 5.3 の利用しやすい同値形。) |
| **5.5** | **Thm (capstone)** | R narrow, A=solvable ≤ Aut(R), `|A|` odd ⇒ **(a)** `A/O_p(A)` は abelian p′-群、**(b)** `r(R)≥3` なら A の各 p′-元の位数は (p-1) を割る、**(c)** `|A|` が `p(p-1)` を割らない素数なら `|A| ∣ (p+1)/2`; さらに `R=[R,A]` かつ R 非abelian なら `|R|=p³`。 |
| **5.6** | Thm | G solvable odd, p∈π(G), S=narrow Sylow p; `r(S)≥3` なら p-length 1 を仮定 ⇒ **(a)** p は `|G/O_{p'}(G)|` の最大素因子、**(b)** p=3 or p 最小素因子 ⇒ G に normal p-complement、**(c)** G' に normal p-complement、**(d)** G' の p′-部分群 ⊆ `O_{p'}(G')`、**(e)** `G/O_{p',p}(G)` abelian p′。 |
| **5.7** | Thm | G solvable odd, E=elem-ab p ⊆ F(G), `r(C_{F(G)}(E))≤2` ⇒ **G' ⊆ F(G)**。 |

**capstone 特定**: グラフ上の hub は **Lemma 5.1 (4箇所で内部 cite: 5.1 proof内, 5.2 L1826, §8 L2324, §9 L2629)** と **Theorem 5.5 (下流最多: §10/§14/§15/App.E)**。数学的頂点は **Theorem 5.5** (narrow の automorphism 制御 = FT 局所解析の道具)。Theorem 5.3 は構造 characterization の頂点。

**証明依存 (§5 内部)**:
```
Lem 4.7 ─┐
Lem 1.22 ┼→ Lem 5.1 ──→ Lem 5.2 ──→ Thm 5.3 ──→ Cor 5.4
Prop 4.4 ┘        (5.2 は Lem 5.1 を L1826 で使う)   │
Lem 4.5(c)────────→ Lem 5.2                          │
Thm 1.13 ─┐                                          │
Lem 1.9   ┼→ Thm 5.5 ←(Cor 5.4 経由で narrow の R₀ を取る)
Thm 4.16  ┤            ↑ rank≤2 分岐で Lem 4.7/4.14/4.16/4.17
Lem 4.14  ┤
Lem 4.17  ┘
Thm 4.18 ──→ Thm 5.6 (r≤2分岐), Thm 5.5 (r≥3分岐) ──→ Thm 5.6
Thm 5.3 + Thm 5.5 ──→ Thm 5.7
```

---

## 3. §4 → §5 依存 (突き合わせ)

§5 が **明示 cite** する §4 結果と、Lean 現状 (`S04_PGroupsSmallRank.lean` / `GroupTheory/{PRank,SCN,CriticalSubgroup}.lean`):

| §4 結果 | §5 でどこで使うか | mmd statement 要約 | Lean 現状 | 状態 |
|---|---|---|---|---|
| **Lem 4.7** | 5.1(a) (L1800), 5.5(c) (L1935) | `SCN₃(R)=∅ ⟺ r(R)≤2` | `scn3_empty_of_pRank_le_two` = **⇐ のみ** (r≤2⇒空)。5.1(a) が要るのは **⇒ (r≥3⇒SCN₃≠∅) = 未実装** (Gorenstein 5.4.15) | ⚠ **⇒ 欠落** |
| **Lem 1.22** | 5.1(b) (L1800) | p-群 `N⊴G`, `\|N\|=p^k`, `r≤k` ⇒ N 内に位数 p^r の `G`-normal 部分群 | repo 検索: **未実装** (S04 にも無い) | ❌ 欠落 |
| **Prop 4.4** | 5.1(b) (L1800, "B* が SCN₃ 元に含まれる") | (a) `SCN(R)=maximal-abelian-normal`、(b) Syl_p ⇒ `C_G(A)=A×H` | (a) = `isSCN_iff_isMaximalAbelianNormal` ✅。5.1 が使うのは "elem-ab `B*`⊴R, `\|B*\|≥p³` ⇒ SCN₃ 元に含まれる" = **Prop 4.4(a) + 拡大補題、要 maximal-abelian-normal の存在/拡大** | △ 部分 |
| **Lem 4.5(c)** | 5.2 proof (L1818) | `Ω₁(Z₂(R))` は noncyclic exponent p | repo: **未実装** (S04 に 4.5(a)/(b) はあるが (c) 無し)。Prop 4.3(a) cl≤2 = `Omega.exponent_eq_of_class_le_two` で exponent 部分は近い | ⚠ 欠落 |
| **Lem 4.5** (general) | (5.2 経由) | (a) normal `E_p²` 存在 | `exists_normal_isElementaryAbelian_..._omega1Center` = **abelian-center case のみ** | △ 部分 |
| **Thm 4.16** (Blackburn) | 5.5(c) (L1937) | r≤2, [R,A]=R, \|A\| odd ⇒ p>3 & (abelian or central product extraspecial∘cyclic) | **未実装** (commutator-engine `isPGroup_commutator_of_faithful_two_dim_charP` のみ)。issue 0051 進行中 | ❌ 欠落 (§4 最難) |
| **Lem 4.14** | 5.5(c) (L1935) | Lem 4.13 の設定で `q ∣ (p+1)/2` or `(p-1)/2` | **未実装** | ❌ 欠落 |
| **Lem 4.17** | 5.5(a) r≤2分岐 (L1933) | A solvable p′-op, r(R)≤2, \|A\| odd ⇒ A' は p-群 | **未実装** (m(V)=2 エンジンのみ)。Thm 1.13 直用で最速とされる | ❌ 欠落 |
| **Thm 4.18** | 5.6 r≤2分岐 (L1953) | G solvable odd, r_p(G)≤2 のときの大域構造 (normal p-complement 等) | **未実装** | ❌ 欠落 |

**§4 以外の依存 (利用可能なもの)**:

| 結果 | §5 でどこ | Lean 現状 | 状態 |
|---|---|---|---|
| **Thm 1.13** (Thompson critical) | 5.5 proof 冒頭 (L1887: "R has char subgroup H of class≤2, exp p, [R,H]⊆Z(H), C_A(H) p-群") | **`thompson_critical_omega` sorry-free** (`S01_Solvable.lean:845`, via `CriticalSubgroup.lean`) | ✅ **利用可** |
| **Lem 1.9** (operator が normal series を stabilize ⇒ A/C_A(G) は π-群) | 5.5(a)(b)(c) (L1931: H_i 鎖の stabilization) | `S01_Solvable.lean:656` に **2-step instance 形**あり (`AppA_PStability.lean` でも使用)。**一般 n-step 鎖版が要るか要確認** (Thm 5.5 は長さ n の鎖) | △ 2-step のみ |
| **Lem 1.20** (Maschke) | (5.5 では直接不要だが §4 経由) | repo 既存 (`S02_Representations`) | ✅ |

**インフラ (shared module) 突き合わせ**:

| 概念 | 必要箇所 | Lean 現状 |
|---|---|---|
| `pRank G p` / `rank G` + 評価補題 | 全 §5 | ✅ `PRank.lean` 充実 (`pRank_le_iff`, `le_pRank`, `pow_le_card_of_le_pRank`, `pRank_mono_of_le`, 2形の橋) |
| `IsSCN` / `IsSCN_n` / `IsSCN₃` | 5.1, (5.5) | ✅ `SCN.lean` (def + Prop 4.4(a) + `.le_pRank` / `.mono`) |
| `IsElementaryAbelian` + `.map` | 全 §5 (E², E*) | ✅ `ElementaryAbelian.lean` |
| **`E²(R)` / `E*(R)` (maximal elem-ab) 述語層** | Lem 5.2, Thm 5.3 全面 | ❌ **未実装** — `E*(R)` (極大 elem-ab) の述語 (`IsMaximalElementaryAbelian` 的) と `E²∩E*` の handling が無い。**新規必須** |
| **`Z₂(R)=upperCentralSeries R 2`, `Ω₁(Z(R))`, `Ω₁(Z₂(R))`, `C_R(Ω₁(Z₂(R)))`** | Lem 5.2, Thm 5.3 | △ `upperCentralSeries` は mathlib にあり repo 使用例あり (`Isaacs/Ch01,Ch02`)。`Omega1OfAbelian` は `OmegaSubgroup.lean` にあるが **`Ω₁(Z₂(R))` 専用の補題層 (noncyclic, exp p, `[W,R]⊆Z`) は無い** |
| `IsExtraspecial` / `IsExpPExtraspecial` | (5.5(c) 経由 Thm 4.16) | ✅ `IsExtraspecial.lean` (def + projection) |
| `IsCentralProduct` | (Thm 4.16 経由) | ✅ `CentralProduct.lean` (新規, issue 0051) |
| `Omega` / `Agemo` | 全般 | ✅ `OmegaSubgroup.lean` |
| **coprime A-invariant 鎖の stabilization API** | Thm 5.5 | ⚠ **薄い** — `IsAInvariant` 述語が `CoprimeAction.lean`/`CoprimeConjugacy.lean` に grep ヒットせず。Thm 5.5 の "A-invariant chain `H=H_0⊃...⊃H_n=1`, 各 factor 位数 p, A' と α^{p-1} が stabilize" を組む土台が要整備 |

---

## 4. §5 → 下流供給 (なぜ critical path 上か)

**task の "§7 Thompson 推移性" framing の訂正**: §7 (Transitivity, mmd L2310 付近) の頂点 **Theorem 7.6 (Thompson Transitivity)** は `A∈SCN₃(p)` を **仮説として受ける**だけで §5 を cite しない (Gorenstein 8.5.4 のラッパー)。§5 の最初の実 downstream は **§8 (Uniqueness Theorem) L2324** の Remark "by Lemma 5.1, SCN₃(P)≠∅"。**§5 が critical path 上にある真因**:

- **Lemma 5.1(a)** (r(R)≥3 ⇒ SCN₃(R)≠∅) が、§7-§9 で `SCN₃(p)` を「空でない」状態で供給する。Transitivity/Uniqueness の議論は SCN₃ の元 A を取って `O_{p'}(C_G(A))` の transitive 作用を回すので、**SCN₃ が空でないことが前提**。L2629 (§9): "By Lemma 5.1, there exists A∈SCN₃(P)" が明示。
- **Theorem 5.5** が下流最多供給:
  - **§10 L2854**: `N_G(Q)'/C(Q)` が q-群 (Thm 5.5(a))。
  - **§10 L2817**: narrow Sylow ⇒ Thm 5.6 で M' に normal p-complement。
  - **§14 L4130**: `(DK)'=D` が Q を中心化 (Thm 5.5(a))。
  - **§15 L4188**: `r(P)=2` 強制 (Thm 5.5(b))。
  - **App.E/D L5164-5168**: Lemma 5.2 + Thm 5.3(d) + Thm 5.5 を narrow Sylow S に適用。
- **Theorem 5.3 / Cor 5.4** が **§10 L2643 の "ideal prime" 定義の基盤** (ideal ⟺ Sylow not narrow ⟺ `E²∩E*` empty)。§12 L3373/3379 で Cor 5.4 + Thm 5.3(d) を使い `p∉β(G)` 判定。⇒ §5 は §10-§16 全体に**定義的 forward dependency** を持つ。

**結論**: §5 は「narrow という FT 局所解析専用 class の構造定理 + automorphism 制御」を確立し、§8 以降の Uniqueness/Maximal-subgroup 解析の道具を供給する。critical path は **§4 (capstone) → §5 → §8/§9 (Uniqueness) → §10-§16**。

---

## 5. 既存資産レビュー

### 5.1 既存 `notes/bg/s05_narrow_pgroups.md` (2026-05-23 audit)

**正しい点 (再利用可)**:
- 7 結果リスト・mmd 行レンジ (L1789-1968) は正確。
- narrow 定義 §1 L354 正本の指摘、"r(R)≤2 は informal restatement" の指摘は正しい。
- "§5 は §4 を複数 distinct result で cite、実装順 §4→§5 strict" は正しい (本サーベイ §3 が裏付け)。
- Lem 5.1 が hub という指摘は正しい。

**stale / 訂正点**:
- **§10/§13 への cross-reference が "未定義番号、確認要" の推測**: 本サーベイ §4 で実 cite 箇所を確定 (§8 L2324, §9 L2629, §10 L2817/L2854, §12 L3373/3379, §14 L4130, §15 L4188, App.E L5164)。**§13 を主 downstream とした旧記述は誤り** (§13 L1313 の "Lemma 1.9" は別物、§13 は §5 を直接 cite せず)。
- **"§7 transitivity への供給" を主軸にした旧 framing は弱い**: §7 は SCN₃ を仮説受けするのみ。実供給先は §8/§9。
- **インフラ状況が古い**: `PRank.lean`/`SCN.lean`/`CentralProduct.lean`/`IsExtraspecial.lean`/`OmegaSubgroup.lean` は **2026-05-30 までに def + 基本補題が整備済**。旧ノートの "新規 100%" は def 層について過大。**ただし `E*(R)` 述語層・`Ω₁(Z₂(R))` 補題層・A-invariant 鎖層は依然未実装**。
- 旧ノートの "並行可 (§4 と同時進行)" は **誤り** (§3 の依存表より §4 capstone 完了が前提)。

### 5.2 `OddOrder/GroupTheory/SCN.lean` の SCN₃ 定義 (確認済)

- `IsSCN A` = `{A.Normal, IsMulCommutative A, centralizer (A:Set G) = A}` (structure)。
- `IsSCN_n p n A := IsSCN A ∧ n ≤ pRank A p`、`IsSCN₃ p A := IsSCN_n p 3 A` (abbrev)。
- **`m(A) ≥ n` を `n ≤ pRank A p` で表現**する設計 (abelian A では `m(A)=pRank A p`)。Lem 5.1 の "SCN₃(R)≠∅" は `∃ A, IsSCN₃ p A` で表せる。
- `isSCN_iff_isMaximalAbelianNormal` (Prop 4.4(a), p-群) 利用可。Lem 5.1(b) の "maximal-abelian-normal ⇒ SCN" の向きはこれで取れる。

### 5.3 再利用できる mathlib / repo インフラ

- **mathlib**: `upperCentralSeries G n` (Z_n(G)、`Z₂=upperCentralSeries G 2`)、`Subgroup.center`、`Subgroup.centralizer`、`Subgroup.IsElementaryAbelian` (repo 拡張)、`IsPGroup` 全般、`commutator`/`⁅·,·⁆` API。
- **repo**: `pRank`/`rank` 評価補題群、`IsSCN`/`IsSCN₃`、`Omega`/`Agemo`/`omega1OfAbelian`、`thompson_critical_omega` (Thm 1.13、Thm 5.5 用)、Lem 1.9 2-step (`S01_Solvable.lean:656`)、`IsCentralProduct`/`IsExtraspecial` (Thm 4.16 接続用)。
- **要新規**: `E*(R)` (極大 elem-ab) 述語 + `E²∩E*` 補題、`Ω₁(Z₂(R))` の noncyclic/exp-p/`[W,R]⊆Z` 補題 (Lem 4.5(c) 依存)、A-invariant 鎖 stabilization (Thm 5.5)、Lem 1.22 (p-群の normal subgroup 内に各位数の normal subgroup)。

---

## 6. Gorenstein 行間

**§5 本文 (L1789-1967) 中の "**G**, Thm X.Y.Z" cite は 1 箇所のみ**:

- **Thm 5.5(c) proof, L1941**: "As q does not divide p-1, by **G**, Theorem 5.4.1, p.189, A centralizes R/Ω₁(R)."
  - **実体**: Gorenstein の "p′-群 A が odd p-群 P の `Ω₁(P)` 上 trivial に作用 ⇒ A=1" (= `references/gorenstein/finite-groups.mmd` の **Theorem 3.10** L3897: "*If A is a p′-group of automorphisms of the p-group P with p odd which acts trivially on Ω₁(P), then A=1*"; abelian 版は **Theorem 2.4** L3751)。BG の printed numbering "5.4.1" は Gorenstein 1968 (1st ed) の章節、mmd は 1980 (2nd ed) で chapter-relative 表記のため番号ずれ。**substance は同一**。
  - **使い方 (Thm 5.5(c))**: r(R)≤2 分岐で `R=[R,A]`, R 非abelian、Thm 4.16 より `|Ω₁(R)|=p³`, `R/Ω₁(R)` cyclic。A が `R/Ω₁(R)` を中心化 (Gorenstein 3.10 の系: `q∤p-1` ⇒ cyclic factor 上 trivial)、`[R,A]=R` から `R=Ω₁(R)`、よって `|R|=p³`。
  - **Isaacs 対応 (優先確認)**: Isaacs Ch04 §4D に `isaacs_thm_4_36` (一般 p-群版) / Cor 4.35 (`actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p`) が **sorry-free で存在** (s04 plan §0-4 が確認)。これは「p′-作用が位数 p 元 (=Ω₁) を固定 ⇒ trivial 作用」型で **Gorenstein 3.10 とほぼ同値**。**⇒ Gorenstein をゼロから書く必要はなく、Isaacs 4.35/4.36 への読み替えで賄える公算が高い** (CLAUDE.md 方針: Isaacs 優先)。実装時に `actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p` の仮説 (cyclic factor / coprime) が Thm 5.5(c) の状況に合うか要確認。

**ゼロから書く必要がある Gorenstein 行間 (§5 直接ではなく §4 経由)**: §5 の §4 依存 (Lem 4.5(a) Gorenstein 5.4.10, Lem 4.5(b) 5.4.3/5.4.4, Lem 4.7⇒ 5.4.15, Lem 4.15 5.4.6) は **§4 側で処理**。§5 実装者は §4 完了を前提にできる (§3 のゲート参照)。

---

## 7. sub-issue 分割案 + 工数 + 山場

**前提ゲート (§5 着手の必要条件)**: 以下の §4 結果が Lean で完成していること。**未完なら §5 は forward axiom で statement だけ置くか、§4 Wave 2 完了を待つ**。
- Lem 4.5(c) (`Ω₁(Z₂(R))` noncyclic exp p) — Lem 5.2 が直接使う。
- Lem 4.7 ⇒ (r≥3 ⇒ SCN₃≠∅) — Lem 5.1(a) の本体。
- Lem 1.22 (p-群 normal sub 内の各位数 normal sub) — Lem 5.1(b)。
- Prop 4.4(a) ✅ 済。
- (Thm 5.5/5.6 まで進むなら) Thm 4.16, Lem 4.14, Lem 4.17, Thm 4.18。

工数: S=半日, M=1-2日, L=3-5日, XL=1週間+。依存順 = 実装シーケンス。

| # | sub-issue | 内容 | 工数 | 依存 | 山場? |
|---|---|---|---|---|---|
| **S5-0** | **`E*(R)` 述語 + `Ω₁(Z₂(R))` 補題層** (新規 infra) | `IsMaximalElementaryAbelian` 述語、`E²∩E*` の handling、`Z=Ω₁(Z(R))`/`W=Ω₁(Z₂(R))`/`T=C_R(W)` の基本補題 (`Z⊆W`, `[W,R]⊆Z`, W noncyclic exp p via Lem 4.5(c))。`upperCentralSeries G 2` ラップ。 | **L** | Lem 4.5(c) (§4) | — (機械的だが量がある) |
| **S5-1** | **Lemma 5.1** (a)(b) | (a) = Lem 4.7⇒ 直用 (`∃ A, IsSCN₃ p A`)。(b) = Lem 1.22 で normal `B`(位数p³) 取り、`B*=E·C_B(E)`、Prop 4.4(a) で SCN₃ 元へ拡大。 | **M** | S5-0, Lem 4.7⇒, Lem 1.22, Prop 4.4(a) | — |
| **S5-2** | **Lemma 5.2** (a)(b)(c) | central structure: `EZ=E`⇒`Z⊆E`, `r(C_R(E))=2`, `|Z|=p`; `Z⊂W`, `[W,R]⊆Z`; `C_W(E)=Z`, `|W/Z|=p`, `|W|=p²`; `|R/T|=p`, T char。 | **L** | S5-0, S5-1 (5.2 が 5.1 を L1826 で使う) | **★山場 (A)** |
| **S5-3** | **Theorem 5.3** (characterization + (a)-(d)) | ⇒: narrow ⇒ R₀ 取り `E=Ω₁(C_R(R₀))∈E²∩E*`、Lem 5.2 で (a)(b)(c); (d) は S 位数p, `r(C_R(S))≤2` から `SZ∈E²∩E*`, `S∩T=S∩R'=1`, `R=ST`, `C_R(S)=S×C_T(S)`, `C_T(S)` cyclic。⇐: `E∈E²∩E*` ⇒ `E=Z×S`, `C_R(S)` 経由で narrow。 | **L** | S5-2 | **★山場 (A 延長)** |
| **S5-4** | **Corollary 5.4** | `r(R)≥3` ⇒ (narrow ⟺ ∃S位数p, `r(C_R(S))≤2`)。Thm 5.3 + `SZ∈E²∩E*` の短い往復。 | **S** | S5-3 | — |
| **S5-5** | **coprime A-invariant 鎖 stabilization infra** (新規) | Thm 5.5 用: A-invariant な `H=H_0⊃H_1⊃...⊃H_n=1` (各 factor 位数 p) を `H_i=[R,H_{i-1}]` で構成し、A' と α^{p-1} が stabilize ⇒ Lem 1.9 で `A/C_A(H)` 制御。`x↦[v,x]` 写像で `|H_{i+1}|≥p^{-1}|H_i|` の鎖長 = n 補題。Lem 1.9 の **n-step 版**が要るか確認 (現状 2-step)。 | **L** | Lem 1.9 (一般化要?), S5-4 | **★山場 (B 土台)** |
| **S5-6** | **Theorem 5.5** (a)(b)(c) | Thm 1.13 で H 取得 (`thompson_critical_omega`)。**r≥3 分岐**: R₀ 取り `R₀⊄H`, `|C_H(R₀)|=p`, H_i 鎖で (a)(b)。**r≤2 分岐**: (a)=Lem 4.17、(c)=Lem 4.14/4.16 + Gorenstein 5.4.1(=Isaacs 4.35)。 | **XL** | S5-5, Thm 1.13✅, Lem 4.17, Lem 4.14, Thm 4.16, (Isaacs 4.35) | **★★山場 (B 本体)** |
| **S5-7** | **Theorem 5.6** (a)-(e) | r≤2 ⇒ Thm 4.18 直用; r≥3 ⇒ Thm 5.5 + Thm 4.18 の証明法を移植。 | **L** | S5-6, Thm 4.18 | △ (Thm 4.18 依存) |
| **S5-8** | **Theorem 5.7** | G' が `U/V` (chief factor, `U⊆F(G)`) を中心化。`R=O_q(G)` が narrow を Thm 5.3 で示し、Thm 5.5 で G' が q-群作用 ⇒ `O_q(G/C_1)=1` から `G'⊆C_1`。 | **M** | S5-3, S5-6 | — |

**実装シーケンス**: S5-0 → S5-1 → S5-2 → S5-3 → S5-4 → S5-5 → S5-6 → S5-7 → S5-8。
S5-0/S5-1/S5-2/S5-3/S5-4 (Lem 5.1-Cor 5.4) は **Thm 4.16/4.17/4.18 不要**で、Lem 4.5(c)/4.7⇒/1.22 + Prop 4.4(a) のみで完結 ⇒ **§4 Wave 2 の一部 (4.16 等) を待たずに着手可能な前半**。S5-5 以降 (Thm 5.5-5.7) は §4 capstone 全部が前提。

### 山場 (scaffold-hoisting 誘惑、hoist 禁止・本物で証明すべき)

memory `scaffold-sorry-free-not-done` 厳守。以下は hard content を未充足仮説に逃がしやすい:

1. **★山場 (A) = Lemma 5.2 + Theorem 5.3 (S5-2/S5-3)**: `|Ω₁(Z(R))|=p`, `Ω₁(Z₂(R))∈E²(R)`, `T=C_R(Ω₁(Z₂(R)))` が char index p、という central structure。**逃げの誘惑** = これらを `(hZ : |Z|=p) (hW : W∈E²) (hT : [R:T]=p) →` の仮説束にして Thm 5.3 を "sorry-free" に見せる。**禁止**: `Ω₁(Z₂(R))` 層 (S5-0) を実装し、`[W,R]⊆Z`/`C_W(E)=Z`/`|W/Z|=p` を `⁅·,·⁆` API と `Aut E` への埋め込み (`W/C_W(E) ↪ p-Sylow of Aut E`) で**本当に**導く。`r(C_R(E))=2` の導出 (`E∈E*` から) も本物で。

2. **★★山場 (B) = Theorem 5.5 r≥3 分岐 (S5-5/S5-6)**: A-invariant 降鎖 `H=H_0⊃...⊃H_n=1` (各 factor 位数 p) と Lem 1.9 stabilization で `A/O_p(A)` abelian p′ + p′-元 order ∣ p-1。**逃げの誘惑** = 鎖の存在・stabilization・Lem 1.9 の n-step 版を仮説に hoist。**禁止**: `H_i=[R,H_{i-1}]` の構成、`x↦[v,x]` 写像で `|H_{i+1}|≥|H_i:C_{H_i}(v)|≥p^{-1}|H_i|` (mmd L1925)、各 `H_i char R`、鎖が A' と α^{p-1} で stabilize される (Lem 1.9 適用) を**実際に**書く。Lem 1.9 が 2-step instance のみなら **n-step 一般化を先に S5-5 で実装**(これ自体が独立 sub-issue 価値)。

3. **準山場 = Thm 4.16 への接続 (Thm 5.5(c), S5-6)**: Thm 4.16 (§4、未完) の結論 `|Ω₁(R)|=p³ & R/Ω₁(R) cyclic` を使う。**Thm 4.16 が未完なら Thm 5.5(c) も完成しない** — ここは §4 ゲートに正直に従い、Thm 4.16 を仮 axiom 化して進めるか §4 完了を待つ。Gorenstein 5.4.1 部分は **Isaacs 4.35 (`actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p`) への読み替えを最優先**で試す (ゼロから Gorenstein を書かない)。

---

## 8. 着手チェックリスト (cold-start 用)

1. `references/bg/local-analysis.mmd` L1789-1967 を Read (本サーベイ §1 の行レンジ)。**L1957 のゴースト §6 ヘッダに注意**。
2. §4 ゲート確認: `grep scn3_empty_of_pRank_le_two`, Lem 4.5(c)/Lem 1.22/Thm 4.16/4.17/4.18 の Lean 完成状況を再確認 (本サーベイ §3、issue 0051 の進捗)。未完なら前半 (S5-0〜S5-4) に絞る。
3. 新規 infra (S5-0) を `OddOrder/GroupTheory/` に: `E*(R)` 述語 (`ElementaryAbelian.lean` 拡張 or 新規)、`Ω₁(Z₂(R))` 補題 (`OmegaSubgroup.lean` 拡張)。`upperCentralSeries G 2` を使う。
4. 形式化先 = `OddOrder/BG/Ch1_Preliminary/S05_NarrowPGroups.lean` (新規)。トレーサビリティ 3 層 (冒頭 `/-! # ... -/` に "BG §5, mmd L1789-1967, pp.44-48"、`section /- 5.x ... -/`、docstring 冒頭 `**BG Lemma 5.x**`)。命名は記述的 (`narrow` / `isNarrow` / `scn3_nonempty_of_three_le_rank` 等、番号を識別子に入れない)。
5. issue 採番: main レンジ (base 0) で `bin/new-issue` (Peterfalvi=1000 固定なので衝突なし)。S5-0〜S5-8 を個別 issue 化推奨。
6. scaffold trap: 山場 (A)(B) は memory `scaffold-sorry-free-not-done` 厳守。Verify は hypothesis constructibility で。`/goal` 単発は design/multi-sub 型の §5 には不適 (memory `goal-command-spec`)。

---

## 付録: narrow の Lean 定義案

§1 L354 正本に忠実に (r(R)≤2 は導出される副次条件、定義には入れない方が素直):

```
/-- **BG narrow p-group** (§1 p.2, π* on FT p.845). R は narrow ⟺
位数 p³ の elementary abelian 部分群を含まない、または
位数 p の R₀ と cyclic R₁ で C_R(R₀)=R₀×R₁ となるものを持つ。 -/
def IsNarrow (p : ℕ) (R : Type*) [Group R] : Prop :=
  pRank R p ≤ 2 ∨ ∃ R₀ R₁ : Subgroup R, Nat.card R₀ = p ∧ IsCyclic R₁ ∧
    Subgroup.centralizer (R₀ : Set R) = R₀ ⊔ R₁ ∧ ... (内部直積条件)
```
(注: "no elem-ab of order p³" ⟺ `pRank R p ≤ 2` は Lem 4.7 で同値。定義に `pRank≤2` を採るか "no E_p³" を採るかは実装時判断。直積 `R₀×R₁` は `IsInternalDirectProduct` 的な条件で表現。Thm 5.3/Cor 5.4 が rank≥3 での同値刻画を与えるので、定義はこの素朴形で十分。)
