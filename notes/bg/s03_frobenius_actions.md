# BG §3: Actions of Frobenius Groups and Related Results — mini-roadmap

**スコープ**: BG §3 (pp.17-32), mmd L795-1358, **10 結果** (Lemma 3.1-3.10).
形式化先 (予定): `OddOrder/BG/Ch1_Preliminary/S03_FrobeniusActions.lean`
ROADMAP 上の位置: **Phase 2a 第 2 波** (Phase 1 Ch.6 Frobenius groups 完成必須)
役割: **Isaacs Ch.6 の BG 流再展開 + 表現論的 Frobenius action**. Frobenius kernel の nilpotent 性と vector module 上の作用理論を統合.

## TL;DR

BG §3 は Isaacs Ch.6 "Frobenius Actions" を基盤として、**表現論的な拡張と solvable group の制約**を加えた章. 全 10 結果で Frobenius group の基本性質 (kernel/complement 分解, quotient 保存) から始まり、odd order + Hall subgroup の仮定で Frobenius kernel が nilpotent であること (Thompson), さらに vector module への作用で K' (commutator subgroup) の centralization を導く主要定理群を展開. **Peterfalvi §10-§14 で maximal subgroup 分類の核となる Frobenius 群定義・性質を参照**.

## §3 全 10 結果

| 番号 | 種別 | 行 | 内容 (1行要約) | Isaacs 対応 | 主要性 |
|------|------|-----|----------------|-----------|---------|
| **3.1** | Lemma | 797-819 | Frobenius 群の等価条件: KR 分解 ⇔ C_K(x)=1 ∀x∈R^# | 6.4 / 6.7 | ◎ 定義 |
| **3.2** | Lemma | 820-843 | quotient Frobenius 保存: G=KR ⊳ N, K⊄N ⇒ G/N Frobenius | 6.2 + 6.7 | ✅ 完了 |
| **3.3** | Lemma | 845-862 | 表現論的 fixed point: K nontrivial on V, char∤\|K\| ⇒ C_V(R)≠0 | **Ch.6 拡張** | ◎ 新規 |
| **3.4** | Theorem | 863-902 | odd order Hall: C_V(R)=0 ⇒ [R,K]⊆C_K(V) | **Ch.6 拡張** | ☆ 表現論的分析 |
| **3.5** | Theorem | 903-951 | cyclic R, dim C_V(R)=1 ⇒ K'⊆C_K(V) | **Ch.6 拡張** | ★ 重要 |
| **3.6** | Theorem | 953-1196 | Z-group centralizer: C_H(R_0) Z-群 ⇒ [H,R] p-length 1 | **新規** | ★ 構造定理 |
| **3.7** | Theorem | 1199-1219 | Frobenius kernel nilpotent (prime complement): C_K(R)=1 ⇒ K nilpotent | 6.24 再述 | ◎ Thompson |
| **3.8** | Theorem | 1221-1259 | [K,R]⊆F(K): 3 条件 ⇒ commutator が Fitting に | **新規** | ★ Fitting 分析 |
| **3.9** | Proposition | 1261-1265 | Regular action: p 奇数, R p-group 正則作用 ⇒ R cyclic | **新規** | ◎ 補助 |
| **3.10** | Theorem | 1267-1357 | Frobenius on nilpotent: G=KR Frobenius, M nilpotent, 3条件 ⇒ R cyclic, 位数公式, K'⊆C_K(M) | **新規** | ★ 最大 |

**小計**: 3 結果が Isaacs 再述 (3.1, 3.2, 3.7), 7 結果が Isaacs からの新規拡張 (3.3-3.6, 3.8-3.10).

## Lemma 3.2 (quotient Frobenius) — Isaacs 6.2 との対応

**BG L820-843**. Isaacs Ch.6 Corollary 6.2 の精密版.

### Statement

G=KR が solvable Frobenius kernel K, complement R を持つとき, N⊳G で K⊄N ⇒
(a) N⊂K (proper)
(b) Ḡ:=G/N は Frobenius 群, kernel K̄, complement R̄

### Phase 1 (Isaacs Ch.6) との接続

- **Isaacs 6.2**: "A-invariant 正規 M ⇒ N/M 上の A 作用も Frobenius"
- **BG 3.2(a)**: N⊂K を先に証明し, その後全体を Frobenius に

### 証明の流れ

1. **First case (N⊆K)**:
   - Lemma 3.1 を quotient に適用: C_K̄(x̄)=1 ∀x∈R^# ⇒ Ḡ Frobenius
   - Lean status (2026-05-25): `quotient_complement_of_normal_le_kernel`,
     `quotient_kernel_map_ne_bot_of_not_le`,
     `quotient_complement_map_ne_bot_of_le_kernel`,
     `fixedPoint_lift_of_zpowers_quotient_fixed`,
     `zpowers_quotient_fixed_of_generator_quotient_fixed`,
     `fixedPoint_lift_of_generator_quotient_fixed`,
     `quotient_centralizer_inf_kernel_eq_bot_of_fixedPoint_lift`,
     `quotient_isFrobeniusGroup_of_le_kernel_of_centralizer`,
     `quotient_isFrobeniusGroup_of_le_kernel_of_fixedPoint_lift`,
     `quotient_isFrobeniusGroup_of_le_kernel_of_coprime_zpowers` を
     `OddOrder.BG.Ch1.S03` に追加. Prop 1.5(d) / Isaacs Cor 3.28 の
     cyclic-action 包装は完了し, first case は
     `Nat.Coprime |⟨x⟩| |K|` と `IsSolvable K` を明示仮定に切り出した形まで
     Lean 化済み. 残りはこの coprimality を Frobenius setup から導く補題と,
     general case (`H := N ∩ K`) の合成.

2. **General case**:
   - H:=N∩K とし, Ĝ:=G/H で同じ議論を反復
   - [N∩R, K]⊆H ⇒ [N̂∩R̂, K̂]=1
   - Ĝ Frobenius (by case 1) かつ K̂^x∩K̂=1 ⇒ Ĝ Frobenius (Lemma 3.1)
   - ⟹ 最終的に N⊆K

### mathlib への影響

- **新規**: `FrobeniusGroup.quotient` — Frobenius 群の商が Frobenius
- **既存利用**: Proposition 1.5(d) (centralizer 商, Isaacs + BG Ch.1 で実装予定)
- **前提**: Frobenius 群定義そのもの (Phase 1 Ch.6 で実装)

### Phase 2a での着手

3.2 の形式化は **Ch.6 完成直後の Phase 2a 第 2 波初期**に配置. 難度は **中** (induction + 3 つの Lemma 3.1 適用だが, 記号が複雑).

## Frobenius kernel nilpotent — L825 周辺と Isaacs 6.24

**BG L825 Note**: "Since Thompson's Thesis (G, Theorem 10.2.1, p. 337) implies that the kernel of a Frobenius group is nilpotent (G, Theorem 10.3.1(iii), p. 339)".

### BG の扱い

BG は Lemma 3.2 の直後, すぐに Thompson の結果を引用 (proof なし). 理由は:
- **solvable 仮定を外すため**: Lemma 3.2, 3.5, 3.8 の「solvable kernel」仮定は Thompson により不要
- **後続定理との整合**: Theorem 3.7 (prime complement → nilpotent) で再証明する方針

### Isaacs Ch.6 6.24 との対応

| Isaacs | BG | 説明 |
|---|---|---|
| 6.22 | L1199-1219 (Thm 3.7) | solvable Frobenius kernel ⇒ nilpotent (Higman) |
| 6.23 | — | Thompson normal p-complement ✅ (`Isaacs/Ch06_FrobeniusActions/ThompsonPComplement.lean`, Ch.7 Thm 7.1 から導出) |
| 6.24 | L825 Note | Frobenius kernel ⇒ nilpotent (Thompson, 一般版) |

### Phase 2a での扱い

**Theorem 3.7 (L1199-1219)** で solvable 限定版を証明してから, Thompson axiom を **`axiom` として一時的に置く** か, または **Phase 1 Ch.7 で Thompson normal p-complement を先に完成させる** ことで後付け. 予定としては:

- Phase 2a 第 3 波: Thm 3.7 形式化 (induction + Lemma 3.1, 3.3 利用)
- Phase 1 Ch.7 完了後: Thompson p-complement → 3.7 の拡張で 3.24 equivalent を記述

## 表現論的 Frobenius action — Lemma 3.3, Theorem 3.4, 3.5

### Lemma 3.3 (Fixed Point on Modules)

**L845-862**. Wielandt 固定点定理の代数的バージョン.

**Statement**: G=KR Frobenius, V 上に作用 (char F ∤ |K|), K nontrivial on V ⇒ C_V(R) ≠ 0.

**Proof 概略**:
1. 群環 FG の元 R̄ := Σ_{r∈R} r を考える
2. G = K ∪ ⋃_{x∈K} R^x (disjoint union) を利用
3. v ∈ V に対し v·R̄ = 0 ⇒ |K|·v = v·K̄ (algebra の計算)
4. char F ∤ |K| ⇒ K が V に自明に作用 (矛盾)

**mathlib との接続**: 
- **新規**: `FrobeniusGroup.centralizer_nonzero_representation`
- **既存利用**: Maschke's Theorem (1.20), 群環の module theory (`Mathlib.RepresentationTheory`)

### Theorem 3.4 (C_V(R)=0 ⇒ commutator condition)

**L863-902**. odd order + Hall subgroup 設定で, complement 作用の非自明性から commutator の centralization を導く.

**Statement**: 
- G = solvable odd order, K normal Hall, |R|=p prime
- G acts on V, char F ∤ |G|, C_V(R)=0
- ⇒ [R,K] ⊆ C_K(V)

**難度**: ★★★ (大). 最小反例を取り, minimal normal subgroup analysis, extraspecial p-group, Theorem 2.6 (odd order 2-dimensional), Thompson normal p-complement (6.23) 等を組み合わせ, Clifford's Theorem で Wedderburn components の transitive action を分析. 証明は 30 行超.

### Theorem 3.5 (dim C_V(R)=1 ⇒ K'⊆C_K(V))

**L903-951**. cyclic prime complement, 1-dimensional fixed space 限定. Theorem 3.4 より技術的に細かい.

**難度**: ★★★ (中の上). induction on |G|, Lemma 3.3 + Theorem 3.4 の反復適用, Clifford's Theorem で irreducible K-module の構造分析.

### Phase 2a での配置

Lemma 3.3 (簡潔, 15行) → Theorem 3.4 (大型, 40行) → Theorem 3.5 (中型, 45行) の順で **Phase 2a 第 2 波中盤～後盤** に配置. Isaacs Ch.6 完成 + representation theory 基礎準備 (mathlib + Phase 1 Ch.2 Fitting, Ch.3 Hall) 完了後.

## Theorem 3.6 (Z-group centralizer) と p-length 構造定理

**L953-1196**. 最も複雑な定理. 244 行の大型証明.

**Statement**:
- G = solvable odd order
- H normal Hall subgroup, R complement
- R_0 ⊆ R subgroup of prime order r
- C_H(R_0) は Z-group (all Sylow cyclic)
- p arbitrary prime
- ⇒ [H,R] has p-length one

**構造**:
- (3.6) H = [H,R] (no proper R-invariant subgroups)
- (3.8) O_{p'}(H) = 1
- (3.9)-(3.10) V:=F(H) は elementary abelian p-group
- (3.14)-(3.15) K := N_H(complement) の構造, K=F(N_H(K))
- (3.17)-(3.21) [K,R_0]≠1, C_V(R_0)=p, C_P(R_0)=1 の連鎖
- (3.22)-(3.25) K は special q-group (q≠p, q≠r)
- (3.28)-(3.30) C_K(R)=1, C_K/K'(R)≠1
- (3.31)-(3.36) |C_K(R)|=q, K elementary abelian
- (3.37)-(3.43) |K|>q^2 の示唆から V の直和分解へ
- 最終: |K|>q^2 と |K| の dual-orbit analysis から矛盾

**難度**: ★★★★ (最難). **BG 全体でも屈指のテクニカル証明**. Phase 2a の山場.

**Phase 2a での配置**: Theorem 3.7 (prime complement nilpotent) の **直後, Phase 2a 第 3 波** に配置. Thm 3.6 形式化は **2 週間コスト見積もり** (induction + 複数の critical sub-lemma: (3.8) の p'-Fitting, (3.19) の cyclic order p, (3.36) elementary abelian 判定, (3.37) の |K|>q^2 arithmetic).

## Peterfalvi §10-§14 からの被引用

### (9.1) Wielandt 固定点定理

**Peterfalvi 04.11 L5**: "Let U⋊E be a Frobenius group with kernel U. Assume that UE acts on a finite solvable group H...". Frobenius 群と solvable group coprime action の設定で, Wielandt 原論文 ([HB] XI 12.4) を引用.

⟹ **BG 3.3 (Lemma) を基盤として Peterfalvi (9.1) が構築される**. Phase 2a 后半の Peterfalvi 同期始期.

### Proposition 3.9 (Regular action ⇒ cyclic)

**Peterfalvi 04.10 L1, 04.15 L3**: "[BG], Proposition 3.9 ⇒ Frobenius complement of odd order has cyclic Sylow".

⟹ **BG 3.9 の direct 引用**. 形式化は短い (5 行 proof, Burnside p-group theory).

### Lemma 3.2 (quotient Frobenius)

**Peterfalvi 04.15 L60**: "By [BG], Lemma 3.2, K ⊂ C_{KW_2}(W_1)".

⟹ quotient に持ち上げた Frobenius 性質を maximal subgroup 分類で活用. Phase 2a 後半の技術的基盤.

**合計被引用**: Peterfalvi §4 内で BG §3 の 3 結果 (Lem 3.2, Prop 3.9, Thm 3.6 implicit) が Frobenius 群定義・構造の中核をなす.

## mathlib カバレッジ

| 項目 | 状況 | コスト |
|------|------|--------|
| **FrobeniusGroup 定義** | Phase 1 Ch.6 で新規実装 | 大 (Phase 1) |
| 3.1 Lemma (等価条件) | Ch.6 の系 | 短 |
| 3.2 quotient Frobenius | 新規 | 中 |
| 3.3 fixed point on modules | 新規 (群環 theory) | 中 |
| 3.4 C_V(R)=0 condition | 新規 (representation + Clifford) | 大 |
| 3.5 1-dimensional fixed space | 新規 | 大 |
| 3.6 Z-group centralizer | 新規 (複雑) | 大 |
| 3.7 kernel nilpotent (solvable) | Isaacs 6.22 再実装 | 中 |
| 3.8 [K,R]⊆F(K) | 新規 | 大 |
| 3.9 regular cyclic | 新規 (短) | 短 |
| 3.10 Frobenius on nilpotent | 新規 | 中 |

**新規実装の度合い**: §3 全体で **90%** (Isaacs Ch.6 の精緻化 + 表現論拡張).

## Phase 2a 形式化着手順

### Wave 1 (Phase 1 Ch.6 完成直後)
1. **3.1** Lemma: Ch.6 Thm 6.4 / 6.7 の系として. 難度 **低**.
2. **3.2** Lemma: quotient Frobenius. 難度 **中**. induction が key.
3. **3.9** Proposition: regular cyclic. 難度 **低**. Burnside p-group.

### Wave 2 (App.A p-Stability + Ch.7 Thompson 準備期)
4. **3.3** Lemma: fixed point modules. 難度 **中**. Wielandt + 群環.
5. **3.7** Theorem: solvable kernel nilpotent (Thompson solvable 版). 難度 **中**.

### Wave 3 (§1-§6 完成後, Phase 2a 中盤)
6. **3.4** Theorem: C_V(R)=0 ⇒ commutator. 難度 **大** (最小反例, Clifford, Wedderburn).
7. **3.5** Theorem: 1-dimensional C_V(R). 難度 **大** (3.4 の反復応用).
8. **3.10** Theorem: Frobenius on nilpotent. 難度 **中** (3.3-3.5 の統合).

### Wave 4 (Phase 2a 終盤、Peterfalvi 準備期)
9. **3.6** Theorem: Z-group centralizer p-length. 難度 **最難** (244行 proof, orbit analysis, elementary abelian 判定, |K|>q^2 arithmetic).
10. **3.8** Theorem: [K,R]⊆F(K). 難度 **大** (induction + chief factors).

**推定スケジュール**: 3.1-3.3, 3.7, 3.9 で 2-3 週間, 3.4-3.5, 3.10 で 3-4 週間, 3.6, 3.8 で 4-5 週間. **合計 9-12 週間 (Phase 2a 約 30% コスト)**.

## 未解決 / TODO

1. **Theorem 3.4 の counterexample** (L865, SL(2,3) over F_p, p>3): 特定の構成が FT で本質的かどうか検証不要 (phase 2a では statement level で OK).

2. **Theorem 3.6 の orbit analysis** (L1169-1195): 群の作用による orbits の parity argument. **実装時に Lean の `Fintype.card` と `action.orbit` で機械化できるか検証必要**. 特に L1177-1180 の "v + vx + ... + vx^{r-1} ∈ C_V(R)" の群環表現から projections への転換.

3. **Phase 1 Ch.7 Thompson normal p-complement** (6.23) との連携: BG は L825 で statement のみ引用. Phase 1 でこれを完成させれば, BG 3.7 の証明を「solvable ⇒ general」へ自動拡張可. **Phase 1 終盤での調査要**.

4. **Peterfalvi §10-§14 との同期**: Phase 2a 後半で Peterfalvi を開始する際, (9.1) Wielandt の正確な statement が BG 3.3 / Isaacs 6.2-3 のどちらと対応するか明確化. Peterfalvi 原論文 [22] の 確認有益かもしれない (Phase 2a 進行中に判断).

## Landing log

- **2026-06-23 (lane-h): BG Lemma 3.2 完全版 (K⊄N 枝) landed** (`S03_FrobeniusActions.lean`, sorry-free +
  axiom-clean, AxiomsCheck 登録). repo は従来 Lemma 3.2 の **`N ≤ K` 枝のみ** だった
  (`quotient_isFrobeniusGroup_of_le_kernel_of_*`); 未実装の一般枝 `K ⊄ N` を補完:
  - `inf_complement_eq_bot_of_normal_not_le_kernel` — crux: `N ⊓ R = ⊥` (mmd L837-843)。証明 =
    `Ĝ = G/(N⊓K)` を `N≤K` 枝で Frobenius 化 → `[N⊓R, K] ⊆ N⊓K` ゆえ `K̂` が像 `Ĵ` を中心化 →
    `trivialIntersection` で `Ĵ ⊆ R̂ ⊓ R̂^x̂ = ⊥` → `N⊓R ⊆ N⊓K ⊆ K`, かつ `⊆ R` ゆえ `⊆ K⊓R = ⊥`。
  - `normal_le_kernel_of_not_le` — 3.2(a): `N ≤ K` (crux + `kernel_eq_notConjugateSet` (Cor 6.6) + 正規性)。
  - `isFrobeniusGroup_quotient_of_normal_not_le_kernel` — 3.2(a)+(b): `N < K` ∧ `Ḡ=G/N` Frobenius
    (`N≤K` 枝に帰着)。仮説 = `[Finite G]` + `IsSolvable ↥K` (BG 同様; Thompson で solvable は本来不要)。
  - 下流: Pf (13.16) `normalizer_W1` step 5 (K ⊆ C(W₁)) の obligation を解消 (但し (13.16) full は残 5
    obligation が cross-lane gate)。reusable infra。

---

*作成: 2026-05-22. 出典: BG `references/bg/local-analysis.mmd` L795-1358. Isaacs Ch.6 ノート (`notes/isaacs/ch06_frobenius_actions.md`) との対応確認済. 下流被引用 (Peterfalvi §10-§14) 確認済.*
