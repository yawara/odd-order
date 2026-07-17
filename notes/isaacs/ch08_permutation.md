# Isaacs Ch.8: Permutation Groups — mini-roadmap

> ✅ **COMPLETE (2026-07-17, lane b)** — 実作業ギャップ 25 件 (survey note 判定)
> を全て sorry-free で形式化。mathlib 既収載分 (8.1/8.2/8.11-8.22/8.27-8.30 等)
> はラッパー方針によりそのまま利用 (本文 docstring で対応記録)。
>
> **ファイル対応** (`OddOrder/Isaacs/Ch08_PermutationGroups/`):
> - `AffineGroup` (Cor 8.7)、`NonzeroVectors`/`RegularNormal` (支持)、
>   `TransitiveAutomorphisms` (Lem 8.8)、`HalfTransitive` (Thm 8.9, Lem 8.10)
> - `CycleCommutators` (Lem 8.24, 8.25)、`PCycleJordan` (Thm 8.23; mathlib の
>   `proof_wanted` 解消)、`Bochert` (Thm 8.26)
> - `TransvectionGeneration` (Thm 8.31, 8.32)、`PSLSimple` (Thm 8.33、
>   仮定は honest 一般化 `3 ≤ card ∨ ∃ β ≠ 0, β² ≠ 1`)
> - `Orbitals` (Lem 8.34)、`OrbitalGraph` (Thm 8.35, Lem 8.36)、
>   `Subdegrees` (Thm 8.37 gap 形一般化, Thm 8.38 Weiss, Lem 8.39(a-c),
>   Thm 8.40 Manning + relIndex 橋 API)、
>   `CommonDivisorGraph` (m-arrow/`[α]_m`/K_m 装置, Thm 8.42(a)(b),
>   Thm 8.41 ≤3 成分, Thm 8.43, Cor 8.44 semidirect 転写)
>
> 次クラスタ (lane b): Pf App Suzuki (32 件) → Suzuki2Groups (8 件)。

**スコープ**: Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) Ch.8 (pp. 223-270).
形式化先 (予定): `OddOrder/Isaacs/Ch08_Permutation.lean` (未作成).
原典抽出: `references/isaacs/finite-group-theory.mmd` lines 4059-4878.
ROADMAP 上の位置: **第 1 波 (前提なし、mathlib 既存資産で薄く)** — Ch.1 のみが軽い前提。
4 視点 framework 適用 (2026-05-23 audit 統合): 詳細クロス参照 [`../meta/ch08_10_audit_2026_05_23.md`](../meta/ch08_10_audit_2026_05_23.md).

## 章のセクション分割と全 44 定理

Isaacs Ch.8 は § 8A–8D の **4 節構成** (8E は無し)。mmd 抽出では `### 8a`, `### Problems 8a`,
`### Problems 8b`, `### 8c`, `### 8d`, `### Problems 8C`, `### Problems 8D` は捕捉できているが、
`### 8b` のヘッダ自体は抽出失敗で欠落。境界は本文の "block / primitive" 定義の入り方と
Problems 8a/8b フッタ位置から確実に同定可能 (8b は L4299 の block 定義から)。

| § | mmd 行 | 内容 | Isaacs 番号 | 主要結果 |
|---|---|---|---|---|
| 8A | 4061-4298 | 推移作用・k-推移作用・正則部分群・half-transitive | 8.1 – 8.10 | k-trans 再帰 (8.2), AN=G ↔ N 推移 (8.5), 自己同型作用の k-trans 構造制約 (8.8) |
| 8B | 4299-4513 | block と primitivity・Jordan・Bochert | 8.11 – 8.26 | 2-trans ⇒ primitive (8.16), Jordan 転置 (8.17), 1 つでも 3-cycle 含む primitive ⇒ Alt or Sym (8.19), Bochert (8.26) |
| 8C | 4514-4641 | Alt(n) 単純性・SL(n,q) perfect・PSL(n,q) 単純性 (Iwasawa) | 8.27 – 8.33 | A_n simple (8.27), Iwasawa 単純性判定 (8.30), SL(n,q) perfect (8.32), PSL(n,q) simple (8.33) |
| 8D | 4642-4870 | orbital, suborbit, subdegree, common-divisor graph | 8.34 – 8.44 | 軌道-suborbit 対応 (8.34), Weiss (8.38), Manning (8.40), CDG 三連結成分 (8.41), 自己同型作用版 (8.44) |

### 全結果一覧 (mmd 行番号付き)

#### § 8A — Transitive & k-transitive actions, regular subgroups, half-transitive (lines 4061-4298)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 8.1  | Lemma   | G 推移 ⇒ 推移作用 ≅ G/G_α 上の右乗法 (permutation isomorphism) | L4071 |
| 8.2  | Lemma   | G k-推移 on Ω ⇔ G_γ (k-1)-推移 on Ω−{γ} | L4119 |
| 8.3  | Lemma   | SL(n,q) は P^{n-1}(F_q) (1-次元部分空間集合) 上 2-推移 | L4139 |
| 8.4  | Corollary | GL(n,2) は F_2^n−{0} 上 2-推移 | L4151 |
| 8.5  | Lemma   | G 推移, A=G_α: N 推移 ⇔ AN=G; N 正則 ⇔ +A∩N=1; N 正則正規 ⇒ A の N\{1} 共役作用 ≅ A の Ω−{α} 作用 | L4157 |
| 8.6  | Corollary | A↷N の k-推移 ⇒ G=N⋊A の右剰余類作用は (k+1)-推移 | L4167 |
| 8.7  | Corollary | V=(F_2)^n ⋊ GL(n,2) は 2^n 点上 3-推移 (8.6 + 8.4) | L4173 |
| 8.8  | Lemma   | A↷N k-推移 (k ≥ 1): N は素位数群; k>1 ⇒ p=2 or |N|=3; k>2 ⇒ |N|=4, k=3 | L4179 |
| 8.9  | Theorem | half-transitive 版: 作用が Frobenius か, または N elementary abelian で固有 A-部分群無し | L4195 |
| 8.10 | Lemma   | G が proper 正規部分群族 Π の交わらない和 = G ⇒ G elementary abelian p-群 | L4201 |

#### § 8B — Blocks, primitivity, Jordan sets, Bochert (lines 4299-4513)

block / primitive / imprimitive の定義が L4299-4305 (8.10 と 8.11 の間) に入る.

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 8.11 | Lemma   | Δ block ⇒ \|Δ\| ∣ \|Ω\|, \|Ω\|/\|Δ\| 個の translate が disjoint partition | L4307 |
| 8.12 | Corollary | 素数位数推移作用 ⇒ primitive | L4313 |
| 8.13 | Lemma   | block 格子 ⟷ stabilizer H を含む subgroup 格子 の対応 | L4319 |
| 8.14 | Corollary | (\|Ω\|>1) primitive ⇔ H = G_α 極大部分群 | L4327 |
| 8.15 | Lemma   | N ⊴ G ⇒ N-軌道は block; primitive 下では N-作用は自明 or 推移 | L4337 |
| 8.16 | Lemma   | 2-推移 ⇒ primitive | L4347 |
| 8.17 | Theorem | **Jordan** (転置): primitive G が transposition 含む ⇒ G = Sym(Ω) | L4355 |
| 8.18 | Theorem | **Jordan** (一般): primitive G, Λ ⊂ Ω: G_Λ が Ω−Λ で primitive ⇒ G は (\|Λ\|+1)-推移 | L4377 |
| 8.19 | Corollary | primitive G が 3-cycle 含む ⇒ G = Sym(Ω) or Alt(Ω) | L4387 |
| 8.20 | Lemma   | H ⊂ G, H-軌道 X: H primitive on X かつ \|X\|>\|Ω\|/2 ⇒ G primitive | L4393 |
| 8.21 | Lemma   | Jordan 集合 X, Y で X∪Y<Ω ⇒ X∩Y も Jordan (強 Jordan も保存) | L4403 |
| 8.22 | Theorem | primitive G, Jordan X, 0<\|X\|<\|Ω\|−1 ⇒ G_α 推移 on Ω−{α}, よって G は 2-推移 (強 ⇒ G_α primitive) | L4411 |
| 8.23 | Theorem | primitive G が p-cycle (p 素, p ≤ \|Ω\|−3) 含む ⇒ G = Sym(Ω) or Alt(Ω) | L4435 |
| 8.24 | Lemma   | S_n 内で n-cycle x の中心化群 = ⟨x⟩ | L4437 |
| 8.25 | Lemma   | x, y permutation で「両方が動かす点が α 唯一」⇒ [x,y] は 3-cycle | L4451 |
| 8.26 | Theorem | **Bochert**: primitive proper G < S_n が G ≠ Alt なら \|S:G\| ≥ ⌊(n+1)/2⌋! | L4467 |

#### § 8C — Alt simple, PSL simple via Iwasawa (lines 4514-4641)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 8.27 | Theorem | n ≥ 5 ⇒ A_n は単純 | L4518 |
| 8.28 | Corollary | n ≥ 5 ⇒ S_n の正規部分群は {1, A_n, S_n} だけ | L4526 |
| 8.29 | Lemma   | n ≥ 2: PSL(n,q) は次数 (q^n−1)/(q−1) の 2-推移群 | L4534 |
| 8.30 | Lemma   | **Iwasawa**: primitive perfect G, A ⊴ G_α 可解, ⟨A^G⟩=G ⇒ G simple | L4548 |
| 8.31 | Theorem | SL(n,q) は基本行列 t_{i,j}(α) で生成される | L4566 |
| 8.32 | Theorem | (n ≥ 3) or (n=2, q>3) ⇒ SL(n,q) is perfect | L4576 |
| 8.33 | Theorem | (n ≥ 3) or (n=2, q>3) ⇒ PSL(n,q) is simple | L4604 |

#### § 8D — Orbitals, subdegrees, common-divisor graph (lines 4642-4870)

orbital / paired orbital / rank / 自己ペア / orbital function / subdegree の定義が L4642-4682
(8c-8.34 の間) に入る. m-arrow, K_m(α), k_m, [α]_m の定義が L4744-4806.

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 8.34 | Lemma   | orbital Δ ↦ Δ(α) は G_α-軌道との全単射, \|Δ(α)\| = \|Δ\|/\|Ω\| | L4664 |
| 8.35 | Theorem | G primitive ⇔ 非対角の全 orbital graph が連結 | L4698 |
| 8.36 | Lemma   | 有限有向グラフ G が topologically connected かつ Aut(G) が頂点上推移 ⇒ G path connected | L4702 |
| 8.37 | Theorem | primitive G, subdegree 1 = m_1 ≤ … ≤ m_r ⇒ m_{i+1}/m_i ≤ m_2 | L4722 |
| 8.38 | Theorem | **Weiss**: primitive G, 最大 subdegree n: 互いに素な subdegree m ⇒ m=1 | L4742 |
| 8.39 | Lemma   | α→β m-arrow, α→γ n-arrow ((m,n)=1), β↔γ u-arrow ⇒ u ≥ n, u ∣ mn, G_γ G_α ⊂ G_γ G_β | L4752 |
| 8.40 | Theorem | **Manning**: primitive G, 最大 subdegree n ≥ 3, G_α が大きさ n の suborbit 上 2-推移 ⇒ n=\|Ω\|−1, G 3-推移 | L4780 |
| 8.41 | Theorem | subdegree set D の common-divisor graph G(D) は連結成分 ≤ 3 (含 {1}) | L4796 |
| 8.42 | Theorem | m<n subdegree, 全 subdegree が m か n に互いに素 ⇒ k_m ∣ k_n, k_m ∣ n | L4808 |
| 8.43 | Theorem | G(D) が 3 成分 {1}, A, B (B が最大要素含む) ⇒ a<b (∀a∈A, b∈B), B 内任意 2 整数は edge で結合 | L4841 |
| 8.44 | Corollary | A↷G 自己同型, D = A-軌道サイズ集合 ⇒ G(D) は同じ性質 (8.41 + 8.43 系) | L4851 |

## mathlib カバレッジ

**朗報**: mathlib `Mathlib/GroupTheory/GroupAction/` 下に Ch.8 を直撃するファイル群が
**驚くほど揃っている**. 8A/8B/8C の大半が直接利用可で、新規実装は 8D (orbital theory)
と 8C の simplicity 一般化, および Bochert (8.26) が中心.

### 直接利用できるもの

| Isaacs | mathlib | 備考 |
|---|---|---|
| (def) 推移作用 | `MulAction.IsPretransitive` (`GroupAction/Defs.lean`, `Transitive.lean`) | |
| (def) k-推移 | `MulAction.IsMultiplyPretransitive n` := `IsPretransitive G (Fin n ↪ α)` | `MultipleTransitivity.lean` |
| (def) block | `MulAction.IsBlock` (`Blocks.lean`) | 69 補題完備 |
| (def) trivial/fixed/invariant block | `IsTrivialBlock`, `IsFixedBlock`, `IsInvariantBlock` | |
| (def) primitive | `MulAction.IsPreprimitive` (`Primitive.lean`) | extends IsPretransitive |
| (def) k-primitive | `MulAction.IsMultiplyPreprimitive` (`MultiplePrimitivity.lean`) | |
| (def) quasi-primitive | `MulAction.IsQuasiPreprimitive` | |
| **Lemma 8.1** (推移 ≅ G/H) | `MulAction.orbitEquivQuotientStabilizer` + permutation isomorphism API | Ch.1 で 1.4 として使用済 |
| **Lemma 8.2** (k-trans 再帰) | `is_one_pretransitive_iff`, `is_two_pretransitive_iff`, `isMultiplyPretransitive_iff_of_conj` 等 | |
| **Lemma 8.11** (block ∣) | `MulAction.IsBlock.disjoint_smul_set_smul`, `IsBlock.orbit.eq_or_disjoint` 等 | |
| **Lemma 8.13** (block ↔ over H subgroup) | `Blocks.lean` 内に block-lattice ↔ overgroup-lattice 対応あり (要確認) | `isSimpleOrder_blockMem_iff_isPreprimitive` 関連 |
| **Cor 8.12** (素数位数 ⇒ primitive) | `MulAction.IsPreprimitive.of_prime_card` (`Primitive.lean`) | 直接 |
| **Cor 8.14** (primitive ⇔ H 極大) | `isCoatom_stabilizer_iff_preprimitive` | 直接 |
| **Lemma 8.15** (N-軌道は block) | `MulAction.IsBlock.subgroup` + 既存補題 | 構成は可能 |
| **Lemma 8.16** (2-trans ⇒ primitive) | `isPreprimitive_of_is_two_pretransitive` | 直接 |
| **Thm 8.17 Jordan (転置)** | `Jordan.lean` `subgroup_eq_top_of_isPreprimitive_of_isSwap_mem` | 直接 |
| **Cor 8.19 Jordan (3-cycle)** | `Jordan.lean` `alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem` | 直接 |
| **Thm 8.18 Jordan (一般)** | `Jordan.lean` 内 (要詳細確認) | normalClosure_of_stabilizer_eq_top など |
| **Lemma 8.30 Iwasawa** | `Iwasawa.lean` `IwasawaStructure` + `isSimpleGroup` | 直接! 構造体ベース |
| **Thm 8.27** (A_n simple, n ≥ 5) | `alternatingGroup.isSimpleGroup_five` (`SpecificGroups/Alternating.lean`) のみ; 一般 n ≥ 5 は **TODO** (mathlib 内に明示) | |
| **Thm 8.28** (S_n 正規部分群分類) | 8.27 から導出 | |
| **Thm 8.31** (SL(n,q) 生成) | (要確認: `Matrix.SpecialLinearGroup.lean` 周辺) | |
| **Thm 8.32-8.33** (SL perfect / PSL simple) | `LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup.lean` に **abbrev のみ**, 単純性なし | 新規実装 |

### 新規実装が必要な主要項目

* **§8A の薄い再述** (Lemma 8.1, 8.2, 8.5, 8.6, 8.7) — mathlib `IsPretransitive` /
  `IsMultiplyPretransitive` の上に Isaacs 記法でラッパーを書く. **Lemma 8.5** (正則
  正規 ⇒ 共役作用 ≅ 点作用) は Frobenius 群論 (Ch.6) や Suzuki 定理 (Peterfalvi 付録)
  の基礎で重要.
* **Lemma 8.8** (k-推移自己同型作用の構造制約) — Ch.8 §8C の A_n 単純性証明 (Thm 8.27)
  で使う. Peterfalvi 直接被引用は無いが Suzuki 定理付近の議論で類似の制約が散在.
* **Thm 8.9 / Lemma 8.10** (half-transitive の Frobenius 分解) — Passman & Isaacs.
  ⇒ Frobenius 理論 (Ch.6) と接続するが、Isaacs §8A 内で完結. 下流被引用ゼロなので
  §8 内のみで使用.
* **Thm 8.18 (Jordan 一般版) / 8.20-8.22 (Jordan 集合 / 強 Jordan)** — mathlib の Jordan.lean
  に既に近い結果はあるが、Isaacs の "Jordan set" 概念での記述は新規補題が必要.
* **Thm 8.23** (p-cycle ⇒ Sym or Alt) — 8.18 + 8.19 の系統. Bochert と並ぶ §8B の "山".
* **Thm 8.24** (n-cycle centralizer = ⟨x⟩) — **(2026-05-23 audit 訂正)** Bochert 8.26 ではなく
  Thm 8.23 (p-cycle ⇒ Sym/Alt) の proof L4435-L4449 内で使用. mathlib `Equiv.Perm.cycleType`
  周辺で類似結果はある可能性.
* **Thm 8.25** (重なる動点 1 つ ⇒ [x,y] 3-cycle) — Bochert 8.26 の直接の準備.
* **Thm 8.26 Bochert** — 本章の §8B の大物. mathlib 未収載, 新規実装. 証明は 8.25 + 8.19 +
  純組合せ (8.24 は使わない). proof-internal API: `Equiv.Perm.support`,
  `MulAction.fixingSubgroup` (集合版), `Equiv.Perm.card`, `Fintype.card_perm`,
  `Subgroup.index`, `Nat.factorial_le`.
* **Thm 8.27** (A_n simple, n ≥ 5) — mathlib に TODO として明記 ("Show that
  `alternatingGroup α` is simple if and only if `Fintype.card α ≠ 4`"). mathlib の
  `IsThreeCycle.alternating_normalClosure` (n ≥ 5 で 3-cycle が任意の非自明正規部分群を
  生成) と `Jordan.lean` `alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem`
  (Cor 8.19) を組み合わせれば短く書ける.
* **Thm 8.31** (SL(n,q) 生成) — `Matrix.SpecialLinearGroup` 周辺に transvection / row
  reduction 補題があるか要確認. 無ければ新規実装.
* **Thm 8.32** (SL perfect, n ≥ 3 or (n=2, q>3)) — `commutator (SL n F) = ⊤` の形で mathlib
  に直接対応無し. 8.31 + 行列計算で証明.
* **Thm 8.33** (PSL simple) — 8.30 (Iwasawa) + 8.29 (PSL 2-trans) + 8.32 (perfect) を
  組み合わせ. mathlib の `IwasawaStructure` 構造体に値を埋める形.
* **§8D 全体 (Thm 8.34-8.44)** — orbital, suborbit, subdegree, common-divisor graph の
  概念自体が mathlib に無い. orbital を Ω × Ω 上の G-軌道として定義し、graph theory と
  接続する大きな新規実装. FT 経路への直接寄与は薄い (BG/Peterfalvi 直接引用ゼロ) ので
  優先度低.

## 視点 3: proof-internal mathlib API (per major theorem)

(2026-05-23 audit 統合) — statement 単位の有無だけでなく, 証明本体で呼ぶ mathlib API
v4.29.1 の具体名 + path を per-theorem で列挙. 既存ノートの「mathlib カバレッジ」表
(statement level) を補完する形.

| Isaacs | mathlib API 名 (v4.29.1) | path | 備考 |
|---|---|---|---|
| **8.16** 2-trans ⇒ primitive | `MulAction.isPreprimitive_of_is_two_pretransitive` | `GroupAction/Primitive.lean:~248` | 1 行 |
| **8.17** Jordan (転置) | `Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem` | `GroupAction/Jordan.lean:385` | alias `eq_top_of_…` `:422` |
| **8.18** Jordan general | `MulAction.IsPreprimitive.is_two_motive_of_is_motive`, `isMultiplyPretransitive_succ_iff_ofStabilizer`, `ofFixingSubgroup` API | `Jordan.lean:107-245`, `MultiplePrimitivity.lean`, `SubMulAction/OfFixingSubgroup.lean` | 既存 Jordan.lean 内 motor |
| **8.19** Cor 3-cycle ⇒ Alt/Sym | `Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem` | `Jordan.lean:426` | 直接 |
| **8.26** Bochert (新規) | `Equiv.Perm.support`, `MulAction.fixingSubgroup` of set, `Equiv.Perm.card`, `Fintype.card_perm`, `Subgroup.index`, `Nat.factorial_le` | `Perm/Support.lean`, `GroupAction/FixingSubgroup.lean`, `Logic.Equiv.Defs` | 純組合せ; 既存ノートが指すが具体名なし |
| **8.27** A_n simple (n ≥ 5) | `Equiv.Perm.IsThreeCycle.alternating_normalClosure` + base `alternatingGroup.isSimpleGroup_five` + `Subgroup.normalClosure_eq_iSup` + `normalClosure_le_normal` | `SpecificGroups/Alternating.lean:260, 385, 322-353` | mathlib TODO `:56` を埋める形 |
| **8.28** S_n 正規部分群分類 | `alternatingGroup.index_eq_two`, `Equiv.Perm.eq_alternatingGroup_of_index_eq_two` | `Alternating.lean:112, 38 ref` | 8.27 完成後直接 |
| **8.30** Iwasawa | `IwasawaStructure` + `IwasawaStructure.isSimpleGroup` | `GroupAction/Iwasawa.lean:47, 82` | **要注意**: hypothesis は `IsQuasiPreprimitive M α` + `IsPerfect`. Isaacs は primitive のみ ⇒ `IsPreprimitive.isQuasipreprimitive` (`Primitive.lean:~54`) で wrapper. |
| **8.31** SL generated | (mathlib 不在; `LinearAlgebra/Matrix/SpecialLinearGroup.lean:240` 周辺に transvection 関連 lemma 散在) | — | Gauss elimination 新規 |
| **8.32** SL perfect | `Matrix.SpecialLinearGroup.commutator`, basic matrix mul | — | 計算 |
| **8.33** PSL simple | 8.30 IwasawaStructure + 8.29 + 8.32 | — | structure 埋め |

**Helper 候補** (新規 `OddOrder/` 配下):
- `OddOrder/GroupTheory/Orbital.lean` — §8D の `Orbital`, `subdegree`, `commonDivisorGraph`
  は mathlib 不在. FT 経路 0 件で skip 推奨だが mathlib upstream 候補.
- `OddOrder/Mathlib/Alternating/IsSimpleGroup.lean` — Thm 8.27 A_n simple 一般 n ≥ 5
  (mathlib TODO `Alternating.lean:56` を埋める形, mathlib PR 候補).

## Ch.8 から下流への被引用

### Isaacs 内 (Ch.9+ 本文を grep)

```
0 件: いずれの Theorem/Lemma/Corollary 8.X も Ch.9-10 本文で **引用されない**.
```

⇒ Ch.8 は **Isaacs FGT 内で文字通り「葉」** の章. ROADMAP の依存図にもある通り
「Ch.1 が前提、それ以外は実質独立」.

### BG での引用

`references/bg/local-analysis.mmd` を `Theorem|Lemma|Corollary 8\.` で grep:

```
全マッチが \mathbf{G} (= Gorenstein 1968) への参照. Isaacs Ch.8 引用は ゼロ.
```

permutation group 関連の概念 (primitive, transitive 等) で grep しても、BG 本文は
独自の §3 Frobenius actions, §10 M_α/M_σ で「`X が Y 上 (sharply) transitive に作用する」
程度の局所利用に留まる. **named theorem (Bochert, Jordan, Iwasawa) は一切引用無し.**

### Peterfalvi での引用 (Ch.8 概念の直接利用は **Suzuki 定理付録に集中**)

Peterfalvi 本体 §1-§16 (FT character theory) では Ch.8 概念は実質出ない. しかし
**Peterfalvi Part II: Suzuki 定理付録 (`05.X` 全ファイル) + Huppert 付録 (`06.0`) +
Near-fields 付録 (`07.0`)** で:

| 概念 | 出現箇所 | Isaacs Ch.8 対応 |
|---|---|---|
| doubly transitive (主仮説 A1) | 05.X 全体, 06.0 | **§8A 基本定義 + Lemma 8.5** (正則部分群とのつなぎ) |
| sharply 2-transitive | 05.0, 05.1 | **Lemma 8.5** + 8a 流の規範形 |
| Zassenhaus group (3-pt 自由 + 2-trans) | 05.0, 05.1, 05.5 | k-transitive concept (mathlib `IsMultiplyPretransitive`) |
| Ω−{point} 上の正則作用 | 05.0-05.6, 07.0 | **Lemma 8.5** |
| PSL(2,q), Sz(q), PSU(3,q) | 05.0-05.6, 07.0 | **Thm 8.29** (PSL 2-trans), 8.33 は **使わない** (Peterfalvi は H/HB で単純性を既知扱い) |
| near-field ↔ sharply 2-transitive | 07.0 | (§8A 周辺の概念) |
| split BN-pair of rank 1 | 05.6 序文 | 抽象枠組み |

**結論 (FT クリティカル度)**:
- **§8A 基礎概念 (transitive, k-transitive, regular, primitive 入り口, Lemma 8.5)**:
  **HIGH** — Peterfalvi Suzuki 付録の前提語彙.
- **§8B (block / primitive 構造, Jordan, Bochert)**: **MEDIUM**. primitive の基本性質
  (8.11, 8.14, 8.16) は 8.5 と共に使われる可能性. Bochert (8.26) と Jordan 系
  (8.17-8.23) は FT 経路で直接被引用無し ⇒ 完全形式化目的のみ.
- **§8C (Alt simple, Iwasawa, PSL simple)**: **LOW for FT 経路**. Peterfalvi は PSL/Sz/PSU
  の simplicity を [H], [HB] 既知として扱い、本プロジェクトで 8.33 を証明する必要は
  Phase 1 内で完結させる動機しかない. **Iwasawa の補題 (8.30)** は mathlib 既収載で
  単純性証明の汎用道具として価値あり.
- **§8D (orbital theory)**: **LOW** — FT 経路への寄与ほぼゼロ.

## 視点 4: 先行章節への依存 (per-target)

(2026-05-23 audit 統合) — mmd L4059-4878 全範囲で `(Theorem|Lemma|Corollary|Proposition) [1-7]\.[0-9]+`
を grep した結果:

| Ch.8 target | Ch.1-7 cite | mmd | OddOrder 状態 |
|---|---|---|---|
| **8.1 prose intro** | Thm 1.4 (orbit ↔ coset 計数) | L4069 | ✅ mathlib `MulAction.orbitEquivQuotientStabilizer` (Ch.1 既使用) |

それ以外の Ch.2-7 cite は **proof body 内も prose 内も 0 件**.

**結論**: Ch.8 は Isaacs FGT で最も独立した章. prerequisite は mathlib `IsPretransitive` のみ.

## 章内依存 (Ch.8 内で 8.X が引用される頻度)

`awk` で Ch.8 本文 (L4059-4878) を切り出し `(Theorem|Lemma|Corollary|Proposition) 8\.[0-9]+`
を grep:

| 回数 | 番号 | 結果 |
|---|---|---|
| 8 | **8.18** | Jordan (一般) — §8B 内で他結果の証明に最も使われる |
| 5 | **8.39** | §8D の m-arrow 補題 — 8.40, 8.42, 8.43 で使う |
| 5 | **8.29** | PSL は 2-推移 — 8.33 の核心 |
| 5 | **8.2**  | k-推移再帰 — §8A 全体の基幹 |
| 5 | **8.19** | 3-cycle ⇒ Alt or Sym — 8.27 (A_n simple) の鍵 |
| 4 | 8.42, 8.41, 8.35 | §8D 内連鎖 |
| 4 | **8.5**  | AN=G ⇔ 推移、正則正規 — §8A 全体 |
| 3 | 8.38, 8.31, 8.17 | |
| 3 | **8.11**, 8.1, **8.14** | block 基本、推移 ≅ G/H、primitive ⇔ 極大 — §8A/8B 基幹 |
| 2 | 8.30, 8.9, 8.37, 8.8, 8.3 | |

**証明依存の強い軸**:
- 8.1 → 8.5 → 8.8 → 8.27 (A_n 単純性のメイン経路)
- 8.11 → 8.13 → 8.14 → 8.15 → 8.16 → 8.17/8.18/8.19 (primitive 基礎)
- 8.18 が §8B 内ハブ
- 8.29 → 8.30 (Iwasawa 適用) → 8.31 → 8.32 → 8.33 (PSL simple 経路)
- 8.34 → (8.35, 8.39) → 8.37, 8.38, 8.40, 8.41, 8.42, 8.43, 8.44 (§8D 連鎖)

### 章内依存 sharpening (2026-05-23 audit)

ハブ frequency 表だけでは見えない proof-internal chain の細部:

(a) **8.20 → 8.21 → 8.22 strict chain**: 8.22 の minimality argument は 8.21 (Jordan 集合 ∩
   も Jordan) を L4419 で直接 cite, 8.21 は 8.20 (primitive on big H-orbit) を L4407 で cite.
   実装順序は `8.20 → 8.21 → 8.22 → 8.18 → 8.19`.

(b) **8.23 → 8.18 + 8.19 + 8.24** (proof L4435-L4449): Sym(Λ) Frattini argument で 8.18 を
   直接呼び, 内部で n-cycle centralizer の 8.24 も使用. **(8.24 は 8.23 用)**

(c) **8.26 Bochert → 8.25 + 8.19 のみ** (proof L4467-L4513): 8.24 は **使わない**. 既に
   上記「新規実装が必要な主要項目」の **Thm 8.24** の項で訂正済 (8.24 は 8.23 用,
   Bochert proof 内では引かれない).

(d) **8.27 (A_n simple) proof は 8.5 + 8.8(c) + 8.15 + 8.16 を全部使用** (proof L4520-L4524).
   主軸 `8.1 → 8.5 → 8.8 → 8.27` に加え, **8.15 が proof 第一手** で必須. 実装段階で
   8.15 が in scope であること.

(e) **Nougat OCR 注意**: mmd L4435 に "Proof of Theorem 18.23" の typo あり (= 8.23 の
   proof 開始). naive `grep "Theorem 8\.23"` は 1 件 under-count するため自己引用頻度
   表が微妙にずれる可能性 (本ハブ表に対する影響は無し).

## Shared module 配置提案

(2026-05-23 audit 統合) — Ch.4-7 audit で確立した `OddOrder/GroupTheory/` shared module
パターンを Ch.8 に適用. Ch.8 から派生する新規ファイル候補:

- **`OddOrder/GroupTheory/Orbital.lean`** — §8D (Thm 8.34-8.44) の orbital, paired orbital,
  subdegree, common-divisor graph の概念は mathlib 不在. orbital を Ω × Ω 上の G-軌道
  として定義する shared module. FT 経路寄与は 0 件で Phase 1 内優先度は低いが, mathlib
  upstream 候補として独立価値あり.

- **`OddOrder/Mathlib/Alternating/IsSimpleGroup.lean`** — Thm 8.27 (A_n simple, n ≥ 5) を
  実装する場所. mathlib `Mathlib/GroupTheory/SpecificGroups/Alternating.lean:56` に
  TODO として明記された "Show that `alternatingGroup α` is simple if and only if
  `Fintype.card α ≠ 4`" を埋める形. `OddOrder/Mathlib/` 名前空間に置き将来 mathlib PR.

## 着手順 (提案)

FT クリティカル度 + mathlib カバレッジ + 章内依存で並べる:

1. **§8A 基礎 (Lemma 8.1, 8.2, 8.5, 8.6, 8.7) + primitive 入口 (8.11, 8.12, 8.13, 8.14, 8.15, 8.16)**
   — mathlib `IsPretransitive`, `IsMultiplyPretransitive`, `IsBlock`, `IsPreprimitive` の
   ラッパー仕事中心. Peterfalvi 付録の前提語彙. **最優先**.
2. **Iwasawa (8.30)** — mathlib `IwasawaStructure` の Isaacs ステートメントへの bridge.
   §8C で 8.33 (PSL simple) の鍵だが、単独で簡単.
3. **§8A 残り (8.3, 8.4, 8.8) + §8B 名前付き定理 (8.17 Jordan, 8.18 Jordan general, 8.19 3-cycle,
   8.23 p-cycle)** — Jordan.lean 既収載をラップ. Bochert (8.26) は別仕事.
4. **§8C A_n simple (8.27, 8.28) + Iwasawa の周辺 (8.29 PSL 2-trans)** — mathlib に
   A_5 だけある状態を A_n (n ≥ 5) に拡張. mathlib TODO だが Isaacs の証明をそのまま流せる.
5. **§8B Jordan/Bochert 完備 (8.20-8.22 Jordan 集合, 8.24, 8.25, 8.26 Bochert)** —
   FT 直接被引用無いが Phase 1 完成度で実装.
6. **§8C PSL simple (8.31 SL 生成, 8.32 SL perfect, 8.33 PSL simple)** — `SpecialLinearGroup`
   の transvection API を整え、Iwasawa を適用. **重い新規実装だが Peterfalvi 直接被引用無し
   (PSL simplicity は [H], [HB] 既知扱い)** ⇒ 急がない.
7. **§8A Half-transitive (8.9, 8.10)** — §8 内のみで使う独立小テーマ.
8. **§8D 全体 (8.34-8.44)** — orbital / subdegree 理論. **FT 経路寄与ほぼゼロ**なので
   Phase 1 最後回し可. ただし self-contained で書きやすいので時間が余れば早めでもよい.

## 開発時の注意点

* **mathlib `IsMultiplyPretransitive n` の定義**: `IsPretransitive G (Fin n ↪ α)` という
  embedding 集合上の推移性として定式化されている. Isaacs の "G acts k-transitively on Ω"
  (distinct k-tuple を distinct k-tuple に送る) と等価だが、ラップ補題で橋渡しが必要かも.
* **mathlib `IsBlock` の定義** は Isaacs (`Δ ∩ Δ·g = ∅ or = Δ`) と Mathlib (`∀ g₁ g₂, g₁•B ≠ g₂•B → Disjoint`)
  で微妙に異なる. `isBlock_iff_smul_eq_or_disjoint` で標準形に戻せる.
* **Iwasawa.lean の `IwasawaStructure`** は構造体ベース — 4 つのデータ (T, is_comm, is_conj, is_generated)
  を組み立てる必要. Isaacs Thm 8.30 の "A ⊴ G_α 可解, G = A^G" から構造体への変換は
  パターン化できる. **(2026-05-23 audit 注意)** `IwasawaStructure.isSimpleGroup` (`Iwasawa.lean:82`)
  は hypothesis に `[IsQuasiPreprimitive M α]` を要求 (primitive のみではない). Isaacs 8.30 は
  primitive 仮定なので, `IsPreprimitive.isQuasipreprimitive` (`Primitive.lean:~54`) を間に
  挟む wrapper が必要.
* **Jordan.lean** は `Jordan set` の Isaacs 概念とは別の意味 (?) で命名されている可能性
  あり (mathlib の Jordan は transposition theorem 等を含む). Lemma 8.21 の "Jordan set"
  概念は自前定義が必要かも.
* **mathlib の Alt(n) は `alternatingGroup α : Subgroup (Equiv.Perm α)`** で型 α 上で定義.
  Isaacs の "n ≥ 5" は `5 ≤ Fintype.card α` で表現される.
* **PSL** は mathlib に abbrev だけ — `noncomputable abbrev ProjectiveSpecialLinearGroup
  (n : Type*) [...] (R : Type*) [...] := SpecialLinearGroup n R ⧸ center _`. 単純性証明は
  新規仕事.
* mathlib に **Bochert** "(n+1)/2" 階乗下限は無い. これは純組合せ + 8.18, 8.24, 8.25.
* **subdegree / orbital** は mathlib 未収載 ⇒ §8D は丸ごと新規.

## 解決済みの確認

### Ch.8 セクション境界 (mmd 抽出失敗の補完)

mmd で `### 8b` ヘッダが欠落しているが、本文構造 (block 定義の入り方 + Problems 8a/8b
フッタ位置) から:

* §8A: L4061-L4298 (Problems 8a まで)
* §8B: L4299-L4513 (block 定義から Problems 8b まで)
* §8C: L4514-L4641
* §8D: L4642-L4870

の 4 セクション構成 (§8E 無し) で確定. Problems sections は 8a/8b/8C/8D とラベリング
不統一 (Isaacs 原典側の表記揺れ).

### mathlib 既収載の発見 (2026-05-21)

`Mathlib/GroupTheory/GroupAction/` に **Ch.8 直撃ファイル群**が存在:

| ファイル | 主機能 | Isaacs 対応 |
|---|---|---|
| `Transitive.lean` | `IsPretransitive` 基本 | §8A 基底 |
| `MultipleTransitivity.lean` | `IsMultiplyPretransitive` | §8A k-推移 |
| `Blocks.lean` (69 補題) | `IsBlock` 完備 | §8B block |
| `Primitive.lean` | `IsPreprimitive`, prime card, coatom stab | §8B 主定理 |
| `MultiplePrimitivity.lean` | `IsMultiplyPreprimitive` | §8B 拡張 |
| `Jordan.lean` | Jordan 転置 8.17, 3-cycle 8.19 等 | §8B 主定理 |
| `Iwasawa.lean` | `IwasawaStructure` + `isSimpleGroup` | Thm 8.30 直接 |
| `SubMulAction/OfStabilizer.lean` | G_α-作用周辺 | §8A-8B 補助 |

⇒ §8A/8B の **過半が既存資産のラッパー仕事**で済む見通し. §8C, §8D, Bochert (8.26),
A_n general (8.27) が新規実装の中心.

### 下流被引用調査 (2026-05-21)

* **Isaacs Ch.9-10**: Ch.8 結果への引用ゼロ. Ch.8 は完全な「葉」.
* **BG**: Ch.8 名前付き定理への引用ゼロ. permutation 概念は局所利用のみ.
* **Peterfalvi 本体 §1-16**: Ch.8 名前付き定理への引用ゼロ.
* **Peterfalvi Suzuki 付録 (05.X, 06.0, 07.0)**: **doubly transitive を主仮説 (A1) として
  多用**. これは §8A 基本概念 (transitive, k-transitive, regular, Lemma 8.5) を必要とする.
  Bochert / Jordan / orbital は使われない.

⇒ **FT 経路への Ch.8 寄与は §8A 基本概念のみ**. それ以外は Phase 1 完成度のための
形式化で、急ぐ必要無し.

## 関連ノート

(2026-05-23 audit 統合)

- [`../meta/chapter_investigation_framework.md`](../meta/chapter_investigation_framework.md) —
  4 視点 framework (本ノートの構造ベース).
- [`../meta/ch08_10_audit_2026_05_23.md`](../meta/ch08_10_audit_2026_05_23.md) —
  Ch.8/9/10 横断 audit 統合 doc. 本ノートの視点 3/4 + sharpening の出所.
- [`ch01_sylow.md`](ch01_sylow.md) — Thm 1.4 (Ch.8 唯一の Ch.1-7 依存) 実装ノート.
- [`ch07_thompson.md`](ch07_thompson.md) — Phase 1 完成 sibling 章 (Thompson subgroup,
  Ch.4-7 wave の末尾).
- [`../meta/mathlib_coverage.md`](../meta/mathlib_coverage.md) — 全体カバレッジ.
  `GroupTheory/GroupAction/` 配下 (Transitive, Blocks, Primitive, Jordan, Iwasawa, ...)
  の Ch.8 直撃ファイル群が要となる.
