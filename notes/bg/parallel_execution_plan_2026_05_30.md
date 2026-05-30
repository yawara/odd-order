# BG 並列実行計画 — §1/§2 ゲート起点 (2026-05-30)

> **生成**: `bg-parallel-frontier` workflow (run `wf_80d0d0a4-6f9`, 25 agent / 1.69M tok / 9.8 min)。
> §1/§2 未完ゲート 12 件 (0011-0019, 0028, 0033, 0034) を survey → adversarial verify → synthesize。
> スクリプト: `~/.claude/projects/-home-ywr-odd-order/.../workflows/scripts/bg-parallel-frontier-wf_80d0d0a4-6f9.js`。
> **着手決定** (2026-05-30, ユーザー選択): **本線 W-3 = 0016 (Thm 1.13) → §4 に集中**。FT 直列スパインを開く最高レバレッジ。
> このファイルは確定スナップショット。個別ゲートの掘り下げは各 issue と `notes/bg/sNN_*.md` が正本。

> 基底スナップショット: `main` @ `710da69`。**BG 本体に実 sorry は 0**(`OddOrder/BG/` 全 grep + S01 build green 2205 jobs で確認)。**Thm 6.2 一般形(`Z(L(S))·O_{p'}(G)⊴G`, `AppB_Thm62.lean`)・App.A A.1-A.5・App.B B.1-B.4 は完成・sorry-free**。以下はこれらを done とした上での前進計画。

## 0. 検証で覆った前提(計画に反映済み)

survey から verify が覆した/精査した点のうち、wave 分割に効くもの:

| ゲート | survey の主張 | 確定した実態(本セッションで再確認) |
|---|---|---|
| **0011** | Prop 1.2 reverse + Prop 1.4 が open | Prop 1.2(両方向)+ Prop 1.3 は**完成・axiom-clean**。残るのは **Prop 1.4 のみ**(`S01:478` docstring だけ、theorem 不在)。issue は stale。 |
| **0013** | readyNow=true (Prop 1.6 全部 done) | **要訂正(本人確認 2026-05-30)**: (a)(b)(e) は Ch04 に sorry-free 実在(§1B docstring L493/494/497)。だが **(c)(d) は §1B docstring 上「未実装」「存在予定」= Ch.4 §4D 依存で残**。verify は `Main:3396/3442`(abelian 補題)を見て「全部 done」と早合点。→ **0013 は closed 不可、open 維持**。 |
| **0014** | full Lem 1.9 は未実装、2-step のみ | **覆る**: full 版(任意長 series)は `coprime_stabilizes_chain_trivial`(`AppA_PStability.lean:1362`)として**実在・sorry-free**。Prop 1.10 も `S01:710` で完成。**gate 0014 は実質 DONE**、残務は issue を closed/ へ移すだけ。 |
| **0015** | parallelSafe=true | **覆る → false**: 0016 と同一 §1D(現 placeholder 1 行)+ 隣接 mapping-table 行を編集。 |
| **0028/0033/0034** | §2 hard gates、§4/§5/§7 を gate | **覆る(下流)**: これらの shared module は **`AbsolutelyIrreducible`/`ExtraspecialFaithful` = importer 0 件**、`Eigenspace` = S02 のみ。**§3(S03, 13 定理)は Isaacs Ch.6 経由で既に sorry-free**、BG §2 native machinery を**バイパス済**。→ 0033/0034 は現状**どの下流 Lean 依存路にも乗っていない**(教科書完全性のための作業)。 |

**§4 の §2 依存の訂正**: §4 mmd 内の "Lemma 2.2" は実は **"G, Lemma 2.2.2"(Gorenstein)** の誤マッチ。§4 の真の §2 依存は **Thm 2.6(done)のみ**。→ **§4 は 0033/0034/0028 に依存しない**。

---

## 1. 確定依存グラフ

### 1.1 §1/§2 ゲート間(verify 確定分のみ)

```
§1A  Prop 1.2 ✅ ─ Prop 1.3 ✅ ─ Prop 1.4 ⬜(0011 残) ── 依存→ §1B Prop 1.5(0012)
                                          (BG 証明が X=G⋊A の Hall σ を要求)
§1B  Prop 1.5(0012) ⬜  ──┐  ※ 0012/0013 は同一 §1B mapping-table を共同編集(衝突)
     Prop 1.6(0013) ✅本体/doc残 ─┘
§1C  Lem 1.9(2-step)✅ ─ Prop 1.10 ✅  (= §1D/§1E ゲートの engine, 既 done)
§1D  Thm 1.11(0015)⬜ ── Cor 1.12(0015, Prop 1.10 ✅に依存)
     Thm 1.13(0016)⬜ ── (独立。Thompson critical = Gorenstein 5.3.11 新規, repo 不在)
        ※ 0015 と 0016 は同一 §1D(現 placeholder)を編集(衝突)
§1E  Prop 1.15b(0017)⬜ ── 依存→ Prop 1.10 ✅ + Prop 1.3 ✅ + (Lem 1.14 centralizer-商形 ⬜新規)
     Prop 1.16(0018)⬜  ── 依存→ Isaacs Thm 6.21 ✅ (Ch06, §1/§2 内部依存なし=leaf)
§1G  Lem 1.21(0019)⬜ ── 依存→ Isaacs Ch03 oPiCore 群 ✅ + (p-elements生成部分群 API ⬜新規)

§2A  Prop 2.1(0033)⬜空殻 ── §2B Prop 2.2 ⬜ ── §2E Thm 2.5(0034)⬜空殻
§2D  Prop 2.4(a-g)✅ ─ Prop 2.4(c)(f-k)(0028)⬜ ── (Thm 2.5 が (j)(k) を消費)
        ※ §2 chain: 2.1 → 2.2 → 2.5 / 2.4(j,k) → 2.5
        ※ この chain の現 in-repo consumer は無い(§3 は Isaacs Ch.6 経由で done)
```

### 1.2 §1/§2 → §4/§5/§6/§7 接続

```
                          ┌──────────────── §1A Prop 1.2 ✅
                          ├──────────────── §1B Prop 1.6 ✅
§4 (Blackburn rank≤2) ────┼──────────────── §1C Thm 1.8 ✅ (burnside_operator)
   (XL hard gate)         ├──────────────── §1F Thm 1.20 = Maschke ✅
                          ├──────────────── §1G Lem 1.22 ✅
                          ├──────────────── §2  Thm 2.6 ✅ (done, 4697行)
                          └━━━━━━━━━━━━━━━━━ §1D Thm 1.13 ⬜ (0016) ← §4 唯一の未完前提
                                                              (+ Lem 2.1/Thm 1.13 内蔵で Ω₁,critical)
§5 (Narrow) ── §4 を 6 結果が cite → §4 partial 後に Lem5.1-Cor5.4、§4 完成後に Thm5.5-5.7

§6 Additional ✅(reduced)+ Thm 6.2 一般形 ✅  → 既開通(直列スパイン入口)

§7 Transitivity ── 依存→ Thm 6.2 一般形 ✅ + §5 + §1B Prop 1.5/1.6(0012)
                                              └ §7 が §1B Hall-σ 推移性を実際に使う
```

**結論**: クリティカル経路上で §1/§2 ゲートが本当に gate しているのは — **(a) §4 を gate する 0016(Thm 1.13)**、**(b) §7 を gate する 0012(Prop 1.5)+ 0011 の Prop 1.4(§1B Hall-σ 一般版)**。0013/0014 は done。**0028/0033/0034 はクリティカル経路外**(現 Lean 依存なし)。

---

## 2. Wave 分割

### Wave 0 — issue 衛生(即時、Lean 作業ほぼ無し、逐次 1 セッションで)

- **0014 → closed/**: full Lem 1.9 (`coprime_stabilizes_chain_trivial`) + Prop 1.10 とも完成済。
- **0013 → open 維持(訂正)**: Prop 1.6 **(a)(b)(e)** は Ch04 に sorry-free 実在(§1B docstring 記録済)。**(c)(d) は未実装**(docstring に「未実装」「存在予定」と明記、Ch.4 §4D 依存)。(c) は (b) の系、(d) は (a)+`fixedPoints_inf_actionCommutator_eq_bot_of_abelian` から導出可能と見込まれるが、明示 decl / doc 判断は §1B 着手時に。
- **0011 を Prop 1.4-only に縮約**: Prop 1.2/1.3 done をチェックオフし、残務を Prop 1.4 のみに明示。

> **注意**: 0013 と 0012 が §1B mapping-table を共有。0013 doc 更新は 0012 着手前に。

### Wave 1 — 今すぐ並列着手可(readyNowConfirmed=true ∧ 相互依存なし)

| 束 | ゲート | 内容 | 工数 | 配置 |
|---|---|---|---|---|
| **A** | **0018** | Prop 1.16(noncyclic auto)。第1主張 = Isaacs Thm 6.21 ✅。実コンテンツ = 第2主張の \|G\| 帰納 | M | S01 §1E (Ch06 import) |
| **B** | **0028** | Prop 2.4(c)(f)(g)(h)(j)(k)。(j) の S₁/S₂ 場合分けが実コンテンツ | L | `EigenspaceUnderCyclicAction.lean` |
| **C** | **0033** | Prop 2.1(absolutely irreducible)。`IsAbsolutelyIrreducible` 新規定義 + (a)(b)(c) | L | `AbsolutelyIrreducible.lean` |

3 本とも編集ファイルが互いに素(0018=S01 §1E, 0028/0033=別 RepTheory ファイル, mathlib のみ)。**0028/0033 は現状どの下流 Lean ゲートも待っていない**(FT 経路外)。

### Wave 2 — §1 の残ハード(同一 S01、section 別 worktree 分離必須)

| ゲート | 内容 | 工数 | 依存 | section |
|---|---|---|---|---|
| **0011 (Prop 1.4)** | coprime auto faithful on F(G)。X=G⋊A solvable + Hall σ + O_σ(F)=1 分解 | L | **0012** に依存 | §1A |
| **0012 (Prop 1.5 a-c,e)** | A-invariant Hall-π 一般版。subtype に共役作用 + transitivity(hall_C)+ glauberman | L | engine done | §1B |
| **0015 (Thm 1.11/Cor 1.12)** | p-odd p群 + p'作用が Ω₁ 上自明 ⇒ 自明。engine = `isaacs_thm_4_36` ✅ | S | engine done | §1D |
| **0017 (Prop 1.15b)** | Goldschmidt: O_{p'}(C_G(R))⊆O_{p'}(G)。補助補題 3 本新規 | L | engine done | §1E |
| **0019 (Lem 1.21 a-e)** | p-length one 5 性質。汎用 API 2 本新規 | L | engine done | §1G |

依存: **0011 → 0012**(先に 0012)。残り(0015/0017/0019)は相互独立。衝突: 0015↔0016 が §1D 共有、0012↔0013 が §1B 共有。

### Wave 3 — Thm 1.13(独立 XL hard gate)★本線

| ゲート | 内容 | 工数 | ブロッカー |
|---|---|---|---|
| **0016 (Thm 1.13)** | Thompson critical subgroup。**Gorenstein 5.3.11/5.3.13 が repo 全体に不在**。新規 `CriticalSubgroup.lean` + OmegaSubgroup の characteristic/normal 強化 | XL | critical subgroup 存在を Gorenstein 原文から新規形式化 |

- **§1 で唯一の真のハード新規ゲートかつ §4 の唯一の未完前提**。
- worktree 分離必須(OmegaSubgroup 強化が active Isaacs Ch07 と衝突しうる)。
- 0016 内で建てる critical subgroup + Ω₁ 強化 + SCN インフラは §4/§5 でも再利用 → 0016 と §4 は同じ worktree で連続。

### Wave 4 — §2 chain 完成(現状クリティカル経路外、§3 native 化を選ぶ場合のみ)

Prop 2.2(a) module 形 → **0034 (Thm 2.5)**(Prop 2.1 + Prop 2.2(a) + Prop 2.4(j)(k) + G Thm 5.5.4-5 が前提)。**着手は §4 以降の本線が一段落してから**。

---

## 3. 直列スパイン §7→§16(並列化できない部分)

```
§7 Transitivity ──→ §8 Fitting of Max ──→ §9 Uniqueness
    │                                          │
    └─依存: Thm6.2 ✅ + §5 + §1B(0012/0011)     ↓
                                       §10 Mα/Mσ ──→ §11 Exceptional ──┬─→ §12 E (XL,19結果)
                                                                       └─→ §13 Prime Action
                                                                              ↓ (§12∥§13 のみ並列可)
                                       §14 Type-𝒫 counting ──→ §15 M_F ──→ §16 Main Results (Thm A-E)
```

**並列化できる唯一の枝**: §12 ∥ §13(§10-§11 完成後)。それ以外(§7→§8→§9, §14→§15→§16)は厳密に直列。

**スパインが開くタイミング**: §7 の律速 = §5 完成 + 0012/0011 完成。§5 は §4 依存。⇒ **直列スパインの開始は §4 → §5 完成後**。§4 が律速。

---

## 4. §4(Blackburn rank≤2)の位置づけ

**着手可能になる条件 = Thm 1.13(0016)が lands すること。** §4 の §1/§2 前提のうち、`Prop 1.2 / Prop 1.6 / Thm 1.8 / Thm 1.20(Maschke) / Lem 1.22 / Thm 2.6` は全て done。**未完は Thm 1.13(0016)ただ 1 つ**。

⇒ **0016 が §4 → §5 → 直列スパイン全体を開く最大レバレッジ**。§4 自体は XL(Blackburn 4.16 分類 + rank/SCN/metacyclic/central-product 記法定義群を先行構築)。0016 と §4 は同じ worktree で連続的に進めるのが効率的。

---

## 5. 推奨 workflow スコープ

- **W-0**(逐次・即時): {0014 → closed, 0011 → Prop 1.4-only 縮約}。0013 は (c)(d) 未実装が判明し **open 維持**(本人確認で訂正)。Lean 新規証明ゼロ。← **本セッションで実施済**
- **W-1**(並列 3 本): {0018, 0028, 0033}。互いに素なファイル。0028/0033 は FT 経路外。
- **W-2**(§1 残ハード, worktree 分離): {0012 → 0011} + {0015, 0017, 0019}。section 単位で worktree。
- **W-3**(§1 唯一の XL, ★最高レバレッジ): **{0016} ✅完成** (2026-05-30, commits 4aefbf5..37a6277, sorry-free/axiom-clean, bg-thm113-impl workflow) → §4 → §5。← 0016 done、§4 着手可能に
- **1 本に束ねない**: 0034(Thm 2.5)は 4 上流未完 + 経路外。

```
W-0 (逐次,即) ──┬─→ W-1 {0018,0028,0033}  (並列, FT 経路外含む)
                 ├─→ W-2 {0012→0011, 0015,0017,0019}  (worktree 分離, §1 完成)
                 └─→ W-3 {0016} → §4 → §5  (専用 worktree, ★FT スパインを開く本線)
                                              ↓
                                    §7→§8→§9→…→§16 (直列スパイン)
```

---

## 関連ファイルパス

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`(§1A-§1G、0011-0019 の編集対象、build green 2205 jobs)
- `OddOrder/BG/Ch1_Preliminary/S02_Representations.lean`(§2、0033 docstring stub @L200-214)
- `OddOrder/BG/AppA_PStability.lean`(full Lem 1.9 = `coprime_stabilizes_chain_trivial`@L1362 → gate 0014 done の根拠)
- `OddOrder/GroupTheory/RepresentationTheory/EigenspaceUnderCyclicAction.lean`(0028、importer は S02 のみ)
- `OddOrder/GroupTheory/RepresentationTheory/AbsolutelyIrreducible.lean`(0033、空殻・importer 0)
- `OddOrder/GroupTheory/RepresentationTheory/ExtraspecialFaithful.lean`(0034、空殻・importer 0)
- `OddOrder/Isaacs/Ch04_Commutators/Main.lean`(Prop 1.6 本体 @3396/3442/3932、Thm 1.11=`isaacs_thm_4_36`@4173)
- §4/§5 ファイルは**未作成**(`OddOrder/BG/Ch1_Preliminary/S04*.lean`, `S05*.lean` 不在)
