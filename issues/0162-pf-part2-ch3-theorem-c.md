---
id: 162
slug: pf-part2-ch3-theorem-c
title: "Peterfalvi Part II Ch.III Theorem C: Q は 2-群 (Q₁ = 1)"
created: 2026-07-28
---

# Peterfalvi Part II Ch.III Theorem C: `Q` は 2-群 (`Q₁ = 1`)

## 実測 (2026-07-28) — 本当に未形式化かの検証

survey (`three_books_full_survey_2026_07_16.md` L852) は Thm C を「未」とするが、
**その根拠は stale** (「`structure_of_H` (Suzuki.lean:133, sorry) が opaque scaffold」と
書くが、当該宣言は de-opacification campaign で**削除済**)。ラベルを信用せず実測した:

| 検証 | 結果 |
|---|---|
| `Appendices/Suzuki.lean` | **宣言ゼロ**の pure re-export hub (58 行)。scaffold は削除済で、置換もされていない |
| `(C1)` 仮説の carrier | repo 全体に**存在しない** (grep 0 件) |
| `feit_sibley_coherence` の consumer | **ゼロ** (自 file chain と AxiomsCheck のみ)。書籍でこの定理を使うのは Thm C の証明だけなので、これが決定的 |
| `theoremC` 識別子 | 全て **BG App.C / BG §16 の Theorem C** — 別の本の別定理 |
| `Q₁ = ⊥` の hit | すべて Ch.II FirstCase で `Q₁ = ⊥` を**仮説に取る**側 (`FirstCase/StepSix.lean:270` `card_Q_eq_two_pow_of_Q1_eq_bot`)。Thm C が供給すべきものであって Thm C ではない |
| pp. 115–121 / "Structure of H" を参照する file | **ゼロ** |
| 未マージのレーン作業 | b / c / d とも main の 0 commit 先行 = 無し |

⟹ **未形式化で確定**。「`Q₁ = 1` ⟹ `Q` は 2-群」の配管だけは Ch.II 側に既存で、
欠けているのは `Q₁ = 1` を**証明する**側。

### git log からも直接読める (2026-07-28 確認)

| 時刻 | commit |
|---|---|
| 07-26 05:30 | `55ec6f681` **Theorem B 完成** — Ch.II 完結 |
| 07-26 05:32 | `2e431ea73` Hall–Wielandt を AxiomsCheck 登録 |
| 07-26 05:34 | `b90e31082` issue 9503 close / 2053 を pending 化 |
| 07-26 05:43 | `25521c85c` **docs(survey): Isaacs のラベル突き合わせを再実測** ← 別トラックへ pivot |

`OddOrder/Peterfalvi/Appendices/Suzuki/` への commit は **07-26 05:30 の Theorem B 完成が最後**で、
以後ゼロ。全期間の commit message にも Peterfalvi の Theorem C / Ch.III / "Structure of H" は
一度も現れない。⟹ Ch.II 完結の直後に Part I の一般化トラック (0151–0161) へ移り、
**文書順の次である Ch.III に入らないまま**現在に至った。

### 原因 = frontier リスト側の取りこぼし (process bug)

survey の「📍 2026-07-26 終了時点の frontier」(L1441 `### 残っているもの`) が挙げる 6 項目に
**Part II Ch.III–Ch.IV が入っていない**。一方 `### Pf App: Suzuki` の表には Thm C 以下
**12 行の「未」**が並んでいる。frontier 節が Part I 側の表からしか拾っていなかったため、
「残りは packaging とごく少数」という誤った全体像になっていた。
⟹ 本 issue と同時に frontier 節を訂正する。

## 書籍 (pp. 115–116、ページ画像 `references/peterfalvi/pages/peterfalvi-p115.png` / `-p116.png` で確定)

**(C1)** `V ≠ 1` かつ、素数位数の任意の `P ≤ V` に対し `C_G(P)` の 2-rank ≥ 2。

**Theorem C.** `Q` は 2-群。

証明 (背理法、`Q₁ ≠ 1` と仮定):

1. **`D` が `Q₁` に fixed-point-freely 作用**。素数位数の `P ≤ D` について
   `|Ω_P| = 2` なら `C_H(P) ⊆ D` ゆえ `C_Q(P) = 1`;
   `|Ω_P| ≥ 3` なら `P` は `D` 内で `V` の部分群に共役 (Ch.I §1 Prop 6(c)) ゆえ
   (C1) + Ch.I §3 Prop 1(c) で `C_{Q₁}(P) = 1`。
2. **`Q ∩ Q^x = 1` (`x ∈ G − H`)** — `H ∩ H^x` が `H` 内で `D` に共役ゆえ。
3. ⟹ Feit–Sibley (Appendix IV) の仮説が充足 ⟹
   `𝒮 = {χ ∈ Irr(H) | Q₁ ⊄ Ker χ}` が `Ind_H^G` について coherent。
4. `λ` = `H` の線形指標、`λ ≠ 1_H`、`QK ⊆ Ker λ` (`H/QK ≅ V` が可解非自明ゆえ存在)。
5. `(|K|,|V|) ≠ 1` なら `D` が位数 `p²` の非巡回部分群を持ち fpf に反する
   ([H] Kap V Satz 8.15) ⟹ **`QK` は `H` の Hall 部分群**。
6. `x, x^g ∈ H` ⟹ `λ(x^g) = λ(x)` (π′-成分に帰着 → Hall の定理で `V` の元に共役 →
   Ch.I §3 Lemma 2 で `V` 内共役)。
7. ⟹ `(Ind λ)(x) = λ(x)(Ind 1_H)(x)` (`x ∈ H`) ⟹ `⟨Ind λ, Ind λ⟩ = 2`。
8. `Ind_H^G λ = f₁ + f₂` (`fᵢ ∈ Irr(G)`)、`⟨Ind λ, 1_G⟩ = ⟨λ, 1_H⟩ = 0` ゆえ `fᵢ ≠ 1_G`。
9. `𝒮 = {χ₁,…,χₙ}`、`χᵢ(1) = aᵢ|D|`、`a₁ = 1`、coherence から
   `Ind(χᵢ − aᵢχ₁) = eᵢ − aᵢe₁` (`i ≥ 2`, `eᵢ ∈ ±Irr(G)`)。
10. `f₁ = ±eᵢ` を仮定すると矛盾: Appendix IV Lemma 2(c) で `χ̄ᵢ ≠ χᵢ ∈ 𝒮`、
    `Ind(χᵢ − χ̄ᵢ) = eᵢ − e′ᵢ`、[Is] Lemma 7.7 で `Res(eᵢ − e′ᵢ) = χᵢ − χ̄ᵢ`
    (`Q` が Hall + `χᵢ − χ̄ᵢ` が `H − Q` で消える) ⟹ `Ind λ = ±(eᵢ + e′ᵢ)` ⟹
    `|Q| + 1 = ±2eᵢ(1)` は `|Q|` 偶より不可能。
11. ⟹ `⟨Res f_j, χᵢ − aᵢχ₁⟩ = 0` ⟹ `Res f_j = b_j(∑ aᵢχᵢ) + ψ_j` (`Q₁ ⊆ Ker ψ_j`)。
12. 次数評価 `|Q| + 1 = f₁(1) + f₂(1) ≥ (b₁+b₂)∑aᵢχᵢ(1) = (b₁+b₂)|S|(|Q₁|−1)`
    ⟹ `b₁ + b₂ ≤ |Q₁|/(|Q₁|−1) < 2` ⟹ ある `j` で `b_j = 0` ⟹ `Q₁ ⊆ Ker f_j`。
13. `N = Ker f_j` は `1 ≠ N ≠ G` の正規部分群 ⟹ Ch.I §3 Prop 2 で Theorem A の結論
    ⟹ Ch.I §3 Lemma 1 で `Q` は 2-群 ⟹ `Q₁ = 1`、矛盾。

⚠ pdftotext の誤り 1 件: 書籍は `χᵢ(1) = aᵢ|D|` (OCR は `aᵢ|K|` に見える)。ページ画像で確定済。

## 前提の所在 (実測、すべて landed)

| 書籍 | repo |
|---|---|
| Ch.I §1 Prop 6(c) | `exists_conj_mem_D_map_le_V` (`FixedPointCentralizer.lean:485`) |
| Ch.I §3 Prop 1(c) | `centralizer_trichotomy_of_induction` (`CentralizerTrichotomy.lean`) |
| Ch.I §3 Prop 2 | `theoremAConclusion_of_not_simple` (`InductionNonSimple.lean:627`) |
| Ch.I §3 Lemma 1 | `TheoremAConclusion.Q_and_residual` (`CentralizerInductionBridge.lean:112`) — `IsPGroup 2 Q` を直接与える |
| Ch.I §3 Lemma 2 | `ConjugacyInV.lean` |
| Appendix IV (Feit–Sibley) | `feit_sibley_coherence` (`FeitSibleyMain.lean:319`)、sorry-free |
| `Q = S × Q₁` | `SylowDecomposition.lean` (`Q1` = `Q` の正規 2-補群、characteristic、奇位数) |
| `Q` 冪零 | `isNilpotent_Q` (`QStructure.lean`) |

## 置き場

新ディレクトリ `OddOrder/Peterfalvi/Appendices/Suzuki/StructureOfH/`
(Ch.II の `FirstCase/` と同じ流儀)。**新 leaf は同じ commit で `OddOrder.lean` に配線する。**

## ⚠ step 3 で判明した上流の阻害 — Feit–Sibley が書籍に無い `Odd |G|` を要求している

`feit_sibley_coherence` は `(hoddG : Odd (Nat.card G))` を取るが、**書籍 Appendix IV の
"Hypotheses and Notation" (p. 144、ページ画像で確定) に `G` の奇性は無い**:

> `G` is a finite group and `H = Q ⋊ D` is a **proper** subgroup of `G`. We assume that
> `(|D|,|Q|) = 1` and that `Q ∩ Q^x = 1` for `x ∈ G − H`. …
> `Q = S × Q₁`, `|Q₁|` and `|S|` are relatively prime, `D` acts without fixed points on `Q₁`,
> `Q₁` is not a 2-group and `S` is nilpotent.
> **Theorem.** If `d` is odd, then `𝒮` is coherent …

⟹ **Ch.III は `|G|` が偶 (involution `t ∈ G`) なので、現状の repo 版は適用できない。**
Theorem C は Appendix IV の唯一の consumer なので、これが `feit_sibley_coherence` の
consumer ゼロだった真因でもある。

### `hoddG` が実際に何に使われているか (trace 済)

1. `Odd (Nat.card Q1)` の導出 (`feit_sibley_coherence` 冒頭)。
2. `witness_charValue_cong` → **`peterfalvi_67_hall_of_odd`** — ここでは
   `hreal : ConjClasses.mk z⁻¹ ≠ ConjClasses.mk z` (= `z` が `z⁻¹` と共役でない) を作るためだけ
   に使われている。一般版 `peterfalvi_67_hall` は `hreal` を直接取る。

### 書籍は (2) を `d` 奇から出している (p. 149、step (7))

> **Since `d` is odd**, we may assume that `𝒦₁ ∩ Z^# ≠ ∅` and `𝒦₂ = (𝒦₁)⁻¹`.

論法 (`Z = [Q₁,Q₁] ∩ Z(Q₁)`、`Z ⊴ H`、`Q` は `Z` を中心化):
`g z g⁻¹ = z⁻¹` とすると `z⁻¹ ∈ Q ⊓ Q^g` が非自明 ⟹ TI より `g ∈ H = QD` ⟹
`g = q·δ` と書くと `q` は `Z` を中心化するので `δ` が `z` を反転 ⟹ `δ²` は `z` を中心化 ⟹
fpf より `δ² = 1` ⟹ `|D|` 奇より `δ = 1` ⟹ `z = z⁻¹` ⟹ `z² = 1`、`|Q₁|` 奇に矛盾。

### やること (step 3 の前段)

**`feit_sibley_coherence` の `Odd (Nat.card G)` を `Odd (Nat.card Q₁)` に弱める** — 書籍が
実際に使うのはこれだけ (Lemma 2(c) の「odd order group `Q₁D`」も `|Q₁|` 奇 + `d` 奇)。
`hreal` は上記の書籍論法で `hd` から導出する。影響範囲は `FeitSibleyMain` /
`FeitSibleyConclusion` の 4 signature + `peterfalvi_67_hall_of_odd` の呼び出し 1 箇所
(`peterfalvi_67_hall_of_odd` の consumer はこの 1 箇所のみと実測)。

## やること

- [x] step 1: `(C1)` carrier `SecondCaseHypothesis` + `D` の `Q₁` 上 fpf (2026-07-28、`794473d39`)
- [x] step 2: `Q ∩ Q^x = 1` (`x ∉ H`) — `Q_inf_map_conj_eq_bot` (2026-07-28)
- [x] **step 3a: Feit–Sibley の `Odd |G|` を書籍どおり `Odd |Q₁|` へ弱める** (2026-07-28、`d64642791`)
- [x] step 3b: Feit–Sibley `Hypothesis` の構成と coherence の取得 (2026-07-28)
- [x] **step 4 前半: `QK` 一式 + 線形指標 `λ` の存在** (2026-07-28)
      — `QK ⊴ H` / `QK ⊓ V = 1` / `QK ≠ H` / `[H:QK]` 奇 →
      Feit–Thompson で可解 → `commutator (H/QK) ≠ ⊤` →
      `exists_linearCharacter_leKer_QK`
- [x] **step 13 (終端): `Q₁ = 1`** (2026-07-28) — `Q1_eq_bot_of_not_isSimpleGroup`

### step 3b の材料 (2026-07-28 実測)

`FeitSibley.Hypothesis G` の各フィールドの供給元:

| フィールド | 供給元 | 状態 |
|---|---|---|
| `H_ne_top` | `t ∉ H` | 自明 |
| `Q_le_H` / `D_le_H` / `Q_normal_in_H` / `Q_inf_D_eq_bot` / `Q_mul_D_eq_H` | Ch.I `Hypothesis` の公理 | ✅ |
| `Q_trivial_intersection` | **step 2** `Q_inf_map_conj_eq_bot` | ✅ |
| `D_fixedPointFree_on_Q1` | **step 1** | ✅ |
| `S_le_Q` / `Q1_le_Q` / `S_inf_Q1_eq_bot` / `S_mul_Q1_eq_Q` / `S_commutes_Q1` | `SylowDecomposition.lean` (`sylowTwo_*_Q1Subgroup`、`sylowTwoProdQ1MulEquiv`) を**ambient `S` へ移送**する必要あり (repo 側は `Sylow 2 ↥Q` の bundled 形) | 要作業 |
| `coprime_S_Q1` | `S` は 2-群 / `Q₁` は奇 (`two_not_dvd_card_Q1Subgroup`) | 要作業 |
| `S_nilpotent` | `S` は 2-群 | 要作業 |
| `Q1_not_two_group` | `Q₁ ≠ 1` (背理法の仮定) + `Q₁` 奇 | 要作業 |
| **`coprime_Q_D`** | `p` 奇素数が `|Q|` を割れば `|Q₁|` を割る (`Q₁` = 正規 2-補群) + fpf から `Coprime |Q₁| |D|` (`IsFrobeniusAction.coprime_card`, `FrobeniusActionBasics.lean:200`)。`|D|` 奇なので 2 は除外 | 要作業 |

`feit_sibley_coherence` の追加仮説:

| | 供給元 |
|---|---|
| `hd : Odd hyp.d` | 公理 `D_odd` ✅ |
| `hQ1odd : Odd (Nat.card Q₁)` | `two_not_dvd_card_Q1Subgroup` + `card_Q1` ✅ (step 3a で `Odd \|G\|` から置換済) |
| `hnil : Group.IsNilpotent ↥Q1` | `isNilpotent_Q` の部分群 ✅ |
| `hHallG : Coprime \|Q\| Q.index` | `card_G_eq` (`\|G\| = \|Q\|\|D\|(\|Q\|+1)`) より `Q.index = \|D\|(\|Q\|+1)`、`gcd(\|Q\|,\|Q\|+1) = 1` と `coprime_Q_D` |

⟹ 残るのは **ambient `S` の導入 + `coprime_Q_D`** が主。新 leaf
`StructureOfH/FeitSibleyInput.lean` に置く。
- [x] **step (5) 完結 (2026-07-28)**: `(|K|,|V|) = 1` → `QK` は `H` の Hall
      — `coprime_card_K_V` / `card_D_eq` / `card_QK_eq` /
      `index_QK_subgroupOf_eq_card_V` / `coprime_card_QK_index`。
      ⚠ [H] V.8.15 は不要だった (`isCyclic_of_isMulCommutative_le_D` +
      Fermat の小定理で代替)。
- [ ] step 4 後半 = 書籍 step (6)–(12): `QK` が `H` の Hall → `λ` の共役不変性 →
      `⟨Ind λ, Ind λ⟩ = 2` → `Ind λ = f₁ + f₂` → coherence 簿記 → 次数評価で
      `Q₁ ⊆ Ker f_j` → `G` は単純でない

### 書籍 step (5) の論法 (2026-07-28 に再構成、着手前に実測で再確認すること)

**主張**: `(|K|,|V|) = 1`、したがって `QK` は `H` の Hall 部分群。

repo に `Coprime |K| |V|` は**無い** (grep 0 件) ので新規。書籍は 1 行
「`(|K|,|V|) ≠ 1` なら `D` は位数 `p²` の非巡回部分群を持ち、`D` は `Q₁` に
fpf に作用できない ([H] Kapitel V, Satz 8.15)」で済ませている。展開すると:

1. `K` は巡回 (`K_isCyclic`) かつ `K ⊴ D` (`K_normal`)。
2. `p ∣ |K|` かつ `p ∣ |V|` と仮定。`K` の Sylow `p`-部分群 `K_p` は `K` に
   characteristic ゆえ `D`-不変、その `Ω₁(K_p) ≅ C_p` も `D`-不変。
3. Cauchy で `y ∈ V` を位数 `p` に取る。`y` の共役作用は `Ω₁(K_p) ≅ C_p` の
   自己同型で位数は `p` を割るが、`|Aut(C_p)| = p − 1` は `p` と互いに素なので
   **`y` は `Ω₁(K_p)` を中心化する**。
4. `x ∈ Ω₁(K_p)` を位数 `p` に取ると `⟨x, y⟩` は指数 `p` の可換群。
   `K ⊓ V = 1` より `x ∉ ⟨y⟩` なので位数 `p²` の**非巡回**群 (`C_p × C_p`)。
5. step 1 より `D` は `Q₁` に fpf 作用する。⟹ 矛盾。

⚠ **書籍の [H] V.8.15 は引かなくてよい (2026-07-28 の改良)**。より短い経路が repo に在る:

> **`D` の可換部分群はすべて巡回**である (Frobenius 補群の標準性質)。
> 証明: 可換非巡回 `A ≤ D` が在るとすると、`A` は `Q₁` に**互いに素に**作用する
> (`coprime_card_Q1_D`、step 3b で landing 済)。**Isaacs Thm 6.21**
> (`Isaacs.Ch06.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic`,
> `FrobeniusGroup.lean:1372`) より `Q₁ = ⟨C_{Q₁}(a) : a ∈ A^#⟩`。ところが fpf
> (step 1) で各 `C_{Q₁}(a) = 1` なので `Q₁ = 1`、`Q₁ ≠ 1` に矛盾。

⟹ Frobenius 補群の構造定理も Huppert の p-群補題も要らず、**既に landing 済の
step 1 + step 3b の帰結だけ**で済む。`C_p × C_p` を作る (2)-(4) はそのまま使い、
(5) をこの一般補題に差し替える。

**実装順**: (i) `isCyclic_of_isMulCommutative_le_D` (可換 ⟹ 巡回) を一般補題として
landing → (ii) `p ∣ |K|` かつ `p ∣ |V|` から `C_p × C_p ≤ D` を作って矛盾。

#### (i) は 2026-07-28 に landing 済 (`FeitSibleyInput.lean`)

#### (ii) の完全な手順 (2026-07-28 に道具まで確定、次セッションはこれを書くだけ)

1. **`x`, `y` を取る**: `p ∣ |K|` から Cauchy で `x ∈ K`、`orderOf x = p`;
   同様に `y ∈ V`、`orderOf y = p`。
2. **`y` は `zpowers x` を正規化**: `K ⊴ D` (`conj_mem_K_of_mem_D`) で
   `y (zpowers x) y⁻¹ ≤ K` は位数 `p`、`K` は巡回 (`K_isCyclic`) なので位数 `p` の
   部分群は一意 (`OddOrder.GroupTheory.cyclic_subgroup_eq_of_card_eq`,
   `CyclicSubgroupUniqueness.lean:37`) ⟹ `y x y⁻¹ ∈ zpowers x`。
3. **`x` と `y` は可換** (書籍の `|Aut(C_p)| = p − 1` を初等化):
   `y x y⁻¹ = x^j` と書くと `y^p x y^{-p} = x^{j^p}`、`y^p = 1` より `x^{j^p} = x`、
   `orderOf x = p` から **`j^p ≡ 1 (mod p)`**。Fermat (`ZMod.pow_card`) で
   `j^p ≡ j (mod p)` なので `j ≡ 1 (mod p)` ⟹ `x^j = x` ⟹ 可換。
4. **`E := closure {x, y}` は可換**: `Subgroup.isMulCommutative_closure` に 3 を渡す
   (repo 先例 = `HigmanMaximalNormalAbelian.lean:426`)。`E ≤ D` は `x ∈ K ≤ D`,
   `y ∈ V ≤ D` から。
5. **矛盾**: (i) より `IsCyclic ↥E`。`↥E` の中で `zpowers x'` と `zpowers y'` は
   ともに位数 `p` なので `cyclic_subgroup_eq_of_card_eq` で一致 ⟹ `x ∈ zpowers y ≤ V`。
   だが `x ∈ K`、`x ≠ 1`、`K ⊓ V = 1` (`K_inf_V_eq_bot`) に矛盾。

#### Hall 性への接続 (再掲、(ii) の後)

`|D| = |K||V|` + `|QK| = |Q||K|` ⟹ `[H:QK] = |V|`;
`gcd(|Q|,|V|) = 1` は `coprime_card_Q_D` の帰結なので、(5) と合わせて
`gcd(|QK|, [H:QK]) = 1`。

**Hall 性への接続**: `|D| = |K||V|` (`K ⊓ V = 1` + `exists_mem_V_mul_mem_K`) と
`Q ⊓ K ≤ Q ⊓ D = 1` より `|QK| = |Q||K|`、`[H:QK] = |V|`。
`gcd(|Q|,|V|) = 1` は既済 (`coprime_card_Q_D` の帰結) なので、(5) と合わせて
`gcd(|QK|, [H:QK]) = 1`。
- [ ] step 5: `Q₁ = ⊥` の結論 + AxiomsCheck 登録

## 完了条件

`SecondCaseHypothesis` の下で `IsPGroup 2 hyp.Q` (同値に `hyp.Q1 = ⊥`) が sorry-free で
landing し、AxiomsCheck に登録されて axiom-clean。フルビルド green + `--strict` 警告ゼロ +
sorry 非退行。

## 参照

* 前章 = [issue 2053](pending/2053-pf-suzuki-theorem-b.md) (Ch.II Theorem B、2026-07-26 完成)
* Appendix IV = issues 1049 / 1053 / 1054 (Feit–Sibley、lane a)
* survey `notes/meta/three_books_full_survey_2026_07_16.md` L825–L862 (Pf App: Suzuki の表)

## 次 = 書籍 step (6) の分析 (2026-07-28)

**主張**: `x ∈ H`, `g ∈ G`, `x^g ∈ H` なら `λ(x^g) = λ(x)`。

書籍の論法:
1. `π` = `|QK|` の素因子集合。`x` の `π`-成分は `QK ⊆ Ker λ` に入るので
   `λ(x) = λ(y)`, `λ(x^g) = λ(y^g)` (`y` = `x` の `π′`-成分) ⟹ `x` は `π′`-元と仮定してよい。
2. **Hall の定理**で `x` と `x^g` は `H` 内で `V` の元に共役 ⟹ `x, x^g ∈ V` と仮定してよい。
3. **Ch.I §3 Lemma 2** (`ConjugacyInV.lean`) で `x` と `x^g` は `V` 内で共役 ⟹ `λ(x) = λ(x^g)`。

### 材料の所在 (実測)

| 必要なもの | 状態 |
|---|---|
| `π`/`π′` 分解 (`IsPiElement`, `exists_isPiElement_mul`) | ✅ `GroupTheory/PiElementDecomposition.lean` |
| `QK ⊓ V = ⊥` | ✅ `QK_inf_V_eq_bot` |
| `QK ⊔ V = H` | 未 — `|QK||V| = |H|` (`card_QK_eq` + `card_D_eq` + `card_H_eq`) と `QK ⊓ V = ⊥` から数え上げ |
| **`π′`-元は `H` 内で `V` に共役** | ✅ **道筋確定 (2026-07-28)**。`H` は**可解**なので Hall の定理がそのまま使える (下記) |
| Ch.I §3 Lemma 2 | ✅ `ConjugacyInV.lean` |

⟹ 着手時はまず「`π′`-部分群が補群に共役で入る」(Schur–Zassenhaus の強い形) が
mathlib / repo にあるかを実測すること。無ければそこが step (6) の本体になる。

### 🔑 step (6) の unlock: `H` は可解 (2026-07-28 landing)

`isSolvable_H` (instance, `LinearCharacter.lean`): `Q` は冪零 (Ch.I §2 Prop 1(b))
ゆえ可解、`|H/Q| = |D|` は奇ゆえ **Feit–Thompson** で可解、`solvable_of_ker_le_range`
で拡大が可解。**Ch.I / Ch.II では明示されていなかった事実**。

⟹ 書籍の「by a theorem of Hall」は repo 既存の **`Isaacs.Ch03.hall_D`**
(`Ch03_SplitExtensions/Basic.lean:1329`: 可解群では任意の π-部分群が Hall π-部分群に
含まれる) で直接使える。Schur–Zassenhaus の共役部分を自前で用意する必要は無い。

### step (6) の残り

1. ~~`π := (Nat.card ↥QK).primeFactors` と置く~~ ✅
2. ~~**`V` は `H` の Hall `π′`-部分群**~~ ✅ **2026-07-28 landing**
   (`isHallSubgroup_V_subgroupOf`、支えは `card_H_eq_card_QK_mul_card_V` /
   `index_V_subgroupOf_eq_card_QK` / `coprime_card_QK_V`)。
3. [ ] `x` が `π′`-元 ⟹ `hall_D` で `⟨x⟩` は Hall `π′`-部分群に含まれ、**Hall 共役性**で
   `V` に共役。⚠ Hall 共役定理 (Hall C-定理) が repo にあるか要実測
   (`Ch03_SplitExtensions` に `hall_D` はあるので同ファイル周辺を探す)。
4. [ ] `π`-成分が `QK ⊆ Ker λ` に入ることで `λ(x) = λ(π′-成分)` へ帰着
   (`GroupTheory/PiElementDecomposition.lean` の `exists_isPiElement_mul`)。
5. [ ] Ch.I §3 Lemma 2 (`ConjugacyInV.lean`) で `V` 内共役に落として `λ(x) = λ(x^g)`。
