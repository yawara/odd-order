---
id: 1042
slug: pf-8-15-dade-hypothesis-instances
title: "(8.15) の残り主張: type-𝒫 (4.6)/(5.2) instance"
created: 2026-07-19
---

# (8.15) の残り主張: type-𝒫 (4.6)/(5.2) instance

## 教科書 (PDF p.48 で確定, 2026-07-19)

**(8.15)** M maximal, A = A₀(M), A(M), A₁(M) のいずれか。
1. **M = N_G(A) かつ Hypothesis (2.2)** が L = M, H(a) = R(a) で成立。
   証明: (2.2.a,b,c) は (8.13.a,c1,c2) から。
2. **M が type 𝒫, M′ = [M,M] なら Hypothesis (4.6)** が
   L = M, K = M′, A = A(M), A₀ = A₀(M), **H = M_F または H = M_s** で成立。
   証明: (8.4.a,d), (8.5.c), (8.10) から。
3. **M が type 𝒫 で 𝒮 ⊆ {Ind_{M′}^M θ | θ ∈ Irr M′, M_s ⊄ Ker θ} 非空・共役閉なら
   Hypothesis (5.2)** が L = M で成立。証明: (1.5.e) + (5.3.b) から。

(8.10): M_s = H (type I/II/V) / M′ (type III/IV)。A(M) (type 𝒫) = ⋃_{x∈M_s^#} C_{M′}(x)^#。

## 現状 (frontier note 2026-07-19 実測 + 本 issue での確認)

- 主張 1: `DadeSupportHypothesisData` (S10_StructureSetup.lean:710) + 型別 3 instance
  (typeI / typeP₁ / typeII) が存在。docstring に「(4.6)/(5.2) 特殊化は別 TODO」と明記。
- 主張 2: typeP₁ 消費側 ((4.6) = `S06.Hypothesis46`) は S12 が持つが、
  **(8.15) としての一般 statement (H = M_F / M_s の両方、type II 込み) は未形式化**。
- 主張 3 ((5.2) instance): **皆無**。
- ⚠ gate: type II/V では M_s = M_F ≠ M′ なので、repo の `typePA` ((M′)^# 添字固定、
  issue 9008 で IsTypeP1 に narrow 済) では A(M) が書籍と食い違う。9008 hub 裁定:
  「S-side honest 化の設計変更が起きた場合のみ Option A (typePA 訂正) を再検討・re-open」。
  **(8.15) の type-II 完全形式化がその trigger になり得る** — 着手時に 9000 issue で
  hub に設計確認 (typePA の M_s^# 添字化 or 別 def 新設) を出すこと。無断で typePA を
  再定義しない (shared infra、lane b の S12/S14 consumer に波及)。

## 進捗

- **着手順 1 完了 (2026-07-19)**: `OddOrder/Peterfalvi/S10_SubcoherentTypeP.lean` 新設。
  - (5.2) の repo 対応物 = `S07.Hypothesis` (既約メンバー形、2 元 `CharacterDifferenceImage`
    固定) と確認。可変長 R (可約 μ 列) は S07_Subcoherent の corrected module note
    (2026-07-06 hub 検証) どおり `S06.certainTypeR`/`columnImageFamilyCohFree` 側が正本 —
    `S07.Hypothesis` 形の (8.15.3) は既約部分家族が honest な全内容。
  - `inducedKernelFamily_subcoherent` (A = A₀(M)、consumer 形) +
    `inducedKernelFamily_subcoherent_sharp` (A = M^#、書籍 (5.2.b) 字義形; narrowing
    Z[S,M^#] ⊆ CF(M,(M′)^#) 込み) を `irrSubcoherent` 経由で構成。
    supporting: `mderivSharp_subset_supportInSubgroup_typePA0` ((8.10) 包含の §8 レベル形)、
    `inducedKernelFamily_member_support_subset_derivedInG`。
  - 全 4 宣言 axiom-clean (`propext`/`Classical.choice`/`Quot.sound` のみ、#print axioms 確認)。
  - 注: 文言は「type III/IV」でなく **P₁ regime** (typePA 忠実域 = 9008 裁定) で scoping。
    statement 自体は素の `TypePData` で成立 (IsTypeP1 は入力 datum `d` の producer 側)。

- **着手順 2 完了 (2026-07-19)**: `OddOrder/Peterfalvi/S10_Hypothesis46TypeP.lean` 新設。
  - `typePData_toHypothesis46`: (8.15.2) の一般形 — 素の `TypePData` + claim-1 datum +
    hodd + hHall から `S06.Hypothesis46 (typePA M data) M` を、**(4.6.c) の H を
    パラメータ** (normal, W₂ ≤ H ≤ K) として構成。(4.6.d) covering は A(M) = K^# ゆえ
    全 H ≤ K で自明 — 書籍が両選択を許す理由がそのまま形式化に写る。
  - 両 instance: `_hallKernel` (H = M_F = data.H; type II では これが忠実な M_s 選択) /
    `_derived` (H = K = M′ = P₁ 域の M_s; S12 版 `toHypothesis46` の選択)。
  - `conj_mem_typePA`: A(M) の M-安定性の bare 形 (S12 `le_normalizer_typePA` の脱 bundle 化)。
  - **hHall を明示パラメータ化**したことで S12 版と違い sorry 非継承 — 全 4 宣言 axiom-clean
    (#print axioms 確認)。scoped `S12.FiniteInduce` instance 規律に注意 (binder 混在不可、
    memory の既知トラップ — 実際に一度踏んで修正)。
- **着手順 3 (gated) 起票 (2026-07-19)**: hub 設計確認 issue **9163** を起票
  (typePA の M_s^# 添字化 Option A vs 新 def 並置 Option B′; 9008 re-open trigger)。
  hub 裁定待ちの間、lane a は次 frontier へ進む。

## 2026-07-20 実測: 主張 3 の P₁ scoping の**原因**が判明 — 族の絞りが違う

`S10_SubcoherentTypeP` の「型 `P₁` regime」注記は、単に「`typePA` が A(M) と一致するのは P₁ だけ」
という一般論ではなく、**族の定義そのものの食い違い**が原因だった:

- 書籍 (8.15.3) の族は `𝒮 ⊆ {Ind_{M′}^M θ | θ ∈ Irr M′, **M_s ⊄ Ker θ**}`。
- repo の族は `S08.inducedKernelFamily ((derivedInG M).subgroupOf M) ⊥` = 「θ ≠ 1」だけ。
- **P₁ では M_s = M′ なので θ ∈ Irr M′ に対し `M_s ⊄ Ker θ ⟺ θ ≠ 1`** で両者は一致する。
  P₂ (type II/V) では `M_s = M_F ⊊ M′` なので repo の族の方が真に広い。

なぜこの差が効くか: `S07.Hypothesis` ((5.2)) は「メンバー差 χ − χ̄ が A₀-supported」を要求し、
repo はこれを `hKsupp : (M′)^# ⊆ supportInSubgroup A₀ M` 経由の粗い評価
(`inducedKernelFamily_conjDiff_support`) で出している。ところが書籍の
`A(M) = ⋃_{x ∈ M_s^#} C_{M′}(x)^#` に対しては **`(M′)^# ⊆ A(M)` が P₂ で偽**なので、
この経路は P₁ でしか動かない。**書籍が族を `M_s ⊄ Ker θ` で絞るのは、まさにこの支持条件を
細かく出すため**。

⟹ 型一様な (8.15.3) に必要なのは `typePA0` → `typePACore0` の置換だけでなく、
**族を `M_s ⊄ Ker θ` 側へ絞り、その族のメンバー差が `A(M)` に台を持つことを直接証明する**こと
(§9 の `xiSet data = {χ ∈ Irr(HU) | H ⊄ Ker χ}` と同型の絞り)。

### ✅ 経路確定 (2026-07-20、書籍 PDF で確認) — 支持補題は既に repo に在る

(8.15) の証明は「the third follows from (1.5.e) and **(5.3.b)**」(PDF 04.10 p.5 = 書籍 p.48)。
**(5.3.b)** (PDF 04.7 p.1 = 書籍 p.25) は Hypothesis (4.6) + (5.2.a) +
`𝒮 ⊂ {Ind_K^L θ | θ ∈ Irr K, H ⊄ Ker θ}` を仮定し、その証明の**第 1 文がまさに支持補題**:

> **By (4.7), `Z[𝒮, L^#] = Z[𝒮, A]`**, and so τ is defined on `Z[𝒮, L^#]`.

つまり「`H ⊄ Ker θ` で絞った族については `L^#`-supported な ℤ-結合が自動的に `A`-supported」。
`(M′)^# ⊆ A` は**要らない** — repo が使っていた粗い経路の代わりがこれ。

**repo に既にある部品** (実測):

1. **(4.6) at `A = typePACore M`, `H = M_s = M_σ`** — `S10.typePACore_toHypothesis46_core`
   (2026-07-20、本 issue 着手順 3 で landed。Coq `FT_prDade_hyp` 相当)。
2. **(4.7) 誘導台形** — `S06.induce_apply_eq_zero_of_not_mem_union_of_not_subset_characterKernel`
   (`S06_CertainTypeSupport.lean:138`): `h : Hypothesis46Core A L` と
   `χ : Irr ↥h.K` で `h.subH ⊄ Ker χ` なら `Ind_{h.K}^L χ` は `A ∪ {1}` の外で消える。
   **`A` について引数化済**なので `A = typePACore M` でそのまま使える。
3. 組み立て engine — `S07.irrSubcoherent` (既存 `inducedKernelFamily_subcoherent` と同じ)。

### ✅ 実装完了 (2026-07-20) — `S10_SubcoherentTypeP.lean` §8E

- (a) **族**: `inducedNonKernelFamily K H = {Ind_K^L θ | θ ∈ Irr K, H ⊄ Ker θ}`
  (書籍 (5.3.b)/(8.15.3) の族そのもの)。
- (b) **粗い族への包含**: `inducedNonKernelFamily_subset_inducedKernelFamily_bot` —
  `H ⊄ Ker θ ⟹ θ ≠ 1` (自明指標は全てを核に持つ) かつ `⊥` 核条件は空虚。
  ⟹ **非実性・対直交性・有限性・共役閉性は `S08.inducedKernelFamily_*` からそのまま継承**。
  作り直しが要るのは**台の評価だけ**。
- (c) **台の評価** (本体): `inducedNonKernelFamily_apply_eq_zero` ((4.7) の直適用) +
  `inducedNonKernelFamily_apply_one_eq_natCast` (次数 = `|L:K|·θ(1)` は自然数 ⟹ 実)
  ⟹ `inducedNonKernelFamily_conjDiff_support` : `Supp (φ − φ̄) ⊆ supportInSubgroup A M`。
  **`(M′)^# ⊆ A` を一切使わない** = 型一様。
- (d) **producer**: `inducedNonKernelFamily_subcoherent` — 任意の ambient support `A`、
  `h46 : S06.Hypothesis46Core A M`、`d : DadeSupportHypothesisData M A` から
  `S07.Hypothesis S (supportInSubgroup A M)`。これが書籍 (5.3.b) 逐語。

5 宣言とも axiom-clean (propext/Classical.choice/Quot.sound)、AxiomsCheck 登録済。
`lake build OddOrder.Peterfalvi.S10_SubcoherentTypeP` green (4032 jobs)。

⚠ P₁ 版 (`inducedKernelFamily_subcoherent` / `_sharp`) は signature 不変で残す
(下流無変更)。docstring で「§8D は P₁ regime、§8E が型一様」と対比を明示。

### ✅ 具体化 完了 (2026-07-20): `S10.typePACore_subcoherent` (§8F)

`A = A(M) = typePACore M` / `H = M_σ` / `K = M′` / `L = M` での書籍逐語の (8.15.3)。
**型仮定は `IsTypeP` のみ** — 型 I–V すべてで成立 (型 II/V を含む)。axiom-clean。

Dade 入力 2 つはいずれも (8.15) claim 1 で型一様:
`dadeSupportHypothesisData_typePACore0` → (4.6) (`typePACore_toHypothesis46_core` 経由)、
`dadeSupportHypothesisData_typePACore` → 等長 `τ`。

⚠ **instance 規律**: 独立 section に置き `[Finite G]` のみを取り
`open scoped OddOrder.Peterfalvi.S12.FiniteInduce in` の下で宣言した。scoped 側が
`Fintype G` / `Fintype ↥H` / `Invertible (Nat.card G)` / `Invertible (Nat.card ↥H)` を
`Finite G` から一様に供給するので、§8D/§8E の `[Fintype G]` binder と混ざらない。
(下記の失敗記録どおり、混ぜると `S04.Hypothesis` の引数が defeq にならない。)

### (参考) 一度失敗した記録 — instance 規律

**2026-07-20: 層の逆転は issue 1046 で解消済** (`dadeSupportHypothesisData_typePACore` →
`S10_TypePSupport`, `..._typePACore0` + 閉包 → 新 leaf `S10_TypePSupportA0`、いずれも
namespace `S10`)。⟹ §10 から両 producer を呼べる。

具体化は 1 度試して **instance 規律**で落ちたので、次回はこの 2 点を先に直すこと:

1. **`Invertible (Nat.card ↥((derivedInG M).subgroupOf M) : ℂ)` が要る** —
   §8D の `section SubcoherentTypeP` は `variable` でこれを宣言している
   (`S10_SubcoherentTypeP.lean:111`)。§8E の `CoreNontrivialSupport` 節にも同じ
   `variable` を足す。
2. ⚠ **scoped `FiniteInduce` と `[Fintype G]` binder を混ぜない** — 実エラー:
   ```
   ⋯.some.dade : @S04.Hypothesis G inst✝⁵ inst✝⁴ (typePACore0 M data) M
   but expected : @S04.Hypothesis G inst✝⁵ S12.FiniteInduce.finiteGFintype (typePACore0 M data) M
   ```
   `typePACore_toHypothesis46_core` は `open scoped S12.FiniteInduce` の下で宣言されており
   `Fintype G` を **`S12.FiniteInduce.finiteGFintype` (= `Finite G` 由来)** で取る。
   §8E 節は `variable [Fintype G]` binder なので defeq にならない。
   ⟹ 具体化の def は **`[Finite G]` だけを取り、`open scoped OddOrder.Peterfalvi.S12.FiniteInduce in`
   の下で宣言する** (`S10_Hypothesis46TypeP` と同じ規律)。
   正本 = [[lean-instance-defeq-traps]]「scoped FiniteInduce vs binder 混在不可」。
   本 issue 着手順 2 の作業でも同じ罠を一度踏んでいる (上記「着手順 2 完了」の注記)。

書く内容 (試作は revert 済、build green を維持):
```
noncomputable def typePACore_subcoherent [Finite G]
    (hG : IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G) (hTP : IsTypeP M)
    (hodd : Odd (Nat.card ↥M)) (data : TypePData M) (hHall : …) (hW2σ : …) (hσK : …)
    (hsub : S ⊆ inducedNonKernelFamily ((derivedInG M).subgroupOf M) ((Msigma M).subgroupOf M))
    (hirr) (hconjS) :
    S07.Hypothesis S (S04.supportInSubgroup (typePACore M) M) :=
  inducedNonKernelFamily_subcoherent hodd
    (typePACore_toHypothesis46_core data hG.odd hHall
      (dadeSupportHypothesisData_typePACore0 hG hM hTP data).some.dade
      (…).some.hconj hW2σ hσK).toCore
    (dadeSupportHypothesisData_typePACore hG hM hTP).some hsub hirr hconjS
```
⚠ `h46.toCore.K` / `.subH` が `(derivedInG M).subgroupOf M` / `(Msigma M).subgroupOf M` と
defeq であること (`typePData_toS06Hypothesis` の `K := (derivedInG M).subgroupOf M`,
`typePACore_toHypothesis46` の `subH := H`) に依存する。合わなければ橋渡し補題を足す。

### (参考) 解消済だった層の逆転

必要な部品は 2 つとも既に在るが、**どちらも S15 に置かれている** (実測 2026-07-20):

| 部品 | 場所 | 型仮定 |
|---|---|---|
| `S15.dadeSupportHypothesisData_typePACore` | `S15_SAndT_Setup/SubcoherenceInputs.lean:706` | `IsTypeP` のみ = **型一様** |
| `S15.dadeSupportHypothesisData_typePACore0` | `S15_HonestTypeP2A0.lean:538` | `IsTypeP` のみ = **型一様** |

これらは書籍 **(8.15) claim 1** そのもの (§8 の内容) なのに §13 の file / namespace `S15` に居る。
`sSet_finite` (§9 の事実が §15 に居た、commit 998d28af5 で是正) と**同型の層の逆転**。

⚠ 移設の規模: `dadeSupportHypothesisData_typePACore0` は `S15_HonestTypeP2A0.lean`
(**1266 行**、namespace `S15`、importer 6 — うち `FeitThompsonNuGrid` /
`FeitThompsonCharacterData` は spine) のローカル補題群 (`typePACore0_subset` /
`_ne_one` / `_conj_mem` / `escaping_typePACore0_mem_typePACore` /
`not_isConj_typePACore_typePV`) に依存するので、**ファイル単位の移設**になる。
実体は §8 の A₀(M) 論なので `S10_TypePSupportA0.lean` 相当が正しい置き場。
⚠ spine file を触るので [[relayer-verify-with-build-not-bfs]] に従い edge ごとに build 検証する。

⟹ 次の一手 = この移設 (別 issue 化して段階実施)。移設後に
`inducedNonKernelFamily_subcoherent` へ `h46 := typePACore_toHypothesis46_core …` と
`d := dadeSupportHypothesisData_typePACore …` を渡すだけで型一様な (8.15.3) の具体化が終わる。

⚠ **薄いラッパーは書かない**: 一般 producer に `A := typePACore M` を渡すだけの specialization は
CLAUDE.md のラッパー方針で不可。具体化として価値があるのは「族が書籍の
`{Ind_{M′}^M θ | M_σ ⊄ Ker θ}` に一致する」ことの明示 (= `h46.toCore.K` /
`.subH` の同定) と、下流 consumer への接続。

### docstring の精度 (2026-07-20 に是正済)

§8E の docstring は「`H = K` のとき 2 つの絞りは一致する (= P₁ の符合)」と書いているが、
形式化されているのは**下流で実際に使う `⊆` 方向のみ**
(`inducedNonKernelFamily_subset_inducedKernelFamily_bot` = `H ⊄ Ker θ ⟹ θ ≠ 1`)。
逆 `θ ≠ 1 ⟹ K ⊄ Ker θ` (= 既約指標の核が全体なら自明指標; 経路は
`IsIrreducibleCharacter.inner_self_eq_one` で次数 1 を強制) は標準事実だが**未形式化**。
⟹ docstring 側に「motivation であって formalized lemma ではない」と明記した
(検証済のように読ませない)。必要になったら形式化する。

なお `inducedKernelFamily_subcoherent` 自体は `hKsupp` を引数化すれば `A₀` について一般化できる
(item 1 の `typePData_toHypothesis46_ofSupport` と同じ形) ので、**族の絞りと支持補題が本体**。

関連: issue 1045 ((9.11) の §9 レベル化) — (9.11) の base subfamily coherence は
現状 §10 engine (`inducedFamily_degreeSubfamily_isCoherent`) 経由だが、書籍では (8.15.3) 経由。
⟹ 本項が (9.11) 型 II 化の上流 prerequisite。文書順でも §8 < §9。

## ✅ 完了 (2026-07-20) — (8.15) の 3 主張すべてが型一様で形式化された

| 主張 | 形式化 | 型仮定 |
|---|---|---|
| claim 1 (Hyp (2.2) / `M = N_G(A)`) | `S10.dadeSupportHypothesisData_typePACore` / `_typePACore0` (issue 1046 で S10 へ移設) | `IsTypeP` のみ |
| claim 2 (Hyp (4.6), H = M_F / M_s) | `S10.typePACore_toHypothesis46_core` / `_hallKernel` | 素の `TypePData` |
| claim 3 (Hyp (5.2)) | **`S10.typePACore_subcoherent`** (§8F, commit 26cb99374) | `IsTypeP` のみ |

⟹ 型 II/V を含む全型 `𝒫` で書籍の文に到達。`lake build OddOrder` green (4546 jobs)、
全宣言 axiom-clean、AxiomsCheck 登録済。

**下流**: issue 1045 ((9.11) の §9 レベル化)。(9.11) の base subfamily coherence は現状
§10 engine 経由だが、書籍では (8.15.3) 経由 — 本 issue の完了でその素材が揃った。

## 着手順 (ungated → gated)

1. ~~**主張 3 の type III/IV 形**~~ ✅ 上記 (2026-07-19)。旧計画:
   `Hypothesis (5.2)` の repo 対応物を確認 (S07 の coherence context;
   (5.2) = 「S ⊆ Irr L induced family + τ isometry」形の仮説) し、
   (1.5.e) + (5.3.b) 経由で instance を証明。
   ⚠ まず「repo に (5.2) 対応の Hypothesis オブジェクトが在るか」を grep
   (frontier note の (9.11) 行いわく「repo に Hypothesis (9.5) が無い」同様、
   (5.2) も handle が無い可能性 — その場合 (5.2) carrier の新設から)。
2. **主張 2 の一般形** (H = M_F と H = M_s の両方; type III/IV は M_s = M′):
   既存 S12 の Hypothesis46 producer を (8.15) 名義の一般 statement に持ち上げ。
3. **type II/V** (gated): 9000 issue で hub 設計確認後。

## 参照

- frontier note §8 (8.15) 行 / issue 9008 (closed; Option B 裁定と re-open 条件)
- S10_StructureSetup.lean:703-750 (DadeSupportHypothesisData + TODO)
- 書籍 p.47-48 (PDF pages 4-5)
