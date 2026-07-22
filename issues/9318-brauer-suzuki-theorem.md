---
id: 9318
slug: brauer-suzuki-theorem
title: "Brauer-Suzuki 定理: 一般化四元数 Sylow 2 → G = O_{2'}(G)C_G(u)"
created: 2026-07-21
---

# Brauer-Suzuki 定理: 一般化四元数 Sylow 2 → G = O_{2'}(G)C_G(u)

## 🎯 HUB RULING (2026-07-22, ユーザー裁可): claim owner **b → c 移管**

本 issue の owner を **lane c** に移管する。c の primary frontier = 本 issue。根拠:

1. **b は未着手** (2026-07-22 実測: main..b に BS 関連 commit 0、調査 checkbox 未チェック)
   かつ issue 2053 Theorem B の 17-step campaign 進行中 — b は 2053 に専念する。
2. **c は既に前提 2 件を完了済** (下記 checkbox、issue 9404 closed) で文脈を持っている。
3. **消費点 `rankOne_affine_nearField` (NearFields.lean) は c 所有ファイル** — 自所有の
   gate を自分で外す形になり、gated-frontier 問題も同時に解消。
4. c の BG scope は closed (Thm A(6)/(7) landing、実 sorry 0) で live frontier が空だった。

b 側は Theorem B step (2) で App C Prop 1 を **sorried-cite** してよい (signature は
`rankOne_affine_nearField` で確定済、[[feedback-cite-sorried-lemmas-if-signature-correct]])。
BS 本体の置き場所は一般有限群論ゆえ `OddOrder/GroupTheory/**` (shared) を第一候補とし、
新 leaf は claim-before-build どおり本 issue が claim を兼ねる (c は 9400 番台で追加
claim を切ってもよい)。step 1.5 の所有 regex 変更は不要 (shared_re / c_re で被覆)。

## 背景

Peterfalvi Appendix C Prop 1 (`rankOne_affine_nearField`, NearFields.lean:741)
は honestly-stated sorry で、その未形式化前提の最大物が **Brauer–Suzuki 定理**
(Sylow 2-subgroup が一般化四元数なら G = O_{2'}(G)·C_G(u)、u は中心的 involution;
系として G は単純でない)。Ch.II Theorem B (issue 2053 step (2)) が App C Prop 1
を消費するため、lane b が claim する。~~(claim 経緯)~~ → **2026-07-22 に c へ移管
(冒頭 HUB RULING 参照)**。

他の前提 2 つは軽い: Huppert III 8.2 (2-rank 1 → Sylow-2 cyclic or
generalized quaternion) と Huppert II 3.2 (normal complement)。

Brauer–Suzuki の証明は指標理論 (block theory or 例外指標)。Isaacs FGT には
無い (Ch.7 の quaternion 関連は別)。文献: Gorenstein Ch.12? / Isaacs
Character Theory Ch.7 (block-free proof by Glauberman?)。repo の指標 infra
(Peterfalvi S04 Dade isometry 系) との接続を調査してから証明戦略を決める。

## やること

- [ ] 証明戦略調査 (Gorenstein §12.1 / Glauberman の block-free 証明 /
      Coq odd-order に相当物があるか grep)
- [ ] cyclic Sylow-2 case (Cayley normal 2-complement で軽い) の確認
- [ ] generalized quaternion case の形式化
- [x] ~~Huppert III 8.2 / II 3.2 の form 化~~ → **lane c が完了 (2026-07-22)**:
      II 3.2 = `GroupTheory/SolvableTwoTransitive.lean`
      `exists_elementaryAbelian_regular_normal_of_isMultiplyPretransitive` (issue 9404 closed)、
      III 8.2 = `NearFields.lean` `RankOneHypothesis.sylow_two_isCyclic_or_quaternion`
      (two_rank_one → Isaacs Thm 6.11 橋)。いずれも axiom-clean。
- [ ] rankOne_affine_nearField の sorry 解消 (残 gate は BS 本体のみ)

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

---

## 証明戦略調査 (2026-07-22, lane c) — Gorenstein Ch.12 読了

### 原典の所在 (実測)

- **Gorenstein Ch.12 "Groups with Generalized Quaternion Sylow 2-Subgroups"**
  (`finite-groups.pdftotext.txt` L20072〜、書籍 pp. 373-377) = **Thm 1.1 (Brauer-Suzuki)**、
  `|S| ≥ 16` を例外指標理論で証明する短章。**`|S| = 8` (Q8) は「all known proofs require
  the theory of modular characters」と明記** (1968 時点) — Q8 は別ルート要調査。
- 支持機構: **Thm 4.6 (Brauer-Suzuki)** = TI 集合上の誘導等長 (L8117)、
  **Thm 5.4 (Brauer-Suzuki)** = 例外指標系の存在 (L8533)。
- **Coq odd-order に BS 無し** (grep 実測 0 件 — 奇数位数群に involution が無いので当然)。

### Gorenstein Ch.12 の証明骨格 (|S| = 2^n ≥ 16)

Setup: `x` = S の指数 2 巡回部分群の生成元、`X = ⟨x⟩`, `T = ⟨x²⟩`, `R = ⟨x⁴⟩`,
`C = C_G(T)`, `N = N_G(T)`。
1. **Lem 1.2**: `N = SH` (`H ⊴ N` 奇数位数)、`C = XH`。X が C の cyclic Sylow-2 →
   Burnside normal 2-complement (G Thm 7.6.1 = mathlib Burnside)。
2. **Lem 1.3**: `A = C − RH` は **TI subset**、`N_G(A) = N`。
3. **Lem 1.4**: ψ = C の線形指標 (RH ⊆ ker、x ↦ i) の誘導 ψ̃ (N 上既約 deg 2)、
   `θ = 1_C↑N − ψ̃`: `(θ,θ)_N = 3`、`deg θ = 0`、`θ ≡ 0 on N − A`。
4. **TI 等長** (G Thm 4.4.6): `(θ*,θ*)_G = 3`、Frobenius 相互律で 1_G の重複度 1 →
   **Lem 1.5**: `θ* = 1_G + χ₁ − χ` (χ₁ ≠ χ 非主既約)。
5. **Lem 1.6**: involution・奇数位数元上で `θ* = 0` → `χ = 1 + χ₁` そこで。
6. **Lem 1.7**: β(y) = #{(u,v) : involutions, uv = y} は偶数位数 y で 0
   (一意 involution ⟹ Klein four が存在しない)。
7. **(9.4.2)**: β(y) = |G|/|C_G(u)|² Σᵢ ζᵢ(u)²ζᵢ(y)/ζᵢ(1) (class 積の構造定数公式)。
8. Σ β·θ* = 0 + 直交性 → **Lem 1.8**: `1 + χ₁(u)²/χ₁(1) − χ(u)²/χ(1) = 0` →
   **Lem 1.9**: `(χ(u) − χ(1))² = 0` → **全 involution ⊆ ker χ**、χ 非線形。
9. **endgame (純群論)**: `M = ⟨involutions⟩ ⊴ G`、`Q = S∩M` は cyclic (さもなくば
   SM の非線形指標が線形化して矛盾) → Burnside → `L ⊴ G` 奇 → `KQ ⊴ G`
   (`K = O_{2'}(G)`) → `Ḡ = G/K` で `Ω₁(Q̄) = Z(Ḡ)`、位数 2。□

### repo 資産との対応 (grep 実測)

| Gorenstein | repo |
|---|---|
| Thm 4.4.6 (TI 誘導等長) | `inner_induce_eq_of_isTISubset` / `induce_apply_coe_of_isTISubset` (InducedCharacter.lean、generic・sorry-free) |
| (9.4.2) 構造定数公式 | `ClassSumCoefficientFormula.lean` `classSumCoeff_mul_centralizer_card_eq_sum_irreducibleCharacter` |
| Thm 7.6.1 (Burnside) | mathlib (`Sylow.ker_transferSylow_isComplement'` 系; Ch05 で被覆済記録) |
| quaternion 分類 | mathlib `QuaternionGroup` + `Isaacs.Ch06.isCyclic_or_two_quaternion_of_subgroups_card_prime_unique` |
| norm-3/deg-0 分解 (Lem 1.5) | Pf S03/S05 の IsometryDifferencePair 系パターン (要 adapt) |

### 形式化順序 (提案)

1. **cyclic Sylow-2 case** (軽い): Burnside → `G = O_{2'}(G) ⋊ S` → `G = O_{2'}(G)·C_G(u)`。
2. **|S| ≥ 16 case**: 上記骨格を新 leaf 群 (`OddOrder/GroupTheory/BrauerSuzuki*.lean`) で。
   最難所は Lem 1.4-1.5 (指標の具体構成 + norm 計算) と (9.4.2) の接続。
3. **Q8 case**: 別調査 — block-free 証明の文献特定 (Glauberman?) or 教科書省略として
   ChatGPT 再構成ルート ([[feedback-ask-chatgpt-for-elided-gaps]])。**ここだけが真の
   research-adjacent gap**。
4. 統合 → `rankOne_affine_nearField` の sorry 解消。

## 進捗 (2026-07-22, lane c)

- ✅ **cyclic case** (`BrauerSuzuki.lean` `brauerSuzuki_of_isCyclic_sylowTwo`)。
- ✅ **quaternion setup** (`BrauerSuzukiSetup.lean`): presentation → S = X ∪ X·y、
  unique involution z、T ⊴ S、S ∩ C = X。
- ✅ **Gorenstein Lem 1.2** (`BrauerSuzukiNormalizer.lean`): X = C の cyclic Sylow-2、
  Burnside 2-補群 H (= C の奇数位数元全体、choice 非依存)、**C = XH**、H ⊴ N、
  **N = SH**。全て axiom-clean + AxiomsCheck 登録。
- ✅ **Gorenstein Lem 1.3 (TI 性)** (`BrauerSuzukiTISubset.lean`): **`A_isTISubset :
  IsTISubset Q.A Q.N`**(`A = C − RH`)。核心 = `T_le_zpowers_of_mem_A`「`a∈A ⟹ T ≤ ⟨a⟩`」
  (a の 2-part `a₂` が `X` の C 内共役 `cxc⁻¹` に入る → `T` は `⟨a⟩` 唯一の位数 2ⁿ⁻¹
  部分群 → `T = g⁻¹Tg`)。汎用 cyclic 補題も追加: `eq_of_le_zpowers_of_card_eq`
  (同位数部分群一意性)・`le_of_le_zpowers_of_card_dvd`(入れ子)・
  `zpowers_eq_of_mem_of_orderOf_eq`。axiom-clean (`[propext, Classical.choice, Quot.sound]`)。
  → 下流 Lem 1.4 の induced-character 等長 `inner_induce_eq_of_isTISubset` が直接消費可能。
- ✅ **`N ≤ N_G(A)`** (`conj_mem_A_of_mem_N`): N は A = C−RH を正規化。核心 = `map_R_conj_of_mem_N`
  (R char T ⊴ N を cyclic 一意性で `R.map (conj n) = R`) + `map_H_conj_of_mem_N` → `RH ⊴ N`。
- ✅ **完全等式 `N = N_G(A)`** (`mem_N_iff_forall_conj_mem_A`): 逆向き `N_G(A) ≤ N` も完成。
  基盤 = **`mem_RH_iff`** (RH = R·H 積構造、R 中心的ゆえ H と可換) + `X_inf_H_eq_bot` +
  `x_notMem_RH` (x∈RH⟹x∈R⟹位数|2ⁿ⁻²、矛盾) → **`A_nonempty`** (x∈A)。
  → **Gorenstein Lemma 1.3 完全形式化 (axiom-clean [propext, Classical.choice, Quot.sound])**。
- 次 = **Lem 1.4** の指標構成 (ψ: C の線形指標 RH ⊆ ker、ψ̃ = ψ↑N 既約 deg 2、
  θ = 1_C↑N − ψ̃ norm 3)。TI 集合 A + 等長 lemma は形式化済。

### Lem 1.4 計画 (2026-07-22 lane c、⚠ 下記 infra は grep 発見のみ・API 未精査)

Gorenstein Lem 1.4: `θ = 1_C↑N − ψ̃` について (i) `(θ,θ)_N = 3` (ii) `deg θ = 0`、
`N − A` 上で `θ = 0`。使えそうな既存 repo infra (要 API 精査):
- **`RepresentationTheory/LinearCharacter.lean`** — 線形指標 (ψ: C→ℂ の構成、値 i on x)
- **`RepresentationTheory/InflationCharacter.lean`** — RH ⊆ ker の inflation 構成
- **`RepresentationTheory/Clifford.lean` / `CliffordCorrespondence.lean`** — ψ↑N の既約性
  (C は N 内 index 2、ψ が N-不変でない ⟹ 誘導既約; Clifford/Mackey)
- **`RepresentationTheory/InducedCharacter.lean`** — `induce`/`induce_add`/`induce_smul`/
  `induce_apply_one`、内積、**`inner_induce_eq_of_isTISubset` (TI 等長 ← `A_isTISubset` が feed)**
- **`Peterfalvi/S05_NormThree.lean`** — norm-3 パターン ((θ,θ)=3、Lem 1.5 の θ* 分解へ)
- Tc = `1_C↑N` = N/C (index 2) の正則表現指標 = 1_N + (N/C の非自明線形指標)
証明順: ψ 構成 (LinearChar, x↦i, RH⊆ker) → ψ̃=ψ↑N 既約 deg 2 (Clifford) →
θ 定義・deg 0 → (θ,θ)_N=3 (Thm 4.2.4(i) = 内積計算) → N−A 上 θ=0 (Thm 4.4.3(ii))。

#### ψ 構成の具体経路 (2026-07-22、RH 積構造 commit e039809db を基盤に確定)

**`C/RH ≅ ℤ/4`** が ψ の土台。実測で確定した部品:
- `mem_RH_iff` (積構造) + `mem_R_of_mem_X_of_mem_RH` より **`x² ∉ RH`** (x²∈RH⟹x²∈R=⟨x⁴⟩⟹
  orderOf x²=2ⁿ⁻¹ ∣ 2ⁿ⁻², 矛盾) かつ **x⁴ ∈ R ⊆ RH**。⟹ `orderOf (xRH) = 4`。
- `C = XH`、H ⊆ RH ⟹ **`C/RH = ⟨xRH⟩`** (巡回、位数 4 = ℤ/4)。∴ 未計算の |C|/|RH| 不要。
- **ψ 構成手順**: (1) `(RH.subgroupOf C) ⊴ ↥C` (RH ⊴ N ⊇ C より)。(2) 商 `↥C ⧸ (RH.subgroupOf C)`
  ≅ ℤ/4 (gen = xRH 像, 位数 4)。(3) ℤ/4 → ℂˣ (gen ↦ i = `Complex.I` の単元) の character。
  (4) `InflationCharacter.inflate` or `compHom` で ↥C に inflate → χ : ↥C →* ℂˣ。
  (5) `LinearCharacter.linearClassFunction χ` = ψ (ClassFunction ↥C ℂ)。RH ⊆ ker は構成から自明。
- ψ̃ = `induce (C.subgroupOf N) ψ` 既約 deg 2: C は N 内 index 2、ψ ≠ ψ^{conj by N∖C} (ψ(x)=i vs
  ψ(x⁻¹)=−i)、Clifford/Mackey 既約判定 (`Clifford.lean`/`CliffordCorrespondence.lean`)。
- θ = `induce 1_C − ψ̃`、(θ,θ)_N=3: N/C の正則指標 Tc = 1_N+sgn、Thm 4.2.4(i) 内積。
  N−A 上 θ=0: RH⊆ker ψ ゆえ ψ↑N は A 上のみ非零 (`induce_apply` 系)。
