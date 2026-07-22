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

- [x] 証明戦略調査 (Gorenstein Ch.12 読了、下記)
- [x] **cyclic Sylow-2 case** → `brauerSuzuki_of_isCyclic_sylowTwo` (`BrauerSuzuki.lean`) 完成
- [x] **generalized quaternion case (|S| ≥ 16)** → `brauerSuzuki_of_quaternionSylow`
      (`BrauerSuzukiEndgame.lean`) **完成 2026-07-22, axiom-clean**。Lem 1.4〜1.9 (指標理論) +
      endgame (M 2-nilpotent / z̄ 中心 / Frattini) の全体。AxiomsCheck 登録済。
- [x] ~~Huppert III 8.2 / II 3.2 の form 化~~ → **lane c が完了 (2026-07-22)**:
      II 3.2 = `GroupTheory/SolvableTwoTransitive.lean`
      `exists_elementaryAbelian_regular_normal_of_isMultiplyPretransitive` (issue 9404 closed)、
      III 8.2 = `NearFields.lean` `RankOneHypothesis.sylow_two_isCyclic_or_quaternion`
      (two_rank_one → Isaacs Thm 6.11 橋)。いずれも axiom-clean。
- [ ] **Q₈ case (|S| = 8)** — 別ルート (modular character theory)、真の research-adjacent gap。
      Gorenstein は「all known proofs require the theory of modular characters」と明記。未着手。
- [ ] rankOne_affine_nearField の sorry 解消 (残: near-field transport (Pf p.137) + Q₈ BS)

## 状態 (2026-07-22 完了): BS 定理本体は cyclic + 一般化四元数 |S|≥16 で完成

**達成**: `oPiCore {p | p ≠ 2} G ⊔ centralizer {z} = ⊤` (= `G = O_{2'}(G)·C_G(z)`)。
cyclic case (`brauerSuzuki_of_isCyclic_sylowTwo`) と quaternion |S|≥16 case
(`brauerSuzuki_of_quaternionSylow`) の両方 axiom-clean [propext, Classical.choice, Quot.sound]。
**残る gap は Q₈ (|S|=8) のみ** — modular character theory を要し別 issue 相当。消費点
`rankOne_affine_nearField` は BS 以外に near-field transport が残るため sorry のまま。

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
- ✅ **Gorenstein Lem 1.4 完全形式化** (`BrauerSuzukiCharacter.lean`、2026-07-22、axiom-clean
  `[propext, Classical.choice, Quot.sound]`、sorry 0):
  - **構造前提**: `x² ∉ RH`、`y ∈ N ∖ C`、coset 分解 **`N = C ∪ yC`**
    (`mem_C_or_yinv_mul_mem_C`、自己完結部分群 K = C ∪ yC) → **`[N:C] = 2`**
    (`index_C_subgroupOf_N`、`index_eq_two_iff'`)。
  - **線形指標 ψ** (`psiHom : ↥C →* ℂˣ`): `C/RH ≅ ℤ/4` の忠実指標 x̄↦i を引き戻し。
    `orderOf x̄ = 4` (x²∉RH, x⁴∈RH)、`C/RH = ⟨x̄⟩` (`subgroupOf_sup` で X⊔RH=C)、
    `monoidHomOfForallMemZpowers` x̄↦iUnit → `mk'` 合成。`ψ(x)=i`、`RH⊆ker ψ`、`ψ≠1`。
  - **θ = Ind_C^N 1_C − Ind_C^N ψ** (`theta`): **`θ(1)=0`** (`theta_apply_one`)、
    **`θ≡0 on N−A`** (`theta_apply_eq_zero_of_notMem_A`、C外=normal support / RH上=同一定数)。
  - **`ψ≠ψʸ`** (`conjBy_y_psiN_ne_psiN`: x で ψʸ(x)=ψ(x⁻¹)=i⁻¹≠i) → **`I_N(ψ)=C`**
    (`inertia_psiN`) → **`Ind_C^N ψ` 既約** (`psiN_induce_irreducible`、
    `isIrreducibleCharacter_induce_of_inertia_eq`、bundled IrreducibleCharacter)。
  - **`(θ,θ)_N = 3`** (`theta_inner_self`): (Tc,Tc)=[N:C]=2 − (Tc,Ps)=0 − (Ps,Tc)=0
    + (Ps,Ps)=1。使用: `induce_trivial_inner_self` / `induce_inner_induce_trivial_eq_zero_of_irreducible`
    / `inner_star_comm` / `irr_cf_inner`。
  - ⚠ 計画で想定した「Clifford で ψ↑N 既約」は **`InducedIrreducible.lean`
    `isIrreducibleCharacter_induce_of_inertia_eq` (inertia=H → 誘導既約) がより直接**だった
    (一般 Clifford correspondence の subtype juggling 不要)。deg 2 は使わず (deg θ=0 は
    [N:C] 相殺で deg
    値不要)。

### Lem 1.5 計画 (2026-07-22 lane c、次 frontier)

Gorenstein Lem 1.5: `θ* = Ind_N^G θ` (TI 誘導、`A_isTISubset` が feed)。
- **`(θ*,θ*)_G = 3`**: TI 等長 `inner_induce_eq_of_isTISubset` (θ が A 外で消滅 =
  `theta_apply_eq_zero_of_notMem_A` を feed) → `(θ*,θ*)_G = (θ,θ)_N = 3`。
- **`(θ*,1_G)_G = 1`**: Frobenius `inner_induce_eq_inner_restrict` → `(θ, 1_N)_N`
  = (Ind 1_C, 1_N) − (Ind ψ, 1_N) = 1 − 0 = 1。
- **`θ*(1) = 0`**: `induce_apply_one` で [G:N]·θ(1) = 0。
- ✅ **解析部完成** (`thetaStar` 系、2026-07-22 commit): `(θ*,θ*)_G=3` / `θ*(1)=0` /
  `(θ*,1_G)=1`。axiom-clean。

#### Lem 1.5 分解の実装計画 (2026-07-22、API 精査済 — 次 iteration frontier)

**⚠ 経路確定 (誤経路を排除)**: ρ = θ*−1_G は norm 2 だが **`ρ(1) = θ*(1)−1 = −1 ≠ 0`**
なので `exists_irr_sub_irr_of_inner_self_two` (ZIrrFourier:574、**`φ(1)=0` を要求**) は
**適用不可**。**norm-3 を θ* に直接適用**する (θ*(1)=0 は満たす)。

必要な部品:
1. **`θ* ∈ ZIrr G`** — `induce_mem_ZIrr Q.N (hθ : θ ∈ ZIrr N)` (InducedCharacter:1062)。
   θ ∈ ZIrr N は θ = Ind 1_C − Ind ψ (両者 character ∈ ZIrr) の差。要 `induce_mem_ZIrr` を
   C.subgroupOf N に 2 回 + `sub_mem`。
2. **`exists_triple_of_sum_sq_eq_three`** (新 infra、`exists_pair_of_sum_sq_eq_two`
   ZIrrFourier:262 の 3 版): `∑_{a∈s} cₐ² = 3 ∧ cₐ≠0 → s = {α,β,γ} 相異 ∧ 各 cₐ=±1`。
   証明: 各 cₐ²≥1、和=3 → card≤3; card=1(c²=3 不可)・card=2(c₁²+c₂²=3 整数解無)を omega 排除
   → card=3、各 cₐ²=1。
3. **1_G の係数 = 1**: `inner_eq_coeff_of_repr` (ZIrrFourier:117) で c(1_G) = (θ*,1_G) = 1
   (`thetaStar_inner_trivial`)。
4. **次数論法**: θ*(1) = ∑ cᵢ dᵢ = 0、1_G の項 = 1·1、残り 2 項 c₁d₁+c₂d₂ = −1、
   cᵢ=±1・dᵢ≥1 → 一方 +1 他方 −1 かつ |d₁−d₂|=1 → **θ* = 1_G + χ₁ − χ、χ(1)=χ₁(1)+1**。
   `exists_irr_sub_irr_of_inner_self_two` の (±1,±1) case 分析 (597-613) が雛形。

出力定理 (提案): `∃ χ₁ χ : IrreducibleCharacter G, χ₁ ≠ χ ∧ χ₁ ≠ 1 ∧ χ ≠ 1 ∧
  θ* = 1_G + χ₁ − χ ∧ χ(1) = χ₁(1) + 1`。→ 下流 Lem 1.6 (involution/奇数位数元上 θ*=0) へ。

#### ✅ 基礎完了 (2026-07-22 commit 3c3e07c38) + 分解本体の確定手順

**完了**: `exists_triple_of_sum_sq_eq_three` (汎用) + `theta_mem_ZIrr` /
`thetaStar_mem_ZIrr` (∈ZIrr)。`thetaStar_inner_self=3` / `_apply_one=0` /
`_inner_trivial=1` も既済。

**⚠ 最終判断: 分解本体は ρ = θ*−1_G (norm 2) 経由が最良** (triple 版より nontrivial 判定が楽):
`exists_irr_sub_irr_of_inner_self_two` (ZIrrFourier:574) は φ(1)=0 要求で ρ(1)=−1 に
不適 → **その proof (578-613) を ρ 用に複製**する。手順:
1. `ρ := θ* − 1_G`、`hρZ : ρ ∈ ZIrr` (`sub_mem thetaStar_mem_ZIrr trivial.mem_ZIrr`)。
2. `(ρ,ρ)=2`: `inner_sub_left/right` 展開 = (θ*,θ*)−(θ*,1)−(1,θ*)+(1,1) = 3−1−1+1
   ((1,θ*)=conj(θ*,1)=1 via `inner_star_comm`、(1,1)=1 via `irr_cf_inner`)。
3. `ρ(1)=−1`: `sub_apply` + `thetaStar_apply_one` + `trivialClassFunction_apply`。
4. Fourier `mem_ZIrr_inner_self_eq_sum_sq hρZ` → c, `Σc²=2` → `exists_pair_of_sum_sq_eq_two`
   → α₀,β₀ 相異・c=±1、`hrepr : ρ = cα•α₀ + cβ•β₀`。
5. 次数: `irreducibleCharacter_apply_one_eq_pos_natCast` → dα,dβ≥1、
   `hone' : cα·dα+cβ·dβ = −1` (hρ1 に hrepr 代入)。
6. **4-case (cα,cβ)=(±1,±1)**: (+,+)→dα+dβ=−1 不可、(−,−)→dα+dβ=1 だが dα,dβ≥1 で不可、
   (+,−)→dβ=dα+1 [χ₁=α₀,χ=β₀]、(−,+)→dα=dβ+1 [χ₁=β₀,χ=α₀]。
7. **nontrivial**: `(ρ,trivial)=0` (=(θ*,1)−(1,1)=1−1)、かつ `(ρ,α₀)=cα₀` (hrepr+orthonormality)。
   α₀=trivial なら (ρ,α₀)=(ρ,trivial)=0 だが cα₀=±1≠0 で矛盾 → α₀≠trivial (β₀ も同様)。
8. `θ* = 1_G + ρ = 1_G + χ₁ − χ` (`hρ` を戻す + abel)。
triple 版 (θ* 直接、`exists_triple_of_sum_sq_eq_three`) は trivial が {α,β,γ} の
どれかの 3-way 識別が必要で冗長 — triple 補題は汎用 infra として保持 (別 norm-3 用)。

### ✅ Lem 1.5 完成 (2026-07-22 commit 3e56a40ca)

`thetaStar_decomposition`: **θ* = 1_G + χ₁ − χ** (χ₁≠χ 非主既約、χ(1)=χ₁(1)+1)。
上記 ρ+pair 手順どおり、次数 4-case は ℤ で `exact_mod_cast` → omega。axiom-clean。
→ **Lemma 1.4 + 1.5 完全形式化完了** (`BrauerSuzukiCharacter.lean`、~660 行、sorry 0)。

### ✅ Lem 1.6 完成 (2026-07-22 lane c、`BrauerSuzukiCharacter.lean` + `BrauerSuzukiTISubset.lean`)

Gorenstein Lem 1.6: **involution・奇数位数元上で θ* = 0** かつ **χ(y) = 1 + χ₁(y)**。全て
axiom-clean (`[propext, Classical.choice, Quot.sound]`)、AxiomsCheck 登録済 (Lem 1.3/1.4/1.5
も同時に import+登録 — 従来 AxiomsCheck は Normalizer までしか import していなかった)。

**⚠ 原文より簡潔な機構を採用** (z 個別の議論不要): 「θ* = Ind_N^G θ は A の共役の外で消滅」
(`induce_eq_zero_of_not_conjugatesIntoSet`、θ が A に台) × 「**A の元は位数が 4 で割れる**」
(新 `four_dvd_orderOf_of_mem_A`: a∈A ⟹ T ≤ ⟨a⟩ ⟹ |T|=2ⁿ⁻¹ ∣ orderOf a、n≥3 で 4 ∣ 2ⁿ⁻¹)。
位数は共役不変 (`SemiconjBy.orderOf_eq`) ゆえ involution (order 2)・奇数位数元は A に共役外
→ θ*(y)=0。実装補題:
- `four_dvd_orderOf_of_mem_A` (TISubset) — A の元の位数は 4 で割れる。
- `thetaStar_apply_eq_zero_of_not_four_dvd` (Character) — ¬4∣orderOf y ⟹ θ*(y)=0 (核心)。
- `thetaStar_apply_eq_zero_of_orderOf_eq_two` / `_of_odd` — involution / 奇数位数元で θ*=0。
- `apply_eq_of_thetaStar_apply_eq_zero` — θ*=1_G+χ₁−χ に θ*(y)=0 を代入 ⟹ χ(y)=1+χ₁(y)。

### ✅ Lem 1.7 核心完成 (2026-07-22 lane c、`BrauerSuzukiInvolutions.lean` 新 leaf)

Gorenstein Lem 1.7 の**純群論核心**を完成 (axiom-clean、AxiomsCheck 登録済):
- **`commute_involution_eq`**: 可換な involution 対 u,v は相等。⟨u,v⟩ (可換ゆえ elementary
  abelian 2-group、`closure_induction₂` で abelian・全元 sq=1 → `IsPGroup 2`) は Sylow-2 P に
  含まれ (`IsPGroup.exists_le_sylow`)、P は S に共役 (`MulAction.exists_smul_eq`)。共役で u,v を
  S に落とすと `eq_one_or_eq_z_of_sq_eq_one` (S の unique involution z) より両者 = z → u=v。
- **`odd_orderOf_mul_of_involution`**: involution 積 u·v は奇数位数。もし偶数 2s なら z'=(uv)ˢ が
  involution で u,v が反転・中心化 (`SemiconjBy.pow_right`) → `commute_involution_eq` で u=v=z'
  → uv=z'²=1、偶数位数 ≥2 と矛盾。**= β(y)=0 for even order y** (involution 対は偶数位数元を作らない)。
- **`exists_conj_eq_z`** (任意 involution は z に共役) + **`isConj_of_orderOf_eq_two`** (全
  involution は互いに共役 = **G は単一 involution 共役類 K**)。Sylow 部分は helper
  `exists_conj_subgroupLe_S` に factor して 3 補題で共有。→ Lem 1.8 の (9.4.2) で Ci=Cj=K の入力。
- setup 確認済: `QuaternionSylowSetup` は `S : Sylow 2 G` を posit ゆえ全 Sylow-2 が S 共役で
  unique involution。原文の「z 個別 Klein-four」議論より `commute_involution_eq` 汎用形が簡潔だった。

### ✅ Lem 1.8 完成 (2026-07-22 lane c、`BrauerSuzukiCounting.lean` 新 leaf、axiom-clean)

**`lem_1_8_relation`: `1 + χ₁(u)²/χ₁(1) − χ(u)²/χ(1) = 0`** (u = involutionClass.out)。
sub-step 分割で完成: `mk_eq_involutionClass_iff` / `classSumCoeff_involutionClass_eq_zero_of_even`
(step 2) / `sum_classSumCoeff_thetaStar_eq_zero` (A) / `sum_thetaStar_char_div_centralizer_eq_inner`
(B1: (9.4.2)-weighted class 和 = ⟨θ*,χ⟩、orbit-stabilizer + apply_inv) /
`sum_degWeight_inner_eq_zero` (B2: (9.4.2) 代入) / `lem_1_8_relation` (⟨θ*,ψ⟩ 重複度 collapse +
|K|² 除)。全 AxiomsCheck 登録済。⚠ 実装で苦労した点 = ClassFunction (submodule subtype) の
coercion: `simp_rw [∀χ hinner]` は binder 下で coercion mismatch → `simp only [hdecomp]`
(ground rewrite) + `irr_cf_inner` (ClassFunction 版) で回避。

### ✅ Lem 1.9 完成 (2026-07-22 lane c、`BrauerSuzukiCounting.lean` `lem_1_9`、axiom-clean)

**`lem_1_9`: G は非線形既約指標 χ (degree ≥ 2) を持ち、全 involution が χ(u)=χ(1) (ker χ)**。
下記手順どおり (thetaStar_decomposition + lem_1_8_relation + apply_eq + hdeg 代入 → field_simp +
linear_combination で (χ(u₀)−χ(1))²=0 → 任意 involution は u₀ 共役)。全 AxiomsCheck 登録済。
**これで Lem 1.4〜1.9 完成 = Brauer–Suzuki 指標理論核心 完了。**

### endgame 計画 (次 frontier、Gorenstein Ch.12 p.376-377、純群論、⚠ 大 piece)

`lem_1_9` の非線形 χ (全 involution ⊆ ker χ) から:
1. ✅ **M := ⟨全 involution⟩ ⊴ G** 完成 (`BrauerSuzukiEndgame.lean` 新 leaf、`involutionClosure` +
   `involutionClosure_normal`: involution 集合は共役不変ゆえ `le_normalizer_closure_iff` +
   `orderOf_eq_of_isConj` で closure 正規)。axiom-clean。
2. ✅ **`QuaternionSylowSetup ↥(SM)` 構築完成** (`smSetup`、最難所突破、axiom-clean):
   `Sylow.subtype` で Q.S を SM の Sylow-2 に制限、field transport (orderOf_mk / Subtype.ext+
   push_cast / hclosure = `Subgroup.map_injective` + `MonoidHom.map_closure` + `map_comap_eq`)。
   **Q := S∩M は cyclic** (残):背理で Q not cyclic ⟹ SM/M abelian ⟹ 矛盾。**全部品確定・feasible**:
   - **`not_isMulCommutative_quotient` helper** (rep-theory glue、~30 行): `lem_1_9 Q.smSetup` で
     SM の非線形 φ (φ(1)=d≥2) 取得 + `M.subgroupOf SM ⊆ characterKernel φ` (involution が M 生成、
     `characterKernel`=S03、`characterKernelSubgroup`=S13 が subgroup) + **鍵補題
     `apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient`**
     (InflationCharacter:344、M⊆ker + SM/M abelian → φ(1)=1) → φ(1)=1 vs d≥2 矛盾。
     ⟹ `¬ IsMulCommutative (↥SM ⧸ M.subgroupOf SM)`。
   - **`Q not cyclic → SM/M abelian`** (群論、~50-70 行 fiddly): Q⊴S (M⊴G)、Q⊄X (else cyclic) ⟹
     ∃ xᵏy∈Q ⟹ (Q⊴S で) x²∈Q ⟹ |S:Q|≤2 ⟹ S/Q abelian、SM/M≅S/Q (第二同型)。
   - 上 2 つが矛盾 → Q cyclic。
3. **M の正規 2-補群 L** (Burnside、Q=S∩M は M の cyclic Sylow-2)。L char M ⊴ G → **L ⊴ G**、
   L ⊆ K:=O_{2'}(G)。M=LQ ⟹ **KQ ⊴ G**。
4. **Ḡ:=G/K で Ω₁(Q̄)=Z(Ḡ) 位数 2** (Q̄ cyclic 正規、O_{2'}(Ḡ)=1 ⟹ Z(Ḡ) は 2-群、Z(S) 位数 2)。
   → **Z(G/O_{2'}(G)) 位数 2** = Gorenstein Thm 1.1。
5. **系 `G = O_{2'}(G)·C_G(u)`** (u = 中心 involution): Z(G/K) 位数 2 から Frattini 型で導出。
   → `rankOne_affine_nearField` (NearFields.lean) の sorry が要求する形へ橋渡し。

⚠ endgame は ~150-250 行の純群論 (⟨involutions⟩ 正規 / SM への Lem 1.9 適用 / Burnside /
G/K の中心解析)。Q8 case (|S|=8) は別途 research-adjacent gap のまま。

<details><summary>Lem 1.9 手順 (完成前の計画記録)</summary>

Gorenstein Lem 1.9: `(χ(u)−χ(1))²=0` → 全 involution ⊆ ker χ。手順:
1. `obtain ⟨χ₁,χ,...,hdecomp,hdeg⟩ := thetaStar_decomposition` (hdeg: χ(1)=χ₁(1)+1)。
2. `lem_1_8_relation hdecomp`: `1+χ₁(u)²/χ₁(1)−χ(u)²/χ(1)=0` (u=involutionClass.out)。
3. u は involution (`mk_eq_involutionClass_iff`: mk(out)=K → orderOf out=2)、θ*(u)=0
   (`thetaStar_apply_eq_zero_of_orderOf_eq_two`)、`apply_eq_of_thetaStar_apply_eq_zero hdecomp`:
   **χ(u)=1+χ₁(u)** → χ₁(u)=χ(u)−1。hdeg: χ₁(1)=χ(1)−1。
4. 代入 + 分母払い (χ₁(1),χ(1)≠0 = degree ≥1) → `(χ(u)−χ(1))²=0` → χ(u)=χ(1)。
   → 全 involution v: χ(v)=χ(u)=χ(1) (v~u 共役 + χ class fn) → v∈ker χ。χ 非線形 (χ(1)=χ₁(1)+1≥2)。

</details>

<details><summary>Lem 1.8 導出経路 (完成前の計画記録)</summary>

**核心洞察**: Gorenstein は per-element β(y) を使うが、`classSumCoeff` (= 共役類 Cs 全体で和を
取った版、`ClassSumCongruence.lean` 定義 = #{(u,v): u,v∈K, uv∈Cs}) で書き換えると per-element β
の定義を回避でき、既存の `classSumCoeff_mul_centralizer_card_eq_sum_irreducibleCharacter`
(`ClassSumCoefficientFormula.lean`) を直接使える。導出:

1. **K := ConjClasses.mk Q.z** = involution 共役類。`mk u = K ↔ orderOf u = 2`
   (`isConj_of_orderOf_eq_two` + `exists_conj_eq_z` + `orderOf z = 2`)。要 `orderOf_z` 補題。
2. **`classSumCoeff K K Cs · θ*(Cs.out) = 0`** (各 Cs): Cs.out が奇数位数 → θ*(Cs.out)=0
   (Lem 1.6 `thetaStar_apply_eq_zero_of_odd`); 偶数位数 → **classSumCoeff K K Cs = 0**
   (`odd_orderOf_mul_of_involution`: u,v∈K involution ⟹ uv 奇数位数 ⟹ uv∉Cs、filter 空)。
   → **要 `classSumCoeff_eq_zero_of_even_order` 補題**。
3. **(9.4.2) 代入**: `classSumCoeff K K Cs · |C_G(Cs.out)| = Σ_χ (|K|χ(u))²/χ(1) · χ(Cs.out⁻¹)`
   (Ci=Cj=K)。両辺に θ*(Cs.out)/|C_G(Cs.out)| を掛け Cs で和 → 左辺 0 (step 2)。
4. **重複度 collapse**: 右辺 = Σ_χ (|K|χ(u))²/χ(1) · [Σ_Cs χ(Cs.out⁻¹)θ*(Cs.out)/|C_G(Cs.out)|]。
   内側 = (1/|G|)Σ_{y∈G} χ(y⁻¹)θ*(y) = ⟨θ*, χ⟩ = χ の θ* 内重複度 (θ*=1_G+χ₁−χ より
   1_G:+1, χ₁:+1, χ:−1, 他:0)。→ |K|²(1 + χ₁(u)²/χ₁(1) − χ(u)²/χ(1)) = 0。
   **要**: ⟨θ*, χ⟩ の値 (既存 `thetaStar_decomposition` + 内積 API) と Σ_Cs → Σ_{y∈G} の
   class-function 和の変換 (`|Cs| = |G|/|C_G|`、既存 conjugacy sum API を要調査)。
5. **Lem 1.8**: |K|²≠0 で割り `1 + χ₁(u)²/χ₁(1) − χ(u)²/χ(1) = 0`。

⚠ step 4 の Σ_Cs ↔ Σ_{y∈G} 変換 (class 和) と ⟨θ*,χ⟩ 抽出が最難所。既存の column/row 直交
API (`ColumnOrthogonality.lean`) と inner product 定義の接続を精査してから着手。

</details>

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
