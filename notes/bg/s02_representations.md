# BG §2: General Results on Representations — mini-roadmap

**スコープ**: BG §2 (pp.9–16, mmd L586–794), **6 結果** (Thm/Prop/Lem 2.1, 2.2, 2.3, 2.4, 2.5, 2.6).

形式化先 (予定): `OddOrder/BG/Ch1_Preliminary/S02_Representations.lean`.

**ROADMAP 上の位置**: **Phase 2a 第 1 波必須節** — §3 (Frobenius 作用), §4, §15, App.A から引用される前提節.

**役割**: operator group の表現論基礎、Fong–Swan 系 (Thm 2.3)、extraspecial p-群の加群構造 (Thm 2.5)、odd-order 2-次元表現 (Thm 2.6). 監査で **8+ cites** を確認済みで、特に §3 と App.A への前提として優先度が高い.

## Audit log (2026-05-23 audit 訂正)

統合 doc: [`notes/meta/bg_phase2a_wave1_audit_2026_05_23.md`](../meta/bg_phase2a_wave1_audit_2026_05_23.md).

- **"§9 周辺で 1-2 箇所のみ被引用" → 完全に誤り**. 実測 §9 = **0 cites**. 実際: §3 ×5 (Prop 2.1, Prop 2.2 ×2, Thm 2.5, Thm 2.6 ×2 + 別 cite), §4 Lem 4.17, §15 Thm 15.7, **App.A Thm A.1 proof (L4464) で Thm 2.6 cite**. 合計 **8+ cites**, §2 は FT 中核.
- **"optional 節, 形式化は必要時のみ" / "skip 推奨" → 完全に逆**. §3 + App.A の **前提** ⇒ Phase 2a 第 1 波必須.
- **"Short path Thm 2.3 only" 推奨 → INVERTED**. Lem 2.3 (Fong-Swan) は forward use **0**, defer 可. Thm 2.5 + Thm 2.6 + Prop 2.1 + Prop 2.2 が必須.
- **L70 "Jacobson Density mathlib 未実装" → 誤り**. `Mathlib/RingTheory/SimpleModule/Basic.lean:582` `Module.Finite.toModuleEnd_moduleEnd_surjective` ✓.
- §2 ⇒ Peterfalvi §3-§8 オーバーラップなし (Peterfalvi は character-theoretic `[Is]`=Isaacs *Character Theory* 別書).
- **§2 は Isaacs Ch.6 §6F Clifford 完成依存** (Prop 2.2 で必須). Ch.6 not started ⇒ §2 全体 blocker.
- 新規 shared modules: `IsExtraspecial.lean`, `AbsolutelyIrreducible.lean`, `Clifford.lean`, `PGroupFixedVector.lean`, `EigenspaceUnderCyclicAction.lean`.

## 実装ログ

- **2026-05-24** [`OddOrder/BG/Ch1_Preliminary/S02_Representations.lean`](../../OddOrder/BG/Ch1_Preliminary/S02_Representations.lean) **skeleton 完成** (~330 行 docstring 中心). 6 sub-section (§2A Prop 2.1 / §2B Prop 2.2 / §2C Lem 2.3 / §2D Prop 2.4 / §2E Thm 2.5 / §2F Thm 2.6) に BG 本文 statement (mmd L598-793) + 形式化方針 + mathlib カバレッジ + 下流引用 (audit 実測) + Lean signature 案 を整理. **statement stub は全 6 結果未配置** (`RepresentationTheory/*` shared module 5 件未作成 + Isaacs Ch.6 §6F Clifford 未完成). 着手順 (audit 推奨): Thm 2.6 → Prop 2.4 → Prop 2.1 → Thm 2.5 → Prop 2.2 (Ch.6 待ち); Lem 2.3 (forward use 0, defer).
- **2026-05-24** (同日, 後続 commit) **Gorenstein G 引用 mapping rule 徹底**: 初回 skeleton で 7 個の G 引用 (Clifford G 3.4.1, Schur G 3.5.2, Jacobson G 3.6.2, 既約⟺Hom=F G 3.5.7, Lem 2.6.3 fixed vec, extraspecial repr G 5.5.4-5, Wedderburn) を素通ししていた CLAUDE.md L20 違反を訂正. 冒頭 mapping section + 6 箇所 inline 注記 + [`phase2_cross_refs.md`](../meta/phase2_cross_refs.md) §5 連動訂正. **重要確認**: Isaacs FGT (群論本) は `Clifford` `Jacobson` 0 hit, representation theory 章なし ⇒ BG §2 の G 引用は全部 Isaacs FGT 対応なし ⇒ mathlib + 新規 `OddOrder/GroupTheory/RepresentationTheory/*` shared module で再構築方針. feedback memory `feedback-bg-g-isaacs-mathlib-mapping` に永続化.
- **2026-05-24** (同日, 後続 commit) **§2F Thm 2.6 着手 — `PGroupFixedVector` shared module skeleton + Thm 2.6 (a)(b) Lean stub 配置**:
  - [`OddOrder/GroupTheory/RepresentationTheory/PGroupFixedVector.lean`](../../OddOrder/GroupTheory/RepresentationTheory/PGroupFixedVector.lean) 新規 (~95 行). mathlib `IsPGroup` namespace を直接拡張 (既存 `ChermakDelgado.lean` / `ElementaryAbelian.lean` の `Subgroup` namespace 拡張流儀踏襲). 主 statement: `IsPGroup.invariants_ne_bot` (`Representation F G V` で `IsPGroup p G` + `CharP F p` + `V ≠ ⊥` ⇒ `ρ.invariants ≠ ⊥`) + corollary `IsPGroup.exists_fixed_vector_ne_zero` (corollary は sorry-free, 主 stmt が sorry). Proof strategy docstring に |G| 帰納 + p-群 center 非自明 + `(ρ z - 1)^{p^k} = 0` (Frobenius binomial) + G/⟨z⟩ on `ker (ρ z - 1)` 帰納 構造を記載 (次セッションで sorry-free 化).
  - [`OddOrder/BG/Ch1_Preliminary/S02_Representations.lean`](../../OddOrder/BG/Ch1_Preliminary/S02_Representations.lean) に `import` 追加 + §2F 末尾に **Thm 2.6 (a) `odd_two_dim_abelian`** + **(b) `odd_two_dim_sylow_abelian`** の sorry 付き statement 配置 (BG §1 流儀: 一部 stub + 他 sub-section は docstring のみ).
  - 残: (i) `invariants_ne_bot` の proof, (ii) Thm 2.6 帰納本体 + GL(2,F) 計算 + MISSING_PAGE:29 補完, (iii) hchar 引数の `CharP F p` 型整合 (現状 `¬ CharP F q` 形 = ringChar 風), (iv) `Std.Commutative` vs `IsMulCommutative` 統一 (Sylow `P` も Group instance なので両方使える).
- **2026-05-24 (ralph-loop iter 1)**: `PGroupFixedVector.lean` 進化 — (i) helper `map_pow_orderOf_eq_one` (`(ρ g)^(orderOf g) = 1` as `Module.End F V`, `map_pow + pow_orderOf_eq_one + map_one`) sorry-free 追加, (ii) helper `exists_map_pow_prime_pow_eq_one` (p-群で `∃ k, (ρ g)^(p^k) = 1`, `IsPGroup.iff_orderOf` 経由) sorry-free, (iii) main `invariants_ne_bot` の **base case** (`¬ Nontrivial G` ⇒ `Subsingleton G` ⇒ `ρ g = 1 ∀ g` ⇒ `invariants = ⊤`) sorry-free. step case (`Nontrivial G` ⇒ `IsPGroup.center_nontrivial` 経由) 内に sorry 残, 次 iter で.
- **2026-05-24 (iter 2)**: `PGroupFixedVector.lean` step case 中段まで進捗 — 新 helper **3 件 sorry-free** 追加 + step case で `ker (ρ z - 1) ≠ ⊥` まで sorry-free 化:
  - **`charP_End_of_field`** (sorry-free): `[Nontrivial V]` の下で `CharP (Module.End F V) p` instance を `charP_of_injective_algebraMap` + `Algebra.algebraMap_eq_smul_one` + `Module.End.one_apply` + `smul_left_injective F (v ≠ 0)` で導出. 探索で `Module.Free F V + Nontrivial V ⇒ FaithfulSMul F V` instance ([`Mathlib/LinearAlgebra/FreeModule/Basic.lean:113`]) + `IsTorsionFree` 経由でも届くが本実装は ad hoc explicit injection.
  - **`exists_pow_sub_one_eq_zero`** (sorry-free): p-群 `G` + `[CharP F p]` + `[Nontrivial V]` 下で `∃ k, ((ρ g) - 1)^(p^k) = 0`. proof: `exists_map_pow_prime_pow_eq_one` で `(ρ g)^(p^k) = 1`, `sub_pow_char_pow_of_commute` ([`Mathlib/Algebra/CharP/Lemmas.lean:226`]) + `Commute.one_right` で `(ρ g - 1)^(p^k) = (ρ g)^(p^k) - 1^(p^k) = 0`. **重要**: `Module.End F V` は非可換環なので `sub_pow_char_pow` (CommRing 版) ではなく `_of_commute` 変種.
  - **`ker_ne_bot_of_pow_eq_zero`** (sorry-free): `f : Module.End F V` + `f^N = 0` + `[Nontrivial V]` ⇒ `LinearMap.ker f ≠ ⊥`. proof: `ker = ⊥ ⇒ Function.Injective f` (mathlib `LinearMap.ker_eq_bot`) ⇒ `Function.Injective (⇑(f^N))` を `Module.End.mul_apply` ベース induction で示し, `f^N v = 0` (∀v) と `v ≠ 0` で矛盾.
  - **main `invariants_ne_bot` step case**: `haveI : Nontrivial V` を `Submodule.exists_mem_ne_zero_of_ne_bot hV` 経由 instance 化 → `exists_ne (1 : Subgroup.center G)` で非自明 z 取得 → 新 helper 適用で `ker ((ρ z : Module.End F V) - 1) ≠ ⊥` まで sorry-free. **残 sorry**: (a) ker が G-invariant (z ∈ Z(G) で全 g と可換), (b) `G/⟨z⟩` 上の representation 構築 + |G/⟨z⟩| < |G| + 帰納仮定適用.
  - Build OK (2272 jobs, sorry 1 件のみ on `invariants_ne_bot` step case 内). 次 iter で残 sorry 2 段階に着手.
- **2026-05-25**: `PGroupFixedVector.lean` を sorry-free 化. `IsPGroup.invariants_ne_bot` と `IsPGroup.exists_fixed_vector_ne_zero` は完成済みで、§2F Thm 2.6 の fixed-vector dependency は解消.
- **2026-05-25**: mmd の `[MISSING_PAGE_FAIL:29]` は BG PDF p.29 を `pdftotext` で復元して解消. §2F の証明 sketch に q=p / q≠p / `G*` induction の分岐を反映済み.
- **2026-05-25**: §2F 用 helper を追加済み: `perm_fin_two_eq_one_of_odd_order`, `smul_fin_two_eq_self_of_odd_card`, `eq_one_of_pow_prime_pow_eq_one`, `unit_eq_one_of_pow_prime_pow_eq_one`. 現在の残 sorry は `odd_two_dim_abelian` と `odd_two_dim_sylow_abelian` の 2 件.
- **2026-05-25**: q=p 分岐用に scalar character helper 群 (`monoidHom_units_eq_one_of_isPGroup_charP` ほか) と、`C_G(W) ∩ C_G(V/W)` の可換性に対応する補題 `end_commute_of_fixed_on_submodule_and_quotient` / `submonoid_commutative_of_fixed_on_submodule_and_quotient` / `commutative_of_faithful_representation_fixed_on_submodule_and_quotient` / `subgroup_commutative_of_faithful_representation_fixed_on_submodule_and_quotient` を追加済み. さらに実際の subgroup `fixedOnSubmoduleAndQuotientSubgroup` とその可換性補題を追加済み.
- **2026-05-25**: p-subgroup の `W` / `V/W` action が scalar characters で書けるなら char p で `fixedOnSubmoduleAndQuotientSubgroup` に入る補題 `subgroup_le_fixedOnSubmoduleAndQuotientSubgroup_of_isPGroup_scalar_actions` と、faithful 版の可換性補題 `subgroup_commutative_of_isPGroup_scalar_actions` を追加済み. BG の「dim W = dim V/W = 1 なので scalar」段だけが次の橋渡し.
- **2026-05-25**: rank-one representation 用に `scalarMonoidHomOfFinrankEqOne`, units 版 `scalarCharacterOfFinrankEqOne`, および char p の p-group rank-one 表現自明性 `isPGroup_rank_one_representation_trivial_of_charP` を追加済み. 次はこれを実際の submodule `W` と quotient `V/W` 表現へ適用する.
- **2026-05-25**: `isPGroup_rank_one_submodule_action_trivial_of_charP`, `isPGroup_rank_one_quotient_action_trivial_of_charP`, `subgroup_le_fixedOnSubmoduleAndQuotientSubgroup_of_rank_one_subquotients`, `subgroup_commutative_of_rank_one_subquotients` を追加済み. q=p 分岐で rank-one subquotient まで到達すれば、`C_G(W) ∩ C_G(V/W)` 可換性までは Lean helper で閉じる.
- **2026-05-25**: 2 次元空間の非零 proper submodule から `dim W = dim V/W = 1` を出す
  `rank_one_subquotients_of_finrank_two` を追加済み. q=p 分岐は次に `W = C_V(K)`
  の非零性・proper 性・`G`-invariance を作れば、既存 rank-one subquotient helper へ接続できる.
- **2026-05-25**: q=p 分岐用の入口として
  `subgroup_commutative_of_finrank_two_invariant_submodule` を追加済み.
  非零 proper な invariant submodule `W` ができれば、2 次元性から rank-one
  subquotient helper へ直接接続して p-subgroup の可換性を得られる.
- **2026-05-25**: normal p-subgroup の fixed space を直接扱う
  `subgroup_commutative_of_normal_p_fixed_space_proper` を追加済み.
  `K ⊴ G`, `K` p-group, `C_V(K) ≠ V` から `IsPGroup.invariants_ne_bot`
  と `Representation.le_comap_invariants` を組み合わせて p-subgroup の可換性へ接続する.
- **2026-05-25**: faithful 表現で非自明 subgroup が全空間を点wise 固定できない補題
  `invariants_ne_top_of_faithful_subgroup_ne_bot` と、それを使う直結版
  `subgroup_commutative_of_nontrivial_normal_p_fixed_space` を追加済み.
  q=p 分岐は非自明 normal p-subgroup `K` を構成できれば p-subgroup 可換性まで閉じる.
- **2026-05-25**: rank-one submodule/quotient への scalar character が commutator を殺すことから、
  `commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_rank_one_subquotients`,
  2 次元版 `commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_finrank_two`,
  normal p-subgroup fixed-space 版
  `commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_nontrivial_normal_p_fixed_space`
  を追加済み. q=p 分岐の `G' ≤ C_G(W) ∩ C_G(V/W)` 接続は Lean helper として閉じた.
- **2026-05-26**: q=p 分岐で Sylow 包含へ進むため、
  `fixedOnSubmoduleAndQuotientSubgroup_normal_of_rank_one_subquotients`,
  `fixedOnSubmoduleAndQuotientSubgroup_normal_of_finrank_two`,
  `fixedOnSubmoduleAndQuotientSubgroup_normal_of_nontrivial_normal_p_fixed_space`
  を追加済み. さらに Sylow D + Sylow conjugacy + 正規性を組み合わせる
  `normal_pSubgroup_le_sylow` と、`G' ≤ N` を任意の Sylow 包含へ運ぶ
  `commutator_le_sylow_of_le_normal_pSubgroup` を追加した. 次の未解決点は
  `C = C_G(W) ∩ C_G(V/W)` が char p で p-subgroup になることを示し、
  `commutator_le_sylow_of_le_normal_pSubgroup C ...` へ渡すこと.
- **2026-05-26**: 上の未解決点を解消. `g ∈ C_G(W) ∩ C_G(V/W)` なら
  `n = ρ(g)-1` が `n^2 = 0` となり、char p で `(ρ(g))^p = 1`、faithful
  なら `g^p=1` となることから
  `fixedOnSubmoduleAndQuotientSubgroup_isPGroup_of_faithful` を追加した.
  これにより 2 次元 invariant submodule 版
  `commutator_le_sylow_of_finrank_two_invariant_submodule` と、q=p で使う
  fixed-space 版 `commutator_le_sylow_of_nontrivial_normal_p_fixed_space`
  まで Lean helper で閉じた. 現 frontier は **非自明 normal p-subgroup `K`
  の構成**: `subgroup_commutative_of_nontrivial_normal_p_fixed_space` で Sylow
  可換性、`commutator_le_sylow_of_nontrivial_normal_p_fixed_space` で `G' ≤ P`
  を得る. これらを theorem 結論形にまとめる endpoint
  `sylow_commutative_and_commutator_le_of_nontrivial_normal_p_fixed_space`
  も追加済み.
- **2026-05-26**: theorem 本体側で使いやすい reduction として
  `sylow_commutative_and_commutator_le_of_exists_nontrivial_normal_pSubgroup`
  を追加し、q=p は「非自明 normal p-subgroup の存在」まで落とした.
  さらに ambient group 自身が p-group の場合に `K = ⊤` を使う
  `sylow_commutative_and_commutator_le_of_isPGroup` も追加済み.
  次は determinant kernel `G* = G ∩ SL(V,F)` / `O_p(G*)` 側の構成を
  Lean で切れる小補題に分割する.

## TL;DR

**§2 は基本的な表現論モジュール**: operator group G に対する FG-加群の性質を 6 つの定理で系統化. 主な成果は:
- **Thm 2.1 (Schur 補題応用)**: 既約加群の自己準同型環と enveloping algebra の関係
- **Thm 2.3 (Fong–Swan)**: 可解群の絶対既約加群の次元は群の位数を割る
- **Thm 2.5**: extraspecial p-群と cyclic H の semidirect product における加群構造制約
- **Thm 2.6**: 奇数位数 2-次元加群 ⇒ G abelian or Sylow p-subgroup abelian (奇数位数限定)

**mathlib カバレッジ**: 基礎 API は使えるが、§2 の主結果は新規実装が多い. `RepresentationTheory.Basic`, `Maschke`, `FDRep` API は足場になり、§2F では p-群固定ベクトル補題を `OddOrder` 側で実装済み.

**下流被引用**: 監査実測で **8+ cites**. 形式化優先度は **高い**. ただし Prop 2.2 は Isaacs Ch.6 §6F Clifford 完成待ちで、Thm 2.3 は forward use 0 のため defer 可.

---

## §2 全 6 結果一覧

| # | 種別 | mmd 行 | statement 要約 (1–2 行) | 依存 | mathlib | 優先度 |
|---|------|--------|--------------------------|------|---------|--------|
| **2.1** | **Prop** | **598–612** | **(Schur の補題 + 既約 ↔ absolutely irreducible)** (a) M 既約, FG-自己準同型環 = F ⇔ M absolutely irreducible; (b) G faithful on M, HomFG(M,M) = F ⇒ HomF(M,M) = E(G); (c) F 有限体, K = HomFG(M,M) ⇒ K 体, M は KG-加群 | Schur, Jacobson Density | `FDRep.IsIrreducible`, `Schur.lemma` | ★ |
| **2.2** | Prop | 614–652 | (Clifford + cyclic quotient) H ◁ G, G/H cyclic, F 代数閉, M 既約 FH-加群, M ≅ M^x (x ∈ G) ⇒ (a) L 既約 FG-加群, M ⊆ L_H ⇒ L_H ≅ M; (b) H の表現 ⇒ G へ lift 可 | Clifford Thm 3.4.1, Jacobson | (Clifford 標準, 新規 statement) | ★ |
| **2.3** | **Lemma** | **655–668** | **(Fong–Swan)** G solvable, F 体, M absolutely irreducible FG-加群 ⇒ dim M \| \|G\| | Fong–Swan Thm 72.1 (高度な結果) | (characteristic 制約なし新規) | ★★ |
| **2.4** | Prop | 670–712 | (線型代数 + 既約性) V 体 F 上、g ∈ Aut V (有限位数), h-th root of unity ε ∈ F ⇒ eigenspace V_i 分解 + dim E_{i,t} 公式 + G-module structure (10 部技術定理) | (純粋線型代数) | (既存概念, 新規 statement) | ★ |
| **2.5** | **Thm** | **716–772** | **(extraspecial p-群と cyclic action)** P extraspecial p-group (order p^{2n+1}), H cyclic coprime, C_P(x)=Z(P) (x ∈ H^#), F char ∤ \|G\|, G = P ⋊ H ⇒ h \| (p^n ± 1); h ≠ p^n+1 ⇒ C_V(H) ≠ 0 (faithful irreducible V に対し) | Thm 5.5.4–5.5.5, Jacobson | (新規 statement, extraspecial 使用) | ★★ |
| **2.6** | **Thm** | **774–793** | **(奇数位数 + 2-次元)** G odd order, F field, V faithful FG-加群 (dim 2) ⇒ (a) char F ∤ \|G\| ⇒ G abelian; (b) char F = p \| \|G\| ⇒ Sylow p-subgroup abelian ∧ contains G' | (Thompson, induction + GL(2,q)) | (新規 statement) | ★★ |

---

## Thm 2.1: Schur 補題 + 既約 ↔ absolutely irreducible

### Statement (mmd L598–603)

```
G: 群, F: 体, M: 既約 FG-加群
─────────────────────────────────

(a) M absolutely irreducible ⟺ HomFG(M,M) = F

(b) G faithful on M, HomFG(M,M) = F ⇒ HomF(M,M) = E(G)

(c) F 有限体, K = HomFG(M,M) ⇒ K 体, M absolutely irreducible KG-加群
```

### 前提条件

- **M は既約 FG-加群**: すべての proper 部分加群は 0
- **absolutely irreducible**: F̄ (F の代数閉包) 上でも既約
- **E(G)**: G が V に faithful に作用する時の enveloping algebra (FG-加群 V を生成する F-部分代数)

### 証明梗概 (BG L604)

- **(a)**: char F = 0 or coprime to |G| ⇒ Gorenstein Thm 3.5.7; 一般的: Jacobson Density Thm (G Thm 3.6.2) 経由
- **(b)**: Jacobson Density + HomFG(M,M) = HomE(G)(M,M) の事実
- **(c)**: Schur 補題 (K division algebra), Wedderburn 有限体定理 ⇒ K は field

### 形式化対応 (mathlib)

**mathlib 側**:
- `FDRep` (有限次元 G-表現): `FDRep.IsIrreducible` 既に定義
- Schur 補題: `Module.Schur.lemma` の variant
- Jacobson Density: mathlib 未実装 (phase 1 での Isaacs 참照 형식화 필요)

**形式化ロードマップ**:
```lean
-- Phase 1 Isaacs Ch.3 から Jacobson Density import
theorem thm2_1_a {M : FDRep F G} (hM : M.IsIrreducible) :
    M.IsAbsolutelyIrreducible ↔ (M.End).ker = ⊥ := by
  -- Jacobson Density Thm via Isaacs
  sorry

-- (b) は (a) + EndAlgebra 結合
-- (c) は 有限体上 division algebra ⇒ field (mathlib basic)
```

---

## Thm 2.3: Fong–Swan — 可解群の既約加群次元

### Statement (mmd L655–657)

```
G: 可解群, F: 体, M: absolutely irreducible FG-加群
──────────────────────────────────────────────
dim M | |G|
```

### 背景

**Fong–Swan Thm 72.1** (高度な結果): 可解群の既約表現次数は群の位数の因子。

### 証明梗概 (BG L659–668)

**帰納法** (|G| について):
1. H ◁ G, prime index p を取得 (§1 Lemma 1.1)
2. L ⊆ M_H 既約 ⇒ dim L | |H| (帰納仮説)
3. **Case 1**: L ≅ L^x (x ∈ G - H) ⇒ Thm 2.2 より L = M_H ⇒ dim M | p · |H| = |G|
4. **Case 2**: L ≁ L^x ⇒ M_H = L ⊕ L^x ⊕ ⋯ ⊕ L^{x^{p-1}} (pairwise nonisomorphic)
   - dim M = p · dim L | p · |H| = |G|

### 形式化対応

**mathlib 側**: 
- **既約性判定**: `IsIrreducible` (既存)
- **制限 (restriction)**: `RestrictScalars` 経由 (既存)
- **次数制約**: 新規 lemma 必要

**形式化難度**: **高い** (Clifford theorem 活用, 帰納構造). Fong–Swan 原理自体は Isaacs references から参照.

```lean
lemma fong_swan {M : FDRep F G} (hM : M.IsAbsolutelyIrreducible) 
    (hsolv : IsSolvable G) :
    FiniteDimensional.finrank F M ∣ Nat.card G := by
  -- BG L659 の帰納法スケッチ
  sorry
```

---

## Thm 2.5: Extraspecial p-群と Cyclic Action

### Statement (mmd L716–722)

```
P: extraspecial p-group (order p^{2n+1})
H: cyclic group, |H| = h, h ⊥ p
G = P ⋊ H (semidirect product)
Condition: ∀x ∈ H^#, CP(x) = Z(P)

F: 체 with char F ∤ |G|
V: faithful, irreducible FG-加群
──────────────────────────────────

⇒ h | (p^n - 1) or h | (p^n + 1)

If h ≠ p^n + 1, then CV(H) ≠ 0
```

### 前提条件

- **extraspecial p-group**: 中心 Z(P) = p, P/Z(P) elementary abelian, |Z(P)| = p
- **coprime action**: (|H|, p) = 1, faithful conjugation H → Aut P
- **条件 C_P(x) = Z(P)**: H の非自明元による固定点は中心のみ

### 證明梗概 (BG L726–772)

**主要ステップ**:
1. (L726–740) V̄ = F̄ ⊗_F V (代数閉体拡張)
2. W ⊆ V̄ irreducible G-submodule, M ⊆ W irreducible P-submodule
3. P は W に faithful に作用 (L743–744, C_V(Z(P)) = 0 から)
4. Thm 5.5.4–5.5.5 (extraspecial 表現): faithful irreducible P-表現 ⇒ dim M = p^n, P はモジュール M を faithful に作用
5. **Prop 2.4 (線型代数)**: E(P) = End_F(V), H 作用下での eigen-space 分解
   - E は H の作用下で "principal module" と "regular module" の直和 (L770)
   - Prop 2.4(j), (k) 条件チェック ⇒ h | (p^n ± 1)
6. (L772) Prop 2.4(k): C_V(H) = 0 ⟺ h = p^n + 1

### 形式化対応

**mathlib 側**:
- **extraspecial p-group**: 新規定義 (Phase 1 にて可能性)
- **Thm 5.5.4–5.5.5**: Isaacs 참조 (extraspecial representation 理論)
- **Prop 2.4 (線型代数)**: **テクニカル** — eigen-space 分解と H-module 構造の相互作用

**形式化難度**: **非常に高い** (extraspecial 표現론, 線型代数テクニック, 複雑な帰納).

```lean
theorem thm2_5 {P : Subgroup G} (hP : IsExtraspecial p P) 
    {H : Subgroup G} (hH : IsCyclic H) (hcoprime : (H.card, p) = 1)
    (haction : ∀ x ∈ H, x ≠ 1 → Centralizer P x = Subgroup.center P) :
    H.card ∣ p ^ n - 1 ∨ H.card ∣ p ^ n + 1 := by
  -- Prop 2.4 (j), (k) + extraspecial 理論
  sorry
```

---

## Thm 2.6: 奇数位数 2-次元加群 ⇒ Structure

### Statement (mmd L774–778)

```
G: finite group of odd order
F: field
V: faithful FG-加群, dim V = 2

──────────────────────────────────

(a) char F ∤ |G| ⇒ G abelian

(b) char F = p | |G| ⇒ Sylow p-subgroup abelian ∧ contains G'
```

### 証明梗概 (BG L779–793 + PDF p.29 補完)

**帰納法** (|G| について):

**Step 1: 前処理**
- G ⊆ GL(V, F) と見做す
- G* = G ∩ SL(V, F)
- F を代数閉体に拡張 (可)

**Step 2: p-element と固定点**
- p = char F の場合分け
- K = Ω₁(Z(O_q(G*))) (K elementary abelian q-group, q | |G|, K ◁ G)

**Step 3a: q = p の場合**
- W = C_V(K) (K-不変部分加群)
- G Lemma 2.6.3: W ≠ 0
- dim V = 2, G faithful on V ⇒ dim W = 1 (L785–786)
- dim W = dim V/W = 1
- W は G-invariant
- C = C_G(W) ∩ C_G(V/W) は elementary abelian p-group
- char F = p では Fˣ の p-power torsion は 1 のみなので, C は G の全 p-element を含む
- Fˣ は abelian なので C は G' も含む
- よって (b)

**Step 3b: q ≠ p の場合**
- Maschke + K abelian + F algebraically closed から V = W₁ ⊕ W₂
  (two one-dimensional FK-modules)
- x ∈ K# の eigenvalues λ₁, λ₂ は λ₁λ₂ = det x = 1 かつ x odd order なので distinct
- x が固定する one-dimensional subspace は W₁, W₂ のみ
- K ◁ G なので G は W₁, W₂ を固定または交換する; |G| odd なので交換できず固定
- よって G は abelian p'-group, (a) に帰着

**Step 4: G* ≠ 1 の一般処理**
- G* が p-group なら O_p(G*) ≠ 1 で Step 3a
- そうでなければ q ≠ p の Sylow Q ≤ G* と H = N_{G*}(Q) を取り, O_q(H) ≠ 1
- Step 3b より H abelian, したがって Q は G* で normalizer の中心
- Burnside (Thm 1.18) で G* は Q の normal complement N を持つ
- N = 1 なら O_q(G*) = Q; N ≠ 1 なら induction で O_r(N) ≠ 1, hence O_r(G*) ≠ 1
- どちらも Step 3 に帰着

**Step 5: G* = 1**
- determinant により G ↪ Fˣ, よって G は abelian p'-group

### 形式化対応

**mathlib 側**:
- **GL(2, F), SL(2, F)**: 基本 linear group (既存)
- **odd order 仮定**: `Odd G.card` (既存)
- **Sylow subgroup**: `Subgroup.Sylow` (既存)
- **Lemma 2.6.3 (Gorenstein)**: G の代数的補助定理 (mathlib 未実装, Phase 1 Isaacs 参照)

**形式化難度**: **高い** (induction + case split, GL(2,q) embedding, Sylow characterization).

```lean
theorem thm2_6 {G : Type*} [Group G] [Fintype G] [Odd G.card]
    (V : Type*) [AddCommGroup V] [Module F V] [Module G V]
    (hfaithful : FaithfulSMul G V) (hdim : FiniteDimensional.finrank F V = 2) :
    (CharP F 0 ∨ ¬ Nat.Prime.dvd (CharP.char F) G.card) → IsCyclic G ∧ IsAbelian G := by
  -- induction + GL(2, F) argument
  sorry
```

---

## Thm 2.2 + Prop 2.4 (Technical Lemmas)

### Thm 2.2: Clifford + Cyclic Quotient

**目的**: H ◁ G cyclic quotient G/H 下で、M ≅ M^x (共役加群が isomorphic) なら M_H (restrict to H) is unique, lift 可.

**mathlib 対応**: Clifford 理論 (`Module.restrictScalars`) 既存、new statement として形式化可.

### Prop 2.4: Eigenspace Decomposition

**目的**: g ∈ Aut V (有限位数), ε ∈ F (primitive h-th root of unity) → eigenspace V_i = {v | vg = ε^i v} 分解 + End(V) の H-module 構造.

**形式化対応**: **線型代数テクニック** (basis 変更、行列ブロック分解). 10 部性質中 (j), (k) が Thm 2.5 の鍵.

---

## mathlib カバレッジ評価

| 結果 | mathlib 対応 | 新規実装 | 難度 |
|-----|------------|---------|------|
| **Thm 2.1** (Schur + 既約) | `FDRep.IsIrreducible`, Schur lemma basic | Jacobson Density variant | 中 |
| **Thm 2.2** (Clifford + cyclic) | Clifford basic, `RestrictScalars` | new statement (Prop 2.2) | 中 |
| **Thm 2.3** (Fong–Swan) | 既約性, 次数制約 new | **Fong–Swan 帰納** | 高 |
| **Prop 2.4** (eigenspace) | 線型代数基本 | **10 部技術定理** | 非常に高 |
| **Thm 2.5** (extraspecial) | 未実装 (extraspecial 理論新規) | **extraspecial 加群論** | 非常に高 |
| **Thm 2.6** (odd 2-dim) | GL(2,F), Sylow, odd order | **induction + GL embedding** | 高 |

**総評**: **Thm 2.1–2.2 は mathlib 基礎活用で中程度、Thm 2.3–2.6 は新規技術理論で高–非常に高難度**.

---

## 下流被引用

### 明示的引用 (2026-05-23 audit)

統合 doc: [`notes/meta/bg_phase2a_wave1_audit_2026_05_23.md`](../meta/bg_phase2a_wave1_audit_2026_05_23.md).

実測:
- §3: Prop 2.1, Prop 2.2, Thm 2.5, Thm 2.6 の引用が集中.
- §4: Lem 4.17 で §2 を参照.
- §15: Thm 15.7 で §2 を参照.
- App.A: Thm A.1 proof で Thm 2.6 を参照.

**現在判断**: §2 は optional ではなく Phase 2a 第 1 波の前提節. ただし Lem 2.3 (Fong–Swan) は forward use 0 なので、§2 内では他結果より後回しでよい.

---

## Phase 2a 形式化着手順

### 優先度判定

1. **Thm 2.6 (odd 2-dim)** ★★★ — §3/App.A で直接使用. 現在 active. fixed-vector dependency と p-power torsion helper は完成、残りは 2 つの theorem stub.
2. **Prop 2.4 (eigenspace)** ★★★ — Thm 2.5 の前提になる線型代数節.
3. **Prop 2.1 (Schur + 既約)** ★★ — mathlib 基礎 API を活用できるが、Jacobson density 周辺は要注意.
4. **Thm 2.5 (extraspecial)** ★★★ — §3 で使用. extraspecial 理論と Prop 2.4 に依存する高難度枠.
5. **Prop 2.2 (Clifford + cyclic)** ★★ — §3 で使用するが、Isaacs Ch.6 §6F Clifford 完成待ち.
6. **Thm 2.3 (Fong–Swan)** ★ — forward use 0. 後回し.

### 推奨スケジュール

**§2 は Phase 2a 必須**:
- **短期 path**: Thm 2.6 の dependency を先に固める (`PGroupFixedVector`, odd action helper, characteristic-p scalar helper).
- **中期 path**: Prop 2.4 → Thm 2.5 → Prop 2.1.
- **blocker path**: Prop 2.2 は Isaacs Ch.6 §6F Clifford 完成後に本実装.

**推奨**: 現在は Thm 2.6 を続行. full theorem proof の前に、再利用できる小補題を 1–2 個ずつ sorry-free で積む.

---

## 未解決 / TODO

| 項目 | 状態 | 확인先 |
|------|------|--------|
| **Fong–Swan citation** | BG L657 "Fong and Swan [5, Theorem 72.1]" — citation 설정 필요 | BG references 재확인 |
| **Lemma 2.6.3 (Gorenstein)** | 解消: `OddOrder/GroupTheory/RepresentationTheory/PGroupFixedVector.lean` の `IsPGroup.invariants_ne_bot` / `exists_fixed_vector_ne_zero` で再構築済み | Lean build 済み |
| **MISSING_PAGE:29 content** | 解消: BG PDF p.29 を `pdftotext` で復元し、§2F proof sketch に反映済み | PDF p.29 |
| **Prop 2.4(j)–(k) statement** | Thm 2.5 증명에서 핵심 but verbose. statement 정확성 재확인 | BG L696–712 정독 |
| **mathlib `Maschke` API** | §2 에서 언급 가능성 (L1.20에서 phase 1 참조) | `Maschke.completely_reducible` 확인 |

---

**작성**: 2026-05-22

**출처**:
- `references/bg/local-analysis.mmd` lines 586–794 (§2 완문)
- `references/bg/bg.pdf` pp. 9–16 (visual confirm)
- `notes/bg/_overview.md` (BG overview)
- `notes/isaacs/ch03_hall.md`, `notes/isaacs/ch07_thompson.md` (참조)

**次ステップ**:
- q=p 分岐で非自明 normal p-subgroup `K` を作る段を小補題化する.
- その後、p-elements / Sylow p-subgroup が `fixedOnSubmoduleAndQuotientSubgroup` に入るところへ接続する.
- その後、determinant / `G*` 分岐のうち、Lean で切れる小補題へ分解する.

## 2026-05-26 進捗ログ: determinant kernel `G*`

- `S02_Representations.lean` に `representationToGeneralLinearGroup`,
  `determinantCharacterOfRepresentation`, `determinantKernelSubgroup` を追加.
- `G* = ker(det ∘ ρ)` は normal, かつ `G' ≤ G*` まで sorry-free.
- `G* = ⊥` なら determinant character が `G ↪ Fˣ` になり `G` が abelian,
  という BG Thm 2.6 の最終分岐を `commutative_of_determinantKernel_eq_bot`
  として切り出し済み.
- q=p theorem-facing endpoint として `G* = ⊥` 分岐と
  `G*` が非自明 p-group の分岐を
  `sylow_commutative_and_commutator_le_of_determinantKernel_bot_or_pGroup`
  に集約済み.
- `O_p(G*) ≠ ⊥` なら Ch.1 `opCore` の characteristic-in-normal を使って
  `G` の非自明 normal p-subgroup を作る bridge
  `sylow_commutative_and_commutator_le_of_determinantKernel_opCore_ne_bot`
  も sorry-free.
- 次 frontier は BG proof の group-theoretic dichotomy:
  `G* ≠ ⊥` から適切な `q` で `O_q(G*) ≠ ⊥` を得る段.
