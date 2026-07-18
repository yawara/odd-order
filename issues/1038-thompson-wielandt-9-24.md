---
id: 1038
slug: thompson-wielandt-9-24
title: "Theorem 9.24 general Thompson-Wielandt (+ 9.23)"
created: 2026-07-18
---

# Theorem 9.24 general Thompson-Wielandt (+ 9.23)

## 背景

Isaacs §9C の主結果 (p. 283, mmd L5155)。§9C の tool 群は 2026-07-18 に全 landed:
- 9.25 (`LayerRestriction.lean` `map_layer_eq_layer_of_fitting_eq_bot`): F(G)=1 ⇒ E(G)=E(H)。
- 9.26/9.27 + O^p core (`PResidual.lean`): O^p(SP)=O^p(S) / O^p(S)◁G。
- 9.18 (`SubnormalSocle.lean`), 9.8 (`GeneralizedFitting.lean`) も既 landed。

9.24 の deps は全て揃っている (9.24 は 9.27 を使い 9.26 は不使用)。

## 9.24 の statement (要 core_H(D) infra)

`H, K` 相異なる部分群, `D = H∩K`。仮説: **D の非自明部分群は H または K を真に含む
どの部分群にも normal でない**。`M = core_H(D)`, `N = core_K(D)`, `E = M∩N`,
`U = core_H(E)`, `V = core_K(E)`。結論: **ある素数 p で U または V が p-群**。

`core_H(D)` = D に含まれ H に normal な最大部分群 = `((D.subgroupOf H).normalCore).map H.subtype`
(mathlib `Subgroup.normalCore` の相対版; transport infra を新設)。

## 進捗 (2026-07-18)

**landed groundwork (全 sorry-free/axiom-clean, `ThompsonWielandt.lean` / `PResidual.lean`)**:
- `relCore H D` (core_H(D)) infra: `relCore_le` (≤D), `relCore_le_left` (≤H),
  `le_normalizer_relCore` (H≤N_G(core)), `le_relCore` (最大性)。
- `NoNormalInSupergroup H K D` (9.24 の仮説 predicate)。
- `normalizer_eq_left/right_of_noNormal`: 仮説から nonidentity N≤D が H(resp K) に normal
  なら N_G(N)=H(resp K)。proof の「H=N_G(U^∞)」deduction 用。
- `pResidual_eq_bot_iff_isPGroup`: O^p(U)=⊥ ⟺ U は p-群 (Case 2 結論用)。

## ⚠ proof body の要検討事項 (原文精読で確定した subtlety)

書籍 proof (p.283–284) を精読して判明した、着手前に解決すべき点:

1. ~~**normal / subnormal**~~ → **✅ 解決 (2026-07-18)**。下記「subtlety 1 の決着」参照。
2. **nested transport**: Case 1 は 9.18/9.25/Fitting を `↥H`,`↥K`,`↥D` 内で適用し
   ambient に戻す必要 (E(↥H) と E(D) の関係、F(↥H)=⊥ from F(H)=1 等)。深い多段 subtype。
   → `O^p` 側は ambient 化済 (`pResidualOf`)。`layer`/`nilpotentResidual` 側の
   transport が Case 1 の残作業。
3. **Fitting**: F(H)=1 ⇔ Fitting ↥H = ⊥; nilpotent normal ≤ Fitting (Ch01) を ↥H で。

## subtlety 1 の決着 (2026-07-18, landed)

**書籍は誤り (行間でなく非自明なギャップ)**: p. 284 は「`V ◁ K` ゆえ `V ◁ M ◁ H`,
so `V ◁ H`」と書くが、`V ◁ M ◁ H` は **subnormal であって normal ではない**
(subnormal から normal は一般に従わない)。同じ jump は後段の `U^k ◁ N ◁ D` にもある。

- **Case 1** (9.18 適用) は 9.18 自体が subnormal 版なので書籍のままで **OK**。
- **Case 2** (9.27 適用) は normal 版では足りず、**subnormal 版 9.27 が真に必要**。
  → 本 repo で証明した (defect 2 で足り、subnormal 帰納は不要):

  `le_normalizer_pResidualOf_of_subnormal_two`: `S ◁ T ◁ G`, `P ◁ G` が p-群
  ⇒ `P ≤ N_G(O^p(S))`。証明は `G₀ = S ⊔ P` 内での `S` の normal closure `R` を取り、
  `S ≤ R ≤ T` から `S ◁ R`、Dedekind で `R = S ⊔ (R⊓P)`、`R⊓P ◁ R` は p-群 ゆえ
  Lemma 9.26 (ambient 版 `pResidualOf_sup_eq`) で `O^p(R) = O^p(S)`;
  `R ◁ G₀ ⊇ P` ゆえ `P ≤ N_G(R) ≤ N_G(O^p(R))`。

  ⚠ Dedekind は**要素計算**で証明した — `Subgroup G` の束は一般に modular でなく
  (mathlib の `IsModularLattice` instance は **CommGroup 限定**)、効いているのは
  `P ◁ G` から `S ⊔ P = S·P` (集合の積) になること。

**併せて landed した `O^p` の ambient API** (`pResidualOf p S : Subgroup G`):
`nilpotentResidual` と同じ ambient 設計。`map_pResidualOf` (同型同変性 —
proof 後段の `O^p(U^k) = X^k` に必要)、`normalizer_le_normalizer_pResidualOf`
(`N_G(S) ≤ N_G(O^p(S))`)、`map_subtype_pResidualOf_subgroupOf` (↥R ↔ ambient)、
`pResidualOf_eq_bot_iff_isPGroup`、`pResidualOf_sup_eq` (9.26 ambient)。
`isPGroup_quotient_comap` / `comap_mem_pQuotientNormals` は `G ≃* G` から
一般の `e : G ≃* K` へ一般化。

## やること

- [x] `core_H(D)` (relative normalCore) の infra。
- [x] 仮説 predicate + N_G 補題 + pResidual_eq_bot_iff。
- [x] 上記 subtlety 1 (subnormal-9.27) を確定 → **書籍の誤りと判明・subnormal 版を証明**。
- [x] `O^p` の ambient API (`pResidualOf` + 同変性 + 9.26 ambient 版)。
- [x] 記号 `E`/`U`/`V` (`thompsonWielandtCore H K` = `E`) と subnormal chain `V ◁ M ◁ H`。
- [x] **Case 2 の Step A**: `O_p(H) ≤ N_G(O^p(V))`
      (`opiCoreInG_le_normalizer_pResidualOf_relCore`)。`O_p` は既存の shared infra
      `GroupTheory.opiCoreInG {p} H` を使用 (import 経路 Ch03 → Ch09 で cycle なし)。
- [x] **Case 2 完成 (2026-07-18)** — `pResidualOf_relCore_eq_bot_or`:
      `O_p(H) ≠ 1` ⇒ `O^p(U) = 1` ∨ `O^p(V) = 1`。Step A–F すべて sorry-free。
      副産物の shared infra: `map_normalizer_mulEquiv` (`N_G(A^g) = N_G(A)^g`、mathlib 不在)。
      ⚠ 書籍の subnormal→normal jump は **2 箇所**あった (`V ◁ H` と `U^k ◁ D`);
      両方とも subnormal 版 Cor 9.27 で埋まる。
- [x] **Thm 9.24 完成 (2026-07-18)** — `thompsonWielandt`:
      `∃ p, p.Prime ∧ (IsPGroup p U ∨ IsPGroup p V)`。2 ケース統合済み。
      `exists_prime_opiCoreInG_ne_bot` (`F ≠ 1 ⇒ ∃ p, O_p ≠ 1`、
      `fitting_eq_iSup_primeFactors` + `Ch04.oPiCore_singleton_eq_opCore` 経由) で
      Case 2 の入口を作った。
- [x] **Case 1 完成 (2026-07-18)** — `relCore_eq_bot_or_of_fitting_eq_bot`。
      補助: `layerInG_le_inf_of_fitting_eq_bot` (`E(H) ≤ D`)、
      `layer_ne_bot_of_fitting_eq_bot` (F=1 ⇒ E≠1、Thm 9.8 経由)、
      `nilpotentResidual_ne_bot_of_fitting_eq_bot` (U ◁ H 非自明 ⇒ U^∞ ≠ 1)。
- [x] ~~Case 2 の残り~~ (完了; 手順は下記に保存):
      - `X = O^p(U) ≠ ⊥`, `Y = O^p(V) ≠ ⊥` と仮定 → `N_G(X) = H`, `N_G(Y) = K`
        (`normalizer_eq_left/right_of_noNormal`; `X ◁ H` は `U ◁ H` + `O^p` char)。
      - Step A で `P = O_p(H) ≤ N_G(Y) = K` ⇒ `P ≤ D`, `P ◁ D`。
      - `k ∈ K` に対し `U^k ◁ N ◁ D` に**同じ相対版 9.27** を `D` を ambient として適用
        → `P ≤ N_G(X^k) = H^k` ⇒ `P ≤ D^k` (全 `k`) ⇒ `P ≤ core_K(D) = N`
        (`le_relCore`) ⇒ `O_p(H) ≤ O_p(N) ≤ O_p(K)`。
        ※ `O^p(U^k) = X^k` は `map_pResidualOf` (同変性) で得る。
      - `H`/`K` を入れ替えて `O_p(K) ≤ O_p(H)` ⇒ 等号 ⇒ `P ◁ H` かつ `P ◁ K`,
        `P > 1` ⇒ `H = N_G(P) = K` 矛盾。
- [ ] **Case 1** (`F(H)=F(K)=1`) — ここが次の frontier (subtlety 2)。必要な infra を
      2026-07-18 に調査済み:
      - **ambient `layer`** `layerInG H := (layer ↥H).map H.subtype` を新設する
        (repo 全体に ambient layer は**存在しない** — 確認済み)。`O^p` で作った
        `pResidualOf` と同じ設計・同じ transport 補題群 (`map_subtype_layer_subgroupOf` 等)。
      - **ambient fitting は不要**: 9.25 (`map_layer_eq_layer_of_fitting_eq_bot`) の仮説は
        `Ch01.fitting G = ⊥` の形なので、Case 1 の仮説を `Ch01.fitting ↥H = ⊥` (= F(H)=1)
        と書けばそのまま噛み合う。
        ⚠ BG に `fittingInG` (S08_CenterFittingOpcore) があるが **BG は Isaacs の下流**
        なので import 不可。将来 `GroupTheory/SubgroupInAmbient.lean` (ambient 構成の
        canonical home) へ寄せる consolidation は別 issue 候補。
      - `nilpotentResidual` は**既に ambient 値**で `map_nilpotentResidual` (同変性) と
        `map_subtype_nilpotentResidual_subgroupOf` (transport) も既存 → 追加不要。
      - 9.18 は `V.subgroupOf H` が `↥H` で subnormal であること (`V ◁ M ◁ H` の chain を
        `IsSubnormal` で構成) が要る。normalizer の ambient ↔ subtype 往復は
        本 session で作った `map_subtype_le_normalizer_map_subtype` /
        `subgroupOf_le_normalizer_subgroupOf` が使える。
      - Case 1 の筋: `U`,`V` は nilpotent でない (`U ◁ H` nilpotent なら `U ≤ F(H) = 1`)
        → `U^∞`,`V^∞` ≠ 1 → `N_G(U^∞) = H`, `N_G(V^∞) = K` → 9.18 で `E(H) ≤ N_G(V^∞) = K`
        → `E(H) ≤ D` → 9.25 で `E(H) = E(D) = E(K)` → `H = N_G(E(H)) = K` 矛盾。
- [ ] 9.24 proof の組み立て (書籍 p. 283–284, ~40 行, 2 ケース):
      - F(H)=F(K)=1: E(H),E(K)>0, 9.18 で E(H)⊆N_G(V^∞)=K, 9.25 で E(H)=E(D)=E(K),
        H=N_G(E(H))=K 矛盾 → U or V trivial (p-群)。
      - F(H)>1 (or F(K)): O_p(H)=P>1, 9.27 で P normalizes O^p(V)=Y, cores で
        P ⊆ O_p(H)=O_p(K), H=N_G(P)=K 矛盾。
      使用: F*/9.8 (C_G(F*)⊆F*), 9.18, 9.25, 9.27, `core`, `O_p` (repo `opPi`), N_G。
- [ ] **Theorem 9.23** (Thompson corefree bound) — 進行中 (2026-07-18)。

  **landed**:
  - strand B (setup) 完了: `isCoatom_map_conj` / `normalizer_eq_self_of_corefree_maximal` /
    `noNormalInSupergroup_of_corefree_maximal` (H≠K 不要の一般形) /
    `map_conj_ne_of_corefree_maximal` (`H^g ≠ H`)。
  - n!-定理の相対形: `relCore_relIndex_dvd_factorial` (`|H:core_H(D)| ∣ |H:D|!`)、
    不等式形 `relCore_relIndex_le_factorial`、
    `relCore_relIndex_le_factorial_pred` (`|D:core_H(D)| ≤ (|H:D|-1)!`)。

  **strand A (index 連鎖) も完了 (2026-07-18)**:
  `thompsonWielandtCore_relIndex_le` (`|H:E| ≤ a!·b!`)、
  `relCore_thompsonWielandtCore_relIndex_le` (`|H:U| ≤ (a!b!)!`)、
  `opiCoreInG_relIndex_le_of_isPGroup` (`|H:O_p(H)| ≤ |H:U|`)。
  ヘルパ: `relIndex_ne_zero`, `factorial_pred_mul_self`。
  ⚠ `Subgroup.relIndex_inf_le` は**全て implicit 引数** (`_ _ _` は不可)、
  `relIndex_mul_relIndex` は**部分群 3 つが explicit** — 逆なので注意。

  ### ⚠ 残る唯一の障害: 9.24 の `V`-branch をどう `H` の bound に落とすか

  9.24 の結論は `IsPGroup p U ∨ IsPGroup p V`。`U`-branch は `U ◁ H` なので
  そのまま `|H:O_p(H)| ≤ |H:U| ≤ (a!b!)!` で終わる。**`V`-branch が問題**:
  `V ◁ K` であって `V ◁ H` ではない (Case 2 で判明した通り `V ◁ M ◁ H` の subnormal 止まり)。
  書籍は「`H` と `K` は同型だからどちらでもよい」の一言で済ませている箇所。

  形式化の選択肢は 2 つ (どちらも未着手):

  **(route 1) 共役同変性で `|K:O_p(K)| = |H:O_p(H)|` に読み替える**
  - `oPiCore` の同型同変性 `(oPiCore π A).map e = oPiCore π B` (`e : A ≃* B`) を作る。
    `oPiCore π G = ⨆ H : {H // H.Normal ∧ IsPiGroup π H}, H.val` なので、
    証明の形は本 session で作った `map_layer_mulEquiv` / `map_pResidual_mulEquiv` と同一
    (`map_le_iff_le_comap` → `iSup_le` → 各元が像でも条件を満たす → `e.symm` で逆向き)。
  - その ambient 版 `opiCoreInG π (H.map (conj g)) = (opiCoreInG π H).map (conj g)`。
  - 加えて共役が `relIndex` を保つこと。
  - 置き場所: `oPiCore` 版は Ch03 (定義元)、ambient 版は `GroupTheory/SubgroupInAmbient.lean`。
    どちらも共有 leaf なので 9000 issue で claim してから着手するのが安全。

  **(route 2) subnormal `p`-部分群は `O_p` に入る (Wielandt) を使う**
  - `V ◁◁ H` かつ `V` が `p`-群 ⇒ `V ≤ O_p(H)` が言えれば、`|H:O_p(H)| ≤ |H:V|` となり、
    `|H:V| = |K:V|` (共役ゆえ `|H| = |K|`) から `≤ (a!b!)!`。
  - この定理が repo/mathlib にあるか未調査。無ければ route 1 より重い。
  - 利点: 共役同変性を一切作らなくてよい。

  → **まず route 2 の既存性を grep で確認し、無ければ route 1** が推奨。

  **旧メモ (strand A 用、参考)** — 使った mathlib 補題:
  - `Subgroup.relIndex_mul_relIndex (H K L) (hHK) (hKL) : H.relIndex K * K.relIndex L
    = H.relIndex L` (⚠ 部分群 3 つが**明示引数**、`_ _ _` が要る)
  - `Subgroup.relIndex_inf_le : (H ⊓ K).relIndex L ≤ H.relIndex L * K.relIndex L`
  - `Subgroup.relIndex_dvd_of_le_left (hHK : H ≤ K) : K.relIndex L ∣ H.relIndex L`
    (→ `U ≤ O_p(H)` から `|H:O_p(H)| ∣ |H:U|`、`Nat.le_of_dvd` で不等式へ)
  - relIndex ≠ 0 は `Subgroup.index_ne_zero_of_finite` ∘ `index_eq_zero_of_relIndex_eq_zero`
  - `Nat.factorial_le` (単調性)

  手順: `|D:E| ≤ |D:M|·|D:N| ≤ (a-1)!(b-1)!` (relIndex_inf_le) →
  `|H:E| = |D:E|·|H:D| ≤ (a-1)!(b-1)!·a = a!(b-1)! ≤ a!b!` →
  `|H:U| ≤ (|H:E|)! ≤ (a!b!)!` (n!-定理 + factorial 単調) →
  `U` が p-群 + `U ◁ H` ⇒ `U ≤ O_p(H)`
  (`GroupTheory.le_opiCoreInG_of_normal_of_isPiSubgroup`; `IsPGroup → IsPiSubgroup {p}`
  の橋渡しが要るか要確認) ⇒ `|H:O_p(H)| ≤ (a!b!)!`。

  **a = b = m の根拠**: `|K:D| = |H^g|/|D| = |H|/|D| = |H:D|` (共役ゆえ `|H^g| = |H|`)。
  よって bound は `(m!·m!)! = ((m!)²)!`。

  最後に `thompsonWielandt` + strand B を合成。`H = ⊥` の場合は
  `|H:O_p(H)| = 1` で自明に成立するので先に場合分けする
  (`normalizer_eq_self_of_corefree_maximal` が `H ≠ ⊥` を要求するため)。

## 完了条件

9.24 + 9.23 を sorry-free/axiom-clean で landing。full build green + AxiomsCheck OK。

## 参照

- references/isaacs/finite-group-theory.mmd L5151–5188 (§9C); PDF p. 283–284
- OddOrder/Isaacs/Ch09_MoreSubnormality/{PResidual,LayerRestriction,SubnormalSocle,
  GeneralizedFitting}.lean
- notes/isaacs/ch09_more_subnormality.md §9C 節
