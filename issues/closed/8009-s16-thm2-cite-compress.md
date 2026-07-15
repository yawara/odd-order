---
id: 8009
slug: s16-thm2-cite-compress
title: "BG Thm II 現 statement の 3 sorry を cite-compress (TI helper + signature fix)"
created: 2026-06-15
---

# BG Thm II 現 statement の 3 sorry を cite-compress (TI helper + signature fix)

## 背景

`theoremII_tame_embedding` ([S16_MainResults.lean:458](../OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults.lean)) は
本体大半が cite 済 (Thm D(4) + Prop 16.1) で、**残 sorry 3 本**:

- **L483 `hDsub : D ⊆ sigmaSharp M`** — `D = {x∈X | x≠1, C_G(x)⊄M}` が `M_σ#` に入る。
- **L497 conjunct 1 (Ti)** — `X` の2元が `G`-共役なら `M`-共役。
- **L522 uniqueness** — `C_G(x)` の極大 overgroup が一意 (Type I/II の `∃! N` を `N₀` に pin)。

**本 issue = 現 (lossy) statement を sorry-free 化する cite-compress** で、issue 8005 の
「落ちた構造句 (Tii)/(Tiii) の faithful 復元」とは**別タスク**(8005 は Pf consumer 待ちで defer)。
両者は両立: 本 issue で現 statement を閉じ、8005 で将来 statement を拡張。

## 根本原因: Thm II は under-hypothesized (signature fix が前提)

現 signature は `{M K U : Subgroup G}` で `K U` が**自由変数**。よって `ASet M U` /
`A0Set M K` は BG の `A(M)` / `A₀(M)` を指していない (任意の `U,K` に対する主張 = 不忠実)。
**Thm B(5) / Thm C(9)(repo では Thm C conjunct 10 = `IsTISubset (A0Set M K \ ASet M U) M`) を
cite するには `K,U` を Hall 因子に pin する必要**がある。

## 進捗 (2026-06-15 Lane F)

- [x] **(1) TI ヘルパー** — ✅ `IsTISubset.centralizer_le` 着地 (`cc4c20eb`, axiom-clean `[propext, Quot.sound]`)。共有 file 隔離コミット。
- [x] **(2) signature fix** — ✅ `hK`(κ-Hall)/`hU`((κ∪σ)ᶜ-Hall) 追加 (`f0b16276`, caller ゼロ非破壊)。
- [x] **(3) L483 `hDsub`** — ✅✅ **完全 sorry-free** (`f0b16276`): B(5)/C(9)+`centralizer_le` cite、
  **K=⊥ type-F wrinkle も Thm A(3) (`M=K⊔U⊔M_σ`, K=⊥⟹`M=U M_σ`⟹`x∈hatM_σ⊆M⟹x∈A(M)`矛盾) で解決**。
- [x] **(4) Conjunct 1 (Ti)** — ✅ **gated-endpoint skeleton 着地** (`29b296de`): 新
  `theoremII_conjunct1_of_inputs` (sorry-free+axiom-clean) が within-piece logic (M_σ=Thm D(1),
  各 TI piece=B(5)/C(9)+IsTISubset 定義) を検証、cross-piece exclusion を named hyp `hPieceInv`
  ("distinct orders across pieces") に局所化。theoremII の Conjunct 1 を配線 (K=⊥ は Thm A(3) で
  A_0−A(M)=∅ vacuous TI)。⟹ opaque sorry を `hPieceInv` (= **BG Theorem E** prime-structure, gated) に置換。
- [ ] **(uniqueness)** — 🛑 genuine gate と再確認 (Lane F tick): `|ℳ(C_G(x))|=1` 要。**BG §9
  `uniquenessTheorem` は rank≥2 + rank-3 条件を要求**し、x∈M_σ# の C_G(x) には rank 条件が無く直接 cite 不可;
  D(4) の ∃! は full predicate Q 限定。⟹ documented gate のまま。

リポ sorry 142 (skeleton は sorry-free 追加で不変)、full build 3831 green、AxiomsCheck OK。
**issue 主目標 (hDsub) 達成 + Conjunct 1 skeleton 化。残 = hPieceInv (BG Thm E) + uniqueness (BG §9 rank-gate)、
両者とも §16 main-result / BG Uniqueness の upstream landing 待ち。**

## やること (当初プラン)

- [ ] **(1) TI ヘルパー (汎用 infra, axiom-clean)**: [TISubset.lean](../OddOrder/GroupTheory/TISubset.lean) の
  `namespace IsTISubset` に追加:
  ```
  theorem centralizer_le (hA : IsTISubset A L) {x : G} (hx : x ∈ A) :
      Subgroup.centralizer ({x} : Set G) ≤ L
  ```
  証明: `c ∈ C_G(x)` なら `c*x*c⁻¹ = x ∈ A` (∵ `c*x = x*c`)、よって `hA c ⟨x, hx, _⟩` で `c ∈ L`。3行。

- [ ] **(2) Thm II signature fix (faithfulness, downstream caller ゼロ確認済)**: 追加 —
  `(hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))` /
  `(hKstar : Kstar = Msigma M ⊓ centralizer (K : Set G))` (Thm C 用、必要なら) /
  `(hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ sigma M)ᶜ) (U.subgroupOf M))`。
  ⚠ caller は現状ゼロ (`grep -rn theoremII_tame_embedding OddOrder/`)、破壊なし。8005 の忠実化方向とも整合。

- [ ] **(3) L483 `hDsub` を cite-compress (tractable)**: `x ∈ A0Set M K`, `x≠1`, `C_G(x)⊄M` から:
  - `x ∉ ASet M U` ⟹ `x ∈ A0Set\ASet` = TI (Thm C(9)) ⟹ `centralizer_le` で `C_G(x)≤M`、矛盾。
  - `x ∈ ASet M U`, `x ∉ Msigma` ⟹ `x ∈ ASet\Msigma` = TI (Thm B(5)) ⟹ `C_G(x)≤M`、矛盾。
  - ∴ `x ∈ Msigma`, `x≠1` ⟹ `x ∈ sigmaSharp M`。`X = ASet M U` case も同様 (A0Set 分岐不要)。
  - 🔑 **K=⊥ (type F) wrinkle**: `A0Set M ⊥ = hatMsigma M` (∵ `sharpSubgroup ⊥ = ∅`)、Thm C は `K≠⊥` 要求。
    K=⊥ case は別処理 (Thm A(8) `M_F=M_σ` 経由 or type F で `A0Set=ASet` を示し B(5) のみで閉じる) を要検討。

- [ ] **(4) L497 (Ti) — やや重い**: `A_0(M) = M_σ ⊔ (A(M)−M_σ) ⊔ (A₀(M)−A(M))` 分解 + cross-piece は
  位数相違で非共役 + 各 TI piece 内は TI-共役制御 (要 helper) + `M_σ` part は Thm D(1) fusion。
  hDsub より重い。signature fix 後に着手。

- [ ] **(L522 uniqueness — genuine gate, Lane G 単独では閉じない)**: `|ℳ(C_G(x))| = 1` (BG Uniqueness §9-10)
  を要する。citeable な Uniqueness 定理が repo にあれば cite、無ければ documented gate のまま
  (現 comment L518-521 が既に明記)。

## 完了条件

`theoremII_tame_embedding` の L483 (+ 可能なら L497) が sorry-free (B(5)/C(9)+`centralizer_le` cite)、
signature が Hall-pinned で忠実、L522 は Uniqueness gate として明示。`centralizer_le` は axiom-clean。
full build green + AxiomsCheck 非破壊。

## 参照

- consumer マップ: Thm II は**現状 Pf 未 cite** (issue 8005 §12.1) ⟹ signature 変更は安全。
- 関連: issue 8005 (faithful 復元, defer)、`notes/bg/s15_16_audit.md` §12.2-12.3。
- Thm B(5) = [S16_MainResults.lean:179](../OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults.lean) conjunct 5、
  Thm C(9) = [:201](../OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults.lean) (`IsTISubset (A0Set M K \ ASet M U) M`)。
- mmd Thm II proof = L4546-L4552。

## 🧾 pending 移行 (2026-07-02 hub 全体レビュー)

**BG 凍結 off-spine** — 残 2 gate (hPieceInv = BG Thm E / uniqueness = BG §9-10) は BG 側
frontier 凍結中は進まないため `issues/pending/` へ移動。ポインタ: **issue 8020 (closed) の
`hMaxUnique` 機構** (`S16_MainResults.lean:5743` 以降、signalizer uniqueness 経由の named
obligation 化) が **uniqueness 残 (L522 系) に部分的に効く** — 再開時はまず hMaxUnique
経由の discharge 可能性を確認すること。
