# mathlib v4.29.1 → v4.30.0-rc2 移行記録

2026-05-27 実施 (branch `mathlib-rc2`)。`lake build OddOrder` フル green、
AxiomsCheck の 167 flagship が全て axiom-clean (burnside_p_pow_q_pow 含む)。
**18 .lean + pin 3 ファイル / +76 −51 行**と差分は小さく、drift は下記の数パターンに集中。

## pin (moore57 issue 0009 と同一)

| | 値 |
|---|---|
| `lean-toolchain` | `leanprover/lean4:v4.30.0-rc2` |
| `lakefile.toml` mathlib `rev` | `v4.30.0-rc2` (実タグ) |
| manifest | format `1.2.0`, mathlib `5450b53e…` |

手順: `lean-toolchain` + `lakefile.toml` 編集 → `lake update mathlib` (manifest 再生成 +
post-update hook が `cache get` 実行) → 整合確認 (`lean --version` = 4.30.0-rc2 `3dc1a088…`,
repo と mathlib の `lean-toolchain` 一致) → `lake build` wave 毎修正。**cache は rc2 で正常**
(通常 prerelease タグ、Azure から取得、ソースコンパイル不要)。

## rc2 API 変更パターン (次回 bump で再利用)

1. **`IsMulCommutative → CommGroup/CommMonoid/CommMagma` が `scoped instance` 化** (perf 理由,
   `Algebra/Group/Defs.lean` L1277)。対処 = **`open scoped IsMulCommutative`**。
   - file-wide で OK な file が多い (Ch05/FrobeniusGroup/S7A2/S7D1/Ch07Main/Ch04…)。
   - ただし **`CommGroup (MulAut ?m)` (メタ変数) の typeclass 探索を爆発させる file では timeout**
     (Ch02 で発生)。その場合は **局所 `open scoped IsMulCommutative in <decl>`** か、
     直接 `inst.is_comm.comm a b` を使う。
   - ⚠ **明示 `{ (inferInstance : Group G) with mul_comm := … }` で CommGroup を作ると、
     派生する `One`/`DivisionMonoid`/`Additive.addCommGroup` が ambient `Group` と
     diamond し下流が壊れる** (Ch04 `frattini_le_…` で発生)。ambient instance には scoped を使う。
     Prop ゴール (IsNilpotent 等) や単発の明示引数なら diamond 無害。
2. **`IsMulCommutative.comm` フィールド → `.is_comm.comm`** (field rename: `is_comm : Std.Commutative`)。
   構築は **`⟨⟨mul_comm⟩⟩`** (二重包み: `IsMulCommutative ⟨ Std.Commutative ⟨…⟩ ⟩`)。
3. **`CommGroup.ofIsMulCommutative` 削除** → scoped instance 経由 `(haveI := h; inferInstance)`。
4. **`Subgroup.normalizer` が `Set G` 引数に** (旧 `Subgroup G`; `Defs.lean:667`)。
   Sylow の二重 coercion を解消: `normalizer (P : Set G)` (旧 `normalizer ((P:Subgroup G):Set G)`
   や `normalizer (P:Subgroup G)` は `↑↑P` になり mathlib の 1-coe `↑P` と不一致)。
   `Sylow.coe_coe : ↑↑P = ↑P` が正規化補題。
5. **`mul_pow` (可換部分群の元)** → `Commute a b` を作って `Commute.mul_pow`
   (`{x | x^p=1}` 部分群構成で頻出; `Subtype.ext (habel …)` から Commute)。
6. **`‹T›` (= `by assumption`) は literal hypothesis (instance binder) のみ**拾う。
   **導出 instance** (IsCyclic→IsMulCommutative 等) には **`inferInstance`** を使う。
7. **`IsMulCommutative P → IsMulCommutative ↥⊤` の自動 transport 無し** →
   `⟨⟨fun a b => Subtype.ext (hP.is_comm.comm a b)⟩⟩` で直接構築。

## その他

- `IsCyclic.commGroup` は健在 (`letI := IsCyclic.commGroup` + `⟨⟨mul_comm⟩⟩`)。
- BrauerPermutation の `permMatrix`/`PEquiv.toMatrix_toPEquiv_mul` は **無傷** (移行不要だった)。
- CI (`lean_action_ci.yml`) は AxiomsCheck gate を持つ。lintText/shake は無し (moore57 と違い)。
- `update.yml` = 公式 `mathlib-update-action` (workflow_dispatch)。RC は prerelease なので
  手動が確実 (release タグ自動 PR には乗らない)。
