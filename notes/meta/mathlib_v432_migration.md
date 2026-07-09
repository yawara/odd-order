# mathlib v4.30.0-rc2 → v4.32.0-rc1 移行記録

2026-07-09 実施 (branch `mathlib-v432`)。lean-eval リポジトリの pin に合わせた bump。
`lake build OddOrder` フル green (8m43s / 4005 jobs)、AxiomsCheck 2148 checks 全て
axiom-clean (propext / Classical.choice / Quot.sound のみ)、sorry 81 = 81 (regression 無し)。
**34 waves / 修正 ~70 files + deprecation sweep 488 箇所 / 112 files**。drift = mathlib 1851
commits (2026-04-18 → 2026-06-18)。

## pin

| | 値 |
|---|---|
| `lean-toolchain` | `leanprover/lean4:v4.32.0-rc1` |
| `lakefile.toml` mathlib `rev` | `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56` (exact SHA、lean-eval 合わせ) |
| manifest | mathlib `360da6fa…`、全依存 rev は lean-eval と同一 |

手順: `lean-toolchain` + `lakefile.toml` 編集 → `lake update mathlib` (post-update hook が
cache 8564 files 取得) → wave 方式で修正 (full build → エラー file 群を並列 agent 修正 →
commit → 次 wave)。cache は master commit pin でも正常。

## v4.32 API 変更パターン (次回 bump で再利用)

### 系列 API の Subgroup 相対化 (最大の構造変更)
1. **`lowerCentralSeries` 群値版廃止** (#39844): 新 canonical =
   `Subgroup.lowerCentralSeries (S : Subgroup G) : ℕ → Subgroup G` (lcs 0 = S)。
   群の場合は **`(⊤ : Subgroup G).lowerCentralSeries n`** (⊤ で旧定義と同一再帰 = defeq 互換)。
   root deprecated alias は Subgroup 版を指すため `lowerCentralSeries G n` (Type 適用) は hard error。
   リネーム: `lowerCentralSeries_one` → `top_lowerCentralSeries_one`、`_zero`/`_succ`/`_antitone`/
   `nilpotent_iff_lowerCentralSeries` → `Subgroup.*` (antitone 等は S 引数化)。
   自前 `lowerCentralSeries_map_eq_of_surjective` は mathlib 新 `Subgroup.map_lowerCentralSeries`
   が公式後継 → 削除・置換済 (wrapper 方針)。
2. **`upperCentralSeries` 一族も Subgroup namespace へ移動** (定義は群値のまま、lemma 名のみ):
   `Characteristic` instance が新名にキーされるため instance 合成も旧名では失敗する。
   `mem_upperCentralSeries_succ_iff` の結論は `x*y*x⁻¹*y⁻¹` でなく `⁅x, y⁆` 形に変更。

### instance / 定義の非可換化・厳格化
3. **AddAut の加法化** (#39884): `AddAut M` は AddGroup (合成=加法)。`Mul (AddAut M)` 消滅。
   旧 `→* AddAut R` は **`→* Multiplicative (AddAut R)`** に。`AddAutAdditive` は
   `AddAut (Additive G) ≃+ Additive (MulAut G)` 化 → `AddEquiv.toMultiplicativeLeft` で橋渡し。
4. **非 class 返り型の `instance` 宣言がエラー化**: `instance : CharacterTableIndexing G` /
   `instance : p ∈ π` 等は `def`/`theorem` 化 (消費側は明示適用)。
5. **`Finite → Fintype` の自動昇格消滅箇所**: `Fintype (Subgroup H)` / `Fintype (Sylow p H)` /
   `Fintype ι` (Finset univ 用) は `letI : Fintype _ := Fintype.ofFinite _` を明示。
6. **pending synthesis 入れ子上限**: 具体型 (G →₀ ℂ) での AddCommGroup 連鎖が
   maxSynthPendingDepth 超過 → **zeta 透明な `letI := inferInstance`** で短絡 (haveI は不可)。

### elaboration / simp 挙動変化 (件数最多)
7. **congrArg の結果が beta 簡約済に** → 直後の beta 簡約目的の引数なし `simp only at h` /
   `dsimp only` が "made no progress" **エラー**化 → 削除 (~20 箇所)。同様に simp/rw が goal を
   完全に閉じて後続 `group`/`ring_nf`/`omega` が dead になるパターン → 削除。
8. **simp の zetaDelta デフォルト無効化**: tactic `let`/`set` 束縛 fvar を simp が unfold しない
   → `simpa [x]` (let 名を simp set に明示) or 定義等式 rw or term-mode defeq exact。
9. **simp 正規形の変化** (追加が必要になった simp 引数):
   `Subgroup.subtype_apply` (S.subtype x ↔ ↑x) / `SetLike.mem_coe` / `Subgroup.mem_subgroupOf` /
   `Subgroup.smul_def` / `MulAut.smul_def` + `conj_apply` 連鎖 / `commute_iff_eq` (Commute を simp が
   unfold しない) / `Set.mem_setOf_eq` / `Subgroup.index_eq_card` (default simp から除外) /
   `MulDistribMulAction.toMonoidEnd_apply` 連鎖。
10. **Additive/Multiplicative の defeq が simp 最終照合で効かない** →
    `show Additive.toMul (g • v) = g • Additive.toMul v from rfl` の **show-rfl 明示ブリッジ**
    (± `Nat.card_congr Additive.toMul`)。`Function.IsFixedPt` も unfold されない → `.eq`。
11. **`Representation.asModule` の deriving 化**: `asModuleEquiv` (= LinearEquiv.refl) の
    simp unfold 消滅 → `asModuleEquiv` 明示ブリッジ / defeq exact 化。
12. **representations / ConjAct diamond 修正** (#40421/#40427) の余波: `Subrepresentation` の
    `⊥/⊤/⊓/⊔.toSubmodule` は **defeq のまま** → simpa 経由をやめ `congrArg toSubmodule h` を
    直接 exact。「表示が完全同一の Type mismatch」はこれ (pp.all で instance 経路差を確認)。
13. **`zero_le _` の名前解決変化**: 適用形は `Nat.zero_le _` に明示 (order 系の無引数 zero_le を拾う)。
14. **リネーム/削除**: `Nat.factorization_eq_zero_of_non_prime` **削除** → `_of_not_prime`。
    `Int.cast_natAbs` → `Nat.cast_natAbs`。`Pi.monoidHom` → `MonoidHom.pi` (#40024)。
    `FiniteDimensional.of_fintype_basis` → `Module.Basis.finiteDimensional_of_finite`。
    `Xor'` → `Xor` (alias 存命)。`_root_.smul_apply` 新設 → `ClassFunction.smul_apply` と衝突時は
    qualify。集合差 lemma は `diff` → `sdiff` 系。`Subalgebra.coe_val` / `{p}ᶜ ↔ {q | q ≠ p}` は
    defeq (term-mode 直接)。

### deprecation sweep (2026-07-09 実施済)
同 signature リネーム 488 箇所 / 112 files を機械置換 (commit 68359993)。**返り値型が変わった
deprecated shim は据え置き** (動作中、issue 0104 で追跡): `Subgroup.inf_eq_bot_of_coprime` (68、
→ `disjoint_of_coprime_natCard` + `.eq_bot`)、`commutative_of_cyclic_center_quotient` (24、→
`MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center` + `.is_comm.comm`)、
`IsPGroup.commutative_of_card_eq_prime_sq` (12、→ `isMulCommutative_*`)、`Subgroup.normal_of_comm`
(7、→ `normal_of_isMulCommutative`)。

## 運用知見

- **wave 方式**: full build (incremental、10-80s) → エラー file 群を 1 file = 1 agent で並列修正
  (検証は `lake env lean <file>` 単体 — lake ロック回避 + 下流再ビルド無し) → 審査 agent が
  diff 検査 (sorry/statement 改変無し) → commit → 次 wave。序盤は 4-7 files/wave で並列が効き、
  spine 直列部 (wave 16+) は 1 file/wave になるため hub 直接修正へ切替が効率的。
- **greppable な削除・リネームは初出時に repo 全体を一括先回り置換** (factorization、congrArg 後
  dead simp、lowerCentralSeries) — 3-5 waves 分を圧縮できた。
- lane 再同期: `git merge main` → `lake exe cache get` 不要 (packages symlink 共有で hub が取得済) →
  `.lake/build` は旧 toolchain 分が stale なので初回 build は実質 full (~10-20 分)。
