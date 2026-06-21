---
id: 7008
slug: typepdata-contradictory
title: "TypePData is contradictory — U_normal/fitting_eq/fitting_lt_derived unfaithful to Pf (8.4)"
created: 2026-06-21
---

# TypePData is contradictory — `U_normal`/`fitting_eq`/`fitting_lt_derived` unfaithful to Pf (8.4)

## 🔴 発見（Lean で sorry-free 検証済）

`OddOrder/GroupTheory/MaximalSubgroupType.lean:126` の `structure TypePData` は**論理的に矛盾**しており
**uninhabitable**。`example (d : TypePData M) : False` が sorry-free で通る（2026-06-21 検証、後述）。

帰結:
- `IsTypeP M = Nonempty (TypePData M)` は**全ての M で証明可能に False**。
- `IsTypeII/III/IV/V M`（全て `TypePData` を bundle）も証明可能に False。
- `IsTypeNonI M` も False。
- ⟹ **Prop 16.1 forward bridges (`hP2II`/`hP1neIIIIV`/`hP1eqV`) は honest には証明不能**（充足可能な
  BG-local 仮説から False 結論には到達できない）⟹ **FT path が Prop 16.1 で実質ブロック**。

これは [[scaffold-sorry-free-not-done]] / [[s16-typep-producer-unfillable]] が警告する「hard content を
**矛盾した**未充足仮説に hoist した scaffold」の典型。`typePData_of_inputs`(S16:851) は 6 deep field を
仮説として取るが、それらは**互いに矛盾**しているので honest に discharge することは不可能（LAUNCH cont.³ の
「fitting_decomposition から 6 field を供給する」計画は実行不能）。

## 矛盾の機序

`TypePData` の field（H = M_F, M' = derivedInG M）:
- `U_normal : (U.subgroupOf M').Normal`  — U ◁ M'
- `derived_complement : IsComplement' (H.subgroupOf M') (U.subgroupOf M')` — M_F, U は M' の補元
- `fitting_eq : maxNilpotentNormalHall M = H ⊔ (U ⊓ C_G(H))` — M_F = M_F ⊔ (U⊓C(M_F))
- `fitting_lt_derived : maxNilpotentNormalHall M < derivedInG M` — M_F < M'（strict）

`maxNilpotentNormalHall M` (= M_F) は normal subgroup の sSup ゆえ M で normal、よって M' でも normal。
すると:

1. U ◁ M'（`U_normal`）+ M_F ◁ M' + 補元（`derived_complement`）⟹ **M' = M_F × U 直積** ⟹ U ≤ C_G(M_F)。
2. ⟹ U ⊓ C_G(M_F) = U。
3. `fitting_eq` ⟹ M_F = M_F ⊔ U。
4. `derived_complement` ⟹ M' = M_F ⊔ U（`TypePData.derivedInG_eq_fitting_sup_U`）。
5. (3)(4) ⟹ M_F = M'、`fitting_lt_derived`（M_F < M'）と矛盾。

(type V の U=⊥ では `derived_complement` だけで M_F = M' が出て `fitting_lt_derived` と直接矛盾。)

## 原典との対応（Peterfalvi (8.4)/(8.5)、04.10 L41-67）

**(8.4) Definition** of type 𝒫（H = M_F, M' = [M,M], M'' = [M',M']）:
- (a) cyclic Hall W₁≠1 with M = M' ⋊ W₁ — Lean `M_complement`/`W1_*` ✓
- **(b)** nilpotent U ≤ M', **normalized by W₁**, with **M' = H ⋊ U** —
  - U ≤ M' (`U_le`) ✓ / U nilpotent (`U_nilpotent`) ✓ / M' = H ⋊ U（H normal kernel, U 補元）= `derived_complement` ✓
  - ⚠ **「normalized by W₁」= W₁ ≤ N(U)** であって「U ◁ M'」ではない。**`U_normal` がバグ**。
    M' = H ⋊ U は半直積で、U が M' で normal なら直積 ⟹ U=1 を強制（type II–IV を vacuous 化）。
- (c) H not cyclic ∧ **M'' ⊆ H·C_M(H) = F(M) ⊆ M'**（Peterfalvi の ⊂ は ⊆；type V で F(M)=M' ゆえ非 strict）—
  - H not cyclic (`H_noncyclic`) ✓
  - M'' ⊆ F(M)（= `secondDerived_le_fitting`、(8.5.a) で F(M)=H·C_U(H)=H⊔(U⊓C(H)) ゆえ忠実）✓
  - ⚠ **F(M) = H·C_U(H)**（(8.5.a)）⟹ `fitting_eq` の **LHS は `fittingInAmbient M`（F(M)）であるべき**、
    現状の `maxNilpotentNormalHall M`（M_F）はバグ。
  - ⚠ **F(M) ⊆ M'（非 strict）**⟹ `fitting_lt_derived` は **`fittingInAmbient M ≤ derivedInG M`** であるべき。
    現状の `maxNilpotentNormalHall M < derivedInG M`（strict, M_F）は type V（U=⊥, M_F=M'=F(M)）で False。

## 提案する修正（忠実版）— hub で検証・実装

`TypePData`（`MaximalSubgroupType.lean:126`）の **3 field**:

1. `U_normal : (U.subgroupOf M').Normal` → **`W1_normalizes_U : W1 ≤ Subgroup.normalizer (U : Set G)`**
   （(8.4.b)「U normalized by W₁」忠実。`W1` は既存 field。現状 real consumer ゼロ）。
2. `fitting_eq : maxNilpotentNormalHall M = H ⊔ (U ⊓ C(H))`
   → **`fitting_eq : (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype = H ⊔ (U ⊓ C(H))`**
   （(8.5.a) **実 Fitting** F(M) = H·C_U(H)）。
   - ⚠ **重要な実装制約**: `fittingInAmbient M`（= `OddOrder.BG.Ch2.S08.fittingInG M`）は **BG 下流**ゆえ
     `MaximalSubgroupType.lean`（GroupTheory 上流）から**参照不可**。代わりに `fittingInG M` と**定義同値**な
     `(OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype` を inline する（`Isaacs.Ch01.fitting` は
     MaximalSubgroupType の import closure に在る — **build test で到達性確認済 2026-06-21**）。
   - ⚠ M_F（`maxNilpotentNormalHall M`）を LHS にすると `C_U(H) ≤ M_F`⟺`C_U(H)=⊥` を強制し
     **type IV（C_U(H)≠⊥）を排除**するので不忠実。実 F(M) が必須。
3. `fitting_lt_derived : maxNilpotentNormalHall M < derivedInG M` → **削除**。
   - 緩和（`≤`）でなく**削除**でよい: (8.4.c) の `F(M) ⊆ M'` は **新 `fitting_eq` + `H_le` + `U_le`** から
     導出される（F(M) = H⊔(U⊓C(H)) ≤ M'、H≤M' と U⊓C(H)≤U≤M' より）ので冗長。

修正後の無矛盾性チェック:
- type V（U=⊥）: `derived_complement` ⟹ M'=H=M_F。新 `fitting_eq`: F(M)=H⊔⊥=H=M_F=M'（(8.5.a) で
  F(M)=H·C_⊥(H)=H 忠実）。旧 strict `fitting_lt_derived` が消えたので矛盾なし。
- type II–IV（U≠⊥）: M'=H⋊U 半直積（U_normal なし）、F(M)=H·C_U(H)⊆M'。無矛盾。
- 旧 `example : TypePData M → False` は U_normal/旧 fitting_eq/fitting_lt_derived を使うので**通らなくなる**
  （矛盾解消の sanity check）。

## Consumer 修正（blast radius）

`U_normal` は real consumer ゼロ。`fitting_eq`/`fitting_lt_derived`/`secondDerived_le_fitting` の consumer は
**結論は正しいが矛盾 field で証明している** 2 箇所:

- **`OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults.lean`**（lane-f）: `typePData_of_inputs`(:851) +
  `typePData_of_isTypeP_of_inputs`(:983) の field 引数を更新。
- **`OddOrder/Peterfalvi/S12_MaximalIII_IV_V.lean:666`**（lane-b）: `M'' < M'` を導出。
  現状 `secondDerived_le_fitting.trans fitting_eq.ge` で M''≤M_F、`fitting_lt_derived` で M_F<M'。
  → 修正後は **M' solvable nontrivial ⟹ M''=[M',M']⊊M'** で再証明（`IsSolvable.commutator_lt_top_of_nontrivial`
  系、fitting field 非依存）。
- **`OddOrder/Peterfalvi/S15_SAndT.lean:1309`**（lane-h）: type-II 文脈で `U ≠ ⊥` を導出。
  現状 `fitting_lt_derived` の strict を使う。→ 修正後は **type-II/III/IV core (`TypePNontrivialCore.1` =
  `data.U ≠ ⊥`)** から直接（type II は (8.6.a) で U≠1）。

## 関連構造体の監査結果（2026-06-21、subagent ×2 + 手読み）

ユーザー指示で「TypePData 以外の shared 構造体に同種の独立矛盾がないか」を監査。**結論: 独立矛盾は
TypePData のみ、他は全て下流**（IsTypeP/IsTypeNonI/TypePData を bundle して uninhabitable になっているだけ）。

| 構造体 | 場所 | 判定 |
|---|---|---|
| `TypeFData` / `TypeIData` | `MaximalSubgroupType.lean:82/107` | ✅ **clean**（IsTypeP 非依存、補元 U を normal 化していない、LHS/strict 問題なし） |
| `TypeIIData`–`TypeVData` | `:192/201/208/215` | 下流（`typeP : TypePData` bundle）。追加 field に新矛盾なし |
| `Section16Inputs/MaximalPair/TypePStructure/CharacterData` | `FeitThompson.lean` | 下流（IsTypeNonI/IsTypeP bundle）。**`Section16TypePStructure`/`Section16Inputs` は既に忠実な `W1_normalizes_U` + `derivedInG=M_F⊔U` を使用**（私の診断を裏付け） |
| Pf `S15.Hypothesis`(76)/`BasicStructureData`ほか | `S15_SAndT.lean` | 下流（`S_nonI:IsTypeNonI` 等）。独立 red-flag なし、`W1_normalizes_U` 忠実 |
| Pf `S16 Hypothesis`/`L/MHypothesis`/`CaseB*Data`ほか | `S16_NonExistenceG{,Core}.lean` | 下流（hyp 経由）。独立 red-flag なし |

⟹ **TypePData の 3 field 修正で下流 cascade 全体が修復**。他構造体を独立に直す必要なし（hub が TypePData
fix 後に full build で確認すれば、下流は自動的に整合）。

## やること（hub）

- [ ] **検証**: 本 issue の `example : TypePData M → False`（下記コード）を `OddOrder/ScratchTypePCheck.lean`
  で再現し、矛盾を独立確認（lane-f は 2026-06-21 に確認済、ファイルは削除済）。
- [ ] `TypePData` の 3 field を忠実版に修正（上記「提案する修正」）。
- [ ] `typePData_of_inputs`(S16:851) / `typePData_of_isTypeP_of_inputs`(S16:983) の field 引数更新
  （`hUnorm` 削除/置換、`hFiteq` の LHS、`hFitlt` 削除）。
- [ ] Pf S12:666 consumer を solvability 経由に再証明（`M''=[M',M']⊊M'`: M' solvable nontrivial。
  M' nontrivial は `W2_nontrivial`+`W2≤H⊓M''` から `M''≠⊥`⟹`M'≠⊥`）。
- [ ] Pf S15:1309 consumer を type-core 経由に再証明（`U≠⊥` = `tdata.common.1`、TypePNontrivialCore の第1連言）。
- [ ] full build green + AxiomsCheck OK + `example : TypePData M → False` が**通らなくなる**ことを確認。
- [ ] 各レーン（B/H）に反映（merge 伝播）。S12=lane-b / S15=lane-h の active 編集と衝突しないよう調整。

## 完了条件

`TypePData` が本 issue の矛盾経路で無矛盾になり、full build green + AxiomsCheck OK。`U_normal` 矛盾経路の
`example : False` が再現不能。これにより **Prop 16.1（issue 7007/8015）の forward/reverse bridges が honest に
組める**（IsTypeP/IsTypeII 等が証明可能 False でなくなる）。

## 検証コード（sorry-free、2026-06-21、`OddOrder/ScratchTypePCheck.lean` で確認後削除）

```lean
-- open OddOrder.GroupTheory OddOrder.BG.Ch4.S16 OddOrder.BG.Ch4.S15
example {M : Subgroup G} [Finite G] (d : TypePData M) : False := by
  classical
  have hMFle : maxNilpotentNormalHall M ≤ derivedInG M := d.H_eq ▸ d.H_le
  have hMFleM : maxNilpotentNormalHall M ≤ M := maxNilpotentNormalHall_le M
  have hMnorm : M ≤ Subgroup.normalizer ((maxNilpotentNormalHall M : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).mp
      (maxNilpotentNormalHall_subgroupOf_normal M)
  have hM'leM : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hM'norm : derivedInG M ≤
      Subgroup.normalizer ((maxNilpotentNormalHall M : Subgroup G) : Set G) := hM'leM.trans hMnorm
  have hMFnorm' : ((maxNilpotentNormalHall M).subgroupOf (derivedInG M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFle).mpr hM'norm
  have hdisj : Disjoint ((maxNilpotentNormalHall M).subgroupOf (derivedInG M))
      (d.U.subgroupOf (derivedInG M)) := by
    have h := d.derived_complement.disjoint; rwa [d.H_eq] at h
  have hUcent : d.U ≤ Subgroup.centralizer ((maxNilpotentNormalHall M : Subgroup G) : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]; intro m hm
    have huM' : u ∈ derivedInG M := d.U_le hu
    have hmM' : m ∈ derivedInG M := hMFle hm
    have hcomm := Subgroup.commute_of_normal_of_disjoint _ _ hMFnorm' d.U_normal hdisj
      (⟨m, hmM'⟩ : ↥(derivedInG M)) (⟨u, huM'⟩ : ↥(derivedInG M))
      (Subgroup.mem_subgroupOf.mpr hm) (Subgroup.mem_subgroupOf.mpr hu)
    have heq : ((⟨m, hmM'⟩ : ↥(derivedInG M)) * ⟨u, huM'⟩ : ↥(derivedInG M)) =
        ⟨u, huM'⟩ * ⟨m, hmM'⟩ := hcomm
    simpa using congrArg (Subtype.val) heq
  have hinf : d.U ⊓ Subgroup.centralizer ((maxNilpotentNormalHall M : Subgroup G) : Set G) = d.U :=
    inf_eq_left.mpr hUcent
  have hfe := d.fitting_eq; rw [d.H_eq, hinf] at hfe
  have hMFeq : maxNilpotentNormalHall M = derivedInG M := hfe.trans d.derivedInG_eq_fitting_sup_U.symm
  exact absurd hMFeq (ne_of_lt d.fitting_lt_derived)
```

## 解決 (2026-06-21, hub) — CLOSED

ユーザー裁可で hub が atomic 修正を実施。`example : TypePData M → False` を独立検証で再現
(sorry-free) → 3 field を Pf (8.4)/(8.5) 忠実版に修正 → 旧矛盾証明が `Invalid field U_normal`
で再現不能になることを確認。**実 sorry 134 不変・full build 3881 jobs green・AxiomsCheck OK・
新 axiom 0**。

修正内容 (`MaximalSubgroupType.lean` の `TypePData`):
1. `U_normal : (U.subgroupOf M').Normal` → **`W1_normalizes_U : W1 ≤ Subgroup.normalizer (U : Set G)`**
   ((8.4.b) 忠実、downstream `FeitThompson.lean` の `Section16TypePStructure`/`Section16Inputs` が
   既に使う形と一致)。
2. `fitting_eq` の LHS: `maxNilpotentNormalHall M` → **`(OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype`**
   (実 Fitting `F(M)`、(8.5.a) 忠実)。
3. `fitting_lt_derived : M_F < M'` → **削除** ((8.4.c) の `F(M) ⊆ M'` は新 fitting_eq から導出可、
   type V で False だった strict を除去)。

consumer 修正 (結論は不変、矛盾 field 非依存に再証明):
- producer `typePData_of_inputs`/`typePData_of_isTypeP_of_inputs` (S16): hypothesis 署名更新
  (`hUnorm`→`hKnorm`/`hFiteq` LHS/`hFitlt` 削除) + field 代入。
- **S12:730** `M'' < M'`: `M' = M_F ⋊ U` solvable (`maxNilpotentNormalHall_isNilpotent` +
  `U_nilpotent` + `derived_complement.QuotientMulEquiv` + `solvable_of_ker_le_range`) かつ nontrivial
  (`W₂ ≠ ⊥`) ⟹ 非 perfect で再証明。
- **S15:1313** `hyp.U ≠ ⊥`: `U` が `tdata.typeP.U` (type-II core `common.1` で `≠ ⊥`) に S-共役
  (`exists_conj_typeP_U_of_coprime` + `pointwise_smul_eq_bot_iff`) で再証明。

⟹ **Prop 16.1 forward bridges が honest に組める** (IsTypeP/IsTypeII 等が証明可能 False でなくなった)。
**⚠ レーン伝播**: S12=lane-b / S15=lane-h の active 編集と次回マージで衝突しうる (本 fix を main に
先行投入、各レーンが main 取込時に reconcile)。

## 参照

- 影響: Prop 16.1（issue 7007/8015）の forward/reverse bridges は本 fix 後でないと honest に組めない。
- memory: [[s16-typep-producer-unfillable]] [[scaffold-sorry-free-not-done]] [[bg-s16-gated-on-typedata-construction]]
- 原典: Peterfalvi (8.4)/(8.5) = `references/peterfalvi/04.10_pp_44_49_Structure_of_a_Minimal_Simple_Group_of_Odd_Order.mmd` L41-67
