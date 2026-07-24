# S16 / App C scaffold 監査 — 下流で着手可能な leaf の地図 (2026-06-04)

**目的**: BG/Pf 上流 (§7-16 / §10-16) が別セッション進行中。それと**非交差**で下流から進められる
leaf を特定する。`feitThompson` 還元 (commit 0dfe816) 完成後の「次手の地図」。コード変更なしの監査。

正本: 本ノート。関連 = `feitthompson_critical_path_2026_06_03.md` / `scaffold_opaque_prop_convention.md` /
`notes/bg/appC_final_contradiction.md` / `notes/peterfalvi/s16_nonexistence_g.md (削除済, git履歴)`。

## 配線は honest (laundering 無)

`feitThompson` 直下〜最終矛盾まで、proven 部分はすべて named gap modulo で正直:
- `feitThompson_of_noMinimalSimpleOdd` ✅ sorry-free (還元)。
- `noMinimalSimpleOdd` = `noMinimalSimpleOdd_of_section16 hG (sectionSixteenHypothesis_of_isMinimalSimpleOdd hG)`。
- `noMinimalSimpleOdd_of_section16` = `BG.AppC.final_contradiction` = `S16.nonexistence_of_G hG hyp (theoremC hyp)`。
- **`S16.nonexistence_of_G` (S16:570) は proven** (rcases `field_normalizer_structure` + `not_lt_of_ge (bgAppendixC data) hyp.q_lt_p`)。
  ⟹ 2 仮説 modulo: ① `field_normalizer_structure` (FieldNormalizerData を構成) ② `bgAppendixC = theoremC` (data → p≤q)。

## 2 つの endpoint gap

```
nonexistence_of_G (proven)
 ├─ ① field_normalizer_structure (S16:563) : Nonempty (FieldNormalizerData hyp)   [🔴 sorry]
 │     = §16 (14.x) 全鎖 (caseB_for_T/S, exists_y_L, key_inequality, T_typeII,
 │       main_size_bounds, betaM_expansion, K_eq_V, orthogonality_switch, H_eq_U, ...)
 │     ⟹ 指標論 (Dade/coherence) + Type 解析。**上流 (Pf §10-16 と重なる)。下流不可**。
 └─ ② AppC.theoremC (AppC:97) : FieldNormalizerData hyp → p ≤ q                    [🔴 sorry]
       = 有限体 norm-set 論法 (Lemmas C.1-C.3)。**下流 workable・自己完結 (有限体論)**。
```

## 下流 workable 度の Tier 分け

### Tier 1 — 唯一の実質的下流ターゲット: **BG App C 有限体論 (theoremC + C.1–C.3)**
BG App C `theoremC : FieldNormalizerData → p ≤ q` の数学核 = `F_{p^q}` の norm-set 論法:
- **C.2** `lemmaC2_card_ge_two` : `|E| ≥ 2` (q≥5 / q=3 分岐)。
- **C.3** `lemmaC3_inverse_closed` : `E = E⁻¹` (generator-relation argument, Step1-4, **最大難所**)。
- **C.1** `lemmaC1_root_count` : `E=E⁻¹ ∧ |E|≥2 ⟹ p ≤ q` (多項式根数)。
  ここで `E = {a ∈ F_{p^q} | N(a)=N(2-a)=1}`, `N` = field norm。Condition (A) = `gcd((p^q-1)/(p-1), p-1)=1`
  (= `FieldNormalizerData.cyclotomic_coprime`, **genuine field**)。
- **指標論非依存・BG §7-16 / Pf §10-16 と非交差**。FT 最終矛盾の generator-relation 版。

**mathlib インフラ完備 (feasibility ✅, 2026-06-04 確認)**:
- `GaloisField p n` (位数 `p^n`, `FieldTheory/Finite/GaloisField.lean:70`) + `algEquivGaloisField (h : Nat.card K = p^n)`。
- `Algebra.norm K (S := K')` + `norm_surjective` / `unitsMap_norm_surjective` (同 :237/249)。
- Hilbert 90 (`RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean`) — U = norm-1 部分群 = `{x/x^α}` cyclic (Satz 90)。

**caveat (interface 結合)**: theoremC の入力 `FieldNormalizerData.field_model` は **opaque Prop** (materialize 済でない)
⟹ 入力から実 `F_{p^q}` を取り出せない。よって:
- **C.1-C.3 自体は standalone な有限体補題として下流で証明可能** (FieldNormalizerData 非経由で `GaloisField p q` 上に直接)。
- **theoremC への full 配線**は `FieldNormalizerData.field_model : Prop` を実体 (`G` 内に `F_{p^q}` 構造を持つ data)
  に materialize する必要。これは①の producer (`field_normalizer_structure`, Pf §16) と共有する interface 改変
  = 半上流。**推奨: まず C.1-C.3 を standalone leaf として証明 → 後で theoremC/FieldNormalizerData を materialize して接続**。

### Tier 2 — 自己完結算術 (大半 proven; パターン確認用)
**proven (sorry-free, self-contained number theory)**:
- `q_pow_gt_p_pow` (14.8.a, S16:383) : `q<p` 奇素数 ⟹ `q^{p+1} > p^{q+1}` (q=3 / q≥5 分岐)。
- `CaseBForTData.{v_odd, v_coprime_q_sub_one, divisor_modEq_one}` / `CaseBForSData.u_eq_of_*` (cyclotomic quotient)。
- `Hypothesis.{p_ne_q, five_le_p, q_not_modEq_one_mod_p, tSide_cyclotomic_*}` (S16:47-91)。
⟹ **教訓: 自己完結算術は proven、構造/指標論は sorry** という明確な境界。残る算術 rider (例 `key_inequality` の
`(v-1)/p > (u-1)/q` 部) は v,u の**値**を要し、それは構造由来 ⟹ 純算術でない (下流不可)。

### Tier 3 — blocked / 上流 (下流不可)
- `field_normalizer_structure` + §16 (14.x) 鎖全部 (上記①)。`_formula` opaque rider (S15:44 / S16:37) は
  ω/η/μ/ν 指標 index 族の S03/S04 materialize 待ち (`scaffold_opaque_prop_convention.md`)。Pf §10-16 と重なる。
- `sectionSixteenHypothesis_of_isMinimalSimpleOdd` (FeitThompson.lean) = BG §7-16 + Pf §10-16 全体。

## opaque-Prop placeholder の load-bearing 状態 (監査)
- **FieldNormalizerData** (S16) = **混在**: concrete carrier (`sigma : H→G`, `P`/`P0`/`U` image identifications,
  `W2_conj_y_normalizes_U`) + genuine (`cyclotomic_coprime`=cond A, `Q_elementaryAbelian`,
  `W2_normalizes_Q`, `y`, `y_mem_Q`) + **AppC producer obligation** (`appC_twisted_normOne_step`;
  `appC_normSet_generator_relation` は derived theorem)。
- **NormSetData / HypothesisB** (AppC) = downstream theoremC は finite-field C.1/C.2 と S16 の C.3 producer obligation に配線済み。
  `HypothesisB` は concrete `H=P⋊U`, monomorphism `σ:H→G`, `P0`/`U` image identification,
  normalizer 条件の carrier まで更新済み。残る C.3 本体は S16 `appC_twisted_normOne_step` の materialization。
- vacuous rider 注意 (`scaffold-sorry-free-not-done`): `∃ data, data.caseB_formula ∧ <real>` の `_formula` 連言は
  常時充足可 ⟹ statement は教科書より弱い。実制約 (card 等式/normalizer 包含/D=⊥) は genuine。

## 推奨 (次手)
**Tier 1 = BG App C C.1–C.3 を standalone 有限体 leaf として攻略**が唯一の実質下流増分。順序案:
1. `OddOrder/BG/AppC_FinalContradiction.lean` (or 新 leaf) に `GaloisField p q` ベースで `N`, `E` を materialize。
2. **C.1** (多項式根数, 容易め) → **C.2** (`|E|≥2`, q 分岐) → **C.3** (`E=E⁻¹`, 最難 Step1-4)。
3. 完成後、`FieldNormalizerData.field_model` を実体化して `theoremC` を C.1 に配線 (interface 改変, ①と調整)。
最難は **C.3** (generator-relation の核, BG mmd L4875-5002)。issue 化推奨。
