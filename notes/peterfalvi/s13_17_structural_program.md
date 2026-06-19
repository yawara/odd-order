# Pf (13.17) 構造論プログラム — 方針① (lane-h, 2026-06-19)

> POLE-2 (`field_normalizer_structure`) は `exists_LHypothesis` 経由で Pf **(13.17)**
> `typeII_overNormalizer_frobenius` を cite する。(13.17) は gated-endpoint skeleton 化済
> (`0d99daf1`): `sorry`-free assembly が (12.7) `S14.typeI_frobenius` を cite + 2 faithful
> obligation に分離。本プログラム = その 2 obligation を**深い §13 構造論**で埋める計画。
> 正本 issue = `issues/pending/2009-s16-field-normalizer-pole2.md`。

## ゴールと分担原則

(13.17) の 2 obligation を「H 単独の構造論 + 既存 infra cite + sorried §13 producer cite
(安定 signature) + 新規 reusable 形式化」で証明する。**char/Dade 本体 (basic_structure の
char fields 等) は Lane B 領域**で、cite はするが unconditional 化は B 待ち。

## 検証済み infra (cite 可、再導出不要)

- **SZ 補元共役**: `OddOrder.Isaacs.Ch03.exists_conj_le_of_isComplement'_of_coprime`
  (Main:1223) — 正規部分群 + 補元 + coprime ⟹ 補元は共役。
- **normalizer 同変性**: repo `normalizer_conj_smul` (S12_ExceptionalBridge:266) + mathlib
  `Subgroup.map_normalizer_eq_of_bijective`。
- **maxNNH 同変性**: `maxNilpotentNormalHall_pointwise_smul` (本セッション landing, axiom-clean)。
- **coprime→disjoint**: `IsPGroup.le_or_disjoint_of_coprime` (P は p-群)。
- **type-data**: `TypePData.derived_complement` (P ⊓ typeP.U = ⊥ in derived) +
  `TypePNontrivialCore` (typeP.U ≠ ⊥) + `M_complement` (W1 が derived を補完)。
- **Frobenius 機構**: Isaacs Ch06 `FrobeniusGroup` / `FrobeniusActionTI`。

## crux base = hyp.U coherence (Phase 0)

**問題**: Hypothesis は `hyp.U` を `S_deriv_eq_PU : derivedInG S = P ⊔ U` (**join のみ**) で制約し、
complement (`P ⊓ U = ⊥`) も S の type-data `typeP.U` との一致も pin しない。一方 obligation ① の
L~S 除外は `¬ N_G(hyp.U) ≤ S` (type-II 性) を要し、`IsTypeII.normalizer_not_le` は `typeP.U` についてのみ。
`typeP.U` は complement・≠⊥ (上記 type-data) だが `hyp.U` がそれに pin されていない (under-constraint)。

**🔑 診断確定 (2026-06-20): coprimality は disjointness だけで H 単独導出可** — Phase 1 SZ 補題が要する
`Coprime |U| |P|` は **`P ⊓ hyp.U = ⊥` (disjointness) のみから** H 単独で出る。根拠:
`P = tdata.typeP.H = maxNilpotentNormalHall M'` (`hPH` + `TypeIIData.derived_fitting_eq`)、
**`maxNilpotentNormalHall_isHall M'` は相対形** (`(mnh M').subgroupOf M'` が ↥M' 内で Hall) → `.coprime_index`
で `Coprime |P| (P.subgroupOf M').index`。disjoint + `S_deriv_eq_PU` の join ⟹ U が P の補元 ⟹
`|U| = (P.subgroupOf M').index` ⟹ `Coprime |U| |P|`。**∴ Phase 2 の真の gate は `P ⊓ hyp.U = ⊥` 1 本のみ**。

**解決オプション**:
- (a) `P ⊓ hyp.U = ⊥` を §13 構造論で H 単独導出: 上記 Hall 論法は disjoint を**仮定**する (循環でない:
  Hall は coprime を与えるが、U が真の補元 [P⊓U=⊥] であることは別途要)。disjoint 自体は **hyp.U が
  under-constrained** ゆえ Hypothesis から出ない (hyp.U=M' でも S_deriv_eq_PU を満たす)。⟹ §13 card でも不可。
- (b) **Hypothesis faithfulness enrich (F、最小 ask 確定)**: `hyp.U` を P-補元に pin する **1 フィールド**を追加すれば
  十分 — 最小は `P_inf_U_eq_bot : hyp.P ⊓ hyp.U = ⊥` (disjointness)。これだけで H が coprimality→SZ→Phase 2 を回す。
  (代替: `IsComplement' (P.subgroupOf M') (U.subgroupOf M')` or `typeP.U = hyp.U` でも可、いずれも disjoint を含意。)
  carrier 変更 = FeitThompson の `sectionSixteenHypothesis_of_inputs` producer 要対応 (**F 領域**、cross-lane)。
- **結論**: (a) は infeasible (hyp.U under-constraint は構造論で塞げない、carrier の faithfulness 問題)。
  ⟹ **(b) が唯一の道。F へ「`hyp.P ⊓ hyp.U = ⊥` を Hypothesis に追加」を提案** (issue 2009 + cross-lane notes)。
  F が追加すれば H は `coprime_card_U_card_P_of_disjoint` (Hall 論法、~30 行) → SZ → Phase 2 を一気に進められる。

## Phase 構成 (依存順)

### Phase 0 — hyp.U coherence (上記)。obligation ① の base。
### Phase 1 — coherence bridge (obligation ① の L~S 除外) [Phase 0 後]
hyp.U complement → SZ 共役 `hyp.U ~ typeP.U` (S 内, `exists_conj_le_of_isComplement'_of_coprime`)
→ normalizer 同変性 + `normalizer_not_le` で `¬ N_G(hyp.U) ≤ S`。
### Phase 2 — obligation ① `exists_typeI_maximal_overNormalizer_U` (13.17.a/b)
- C1 存在: `∃ maximal L ⊇ N_G(U)` (N_G(U)≠⊤ ← typeP.U≠⊥ coherence + G simple) = `Finite.exists_le_maximal`。
- C2 type-I: `hyp.theorem88_caseB L hLmax` trichotomy + Phase 1 (L~S 除外) + L~T 除外
  (|L_F|=q^p [T-side cite] → W₁⊆L_F → [U,W₁]=1, (13.2.a) UW₁ Frobenius 矛盾)。
- C3 U⊆L_F: (8.17.a) |L_F| coprime to q → W₁∩L_F=1; U∩L_F=1 なら UW₁ FPF → (9.1) 矛盾 [§8/§9 cite]。
### Phase 3 — Huppert [H] V.8.18 (H 単独・並列可・obligation ② を de-risk)
奇数位数 Frobenius complement ⟹ 素数位数部分群正規 (Z-群構造)。自己完結古典、Isaacs Ch06 Frobenius
機構から形式化。**repo 不在**ゆえ新規。reusable。
### Phase 4 — obligation ② `typeI_overNormalizer_complement` (13.17.c) [Phase 3 後]
complement E (⊇W₁) は odd Frobenius complement → Phase 3 で素数位数正規 → E⊆N_G(W₁)⊆QW₂ [(13.16) cite]
→ Sylow cyclic [BG 3.9 `S03g_Thm310`] → E=W₁ or |E|=pq=W₁W₂^y。W₁ 枝は (14.5) 除外。

## leaf 分類

| leaf | 種別 | 手段 |
|---|---|---|
| hyp.U coherence (P⊓U=⊥) | **crux base** | (a) §13 card 導出 or (b) F 協調 enrich |
| SZ bridge → ¬N_G(U)≤S | H 単独 | 既存 infra cite |
| ∃ maximal L⊇N_G(U) | H 単独 | exists_le_maximal |
| trichotomy glue → type-I | H 単独 | theorem88_caseB + rule-outs |
| Huppert [H] V.8.18 | H 単独・新規 | Isaacs Ch06 から形式化 |
| 補元 E 構造 (Phase 4) | H 単独 | Huppert + cite |
| \|P\|=p^q, (8.17.a), (9.1), \|L_F\|=q^p, (13.16) | cite sorried §13 | 安定 signature |
| basic_structure char fields 等 | **Lane B** | Dade 待ち (cite のみ) |

## 次の一手 (優先順)

1. **Phase 0 (a)**: `P ⊓ hyp.U = ⊥` の §13 card 導出 feasibility 調査 (`|derivedInG S|` 評価)。
   可なら Phase 1 へ直結。不可なら (b) を F に提案 (cross-lane)。
2. **Phase 3 (Huppert [H] V.8.18)**: Phase 0 と独立・H 単独で並行着手可。obligation ② を de-risk。
3. Phase 0 解決後 → Phase 1 → 2、Phase 3 後 → 4。

## cross-lane 伝達 (hub / B / F) — 2026-06-19

> 伝達機構 = 共有 notes/issue + cron merge (lane↔lane の `send_message` は unsupervised lane で
> 不可、[[cross-lane-sync-via-notes]])。本節 + issue 2009 + commit が main へ流れ hub/B が読む。

### ⚠ S15_SAndT の §13 sub-split (hub / B 宛)
`cite_split_three_lanes.md` は名目上 **B = S15_SAndT (§13 char)** とするが、H の方針① は同ファイルの
**(13.17) `typeII_overNormalizer_frobenius` = 構造的 producer** (type-I Frobenius 構造、POLE-2 が cite)
を扱う。**提案する §13 sub-split**:
- **H = §13 構造 producer**: (13.17) typeII_overNormalizer_frobenius + その obligation
  (exists_typeI_maximal_overNormalizer_U / typeI_overNormalizer_complement) + (13.16) normalizer_W1
  等の構造補題 + 本プログラムの Phase 0-4。
- **B = §13 char producer**: basic_structure の **char fields** (tauS_eq_induction/A0S_TI)、(13.3)以降の
  CharacterDegreeData / μ_j / Dade grid、S_coherent、coherence/Dade 本体。
- **即時衝突なし** (B は現在 §6 (6.8) bootstrap、§13 未着手)。B が §13 char に到達したら hub が
  prefix-split (構造 prefix を H-leaf、char を後続) で分離可。H は当面 S15_SAndT で構造 producer を進める。

### H→B cite 関係 (B 宛)
H の §13 構造証明は **B の (sorried) §13 char/構造 producer を安定 signature として cite**:
- `basic_structure` (13.2) の構造 fields (P_elementaryAbelian / P_order |P|=p^q / u_bound)
- (9.1) Wielandt FPF (S11=Pf§9)、(8.17.a) (S10=Pf§8)
これらが B/将来セッションで unconditional 化されると H の構造 producer も自動 unconditional 化。
**逆向き**: H が landing する §13 構造 producer (13.17 等) は B の §13 char (Dade grid が type-I L の
Frobenius 構造を前提) からも cite され得る。

### ⚠ Phase 0(b) F-ask 確定 (2026-06-20、hub / F 宛、最優先)
**Phase 0(a) [H 単独 disjoint 導出] は infeasible と確定** — hyp.U の under-constraint は carrier の
faithfulness 問題で、§13 構造論では塞げない (hyp.U=M' でも全 Hypothesis フィールドを満たす)。
⟹ **(b) が唯一の道。F への ask (最小・確定)**:
> **`Hypothesis` (S15_SAndT:73) に 1 フィールド `P_inf_U_eq_bot : P ⊓ U = ⊥` を追加**。
> carrier 変更ゆえ producer `sectionSixteenHypothesis_of_inputs` (FeitThompson.lean) の対応が要る (**F 領域**)。
これだけで H 側が完結する (Phase 1 SZ 補題は landing 済 `exists_conj_typeP_U_of_coprime`、coprimality は
disjoint から Hall 論法で導出 [上記 Phase 0 診断])。F が追加すれば Phase 2 (obligation ①) が一気に解禁。
**真の構成可能性**: P⊓U=⊥ は実際の数学で真 (U は S' 内で P=S_F の Hall 補元、(13.1.b))。F は §16 producer
構成サイトで U を補元として取れば供給可能 (scaffold でなく faithful enrich)。

## Phase 1 進捗 (2026-06-19 cont.)

- ✅ **transfer 部 `not_normalizer_U_le_S` 完成** (commit `9a8ffcde`, sorry-free): SZ 共役 `hconj`
  (∃ x∈S, U=conj x•typeP.U) を hypothesis に取り、`¬N_G(U)≤S` を `normalizer_conj_smul` +
  `conj_smul_eq_self_of_mem_normalizer` + `pointwise_smul_le_pointwise_smul_iff` で証明。
- ✅✅ **SZ 共役 step `exists_conj_typeP_U_of_coprime` 完成** (sorry-free + axiom-clean
  `[propext, Classical.choice, Quot.sound]`, full build 3868 jobs ~49s)。`Nat.Coprime |U| |P|` 仮説から
  `∃ x∈S, U=conj x•typeP.U` を証明。**Phase 1 完了**。5 API 摩擦の確定した解 (前回の予測どおり):
  1. M'=`derivedInG hyp.S` を**リテラルで使用** (fix iii: `set` は projection 型内の `derivedInG hyp.S` を
     畳まないので不使用)。P≤M'/U≤M' = `S_deriv_eq_PU`+`le_sup_left/right`、typeP.U≤M'=`U_le`、
     M'≤S = `Subgroup.map_subtype_le _` (fix i: `derivedInG_le` は不在、これが正)。
  2. **solvability** (fix ii): `IsSolvable ↥S`=`hG.solvable_of_mem_maximalSubgroups hyp.S_maximal` →
     `IsSolvable ↥M'`=`solvable_of_solvable_injective (Subgroup.inclusion_injective hM'_le_S)` →
     SZ の `hMsolv` (P.subgroupOf M' solvable) は `inferInstance` (subgroup-of-solvable)。
  3. **P◁M'** (fix iv): `(Subgroup.normal_subgroupOf_iff_le_normalizer hP_le).mpr` (mathlib、`K ≤ normalizer H`
     の **Set 形**: 本 repo の `Subgroup.normalizer` は `(Set G) → Subgroup G`)。N_G(P)≥M' は
     `OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S` (**要 fully-qualify**、bare 不可)。
  4. complements in ↥M': hKcompl=`tdata.typeP.derived_complement` (goal で `rw [hPH]`、hPH: P=typeP.H);
     hUcompl=`isComplement'_of_disjoint_and_mul_eq_univ` (disjoint=`disjoint_iff.mpr (Subgroup.inf_eq_bot_of_coprime hcop'.symm)`;
     mul=univ=`Subgroup.normal_mul Pn Un` を `hPnUn_sup`+`coe_top` で書換)。hPnUn_sup=`Pn⊔Un=⊤` は
     `← subgroupOf_sup` + `S_deriv_eq_PU.symm` + `subgroupOf_self`。
  5. card-eq |U|=|typeP.U|: 両 `IsComplement'.card_mul` (=card ↥M') を `Nat.eq_of_mul_eq_mul_left hPpos` で約分
     → card Un=card Kn → `subgroupOfEquivOfLe` の `Nat.card_congr` で `hyp.U`/`typeP.U` へ。
  6. map-back (fix v): `Subgroup.map_map` + intertwine `hintertwine`(`(derivedInG S).subtype∘conj x = conj↑x∘subtype`,
     `ext ⟨y,hy⟩; rfl`) + `← map_map` + `map_subgroupOf_eq_of_le htU_le` + `hsmul_map`(`conj↑x•K=K.map (conj↑x).toMonoidHom`,
     `pointwise_smul_def; rfl`)。等号化は `Subgroup.eq_of_le_of_card_ge hle (le_of_eq …)` + `hconj_card`(conj は card 保存,
     `card_map_of_injective (conj↑x).injective`)。
  - **先例** = `OddOrder/BG/Ch3_MaximalSubgroups/S11_MsigmaANormal.lean:226-290` (SZ → set E₁/Esub map-back)。
- **▶ 次 = Phase 2** (`exists_typeI_maximal_overNormalizer_U`, S15 sorry): `not_normalizer_U_le_S` を
  `exists_conj_typeP_U_of_coprime` で配線 (hconj→coprime) で L~S 除外 → + L~T 除外 + U⊆L_F →
  exists_typeI_maximal_overNormalizer_U close。⚠ coprime `|U| |P|` は enriched Hypothesis (Phase 0(b), F 待ち)
  か §13 card 導出 (Phase 0(a)) を要 — Phase 2 着手時に再判定。

## Phase 2 進捗 (2026-06-20) — ✅ skeleton landing (assembly 証明 + 4 gate 隔離)

`exists_typeI_maximal_overNormalizer_U` を **gated-endpoint skeleton** 化 (ユーザー裁可)。
Pf (13.17.a/b) を原文精読 (mmd `04.15_…S_and_T.mmd` L286-288) し正確な論法を確定。
**assembly は sorry-free 証明**、深い §13 content を 4 gate に隔離 (full build 3868、real sorry 134→137):

**✅ 証明済み assembly**:
- `hcop` = `coprime_card_U_card_P_of_disjoint hyp tdata hdisj` (Hall 機構、landing 済)
- `hNUS : ¬N_G(U)≤S` = `not_normalizer_U_le_S ∘ exists_conj_typeP_U_of_coprime ∘ hcop` (Phase 1 配線)
- `hUne : U≠⊥` (`U=⊥⟹M'=P`、`TypePData.fitting_lt_derived` に矛盾)
- `hUleS : U≤S` / `hUneTop : U≠⊤` (S maximal) / `hNUtop : N_G(U)≠⊤` (`_hG.simple.eq_bot_or_eq_top_of_normal`
  + `normalizer_eq_top_iff`)
- `∃ maximal L⊇N_G(U)` (`Finite.exists_le_maximal (·≠⊤)` → `Maximal`→`IsCoatom` を `lt_irrefl`+`lt_of_lt_of_le` で)
- (8.8.b4) trichotomy dispatch (`hyp.theorem88_caseB L hLmem`)

**残 4 gate (依存順 + 攻略)**:
1. **`hdisj : P ⊓ U = ⊥`** — Phase 0(b) F-ask (carrier faithfulness、cross-lane、上記)。
2. **L~S 除外** (`_hLconjS`) — Pf: `U^g≤S` は S の Hall 部分群 → S 内で U と共役 (Hall C `hall_C`) → 共役子
   `gx∈N_G(U)` → `N_G(U)=N_G(U)^{gx}≤L^{gx}=S` が `hNUS` に矛盾。**要 "U は S の Hall 部分群"** (新 §13 事実、H 次手)。
3. **L~T 除外** (`_hLconjT`) — Pf: `|L_F|=q^p` [T-side cite] → `W₁⊆L_F` (W₁⊆N_G(U)⊆L) → U が L_F 正規化 + u∤q
   → `[U,W₁]⊆L_F∩U=1` が (13.2.a) `UW1_frobenius` (`basic_structure`) に矛盾。
4. **U⊆L_F** (type-I 枝) — Pf (13.17.b): (8.17.a) で `q∤|L_F|` → `W₁∩L_F=1`; `U∩L_F=1` なら `UW₁` が L_F に
   FPF 作用 → (9.1) `S11` で `|L_F|=1` 矛盾 → `U∩L_F≠1` → `U⊆C_L(U∩L_F)⊆L_F`。

**▶ H 次手 = L~S gate の "U Hall in S"**: これが H 単独で出れば L~S 除外 (gate 2) を sorry-free 化できる
(Hall C `hall_C` は既存)。"U は S の (κ∪σ)'-Hall 補元" の形式化 — type-data / σ 構造から導出可能性を調査。
gate 3/4 は §8/§13 cite (basic_structure/(8.17.a)/(9.1))、gate 1 は F 待ち。
