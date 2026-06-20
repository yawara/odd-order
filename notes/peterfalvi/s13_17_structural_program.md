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

## Phase 2 cont. (2026-06-20²) — ✅ gate 2 構造論コア sorry-free + 🔑 残差は W1=κ carrier-coherence (F-ask)

gate 2 (L~S) の**構造論 (Hall 共役論法) を sorry-free + axiom-clean で landing** (commit `4357cc7d`)。
残差を Pf 原文どおりの 1 本 `Coprime |U| [S:U]` (=「U is a Hall subgroup of S」) に縮約。

**✅ 新規 (両 axiom-clean、汎用・再利用可、S15_SAndT.lean)**:
- `normalizer_le_of_isHall_subgroupOf_of_conj` — (13.17.a) 構造論コア: U が可解 V の π-Hall・`L^g=V`・
  `N_G(U)⊆L` ⟹ `N_G(U)⊆V`。証明 = `U^g⊆V` 同位数 π-Hall → Hall 共役 (`exists_conj_eq_of_isHall_subgroupOf`)
  で `w∈V, (U^g)^w=U` → `wg∈N_G(U)` → `N_G(U)=N_G(U)^{wg}⊆L^{wg}=V`。
- `isHall_subgroupOf_primeFactors_of_coprime_index` — `H≤V` で `|H|⟂[V:H]` ⟹ `H` は `π(|H|)`-Hall。

**🔑🔑 知見 (LAUNCH/上記「次の一手」見積りの訂正)**: gate 2 残差は **「~40-60 行 H 単独 basic_structure cite」では
閉じない**。深掘りで以下が確定:
- `Coprime |U| [S:U]` は `[S:U]=[S:M']·|P|` で分解。`|U|⟂|P|` は `hcop` (済) だが **`|U|⟂[S:M']` が問題**。
- `[S:M'] = |tdata.typeP.W1|` (`card_W1_eq_derived_index`、prime)。`|U|⟂[S:M']` には **`tdata.typeP.W1` が
  κ(S)-Hall であること** (`IsHallSubgroup (kappa S) (W1.subgroupOf S)`、`coprime_card_derived_kappaHall_of_isComplement'`
  の入力) を要する。= **BG↔Pf の「W₁ = κ(S)-Hall」同定**。
- ⚠ **`BG.Ch4.S14.IsTypeP` (`(kappa M).Nonempty`) と Pf `GroupTheory.IsTypeP` (`Nonempty TypePData`) は別述語**。
  BG の κ-Hall 補題群 (`typeP_derivedInG_isComplement_kappaHall` 等) は前者 + cyclic κ-Hall K を要求。
- ⚠ **`Section16MaximalPair` (lane-f) では `K_hall`/`S_typeP`/`Z_cyclic` はすべて carrier フィールド** (enrich が供給)。
  bare `TypeIIData hyp.S` からは導出されない。⟹ **W₁=κ 同定は carrier-faithfulness、§13 構造論で塞げない**。
- **∴ gate 2 残差 = gate 1 (hdisj) と同種の F-ask**。

### Phase 0(b) F-ask 改訂 (gate 1 + gate 2 を一括で塞ぐ carrier enrich)
F への ask を以下に統合・拡張 (issue 2009 + cross-lane):
- **gate 1**: `P_inf_U_eq_bot : hyp.P ⊓ hyp.U = ⊥` (既出)。
- **gate 2 (新)**: `hyp.W1` を `derivedInG S` の κ-Hall complement に pin。最小形は
  `W1_complements_derived : IsComplement' ((derivedInG S).subgroupOf S) (W1.subgroupOf S)`
  (⟹ `[S:M']=|W₁|`)。これと `basic_structure.UW1_frobenius` (`Coprime |U| |W₁|`、citeable sorried producer) で
  `Coprime |U| [S:M']` ⟹ `Coprime |U| [S:U]` (`isHall_subgroupOf_primeFactors_of_coprime_index` 経由) ⟹ gate 2 close。
- **真の構成可能性**: いずれも実数学で真 (`hyp.U`/`hyp.W1` は type-P 構造の真の補元; (13.1.b))。F は §16 producer
  構成サイトで補元として取れば faithful に供給可 (scaffold でない)。

### gate 2 を H 単独で閉じる代替 (非推奨・大物)
W₁=κ 同定を H 単独で証明する道もある: `(kappa S).Nonempty` を `TypeIIData` から導出 (τ₁∪τ₃ の prime + 中心化子条件)
+ cyclic κ-Hall 存在 → `typeP_derivedInG_isComplement_kappaHall`。但しこれは深い §14 構造論 (W₁ の prime が κ に
入ることの証明) で、carrier enrich (F-ask) の方が遥かに安価。**F-ask を推奨**。

**▶ H 次手**: gate 2 残差は F 待ち (上記 enrich)。残る H 単独候補 = gate 3 (L~T 除外、`basic_structure.UW1_frobenius`
+ |L_F|=q^p [T-side cite]) / gate 4 (U⊆L_F、(8.17.a)+(9.1) cite) / Phase 3 (Huppert [H] V.8.18、obligation ②、並行可)。

## Phase 2 cont. (2026-06-20³) — ✅ gate 3 構造論コア sorry-free + B1/B2 未記載 signature 追加 (issue 2013)

issue 2013 の (B) 未記載 signature を `S15_SAndT.lean` に追加し、gate 3/4 の振り分けを (A)/(B) に正した。

**(A) cite 可 (signature 既存・sorried producer)** — gate 3 = `basic_structure.UW1_frobenius` (13.2.a) /
gate 4 = `wielandt_fixedPoint_frobenius` (9.1) は従来どおり cite 可。

**(B) 新規 signature (今回追加、すべて faithful sorried producer)**:
- **B1 `card_Q_eq`** (`|Q|=|T_F|=q^p`) — `basic_structure.P_order` の S↔T 対称版。`:= sorry` (§13 機構 gate)。
- **B1' `tConjugate_fitting_data`** — L (conj T) に対し `|L_F|=q^p ∧ W₁≤L_F ∧ L_F⊓U=⊥`。`card` 部は B1 + `M_F`
  同変性 (`maxNilpotentNormalHall_pointwise_smul`) の transfer。gate 3 コアが消費する 3 事実を束ねた producer。`:= sorry`。
- **B2 `card_LF_coprime_pq`** (type-I・非共役 L ⟹ `Coprime |L_F| (p*q)`) — (8.17.a)。`bgTheoremE_cover_data`
  (BG Theorem E、owner=F、sorried) の `primeFactors_disjoint` から derive する派生補題。`:= sorry`。
- **B2' `typeI_overNormalizer_U_le_fitting`** (type-I L ⟹ `U≤L_F`) — gate 4 の FPF コア (W₁∩L_F=1 → UW₁ FPF →
  (9.1) で |L_F|=1 矛盾 → U⊆C_L(U∩L_F)⊆L_F) を束ねた producer。`:= sorry` (FPF 作用構成が深い)。

**✅ gate 3 (L~T) 構造論コア = sorry-free**: `tConjugate_fitting_data` を仮説として `⁅U,W₁⁆≤U`
(`commutator_le_of_le_normalizer`+`W1_normalizes_U`) ∧ `⁅U,W₁⁆≤L_F` (`commutator_mono`+`W₁≤L_F`+`U≤L≤N(L_F)`,
`maxNilpotentNormalHall_le_normalizer`) ⟹ `⁅U,W₁⁆≤L_F⊓U=⊥` ⟹ `U≤C(W₁)` ⟹ 非自明 u,w で
`w u w⁻¹=u` が `UW1_frobenius.conj_frobenius` に矛盾。残差 = B1/B1' のみ (`exists_typeI_maximal_overNormalizer_U`
の `_hLconjT` 枝本体に sorry なし)。

**⚠ gate 4 (type-I) 構造論コア = producer 委任 (B2')**: FPF 作用 `CoprimeFrobeniusAction (↥(U⊔W₁)) (↥L_F)`
の構成 + FPF 性 (`fixedByUE=⊥`) + 自己中心化 (`C_L(U∩L_F)⊆L_F`) が深く、本 issue の予算では sorry-free 化せず
`typeI_overNormalizer_U_le_fitting` (`:= sorry`) に隔離 (`hLI` 枝本体は 1 行 `exact`、sorry なし)。B2 (`card_LF_coprime_pq`)
を proof path として docstring に明示。非共役性 (IsTypeI L ⟹ ¬conj S/T) の補題 (型一意性・共役不変) が repo に無く、
これも producer 内に内包。⟹ gate 4 の sorry-free 化は (a) 型一意性補題 + (b) FPF 作用構成インフラ (cf. `S08_*` の
`MulDistribMulAction H ((MulAut.conjNormal).comp W1.subtype)`) を要する別タスク。

**count-sorry**: 137 → 139 (新 producer 4 本 − target 本体から消えた gate 3/4 の 2 sorry)。full build 3869 jobs green。

## gate 4 攻略精密化 (2026-06-20⁴, lane-h 再開) — infra 棚卸し + piece 6 landing

main 取込後 (HUB の issue 2013 解決済) に gate 4 (`typeI_overNormalizer_U_le_fitting`, U≤L_F) を精読。HUB の
「型一意性補題が repo に無い」評価を**一部訂正** — exclusivity は既存。原文 mmd L288 の 6 ピース分解と infra 棚卸し:

| piece | 内容 | infra 状態 |
|---|---|---|
| 1 | `L` 非共役 S/T (IsTypeI ⟹ ¬conj) | ✅ **DONE (2026-06-20⁵)**: `not_conj_of_isTypeI_of_isTypeNonI` (sorry-free) = `isTypeI_of_conj` (新 infra) + `not_isTypeI_of_isTypeNonI` (既存) |
| 2 | `Coprime |L_F| (p·q)` | `card_LF_coprime_pq` (B2、sorried producer、cite 可) |
| 3 | `W₁ ⊓ L_F = ⊥` | piece 2 + |W₁|=q prime、clean (~10 行) |
| 4 | `L` Frobenius kernel L_F | `S14.typeI_frobenius` ((12.7) `TypeIFrobeniusData`、Frobenius 内蔵) |
| 5 | `U∩L_F=⊥` ⟹ FPF ⟹ Wielandt ⟹ |L_F|=1 矛盾 ⟹ `U∩L_F≠⊥` | ❌ **最深**: `CoprimeFrobeniusAction (UW₁) (L_F)` 構成 + FPF (`fixedByU=⊥` 等)。coprimality は **L の Frobenius (kernel⊥complement, `coprime_card_kernel_complement`)** から (card_LF_coprime_pq でなく) |
| 6 | `U∩L_F≠⊥` ⟹ `U⊆C_L(U∩L_F)⊆L_F` | ✅ **landing 済** (`le_kernel_of_isMulCommutative_of_inf_ne_bot`) |

**✅ piece 6 landing (2026-06-20⁴)**: `le_kernel_of_isMulCommutative_of_inf_ne_bot` (S15_SAndT, sorry-free,
汎用 Frobenius 補題、`Ch06` へ hoist 可): Frobenius 群 L (kernel N) で abelian U が N と非自明交差 ⟹ U≤N。

## ✅ piece 1 DONE — IsTypeI 共役不変 (2026-06-20⁵, commit `d83d56be`)

「型一意性補題が repo に無い」評価を覆し、Peterfalvi 型分類が **`MulAut G` 不変**であることを正面から形式化。

**新 reusable infra `OddOrder/GroupTheory/MaximalSubgroupTypeConj.lean`** (331 行, axiom-clean, AxiomsCheck 登録):
- **MulAut-equivariance toolkit** (汎用・再利用可): `card_pointwise_smul`/`pointwise_smul_eq_bot_iff`/
  `isCyclic_pointwise_smul`/`isMulCommutative_pointwise_smul`/`exponent_pointwise_smul`/
  `centralizer_pointwise_smul`/`normalizer_pointwise_smul`/`image_sharpSubgroup`/`isTISubset_pointwise_smul`/
  `isComplement'_map_of_mulEquiv`/`isFrobeniusGroup_map_of_mulEquiv`/`rank_of_mulEquiv`/
  `opiCoreInG_pointwise_smul` (S07 private `conj_smul_opiCoreInG` を public 再証明)。
- **型データ transfer**: `TypeFData.conj` (15 field 全 transfer; `map_subgroupMap_subgroupOf` で subgroupOf
  field [complement/U1_normal/frobenius_HU0] を処理) / `TypeIData.conj` (alternative 3 枝も transfer) /
  `isTypeI_pointwise_smul` / `isTypeI_of_conj`。TypeFData は `derivedInG` 非依存ゆえ nilpotent transfer 不要。

**gate 4 配線** (`S15_SAndT.lean`):
- `not_conj_of_isTypeI_of_isTypeNonI` (sorry-free proof; transitively `not_isTypeI_of_isTypeNonI` の §16
  classification sorry に依存ゆえ axiom-clean ではない=honest upstream gate)。
- **`typeI_overNormalizer_U_le_fitting` を sorry-free 化**: piece 1 で L~S/L~T 非共役を証明・consume →
  `card_LF_coprime_pq` cite → 残 FPF を **`typeI_U_le_fitting_of_coprime`** (pieces 4-6 隔離, sorried) に押し出し。
- 実 sorry 138 不変 (piece 1 = assumed hyp → proven lemma の置換; CLAUDE.md「進捗の測り方」)。

**⟹ gate 4 の残 = piece 5 のみ** (`typeI_U_le_fitting_of_coprime` 本体): FPF 作用構成
(`CoprimeFrobeniusAction (UW₁) (L_F)` + `wielandt_fixedPoint_frobenius` [sorried §9] 配線 + piece 6 の
↥L bookkeeping)。piece 3/4 は同 producer 内 clean glue。U abelian は `tdata.U_commutative` +
hyp.U~typeP.U 共役 (新 infra の IsMulCommutative transfer) から。**最深・multi-session**。
gate 1/2 は依然 F-ask (hdisj / W₁=κ carrier-faithfulness)。

## ✅ piece 5 の (9.1) FPF engine DONE (2026-06-20⁶, commits `6dd849ed`/`50b8b9fe`)

`typeI_U_le_fitting_of_coprime` の FPF 核心を **reusable engine 化** (`CoprimeAction.lean`, Wielandt sorry のみに
bottom-out)。原文 (mmd L288) 精読で論法確定: 「W₁∩H=1。U∩H=1 と仮定 → UW₁ が H に FPF 作用 → (9.1)|H|=1 矛盾」。

**新 3 補題** (`CoprimeAction.lean`):
- `coprimeFrobeniusAction_card_eq_one`: `fixedByE=⊥ ∧ fixedByU=⊥ ⟹ |H|=1` (既存 `wielandt_fixedPoint_trivial_U_fixed`)。
- `IsFrobeniusGroup.centralizer_inf_kernel_eq_bot_of_not_mem` (**axiom-clean**, AxiomsCheck 登録): Frobenius 核 N の
  非核元 g∉N は `C_L(g)⊓N=⊥` (`centralizer_kernel_le`)。FPF 作用の engine。
- **`isFrobenius_kernel_eq_bot_of_frobenius_subgroup`** (generic engine): 有限 Frobenius 群 L (核 N) に
  N と自明交差する Frobenius 部分群 UE (`U⊓N=E⊓N=⊥`) が coprime 作用 ⟹ **N=⊥**。証明 = mathlib
  `MulDistribMulAction (normalizer N) N` で φ 構成 (N◁L、作用は共役で rfl 展開) → U/E 非自明元 ∉ N で
  fixedByU=fixedByE=⊥ → combinator。Wielandt のみ依存。

## ✅✅✅ piece 5 完成 — typeI_U_le_fitting_of_coprime sorry-free (2026-06-20⁷, commit `753e9722`)

S15 application を完遂し `typeI_U_le_fitting_of_coprime` を **sorry-free 化** (実 sorry 138→137)。
**engine 経由で sorried Wielandt formula のみに bottom-out**。gate 4 の H 構造論 (pieces 1,3,5,6) 完了。

**engine を G-ambient 化** (`CoprimeAction.lean`): `isFrobenius_kernel_eq_bot_of_frobenius_subgroup` を
「Frobenius 群 Lsub≤G、Frobenius 部分群 UE≤Lsub を自然な ↥(U⊔E)[G] 形で受ける」形に書換 — juggling を
lifting で engine 内に封入し **caller は basic_structure.UW1_frobenius を直接供給** (subgroupOf transfer 不要、
当初 crux 視した hUE transfer を回避)。+ reusable coprimality 補題 2 本 (`coprime_card_of_inf_kernel_eq_bot`
[↥L] / `_le` [G-ambient]): 核と自明交差する部分群は核と coprime (`card_dvd_of_injective`+`coprime_card_kernel_complement`)。

**S15 application** (`typeI_U_le_fitting_of_coprime`):
1. piece 3 `W₁⊓L_F=⊥` (`_hcop`→`Coprime |L_F| q`→`inf_eq_bot_of_coprime`)。
2. piece 5 `U⊓L_F≠⊥`: by_contra → engine を L=↥L で適用 (hFrob=typeI_frobenius / hUE=basic_structure 直接 /
   hcop=`|L_F|⟂|U⊔W₁|`=`|U|·|W₁|` [`IsComplement'.card_mul`] を 2 coprimality+`Nat.Coprime.mul_right` から /
   hsolv=maxNNH nilpotent) → `L_F=⊥` 矛盾 (frob.frobenius.ne_bot_kernel)。
3. piece 6 `U≤L_F`: `le_kernel_of_isMulCommutative_of_inf_ne_bot` を ↥L で (U abelian=bdata.U_commutative を
   `isMulCommutative_of_mulEquiv` で ↥L へ + piece 5) → `U.subgroupOf L≤L_F.subgroupOf L` → map back。

**⟹ gate 4 obligation ① (`exists_typeI_maximal_overNormalizer_U`) の H 構造論は全完了**。残 sorried 依存:
`card_LF_coprime_pq` (B2, BG Thm E, owner F) / `card_Q_eq`/`tConjugate_fitting_data` (gate 3 B1/B1') /
gate 1,2 (hdisj/hUhall_cop = F-ask) / Wielandt (§9)。**▶ 次 H = obligation ② `typeI_overNormalizer_complement`
(13.17.c)**: Frobenius 補元 E⊇W₁ が odd Frobenius complement → Huppert [H] V.8.18 (素数位数正規) →
E⊆N_G(W₁)⊆QW₂ [(13.16)] → cyclic Sylow [BG 3.9] → E=W₁ or |E|=pq。Huppert V.8.18 は repo 不在=新規 (Phase 3)。

## ✅✅✅ Phase 3 完成 — Huppert [H] V.8.18 b) 完全形式化 (2026-06-20⁸, commit `5a577c10`)

**obligation ② の核 ([H] Kapitel V Satz 8.18 b) = 「奇数位数 Frobenius complement の素数位数部分群は正規」)
を新規 leaf `OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean` (395 行) で完全形式化**。
sorry-free + axiom-clean + AxiomsCheck 登録 (full build 3844 jobs green, 実 sorry 137 不変)。reusable。

作用形式 `IsFrobeniusAction A U` ベース (Frobenius 入力は **order-pq cyclic 1 本のみ**
=`false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_mul_prime`; 残りは A 内在の Z-群論):
1. `isZGroup_of_isFrobeniusAction_of_odd`: 奇数位数 ⟹ Z-群 (各 Sylow cyclic、6.10+6.11)。
   ⟹ mathlib `IsZGroup` で N=commutator A cyclic normal、A/N cyclic、`coprime_commutator_index`。
2. `centralizes_commutator_of_card_prime_coprime`: r∤|N| の R は N を中心化 (coprime 分解
   `fixedPoints_inf_actionCommutator_eq_bot_of_abelian` + [N,R]≠⊥ なら R⊔S 位数 rs 非cyclic 矛盾)。
3. `normal_of_card_prime_of_isFrobeniusAction_of_odd` (+ `_isFrobeniusGroup_` 版 = (13.17.c) consumer 用):
   R^g≤R を r∣|N| (cyclic N 一意性) / r∤|N| (元論法: k r₀⁻¹=⁅g,r₀⁆∈N、ν^r=1⟹coprime で ν=1) で。
ローカル複製: `eq_of_card_eq_prime_of_isCyclic` (cyclic 素数位数一意性、BG 版を import 方向回避で複製) +
card 積補題 2 本 (BG S01/S12_E 複製)。

**▶ 残り = (13.17.c) assembly 本体** (Huppert を cite して |E|=pq ∧ ∃y∈Q W₂^y≤E を出す)。**未完。3 つの
独立した壁**:
- **(設計) complement choice 問題**: `typeI_overNormalizer_complement` は**任意の** `frob.complement` を取るが、
  原文証明は「W₁⊆E なる complement E を選ぶ」。Frobenius complement は全共役ゆえ |E|=[L:H]=pq の card 部分は
  共役不変だが、**`∃y∈Q W₂^y≤E` 部分は a∈L 共役で y₀↦a·y₀ となり Q 内に戻る保証がない** ⟹ 任意 complement では
  偽になりうる。解 = (a) 仮説 `W₁.subgroupOf L ≤ frob.complement` を追加 (原文に忠実) + consumer
  `typeII_overNormalizer_frobenius` で W₁ 含む complement の存在 (W₁ は q-部分群・W₁∩H=1 ⟹ ある complement に入る)
  を別途供給、or (b) 12.7 `typeI_frobenius` (現 sorried) を W₁ 含む complement を返す形に強化。**(a) 推奨**。
- **(cite) sorried 依存**: (13.16) `normalizer_W1` (N_G(W₁)=QW₂, S15:727 sorried) / (14.5) (S16, E=W₁ 除外) /
  BG Prop 3.9 cyclic Sylow (= `S03g_Thm310` 系、要確認)。
- **(構造) |E|∈{q,pq} 抽出**: E⊆QW₂ + cyclic Sylow + W₁⊆E から |E|=q or pq、第 2 case で Sylow 定理で
  W₂^y≤E (y∈Q)。pure group theory だが Sylow + coercion (↥L vs G) で中量。
レシピ: Huppert normality を `normal_of_card_prime_of_isFrobeniusGroup_of_odd` で cite
(W₁.subgroupOf E が位数 q ⟹ E 内正規 ⟹ E≤N_G(W₁))。
