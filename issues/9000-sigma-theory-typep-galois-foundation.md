---
id: 9000
slug: sigma-theory-typep-galois-foundation
title: "σ-theory 土台: typeP_Galois (Pf 9.7) の generic semilinear/near-field dichotomy"
created: 2026-07-01
---

# σ-theory 土台: typeP_Galois (Pf 9.7) の generic semilinear/near-field dichotomy

> **CLAIM (lane d, hub 裁定 issue 4014/`ft_lane_reallocation` 2026-07-01)**: generic σ-theory
> (semilinear/near-field) = `typeP_Galois` の土台を新 shared-infra leaf `OddOrder/GroupTheory/**`
> で実証明する。lane a §11 は typeP_Galois を再実装せず本 leaf を **cite**。他レーンは着手前に本 issue を scan。

## 🛑 重複発覚 → HUB 裁定案件 (2026-07-02, policy 8 適用)

**lane a が S11 で同じ typeP_Galois (9.7) Singer 機構を concurrent 構築していた** (claim-before-build の
search が見落とし — lane a のは Peterfalvi/S11 *所有 file* 内 subgroup-level ゆえ shared-infra scan に掛からず)。
これは policy 8 (重複発覚→hub 裁定) + hub 齟齬 (issue 4014 再配分が lane a の in-progress を勘案せず) の実例。

**重複 map**:
| math | lane a S11 (既存 commit) | 私の σ-theory leaf | 判定 |
|---|---|---|---|
| Galois Singer \|Ū\|∣p^q−1 | `isCyclic_card_dvd_of_aInvariant_irreducible_faithful_comm` (`e2a673bd`) | `card_dvd..._irreducible_fpf` | **重複** (両 SingerField wrap、subgroup vs module level) |
| FPF→coprime(\|Ū\|,p−1) | `5efa6b5c` | 同 (SingerField cite) | **重複** |
| refined \|Ū\|∣(p^q−1)/(p−1) | S11:4333 (`Nat.dvd_div_iff_mul_dvd`) | `card_dvd_cyclotomicQuotient...` + 算術核 | **重複** (Galois 側) |
| non-Galois \|Ū\|≤(p−1)^{q−1} | Clifford/Hpart 解析 (S11:4471+、別アプローチ) | imprimitive embedding + `card_le_pow_of_block_scalars` (psi core) | **非重複** (別 route) |
| 汎用算術 (`dvd_div_of_coprime_of_dvd_sub_one` 等) | inline | named 版 | 弱重複 (cite 可) |

**hub に defer する判断** (policy 8 step 3): σ-theory の home 一本化 — (i) lane a の subgroup-level を私の
generic module-level leaf に cite 化するか、(ii) 私の Galois leaf を撤退し lane a の subgroup 版に一本化するか、
(iii) 私は非重複な non-Galois imprimitive engine + psi core + 汎用算術のみ残すか。

**凍結** (policy 8 step 4): 重複 Galois piece (`SingerLineBound.lean` の module-level refined bound) は hub 裁定まで
**これ以上広げない**。非重複部 (non-Galois imprimitive engine `SemilinearImprimitiveBound.lean` の psi core +
embedding、`TypePGaloisUBound` dichotomy) は genuine ゆえ保持。lane d は hub 裁定待ちの間、別 on-spine 上流へ。

## ✅ HUB 裁定 (2026-07-02, cron tick) — home = lane d の generic module-level leaf

**決定: Galois-side Singer bound の home は lane d の generic module-level leaf に一本化** (option (i))。
lane d は Galois leaf (`SingerLineBound`) を**凍結解除**して canonical home とする。

**決め手 (generic が subgroup 版に決定的に優位)**: generic module-level lemma は **S-side (lane a の
`basic_structure.u_bound`) と T-side (lane c の `S16:166 v=(q^p−1)/(q−1)`、hub が 2026-07-02 に flag) の
両方に同一 lemma で効く**。lane a の subgroup-level 版 (`isCyclic_card_dvd_of_aInvariant_irreducible_faithful_comm`
等) は S-side 専用で T-side に効かない。σ-theory 再配分 (issue 4014 = lane d が generic σ-theory 所有・
他レーン cite) とも一致。

**lane a への指示 (dedup 実施、S11 は lane a 所有)**:
- 重複 3 定理 (`isCyclic_card_dvd_of_aInvariant_irreducible_faithful_comm` (`e2a673bd`)、
  FPF→coprime (`5efa6b5c`)、refined bound (S11:4333)) を **retire し lane d の generic leaf を cite**
  (`card_dvd_cyclotomicQuotient_of_faithful_irreducible_fpf` 等、必要なら thin subgroup→module adapter)。
- **保持**: genuinely 非重複な S11-specific 構造 feed (W₁ block 分解 / psi injectivity の構造部 =
  lane d generic engine への供給) + 非-Galois Clifford/Hpart route (別 route ゆえ当面共存、u_bound consumer は
  lane d の imprimitive engine を cite)。
- **S11 build-green 維持** (swap は merge gate + full build で強制)。急がば dup 凍結のまま cite 移行を優先。

**hub 自己反省 (齟齬)**: issue 4014 の σ-theory 再配分が lane a の S11 in-progress Singer work を勘案せず、
重複を生んだ (lane d 指摘は正当)。**policy 8 step 5 で再発防止済** (search を subgroup/module 両抽象跨ぎに +
再配分時に既存 in-progress を先に確認)。lane d に非はない (claim-search 手順は正しく踏んだ)。

**lane d**: Galois leaf 凍結解除・保持継続。dedup は lane a が S11 側で実施ゆえ lane d は待たず次 on-spine 上流へ。

## 目標

Coq `typeP_Galois := acts_irreducibly U Hbar 'Q` (PFsection9.v:323 = **Pf (9.7)**) の二分岐を
generic に供給する。`U` = abelian complement (repo: `S_U_commutative`)、`Hbar` = Frobenius-kernel
quotient (elementary abelian `p`-group、`F_p`-space、`q`-dim over the U-stabilized field)。

- **Galois** (`typeP_Galois_P`, 9.7.b): U 既約 ⟹ `Hbar ≅ F_{p^q}` 体、`Ubar ↪ F^×`、
  **`u ∣ (p^q−1)/(p−1)`** (U は line を固定しない ⟹ norm でなく projective に効く精緻化)。
- **non-Galois** (`typeP_Galois_Pn`, 9.7.a): U 非既約 ⟹ minimal submodule `H1` (`|H1|=p`)、
  `Hbar = \dprod_{w∈W1bar} H1^w` (q blocks を W1bar が cyclic に置換)、
  `a := |U : C_U(H1)|` が `a>1`・`a ∣ p−1`・`U/C_U(H1)` cyclic・`Ubar ↪ Z_a^{q−1}`
  ⟹ **`u ≤ (p−1)^{q−1}`**。

両分岐から下流 `basic_structure.u_bound` = `u ≤ (p^q−1)/(p−1)` が従う (`caseB_u_bound_arith`
= `(p−1)^{q−1} ≤ (p^q−1)/(p−1)` は既存 sorry-free、non-Galois 側 bridge)。また `c_eq_one` の
Galois 分岐 (Coq `FTtypeP_Ind_Fitting_reg_Fcore` の `typeP_Galois` boolP 分岐、20× cite) の
structural 入力。

## 既存 infra (dup 回避 — hub mandate scan 済 2026-07-01)

再利用する (再実装しない):
- `OddOrder/GroupTheory/RepresentationTheory/SingerField.lean`:
  - `nonempty_singerFieldData` / `SingerFieldData` (既約 abelian action → 体, `M ≃ F_p[C]/I`)。
  - `isCyclic_and_card_dvd_card_sub_one_of_faithful_irreducible` (**U cyclic + `u ∣ p^n−1`** = Galois の粗 bound)。
  - `exists_galoisField_repr` (GaloisField 表現)、`coprime_card_sub_one_of_faithful_irreducible_comm_fpf`。
  - cyclotomic 算術 `cyclotomicQuotient_not_dvd_pow_sub_one` / `pow_sub_one_dvd_of_dvd` 等。
- `RepresentationTheory/CyclotomicGaloisAction.lean` (`GaloisCharacter`)、`SkolemNoether.lean`、
  `CliffordMultiplicityOne.lean` / `CliffordSingleOrbit.lean` (Clifford imprimitivity)、
  `ExtraspecialSinger.lean`。
- `Peterfalvi/Appendices/NearFields.lean` (`NearField` 構造・`rightMulAction`・
  `exists_aInvariant_complement_of_elementaryAbelian`・`nearField_field_structure`) — Suzuki 2-rank 用だが
  near-field 構造の再利用可否を精査。

## gap (本 issue で実証明する generic 補題)

1. **Galois line 精緻化**: `isCyclic_and_card_dvd_card_sub_one_*` の `u ∣ p^q−1` を
   **`u ∣ (p^q−1)/(p−1)`** に絞る (U が F^× の scalar `F_p^×` と交わらず projective に効く =
   `U ∩ ⟨center⟩ = 1` / no-fixed-line)。SingerField の field 同型 + `F_p^× ≤ F^×` の index。
2. **non-Galois imprimitivity 分解**: 既約でない faithful abelian U-action on `F_p`-space `V`
   (dim = q, q prime, W1bar が q blocks を cyclic transitive 置換) ⟹ minimal block `H1` (dim 1)
   + `V = ⊕_{i<q} H1^{w_i}` + `a := |U:C_U(H1)| ∣ p−1` + `u ≤ a^{q−1} ≤ (p−1)^{q−1}`。
   Clifford (`CliffordSingleOrbit`) + block-permutation の算術。
3. **dichotomy 組立**: `acts_irreducibly U V` の decidable 分岐で 1/2 を束ねた generic
   `typeP_Galois_dichotomy` (lane a が Pf (9.7) instance で cite)。

## 完了条件

`OddOrder/GroupTheory/RepresentationTheory/` (or 新 sub-leaf) に上記 generic 補題群が sorry-free、
`lake build` 緑。lane a が Pf (9.7) `typeP_Galois_P/Pn` を本 leaf cite で薄く assemble できる signature。

## 進め方 (上流順)

- [x] step 0: 既存 SingerField/Clifford/NearField の被覆域を精読し gap 1-3 の正確な signature 確定。
      → Galois/abelian 側は SingerField が大きく被覆 (`isCyclic_and_card_dvd_card_sub_one` +
      `coprime_card_sub_one_..._fpf`)。gap = line 精緻化 + non-Galois imprimitivity + dichotomy。
- [x] step 1 (Galois): line 精緻化 `u ∣ (p^q−1)/(p−1)` — **DONE** (`SingerLineBound.lean`,
      `card_dvd_cyclotomicQuotient_of_faithful_irreducible_fpf` + 算術核
      `dvd_div_of_coprime_of_dvd_sub_one`、sorry-free、既存 SingerField 2定理 assembly)。
- [~] step 2 (non-Galois): imprimitivity 分解 + `u ≤ (p−1)^{q−1}`。
      - [x] **generic 算術 engine** (`SemilinearImprimitiveBound.lean`, sorry-free):
        `card_le_pow_of_injective_to_pi` (embedding → `|U|≤|M|^n`) +
        `card_le_pow_sub_one_of_injective_imprimitive` (injective `Ū↪Fin(q−1)→A`, `|A|=a`, `a≤p−1`
        → `u≤(p−1)^{q−1}`)。Coq `psi` embedding (`PFsection9.v:442`) の算術核。
      - [x] **cyclotomic-quotient bridge**: `pow_sub_one_le_cyclotomicQuotient`
        ((p−1)^{q−1}≤(p^q−1)/(p−1)) + `card_le_cyclotomicQuotient_of_injective_imprimitive`
        (imprimitive embedding → u≤(p^q−1)/(p−1))。**両分岐が同一結論に到達** (Galois=SingerLineBound、
        non-Galois=SemilinearImprimitiveBound)。
        ⚠ dup 記録: `pow_sub_one_le_cyclotomicQuotient` = S15 `caseB_u_bound_arith` と同内容。
        infra(GroupTheory)が正位置ゆえ後で S15 を本 leaf cite 化可 (S15=lane d dormant、後日)。
      - [x] **psi embedding injectivity core** (`card_le_pow_of_block_scalars`, sorry-free):
        block scalars `φ : Fin(n+1)→(Ū→*A)` + no-global-scalar (`hconst`) → ratio 埋め込み
        `x↦(φ_{i+1}(x)/φ_0(x))` injective → `|Ū|≤|A|^n=a^{q−1}`。Coq `psi` (PFsection9.v:442) の
        crux を generic 構成。lane a は block scalars φ を供給するだけ (module 分解から)。
      - [x] **generic block-scalar extraction** (`LineScalarCharacter.lean`, sorry-free, 2026-07-02):
        `lineScalarChar ρ hdim : U →* (ZMod p)ˣ` = 各 block (1-dim 𝔽_p-line) 上の U-作用の scalar
        character (homothety `𝔽_p ≃+* End(line)` 経由) + `lineScalarChar_smul` (`ρ u x = φ u • x`,
        hconst 変換用) + `card_dvd_sub_one_of_faithful_line` (faithful line → `|U|∣p−1`, `a∣p−1` の
        generic 版)。Coq `phi w` (PFsection9.v:442) の generic 核。**ExtraspecialSinger の private
        `card_dvd_sub_one_of_faithful_one_dim` を本 generic に dedup 済** (route B が cite)。
      - [ ] **残 (lane a assembly, W₁/Ū 依存)**: 構造的 block 分解 `Hbar=⊕H1^w` (Maschke 半単純
        instance 済 + W₁-permutation, |H1|=p, q blocks) → 各 block を `lineScalarChar` に渡して φ_i
        family を組む + `hconst` (Ū に nonidentity global scalar 無し = 型 P quotient 構造 = C=1
        Frobenius, `lineScalarChar_smul` で scalar 等式に変換)。scalar 抽出・`a∣p−1` は本 leaf 供給済。
- [x] step 3: dichotomy 組立 — **DONE** (`TypePGaloisUBound.lean`,
      `card_le_cyclotomicQuotient_of_faithful_fpf`、sorry-free)。IsSimpleModule で case-split:
      Galois 分岐は完全証明 (SingerLineBound)、non-Galois 分岐は `hReducible` hypothesis
      (caller が imprimitive engine で discharge)。
- [x] **step 3b: module-level 一発 entry (2026-07-02)** — **DONE** (`TypePGaloisUBound.lean`,
      `card_le_cyclotomicQuotient_of_blocks`、sorry-free): order-p subrepresentation family +
      hconst → `|U|≤(p^(n+1)−1)/(p−1)`。`lineScalarChar` 抽出 + `finrank_eq_one_of_card_eq_prime`
      (card=p→finrank=1) + `card_le_pow_of_block_scalars` + cyclotomic bridge を一本化。これで
      `hReducible` 枝が block 分解から discharge 可能に (lane a の interface = blocks + hconst のみ)。
      **σ-theory generic u_bound engine は本 commit で完成** (Galois/non-Galois 両分岐 + module-level
      entry)。残 = lane a の type-P block 分解 (`Hbar=⊕H1^w`) + hconst (=C=1 Frobenius) の供給のみ。

## 📣 lane a 向け cite signature (hub 裁定「typeP_Galois を再実装せず本 leaf を cite」)

`OddOrder.RepresentationTheory` namespace、`import
OddOrder.GroupTheory.RepresentationTheory.TypePGaloisUBound` で全て入る:

- **u_bound entry point**: `card_le_cyclotomicQuotient_of_faithful_fpf` —
  faithful fpf abelian U on M≅F_p^q → `|U| ≤ (p^q−1)/(p−1)`。Galois 分岐は内部証明済、
  非 Galois 分岐 `hReducible` は下記 engine で discharge。
- **Galois 分岐** (直接も使える): `card_le_cyclotomicQuotient_of_faithful_irreducible_fpf`
  (`|U|∣(p^q−1)/(p−1)`) / `card_le_cyclotomicQuotient_of_faithful_irreducible_fpf` の ≤ 形。
- **非 Galois engine (module-level 一発 entry, 推奨)**: `card_le_cyclotomicQuotient_of_blocks` —
  order-p subrepresentation family `B : Fin(n+1)→Subrepresentation ρ` (各 `Nat.card=p` = block H1^w)
  + `hconst` (nonidentity で全 block 同一 scalar 無し = C_U(M)=1 mod scalars) → `|U|≤(p^(n+1)−1)/(p−1)`。
  lane a は **block subrepresentation と hconst のみ供給** — scalar 抽出 (`lineScalarChar`)・ratio embedding・
  finrank=1 (`finrank_eq_one_of_card_eq_prime`)・算術は本 leaf discharge。`card_le_cyclotomicQuotient_of_faithful_fpf`
  の `hReducible` 枝はこれで discharge (`hReducible := fun _ => card_le_cyclotomicQuotient_of_blocks …`)。
- **非 Galois engine (low-level, φ 直接供給)**: `card_le_cyclotomicQuotient_of_injective_imprimitive` —
  imprimitive ratio embedding `Ū↪Fin(q−1)→A` (|A|=a, a≤p−1) → `|U|≤(p^q−1)/(p−1)`。block を自前で
  φ family 化したい場合。
- **block scalar φ_i + a∣p−1**: `RepresentationTheory.lineScalarChar ρ_i hdim_i : U →* (ZMod p)ˣ`
  (`LineScalarCharacter`) = block i (1-dim 𝔽_p-line) 上の scalar character。`lineScalarChar_smul`
  (`ρ u x = φ u • x`) で hconst を scalar 等式に変換、`card_dvd_sub_one_of_faithful_line` で
  `a=|U:C|∣p−1`。lane a は各 block の restricted representation を `lineScalarChar` に渡して
  `card_le_pow_of_block_scalars` の φ family を組む。

**残 (lane a assembly、W₁ 依存)**: 構造的 imprimitivity 分解 (`Hbar=⊕H1^w` の internal direct sum
+ 各 block U-invariant) + hconst (C=1 Frobenius)。generic scalar 抽出 (`lineScalarChar`)・算術・
embedding・両分岐 bound は本 leaf で供給済。

## ✅✅ σ-theory u_bound engine 完成 (2026-07-02) + kernel char 追加

`LineScalarCharacter.lean` に **`lineScalarChar_eq_one_iff`** 追加 (sorry-free): `φ u = 1 ↔ u が
line を pointwise 固定`。order-p block では「u が block の nontrivial char を固定 ⟺ u が block を
centralize」(𝔽_p^× free action) = Coq `inertia_irr_prime` (PFsection9.v:948) の module-level 版。
**lane a §9 caseA の order-p stabilizer=centralizer piece (issue 1012 の piece C) の module-framing
供給** (lane a の char-inertia framing の代替/補完として cite 可)。

⟹ σ-theory u_bound engine の generic API は完全 (Galois/non-Galois bound + block composite +
scalar char + kernel char + finrank bridge、全 sorry-free、full build green)。

## 🛑 HUB: lane d cluster boundary — 次 target 要裁定 (policy 7, issue 4014 と同型)

**状況 (code-level 検証済 2026-07-02)**: lane d の担当 (σ-theory + owned S15/BG) の on-feitThompson-path
ungated genuine work は **σ-theory engine 完成で枯渇**:
- shared `OddOrder/GroupTheory/**`: **sorry-free** (grep 検証)。σ-theory engine 完成。
- owned S15_SAndT_Setup: `u_bound`/`P_elementaryAbelian` は lane a §11 gated、char cascade は
  lane b coherence gated (issue 4014)。
- owned BG §14–16: 残 sorry は全 off-feitThompson-path (signalizer Thm D/E は char route で bypass、
  monolith/docstring/orphaned — issue 4014 で検証済)。
- 群論 spine (Isaacs/BG §1–13/Pf §1–9) は sorry-free。**残る FT work = 指標終盤 §10–16 = 全て
  active char lane (a §9–13 / b §12+coherence / c §14–16) の territory**。

**⟹ lane d の distinct な group/σ-theory 貢献は実質完了**。次の on-spine work は全て active char
frontier 内 = **carve せずに触ると dup** (σ-theory dup 前例 = issue 9000 冒頭)。これは cluster-complete
の **cross-cluster 再配分案件** (issue 4014 = ユーザー裁定の前例) で、within-cluster frontier 選択
([[feedback-decide-frontier-autonomously]] の射程) ではない。

**HUB/user 裁定を要する選択肢**:
- (A) lane d を binding γ (§14–16, lane c) の非衝突な structural 部分に signature-contract で carve
  (例: S16:166 v-bound / S16:3431/3511 IsCyclic — 現 issue 9001 で lane c 割当だが lane d の σ-theory
  leaf が直接 discharge 可能な構造結論)。
- (B) lane d が hub-confirmed 非-dup な char shared-infra を claim-build (lane a issue 1012 が flag した
  characterKernel-Subgroup 等、ただし lane a active caseA と重複回避の hub 確認要)。
- (C) lane d を off-path BG appendix (3 冊網羅の長期目標、FT 経路外) に回す — 現方針の FT-path 限定に反する。

lane d は裁定待ちの間 idle にせず、次 tick で main 同期して (a/b/c の進捗で新規 consumable が出たか /
hub 応答があるか) 再評価する。

## 🧾 claim 承継 (2026-07-02 hub、lane d 退役 — issue は OPEN 維持)

claim holder (lane d) は 3 レーン再編で退役。**claim は lane a に承継** (σ-theory tail、
`ft_lane_reallocation` 3 レーン再編節で fold 済):
- σ-theory generic engine (`SingerLineBound` / `SemilinearImprimitiveBound` / `LineScalarCharacter` /
  `TypePGaloisUBound` / `GaloisCharacter` / `SkolemNoether`) は **sorry-free で共有ゾーン凍結**
  (2026-07-02 comment-strip 検証済)。
- 残 = 上記「残 (lane a assembly、W₁ 依存)」= block 分解 `Hbar=⊕H1^w` + `hconst` 供給、および
  HUB 裁定の **S11 dup 3 定理 retire→generic leaf cite**。lane a が 11.8 chain の次の自然な区切りで
  文書順 (S11=§9 < §11.8) により着手する。
- 上記「🛑 HUB: lane d cluster boundary — 次 target 要裁定」節は退役で **moot** (選択肢 A/B/C は不要)。
(2026-07-02 hub、ユーザー委任レビュー)

## 参照

- Coq `coq/theories/PFsection9.v:323-560` (`typeP_Galois` / `typeP_Galois_Pn` (9.7.a) / `typeP_Galois_P` (9.7.b))
- issue 4014 (hub 裁定節) / `notes/meta/ft_lane_reallocation_2026_06_28.md` (lane d 再々配分行)
- 既存: `SingerField.lean` / `CyclotomicGaloisAction.lean` / `Clifford*.lean` / `NearFields.lean`
- 下流 consumer: `S15_SAndT_Setup.{basic_structure.u_bound, c_eq_one}` / lane a §11 (Pf 9.7 instance)

## ✅ S11 dup retire→cite 完了 (2026-07-03 lane a, commit e82638d9)

hub 裁定の dedup を実施。S11 の subgroup-level Singer shadow assembly を退役:
- 旧 `isCyclic_card_dvd_of_aInvariant_irreducible_faithful_comm` / 旧
  `coprime_card_sub_one_of_aInvariant_irreducible_faithful_comm_fpf` → **削除**。
  代替 = 変換専用 2 piece (`elabRepresentation_isSimpleModule_and_faithful`、
  `exists_addEquiv_asModule_fpf`) + thin entry 2 本 (`singerAdapter_isCyclic_card_dvd` /
  `singerAdapter_coprime_fpf`、各々 shared `SingerField` lemma を single cite)。
  旧 wrapper 2 本が重複させていた plumbing は 1 回に factor。
- `chiefFactor_caseB_image_dvd_norm` の inline 算術 → shared `SingerLineBound.dvd_div_of_coprime_of_dvd_sub_one`
  cite (算術核の single home 化)。
- ⚠ 実装知見: asModule 型の instance 解決は `[Module (ZMod p) (Additive K)]` **binder 文脈が必須**
  (consumer 側 letI 文脈では `Module (MonoidAlgebra …) asModule` synthesis が stuck) — thin adapter が
  inline 展開より正しい構造である技術的理由。
- full build green (3902 jobs) + AxiomsCheck OK (entries は singerAdapter 対に差替)。

**9000 残 (lane a)**: §9 caseA/Galois 側の block 分解 assembly (`Hbar=⊕H1^w` + `hconst` 供給、
9.8.d de-opacify と一体) — deep sub-phase、着手時は Coq `typeP_Galois` 精読から。

## 🧭 HUB 注記 (2026-07-06, 監視 hub) — 9000 typeP_Galois = char endgame の confirmed multi-consumer root gate

lane-c が (14.9) T-side を airtight 精査 (commit `92ab67f7`/`884a52e0`): `T_not_isTypeIV` を
complement-conjugacy transfer で `IsMulCommutative V` に還元 → **残 V-abelian は (11.9) `typeP_Galois`
char body そのもの**。決め手: σ engine `card_le_cyclotomicQuotient_of_faithful_fpf`
(TypePGaloisUBound:42) は `[CommGroup U]` を **typeclass 仮定で consume** し abelian を*証明しない* ⟹
`typeP_Galois → Ū cyclic → V cyclic → abelian` の char body が必須。c の全 (14.9) route (V-abelian /
s_side / basic_structure u_bound / ratio_le carrier) が本 gate = **§9 block 分解 (`Hbar=⊕H1^w`) +
(11.9) typeP_Galois char body** に収束と確定。

⟹ **本 9000 残 (§9 block 分解 + typeP_Galois) は now confirmed MULTI-consumer root gate** (char endgame の
pivotal critical-path):
- **lane-a** の (10.7)/(10.8) char capstone (issue 1017: prime-TI-reducible coherence が σ-theory §9 に gated)
- **lane-c** の (14.9) T-side type-IV 排除 (本 finding)
- generic module-level lemma は S-side (`basic_structure.u_bound`) と T-side (`S16 v`) の両方に効く (既述の裁定)

owner = **lane-a** (lane-d 退役で σ-theory tail 承継、9.8.d 一体)。lane-a が §9 を landing すれば a・c 両レーンが
unblock。**lane-c は cite-ready sorried-cite endpoint に整理済** (本 gate landing 後に cite; c は context 枯渇
ゆえ deep build は fresh session、待つ間の idle は禁止だが c は既に stop+report 済で policy 準拠)。
lane-a の frontier 選択は自律 (hub は dictate しない) が、本項目が **2 レーン + a 自身の capstone を同時 unblock
する最高レバレッジ σ-theory target** である事実を記録。

## 🔗 lane-c → 9000 downstream 依存の精緻化 (2026-07-07 lane c, post-horth)

**C の (14.9) coherence side は完了** (issue 9072 CLOSED, commit `c8875eb2` → 統合 `06d5a0cb`): `horth`
coherence carrier を実証明 (`T_typeIII_hyp07` + `irrSubcoherent`)。⟹ **9000 landing が unblock する C の
残 S16 consumer は coherence でなく以下に限定**:

1. **`T_not_isTypeIV_of_isTypeP1` (S16:1768) の `hVcomm : IsMulCommutative V`** — `typeP_Galois T →
   cyclic V → abelian V` char body。σ engine `card_le_cyclotomicQuotient_of_faithful_fpf` は `[CommGroup U]`
   を **仮定 consume** し abelian を*証明しない*ので、9000 の §9 block 分解 + typeP_Galois が必須
   (S16:1776-1803 に Coq `FTtype34_structure`/`PFsection9,11` の exact reduction を記載済)。これが landing
   すれば `T_isTypeIII_of_isTypeP1` → `T_isTypeP2` → `T_typeII` の type-determination chain が閉じる。
2. **`s_side_frobenius_kernel` (S16:4419) / `t_side_frobenius_kernel` (S16:4432)** — (9.7.b) 場-model
   (`FieldNormalizerData`/`TFieldModelData`, issue 2035/9000 sphere) の `derived_inf_centralizer_le_{P,Q}`。
   engine は proven (`S16_G0Coprime`); 欠けているのは field-model carrier (Q=Frobenius kernel の injective σ)。

C 側は **cite-ready sorried-cite endpoint に整理済** — 9000 の typeP_Galois/field-model が landing 次第、
上記は薄い cite で close 可能 (C が assemble)。9000 の owner=lane-a は本項目を dictate されないが、C の
type-determination 全体が 1・2 に gated である事実を downstream 影響として記録。
