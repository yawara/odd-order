---
id: 2009
slug: s16-field-normalizer-pole2
title: "POLE-2: field_normalizer_structure (Pf 14.2, lane-h)"
created: 2026-06-18
---

# POLE-2: field_normalizer_structure (Pf 14.2, lane-h)

## 背景

feitThompson は 2 本の独立 bare sorry に bottom-out する ([[ft-endgame-two-poles]])。POLE-1 は
`Section16Inputs` producer (skeleton `80f9aa39` で 8014/7005/1004 に分配)。**POLE-2 = 本 issue**:
`field_normalizer_structure` (`OddOrder/Peterfalvi/S16_NonExistenceG.lean:1965`, bare `sorry`)。
2026-06-18 にユーザー裁可で **lane-h に割当** (typeP_duality 完了で idle 化したため)。POLE-1 側
(lane-g/f/b) と非衝突で並行可能。

## やること

- [x] `field_normalizer_structure : Nonempty (FieldNormalizerData hyp)` を **sorry-free 化** (`d22e2cd8`)。
      教科書結論「By (14.12), (14.16), (14.7)」の忠実 assembly (下記 LANDING)。
- [x] L-vs-M closing: (14.16) `H_eq_U` を配線、(14.7)/(14.12)/(14.16) の 3 ルート case 分析。
- [x] opaque `U_characteristic_in_H` を concrete `(U.subgroupOf H).Characteristic` に materialize
      + (14.16)→(14.7) bridge を実証明 (`d901a183`)。
- [ ] **genuine 残務 (§13/Dade gate)**: `exists_LHypothesis` (14.3, `:1969`) / `exists_MHypothesis`
      (14.10, `:1978`) — L/M over N_G(U)/N_G(V) + Dade data 構成 (Pf (13.17) + Dade isometry)。
- [ ] **irreducible hard core**: `field_normalizer_of_U_characteristic` (14.7, `:199`) = 有限体モデル
      σ: PU↪G of (14.2)(a)。§13 type-I + Dade + GaloisField 構成に深く gate (大物)。
- [ ] 完了後 `nonexistence_of_G` が BG App.C 経由で矛盾を出す閉路が unconditional 化 (上記が全て埋まれば)。

## 2026-06-18 LANDING (assembly + bridge COMPLETE, 残務 gated)

`field_normalizer_structure` (Pf 14.2) は **sorry-free**。stop 条件「sorry 消滅」達成。残務 (14.7 有限体
モデル + L/M producers + 14.4-14.16 char cascade) はすべて Pf §10-13 char theory / Dade / 有限体モデルに
gate = LAUNCH の明示 stop trigger。real sorry 140→141。詳細 = LANDING block in lane-h LAUNCH.md。
ステータス = pending (genuine 残務は §13/Dade unblock 待ち)。

## 2026-06-18 再開 (Singer-field engine 着地 + 14.7 診断訂正)

**重要な診断訂正**: 前回「14.7 有限体モデルは §13 type-I 構造に深く gate」としたが、これは**誤り**。
(14.7) の体構成 (14.2)(a) の核 = 「U が P 上に既約に作用 ⟹ P は体 F_{p^q}、U ↪ F^×」(Singer 機構)
であり、**既約性は §11-13 構造ではなく `c_eq_one`(= U が P に忠実作用)から証明可能**:
U 巡回・忠実 ⟹ `u = lcm(uᵢ)` (Maschke 分解 Pᵢ、各 `uᵢ ∣ p^{dᵢ}-1` を constituent 上 Singer で)、
`u = (p^q-1)/(p-1)` の素因子 r は order_r(p)=q (primitive) か r=q のみ ⟹ dᵢ=q (単一 constituent) ⟹ 既約。

### ✅ 着地 (commit `3b8b7204`)
- **`OddOrder/GroupTheory/RepresentationTheory/SingerField.lean`** (新 leaf, sorry-free, axiom-clean):
  - `SingerFieldData` + `nonempty_singerFieldData` = 「可換群 C の既約 F_p-線形作用 ⟹ M は体 K、C →* Kˣ、
    作用 = 乗法」。可換環の simple module = R⧸𝔪 (極大) = 体 経由 (Wedderburn/Jacobson 不要)。
  - `card_K_eq` (|K|=|M|), `nonempty_ringEquiv_galoisField` (K ≅ GF(p^n)) = FieldNormalizerData の
    `GaloisField p q` への橋。
  - asModule の tactic-mode synth 罠を回避 (M を直接 `Module (MonoidAlgebra (ZMod p) C)` で持つ)。

### 14.7 σ-construction への残り道筋 (concrete, ほぼ ungated)
1. **U-irreducibility on P** (新補題, 要 Maschke + constituent-Singer + 素因子論): `c_eq_one` 忠実性 +
   `u=(p^q-1)/(p-1)` から既約。⚠ `u = q^k` 例外ケースの数論処理が要 (Zsygmondy は mathlib 未収録の可能性)。
   前提 `u = (p^q-1)/(p-1)` は (14.7) 算術 (済) が供給。
2. **P を F_p[U]-module 化** (共役作用、`IsElementaryAbelian` から F_p-module)。
3. **Singer engine 適用** → P ≃+ GF(p^q), U → GF(p^q)ˣ。
4. **σ assembly**: `fieldNormalizerFrobeniusGroup = GF(p^q)⋊U*` → G を P/U/W₂ に合わせて構成
   (frozen Core `S16_NonExistenceGCore` の def 群を**使用**、改変なし)。heavy。
5. **part(b)** (Q elem abelian, W₂ normalizes Q, ∃y∈Q): (13.2.b)/(14.5) gate (これは §13 依存・残置)。

⟹ (14.7) は「§13 に深く gate」ではなく、**(1)(4) が ungated な multi-session 実装、(5) のみ §13 gate**。
exists_L/MHypothesis (14.3/14.10) + caseB cascade は依然 Dade gate (Lane B)。

### ✅✅ 2026-06-18 抽象 (14.2)(a) 機構 COMPLETE (commits `9043df39` + `4bdedb49`)
- **`isSimpleModule_of_isCyclic_faithful_card`** (`9043df39`): U-irreducibility 補題完成 (step 1)。
  Maschke 半単純分解 → 各単純成分に Singer engine → `g^{p^D-1}=1` (D=(q-1)!, q∤D) → faithful ⟹
  `|C|∣p^D-1` → `cyclotomicQuotient_not_dvd_pow_sub_one` で矛盾。dual structure 不要 (Maschke が
  restrictScalars で供給)、`[NeZero (card C : ZMod p)]` のみ。
- **`exists_galoisField_repr`** (`4bdedb49`): 抽象 (14.2)(a) capstone。faithful cyclic |C|=(p^q-1)/(p-1)
  作用 on |M|=p^q ⟹ `∃ e : M ≃+ GaloisField p q, μ : C →* GF(p^q)ˣ (injective), e(of c•x)=μ c·e x`。
- すべて sorry-free + axiom-clean、full build 3859 jobs green。
- **⟹ step 1 + 3 (abstract math) DONE**。残り = FT-specific wiring (step 3 P-as-F_p[U]-module +
  hypotheses discharge / step 4 σ assembly frozen Core / step 5 part(b))。**これらは §13/§15 の
  sorried producers (`basic_structure`(13.2 で |P|=p^q), `c_eq_one`(faithful), (14.7) case 算術) に
  bottom-out** = exists_L/MHypothesis と同じ §13 char theory gate。正本 = notes/peterfalvi/s16_14_7_field_construction.md。

### ✅✅✅ 2026-06-18 再開⁴ σ-bridge (step 4) COMPLETE (commits `aee72713`/`410471ea`/`d948ce69`/`3d2fe09a`)

**step 4 (σ assembly) を実装** — `OddOrder/Peterfalvi/S16_NonExistenceG.lean`、sorry-free + axiom-clean
+ AxiomsCheck 登録:
- **`fieldNormalizerKernelTransport` (fN)**: `e : Additive ↥P ≃+ 𝔽_{p^q}` から `𝔽_{p^q} →* G`
  (`s ↦ ↑(toMul (e.symm s))`)。+ `_apply`/`_injective`/`_range`(= P)。
- **`fieldNormalizerComplementTransport` (fU)**: `μ : U →* 𝔽_{p^q}ˣ` (inj, range=normOneUnits) から
  `U* →* G` (μ を corestrict した全単射の逆 + U.subtype)。+ `_exists`/`_injective`/`_range`(= U)。
- **`fieldNormalizerData_of_repr`**: `σ := SemidirectProduct.lift fN fU hcompatLift` + 5 properties
  (`sigma_injective` via ker=⊥ + P∩U=1、`sigma_P_eq_P`/`sigma_U_eq_U`/`sigma_P0_eq_W2`)。crux =
  `hcompatLift` (hcompat の U-同変性を G-conjugation に変換)。(14.2)(a) iso を**入力**に取るゆえ ungated。

**⟹ step 4 DONE。POLE-2 の ungated leaf (step 1/2/4) はすべて出し尽くした。**残務 = step 3 の
module-setup → `exists_galoisField_repr` 適用 (|P|=p^q `basic_structure` + faithful `c_eq_one` = §13)
+ part(b) (13.2.b/14.5 = §13)。`field_normalizer_of_U_characteristic` の docstring に reduction を明示。
full build 3860 jobs ~12.6s green、real sorry 140 不変 (σ-bridge は reduction lemma、新 sorry 無し)。

### ✅ 2026-06-18 再開⁵ cite-route 訂正 + 構造入力 2 本 (commits `a6ab11ee`/`427e36e9`)

**訂正**: 「POLE-2 は §13-gated で停止」は早計だった (ユーザー指摘「cite してできることないの？」)。sorried §13 定理
(`basic_structure`/`c_eq_one`/`caseB_order_u`=13.15) は **citeable** で、repo は既にこれを多用 (`u_modEq_one_mod_q`
S16:1491、`u_eq_full_cyclotomic_of_caseB` S16:1692 = proven が sorried §13 を cite)。⟹ cite で (14.7) を前進可能。

**教科書 (14.7) は短い**: part(b)=(13.2.b)+(14.5) / あとは `u=full` を示せば足り (cite (14.6)(9.7)(13.12))、
それは (13.15)`caseB_order_u` の二分 + W₂^y の U への FPF 作用 `q≡qu≡1 (mod p)` 矛盾 (q<p)。

**着地した σ-bridge 構造入力 2 本** (`fieldNormalizerData_of_repr` の hypotheses):
- ✅ `conj_mem_P` (hUP: ∀v∈U x∈P, v·x·v⁻¹∈P) + `U_le_normalizer_P` — **完全 unconditional** (Hypothesis
  フィールド S_deriv_eq_PU/P_eq_SF + maxNilpotentNormalHall_le_normalizer のみ、axiom-clean)。
- ✅ `P_inf_U_eq_bot` (hPU_disj: P⊓U=⊥) — **§13-cite** (P elem abelian⟹P≤C_G(P)、c_eq_one⟹C=⊥)、body
  sorry-free だが transitive に sorryAx (NOT axiom-clean)。

**残る (14.7) core (multi-session)**: ① value-argument `u=full` (FPF `u≡1 mod p` = W₂^y on U が**未形式化**、
要 §14-structural) ② `Additive ↥P` の 𝔽_p[U]-module 構成 (~150 行、infra `IsElementaryAbelian.zmodModule`
PRank:87 在) → `exists_galoisField_repr` 適用 → e/μ/hcompat ③ hW2 (prime line↔W₂、iso の scaling) ④ partB
(13.2.b/14.5 cite)。infra は揃い blocked ではない。

### ✅✅✅ 2026-06-18 再開⁶ — step 3 (14.2)(a) field model `exists_pu_field_repr` COMPLETE (`af543785`)

**(14.7) の crux ungated 機械 = module 構成を達成。** `exists_pu_field_repr`: §13 numeric data から
(14.2)(a) の iso (`e : Additive ↥P ≃+ GF(p^q)`, `μ : U →* GF(p^q)ˣ`, U-equivariance) を構成。
- 共役 rep `ρ = (mulAutToEnd ↥P p) ∘ (normalizerMonoidHom ∘ inclusion(U≤N(P)))`。
- `Additive ↥P` を `Module.compHom` で **直接** 𝔽_p[U]-module 化（**asModule trap 回避** = SingerField 自身の
  推奨）→ `of c • x = ρ c x = 共役` が σ-bridge の hcompat と `congr 2`（defeq）で一致。
- card/faithful/NeZero/cyclic: |P|=p^q (cite basic_structure) / c が P 中心化⟹c∈U⊓C_G(P)=C=1 (cite
  c_eq_one) / |U|≡1 mod p (geomSum) / `[IsCyclic ↥U]` 仮説。
- body sorry-free + transitive sorryAx（cite §13）。仮説 = `hu_full`(|U|=full) + `[IsCyclic ↥U]`（standing §13）。
- ⚠ instance-diamond 知見（再利用可）: `open scoped IsMulCommutative`; `AddCommGroup.zmodModule`（≠
  IsElementaryAbelian.zmodModule、CommGroup diamond 回避）; CommGroup ↥U は canonical Group 再利用で構築。

**(14.7) の 2 大技術ピース (σ-bridge step 4 + field model step 3) 完成。** 残: ① value-argument
`u=full`（FPF `u≡1 mod p` = W₂^y on U の形式化要、moderate）② `[IsCyclic ↥U]` の §13 producer ③ hW2
(prime line↔W₂、iso scaling) ④ partB (13.2.b/14.5 cite) → ⑤ exists_pu_field_repr + fieldNormalizerData_of_repr
を組んで `field_normalizer_of_U_characteristic` close。

### ✅ 2026-06-19 再開⁷ — hμ_range producer `mu_range_eq_normOneUnits` COMPLETE (`c83540d7`)

σ-bridge の `hμ_range` 入力を **unconditional**（axiom-clean、§13 非 cite）で landing: 任意の injective
`μ : U →* 𝔽_{p^q}ˣ` で `|U|=(p^q-1)/(p-1)` なら `μ.range = normOneUnits`。両者は cyclic `𝔽_{p^q}ˣ` の
同位数 d=(p^q-1)/(p-1) 部分群 ⟹ 共に `ker(powMonoidHom d)`（card = gcd(p^q-1,d)=d、`IsCyclic.card_powMonoidHom_ker`）
に一致。`Subgroup.eq_of_le_of_card_ge` × 2。

**proven コンポーネント棚卸し**（σ-bridge の hypothesis-inputs）: hUP=`conj_mem_P`✓ / hPU_disj=`P_inf_U_eq_bot`✓ /
hμ_range=`mu_range_eq_normOneUnits`✓ / e,μ,hcompat=`exists_pu_field_repr`✓（value-arg 仮説）/ hcyclotomic=
`cyclotomic_quotient_coprime_of_not_dvd`（q∤(p-1) 仮説）。**残る involved な gap**: ① value-arg `u=full`+`q∤(p-1)`
（(13.15)二分 + W₂^y FPF、part(b) 依存）③ hW2（generic e を W₂-respecting に scaling）④ `[IsCyclic ↥U]` の §13
producer ⑤ partB → ⑥ assembly。これらは clean な standalone でなく real argument 要（FPF 構造・scaling）。

### 🛑 2026-06-19 /loop 停止（depletion）— 残る全ピースが §13/§14-gated と確定

ユーザー指示で `/loop` 起動 → 残 ungated runway を精査した結果、**clean な ungated piece は出し尽くし**た:
- **hW2 scaling**（generic e を W₂-respecting 化）は ungated **に見えたが** `W₂ ≤ P` を前提に要する。
  これは S15.Hypothesis の field でなく **§13-structural fact**（hW2 = `(span{1}).map fN = W2` で
  `fN.range = P` ゆえ `W₂ ⊆ P` 必須）。⟹ `W₂≤P` を仮説に取れば scaling 自体は ungated だが、closure に §13 が入る。
- **scaling 設計**（次セッション用、`W₂≤P` 仮説下で実装）: `exists_pu_field_repr` の generic `e₀` を取り、
  `w₀ ∈ W₂` (≠1, W₂ nontrivial since |W₂|=p≥5)、`c := e₀(ofMul ⟨↑w₀,hW2_le_P⟩) ≠ 0`、
  `e := e₀.trans (DistribMulAction.toAddEquiv₀ GF c⁻¹ hc)`（c⁻¹ 乗算 AddEquiv）。conclusion: ① μ inj 同じ
  ② compat = `c⁻¹*(μv*e₀ x)=μv*(c⁻¹*e₀ x)`（可換、ring）③ hW2: W₂=⟨w₀⟩ (prime order) ⟹ `e₀(W₂)=span{c}`
  ⟹ `e(W₂)=span{1}` ⟹ `.map fN = W₂`（membership ↔ then le_antisymm）。~70 行、submodule/AddEquiv bookkeeping。
- **value-argument** `u=full`+`q∤(p-1)`: (13.15) 二分 + W₂^y の U への FPF `u≡1 mod p`（part(b) の y 依存 = §14-structural、未形式化）。
- **`[IsCyclic ↥U]`**: standing §13（field 構造から導けない=循環: exists_pu_field_repr が要求）。
- **partB**: (13.2.b)/(14.5) cite（§13）。

**⟹ ungated runway 枯渇 = /loop 停止（depletion、policy 準拠）。** 全 proven コンポーネント（σ-bridge / 体モデル /
hUP / hPU_disj / hμ_range）は committed・green。次セッション = scaling（W₂≤P §13 入力下、~70 行）+ §13/§14 pieces
（value-arg FPF / IsCyclic / partB / W₂≤P）+ assembly。

### ✅✅ 2026-06-19 再開⁸ — hW2 scaling COMPLETE + assembly engine（`b2564baf`）

前回 depletion で「次セッションに残した」唯一の ungated piece = **hW2 scaling を完遂**。さらに組み立て全体を
literal-`sorry`-free な engine で検証。3 本 landing（full build 3863 jobs ~32s green、real sorry 140 不変）:

- **`field_repr_rescale_to_W2`（axiom-clean = `[propext, Classical.choice, Quot.sound]`、§13 cite なし）**:
  generic な体モデル `e₀` を `W₂≤P` 仮説下で rescale。`w₀∈W₂`（≠1）, `c := e₀(ofMul w₀) ≠ 0`,
  `e := e₀.trans (×c⁻¹ の AddEquiv)`。`e(ofMul w₀)=1` ⟹ prime line `span 𝔽_p{1}` を `W₂` に正確に運ぶ。
  証明核 = `Span = zpowers(ofAdd 1)`（ZMod p-線形性は `r•x = r.val•x` で nsmul 還元）→ `MonoidHom.map_zpowers`
  → `zpowers(↑w₀) = W₂`（素数位数 `|W₂|=p`）。compat は体の可換性で survive。
- **`exists_pu_field_repr_W2`（§13-cite）**: `exists_pu_field_repr` + 上記 rescaling を chain し、
  `fieldNormalizerData_of_repr` が要求する `(e, μ, hμ_inj, hcompat, hW2)` 完全パッケージを産出。
- **`field_normalizer_of_U_characteristic_of_inputs`（literal-sorry-free）**: §13/§14-gated facts を
  明示仮説（`hu_full` / `IsCyclic ↥U` / `W₂≤P` / cyclotomic coprime / part(b)）に取り、`FieldNormalizerData`
  を組み立てる engine。**σ-bridge 全体が typecheck することを検証**。gate は cite 先の §13 producer
  (`basic_structure`/`c_eq_one`, Lane B) のみ。

**⟹ (14.7) は named §13/§14 obligations に reduce 済**（docstring に recipe 明記）。**ungated field-algebra は
完全に出し尽くした**。残務はすべて純 §13/§14:
1. **`hu_full`+cyclotomic coprime**（value-arg, §14 FPF: `p≡1 mod q` 枝を W₂^y on U で除外）
2. **`[IsCyclic ↥U]`**（§13 standing）
3. **`W₂≤P`**（§13-structural; `FieldNormalizerData` の `W2_le_P` は data 入力ゆえ循環、独立供給要）
4. **part(b)**（Q elem abelian / W₂◁Q / ∃y∈Q with W₂^y◁U = (13.2.b)/(14.5)）
→ 5. これらを `_of_inputs` に渡して `field_normalizer_of_U_characteristic` を close。
これらは exists_L/MHypothesis（14.3/14.10）+ case-B cascade と同じ Dade/§13 char theory gate（Lane B）。

### ✅✅ 2026-06-19 再開⁹ — §14 value-argument 算術核 COMPLETE（`40150bb0`）

ユーザー裁可で **§14 value-argument に着手**。論文 (14.7) の value-argument の**算術核を axiom-clean で形式化**し、
(14.7) を「FPF 合同 `u ≡ 1 mod p` + part(b)」ちょうどに reduce（full build 3863 jobs ~15s green、sorry 140 不変）:

- **`u_eq_full_of_caseB_of_u_modEq_one_mod_p`（axiom-clean = `[propext, Classical.choice, Quot.sound]`）**:
  `CaseBForSData`（caseB dichotomy 13.15）+ FPF 合同 `u ≡ 1 mod p` を仮説に取り、`u = (p^q-1)/(p-1) ∧ ¬(p≡1 mod q)`。
  (13.15) の `p≡1 mod q` 枝では `q·u = (p^q-1)/(p-1) ≡ 1 mod p`(geom sum, private `cyclotomic_quotient_modEq_one_mod_base`)
  ゆえ `q ≡ q·u ≡ 1 mod p` → `p ∣ q-1`、standing `q < p`(`hyp.q_lt_p`)に矛盾。よって full 枝。
- **`field_normalizer_of_U_characteristic_of_fpf`**: 最もタイトな (14.7) assembly engine。value-arg（`caseB_for_S Ldata`
  cite で `u≡1 mod p` → hu_full + cyclotomic coprime）→ `_of_inputs`。**⟹ (14.7) は FPF `u≡1 mod p` + `W₂≤P` + part(b)
  ちょうどに reduce**。gate = §13 producer（basic_structure/c_eq_one/caseB_for_S, Lane B）のみ。

**⟹ value-argument の算術・assembly は完全に done（axiom-clean）。残る唯一の真の §14 gate = FPF fact `u ≡ 1 mod p`。**

### 🛑 FPF fact `u ≡ 1 mod p` = 深い §14 structural（scaffold ゼロ、調査済 2026-06-19）

`u ≡ 1 mod p` の source = W₂^y（位数 p）が U に Frobenius complement として作用 ⟹ `|U| ≡ 1 mod p`。必要:
1. **part(b)**（Q elem abelian / W₂≤N(Q) / ∃y∈Q with W₂^y≤N(U)）= (13.2.b)/(14.5) — **producer ゼロ**（repo grep 済、
   hQ_elemAb 等は全 lemma で仮説のみ）。(13.2.b) は §13、(14.5) は §14。
2. **W₂^y-on-U Frobenius 構造**（FPF-ness 含む）= §14 field-model から構成、**repo に不在**（U⋊W₁ の mod-q 版のみ存在
   = `u_modEq_one_mod_q` / `data.UW1_frobenius.card_kernel_modEq_one`）。
3. generic Frobenius ⟹ kernel≡1 mod complement = `IsFrobeniusGroup.card_kernel_modEq_one`（available）。

⟹ FPF fact は part(b) producer + 新規 §14 field-model action 理論を要する**大物・複数セッション**。lane-H 領域だが
scaffold ゼロ。次セッション or ユーザー判断（part(b) producer 着手 / lane B §13 待ち / 再タスク）。

### ✅✅✅ 2026-06-19 再開¹⁰ — FPF fact 完成 + (14.7) を §13 facts 4本に縮約（`7162a75a`/`db39b06e`/`e9253a02`）

**前回診断「FPF fact は新規 §14 field-model action 理論を要する大物・scaffold ゼロ」は過度に悲観的だった。**
FPF の source は新規理論でなく、**LHypothesis が既に carry している type-I Frobenius 構造 (13.17.a)**。教科書通り
「L = H⋊(W₁W₂^y) は kernel H の Frobenius 群、W₂^y は complement、U⊆H、U char in H」から FPF が出る。実装3本:

- **`card_modEq_one_of_prime_normalizing_fpf`**（汎用・axiom-clean）: 素数位数部分群 A が U を正規化し FPF 作用
  ⟹ |U|≡1 mod p（p-群 fixed-point 合同、{1} が唯一不動点）。
- **`isFrobeniusGroup_conj_ne_of_mem_map_complement`**（汎用・axiom-clean `[propext, Quot.sound]`）:
  `IsFrobeniusGroup.conj_frobenius` を ↥L→G へ `L.subtype` 経由で transport。complement の元（G元として
  `compl.map L.subtype` 内）は kernel H の任意元に FPF 作用。
- **`u_modEq_one_mod_p_of_LHypothesis`**: Ldata + U char in H + (14.5) の `W₂^y ≤ complement.map subtype`
  から、`W₂^y≤N_G(U)`（char + `maxNilpotentNormalHall_le_normalizer` + `mem_normalizer_map_subtype_of_characteristic`）
  と FPF（上記 helper）を導き、`u_modEq_one_mod_p_of_fpf` で `u≡1 mod p`。
- **`W2conj_le_normalizer_U_of_LHypothesis`**: part(14.2.b) の `W₂^y≤N_G(U)` を carrier から抽出（共有 lemma）。

**(14.5) `exists_y_L_structure` を concrete 化**: 旧 opaque field `L_semidirect_formula : G→Prop`（producer/consumer
ゼロの dead scaffold）を削除し、結論を `∃ y∈Q, W₂^y ≤ complement.map L.subtype`（bridge が消費する形）に。

**`field_normalizer_of_U_characteristic` を bridge 後へ移動 + wire**: (14.5)→bridge(`u≡1`)→`_of_fpf` engine、
`W₂^y≤N(U)` は共有 lemma。**⟹ 唯一の残 `sorry` = §13 facts 4本ちょうど**:
`IsCyclic U ∧ W₂≤P ∧ IsElementaryAbelian q Q ∧ W₂≤N_G(Q)`。

**残 4 facts は真に §13/Lane-B gated（cite 不可）**: `Q_elementaryAbelian`/`W2_normalizes_Q`/`W2_le_P` は
**FieldNormalizerData のフィールド（出力＝循環）**で独立 producer なし; `basic_structure`(13.2.b) は P側のみ
（Q側 dual 未形式化）; `IsCyclic U` は c=1 経由 §13 standing。∴ fake-discharge せず honest sorry のまま残置。

**⟹ POLE-2 の §14-internal long pole（FPF value-argument）は完成。残 POLE-2 = §13/Lane-B**:
① §13 facts 4本（basic_structure T-dual / c_eq_one / (13.2.b) / W₂≤P structural）
② (14.5) `exists_y_L_structure`（(13.17.c) 二分 + (13.19.c1) Dade counting = Lane B）
③ (14.6) `caseB_for_S`（Dade = Lane B）
④ もう片方の枝 `field_normalizer_of_L_conj_M` + `exists_LHypothesis`/`exists_MHypothesis`（(13.17)構成 + Dade）。
full build 3863 jobs green（16s）、AxiomsCheck OK、real sorry 140 不変（縮約は sorry の内容、本数でない）。

### ✅✅✅ 2026-06-19 再開¹¹ — POLE-2 両主枝 sorry-free、carrier 構成2本に縮約（`5c229f68`/`ca1b69e2`）

ユーザー指摘「§13 cite で進められないか」を受け、cite-route で POLE-2 を縮約。**`field_normalizer_structure`
の dispatch tree の literal sorry が `exists_LHypothesis`(14.3) + `exists_MHypothesis`(14.10) の2本だけに**:

- **U-char 枝** `field_normalizer_of_U_characteristic` = **literal-sorry-free**（`5c229f68`）。残 §13 構造facts
  3本を named obligation `S_field_model_structural_inputs`(13.2.a/b: IsCyclic U / W₂≤P / Q elem abelian、
  `basic_structure` の companion、sorried)に集約 + cite。`W₂≤N(Q)` は **ungated 導出**（W₂≤W≤T, Q=T_F,
  `maxNilpotentNormalHall_le_normalizer T`、当初 gated 扱いは誤り）。
- **L≅M 枝** `field_normalizer_of_L_conj_M` = **literal-sorry-free**（`ca1b69e2`）。教科書 (14.12) 還元
  「L≅M ⟹ H≅K cyclic ⟹ U char ⟹ (14.7)」を実装。新 reusable 補題 **`characteristic_of_isCyclic`**
  （有限巡回群の部分群は characteristic、**axiom-clean**、d-torsion `ker(powMonoidHom |K|)` 経由）+ named
  obligation `H_cyclic_of_L_conj_M`(14.11/14.4/13.12 = H cyclic、sorried)。U-char engine の後ろへ移動。
- **¬conj 枝** = `H_eq_U`(14.16) + `U_characteristic_of_H_eq_U` で既に sorry-free（H=U ⟹ U char）。

**⟹ POLE-2 は named/faithful な §13/§14/Dade obligation に完全還元**: ① exists_LHypothesis/exists_MHypothesis
(14.3/14.10 = Dade carrier 構成、大型) ② S_field_model_structural_inputs(§13 構造) ③ caseB_for_S(14.6 Dade)
④ exists_y_L_structure(14.5: (13.17.c)構造 + (13.19)Dade) ⑤ H_cyclic_of_L_conj_M(Dade)。**全て Dade(Lane B)
or basic_structure-level §13 構造に bottom-out** = Lane-B-独立な clean win は出尽くし。実 sorry 140 不変
（縮約は sorry の内容；各 inline sorry → named faithful obligation）。full build 3863 jobs 15s green。

## 📋 2026-06-19 セッション HANDOFF（POLE-2 構造を実証明+cite で大きく前進）

**本セッション 11 commit（`7162a75a`..`75bac20d`）、実 sorry 144→138、full build 3863 jobs ~16s green 維持。**

### `field_normalizer_structure`（POLE-2）の現状 = dispatch + 両主枝 sorry-free

`field_normalizer_structure` の dispatch tree で **literal-sorry-free 化したもの**:
- **dispatch 本体**（exists_LHypothesis → by_cases U-char → 各枝）
- **(14.3) `exists_LHypothesis`** — (13.17) `S15.typeII_overNormalizer_frobenius` を cite して carrier 構成。
  LHypothesis は消費フィールド（typeI_data + L/H/normalizer_U_le_L/H_eq_LF + complement_card）に **slim**
  （Dade フィールド Lset/tau/…/betaL は 0 consumer ゆえ削除）。S は type II（basic_structure +
  `q_lt_p_forces_typeII`）。
- **(14.5) `exists_y_L_structure`** — (13.17) carrier の field `exists_y_W2_conj_le_complement` の projection。
  S15 の opaque `complement_structure : Prop` を concrete 2 フィールド（`complement_card_eq_pq` +
  `exists_y_W2_conj_le_complement`）に置換、sorry を `typeII_overNormalizer_frobenius` 1 本に集約。
- **U-char 枝 (14.7) `field_normalizer_of_U_characteristic`** — FPF value-arg を carrier から end-to-end
  組立（FPF 機構 `isFrobeniusGroup_conj_ne_of_mem_map_complement` + bridge `u_modEq_one_mod_p_of_LHypothesis`
  + `W2conj_le_normalizer_U_of_LHypothesis`）。**`W2_le_P` は実証明**（下記）。
- **L≅M 枝 (14.12) `field_normalizer_of_L_conj_M`** — 「H≅K cyclic ⟹ U char ⟹ (14.7)」還元 +
  **`characteristic_of_isCyclic`**（有限巡回群の部分群は characteristic、axiom-clean 汎用）。
- **¬conj 枝 (14.16) `H_eq_U`** — 既に sorry-free。
- **(14.4) `caseB_for_T`** — numeric 内容（D=⊥, v=full）を `T_side_caseB_facts` に集約して literal-sorry-free。

### 新規 reusable 補題（再導出するな）
- **`pgroup_le_of_normal_coprime_index`**（S16, 汎用）: p-群 ≤ 正規・coprime-index 部分群。商位数論。
- **`W2_le_P`**（S16, 実証明・cite でない）: W₂ p-群 ≤ 正規 Hall p-部分群 P=S_F。`maxNilpotentNormalHall_isHall`
  の `Ch03.IsHallSubgroup.coprime_index`（**名前注意**: `coprime_index`, not `coprime_card_index`）+ basic_structure。
- **`characteristic_of_isCyclic`**（S16, axiom-clean）: d-torsion `ker(powMonoidHom |K|)` 経由。
- FPF 機構一式（`card_modEq_one_of_prime_normalizing_fpf` / `isFrobeniusGroup_conj_ne_of_mem_map_complement`
  / `u_modEq_one_mod_p_of_LHypothesis` / `W2conj_le_normalizer_U_of_LHypothesis`）。

### 残り frontier = 2 種類（clean cite/群論は出し尽くし）
**(A) Lane B 指標論（producer 物理的に不在、cite 先なし）**:
- `U_cyclic_and_Q_elemAbelian`（S16）= U cyclic (§9 / 9.7.b) + Q elem abelian (§11 / 11.7、別 carrier bridge 要)
- `caseB_for_S`（14.6）= (9.7.a) を rank-2+FPF+(13.13) で除外（§9 表現必要）
- `T_side_caseB_facts`（§13-T: D=⊥, v=full、swap 不在ゆえ dual 不可）
- `exists_MHypothesis`（14.10）= (14.11) Dade norm-cascade（消費フィールド betaM/G0/generic_bound/betaM_expansion）
  + V側 (13.17) dual（不在）
- 上流 cited sorry: `typeII_overNormalizer_frobenius`(13.17) / `basic_structure`(13.2) / `c_eq_one`(13.12)

**(B) lane-h 重い infra**:
- `H_cyclic_of_L_conj_M` → `maxNilpotentNormalHall` の**共役同変性** `conj g • maxNNH M = maxNNH(conj g•M)`
  （sSup 定義上 ~80 行、candidate 4 clause を conj 保存; normal は `normal_subgroupOf_iff_le_normalizer`+
  normalizer 同変、nilpotent は `subgroupOfEquivOfLe`+`equivSMul`、Hall は relindex 同変）に還元可。
  ただし残 `K_cyclic`（=V cyclic）は (A) の指標論。

### 次セッション pickup
clean な lane-h 独立貢献は **W2_le_P で一区切り**。次は (B) の `maxNilpotentNormalHall` 共役同変性 grind
（reusable BG 補題、`OddOrder/GroupTheory/MaxNilpotentNormalHall.lean` or `BG/Ch4/S15_MF.lean`）か、
(A) は **Lane B の §6→§13 char theory 着地待ち**（cite 先がそこで生まれる）。POLE-2 全体の unconditional 化は
Lane B の Dade 指標論に bottom-out。

## 完了条件

`field_normalizer_structure` の `sorry` が消え、`lake build OddOrder OddOrder.AxiomsCheck` 緑。
可能なら `#assert_only_allowed_axioms` に登録 (sorry 消滅後)。

## 参照

- POLE-2: `OddOrder/Peterfalvi/S16_NonExistenceG.lean:1965` (`field_normalizer_structure`),
  `:1030` (`field_normalizer_of_L_conj_M` scaffold)
- 既証明 expertise: lane-h の BG §14 type-P 構造 (typeP_duality `S14_TypePCounting.lean:7961`)
- 関連: 8014 / 7005 / 1004 (POLE-1)。caveat: 本件は Peterfalvi §14 (field automorphism/Dade) で
  BG §14 とは別物 — lane-h は territory 学習が要る

## 2026-06-19 再開¹² — M_F 自己同型同変性 (reusable infra) + H_cyclic 構造化 (`8e6b3379`)

ユーザー方針「sorry 数でなく FT 寄与・B/F と領域分離・安定 signature 引用」を受け、POLE-2 frontier を
**実証的に全マッピング**した上で、reusable building block を landing。

### FT-path Peterfalvi frontier マッピング (consumer grep で確定)
- **Pf §10 (S10_MinimalSimpleStructure) はほぼ全 orphaned** (0 consumers; `dadeSupportHypotheses_typeP`
  のみ S12 が cite)。typeF Frobenius chain (`typeF_card_U0_eq_exponent`/`typeF_frobenius_of_card_eq_exponent`)
  も 0 consumers。⟹ §10 で作業しても FT に繋がらない ([[ft-path-policy]] 裏付け)。
- **FT-path の Pf producer は §12-§16 の深い char/構造**: `basic_structure`(13.2, char-Prop fields 込)、
  `typeII_overNormalizer_frobenius`(13.17, 構造的だが case 分析 + 多数 cite)、`typeI_frobenius`(12.7,
  minimal counterexample 12.8-16 = char)。いずれも cite-and-assemble だが assembly 入力自体が深い。
  前セッションが cite-and-assemble を出し尽くし済 → 残りは producer 証明本体 (Lane B 領域の char + 構造)。
- ファイル命名 offset 確認: repo S11=Pf §9 / S12=§10 / S13=§11 / S14=§12 / S15=§13。

### 本セッション landing (FT 寄与 + B/F 非衝突 + 安定 signature)
- **`maxNilpotentNormalHall_pointwise_smul`** (`GroupTheory/MaxNilpotentNormalHall.lean`, axiom-clean,
  AxiomsCheck 登録): `φ • M_F = (φ • M)_F` (任意 `φ : MulAut G`)。候補集合の 4 条件 (≤/Normal/Nilpotent/Hall)
  が自己同型不変 + sSup 保存 (le_sSup/sSup_le adjunction)。**BG §13 / Pf §13 の `L_F`/`M_F` 共役論法の
  reusable building block** — 特に Pf (13.17) 証明 (L^g=S 矛盾で L_F 共役を使う) で必要。
  helper: `map_subgroupMap_subgroupOf` (subgroupOf の φ-image)、`pointwise_mulAut_smul_eq_map`。
- **`H_cyclic_of_L_conj_M` (14.12, POLE-2 の L≅M 枝) を sorry-free 化**: L≅M (conj g) ⟹ 上記同変性で
  `H=L_F ≅ M_F=K` ⟹ char 内容 (K cyclic) を canonical obligation **`MHypothesis_kernel_cyclic`**
  (Pf (14.11)/(14.4)/(13.12): K=V は VW₂ の cyclic Frobenius kernel) に isolate。POLE-2 の L≅M 枝が
  「純構造 reduction + 単一 char gate」に。real sorry 133 不変 (sorry 再配置)。

### 次セッション pickup (FT-path, 同変性 building block を使う)
- **`typeII_overNormalizer_frobenius` (13.17, S15_SAndT)** が最有力 — POLE-2 の `exists_LHypothesis` が
  直接 cite、carrier に char-Prop 無し (構造的)、同変性が証明の building block。Pf 原文 (pp.81-82) の証明:
  (a) L~S を type-II def + Hall 共役で除外、L~T を (13.2.a) で除外 → (8.8.b4) type-I → (12.7) Frobenius;
  (b) U⊆H = (8.17.a)+(9.1); (c) 補元 = [H]Satz 8.18 + (13.16) + BG Prop 3.9 (`S03g_Thm310`) + Sylow。
  ∃ maximal L⊇N_G(U) は proper⊆maximal で provable。cite 先 (12.7/13.2.a/8.8 dichotomy/BG 3.9) は repo 在。

## 2026-06-19 再開¹² cont. — (13.17) gated-endpoint skeleton (`0d99daf1`)

`typeII_overNormalizer_frobenius` (13.17, POLE-2 の exists_LHypothesis が cite) を **sorry-free
assembly** 化: (12.7) `S14.typeI_frobenius` を cite + deep §13 内容を 2 faithful obligation に分離。
real sorry 133→134 (bare sorry → 2 obligation + (12.7) cite、[[feedback-gated-endpoint-skeleton-pattern]])。

### 残 obligation (FT-path、次の deep §13 ターゲット) + 攻略メモ
**① `exists_typeI_maximal_overNormalizer_U` (13.17.a/b)** = ∃ type-I maximal L⊇N_G(U) with U⊆L_F:
- ∃ maximal L⊇N_G(U): N_G(U) proper (U≠⊥ + G simple) → `Finite.exists_le_maximal`。
- L type-I: `hyp.theorem88_caseB L hLmax` (Hypothesis field = (8.8.b4) trichotomy) で IsTypeI∨L~S∨L~T。
  - **L~S 除外** = conj g•L=S → conj g•N_G(U)≤S → (Hall 共役で conj•U を typeP.U に取り直し) → N_G(typeP.U)≤S、
    `IsTypeII.normalizer_not_le` 矛盾。**⚠ 真の障害 = coherence — Hypothesis は hyp.U を S の type-II
    `typeP.U` に pin せず** (S_deriv_eq_PU/card_U_eq_uc 等の制約のみ; 両者とも「derivedInG S の P-補元」だが
    補元は一意でなく**共役止まり**) → bridge 要。**normalizer 同変性は既存** (自前導出不要): repo
    `normalizer_conj_smul` (S12_ExceptionalBridge:266) + mathlib `Subgroup.map_normalizer_eq_of_bijective`。
    **maxNNH 同変性 (本セッション landing) と同型の議論** = 候補。
  - **L~T 除外** = |L_F|=q^p → W₁⊆N_G(U)⊆L, W₁⊆L_F, [U,W₁]⊆L_F∩U=1、(13.2.a) UW₁ Frobenius 矛盾。要 |L_F|=q^p (T-side)。
- U⊆L_F: (8.17.a) |L_F| coprime to q → W₁∩L_F=1; U∩L_F=1 なら UW₁ FPF on L_F → (9.1) L_F=1 矛盾。要 (8.17.a)/(9.1) 所在確認。

**② `typeI_overNormalizer_complement` (13.17.c/14.5)** = |complement|=pq ∧ ∃y∈Q, W₂^y≤complement:
- E⊇W₁ complement to L_F in L = odd-order Frobenius complement → 素数位数部分群正規 ([H] V.8.18) → E⊆N_G(W₁)⊆QW₂
  ((13.16)) → Sylow cyclic ([BG] 3.9 = `S03g_Thm310`) → E=W₁ or |E|=pq=W₁W₂^y。W₁ 枝は (14.5) 除外。
  **⚠ [H] V.8.18 (Frobenius complement odd ⟹ prime subgroups normal) の repo 所在未確認** (Appendices.Huppert?)。

### 本セッション成果サマリ (commits `8e6b3379`/`a5fe4a45`/`0d99daf1`)
maxNNH 自己同型同変性 (reusable, axiom-clean) + H_cyclic_of_L_conj_M sorry-free 化 (POLE-2 L≅M 枝) +
(13.17) skeleton。次セッション = obligation ① (coherence bridge + normalizer 同変性から着手、maxNNH 同変性流用)。

## 2026-06-19 再開¹² cont.² — (13.17) obligation 深掘り: 具体的 blocker 特定

obligation ① の L~S 除外を深掘り → **真の blocker = `hyp.U` の under-constraint (Hypothesis faithfulness)**:
- Hypothesis は hyp.U を `S_deriv_eq_PU : derivedInG S = P ⊔ U` (**join のみ**) で制約。complement
  (`P ⊓ U = ⊥`) も S の type-II `typeP.U` との一致も pin せず。⟹ L~S 除外に要る `¬ N_G(hyp.U) ≤ S`
  (type-II 性) が `IsTypeII.normalizer_not_le` (typeP.U について) から直接出ない。
- bridge 道筋: P=maxNNH S は derivedInG S の normal Hall (✓導出可) → hyp.U が P-complement なら
  Schur-Zassenhaus で hyp.U ~ typeP.U (S 内共役) → normalizer 同変性 (既存) で `¬N_G(hyp.U)≤S`。
  **gap = 「hyp.U が complement」= `P ⊓ U = ⊥`**、card 関係 `|P||U|=|derivedInG S|` (= p^q·u·c?) 要、Hypothesis 未供給。
  → (a) §13 card 論で導出 (深い) or (b) Hypothesis に `IsComplement'`/`P⊓U=⊥` を enrich (carrier 変更=
  FeitThompson producer 要対応、cross-file)。
- obligation ② blocker: **[H] V.8.18** (奇数位数 Frobenius complement ⟹ 素数位数部分群正規) が **repo 不在**
  (古典的、新規形式化要)。(13.16)`normalizer_W1`(sorried)/BG 3.9(`S03g_Thm310`)は在。

**⟹ (13.17) 両 obligation は multi-session 深 §13 構造論** (coherence/faithfulness + Schur-Zassenhaus +
Huppert 形式化 + sorried §8/§9 cite)。skeleton で構造化済・cite 先確定済ゆえ、着手準備は整っている。

## 2026-06-19 方針① 確定 — §13 構造論プログラム計画

ユーザー裁可で**方針①「H が深い §13 構造論にコミット」**。(13.17) 2 obligation の攻略計画を
**`notes/peterfalvi/s13_17_structural_program.md`** に整理 (phase 0-4 + leaf 分類 + 検証済 infra)。
crux base = **hyp.U coherence** (Hypothesis が hyp.U を complement/typeP.U に pin せず) →
(a) §13 card 導出 or (b) F 協調 enrich。次の一手 = Phase 0(a) feasibility 調査 ∥ Phase 3 Huppert (H 単独並列)。

## 2026-06-20 再開 — ✅ Phase 1 完了 + Phase 0 診断確定 + F-ask 確定

**✅ Phase 1 DONE** (commit `378e61b1`, sorry-free + axiom-clean): `exists_conj_typeP_U_of_coprime`
(S15_SAndT) — `Coprime |U| |P|` から `∃ x∈S, U = conj x • typeP.U` (Schur-Zassenhaus、↥M' 内適用 →
G へ map-back)。前回 revert した 5 API 摩擦を全解決 (詳細 = notes/peterfalvi/s13_17_structural_program.md
「Phase 1 進捗」)。`not_normalizer_U_le_S` の `hconj` 仮説を供給する。

**🔑 Phase 0 診断確定**: Phase 1 SZ 補題が要する `Coprime |U| |P|` は **`P ⊓ U = ⊥` (disjointness) のみ**
から H 単独導出可 — `P = maxNilpotentNormalHall M'` (`derived_fitting_eq`) が **相対 Hall**
(`maxNilpotentNormalHall_isHall` は `(mnh M').subgroupOf M'` 形) ゆえ `.coprime_index` + 補元 index で coprime。
∴ **Phase 2 (obligation ①) の真の gate は `P ⊓ U = ⊥` 1 本のみ**。

**⚠ F-ask 確定 (最小・cross-lane)**: Phase 0(a) [H 単独 disjoint 導出] は **infeasible** (hyp.U の
under-constraint は carrier faithfulness 問題、§13 構造論で塞げない — hyp.U=M' でも全フィールド満たす)。
⟹ **F へ**: `Hypothesis` (S15_SAndT:73) に **1 フィールド `P_inf_U_eq_bot : P ⊓ U = ⊥` を追加**
(carrier 変更 → `sectionSixteenHypothesis_of_inputs` producer の対応要)。真に構成可能 (U は S' 内 P の Hall 補元、
(13.1.b))。F が追加すれば H は `coprime_card_U_card_P_of_disjoint` (Hall 論法 ~30 行) → SZ → Phase 2 解禁。

**残り obligation の状態**:
- obligation ① (Phase 2 `exists_typeI_maximal_overNormalizer_U`): gate = 上記 F-ask + L~T 除外 (|L_F|=q^p cite)
  + U⊆L_F ((9.1)/(8.17.a) cite)。
- obligation ② (Phase 4 `typeI_overNormalizer_complement`): gate = Phase 3 [H] V.8.18 (**大物・新規形式化、
  Isaacs Ch06 は Sylow-cyclic 部品のみ**) + (13.16) normalizer_W1 [sorried] + (14.5)。

## 2026-06-20² 再開 — ✅ Phase 2 gate 2 (L~S) 構造論コア sorry-free + 🔑 gate 2 残差も F-ask 判明

**✅ gate 2 (L~S) 構造論 DONE** (commit `4357cc7d`, sorry-free + axiom-clean): Pf (13.17.a)「L が S に共役」
枝の Hall 共役論法を 2 汎用補題で landing — `normalizer_le_of_isHall_subgroupOf_of_conj` (U が可解 V の π-Hall
+ `L^g=V` + `N_G(U)⊆L` ⟹ `N_G(U)⊆V`) + `isHall_subgroupOf_primeFactors_of_coprime_index`。L~S 枝の assembly
は sorry-free 化、残差を Pf 原文どおり `Coprime |U| [S:U]` (=「U is a Hall subgroup of S」) 1 本に縮約。

**🔑 知見: gate 2 残差も carrier-faithfulness F-ask** (LAUNCH の「~40-60 行 H 単独 basic_structure cite」訂正):
- 残差 `Coprime |U| [S:U]` は `[S:U]=[S:M']·|P|`、`|U|⟂|P|` = `hcop` (済)、**`|U|⟂[S:M']` が真の gate**。
- `[S:M']=|tdata.typeP.W1|` (prime)。`|U|⟂[S:M']` には `tdata.typeP.W1` が **κ(S)-Hall** であること
  (BG↔Pf の W₁=κ 同定) を要するが、これは bare `TypeIIData hyp.S` から導出されない carrier-faithfulness
  (`Section16MaximalPair`/lane-f レベルでのみ `K_hall`/`S_typeP` として供給)。
- ⚠ `BG.Ch4.S14.IsTypeP` (`kappa nonempty`) ≠ Pf `GroupTheory.IsTypeP` (`Nonempty TypePData`)。

**⚠ F-ask 改訂 (gate 1 + gate 2 一括)**: gate 1 の `P_inf_U_eq_bot` に加え、**gate 2 用**:
`W1_complements_derived : IsComplement' ((derivedInG S).subgroupOf S) (W1.subgroupOf S)` を Hypothesis に追加。
⟹ `[S:M']=|W₁|` + `basic_structure.UW1_frobenius` (`Coprime |U| |W₁|`、citeable) で gate 2 残差が close。
両 ask とも真に構成可能 (U/W₁ は type-P 構造の真の補元、(13.1.b))。詳細 = `notes/peterfalvi/s13_17_structural_program.md`
「Phase 2 cont. (2026-06-20²)」。

**H 次手**: gate 2 残差は F 待ち。残る H 単独 = gate 3 (L~T) / gate 4 (U⊆L_F) / Phase 3 (Huppert)。

## 2026-06-20³ — ✅ gate 3 構造論コア sorry-free + gate 3/4 の (B) 未記載 signature 追加 (issue 2013)

gate 3/4 は (A)「signature 既存・sorried producer (cite 可)」と (B)「signature 未記載」の混合だった
(issue 2013)。(B) を `S15_SAndT.lean` に faithful sorried producer として追加:
- **gate 3 (B)** `card_Q_eq` (`|Q|=q^p`) + `tConjugate_fitting_data` (L conj T ⟹ `|L_F|=q^p ∧ W₁≤L_F ∧ L_F⊓U=⊥`)。
- **gate 4 (B)** `card_LF_coprime_pq` (type-I 非共役 L ⟹ `Coprime |L_F| (p*q)`、`bgTheoremE_cover_data`[F] 派生) +
  `typeI_overNormalizer_U_le_fitting` (type-I L ⟹ `U≤L_F`、FPF コア束ね)。

**✅ gate 3 (L~T) 構造論コア = sorry-free** (`exists_typeI_maximal_overNormalizer_U` の `_hLconjT` 枝):
`tConjugate_fitting_data` ⟹ `⁅U,W₁⁆≤L_F⊓U=⊥` ⟹ `UW1_frobenius.conj_frobenius` 矛盾。残差 = B1 producer のみ。

**⚠ gate 4 (type-I) = producer 委任**: FPF 作用 `CoprimeFrobeniusAction (↥(U⊔W₁)) (↥L_F)` 構成 + FPF 性 +
自己中心化が深く、`typeI_overNormalizer_U_le_fitting` (`:= sorry`) に隔離 (`hLI` 枝は 1 行 `exact`、sorry なし)。
sorry-free 化には (a) 型一意性補題 (IsTypeI L ⟹ ¬conj S/T) + (b) FPF 作用構成インフラ が別途要る。

count-sorry 137→139 (新 producer 4 − 消えた gate 3/4 の 2 sorry)。full build 3869 jobs green。詳細 =
`notes/peterfalvi/s13_17_structural_program.md`「Phase 2 cont. (2026-06-20³)」。

## 2026-06-23 REACTIVATE (relane #5、ユーザー裁可) — pending → active

hub 統合レビュー (4 レーン進捗統合) で、(13.2.a)/step-3 wiring/hP2II の landing 後に
**FT endgame が lane-b character theory に収束 (POLE-1 残バレ sorry 2 本=card_kappaHall+cd は両方 lane-b)、
lane-h のみ割当完遂で idle** と確定。ユーザー裁可で **lane-h を POLE-2 (本 issue) に復帰**。
当面の workable-now = `field_normalizer_of_U_characteristic` (14.7) の Singer-field 核
(c_eq_one から既約性 → 有限体モデル、§13 非依存=上記「Singer-field engine 着地」診断が正本)。
L/M producers (14.3/14.10) は §13/Dade-gated ゆえ cite/defer。status: pending → **active** (issues/ へ移動)。

## 2026-06-23 → pending 復帰 (relane #7) — POLE-2 は driver/await に降格

relane #5 (lane-h→POLE-2) は stale-pointer エラーで無効と判明 (14.7 既に sorry-free、残は全 char-gated、issue 2021)。
lane-h は §6 coherence producer に再配置 → POLE-2 は常駐レーン無しの driver/await に戻す。char (lane-b/lane-c) +
Dade landing で auto-wire。status: active → **pending**。

## 🧾 追記 (2026-07-02 hub 全体レビュー): owner-of-record = lane c

- **owner-of-record = lane c** (3 レーン再編、正本 `notes/meta/ft_lane_reallocation_2026_06_28.md`:
  lane c = S15_SAndT_Setup / S15_SAndT / S16_NonExistenceG)。**§13 producer が land した時点で
  lane c が activate** する (それまでは pending の driver/await のまま)。旧 lane-h/lane-b
  宛先は全て stale。
- issue **0072** (S16_NonExistenceG tail split) 側の trigger 参照も更新済 (旧「2009 が
  pending/closed になるまで保留」→「lane c の §15/§16 frontier 凍結後」、2026-07-02 注記)。
