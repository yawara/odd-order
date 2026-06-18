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

## 完了条件

`field_normalizer_structure` の `sorry` が消え、`lake build OddOrder OddOrder.AxiomsCheck` 緑。
可能なら `#assert_only_allowed_axioms` に登録 (sorry 消滅後)。

## 参照

- POLE-2: `OddOrder/Peterfalvi/S16_NonExistenceG.lean:1965` (`field_normalizer_structure`),
  `:1030` (`field_normalizer_of_L_conj_M` scaffold)
- 既証明 expertise: lane-h の BG §14 type-P 構造 (typeP_duality `S14_TypePCounting.lean:7961`)
- 関連: 8014 / 7005 / 1004 (POLE-1)。caveat: 本件は Peterfalvi §14 (field automorphism/Dade) で
  BG §14 とは別物 — lane-h は territory 学習が要る
