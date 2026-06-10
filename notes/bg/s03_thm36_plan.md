# BG Theorem 3.6 形式化プラン (§3 p-length-one サブプログラム, 2026-06-07)

worktree `bg-s10-spine`。§10 スパインの根本ブロッカー (10.6 経由) として着手。
**Thm 3.6 は単独定理でなく §3 サブツリーの頂点**である。下から積む。

## Thm 3.6 (mmd L955)

「`G` 可解奇数位数, `H ⊴ G` normal Hall, `R` を `H` の補群, `R₀ ≤ R` prime order `r` で
`C_H(R₀)` が Z-群。任意素数 `p` で `[H,R]` は p-length one」。
証明 = 最小反例法、~4 ページ、equation (3.6)–(3.38)。

### 証明フェーズ (equation 番号)
- **Phase A 還元** (3.6)–(3.11): `H=[H,R]` (3.6); 商帰納 (3.7); `O_{p'}(H)=1` (3.8, **Lem 1.21(b)**);
  `V=F(H)=O_p(H)` elementary abelian (3.9, **Lem 1.21(c)** + Lem 1.7/Thm 1.8/Prop 1.3); `C_H(V)=V`
  (3.10, Prop 1.3); `V` に唯一の minimal normal (3.11, **Lem 1.21(e)**)。
- **Phase B 補群 K の構造** (3.12)–(3.16): `U=preimage F(H/V)`, `K`= R-不変補群 (Prop 1.5a + S-Z);
  Frattini で `H=VN_H(K)` (3.12); `[K,P]≠1` (3.13); `[V,K]=V, C_V(K)=1` (3.14, Prop 1.6d + 3.11);
  `K=F(N_H(K))` (3.15); `C_H(K)⊆K` (3.16, Prop 1.3)。
- **Phase C R₀ の作用** (3.17)–(3.21): `[K,R₀]≠1` (3.17, Prop 1.4); `C_{KR₀}(V)=1` (3.18);
  `C_V(R₀)≠1` ⟸ **Thm 3.4** (3.18→faithful→[K,R₀]=1 矛盾); `|C_V(R₀)|=p` (3.19, Z-群); `C_P(R₀)=1`
  (3.20, Z-群); `P=[P,R₀]` (3.21, Prop 1.6a)。
- **Phase D G の構造確定** (3.22)–(3.31): 最小性帰納で `[X,P]=1 (X=X^{PR}⊂K)` (3.22); `G=VKPR₀`,
  `H=VKP, R=R₀` (3.23); `K=[K,P]` (3.24, Prop 1.6b); `K` は special q-群 (**Gorenstein 5.3.7**)
  + `C_{K/K'}(P)=1` (3.25); `K` exp q (3.26, Thm 1.13); `C_{PR}(K)=1` (3.28); `C_{PR}(K/K')=1`
  (3.29, Thm 1.8); `C_{K/K'}(R)≠1` (3.30, **Thm 3.4**); `|C_K(R)|=q, C_K(R)∩K'=1` (3.31, Z-群 + 3.26)。
- **Phase E K elementary abelian** (3.32)–(3.37): `K≠[K,R]` (3.32); `C_{[K,R]}(R)=1` (3.33);
  `[K,R]R` Frobenius (Lem 3.1); **Thm 3.5** で `[K,R]` abelian (3.34); `[K,R]` not P-invariant
  (3.35); `|K:Z(K)|≤q` ⟸ **Thm 2.6(a)** (✅) ⟹ `K` elem abelian (3.36); `|K|>q²` (3.37, Thm 2.6)。
- **Phase F 最終矛盾** (3.38–): `V=⊕V_i` (V_i=C_V(K_i)≠1, index-q K_i; **Prop 1.16** ✅);
  `RP` transitive on {V_i} (3.11); orbit 長さ解析 + `|V_1|=p` (3.19) + parity (n odd vs even) で矛盾。

## 依存サブツリーと状態

| 依存 | mmd | 状態 | 備考 |
|---|---|---|---|
| **Lem 1.21(a)** | L566 | ✅ | `hasPLengthOne_subgroup` (= p-length 部分群単調性, **10.6 でも必要**) |
| **Lem 1.21(b)** | L567 | ✅ | `hasPLengthOne_of_isPiPrime_normal_quotient`。(3.8) で使用 |
| **Lem 1.21(c)** | L568 | ✅ | `hasPLengthOne_of_isPGroup_normal_quotient`。(3.9) |
| **Lem 1.21(d)** | L569 | — bypass | `⟨p-elements⟩` 特徴づけ。(e) を product-core 経由にしたので不要 |
| **Lem 1.21(e)** | L570 | ✅ | `hasPLengthOne_of_inf_eq_bot`。(3.11)。product 埋め込み + (a) |
| **Thm 3.4** | L863 | ❌ 未 (本体) | 可解奇 G, normal Hall K + prime-order 補群 R, V 上 (char∤\|G\|), `C_V(R)=0 ⇒ [R,K]⊆C_K(V)`。reduction は Maschke/Prop1.5/Lem3.1/Lem3.3 で組める。**真の残り = BG §2 (Thm 2.5)**、Gorenstein 系は下記の通り被覆済 |
| **Thm 3.5** | L903 | ❌ 未 | Frobenius G=KR (K 可解, R cyclic prime), V 上, `C_V(R) 1-dim ⇒ K'⊆C_K(V)`。Clifford/Maschke/Wedderburn/Prop2.2/Lem3.3 |
| **Lem 3.3** | L845 | ✅ | S03b_Lemma33 `kernel_acts_trivially_of_centralizer_eq_bot` 等 |
| **Lem 3.1** | — | ✅ | S03 `isFrobeniusGroup_iff_complement_centralizer_inf_kernel_eq_bot` |
| **Gorenstein 5.3.7** (BG 番号; = 当 ed. **Gor 3.7/3.8/3.10**) | — | ✅ **被覆済** | coprime minimal 作用 ⇒ special + irred on K/K' + trivial K'。`S04e_GorThm37.exists_minimal_aInvariant_isExpPSpecial_of_pprimeAction_with_minimality` (sorry-free, AxiomsCheck:1250)。BG 3.4 では K に適用 (existence-of-minimal → K=Q bridge は §3.4 内部) |
| **Gorenstein 3.2.2** (Z(G) cyclic) | — | △ ほぼ被覆 | faithful irreducible ⇒ Z(G) cyclic。ℂ 版 machinery = Isaacs CTFG Cor 2.30 `SchurCenterBound.lean` (`exists_central_scalar` 他, sorry-free)。一般体 F 版 capstone = Schur→`Module.End` division ring + mathlib `isCyclic_of_subgroup_isDomain` で短い追加 |
| **BG Thm 2.5** (+ Prop 2.1/2.2/2.4, Gor 5.5.4-5) | L716 | ❌ 未 (真の frontier) | extraspecial+cyclic faithful irred の最終矛盾。**Gorenstein でなく BG 自前 §2 表現論**。Thm 3.4 完成の本丸。下記 §2 ↔ Peterfalvi 棚卸し参照 |
| §1 Prop1.3/1.4/1.5/1.6/1.7/1.8/1.13/1.16, Thm2.6 | — | ✅ (要再確認) | S01_Solvable / S01b_Prop116 / S02_Representations (使用時に各個検証) |
| special q-group def `IsSpecial` | — | ✅ def | GroupTheory/IsExtraspecial.lean:84 |

## BG §2 ↔ Peterfalvi `RepresentationTheory` 棚卸し (2026-06-07 検証, main `ae2eccc`)

Peterfalvi 用に構築された `OddOrder/GroupTheory/RepresentationTheory/*` 共有 module が BG §2 をどこまで
被覆するか、実測 (decls / LOC / 体)。**「sorry-free だが空 skeleton」の罠に注意**([[scaffold-sorry-free-not-done]])。

| BG §2 | RepresentationTheory module | 実体 | 体 | BG (一般体 F, char∤\|G\|) で使えるか |
|---|---|---|---|---|
| **Prop 2.1** (Schur/abs irred) | `AbsolutelyIrreducible.lean` | **空 skeleton** (0 decls, issue #) | — | ❌ 未。S02 に signature 案のみ |
| **Prop 2.2** (Clifford) | `Clifford.lean` | ✅ 実体 (65 decls, 1172 LOC, sorry-free) | **ℂ 限定** (`Representation ℂ G V`) | △ ℂ専用 ⇒ BG 一般体は **base-change か一般体版**要 |
| **Prop 2.4** (eigenspace under cyclic) | `EigenspaceUnderCyclicAction.lean` | ✅ 実体 (48 decls, 918 LOC, sorry-free) | **一般体** (`[Field F]`) | ◯ 直接再利用可 |
| **Thm 2.5** (extraspecial faithful) / Gor 5.5.4-5 | `ExtraspecialFaithful.lean` | **空 skeleton** (0 decls, issue #34) | — | ❌ 未。Thm 3.4 本丸 |
| **Thm 2.6** (奇数 2-dim) | `PGroupFixedVector.lean` + S02 | ✅ sorry-free (`odd_two_dim_abelian` 他) | 一般体 | ◯ 完了 |
| **Gor 3.2.2** (Z cyclic) | `SchurCenterBound.lean` | ✅ 実体 (= Isaacs CTFG Cor 2.30) | **ℂ 限定** | △ 一般体 capstone 短い追加要 |

**結論**: Peterfalvi 進捗は **大量の再利用可能な ℂ 表現論 + 一部一般体 module** を提供するが、BG §2 を**完全代替はしない**。
(1) Thm 2.5 / Prop 2.1 は空 skeleton で未着手、(2) Clifford/Schur は **ℂ 限定**で BG の一般体 F 設定に直接は乗らない
(BG Thm 2.5 証明自身が代数閉体へ base-change するので、その橋 or ℂ-module の代数閉体一般化が要)。
Prop 2.4 (eigenspace) のみ一般体で即再利用可。**Thm 3.4 着手時の設計判断 = §2 を「ℂ/代数閉体で組んで base-change」か「一般体で再構築」か**。

## base-change レイヤ確立 + Thm 3.4 の真の bottleneck (2026-06-07, main)

**✅ base-change インフラ完了** (`OddOrder/GroupTheory/RepresentationTheory/BaseChange.lean`, 共有レイヤ, sorry-free):
- `baseChangeRepresentation` (+ `_apply_tmul`, `_faithful`) — S02 から移設 (scalar 拡張 `F→K`)
- `invariants_baseChangeRepresentation_eq_bot` — **BG (2.9)** `C_V(R)=0 ⇒ C_{K⊗V}(R)=0` (flat + `piRight`)
- `baseChangeRepresentation_comp` — restriction 互換 (部分群 `H=Z(P)` へ (2.9) 適用)
- **BG (2.8) (dim 不変) は意図的に省略**: Thm 2.5 の "C_V(H)≠0" 方向専用で、Thm 3.4 は "C_V(H)=0 ⇒ h=pⁿ+1" 方向 (= (2.9) 経由) しか使わない。demand-driven。

**Thm 3.4 の残り = Thm 2.5 本体 = 代数閉体上の extraspecial 表現論** (repo・mathlib に**無い**が **mathlib の Wedderburn–Artin (`RingTheory/SimpleModule/IsAlgClosed.lean`) + Schur で構築可能**, from-scratch ではない)。bottom-up:
1. **Prop 2.1** (faithful absolutely irreducible ⇒ `E(P)=Hom_F(V,V)`; Burnside) — Wedderburn-Artin/alg-closed から。`AbsolutelyIrreducible.lean` は空 skeleton。
2. **Gor 5.5.4-5** (extraspecial faithful irreducible: 中心指標で決まり dim=pⁿ; 二乗和 `p^{2n}·1+(p-1)(pⁿ)²=|P|` から) — `ExtraspecialFaithful.lean` 空 skeleton (issue #34)。
3. **Prop 2.2(a)** (Clifford `V_P=M`) — `Clifford.lean` は ℂ 限定ゆえ代数閉体版 or base-change。
4. **Prop 2.4(j)(k)** (eigenspace counting) — ✅ `EigenspaceUnderCyclicAction` (一般体)。
5. **Thm 2.5 assembly** → Thm 3.4 special case (K extraspecial) → 矛盾 (h=qⁿ+1 even vs odd)。
これは複数セッションの表現論サブプロジェクト。char-p (有限体) のため ℂ-Clifford は不可、代数閉体 F̄ 版が要る。

## 推奨着手順序 (bottom-up)

1. **Lem 1.21** (新ファイル `OddOrder/BG/Ch1_Preliminary/PLength.lean` 拡張 or `S01d_Lemma121.lean`)。
   自己完結 (oPiPrimePiCore/oPiCore 商対応 API は S06 に precedent: 第3同型 + `oPiCore_compl_le_oPiPrimePiCore` +
   `oPiPrimePiCore_eq_oPiCore_of_compl_bot`)。**(a)=10.6 でも再利用**。順序 (a)(b)(c) → (d) → (e)。
2. **Thm 3.4** (S03 新ファイル)。表現論。Lem 3.3 (✅) を使う。
3. **Thm 3.5** (S03 新ファイル)。Clifford/Maschke/Wedderburn が要 (mathlib `Representation`/`Module` + 既存 S02)。最重量。
4. **Gorenstein 5.3.7** (special q-群)。`references/gorenstein/finite-groups.{pdf,mmd}` 参照。
5. **Thm 3.6 本体** (S03 新ファイル `S03d_Thm36.lean`)。Phase A–F を組む。

## メモ
- Thm 3.6 は 10.6 の r_p≥3 ケースのエンジン。10.6 はさらに Lem 10.4(b) (lane A1) も要 ([[s10_spine_blockers]])。
- Lem 1.21(a) を landing すれば 10.6 の reduction (H≤M⇒) が解け、10.6 は「easy case 完成 + hard case=Thm3.6+10.4b」に縮む。
- このセッションの成果: 10.14(d) landing (f21eb12) + スパイン/§3 ブロッカー精査。

## Lemma 1.21 着手状況 (2026-06-07)

ファイル `OddOrder/BG/Ch1_Preliminary/PLengthTransfer.lean` (新規)。**(b)(c) + 全 infra 完了 (sorry-free)**。

**✅ Landed (sorry-free):**
- `card_quotient_oPiPrimePiCore_eq` / `hasPLengthOne_iff_card_quotient` (`4a9bf08`): 第3同型 bridge
  `|G/O_{p',p}(G)| = |(G/O_{p'}(G))/O_p(…)|`。(a)–(e) 共通の出発点。
- `oPiCore_quotient_eq_of_isPiGroup` (`db0a10d`): **汎用 engine** — `H ⊴ G` が π-群 ⇒
  `O_π(G/H) = O_π(G).map mk'` (`|N|=|H|·|Kbar|` + `primeFactors_mul` + `IsPiGroup.le_oPiCore`)。(b)=π{p}ᶜ, (c)=π{p}。
- **(b)** `hasPLengthOne_of_isPiPrime_normal_quotient` (`1179617`): normal `p'` 商。
- `oPiPrimePiCore_eq_oPiCore_of_compl_bot` (`6a7a705`, S06 private を §1 layering 維持で再証明)。
- **(c)** `hasPLengthOne_of_isPGroup_normal_quotient` (`6a7a705`): normal `p` 商 + `O_{p'}(G/H)=1`。

**(a) 用 building block 4つ landed (sorry-free, overnight loop 2026-06-07):**
- `le_oPiPrimePiCore_of_quotient_isPGroup` (`2ffd94a`): `K⊴G`, `K.map(mk' O_{p'}(G))` p-群 ⇒ `K ≤ O_{p',p}(G)`。
- `isPGroup_map_oPiPrimePiCore` (`aa64421`): `O_{p',p}(G).map(mk' O_{p'}(G))` は p-群 (=`O_p(G/O_{p'}(G))`)。
- `oPiCore_compl_subgroupOf_le` (`885f8ca`): `(O_{p'}(G)).subgroupOf H ≤ O_{p'}(↥H)`。
- `isPGroup_inf_map_oPiPrimePiCore` (`3b841e9`): `(O_{p',p}(G)⊓H).map(mk' O_{p'}(G))` は p-群。

**✅ (a) DONE** `hasPLengthOne_subgroup` (`2271b55`, crux `oPiPrimePiCore_subgroupOf_le` = `5aeb6f0`):
`hasPLengthOne p G ⇒ hasPLengthOne p ↥H`。crux は `A=O_{p',p}G⊓H` からの 2 hom `gA`(→G/O_{p'}G, range=p群)
/`fA`(→↥H/O_{p'}↥H, range=K.map mk') で `ker gA ≤ ker fA` (`oPiCore_compl_subgroupOf_le`) ⇒ `quotientKerEquivRange`
+`index_dvd_of_le` で `|range fA| ∣ |range gA|`=p冪 ⇒ IsPGroup ⇒ `le_oPiPrimePiCore_of_quotient_isPGroup`。
最終 index 鎖は `index_dvd_of_le` + `relIndex_dvd_index_of_normal` (O_{p',p}G normal)。**(a) は Thm 10.6 の H≤M reduction を解く**。

**✅ Lemma 1.21 完了: (a)(b)(c)(e) すべて sorry-free + axiom-clean。(d) は bypass (不要)。**
PLengthTransfer.lean を `OddOrder.lean` root に配線済 (full build 3587 + AxiomsCheck allowlist OK)。

(e) は product 埋め込み経由で landing (2026-06-07, この章の最終チャンク):
- ✅ `oPiCore_prod` (`ee73dac`): `O_π(A×B) = O_π A ×' O_π B`。product 段の土台。
- ✅ **(e)-1 iso 不変** `hasPLengthOne_of_mulEquiv (e : G ≃* G')`: bridge の double quotient を
  `QuotientGroup.congr` + `oPiCore.map_eq_of_mulEquiv` で O_{p'}/O_p の 2 段 transport ⇒ `Nat.card` 不変。
- ✅ **(e)-2 product 商 iso** `quotientProd_mulEquiv : (A×B)/(H ×' K) ≃* (A/H)×(B/K)`:
  `quotientKerEquivOfSurjective (prodMap (mk' H)(mk' K))` (`ker_prodMap`+`ker_mk'`) + `quotientMulEquivOfEq`。
- ✅ **(e)-3 `hasPLengthOne_prod`** A,B plen1 ⇒ A×B plen1: double quotient を (e)-1/(e)-2/`oPiCore_prod` で
  `DQ(A×B) ≃* DQ(A)×DQ(B)` に分解 ⇒ `Nat.card_prod` + `Nat.Prime.dvd_mul`。
- ✅ **(e) 本体** `hasPLengthOne_of_inf_eq_bot`: `(mk' H).prod (mk' N) : G →* (G/H)×(G/N)`,
  `ker = H⊓N = ⊥` (`ker_prod`) ⇒ injective ⇒ `MonoidHom.ofInjective` で `G ≃* range`;
  `hasPLengthOne_prod` + `hasPLengthOne_subgroup` (=1.21a) + (e)-1 iso 不変。
- **(d)** `hasPLengthOne ⟺ ⟨p-elements⟩=O^{p'}` は (e) 近道で回避 (不要)。Thm 3.6 (3.11) は (e) を cite。

**Thm 3.6 残ブロッカー (1.21 完成済, ここから本丸)**: **Thm 3.4** (L863) + **Thm 3.5** (L903)
= 表現論 (Clifford/Maschke/Wedderburn, 最重量) + **Gorenstein 5.3.7** (special q-群)。

**進捗ログ**: overnight loop (`4a9bf08`..`3b841e9`, 7 commits: foundation+(b)+(c)+(a) building block 4つ)、
朝 attended (`5aeb6f0` crux + `2271b55` (a) 完成)、(e) landing (このセッション: (e)-1〜本体 4 補題 +
root 配線)。**Lemma 1.21 全完。次 = Thm 3.4 着手** (S03 表現論新ファイル, Lem 3.3 ✅ を使う)。

## ✅ 2026-06-09 session 4 cont. (a-keystone): Thm 3.4/3.5 完成後の Thm 3.6 着手準備 — 依存監査 COMPLETE

**Thm 3.4 (`S03d.thm34`) + Thm 3.5 (`S03e.thm35`) とも任意体で完全形式化済** (sorry-free+axiom-clean,
AxiomsCheck 登録)。⟹ Thm 3.6 の 2 大表現論ブロッカーは解消。残りの依存を全て **repo 内で実在確認**:

| 依存 | 実体 (検証済 exact name) |
|---|---|
| Lem 1.21(b) | `PLengthTransfer.hasPLengthOne_of_isPiPrime_normal_quotient` |
| Lem 1.21(c) | `PLengthTransfer.hasPLengthOne_of_isPGroup_normal_quotient` |
| Lem 1.21(e) | `PLengthTransfer.hasPLengthOne_of_inf_eq_bot` |
| Lem 1.21(a) | `PLengthTransfer.hasPLengthOne_subgroup` |
| Thm 3.4 | `S03d.thm34` (一般体), `S03d.thm34_algClosed` |
| Thm 3.5 | `S03e.thm35` (一般体), `S03e.thm35_algClosed` |
| Lem 3.3 | `S03b.kernel_acts_trivially_of_centralizer_eq_bot` 他 |
| Prop 1.3 | `S01_Solvable:181` (Fitting self-centralizing) |
| Prop 1.5(a)(b)(c)(e) | `S01_Solvable:655/1401/688/1480` |
| Prop 1.6(b) | `OperatorQuotientAction:101` (semidirect-product 形, `[[H,R],R]=[H,R]`) |
| Prop 1.6(c)(d) | `S01_Solvable:1521/1540` |
| Lem 1.7 | `S01_Solvable:1575+` / `FrattiniPGroup` |
| Prop 1.16 | `S01b_Prop116` |
| Thm 1.8 | `S01_Solvable:1702` (Burnside operator on p-group) |
| Thm 1.13 | `CriticalSubgroup` (`S6`/`S8` 等) |
| Thm 2.6(a) | `S04_PGroupsSmallRank:86/96` |
| Gor 5.3.7 | `S04e.exists_minimal_aInvariant_isExpPSpecial_of_pprimeAction_with_minimality` |
| IsZGroup | `OddOrder.GroupTheory.IsZGroup` (ZGroup.lean:26; ⚠ mathlib `_root_.IsZGroup` と曖昧→明示修飾) |

**✅ statement 型検証済** (`S03f_Thm36.lean`, **local untracked scaffold**, proof = sorry, leaf build 3016 green,
long-line 0)。exact form:
```lean
theorem thm36 {G} [Group G] [Finite G] [IsSolvable G] (hodd : Odd (Nat.card G))
    {H R : Subgroup G} [H.Normal] (hcompl : Subgroup.IsComplement' H R)
    (hHall : Nat.Coprime (Nat.card ↥H) (Nat.card ↥R))
    {R₀ : Subgroup G} (hR₀R : R₀ ≤ R) (hR₀p : ∃ r : ℕ, r.Prime ∧ Nat.card ↥R₀ = r)
    (hZ : OddOrder.GroupTheory.IsZGroup ↥(H ⊓ Subgroup.centralizer (R₀ : Set G)))
    {p : ℕ} (hp : p.Prime) : hasPLengthOne p ↥(⁅H, R⁆ : Subgroup G)
```
docstring に Phase A–F の equation-by-equation roadmap 込み。**bare-sorry は commit しない方針** (merge-monitor
の sorry-不増 auto-merge を阻害しないため; thm34 も untracked scaffold だった先例)。

**▶ 次セッション (Thm 3.6 本体, multi-session)**: minimal-counterexample induction backbone
(`thm36_aux` を thm34_aux/thm35_aux 型で strong induction on `|G|`) を組み、Phase A (3.6–3.11) から着地。
- (3.6) は Prop 1.6(b) の semidirect-product 形を `⁅H,R⁆ < H` ケースの `⁅⁅H,R⁆,R⁆=⁅H,R⁆` に適応する要あり。
- Phase A の reusable standalone helper 候補: `F(H)=O_p(H) when O_{p'}(H)=1` (Fitting=∏O_q 分解)。
- 最重量は Phase D–F (Gor 5.3.7 適用 + special q-group 構造 + orbit-length parity 矛盾)。

## ✅ 2026-06-09 session 5 (a-keystone): インフラ 3 commit + Phase A (3.6) 着地

このセッションは **standalone infra を 3 commit + scaffold で thm36_aux backbone + (3.6) を完全証明**
(後者は untracked scaffold ゆえ未 commit、precedent 通り)。

### committed infra (3 commit, full build 3618 green, all axiom-clean)
1. **Z-群インフラ** (`af71f3a6`, `OddOrder/GroupTheory/ZGroup.lean`):
   - `isZGroup_iff_mathlib`: repo `OddOrder.GroupTheory.IsZGroup` ↔ mathlib `_root_.IsZGroup`
     (フィールド同一)。これで mathlib の Z-群 API (`of_injective`/`of_surjective` 部分群/商閉包、
     `exponent_eq_card`、`IsPGroup.isCyclic_of_isZGroup`) が使える。
   - `card_eq_prime_of_isZGroup_exponent_dvd`: 非自明 Z-群で全元 `g^p=1` ⟹ `|G|=p`。
   - `card_eq_prime_of_le_isZGroup`: `A ≤ Z` (Z-群)・非自明・exponent|p ⟹ `|A|=p`。
     **⟹ (3.19) `|C_V(R₀)|=p`、(3.31) `|C_K(R)|=q` で直接使う**。
2. **actionCommutator↔subgroup 基盤橋** (`c307c0fa`, `OperatorQuotientAction.lean`):
   `actionCommutator_conjNormal_map_subtype_eq : (actionCommutator (conjNormal∘R.subtype)).map H.subtype = ⁅H,R⁆`
   (`H ⊴ G`)。内部共役作用の actionCommutator 言語 ↔ 部分群交換子 `⁅H,R⁆` の翻訳土台。
3. **Prop 1.6(b) subgroup 形** (`fabbeed1`, `OperatorQuotientAction.lean`):
   `commutator_commutator_right_eq : ⁅⁅H,R⁆,R⁆=⁅H,R⁆` (`H ⊴ G`, coprime, `G` solvable)。
   `actionCommutator_restrict_self_map_subtype_eq` (= `[[N,A],A]=[N,A]`、`⁅H,R⁆⊴G` 不要) を
   2 段 nest して bridge #2 経由で導く。**核 = nested generator 橋** (`toMulAutHom_apply_val` で
   制限作用が φ と一致、`↑↑(nN·(ψr)nN⁻¹)=⁅↑↑nN,↑r⁆`)。⟹ (3.6)/(3.24)/(3.32) で使う。

### scaffold (`S03f_Thm36.lean`, **untracked**, leaf build 3016 green, 唯一 real sorry = (3.7)-(3.38))
- `thm36_aux` (strong induction on `|G|`) + `by_contra hcounter` backbone を組んだ。
- **✅ (3.6) `⁅H,R⁆ = H` を完全証明** (sorry-free within (3.6)):
  - subgroup-IH を `S := ⁅H,R⁆ ⊔ R` (= `⁅H,R⁆R`) に適用 (thm34 の wiring_check パターン)。
  - `S ⊴`-normality: `subgroup_le_normalizer_commutator_self R H` (Isaacs Lem 4.1, 仮定なし) +
    `commutator_comm` で `R ≤ N(⁅H,R⁆)`、`Subgroup.le_normalizer` で `⁅H,R⁆ ≤ N(⁅H,R⁆)`。
  - **Z-群 hyp transport** (新パターン): `C_S(R₀').map S.subtype ≤ ⁅H,R⁆⊓C_G(R₀) ≤ H⊓C_G(R₀)`
    ⟹ `IsZGroup.of_injective` (`inclusion_injective hle`) + `equivMapOfInjective` で `IsZGroup ↥(C_S(R₀'))`。
  - 結論橋: IH → `hasPLengthOne p ↥⁅H'.subgroupOf S, R'.subgroupOf S⁆`、`map_commutator`+
    `subgroupOf_map_subtype` で `(...).map S.subtype = ⁅⁅H,R⁆,R⁆`、`equivMapOfInjective`+
    `hasPLengthOne_of_mulEquiv` で transfer、`commutator_commutator_right_eq` で `=⁅H,R⁆` ⟹ `hcounter` 矛盾。

### 次セッション (Phase A 続き (3.7)–(3.11) → Phase B–F)
- **(3.7) 商 IH** (`G/X`, `1≠X⊴H` R-invariant): thm36_aux の **新しい IH 適用形** (subgroup でなく商)。
  - `X ⊴ G` (char H ◁ G より)、`G/X` で `H/X` normal Hall、`R` 商で補群、`R₀` 商 prime。
  - **Z-群 transport (商側)**: Prop 1.5(d) `C_{H/X}(R₀)=C_H(R₀)X/X` (= image of Z-群) ⟹
    mathlib `of_surjective` で Z-群。**Prop 1.5(d) の clean 形** (`C_{G/N}(A)=C_G(A)N/N`) の repo 所在を
    要確認 (`S03_FrobeniusActions` に bridge 形あるが `hlift` 付き; Isaacs Cor 3.28 が underlying)。
  - (3.7) は (3.6) `H=⁅H,R⁆` を使い `⁅H/X,R⁆=H/X` ⟹ `H/X` plen1。
- **(3.8) `O_{p'}(H)=1`**: `O_{p'}(H)≠1` なら X:=O_{p'}(H) で (3.7) + Lem 1.21(b) ⟹ H plen1 ⟹ 矛盾。
- **(3.9) `V=F(H)=O_p(H)` elem abelian**: `F(H)=O_p(H)` (O_{p'}=1; **opCore↔oPiCore 橋 + fitting sup-split
  が要**, `fitting=⨆opCore p`/`oPiCore {p}ᶜ=O_{p'}`)、Φ(V)=1 reduction (Lem 1.21(c)+Thm1.8+Prop1.3)、Lem 1.7。
- **scaffold の既知 cleanup (commit 前に要)**: long-line 6 箇所 (117,123,153,155,188,191) を ≤100 に。
- 最重量は依然 Phase D–F (Gor 5.3.7 + special q-group + orbit-parity)。

## ✅ 2026-06-09 session 5 cont. (a-keystone, /loop 自走): (3.7) 商 IH 完全証明 COMPLETE

scaffold `S03f_Thm36.lean` (untracked, leaf 3016 green) で **(3.7) `h37` を sorry-free 化**。
唯一の real sorry は最終 (3.8)-(3.38) のみ。⟹ **Phase A の (3.6)+(3.7) 完成**。

**Prop 1.5(d) = `OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient` (実在確認・Cor 3.28 element 形)**:
`{φ : A →* MulAut G}(hCop : Coprime |A| |G|)(hSolv){N⊴G}(hN_inv : IsAInvariant φ N){g}
(hg_fix : ∀ a, ∃ n∈N, φ a g = g*n) : ∃ c, (∀ a, φ a c = c) ∧ ∃ n∈N, c = g*n`。**再調査不要**。

`h37 : ∀ (X : Subgroup G) [X.Normal], X ≠ ⊥ → X ≤ H → hasPLengthOne p (↥H ⧸ X.subgroupOf H)`:
- easy transports: hcardQ (`card_eq_card_quotient_mul_card_subgroup` + `lt_mul_iff_one_lt_right`)、
  hoddQ、hHQnorm (`Normal.map` + `mk'_surjective`)、hcomplQ (`S03.quotient_complement_of_normal_le_kernel`)、
  hHallQ (`card_map_dvd` ×2)、hR₀pQ (mk'X が R₀ 上単射: `Disjoint R₀ X`=`hcompl.disjoint.symm.mono`、
  `MonoidHom.ofInjective`+`range_comp`)。
- **hZQ (Z-群 transport, 核)**: 共役作用 `φ:=conjNormal∘R₀.subtype`、`hval`、`isAInvariant_iff_smul_mem`
  +`Normal.conj_mem` で N=X.subgroupOf H 不変、`coprime_fixedPoints_quotient` で
  `C_{H/X}(R₀) ≤ (H⊓C_G(R₀)).map mk'X` (hg_fix は商内可換 `hcomm` から: `← eq_one_iff`+`← mk'_apply`+
  `simp[map_mul,map_inv]`+`hcomm a`+`group`; **GOTCHA**: eq_one_iff は coe `↑` 形ゆえ `← mk'_apply` で
  mk' に変換要、`(⟨h,hhH⟩:G)=h` は中間 `hnnval` で吸収)、image-of-Z は `of_surjective(subgroupMap_surjective)`、
  subgroup-of-Z は `of_injective(inclusion_injective)`。
- hiso `↥H⧸X.subgroupOf H ≃* ↥(H.map mk'X)`: `quotientKerEquivRange(mk'X∘H.subtype)` + ker=X.subgroupOf H
  (`ext`+simp) + range=H.map mk'X (`range_comp`) + `quotientMulEquivOfEq`/`subgroupCongr`。
- bridge `⁅HQ,RQ⁆=HQ`: `← map_commutator` + h36。conclusion `hasPLengthOne_of_mulEquiv hiso.symm`。

**▶ 次 = (3.8) `O_{p'}(H)=1`**: `O_{p'}(↥H)≠1` なら X:=`(O_{p'}(↥H)).map H.subtype` (char H⟹⊴G, ≤H) で
h37 → `H/X` plen1 → Lem 1.21(b) `hasPLengthOne_of_isPiPrime_normal_quotient` (N=O_{p'}(↥H), p'-群) ⟹
H plen1 = ⁅H,R⁆ plen1 (h36) ⟹ hcounter 矛盾。**要: O_{p'}(↥H) を Subgroup G に上げる + char⟹⊴G**。
→ (3.9) V=F(H) (opCore↔oPiCore + fitting sup-split) → (3.10)(3.11) → Phase B-F。正本=本ファイル「session 5 cont.」。

## ✅✅ 2026-06-10 session 6 (a-keystone): Phase A **完成** ((3.8)–(3.11) 全着地)

**Phase A (3.6)–(3.11) すべて scaffold `S03f_Thm36.lean` で sorry-free。残 real sorry = Phase B–F のみ。**
(3.8) も実は session 5 cont. の handoff 後に着地済だった (h38 完成、(3.9) Part1 `hfit` も)。本 session の成果:

### committed: (3.9) infrastructure (S03f_Prelim.lean, commit `c4497132`, full build 3619 green, axiom-clean)
標準ヘルパー 4 本 (commit 時点 namespace `OddOrder.BG.Ch1.S03f`; うち Burnside element 形は
後に S01 へ移動 → 下記):
- `mulAut_eq_one_of_coprime_orderOf_of_frattini`: Thm 1.8 の **element 形** — p-群 H の p'-order
  automorphism が Φ(H) mod 自明 ⟹ =1。`burnside_operator` を cyclic `⟨f⟩` に適用。
  **✅ 2026-06-10 consolidate 済 (task_1f77b0d7, commit `ff28b600`)**: S04 private 版と本 public 版を
  統合し `OddOrder.BG.Ch1.S01` (`burnside_operator` の隣) へ移動。以後は下記 (3.9) 核 + S04 Lem 4.17 が
  `S01.mulAut_eq_one_of_coprime_orderOf_of_frattini` を参照 (S03f には残らない)。
- `isPGroup_of_forall_eq_one_of_not_dvd_orderOf`: 非自明 p'-元なし ⟹ p-群 (p'-part
  `g^(p^vₚ(orderOf g))` の位数 = `ordCompl[p]` で p 互素、それが自明 ⟹ g は p冪位数)。
- `frattini_fitting_map_characteristic`: `(frattini ↥(fitting Hb)).map (fitting Hb).subtype` は Hb で
  **characteristic** (char-of-char; `characteristicRestrictMulEquiv` は使わず `φ.subgroupMap V`+
  `subgroupCongr` で restriction を自前構成)。**characteristic 強度が要**: Hb=↥H・H◁G で G-lift normal が
  mathlib instance `ConjAct.normal_of_characteristic_of_normal` で自動 + oPiCore helper の `[Normal]` も自動。
- `oPiCore_compl_quotient_frattini_fitting_eq_bot` ⭐ (3.9 核): F(Hb) p-群 ⟹ `O_{p'}(Hb/Φ(F(Hb)))=⊥`。
  Q=Hb/Φ で V̄ (p) と Ō=O_{p'}(Q) (p') は coprime normal ⟹ `⁅V̄,Ō⁆=⊥` (commutator_le_inf +
  `inf_eq_bot_of_coprime`)、pull back で `⁅V,W⁆≤Φ` (W=Ō.comap mk')。p'-元 w∈W: conjNormal w を
  Burnside helper で =1 ⟹ w∈C_Hb(V)≤V (Prop 1.3 `centralizer_fitting_le_fitting`) ⟹ w∈V (p群) p'元
  ⟹ w=1 ⟹ W は p群 ⟹ Ō=W.map は p群かつp'群 ⟹ ⊥。

### scaffold `S03f_Thm36.lean` (untracked) に Phase A 完全配線 (leaf build 3017 green)
hfit の後に (3.9)–(3.11) を追加。**確立した文脈ファクト (Phase B が直接使う)**:
- `hVp : IsPGroup p ↥(fitting ↥H)` (= O_p(↥H), hfit + opCore_isPGroup)
- `hΦbot : frattini ↥(fitting ↥H) = ⊥` ((3.9) Part2-4: Φ(V)≠⊥ なら Phi を G-lift して h37+Lem1.21(c)
  `hasPLengthOne_of_isPGroup_normal_quotient` で H plen1 ⟹ hcounter 矛盾。`quotientMulEquivOfEq` で
  `↥H⧸X.subgroupOf H ≃* ↥H⧸Phi` transport [motive error 回避、rw 不可])
- `hVelem : IsElementaryAbelian p ↥(fitting ↥H)` (Lem 1.7c `frattini_eq_bot_iff_isElementaryAbelian`)
- `hCHV : centralizer (fitting ↥H : Set ↥H) = fitting ↥H` ((3.10) Prop 1.3 + hVelem.1 可換)
- **`h311 : ∀ (A B : Subgroup G) [A.Normal] [B.Normal], A ≤ H → B ≤ H → A ⊓ B = ⊥ → A = ⊥ ∨ B = ⊥`**
  ((3.11) を minimal-normal 抽象を経ず Phase B/F が実際に使う形で。両 nontrivial なら h37 A/h37 B +
  Lem 1.21(e) `hasPLengthOne_of_inf_eq_bot` (ambient ↥H, `A.subgroupOf H ⊓ B.subgroupOf H=⊥`) ⟹
  H plen1 ⟹ hcounter 矛盾)。

### ▶ 次セッション = Phase B (3.12)–(3.16)
- `U` = preimage of `F(H/V)` in `↥H`、`V` = Sylow-p of U、`K` = R-invariant complement (Prop 1.5(a) +
  Schur-Zassenhaus)。`P` = R-invariant Sylow-p of `N_H(K)` (Thm 1.13/critical 系)。
- (3.12) Frattini argument `H = V·N_H(K)`。(3.13) `[K,P]≠1` (else V=Sylow-p ⟹ H plen1)。
- **(3.14) `[V,K]=V, C_V(K)=1`**: Prop 1.6(d) `V=C_V(K)×[V,K]`、両 ◁ G、**`h311` で一方 ⊥**、`hCHV` で
  `C_V(K)≠V` ⟹ `C_V(K)=1`。**h311 がここで効く** (C_V(K), [V,K] を Subgroup G・normal・≤H で渡す)。
- (3.15) `K=F(N_H(K))`、(3.16) `C_H(K)⊆K` (Prop 1.3)。
- 最重量は Phase D–F (Gor 5.3.7 `S04e` 適用 + special q-group + orbit-parity)。Thm 3.4/3.5 は ✅ 済。
- **scaffold long-line cleanup を Thm 3.6 完成 commit 前に**: session 5 既知分 (117/123/153/155/188/191
  系) + 本 session 追加分 (371/372/390 系) を ≤100 codepoint に。正本=本ファイル「session 6」。

## ✅ 2026-06-10 session 6 cont. (a-keystone): Phase B foundation (Hall fact) 着地 + K-construction 精密化

別途ユーザーが Burnside element-form 重複を consolidate (`mulAut_eq_one_of_coprime_orderOf_of_frattini`
→ S01_Solvable に一本化, commit `ff28b600`, full build 3619 green)。

**scaffold に Phase B Part 1 (foundation) 着地** (leaf build green、残 sorry = K-construction〜3.38):
- `set V := fitting ↥H` (3.9/3.10 facts を fold)、`hVnorm`、**`hVoPi : V = oPiCore {p} ↥H`** (hfit +
  `oPiCore_singleton_eq_opCore`)。
- **`hFQ_compl`**: F(↥H/V) は {p}ᶜ-群。**変数分母形** `∀ N [N.Normal], N = oPiCore {p} ↥H →
  IsPiGroup {p}ᶜ (fitting (↥H⧸N))` で dependent-rewrite 回避。proof = Sylow-q of F(Q) を Q に push
  (`Sylow.normal_of_isNilpotent`+`Sylow.characteristic_of_normal`+`normal_pgroup_le_opCore`) ⟹
  ≤ oPiCore {p} Q = ⊥ (`oPiCore_quotient_self_eq_bot`) 矛盾。
- **`hp_ndvd : ¬ p ∣ |fitting (↥H⧸V)|`** ⟹ **V は U の Hall p-部分群**。
- **⚠ inline 重複**: hFQ_compl は S10 `fitting_quotient_oPiCore_isPiGroup_compl` と重複 (S10=BG Ch3 は
  scaffold の下流ゆえ import 不可)。untracked ゆえ committed dup でない。**Phase B commit 前に consolidate**
  (S10 の pSubgroup_le_opCore_of_le_fitting + fitting_quotient... を BG Ch1 base へ移動; S04
  `isPiGroup_singleton` 依存は inline 化)。

### ✅ K-construction setup (steps 1-3) 着地 — 一発 green (char-restriction の難所 解決)
- **U := `(fitting (↥H⧸V)).comap (QuotientGroup.mk' V)`**、**`hUchar : U.Characteristic`**
  (`Subgroup.Characteristic.comap_quotient_mk` [V char + fitting Q char]、一行)、`hVU : V ≤ U`。
- **🔑 R-作用** `φ := (MulAut.conjNormal (G:=G)(H:=H)).comp R.subtype` → `hU_inv : IsAInvariant φ U`
  (= `IsAInvariant.of_characteristic φ`, U char) → **`φU := hU_inv.toMulAutHom : ↥R →* MulAut ↥U`**。
- **`K' : Subgroup ↥U`** = `exists_aInvariant_hall (G:=↥U)(φ:=φU) hCopU ({p}ᶜ)` で取得;
  **`hK'_hall : IsHallSubgroup {p}ᶜ K'`** + **`hK'_inv : IsAInvariant φU K'`** (= R-不変補群)。
  hCopU = `hHall.symm.coprime_dvd_right (card_subgroup_dvd_card U)`。

### ▶ 次 = K の complement 性 + P + (3.12)–(3.16)
- **K は V の complement in U**: V Hall {p} of U (hp_ndvd ⟹ |V| が U の p-part)、K' Hall {p}ᶜ ⟹
  V·K'=U, V⊓K'=⊥ (coprime Hall product)。K (↥H 版) := `K'.map U.subtype`。
- **P** = R-不変 Sylow-p of N_H(K): `exists_aInvariant_sylow` (N_H(K) に R-作用, IsAInvariant)。
- **(3.12) Frattini** `↥H=V·N_H(K)`: U◁↥H(char), V◁↥H, K Hall p' of U, 全 Hall p' conjugate (`hall_C`)
  ⟹ ∀h, K^h=K^u (u∈U) ⟹ h∈N_H(K)·U ⟹ ↥H=U·N_H(K)=V·N_H(K)。
- (3.13) `[K,P]≠1`、**(3.14) `[V,K]=V, C_V(K)=1`** (Prop 1.6(d)+両◁G+**h311**+**hCHV**)、
  (3.15) K=F(N_H(K))、(3.16) C_H(K)⊆K。最重量は Phase D–F。正本=本ファイル「session 6 cont.」。

## ✅✅ 2026-06-10 session 7 (a-keystone): **Phase B (3.12)–(3.16) COMPLETE**

scaffold `S03f_Thm36.lean` (untracked, 1006 行, leaf build 3017 green) の唯一 real sorry = Phase C 以降
((3.17)–(3.38)) のみ。**Phase A+B 全て sorry-free**。

### committed: transport helpers ×4 (`S03f_Prelim.lean`, commit `05df50fa`, axiom-clean)
- `isAInvariant_map_subtype_of_restrict`: U A-inv + L (↥U) restrict-inv ⟹ `L.map U.subtype` A-inv
  (S01/S04e の private 重複の公開版; **Ch03 への consolidation は cleanup pass で**)。
- `normal_map_subtype_of_isAInvariant_conjNormal` ⭐: `H ⊔ R = ⊤`, X ⊴ ↥H + R-inv (conjNormal∘subtype)
  ⟹ `X.map H.subtype ⊴ G`。(3.14) の C_V(K)/[V,K] の G-lift 正規性。Phase D でも使う。
- `fitting_map_le_of_mulEquiv` / `fitting_map_eq_of_mulEquiv`: F(G) の同型転送 ((3.15) が使用)。
- `isHallSubgroup_map_of_mulEquiv`: Hall の同型転送 (card は `card_map_of_injective`、index は
  `card_mul_index` ×2 + cancel)。(3.12) Frattini の conjugate-Hall。

### scaffold 着地分 (Phase B 全部; 確立済み文脈ファクト一覧 = Phase C が直接使う)
- `hK_le_U / hK_inv / hKcard / hK'p'`; `hUcard : |U| = |F(H/V)|·|V|` (ψ=mk'V∘U.subtype, ker=V.subgroupOf U
  [`hψker`], range=F(Q) [`hψrange`]); `hK'm : |K'| = |F(H/V)|` (p'-part 一意性, `hCop_mFidx` 経由);
  `hcomplVK : IsComplement' (V.subgroupOf U) K'`; **`hVK_sup : V ⊔ K = U`**; **`hVK_inf : V ⊓ K = ⊥`**。
- **N/P**: `N := Subgroup.normalizer (K : Set ↥H)` (⚠ mathlib normalizer は **Set 引数**、subgroup は
  coercion)、`hN_inv` (= `hK_inv.normalizer`)、`P := P'.map N.subtype` (P' = `exists_aInvariant_sylow`
  via `hN_inv.restrict`)、`hP_le_N / hP_inv / hPp`。⚠ φU/φN は `.restrict` を使う (`.toMulAutHom` は
  Ch04 の重複 def で `restrict_apply_val` が無い → session 7 で restrict に切替済)。
- **(3.12) `h312 : V ⊔ N = ⊤`**: hall_C を ↥U 内で (K'^hh ↦ K'^u)、commuting square `hsq`/`hsq'`
  (conjNormal/conj vs subtype; **`congr 1` だけで閉じる** — hom が defeq、ext/simp を足すと
  no-goals エラー)、`mem_normalizer_iff` で ↑u·hh ∈ N、分解 hh = ↑u⁻¹·(↑u·hh)。
  + `hVmap_bot / hNmap_top` (mk' V での像)。
- `hUmap / hKmap : U.map (mk' V) = F(H/V) = K.map (mk' V)`。
- **(3.13) `h313 : ⁅K,P⁆ ≠ ⊥`**: P-image ≤ C_Q(F(Q)) ≤ F(Q) (Prop 1.3 in Q) は p-群∩p'-群 ⟹ P ≤ V
  ⟹ Sylow P' ≤ ker(↥N ↠ H/V) ⟹ p ∤ |H/V| (`pow_succ_factorization_not_dvd`; **⚠ `rw [hNcard]` は
  factorization 指数内も書換える → calc で forward 構成**) ⟹ H plen1
  (`hasPLengthOne` + `oPiPrimePiCore_eq_oPiCore_of_compl_bot h38` + `hcard_eq` quotientMulEquivOfEq) ⟹ hcounter。
- **(3.14)**: `letI : CommGroup ↥V` (hVelem.1)、φKV := conjNormal∘K.subtype、Prop 1.6(d)
  `fixedPoints_isComplement_actionCommutator_of_abelian`、橋 `hAC` (= `actionCommutator_conjNormal_map_subtype_eq V K`)
  + `hFP : FP.map V.subtype = V ⊓ C_{↥H}(K)` (手証明)。`hconjK`/`hconjC` (N-共役で K/C(K) 不変,
  elementwise)、`hnormal_of_VN` (X ≤ V + N-conj 不変 ⟹ X ⊴ ↥H; V は abelian で中心化)、
  R-inv `hB_inv`/`hC_inv`、G-lift 正規 (helper ⭐)、`hCB_inf`/`hCB_sup` (complement の像)、
  **`h314C : V ⊓ C_{↥H}(K) = ⊥`** (h311 二分法; [V,K]=⊥ 枝は K ≤ C_H(V) =hCHV= V ⟹ K=⊥ ⟹ (3.13) 矛盾)、
  **`h314B : ⁅V,K⁆ = V`**、**`hVN_inf : V ⊓ N = ⊥`** (v∈V∩N ⟹ ⁅v,k⁆∈V⊓K=⊥ ⟹ v∈C(K))。
- **(3.15) `h315 : F(↥N).map N.subtype = K`** + `hKN_fit : K.subgroupOf N = F(↥N)`:
  eN := ofBijective (mk'V∘N.subtype) (inj=hVN_inf, surj=hNmap_top)、`heN_hom : eN.toMonoidHom = ψN`
  (ext+rfl)、fitting 転送 helper + `map_injective`。
- **(3.16) `h316 : C_{↥H}(K) ≤ K`**: `centralizer_le_normalizer` → ↥N 内で Prop 1.3 + hKN_fit。

### ▶ 次セッション = Phase C (3.17)–(3.21)
- **(3.17) `⁅K,R₀⁆ ≠ ⊥`** (最重量): 仮定 =⊥ ⟹ Prop 1.4 (`S01_Solvable:?` 要確認 — F(N)=K 中心化 ⟹
  N 中心化の形) で `⁅N,R₀⁆=⊥` ⟹ N ≤ C_H(R₀) (Z-群 hZ) ⟹ K cyclic ⟹ Aut K abelian ⟹
  `⁅N,R⁆ ≤ C_H(K) ≤ K` (3.16); 一方 `⁅N,R⁆ ≅ ⁅H/V,R⁆ = (H/V) ≅ N` ((3.6)+商) ⟹ P ≤ K、
  (|P|,|K|)=1 ⟹ P=⊥ ⟹ V Sylow ⟹ (3.13) と同じ矛盾ルート (p ∤ |H/V|... 要再構成)。
- (3.18) `C_{KR₀}(V)=⊥`: C_K(V) ≤ K∩C_H(V) =(3.10)= K∩V = ⊥; R₀ prime order なので C_{R₀}(V)=⊥ or R₀;
  後者なら R₀ ⊴ KR₀ ⟹ ⁅K,R₀⁆=⊥ contra (3.17)。
- (3.19) `|C_V(R₀)| = p`: C_V(R₀)=⊥ なら KR₀ faithful on V ⟹ **Thm 3.4** (`S03d.thm34`) ⟹
  ⁅K,R₀⁆=⊥ contra; ≠⊥ なら elem abelian + Z-群 (`card_eq_prime_of_le_isZGroup`) ⟹ =p。
- (3.20) `C_P(R₀)=⊥`: C_V(R₀) cyclic order p には p-冪 Aut なし ⟹ C_P(R₀) centralizes C_V(R₀)、
  C_P(R₀)×C_V(R₀) ≤ C_H(R₀) Z-群 (Z-群は Sylow cyclic ⟹ p-rank 1) ⟹ C_P(R₀)=⊥。
- (3.21) `P = ⁅P,R₀⁆`: Prop 1.6(a) (`fixedPoints_sup_actionCommutator_eq_top` 形) + (3.20)。
- 残最重量 = Phase D (Gor 5.3.7 `S04e` 適用) + Phase F (orbit-parity)。
- cleanup TODO (Thm 3.6 完成 commit 前): hFQ_compl ↔ S10 重複 consolidate / helper ×4 の Ch03 配置
  / private 2 copy 削除。正本=本ファイル「session 7」。

## ✅ 2026-06-10 session 7 cont. (a-keystone): **(3.17) COMPLETE** — BG 原文より短い経路で

scaffold 唯一 real sorry = (3.18)–(3.38)。(3.17) は **Prop 1.4 / [N,R]≅N counting / Aut-hom 構成を
全て回避**する短縮経路で着地 (上の旧プラン記載は obsolete):

### (3.17) 実装経路 (`h317 : ¬ (K.map H.subtype ≤ centralizer (R₀ : Set G))`)
仮定 hKcent ⟹
1. **K_G は nilpotent Z-群 ⟹ cyclic**: `K_G ≤ H ⊓ C_G(R₀)` (le_inf 直接! BG の N 経由は不要)、
   `IsZGroup.of_injective` + nilpotent (↥K ≅ ↥(K.subgroupOf N) `=hKN_fit=` ↥(F(↥N)) で
   `fitting.isNilpotent` 転送、`nilpotent_of_surjective`+`MonoidHom.coe_comp`) ⟹
   **mathlib instance `[Finite][IsZGroup][IsNilpotent] : IsCyclic`** (ZGroup.lean:127) が自動発火。
2. **F(H/V) cyclic**: `hKmap` + mk'V の K 上単射 (hVK_inf) + `MonoidHom.ofInjective`+`subgroupCongr`
   + `isCyclic_of_surjective`。
3. **φQ := `hV_inv.quotientMulAutHom`** (Ch04, ⚠ 二重 namespace
   `OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom`、フルネーム必須) +
   simp 補題 `quotientMulAutHom_apply_mk'`。
4. **actionCommutator φ = ⊤** ((3.6): bridge `actionCommutator_conjNormal_map_subtype_eq H R` +
   h36、element-chase で ⊤; ⚠ simpa は過剰変形するので手動) → **actionCommutator φQ = ⊤**
   (generator 転送 `hmap_le` + `map_top_of_surjective` calc)。
5. **🔑 `actionCommutator_le_centralizer_of_isCyclic_isAInvariant`** (OperatorQuotientAction:176,
   = cyclic normal A-inv S ⟹ [G,A] ≤ C_G(S); **Aut-cyclic-abelian 論法を完全内包**) を
   (Q, φQ, S=F(Q)) に適用 ⟹ `⊤ ≤ C_Q(F(Q))` ⟹ Prop 1.3 で `F(Q) = ⊤` ⟹ `p ∤ |Q|`
   (hp_ndvd + `Nat.card_congr Subgroup.topEquiv.toEquiv`) ⟹ **`hfalse_of_pndvd`** で矛盾。
- **refactor**: (3.13) の結末を `hfalse_of_pndvd : ¬ p ∣ |↥H ⧸ V| → False` に抽出
  ((3.13)/(3.17) 共有; `hasPLengthOne` rw + `oPiPrimePiCore_eq_oPiCore_of_compl_bot h38` +
  `quotientMulEquivOfEq hVoPi.symm` card 橋)。

### ▶ 次セッション = (3.18)–(3.21) (設計確定済)
- **(3.18) 形式**: `h318 : ((K.map H.subtype) ⊔ R₀) ⊓ centralizer (V.map H.subtype : Set G) = ⊥`
  (G-level)。証明: C := LHS。(i) C ⊓ K_G = ⊥ (c ∈ C∩K_G ⟹ ↥H に落として C_{↥H}(V) =hCHV= V ⟹
  V⊓K=⊥)。(ii) S₁ := K_G ⊔ R₀ 内で K_G ⊴ S₁ ((3.6) の S-block precedent: line 113-117 の
  `normal_subgroupOf_of_le_normalizer` パターン; R₀ は hK_inv の G-level conj で normalize)、
  `IsComplement' (K_G.subgroupOf S₁) (R₀.subgroupOf S₁)` (disjoint: hcompl.disjoint mono +
  normal_mul、(3.6) block コピー) ⟹ |S₁| = |K_G|·r。(iii) C ≠ ⊥ なら C.subgroupOf S₁ ⊴ ↥S₁
  (centralizer V_G ⊴ G: V_G ⊴ G instance [V char ↥H + H ⊴ G] + centralizer-of-normal normal;
  要 instance 確認、なければ elementwise) + C⊓K_G=⊥ ⟹ |C| ∣ |S₁:K_G| = r ⟹ |C|=r ⟹
  **C も R₀ も ↥S₁ の Sylow-r** (r ∤ |K_G|) ⟹ C normal Sylow ⟹ R₀ = C (mathlib Sylow 一意性;
  `Sylow.normal...unique` 系 or conjugacy `exists_smul_eq` で C^g = C) ⟹ R₀ ≤ centralizer V_G。
  (iv) すると ⁅K_G,R₀⁆ ≤ ... 直接: R₀ = C ⊴ S₁ ⟹ ⁅K_G,R₀⁆ ≤ K_G ⊓ R₀ = ⊥ (両 normal in S₁)
  ⟹ `commutator_eq_bot_iff_le_centralizer` で K_G ≤ C_G(R₀) ⟹ **h317 矛盾**。
- **(3.19) 形式**: `h319 : Nat.card ↥(V ⊓ Subgroup.centralizer ... R₀-in-↥H ...) = p` 級。
  **bridge 先例 = `AppA_PStability.lean:1541`**: `Representation (ZMod p) M (Additive ↥W)`
  (W elem abelian subgroup への conj 作用を `Representation.ofDistribMulAction` で; S03c_Thm37:90
  も同型)。手順: (i) C_V(R₀) ≠ ⊥ を出す: by_contra で thm34 を
  G' := ↥(K_G ⊔ R₀), K' := K_G.subgroupOf, R' := R₀.subgroupOf, V := Additive ↥V_G,
  ρ := conj-rep に適用 (hchar: (|G'| : ZMod p) ≠ 0 ⟸ p ∤ |K_G|·r [hK'p' + p≠r ⟸ r ∣ |R|

  coprime |H| ∋ p... 要 p ≠ r 補題: p ∣ |V| ∣ |H|, r ∣ |R|, hHall ⟹ p≠r]; hCV = by_contra 仮定;
  hcompl/hHall = (3.18) の (ii) で構築済を再利用) ⟹ `∀ g ∈ ⁅R',K'⁆, ρ g = 1` ⟹
  ⁅R₀,K_G⁆ ≤ centralizer V_G、⁅R₀,K_G⁆ ≤ S₁ ⟹ **h318 で ⁅R₀,K_G⁆ = ⊥** ⟹ h317 矛盾
  (`commutator_comm` で ⁅K,R₀⁆ 向き合わせ)。(ii) C_V(R₀) ≠ ⊥ + elem abelian (exponent p) +
  Z-群 hZ ⟹ `card_eq_prime_of_le_isZGroup` (ZGroup.lean:26 の repo 補題、session 5 infra) で
  **|C_V(R₀)| = p**。C_V(R₀) の ambient 選択は ↥H (V ⊓ centralizer-in-↥H of R₀-image?) でなく
  **G-level `V_G ⊓ C_G(R₀)`** が hZ (`H ⊓ C_G(R₀)`) と整合的 — 要 `≤ H ⊓ C_G(R₀)` は V_G ≤ H ✓。
- (3.20)(3.21) は session 7 プラン (上) のまま有効。(3.20) の「cyclic p-Sylow ⟹ 唯一 order-p
  部分群」は mathlib `IsCyclic` API (`IsPGroup.isCyclic_of_isZGroup` + cyclic p-群の部分群一意性
  `IsCyclic.card_orderOf_eq_totient` 系? 要探索) か ⟨x⟩·C_V(R₀) rank-2 で Z-群 Sylow-cyclic 矛盾。
- 正本 = 本ファイル「session 7 cont.」。scaffold 1090 行、leaf build 3017 green。

## ✅ 2026-06-10 session 7 cont.² (a-keystone): **(3.18) COMPLETE** (scaffold 1323 行, leaf 3017 green)

上記プラン通り着地。`h318 : ((K.map H.subtype) ⊔ R₀) ⊓ centralizer (V.map H.subtype : Set G) = ⊥`。
`obtain ⟨r, hr_prime, hr_card⟩ := hR₀p` を h318 の**直前**で展開済 (以降のフェーズでも r 使用可)。

実装メモ (プラン との差分・GOTCHA):
- `hS₁norm : S₁ ≤ normalizer (KG : Set G)`: R₀ 側は `mem_normalizer_iff` を **G-element レベル**で
  (x : G は subtype でないので Subtype.ext 不可); 逆向きは witness `(φ ⟨g⟩)⁻¹ k` +
  `MulAut.apply_inv_self` + `mul_left_cancel (mul_right_cancel ·)`。
- `hcompl₁` は (3.6) S-block のコピーパターンそのまま。`hr_ndvd_K : ¬ r ∣ |K|` は
  `Nat.Coprime.eq_one_of_dvd (hHall.coprime_dvd_left ·) ·`。
- `hC'norm` ((S₁ ⊓ C_G(V_G)).subgroupOf S₁ ⊴ ↥S₁): V_G ⊴ G は **手動 conj_mem** (h38 の
  X-normality パターン; instance 自動発火せず)、centralizer 部は calc 3 段。
- **|C'| ∣ r**: 埋め込み `(mk' KG').comp (C.subgroupOf S₁).subtype` + ker=⊥ (hCK) +
  **`Subgroup.card_dvd_of_injective`** (⚠ `Nat.card_dvd_of_injective` は存在しない) +
  `hquot_card : |S₁/KG'| = r` (card_eq_card_quotient_mul + hcompl₁.card_mul + cancel)。
- **C' = R₀' (|C'|=r 枝)**: C'≠R₀' なら C'⊓R₀'=⊥ (prime order ⟹ ⊥ or 等しい,
  `Nat.dvd_prime`+`eq_of_le_of_card_ge`) ⟹ R₀'↪S₁/C' injective ⟹ r ∣ |S₁/C'| ⟹
  r² ∣ |S₁| = |K|·r (`Nat.mul_dvd_mul_iff_right hr_prime.pos`) ⟹ r ∣ |K| 矛盾。
- 結末: R₀' = C' ⊴ ↥S₁ ⟹ `⁅KG',R₀'⁆ ≤ KG'⊓R₀' = ⊥` (`commutator_le_left/right` + 両 Normal) ⟹
  elementwise (`commutator_mem_commutator` + `commutatorElement_eq_one_iff_commute` + val) で
  KG ≤ C_G(R₀) ⟹ **h317 矛盾**。

## ✅✅✅ 2026-06-10 session 8 (a-keystone): **Phase C (3.19)–(3.21) COMPLETE = Phase A+B+C 全完**

scaffold 1684 行、唯一 real sorry = **Phase D–F ((3.22)–(3.38)) のみ**。leaf 3017 green。
**⚠ `set_option maxHeartbeats 1600000 in` を thm36_aux に付与** — 宣言が単一予算 200k を超過
(timeout が line 99 等あちこちに出たら予算切れのサイン; ファイル分割で最終解消予定)。

### 構造変更 (hoist)
- h318 の前に **Phase C ambient を hoist**: `set KG := K.map H.subtype` / `set VG := V.map H.subtype` /
  `set S₁ := KG ⊔ R₀` + hKG_le_S₁/hR₀_le_S₁/hKG_le_H/hS₁norm/hKG'norm/hdisjKR/**hcompl₁**/
  hR₀'card/hKG'card/hr_ndvd_K/**hVGnorm** (V_G ⊴ G 手動)。h318 は `S₁ ⊓ centralizer ↑VG = ⊥` 形に。
- scaffold が `OperatorMaschke` を import (**`OddOrder.BG.Ch1_Preliminary.mulAutToEnd` は public**;
  AppA の private とは別; S03f_Prelim への複製は不要だった)。
- `open scoped IsMulCommutative` を file top に追加 (CommGroup 経路)。

### (3.19) 実装 (`h319 : Nat.card ↥(VG ⊓ centralizer ↑R₀) = p`)
- 前提群: `hH_ne_bot` (H=⊥ なら plen1 で hcounter 矛盾; |quot| ∣ |group| は
  `⟨_, card_eq_card_quotient_mul_card_subgroup _⟩` 一行)、`hV_ne_bot` (fitting_ne_bot)、`ha0 : a ≠ 0`、
  `hpr : p ≠ r`、`hp_ndvd_S₁`、`hVGelem` (equivMapOfInjective 転送)。
- **Part 1 `h319a` (≠⊥) = thm34 初実消費**: AppA:1541 パターン踏襲 — `IsMulCommutative` haveI →
  `hpsmul` → `AddCommGroup.zmodModule` → `Module.Finite.of_finite` → ρ :=
  `mulAutToEnd ∘ conjNormal(H:=VG) ∘ S₁.subtype`、`hρ_apply` は rfl。hCV は by_contra 仮定から
  (toMul/ofMul + conjNormal_apply val-chase)。`S03d.thm34` 適用 → ⁅R₀,KG⁆ 各元が V_G 中心化
  → **h318 で ⊥** → `commutator_eq_bot_iff_le_centralizer` + `commutator_comm` → **h317 矛盾**。
- Part 2: `hA_exp` (exponent p, hoist 済) + `card_eq_prime_of_le_isZGroup hZ`。

### (3.20) 実装 (`h320 : P_G ⊓ centralizer ↑R₀ = ⊥`) — Sylow 機構レス
- `hPV_inf : P_G ⊓ VG = ⊥` (hVN_inf + hP_le_N + map_inf)。
- Cauchy `exists_prime_orderOf_dvd_card'` で order-p 元 y ∈ W := P_G ⊓ C。`hCnorm` (centralizer は
  中心化元の共役で不変, calc 7 段 + `Commute.inv_right`)。**A は `obtain ⟨A, hA⟩ : ∃ A, A = …`
  の opaque 形** (`set` だと文脈書換えが重い) + 必要箇所で `rw [hA]`/`hA ▸`。
- T := A ⊔ zpowers ↑y: `coe_mul_of_right_le_normalizer_left` (T=A·Y 集合分解) → T/A″ は
  mk y で生成 (`zpowers_le`/`mem_zpowers_iff`/zpow witness `Subtype.ext`+`coe_zpow`) →
  |T/A″| = orderOf(mk yT) (`Nat.card_zpowers`+`topEquiv.symm`) ∣ p (`orderOf_map_dvd`) →
  |T| ∣ p² → `IsPGroup.of_card`。
- T ≤ H⊓C (Z-群) → `IsZGroup.of_injective` + **mathlib `IsPGroup.isCyclic_of_isZGroup`**
  (⊤-subgroup 経由 + topEquiv) → T cyclic。
- 仕上げ: `IsCyclic.card_pow_eq_one_le` (`#{a | a^p = 1}` は **filter-univ と同形で直 unify、
  convert using 2 で OK**) + `Set.toFinset` + `Finset.insert_subset`/`card_insert_of_notMem`
  (⚠ notMem 綴り) + omega → y ∈ A ≤ VG → hPV_inf 矛盾。
- ⚠ GOTCHA: `orderOf_injective f hf x : orderOf (f x) = orderOf x` (向き注意)。

### (3.21) 実装 (`h321 : actionCommutator hP₀_inv.restrict = ⊤`, action-commutator 形)
- `hP₀_inv : IsAInvariant (φ.comp (inclusion hR₀R)) P := fun a => hP_inv (inclusion a)` (一行!)。
- Prop 1.6(a) `fixedPoints_sup_actionCommutator_eq_top` + fixedPoints = ⊥ (h320 へ val-chase 2 段:
  `restrict_apply_val` → `simp only [hφ, …, coe_inclusion]` → `mul_inv_eq_iff_eq_mul`)。
- **G-level 形 (`⁅P_G,R₀⁆ = P_G`) は未変換** — Phase D の消費形が決まってから橋を書く
  (2 段 map の generator-chase、`actionCommutator_conjNormal_map_subtype_eq` の類似)。

## ✅ 2026-06-10 session 8 cont. (a-keystone): Phase D 入口 — h321G 橋 + (3.22) kernel

- **scaffold: `h321G : ⁅P.map H.subtype, R₀⁆ = P_G`** ((3.21) の G-level 形) 着地。
  ≤ は generator ⁅↑ph,g₂⁆ = ↑ph·(g₂ ↑ph⁻¹ g₂⁻¹) 分解 (**⚠ goal は `H.subtype ph` 形なので
  `show ⁅(ph : G), g₂⁆ ∈ _` で coe 形に直してから rw**)、≥ は `h321` + actionCommutator を
  `Subgroup.closure_induction` で 2 段 val 押し下げ (`restrict_apply_val` → congrArg val →
  `simp only [hφ, …, coe_inclusion]`、mem ケースは `commutatorElement_def`+group)。
- **committed `825953a7` (S03f_Prelim): `le_opCore_of_hasPLengthOne_of_oPiCore_compl_eq_bot`**
  = (3.22) のエンジン (plen1 + O_{p'}=⊥ ⟹ 任意 p-部分群 ≤ O_p)。axiom-clean。
  新 import: PLengthTransfer + Ch04_Commutators.Main。

### ▶ 次セッション = (3.22) 本体から
- **(3.22) `[X,P]=1` for X = X^{PR₀} ≤ K with VXPR₀ ≠ G** の実装手順:
  1. `HX := VG ⊔ (X ⊔ P.map H.subtype)` (G-level), `S₂ := HX ⊔ R₀`。HX ≤ H。
  2. **HX ⊴ S₂**: R₀ は V (char)/X (仮定)/P_G (hP_inv) を normalize ⟹ sup を normalize
     (pointwise smul_sup)。h318 の hS₁norm パターン (mem_normalizer_iff, G-element level)。
  3. **IH 適用** ((3.6)/(3.7) と同型の transport 8 点セット): hcompl (disjoint = hcompl.disjoint
     mono / sup via normal_mul)、hHall (card_dvd)、hR₀ (≤ + prime card)、hZ (C_{S₂}(R₀') ↪
     H ⊓ C_G(R₀) — (3.6) の hZ' パターン)、card lt (S₂ ≠ ⊤ 仮定 + `eq_top_of_card_eq` 対偶)。
     ⟹ `hasPLengthOne p ↥⁅HX', R₀'⁆`。
  4. **O_{p'}(↥HX') = ⊥**: O_{p'} と V.subgroupOf HX (p-群, normal: V ⊴ H ≥ HX) は coprime normal
     ⟹ commutator ⊥ (`commutator_le_inf` + `inf_eq_bot_of_coprime`) ⟹ O_{p'} 元は V を中心化
     ⟹ (↥H に押し下げ) hCHV で ≤ V ⟹ p'∩p = ⊥。
  5. **O_{p'}(⁅HX',R₀'⁆-group) = ⊥**: char-in-normal で ↥HX-normal 化 ⟹
     `IsPiGroup.le_oPiCore` ⟹ ≤ O_{p'}(↥HX) = ⊥ (4.)。subgroupOf 2 段に注意。
  6. **kernel helper** (`le_opCore_of_hasPLengthOne_of_oPiCore_compl_eq_bot`) ⟹
     P-image ≤ O_p(⁅HX',R₀'⁆): P ≤ ⁅HX,R₀⁆ は **h321G** (P_G = ⁅P_G,R₀⁆ ≤ ⁅HX,R₀⁆ mono)。
  7. `[X,P] ≤ X ⊓ O_p-lift = ⊥` (X は p'-群 ⊆ K)。
- **(3.23)**: X := K で `G = VKPR₀` (≠ なら (3.22)+h313 矛盾)。`H = VKP`: H = G⊓H とカード;
  `R = R₀`: |R| = |R₀| (カード比較) + R₀ ≤ R。**以後 R = R₀ で書き換え可能になり Phase D 後半が
  単純化** (R₀ 添字を R に)。
- (3.24) `K = ⁅K,P⁆` (Prop 1.6(b) 橋 `commutator_commutator_right_eq` は ⊴ G 要 — K_G は
  ⊴ G でないので **S₂=G 内の actionCommutator 版** `actionCommutator_restrict_self_…` 系で)。
- (3.25) K special q-群 (**Gor 5.3.7 = `S04e.exists_minimal_aInvariant_isExpPSpecial_of_pprimeAction_with_minimality`**)、
  (3.26) exp q (Thm 1.13 = CriticalSubgroup)、(3.28)(3.29)、(3.30) **Thm 3.4 二度目**、(3.31) Z-群
  (`card_eq_prime_of_le_isZGroup` 再利用)。
- Phase D が最重量。その後 Phase E ((3.32)–(3.37), Thm 3.5 消費) → Phase F (orbit-parity 矛盾)。
- 正本 = 本ファイル「session 8」。

## ✅✅✅ 2026-06-10 session 9 (a-keystone): **Phase D (3.22)–(3.26) COMPLETE** — G/H/R/K の構造確定

scaffold 単一 sorry = Phase D 末尾 ((3.27)–(3.31) 以降)。leaf 3017 green (47s)、full 3619 green。
`maxHeartbeats 2400000` に増額 (1.6M から)。commits: `48dcde08` `e14db66e` `fd9b7a25` `931c0cd2`。

### 着地した文脈 (Phase D 後半が消費できる形)
- **(3.22)** `h322 : ∀ X ≤ KG, R₀ ≤ N(X) → PG ≤ N(X) → VG ⊔ X ⊔ PG ⊔ R₀ ≠ ⊤ → ⁅X, PG⁆ = ⊥`
  (PG := `P.map H.subtype` 表記)。実装 = 設計通り 7 ステップ: `set HX/S₂/WG` → S₂ ≤ N(HX)
  (`mem_normalizer_sup` ×2 + `normalizer_eq_top` + `mem_normalizer_map_subtype_of_isAInvariant`)
  → IH transport battery ((3.6) ミラー; card lt は `eq_top_of_card_eq S₂` **subgroup 明示引数**)
  → `hasPLengthOne ↥WG` 橋 → `O_{p'}(↥HX) = ⊥` (**Helper A** + hCHV val-chase) →
  `O_{p'}(↥WG) = ⊥` (**Helper B**, `WG ⊴ HX` in-context) → kernel
  (`le_opCore_of_hasPLengthOne_of_oPiCore_compl_eq_bot`; `PG ≤ WG` は h321G + commutator_mono)
  → `⁅X,PG⁆ ≤ X ⊓ OpG = ⊥` (coprime)。
- **(3.23)** `h313G` (G-level (3.13)) / `h323G : VG ⊔ KG ⊔ PG ⊔ R₀ = ⊤` / `hDedekind`
  (一般形: Y ≤ KG R₀-正規化 + VYPR₀=⊤ ⟹ VYP=H; `coe_mul_of_right_le_normalizer_left` +
  H⊓R=⊥ 殺し) / `h323H : VG ⊔ KG ⊔ PG = H` / `h323R : R = R₀`。
- **(3.22)' 無条件形** `h322' : X ≤ KG → X ≠ KG → R₀ ≤ N(X) → PG ≤ N(X) → ⁅X,PG⁆ = ⊥`
  (VXPR₀=⊤ なら hDedekind + **counting** `hcard_VYP : |VG ⊔ Y ⊔ PG| = |VG|·(|Y|·|PG|)`
  [`card_sup_of_le_normalizer_of_disjoint` ×2; disjoint 部品 = `hVG_disj` (hVN_inf 経由) +
  `hPG_p'_disj`/`hcop_KG_PG`] で X = KG)。
- **(3.24)** `h324 : ⁅KG, PG⁆ = KG` (`h16bKP` = Prop 1.6(b) を `KP := KG ⊔ PG` 内で
  `commutator_commutator_right_eq` + subgroupOf 2 連 transport; `mem_normalizer_commutator` で
  R₀-不変性)。
- **(3.25) 前半** `q, hq_prime, hq_ne_p, hq_ne_r, hKGq : IsPGroup q ↥KG`
  (`hKG_nilp` via hKN_fit; fitting ↥KG = ⊤ = ⨆ opCore [`nilpotent_normal_le_fitting` N:=⊤ +
  `fitting_eq_iSup_primeFactors`] + `Subgroup.iSup_induction` + h322' を proper opCore-lift に)。
- **(3.25)+(3.26)** `hK_special : IsSpecial q ↥KG` / `hK_exp : Monoid.exponent ↥KG = q`:
  **Gor 5.3.7** (`S04.exists_minimal_aInvariant_isExpPSpecial_of_pprimeAction_with_minimality`)
  を `φA := KG.normalizerMonoidHom.comp (inclusion (PG ⊔ R₀ ≤ N(KG)))` に適用 (`hφA_val` は
  **rfl**!)。minimal Q は proper だと h322' で ψ₀-中心化矛盾 ⟹ Q = ⊤ ⟹
  `IsSpecial.of_mulEquiv topEquiv` + `Monoid.exponent_eq_of_mulEquiv` で K に転送。
  hCop = `card_sup_of_le_normalizer_of_disjoint` で |A| = |PG|·|R₀|。
  **⚠ BG (3.25) の第 2 文 `C_{K/K'}(P) = 1` は未形式化** ((3.29)/(3.30) 実装時に要否判断)。

### 新規 committed 部品
- `S03f_Prelim` (+10 lemmas, 全 axiom-clean): `map_conj_eq_self_of_mem_normalizer` /
  `mem_normalizer_of_map_conj_eq` (core) / `mem_normalizer_sup` / `mem_normalizer_commutator` /
  `mem_normalizer_map_subtype_of_characteristic` / `mem_normalizer_map_subtype_of_isAInvariant`
  (conjNormal 形) / **`mem_normalizer_map_subtype_of_smul_val`** (任意作用の generic 形) /
  `oPiCore_compl_eq_bot_of_isPGroup_centralizer_le` (Helper A) /
  `oPiCore_eq_bot_of_subgroupOf_normal` (Helper B) / `card_sup_of_le_normalizer_of_disjoint`。
- `IsExtraspecial.lean`: **`IsSpecial.of_mulEquiv`** (center/commutator/frattini の iso 対応;
  frattini は `frattini_le_comap_frattini_of_surjective` 両方向)。

### Gotchas (再利用)
- `Set.mem_mul` destructure は β-未簡約 `(fun x1 x2 ↦ x1*x2) a 1` を残す → `rw [mul_one]` 不発。
  `rw [hr₀bot] at heq; simp only [mul_one] at heq` (simp は β する)。
- sup-membership に `le_sup_left h` は metavar で coercion 不発 → **`Subgroup.mem_sup_left/right`**。
- `Nat.Coprime.mul` は無い → `Nat.coprime_mul_iff_left.mpr ⟨_, _⟩`。
- `.toMonoidHom` 形は `Subgroup.map_equiv_eq_comap_symm'` (**primed**)。
- `Subgroup.iSup_induction` は `induction … using` 不可 (too many targets) → 明示
  `(C := fun w : ↥KG => …)` で直接 apply。
- `Subgroup.normalizerMonoidHom` 由来の作用の val は rfl で出る (comp/inclusion 越しでも)。

### ✅ session 9 cont.: (3.27)+(3.28) も COMPLETE
- **(3.27)** `h327 : PG ⊓ C_G(KG) = ⊥` — h316 G-level 化 (val-chase) + `hPG_p'_disj`。
- **(3.28)** `h328 : A ⊓ C_G(KG) = ⊥` — **A/φA/hφA_val/hAcard を main flow へ hoist 済**
  ((3.29) が再利用可)。素数 ℓ ∣ |A⊓C| で ℓ∈{p,r} 分岐
  (⚠ `rcases … with rfl` は **p/r 側を subst で消す**ので `hℓeq` + `rw [hℓeq] at hy_ordG`):
  p-枝 = PG ⊴ A (normal Sylow) + 商位数 r で像消滅 → h327; r-枝 = **Sylow II**
  (`Sylow.ofCard` ×2 [factorization 計算: `Nat.factorization_mul` + `Finsupp.single_apply` +
  `factorization_self`] + `MulAction.exists_smul_eq ↥A` + `Sylow.smul_def`/`pointwise_smul_def`/
  `coe_ofCard` simpa + `mem_smul_pointwise_iff_exists`) で ⟨y⟩ ~ R₀ 共役 ⟹ 中心化性転送
  (a⁻¹ka ∈ KG calc) ⟹ h317 矛盾。
  gotcha: `orderOf_dvd_natCard` (Nat.card 版; `orderOf_dvd_card` は Fintype)。

### ▶ 次セッション = (3.29)–(3.31) (Phase D 完結)
3. **(3.29)** `C_A(K/K') = ⊥`: K special ⟹ K' = Φ(K) (hK_special.2 — **⚠ 左枝 elem-abelian の
   場合は K'=Φ(K)=⊥ を別証**: 可換 ⟹ K'=⊥, `frattini_eq_bot_iff_isElementaryAbelian`) ⟹ **Thm 1.8**
   (`mulAut_eq_one_of_coprime_orderOf_of_frattini`, S01) で kernel(K/Φ(K) 作用) = kernel(K 作用)。
   φA の quotient 作用構成は `IsAInvariant.quotientMulAutHom` 系 (h317 ブロックの φQ パターン)。
4. **(3.30)** `C_{K/K'}(R₀) ≠ 1`: 背理 — PR₀ faithful on K/K' ((3.29)) + C(R₀)=1 と **Thm 3.4**
   (`S03d.thm34`, 二度目の実消費; (3.19) の thm34-bridge パターン: AppA:1541) ⟹ ⁅PG,R₀⁆ = ⊥
   ⟹ h321G で PG = ⊥ ⟹ h320/(3.13) 系で矛盾 (BG は (3.20) 違反と書く; Lean では
   ⁅P,R₀⁆ = P ≠ ⊥ を使う方が早い — P ≠ ⊥ は h313 ⟸ ⁅K,⊥⁆=⊥)。
5. **(3.31)** `|C_K(R₀)| = q ∧ C_K(R₀) ⊓ K' = ⊥`: q² ∣ |C_K(R₀)| なら exponent q ((3.26)) の
   位数 q² 部分群は elementary abelian ⟹ hZ (Z-group) 矛盾 — (3.19) の
   `card_eq_prime_of_le_isZGroup` 周辺パターン再利用。Prop 1.5(d) で C_K(R₀) ⊄ K'。
6. その後 Phase E (3.32)–(3.37): K ≠ [K,R], C_{[K,R]}(R)=1, Lemma 3.1 (Frobenius), **Thm 3.5**
   消費 ([K,R] abelian), Thm 2.6(a), K elementary abelian, |K| > q²。
正本 = 本節。(3.19)-(3.21) 実装詳細は session 8 節。

### ▶ (旧) session 7 cont. の (3.19) プラン (実装済み、参照用)
- 入口: thm34 への bridge。G' := ↥S₁ (= ↥(K_G ⊔ R₀)、h318 の S₁ をそのまま再利用 —
  hKG'norm/hcompl₁/hKG'card/hR₀'card/hr_ndvd_K は h318 内 local なので**再構築要** (h318 の外へ
  hoist するか (3.19) 内で再演)。⚠ hoist する場合 leaf build で順序確認)。
- V-module 化: `IsElementaryAbelian.zmodModule` (PRank:87) + conj-rep は
  **AppA_PStability:1541 / S03c_Thm37:90 パターン** (`Representation.ofDistribMulAction`)。
- hchar : (|↥S₁| : ZMod p) ≠ 0 ⟸ p ∤ |S₁| = |K|·r ⟸ hK'p' (p∤|K|) + p ≠ r
  (p ∣ |V| ∣ |H| would-be... r ∣ |R|, hHall ⟹ p≠r; |V|=p^a, a≥1? **V ≠ ⊥ 要**: V=F(H)≠⊥
  ⟸ H ≠ ⊥... H≠⊥ は hcounter から (H=⊥ なら ⁅H,R⁆=⊥ plen1) — どこかで `hV_ne_bot` を確立)。
- thm34 結論 `∀ g ∈ ⁅R₀',K'⁆, ρ g = 1` → ⁅R₀,K_G⁆ ≤ S₁ ⊓ C_G(V_G) `=h318=` ⊥ → h317 矛盾。
- その後 (3.19) 後半 (Z-群 ⟹ |C_V(R₀)|=p) → (3.20) → (3.21) → Phase D。
