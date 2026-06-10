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
