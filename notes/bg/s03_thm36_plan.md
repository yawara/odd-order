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
| **Lem 1.21(a)** | L566 | ❌ 未 | `H≤G, plen1 G ⇒ plen1 H` (= p-length 部分群単調性, **10.6 でも必要**) |
| **Lem 1.21(b)** | L567 | ❌ 未 | `H ⊴ G normal p'-sub, plen1(G/H) ⇒ plen1 G`。(3.8) で使用 |
| **Lem 1.21(c)** | L568 | ❌ 未 | `H ⊴ G normal p-sub, O_{p'}(G/H)=1, plen1(G/H) ⇒ plen1 G`。(3.9) |
| **Lem 1.21(d)** | L569 | ❌ 未 | `plen1 G ⟺ ⟨p-elements⟩ が normal p-complement を持つ`。(e) の engine |
| **Lem 1.21(e)** | L570 | ❌ 未 | `H,N ⊴ G, H∩N=1, plen1(G/H), plen1(G/N) ⇒ plen1 G`。(3.11) |
| **Thm 3.4** | L863 | ❌ 未 | 可解奇 G, normal Hall K + prime-order 補群 R, V 上 (char∤\|G\|), `C_V(R)=0 ⇒ [R,K]⊆C_K(V)`。表現論 (Clifford/Maschke/special) |
| **Thm 3.5** | L903 | ❌ 未 | Frobenius G=KR (K 可解, R cyclic prime), V 上, `C_V(R) 1-dim ⇒ K'⊆C_K(V)`。Clifford/Maschke/Wedderburn/Prop2.2/Lem3.3 |
| **Lem 3.3** | L845 | ✅ | S03b_Lemma33 `kernel_acts_trivially_of_centralizer_eq_bot` 等 |
| **Lem 3.1** | — | ✅ | S03 `isFrobeniusGroup_iff_complement_centralizer_inf_kernel_eq_bot` |
| **Gorenstein 5.3.7** | — | ❌ 未 | special q-群の coprime 作用 (3.25)。CLAUDE.md 方針: Gorenstein 原文を読み Lean 化 |
| §1 Prop1.3/1.4/1.5/1.6/1.7/1.8/1.13/1.16, Thm2.6 | — | ✅ (要再確認) | S01_Solvable / S01b_Prop116 / S02_Representations (Explore 2026-06-07 報告、楽観気味なので使用時に各個検証) |
| special q-group def `IsSpecial` | — | ✅ def | GroupTheory/IsExtraspecial.lean:84 |

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

ファイル `OddOrder/BG/Ch1_Preliminary/PLengthTransfer.lean` (新規)。

**✅ Landed (commit `4a9bf08`, sorry-free):**
- `card_quotient_oPiPrimePiCore_eq` : `|G/O_{p',p}(G)| = |(G/O_{p'}(G))/O_p(G/O_{p'}(G))|`
  (第3同型 `quotientQuotientEquivQuotient` + `O_{p',p}(G) = comap mk' (O_p(G/O_{p'}(G)))`
  + `map_comap_eq_self_of_surjective` + `oPiCore_compl_le_oPiPrimePiCore`)。
- `hasPLengthOne_iff_card_quotient` : 上を `hasPLengthOne` に rw した reformulation。
これが (a)–(e) 共通の出発点。

**作業中 (b) `hasPLengthOne_of_isPiPrime_normal_quotient` — 証明法確定済・機械的詰めのみ残:**
- 補題 `oPiCore_compl_quotient_eq` : `H ⊴ G` normal `p'` ⇒ `O_{p'}(G/H) = O_{p'}(G).map mk'`。
  - `≥`: `Ch03.oPiCore.map_le_of_surjective`。
  - `≤`: `N := (O_{p'}(G/H)).comap mk'` は normal、`p∤|N|` (∵ `|N|=|H|·|Kbar|`、`Kbar=O_{p'}(G/H)` は
    `p'`、両者 `p∤`)、ゆえ `N ≤ O_{p'}(G)` (`Ch03.Subgroup.IsPiGroup.le_oPiCore`)、`Kbar=N.map mk'`。
- (b) 本体: `φ : (G/H)/O_{p'}(G/H) ≃* G/O_{p'}(G)`
  `:= (QuotientGroup.quotientMulEquivOfEq hcorr).trans (quotientQuotientEquivQuotient H _ hHle)`。
  `O_p` を `Ch03.oPiCore.map_eq_of_mulEquiv` で φ 越しに移送、index を `Subgroup.index_map_equiv`
  (`Nat.card (A⧸M) = M.index` defeq) で一致させ、`hasPLengthOne_iff_card_quotient` に rw。
- **残る機械的論点** (次セッション fresh budget で即詰め): `Subgroup.card_mul_index` は `(H)` explicit /
  `Subgroup.index_comap_of_surjective` の引数順 / `Subgroup.Normal.map (h)(f)(hf)` の 3 引数 /
  `set Kbar/N` の opacity (`rw [hKbar]/[hN]` で unfold するか set を避ける)。
- **(a) 部分群単調性** (10.6 で必要) は (b) と異なり部分群-core 対応が要る: `O_{p',p}(G).subgroupOf H ≤
  O_{p',p}(↥H)` (normal p-nilpotent ≤ O_{p',p}) + index 整除鎖。(b) より重い。
- (c)(d)(e): (d)=`⟨p-elts⟩=O^{p'}` の normal p-complement 特徴づけ、(e) は (d) 経由、(c) は (b) 類似。
