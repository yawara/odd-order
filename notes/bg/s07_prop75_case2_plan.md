# BG Prop 7.5 case (2) (= brick 3) 実装プラン — living note

> 2026-06-03。`hypothesis71_of_scn2_or_pLengthOne` (S07:~1075) の case (2) を埋める。
> brick 2b (Prop 1.15(b) 一般形) 完了で前提が揃った。case (1) は Thm 6.7 待ちで明示 sorry。
> mmd 出典: `references/bg/local-analysis.mmd` L2252-2307。

## 🟢 大進捗 (2026-06-03 goal-loop セッション): core claim の主要補題 全 build-green

すべて `S07_Transitivity.lean` に private で実装・build-green・commit 済み:
1. **step 6** `mem_map_mk'_of_mem_oPiCore_quotient_of_commute` (crux `C_{O_p(X̄)}(Ā)⊆Ā`): `O_p(X̄)⊆mk(P)`
   (Sylow.mapSurjective + opCore_le) で c=mk s (s∈P), `[a,s]∈N⊓P=⊥` ⟹ s∈C_P(A)⊆A。
2. **specialCase** (special1 抽象形, `b`非依存): Sylow P + A SCN in P + Y A-inv p' ⟹ Y≤O_{p'}(G')。
   bar-quotient 9-step (step6 + Prop1.10 + Prop1.15a + Thm6.1 + commute)。
3. **le_opiCoreInG_of_le_opiCoreInG_centralizer** (per-b 橋): W≤X, W≤O_{p'}(C_G(b)) (b p-elt∈X) ⟹ W≤O_{p'}(X)
   (H2 + relativized-1.15b)。
4. **coreClaimGeneral** (general assembly): noncyclic B≤A of p-elts + hspec (∀b∈B^#, C_Y(b)≤O_{p'}(C_G(b)))
   ⟹ Y≤O_{p'}(X) (Prop1.16 `nontrivialActionFixedByClosure=⊤` + per-b 橋)。
5. 既: oPiCore_map_mulEquiv, opiCoreInG_eq_map_subgroupOf, **relativized 1.15b**, oPiPrimePiCore_map_mk'_eq,
   primesOf_eq_singleton, le_opiCoreInG_of_normal_of_isPiSubgroup, 還元補題。

### 🔜 core claim を閉じる残り (新数学は special2 だけ)
`hypothesis71_…` の case-2 core-claim sorry を埋めるには:
- **✅ (a) hspec for b∈Z(P)** = `le_opiCoreInG_centralizer_of_mem_centralizer_sylow` (done, build-green):
  specialCase@↥(C_G(b)) (Sylow=sylow_subgroupOf_of_le, A.subgroupOf SCN 移送) → map_subgroupOf で ambient。
  **non-cyclic Z(P) ケース (B⊆Z(P)) の hspec はこれで全 b∈B^# 充足。**
- **(b) special2** (cyclic Z(P), b∈B^#∖Z): mmd L2287-2297。`P₁=C_P(b)`,`P₂` Sylow⊇P₁, `Z⊆Z(P₁)⊆O_{p',p}`(Thm6.1),
  `[Y,Z]⊆O_{p'}`, `C_Y(Z)⊆O_{p'}(C_G(Z))`(=hspec(a) for z 生成元∈Z(P); `le_opiCoreInG_centralizer_of_mem_centralizer_sylow`✅)
  ⟹(per-b 橋 `le_opiCoreInG_of_le_opiCoreInG_centralizer`✅, X=C_G(b), z) `C_Y(Z)⊆O_{p'}(C_G(b))`,
  `Y=C_Y(Z)·[Y,Z]`。**🔴 要新規インフラ (repo/mathlib に無し, 確認済 2026-06-03)**:
  (i) **coprime 分解 `Y=C_Y(Z)·[Y,Z]` for NON-ABELIAN Y** = Gorenstein 5.3.5 / Isaacs coprime action (~100 LOC);
  (ii) **`Z⊆Z(P₁)⊆O_{p',p}(C_G(b))`** = P₁=C_P(b), P₂ Sylow⊇P₁ (|P₂:P₁|≤p via 7.4), Z(P₁)⊴P₂, Thm6.1。
- **(c) B-construction** (E_p² in A, ⊴P): Z(P) noncyclic→B∈E_p²(Z(P))⊆Z(P) (全 b∈Z(P), special1=(a)で hspec);
  Z(P) cyclic→B=⟨b⟩×Z, Z=Ω₁(Z(P)) (special2=(b))。G 2.6.4。
  **🔴 要新規インフラ**: noncyclic 側 = **finite abelian p-group `¬IsCyclic ⟹ E_p²`** (gateway 対偶 `isCyclic_of_card_pow_eq_one_le`, ~50 LOC); cyclic 側 = G 2.6.4 + `(Ω₁(A)/Z)∩Z(P/Z)≠1` の B 持ち上げ。
- **(d) 配線**: core claim で `primesOf A={p}` (primesOf_eq_singleton) 変換 → by_cases Z(P) cyclic →
  B 構成 → coreClaimGeneral (hspec を (a)/(b) で供給)。

## 完了済み (このセッション)

- **✅ 還元補題 `generated_eq_of_forall_le_opiCoreInG`** (S07, private, build-green, axiom-clean):
  `A ≤ X` かつ `∀ Y ∈ hInvariant X A π, Y ≤ opiCoreInG π X` ⟹ `sSup (hInvariant X A π) = opiCoreInG π X`。
  逆向きは `opiCoreInG π X ∈ hInvariant X A π` (自身が A-不変 π-部分群) から自動。**case 1/2 双方で使う**。
  これで Hypothesis71 の `generated_eq` は「**core claim**: 各 `Y ∈ ℋ_X(A;π')` が `O_{π'}(X)` に入る」に還元済。
- **✅ ne_bot / proper 実証明 + core-claim helper 2 種** (S07, build-green):
  - `primesOf_eq_singleton` (`IsPGroup p A` + `A≠⊥` ⟹ `primesOf A={p}`): `(primesOf A)ᶜ={p}ᶜ` 変換用。core claim で {p}-固有補題(Thm 6.1 等)を呼ぶ際に必要。
  - `le_opiCoreInG_of_normal_of_isPiSubgroup` (`N≤H` + `(N.subgroupOf H).Normal` + `IsPiSubgroup π N` ⟹ `N≤opiCoreInG π H`): `subgroupOf→oPiCore→map subtype` 連鎖の packaging。general case の `O_{p'}(C_G(b))⊓C_X(b) ≤ O_{p'}(C_X(b))` 等で再利用。

## ゴール構造 (`hypothesis71_of_scn2_or_pLengthOne`)

`Hypothesis71 A = ⟨ne_bot, proper, generated_eq⟩`。`rcases hcase with hcase1 | hcase2`:
- **case 1** (p-length one): 全体 `sorry` (Thm 6.7 未形式化; BG 「follows easily from Theorem 6.7」)。
- **case 2** (`A ∈ SCN₂(P)`): `obtain ⟨P, hAP, hAscn2⟩ := hcase2`; `refine ⟨ne_bot, proper, generated_eq⟩`。

### ne_bot (`A ≠ ⊥`) — provable, ~12 LOC
`hAscn2.le_pRank : 2 ≤ pRank ↥(A.subgroupOf P) p`。
`exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank (by norm_num) this`
⟹ `∃ B, B.IsElementaryAbelian p ∧ 2 ≤ Nat.log p (card B)`。
`Nat.pow_le_of_le_log (card_pos.ne') hBlog : p^2 ≤ card B`; `card B ∣ card ↥(A.subgroupOf P)` (Lagrange);
`card ↥(A.subgroupOf P) = card ↥A` (`Subgroup.subgroupOfEquivOfLe hAP` の `Nat.card_congr`);
`p ≥ 2` ⟹ `card A ≥ 4 > 1` ⟹ `Nontrivial ↥A` ⟹ `A ≠ ⊥` (`Subgroup.nontrivial_iff_ne_bot` 系)。
別ルート: SCN `selfCentralizing` で `A=⊥ ⟹ C_↥P(⊥)=⊤=⊥ ⟹ ↥P trivial`, P Sylow nontrivial と矛盾。

### proper (`A < ⊤`) — provable, ~8 LOC
`P : Sylow p G`。`P < ⊤` を示す: `P=⊤ ⟹ IsPGroup p G ⟹ IsNilpotent ⟹ IsSolvable`, `hG.notSolvable` と矛盾。
`P.isPGroup' : IsPGroup p ↥↑P`; `hPtop ▸ this : IsPGroup p ↥(⊤:Subgroup G)`;
`.of_surjective Subgroup.topEquiv.toMonoidHom topEquiv.surjective : IsPGroup p G`;
`haveI := this.isNilpotent` (要 `[Finite G]`); `IsNilpotent.to_isSolvable` (instance) で `IsSolvable G`。
最後 `lt_of_le_of_lt hAP hP_lt : A < ⊤`。

### generated_eq — 還元補題適用 + core claim
```
intro X hAX hXlt
apply generated_eq_of_forall_le_opiCoreInG hAX
intro Y hY            -- hY : Y ∈ hInvariant X A (primesOf A)ᶜ
-- core claim: Y ≤ opiCoreInG (primesOf A)ᶜ X
```
`primesOf A = {p}` (A は p-群, nontrivial): `primesOf A = {q | q ∈ (card A).primeFactors}`,
`IsPGroup p A` + `A≠⊥` ⟹ `(card A).primeFactors = {p}`。よって `(primesOf A)ᶜ = {p}ᶜ`。

## core claim 本体 (mmd L2273-2307) = 最重部分

設定: `π={p}`, `Z = Ω₁(Z(P))` (= `Omega ↥(center P) p 1` を G に戻す or `omega1OfAbelian`)。
`Y ∈ ℋ_X(A;p')` = `Y ≤ X ∧ A ≤ N_G(Y) ∧ IsPiSubgroup {p}ᶜ Y`。目標 `Y ≤ O_{p'}(X)`。

### B 構成 (7.4): `B ∈ E_p²(A)` かつ `B ⊴ P` — 要新規補題
`A ⊴ P` (SCN), `Z(P) ⊆ A` (SCN selfCentralizing ⟹ center P ≤ C_P(A)=A)。2 分岐:
- **Z(P) 非 cyclic**: `B ∈ E_p²(Z)`, `Z = Ω₁(Z(P))`。`ElementaryAbelian.of_card_prime_sq_of_not_isCyclic` 系。
- **Z(P) cyclic**: `|Z|=p`。`(Ω₁(A)/Z) ∩ Z(P/Z) ≠ 1` を **G 2.6.4** (`IsPGroup.normal_inf_center_nontrivial`,
  P/Z の p-群性 + Ω₁(A)/Z 正規 nontrivial) で。`B/Z` 位数 p を取り `B ⊴ P`。
  **罠**: P/Z 商 + Ω₁(A)/Z の正規性 + pullback。要 bar-quotient 補助。
共通: `B ≤ A`, `B` elementary abelian 位数 p², `B ⊴ P`, `Nat.Coprime (card B) (card Y)` (B p-群, Y p'-群)。

### 🎯 special case 抽象版 = `specialCase` (推奨 Lean 分解, 2026-06-03 設計) — `b` 非依存で再利用
**狙い**: 群 `G'` (= ↥X = ↥C_G(b) の役) で `b` を消した抽象形を private 補題に切り出す:
```
specialCase {p}[Fact p.Prime]{G'}[Group G'][Finite G'][IsSolvable G'] (hp2 : p ≠ 2)
  (hodd : Odd (Nat.card G')) (P : Sylow p G') {A : Subgroup G'} (hAP : A ≤ ↑P) [IsMulCommutative A]
  (hAnormP : (↑P:Subgroup G') ≤ normalizer A) (hCPA : centralizer (A:Set G') ⊓ ↑P ≤ A)
  {Y : Subgroup G'} (hYnorm : A ≤ normalizer Y) (hYpi : IsPiSubgroup {p}ᶜ Y) :
  Y ≤ Ch03.oPiCore {p}ᶜ G'
```
✅ 既 build 済 helper: `oPiPrimePiCore_map_mk'_eq` (= `mk(O_{p',p})=O_p(X̄)`, bar 方向)。
**proof 9 step** (mmd L2275-2285, step 7-8 は S01 `mem_centralizer_opCore_…` の写し):
1. `N := Ch03.oPiCore {p}ᶜ G'` (=O_{p'}), `mk := mk' N`, `X̄ := G'/N`. `O_p(X̄) := Ch03.oPiCore {p} X̄`.
2. **Thm 6.1** `thmA4b hp2 ‹IsSolvable G'› hodd P hAP hAnormP : A ≤ Ch03.oPiPrimePiCore {p} G'`.
3. `Ā := A.map mk ≤ (oPiPrimePiCore {p} G').map mk = O_p(X̄)` via `oPiPrimePiCore_map_mk'_eq` + `map_mono`.
4. `Ȳ := Y.map mk`. p'-群 (`card_map_dvd`). `Ā` が `Ȳ` 正規化 (A↷Y を mk で).
5. `⁅Ā,Ȳ⁆ ≤ O_p(X̄) ⊓ Ȳ = ⊥`: ⊆Ȳ (Ā 正規化 Ȳ); ⊆O_p(X̄) (Ā≤O_p(X̄)⊴X̄); ⊓=⊥ (`inf_eq_bot_of_pGroup_coprime`)
   ⟹ `Ā ≤ centralizer Ȳ` (commutator ⊥ = 中心化), 特に `Ā ≤ C_{O_p(X̄)}(Ȳ)`。
6. **🔴 crux `C_{O_p(X̄)}(Ā) ⊆ Ā`** (= `C_P(A)⊆A` から; Sylow correspondence。**最大未解決 sub-design**):
   - `S := ↑P ⊓ oPiPrimePiCore {p} G'` = **Sylow-p of O_{p',p}(G')** (Sylow∩normal=Sylow of normal; mathlib に
     直接無し→`IsPGroup.inf_normalizer_sylow`(Sylow.lean:281) or 自作要)。`A ≤ S` (A≤P ∧ A≤O_{p',p}(step2))。
   - `mk|_S : S ≃* O_p(X̄)`: 単射 (`S⊓N=⊥`, S p-群/N p'-群) + 全射 (`O_{p',p}=N·S` で `mk(S)=mk(O_{p',p})=O_p(X̄)`)。
   - 同型下 `C_{O_p(X̄)}(Ā)=mk(C_S(A))`, `C_S(A)≤C_P(A)≤A` (S≤P) ⟹ `C_{O_p(X̄)}(Ā)≤mk(A)=Ā`。
   - **代替案** (Sylow iso 回避): `c̄∈C_{O_p(X̄)}(Ā)` を S=P⊓O_{p',p} へ lift (mk|_S 全単射) し C_P(A)⊆A。同じ難度。
7. **Prop 1.10** `coprime_nilpotent_acts_trivially_of_centralizer_self` (Ȳ↷O_p(X̄), φ=normalizerMonoidHom):
   `fixedPoints=C_{O_p(X̄)}(Ȳ)`; hyp `C(C(Ȳ))⊆C(Ȳ)`: step5 `Ā⊆C(Ȳ)` ⟹ `C(C(Ȳ))⊆C(Ā)⊆Ā⊆C(Ȳ)` (step6);
   coprime (Ȳ p'/O_p p), nilpotent (O_p p-群) ⟹ `Ȳ が O_p(X̄) 中心化` ⟹ `Ȳ ≤ C_{X̄}(O_p(X̄))`。
8. **Prop 1.15(a)** `hall_higman_solvable_specialization` @X̄ (`oPiCore {p}ᶜ X̄=⊥` by `oPiCore_quotient_self_eq_bot`;
   `oPiCore_singleton_eq_opCore` で opCore 整合): `C_{X̄}(O_p(X̄))⊆O_p(X̄)` ⟹ `Ȳ≤O_p(X̄)`。
9. `Ȳ≤O_p(X̄)⊓Ȳ=⊥` (step5) ⟹ `Y.map mk=⊥` ⟹ `Y≤ker mk=N=oPiCore {p}ᶜ G'`。∎
**step 7-8 は S01:2304-2431 `mem_centralizer_opCore_of_mem_oPiPrimeCore_centralizer` を G'=X̄ で写経**。
**step 6 が唯一の重い未解決** (Sylow-of-normal + 商同型 + centralizer transport, ~80-120 LOC)。

### special case 1 (mmd L2275-2285): `X = C_G(b)`, `b ∈ B^# ∩ Z`
- `P` は `X = C_G(b)` の Sylow p (b ∈ Z(P) ⟹ P ≤ C_G(b)=X, かつ |X|_p = |P|)。**要補題: P ∈ Sylow p X**。
- `A` abelian normal in P ⟹ **Thm 6.1** (`thmA4b`, X solvable/odd を `hG.solvable_of_lt_top`+`hodd.of_dvd_nat`):
  `A ≤ O_{p',p}(X) = oPiPrimePiCore {p} ↥X`。
- bar = mod `O_{p'}(X)`: `X̄ = X/O_{p'}(X)`, `O_p(X̄) = O_{p',p}(X)/O_{p'}(X)`。**要 bar-quotient bridge**:
  `oPiPrimePiCore {p} X` の像 = `oPiCore {p} X̄ = opCore p X̄` (`oPiPrimePiCore` 定義が comap mk' なので
  `map mk'` で像 = `oPiCore {p} X̄`; `oPiCore_singleton_eq_opCore` で `opCore`)。
- `[Ā,Ȳ] ⊆ O_p(X̄) ∩ Ȳ = 1` (Ȳ は O_p(X̄) を正規化, A normalizes Y; Ȳ p'-群, O_p p-群 ⟹ 交わり 1)
  ⟹ `Ā ⊆ C_{O_p(X̄)}(Ȳ)`。
- `C_P(A) ⊆ A` (SCN) ⟹ `C_{O_p(X̄)}(Ā) ⊆ Ā` ⟹ **Prop 1.10** (Ȳ, O_p(X̄) を A,G に置く;
  `coprime_nilpotent_acts_trivially_of_centralizer_self`, φ = Ȳ の O_p(X̄) 共役作用):
  Ȳ が O_p(X̄) を中心化。
- **Prop 1.15(a)** (`hall_higman_solvable_specialization` @ X̄, `O_{p'}(X̄)=1` は `oPiCore_quotient_self_eq_bot`):
  `C_X̄(O_p(X̄)) ⊆ O_p(X̄)` ⟹ `Ȳ ⊆ O_p(X̄)`。Ȳ p'-群 ∩ p-群 ⟹ `Ȳ=1` ⟹ `Y ⊆ O_{p'}(X)`。

### special case 2 (mmd L2287-2297): `X = C_G(b)`, 任意 `b ∈ B^#`
case 1 から `|Z|=p`, `B = ⟨b⟩ × Z` と仮定可。`P₁ = C_P(b)`, `P₂` Sylow p of X ⊇ P₁。
`P/P₁ = P/C_P(B) ≅ Z_p` (7.4) ⟹ `|P₂:P₁| ≤ p`, `P₁ ⊴ P₂` ⟹ `Z ⊆ Z(P₁)`, `Z(P₁) ⊴ P₂`。
**Thm 6.1**: `Z ⊆ Z(P₁) ⊆ O_{p',p}(X)`。`[Y,Z] ⊆ Y ∩ O_{p',p}(X) ⊆ O_{p'}(X)`。
`A normalizes C_Y(Z)`, special case 1 (Z に適用) ⟹ `C_Y(Z) ⊆ O_{p'}(C_G(Z))`
⟹ `C_Y(Z) ⊆ O_{p'}(C_X(Z))` ⟹ **Prop 1.15(b)** (`oPiPrimeCore_centralizer_le_oPiPrimeCore`):
`C_Y(Z) ⊆ O_{p'}(X)`。`Y = C_Y(Z)·[Y,Z] ⊆ O_{p'}(X)`。

### general case (mmd L2299-2307): 任意 `X`
**Prop 1.16** (`cocyclicFixedByClosure_eq_top_of_not_isCyclic` or `exists_..` 系): `Y = ⟨C_Y(b) | b ∈ B^#⟩` (7.5)。
各 b: A normalizes C_Y(b); special 1/2 ⟹ `C_Y(b) ⊆ O_{p'}(C_G(b))`
⟹ `C_Y(b) ⊆ O_{p'}(C_X(b)) ⊆ O_{p'}(X)` (**Prop 1.15(b)**)。closure で `Y ⊆ O_{p'}(X)`。

## 要新規補題 (core claim 前に build)
1. **✅ `primesOf` = {p}** = `primesOf_eq_singleton` (done)。
2. **✅ normal p'-subgroup → opiCoreInG** = `le_opiCoreInG_of_normal_of_isPiSubgroup` (done)。
3. **Sylow-of-centralizer**: `b ∈ center P` (or `b ∈ Z(P_1)`) ⟹ `P ∈ Sylow p ↥(C_G(b))` (P ≤ C_G(b), index coprime p)。**型注意**: `Sylow p ↥(C_G(b))` は ↥(C_G(b)) 上, P を `.subgroupOf (C_G(b))` で持ち上げ。Thm 6.1 (`thmA4b`) が要求。
4. **bar-quotient bridge**: `(oPiPrimePiCore {p} X).map (mk' (oPiCore {p}ᶜ X)) = opCore p (X/O_{p'}(X))`
   (`oPiPrimePiCore` 定義 unfold + `map_comap` + `oPiCore_singleton_eq_opCore`)。
   `[Ā,Ȳ]⊆O_p(X̄)∩Ȳ` の commutator-in-quotient 計算も。
5. **✅ relativized Prop 1.15(b)** = `opiCoreInG_centralizer_inf_le_opiCoreInG` (S07, done, build-green):
   `IsSolvable ↥X` + `R≤X` p-subgroup ⟹ `opiCoreInG {p}ᶜ (C_G(R)⊓X) ≤ opiCoreInG {p}ᶜ X`。
   絶対形を **G':=↥X** で適用 → transport で ambient へ。支える新規補題 (両方 done):
   - `oPiCore_map_mulEquiv` (φ:G₁≃*G₂ ⟹ `(O_π G₁).map φ = O_π G₂`; `map_le_of_surjective` 両方向)。
   - `opiCoreInG_eq_map_subgroupOf` (`K≤X` ⟹ `O_π(K) = (O_π(K.subgroupOf X)).map X.subtype`; iso-naturality + map_map)。
   - centralizer bridge `(C_G(R)⊓X).subgroupOf X = centralizer (R.subgroupOf X : Set ↥X)` (inline)。
   special2 の `C_Y(Z) ⊆ O_{p'}(C_X(Z)) ⟹ O_{p'}(X)` も同じ補題で。
6. **B-construction** (E_p² in A normal in P) helper (cyclic/noncyclic Z(P) 2 分岐 + G 2.6.4)。

### general case の精密分解 (helper 3/5 + 確認済 lemma で組める, 2026-06-03 設計)
`Y ≤ X`, `A ≤ N_G(Y)`, `IsPiSubgroup {p}ᶜ Y`, B(E_p² ≤ A) 与え, special property
`hspec : ∀ b∈B^#, ∀ W≤C_G(b) A-inv p', W ≤ opiCoreInG {p}ᶜ (C_G(b))` を仮定:
1. Prop 1.16 (B↷Y 共役, coprime, noncyclic) で `Y = ⟨C_Y(b)|b∈B^#⟩`。
2. 各 b∈B^#: `C_Y(b):=Y⊓C_G(b)`。A-inv (A≤N_G(Y) ∧ A≤C_G(b) (b∈A abelian) ⟹ A≤N_G(C_Y(b)))。p' (≤Y)。
   `hspec` ⟹ `C_Y(b) ≤ opiCoreInG {p}ᶜ (C_G(b))`。
3. `opiCoreInG {p}ᶜ (C_G(b)) ⊴ C_G(b)` (oPiCore characteristic の像) ⟹ `(それ)⊓C_X(b) ⊴ C_X(b)` (N⊴H,K≤H)
   ⟹ **helper 2** で `≤ opiCoreInG {p}ᶜ (C_X(b))`。`C_Y(b) ≤ それ⊓C_X(b)` (C_Y(b)≤両方)。
4. **helper 5** (relativized 1.15b) で `opiCoreInG {p}ᶜ (C_X(b)) ≤ opiCoreInG {p}ᶜ X`。
5. closure (Prop 1.16 の sup) で `Y ≤ opiCoreInG {p}ᶜ X`。

## 確認済 lemma インベントリ (file:line, signature)
- `Hypothesis71` = ⟨ne_bot:A≠⊥, proper:A<⊤, generated_eq:∀X,A≤X→X<⊤→sSup(hInvariant X A (primesOf A)ᶜ)=opiCoreInG (primesOf A)ᶜ X⟩ (S07:119)
- `hInvariant H A π = {Q | Q≤H ∧ A≤N_G(Q) ∧ IsPiSubgroup π Q}` (`GroupTheory/AInvariantPiSubgroups.lean:41`); `mem_hInvariant` (:51)
- `IsSCN` = ⟨isNormal, isMulCommutative, selfCentralizing: C_G(A)=A⟩ (`GroupTheory/SCN.lean:75`);
  `IsSCN_n p n A = IsSCN A ∧ n ≤ pRank A p` (:221); `.isSCN`(:228) `.le_pRank`(:230)
- `thmA4b` (Thm 6.1): `[Finite G](hp_odd:p≠2)(hsolv:IsSolvable G)(hodd:Odd(card G))(P:Sylow p G){A}(hA_le:A≤↑P)(hA_norm:↑P≤N_G(A))[IsMulCommutative A] : A ≤ oPiPrimePiCore {p} G` (`BG/AppA_PStability.lean:1915`)
- `IsMinimalSimpleOdd`: `.odd`, `.simple`, `.notSolvable`, `.properSolvable`/`.solvable_of_lt_top M (hM:M<⊤):IsSolvable ↥M` (`BG/Ch2_Uniqueness/Setup.lean:47,68`)
- Odd 伝播: `hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)`
- Prop 1.10 `coprime_nilpotent_acts_trivially_of_centralizer_self {A G}[…][IsNilpotent G]{φ:A→*MulAut G}(hCop)(hCC:C_G(Fix φ)≤Fix φ):∀a g,(φ a)g=g` (S01:1777)
- Prop 1.15(a) `hall_higman_solvable_specialization [IsSolvable G](hp':oPiCore {q|q∉{p}} G=⊥):C_G(oPiCore{p}G)≤oPiCore{p}G` (S01:2297)
- Prop 1.15(b)特殊 `oPiPrimeCore_centralizer_eq_bot_of_oPiPrimeCore_eq_bot` (S01:2438); 一般 `oPiPrimeCore_centralizer_le_oPiPrimeCore` (S01:2483)
- Prop 1.16: `cocyclicFixedByClosure_eq_top_of_not_isCyclic (φ)(hCop)(hNC:¬IsCyclic A):cocyclicFixedByClosure φ=⊤` (S01b_Prop116:138);
  S07 specialization `exists_cocyclic_inf_centralizer_ne_bot_of_not_isCyclic` (S07:700)
- G 2.6.4 `IsPGroup.normal_inf_center_nontrivial (hP:IsPGroup p P){N}[N.Normal](hN:Nontrivial N):Nontrivial ↥(N⊓center P)` (Isaacs/Ch01_Sylow/Main:355)
- Ω: `Omega (p n) := closure {g|g^(p^n)=1}` (`GroupTheory/OmegaSubgroup.lean:55`); `omega1OfAbelian` (:185)
- ElementaryAbelian `IsElementaryAbelian` (type:41 / Subgroup:514); `of_card_prime_sq_of_not_isCyclic` (:84)
- pRank `pRank (p) := ⨆ A elem-ab, log p (card A)` (`GroupTheory/PRank.lean:373`);
  `exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank (0<n)(n≤pRank G p):∃A elem-ab,n≤log p(card A)` (:446)
- `oPiPrimePiCore π G = comap (mk'(oPiCore πᶜ G)) (oPiCore π (G/oPiCore πᶜ G))` (Ch03:2812);
  `oPiCore_quotient_self_eq_bot` (Ch03:1793); `oPiCore_singleton_eq_opCore` (Ch04)
- 還元補題 `generated_eq_of_forall_le_opiCoreInG (hAX:A≤X)(hY:∀Y∈hInvariant X A π,Y≤opiCoreInG π X):sSup(hInvariant X A π)=opiCoreInG π X` (S07, このセッション)

## 罠メモ
- bar-quotient は §4 (AppA/S04e/S04g) の商引き戻しパターン流用。`O_p(X̄)` の identification が最 fiddly。
- `Subgroup.IsPiGroup` / `.subgroupOf` / `.le_oPiCore` は **`OddOrder.Isaacs.Ch03` namespace 配下** (full-qualify)。
- 変数名に結合マクロン `X̄` 等 (U+0304) 不可 → `Xbar` 等にリネーム (brick 2b 実測)。
- core claim は special1 → special2 → general の 3 段。special1 を `private` 補題に切り出し special2/general から呼ぶのが楽
  (special2 は special1 を Z に, general は special1/2 を b に適用)。incremental skeleton 推奨 (sorry で型通し→1 個ずつ)。
