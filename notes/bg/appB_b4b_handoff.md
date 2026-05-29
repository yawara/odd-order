# BG App.B Theorem B.4(b) — 別セッション引き継ぎ (2026-05-30)

**目標**: `OddOrder.BG.AppB.zCenter_lOdd_normal_of_oPiCore_eq_bot` を完成させる
= **BG Thm 6.2 (Glauberman Z(J)) の自己完結代替** = `O_{p'}(G)=1 ⇒ Z(L(S)) ⊴ G`。
issue 2001 の主目標。完成後 → BG Thm 6.2 一般形 → §7-§16(支配的ボトルネック)が開く。

> このファイルだけで作業を再開できるよう自己完結に書いた。設計の出自は overnight workflow
> `bg-overnight-b4b-and-backlog` (run wf_3a0e8aa0-985, 22 agent)。原文 mmd `references/bg/local-analysis.mmd`
> L4686-4762。`scaffold-sorry-free-not-done` を厳守 — 仮説に難所を退避した scaffold は不可。

## 0. 完成させる最終定理 (署名)

```lean
theorem zCenter_lOdd_normal_of_oPiCore_eq_bot [Finite G] {p : ℕ} [Fact p.Prime]
    (hp_odd : p ≠ 2) (hsolv : IsSolvable G) (hodd : Odd (Nat.card G))
    (hOp' : oPiCore {q | q ≠ p} G = ⊥) (S : Sylow p G) :
    (zCenterLOdd (S : Subgroup G)).Normal
```
(`open OddOrder.Isaacs.Ch01 OddOrder.Isaacs.Ch03 OddOrder.BG.AppA` 済なので `opCore`/`oPiCore`/`thmA5_part1` は無修飾。)

## 1. ファイルとビルド

- 実装先: `OddOrder/BG/AppB_PuigB3B4.lean` (現 249 行, namespace `OddOrder.BG.AppB`)。末尾 `end` の前に追記。
- **import 追加が必要**: `import Mathlib.GroupTheory.GroupAction.ConjAct`
  (`ConjAct.normal_of_characteristic_of_normal` 用; 現 import は `AppB_Puig` + `AppA_PStability` のみ)。
- ビルド: `lake build OddOrder.BG.AppB_PuigB3B4` (~2s, 速い)。フル: `lake build OddOrder`。
- 完成後 `OddOrder/AxiomsCheck.lean` に `#assert_only_allowed_axioms OddOrder.BG.AppB.zCenter_lOdd_normal_of_oPiCore_eq_bot`
  を追記 (L603 付近の B.4(b) ブロックに続けて) → 標準3公理のみを確認。

## 2. 利用できる完成済み土台 (全て sorry-free / axiom-clean)

### `AppB_PuigB3B4.lean` 内 (今セッションで完成)
- `b3_chain` — **BG Lemma B.3**: `p` odd solvable, `O_{p'}=1`, `S∈Syl_p`, `T=opCore p G` ⇒
  `lStarIn ↑S ≤ lStarIn T ∧ lStarIn T ≤ lOddIn T ∧ lOddIn T ≤ lOddIn ↑S` (= `L_*(S)⊆L_*(T)⊆L(T)⊆L(S)`)。
- `zCenterLOdd H` := `(Subgroup.center (lOddIn H : Subgroup G)).map (lOddIn H).subtype` (= `Z(L(H))` を G の部分群に)。
- `zCenterLOdd_le_lOddIn H : zCenterLOdd H ≤ lOddIn H`。
- `zCenterLOdd_eq_centralizer_inf H : zCenterLOdd H = Subgroup.centralizer (lOddIn H : Set G) ⊓ lOddIn H` (**keystone bridge**)。
- `zCenterLOdd_sylow_le_zCenterLOdd_opCore` — **Step2**: `zCenterLOdd ↑S ≤ zCenterLOdd (opCore p G)` (= `Z(L(S))⊆Z(L(T))`)。
- `lOddIn_map_equiv (φ : G ≃* G) (hH : H.map φ.toMonoidHom = H) : (lOddIn H).map φ.toMonoidHom = lOddIn H`。
- `map_conj_eq_iff_mem_normalizer {K g} : K.map (MulAut.conj g).toMonoidHom = K ↔ g ∈ normalizer (K:Set G)`。
- **`normalizer_le_normalizer_lOddIn (H) : normalizer (H:Set G) ≤ normalizer (lOddIn H : Set G)`**
  (= `N_G(H) ⊆ N_G(L(H))`, 任意 `H`, 共役同変)。**Step3 の要**。
- `normalizer_le_normalizer_map_of_characteristic {H'}[Group H']{K:Subgroup H'}{W:Subgroup ↥K}[W.Characteristic] :`
  `normalizer (K:Set H') ≤ normalizer ((W.map K.subtype):Set H')` (S7D1 port; **FINAL の center 段**)。

### `AppB_Puig.lean` 内 (B.4 で使う主なもの)
- `lOddIn_le_self H : lOddIn H ≤ H`; `lRelIn_lStarIn H : lRelIn H (lStarIn H) = lOddIn H` (B.1g);
  `lRelIn_le_iSup_pgroup_normalized (hH:IsPGroup p ↥H)(hPX:P≤X) : lRelIn H X ≤ ⨆ A∈{IsMulCommutative ↥A ∧ IsPGroup p ↥A ∧ P≤normalizer (A:Set G)}, A` (thmA5 橋渡し);
  `abelian_le_lNIn`; `lOddIn_eq_of_lOddIn_le_relative {H₀ H}(hHH₀:H≤H₀)(hH₀H:lOddIn H₀≤H) : lOddIn H = lOddIn H₀` (相対 B.2);
  `lOddIn_characteristic_of_characteristic (hH:H.Characteristic) : (lOddIn H).Characteristic`;
  `centralizer_lStarIn_inf_le` (相対 B.1f, L_* 版)。
### `AppA_PStability.lean` / Ch01 / Ch03
- `thmA5_part1 [Finite G](hp_odd)(hsolv)(hodd){P:Subgroup G}[P.Normal](hP:IsPGroup p P){X}(hX: X ≤ ⨆ A∈{IsMulCommutative ↥A ∧ IsPGroup p ↥A ∧ P≤normalizer (A:Set G)},A) : X.map (QuotientGroup.mk' (centralizer (P:Set G))) ≤ opCore p (G ⧸ centralizer (P:Set G))`。
- `opCore_isPGroup p G : IsPGroup p ↥(opCore p G)`; `opCore.characteristic`/`opCore.normal` (instances)。

## 3. 残作業 (実装順; 各 §3.x が 1 ステップ)

> **重要な設計更新**: overnight 設計は Step3 で `lRelIn_subgroupOf` 等の **subgroupOf transport (~60行, 最高リスク)**
> を要求していたが、**`normalizer_le_normalizer_lOddIn` (共役同変, 完成済) で完全に不要化された**。
> 下記は transport を使わない更新版。原設計の transport 群は **作らないこと**。

### 3.1 `normalInf_isSylow` (Step4 Frattini 用)
```lean
noncomputable def normalInf_isSylow {p : ℕ} [Fact p.Prime] [Finite G]
    {N : Subgroup G} [N.Normal] (Q : Sylow p G) : Sylow p ↥N :=
  (show IsPGroup p ↥(((Q : Subgroup G) ⊓ N).subgroupOf N) from
    (Q.2.to_inf_left).comap_subtype).toSylow (by /- index 義務 -/)
```
- `IsPGroup.toSylow (hP1 : IsPGroup p P)(hP2 : ¬ p ∣ P.index) : Sylow p G` (Sylow.lean:85, ambient = P の住む群; ここでは ↥N)。
- isPGroup': `Q.2 = Q.isPGroup' : IsPGroup p ↥↑Q`; `.to_inf_left : IsPGroup p ↥(↑Q⊓N)` (PGroup:239); `.comap_subtype : IsPGroup p ↥((↑Q⊓N).subgroupOf N)` (PGroup:267)。
- **index 義務** `¬ p ∣ ((↑Q⊓N).subgroupOf N).index`: `((↑Q⊓N).subgroupOf N).index = (↑Q⊓N).relIndex N` (relIndex の定義) で,
  これが `Q.index` を割り (`Sylow.not_dvd_index` Sylow.lean:442 で p-free), `[Q.FiniteIndex]` は `[Finite G]` から。
  dvd 連鎖は `Subgroup.relIndex_dvd_index_of_le` / `Subgroup.index_dvd_of_le inf_le_left` あたりで詰める
  (向きに注意; **`Sylow ∩ normal = Sylow of normal` の標準事実**)。
- **先例 (ほぼ写経可)**: `OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJ_PComplement.lean:955-967`
  が `hUAsub_pg.toSylow hp_not_dvd : Sylow p ↥LA` + `toSylow_coe` で同型パターンを実装済 (`hp_not_dvd` の出し方含め参照)。
- 配置: `AppB_PuigB3B4.lean` か `Ch01_Sylow/Main.lean` (generic)。**isolation で先にビルド**。

### 3.2 Step3 (FINAL 内 inline; `N_G(C∩S) ⊆ N_G(L(S))` を出す)
`set Y := zCenterLOdd (opCore p G)`, `set C₀ := Subgroup.centralizer (Y : Set G)`,
`set C := (opCore p (G ⧸ C₀)).comap (QuotientGroup.mk' C₀)`, `set CapS := C ⊓ (S:Subgroup G)`。
1. **Y.Normal の instance**: `haveI : (lOddIn (opCore p G)).Normal := (lOddIn_characteristic_of_characteristic (opCore.characteristic p G)).to... ` —
   正しくは `haveI : (lOddIn (opCore p G)).Characteristic := lOddIn_characteristic_of_characteristic (opCore.characteristic p G); haveI : (lOddIn (opCore p G)).Normal := inferInstance`;
   次に `haveI : (Subgroup.center _).Characteristic := Subgroup.centerCharacteristic`;
   `haveI : Y.Normal := inferInstance` (`ConjAct.normal_of_characteristic_of_normal`: `[H.Normal][K.Characteristic] ⇒ (K.map H.subtype).Normal`)。
   **`.normal` アクセサは存在しない** — 必ず `haveI ...Normal := inferInstance`。instance が渋れば `unfold zCenterLOdd` / `show ((center _).map _).Normal`。
2. `hY_le_T : Y ≤ opCore p G := (zCenterLOdd_le_lOddIn (opCore p G)).trans (lOddIn_le_self (opCore p G))`
   (**FIX: `Y ≤ L(T) ≤ T`。`(lOddIn_le_self _).trans le_rfl` は型が合わない — Y ≠ L(T)**)。
   `hY_pg : IsPGroup p ↥Y := (opCore_isPGroup p G).to_le hY_le_T`。
3. `hY_le_LstarS : Y ≤ lStarIn ↑S` — Step2 経由 (Y ⊇ Z(L(S)) ではなく, Y は L_*(S) を含む向き; mmd L4736 を確認。`abelian_le_lNIn` + `exists_lStarIn_eq` で)。**ここは原文 L4736-4740 を精読して詰める**。
4. `hX`: `rw [← lRelIn_lStarIn (S:Subgroup G)]; exact lRelIn_le_iSup_pgroup_normalized S.isPGroup' hY_le_LstarS` (P:=Y)。
5. `hmap := thmA5_part1 hp_odd hsolv hodd (P:=Y) hY_pg hX` → `(lOddIn ↑S).map (mk' C₀) ≤ opCore p (G⧸C₀)`
   (注: thmA5_part1 の X は `lOddIn ↑S`; hP は `[Y.Normal]` instance + `hY_pg`)。
6. `hL_le_C := Subgroup.map_le_iff_le_comap.mp hmap : lOddIn ↑S ≤ C`。
7. `hLeq := lOddIn_eq_of_lOddIn_le_relative (H:=CapS) inf_le_right (le_inf hL_le_C (lOddIn_le_self ↑S)) : lOddIn CapS = lOddIn ↑S`。
8. **`hN : normalizer (CapS:Set G) ≤ normalizer (lOddIn ↑S : Set G)`**:
   `(normalizer_le_normalizer_lOddIn CapS).trans (by rw [hLeq])` (= `N_G(CapS) ⊆ N_G(L(CapS)) = N_G(L(S))`)。
   **← これが transport を置き換える核心。**

### 3.3 Step4 (FINAL 内 inline; `C₀ ⊔ N_G(CapS) = ⊤`)
- `C₀.Normal := Subgroup.normal_centralizer` (要 `[Y.Normal]`); `C.Normal := Subgroup.normal_comap`。
- **Frattini**: `Qcs := normalInf_isSylow (N:=C) S : Sylow p ↥C`; `(Qcs:Subgroup ↥C).map C.subtype = CapS`
  を `subgroupOf_map_subtype` + `inf_comm`/`inf_idem` で示し, `Sylow.normalizer_sup_eq_top Qcs` (Sylow.lean:480, **UN-primed**;
  primed ' は Sylow p G を取り CapS に合わない) で `normalizer (CapS) ⊔ C = ⊤`。`[Finite (Sylow p ↥C)]` は自動。
- **吸収** `C ≤ C₀ ⊔ CapS`: `intro c hc`; `mk' C₀ c ∈ opCore p (G⧸C₀)` を `map_comap_eq_self_of_surjective` +
  `opCore_le ∘ (S.mapSurjective mk'_surjective)` で取り, `s ∈ S` で `mk' s = mk' c` を得て `s ∈ C` (∴ `s ∈ CapS`);
  **`c * s⁻¹ ∈ C₀`**: `mk'(c*s⁻¹) = mk' c * (mk' s)⁻¹ = 1` ⇒ `c*s⁻¹ ∈ ker (mk' C₀) = C₀` (`MonoidHom.mem_ker` + `QuotientGroup.ker_mk'`);
  `c = (c*s⁻¹)*s` を `mul_mem_sup` で。**符号罠注意**: `(c⁻¹*s)⁻¹ = s⁻¹*c ≠ c*s⁻¹` (非可換)。`c*s⁻¹` を直接使う。
- `hTop : C₀ ⊔ normalizer (CapS) = ⊤` を Frattini + 吸収 (`C ≤ C₀⊔CapS ≤ C₀⊔normalizer CapS`) + `sup_le`/`eq_top` で。

### 3.4 FINAL 組立
`rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hTop]; refine sup_le ?_ ?_`:
- **左枝** `C₀ ≤ normalizer (Z:Set G)` (Z := zCenterLOdd ↑S): `Z ≤ Y` (Step2 = `zCenterLOdd_sylow_le_zCenterLOdd_opCore`) ⇒
  `C₀ = C_G(Y) ≤ C_G(Z) ≤ N_G(Z)` = `(Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZ_le_Y)).trans (Subgroup.centralizer_le_normalizer _)`。
- **右枝** `normalizer (CapS) ≤ normalizer (Z:Set G)`: `hN.trans (normalizer_le_normalizer_map_of_characteristic (K:=lOddIn ↑S) (W := Subgroup.center _))`
  (Z = `(center ↥(lOddIn ↑S)).map subtype`, W=center は `centerCharacteristic`)。

## 4. 落とし穴 (今セッションで踏んだ/検証で判明)
- **`.normal` アクセサは無い** (Characteristic は構造体): 必ず `haveI ...Characteristic := ...; haveI ...Normal := inferInstance`。
- **共役ルートが transport を不要化**: `N_G(K) ⊆ N_G(L(K))` は `normalizer_le_normalizer_lOddIn K` で一発。`lRelIn_subgroupOf` 系は作らない。
- **`Subgroup.centralizer_le` は反変** (`s ⊆ t → centralizer t ≤ centralizer s`): `SetLike.coe_subset_coe.mpr h` を渡す。
- **`⊓` membership の destructure**: `rintro ⟨_, _⟩` が `toSubmonoid` coe 形を出すことがある → `rw [Subgroup.mem_inf] at h` してから `obtain`。
- **`∈ ↑K` (Set) vs `∈ K` (Subgroup)**: `mem_center_iff`/`mem_normalizer_iff` が刺さらない時は `rw [SetLike.mem_coe]` / `← SetLike.mem_coe`。
- **`rw [zCenterLOdd_eq_centralizer_inf]` は最初の出現を書き換える**: RHS だけ狙うなら引数指定 `zCenterLOdd_eq_centralizer_inf (opCore p G)`。
- **`2*n+1`/`2*0+1` の literal**: `lNIn_one`/`lNIn_zero` を `have e : ... := lNIn_one _` で defeq 受けしてから `rw [e]` (直接 `rw [lNIn_one]` は index 不一致で刺さらない)。
- 既存の軽微 lint: `map_conj_eq_iff_mem_normalizer` の `simp only [...]` に unused-arg 警告が残る (掃除可)。

## 5. 参照
- issue 2001 (本体), issue 2002 (B.4(a), 異群 iso 分離)。
- 設計出自: workflow run wf_3a0e8aa0-985 (出力は `/tmp` で揮発する可能性 → 本ファイルに要点転記済)。
- 原文 mmd L4686-4762; per-section `notes/bg/appB_puig.md`。
- 先例: S7B2:955 (Sylow∩normal), S7D1:862 (normalizer of char subgroup, port 済)。
