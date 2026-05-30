---
id: 40
slug: peterfalvi-2-6-dade-map-construction
title: "Peterfalvi (2.6.b)/(2.8)-(2.10) Dade 写像の構成 (inclusion-exclusion)"
created: 2026-05-27
---

# Peterfalvi (2.6.b)/(2.8)-(2.10) Dade 写像の構成 (inclusion-exclusion)

## 背景

§4 The Dade Isometry のうち、**(2.7) adjoint formula は issue 0039 で完成**
(`OddOrder/Peterfalvi/S04_DadeIsometry.lean`, sorry-free).  残るのは

- **(2.6.b)** Dade 写像 τ が virtual character を virtual character に写すこと
- **(2.8)-(2.10)** その証明に使う構造補題 + inclusion-exclusion 公式

で、これらは合わせて **Dade 写像 τ の明示的構成** に相当する.

現状 S04 は (2.6) を `DadeIsometryData` / `FullDadeIsometryData` の
**インターフェース (仮定束)** として扱い、構成は保留している.  §5-§8 は
このインターフェース + (2.7) adjoint formula を使うので、本 issue は §4 の
完成度を上げるものだが §5-§8 の前提ではない (優先度は中).

## 証明構造 (教科書 `04.4_pp_10_14_The_Dade_Isometry.mmd` L56-124)

- **(2.8)** 非空 `B ⊆ A` に対し `H(B) = ⋂_{a∈B} H(a)`, `N_L(B)` = `B` の L-正規化群,
  `M(B) = H(B)·N_L(B)`.  このとき `M(B) = H(B) ⋊ N_L(B)`
  (H(B) ◁ M(B), H(B) ∩ N_L(B) = 1).  `card_centralizer_eq` 同様の積構造.
- **(2.9)** Notation: `α ∈ CF(L,A)` と非空 `B` に対し `α_B ∈ CF(M(B))` を
  `α_B(hx) = α(x)` (h∈H(B), x∈N_L(B)) で定義.  = `α ∘ f_B`,
  `f_B : M(B) → L` は核 `H(B)` の商準同型.  α が virtual char ⟹ α_B も virtual char.
- **(2.10)** **核心の inclusion-exclusion**: ℬ = 非空部分集合の L-共役類代表系 として
  `α^τ = -∑_{B∈ℬ} (-1)^|B| Ind_{M(B)}^G α_B`.
  右辺は誘導指標の交代和なので virtual character ⟹ (2.6.b).
  - **(2.10.1)** `x∈L`, 非空 `B` に対する Ind 値の式 (g の共役での寄与).
  - **(2.10.2)** `C_{H(B)}(a) = H(B∪{a})` (a∈A).
  - **(2.10.3)** `g ∉ ⋃_a (aH(a))^G` なら `(Ind_{M(B)}^G α_B)(g) = 0`;
    `g ∈ (aH(a))^G` なら値の明示式.
  - 証明: γ := -∑(-1)^|B| Ind α_B とおき、γ(g) を場合分け.  項が 2 つずつ相殺
    (B と B∪{a} のペア, (2.10.2) 経由) し `B={a}` の項だけ残る.
    `𝒜(g, H(a)a) = x·C_G(a)` (= issue 0039 の `card_conj_fiber` の中身) を使い
    `γ(g) = α(a)·|C_G(a)|/(|C_L(a)||H(a)|) = α(a) = α^τ(g)`.
- **(2.6)** (a) (2.7) から従う (β^τ が aH(a) 上定数). (b) (2.10) から.
- **(2.11)** `A₁ ⊆ A` が L-正規化されるとき (2.2) が A₁ で成立し、τ₁ は τ の
  CF(L,A₁) への制限.  (現 S04 の `restrict` インターフェースを実 τ で正当化.)

## 必要インフラ

- 誘導指標: `OddOrder/GroupTheory/RepresentationTheory/InducedCharacter.lean`
  (`induce`, `induceSum`, 加法性, support) は存在.  **誘導指標値公式
  (Frobenius reciprocity / Ind の明示値)** が追加で要りそう ((2.10.1)/(2.10.3)).
- 商準同型 `f_B : M(B) → L` と `α_B = α ∘ f_B` の virtual-char 保存.
- 非空部分集合の L-共役類代表系 ℬ と Möbius 型相殺の組合せ論.
- issue 0039 で作った `card_conj_fiber`, `card_centralizer_eq` を再利用.

## やること

- [ ] (2.8) `M(B) = H(B) ⋊ N_L(B)` の構造補題 (H(B), N_L(B), M(B) を定義)
- [ ] (2.9) `α_B` を商準同型 `f_B` 経由で定義、virtual char 保存
- [ ] 誘導指標値公式 (必要なら InducedCharacter.lean に追加)
- [ ] (2.10.1)-(2.10.3) sub-lemmas
- [ ] (2.10) inclusion-exclusion 本体 (Möbius 相殺)
- [x] **(2.6.a) を (2.7) から** — `IsDadeMap` + `HConjInvariant` ⟹ `IsDadeIsometry`
      を導出 (`isDadeIsometry_of_isDadeMap`, 2026-05-30 完了; 下記参照).  残るは
      (2.6.b)/(2.10) 経由の Dade 写像 τ の明示構成と `FullDadeIsometryData` への接続.
- [x] **(2.6.b) 前提 — `restrict_mem_ZIrr` + `induce_mem_ZIrr`** (Res/Ind が virtual char を
      保存; InducedCharacter.lean, 2026-05-30 完了, sorry-free + axiom-clean; 下記「進捗 (2)」).
      これは (2.6.b) の単一最大前提だった.
- [ ] (2.11) restriction 互換性

## 完了条件

Dade 写像 τ が `IsDadeMap` + isometry + virtual-char 保存を満たすものとして
**構成** され (インターフェース仮定でなく)、(2.8)-(2.11) が形式化される.
規模が大きいので sub-issue 分割可.

## 参照

- 教科書: `references/peterfalvi/04.4_pp_10_14_The_Dade_Isometry.mmd` (2.6),(2.8)-(2.11)
- (2.7) 完成: issue 0040 の前提 = issues/closed/0039-*, commits 40211fe..0d8307e
- ミニロードマップ: `notes/peterfalvi/s04_dade_isometry.md`
- インフラ: `OddOrder/GroupTheory/RepresentationTheory/InducedCharacter.lean`

## 進捗 2026-05-30 — (2.6.a) isometry を Dade-map equations から導出 (sorry-free)

**landed** (`OddOrder/Peterfalvi/S04_DadeIsometry.lean`, `section AdjointFormula`, green):

- `adjointAverageFun_dadeMap_eq` — Dade map `τ` と `β ∈ CF(L,A)` に対し
  (2.7) の平均化写像 `adjointAverageFun hyp (τ β)` が `A` 上で `β` に一致する.
  証明: `τ β` は coset `aH(a)` 上で定数 `β(a)` (`IsDadeMap.map_eq_of_mem_hCoset`)
  なので `H(a)` 上の平均は `β(a)`.  教科書 (2.6.a) 冒頭「`β^τ` は `aH(a)` 上定数」の計算.
- `isDadeIsometry_of_isDadeMap` — **(2.6.a) 本体**.  `IsDadeMap hyp τ` ((2.5) の
  pointwise equations) と `hyp.HConjInvariant` ((2.4.a)) だけから `IsDadeIsometry τ`
  (= `(α^τ,β^τ)_G = (α,β)_L`) を導出.  教科書の証明そのまま: (2.7) `adjoint_formula`
  に `χ := τ β`, `ψ := β` を入れる (`hψ` は `adjointAverageFun_dadeMap_eq`).
- `DadeIsometryData.ofIsDadeMap` (+ `_toDadeMap` simp) — Dade map と (2.5)/(2.4.a)
  仮定だけから `DadeIsometryData` を束ねる constructor.  従来 isometry を独立 field
  として仮定していたのを、defining equations から導けるようにした (インターフェース改善).

**意義**: (2.6.a) はもはやインターフェース仮定でなく `IsDadeMap` から導出される定理.
残る未構成は (2.6.b) (virtual char 保存) と、その前提となる Dade 写像 τ の明示構成
((2.8)-(2.10) inclusion-exclusion) のみ.

### 残作業の精密プラン ((2.6.b)/(2.8)-(2.10) — 大規模, 別 sub-issue 推奨)

検証済みのブロッカーと工数見積り (本セッションで mmd / 既存 API を確認):

1. **BLOCKER (critical, (2.6.b))**: `induce_mem_ZIrr` が repo にも mathlib にも無い.
   必要な statement:
   ```lean
   theorem induce_mem_ZIrr {H : Subgroup G} [Invertible (Nat.card H : ℂ)]
       {θ : ClassFunction H ℂ} (hθ : θ ∈ ZIrr H) :
       ClassFunction.induce H θ ∈ ZIrr G
   ```
   `InducedCharacter.lean` には `induce`/`induceSum` と線形性 (`induce_add`,
   `induce_smul`) はあるが、誘導が virtual char を virtual char に送る事実 (Frobenius
   相互律 + 整係数性) が無い.  証明には `⟨Ind χ_i, ψ⟩_G = ⟨χ_i, Res ψ⟩_H` 型の
   Frobenius reciprocity を整係数で先に立てる必要 (~80-100 LOC).  これが (2.6.b) の
   唯一かつ最大の前提 — **独立 sub-issue 化推奨**.

2. **(2.8) `M(B) = H(B) ⋊ N_L(B)`**: `hIntersection B = ⨅ a ∈ B, hyp.H a` と
   `N_L(B)` (B の L-set-stabilizer) を定義し disjointness を示す.
   - disjointness の数学は容易: `x ∈ H(B) ∩ N_L(B) ⊆ H(a) ∩ L`; `commute_of_mem_H`
     で `x ∈ C_L(a)`; `centralizer_disjoint` で `x = 1` (~20 LOC).
   - 注意: `Subgroup.setNormalizer` は mathlib では `Subgroup.normalizer` の **alias で
     subgroup 用** — Finset `B` の set-stabilizer には使えない.  `N_L(B)` は
     conjugation による `L` の set-stabilizer を手書き subgroup (carrier + closure 証明)
     として定義する必要があり、faithful な `N_L(B)` 構成自体が ~40-50 LOC.
3. **(2.9) `α_B = α ∘ f_B`**: 商準同型 `f_B : M(B) →* L` (核 `H(B)`) を (2.8) の
   semidirect 分解から構成し `α_B := α.comp f_B`.  `α ∈ ZIrr L ⟹ α_B ∈ ZIrr (M B)`
   は (1) の `induce_mem_ZIrr` とは別に「ZIrr の準同型 pullback (Res along f_B)」が要る.
4. **(2.10.1)-(2.10.3) + Möbius 相殺**: (2.10.3) の Ind 値公式 → `B` と `B∪{a}` の
   項が `(2.10.2) C_{H(B)}(a)=H(B∪{a})` 経由でペア相殺、`B={a}` のみ残す.
   `card_conj_fiber` (= 𝒜(g,H(a)a)=xC_G(a)) を再利用.  組合せ engine は
   `Finset.sum_powerset_insert` + `Finset.sum_powerset_neg_one_pow_card_of_nonempty`.
   最難、~150-200 LOC.
5. **接続**: `dadeSumMap` を (2.10) 公式で定義 → `IsDadeMap` を (2.10.3) から証明 →
   (2.6.a) は本セッションの `isDadeIsometry_of_isDadeMap` で自動 → (2.6.b) は (1)+(3)+
   (4) → `FullDadeIsometryData` 完成.  `[Fintype {a // a ∈ A}]` は `[Fintype G]` から
   `Fintype.ofFinite` で供給 (A は `Set G`).

依存順: (1) induce_mem_ZIrr [独立] → (2)(3) → (4) → (5).  全体 ~400-500 LOC.

## 進捗 2026-05-30 (2) — (1) induce_mem_ZIrr + restrict_mem_ZIrr 完成 (sorry-free, axiom-clean)

**landed** (`OddOrder/GroupTheory/RepresentationTheory/InducedCharacter.lean`,
`section VirtualCharacters` / `section InduceVirtualCharacters`, `lake build OddOrder` green,
`#assert_only_allowed_axioms` 両定理とも 3 axioms 全て allowlist 内):

- `restrict_repCharacterClassFunction` — `Res^G_H (χ_ρ) = χ_{ρ.comp H.subtype}` (ext で即).
- **`restrict_mem_ZIrr`** `(H : Subgroup G) [Finite G] {φ} (hφ : φ ∈ ZIrr G) : restrict H φ ∈ ZIrr H`.
  (2.6.b) の片側.  上の進捗ノートの「critical BLOCKER」評価は**誤りだった**: 当初は
  「ρ|H は既約でないので `repCharacterClassFunction_mem_ZIrr` が使えず、char-of-restriction
  分解 (issue 0026 module-theoretic blocker) が要る」と見ていたが、**同日 landed の keystone
  `character_mem_ZIrr` (CharacterCompleteness.lean、任意の有限次元複素表現の指標 ∈ ℤ[Irr]) が
  既約性を要求しない**ため、span induction の base case (φ = χ_ρ, ρ 既約) で
  `restrict H φ = repCharacterClassFunction (ρ.comp H.subtype)` と書き換え
  `character_mem_ZIrr (ρ.comp H.subtype)` を直接適用するだけで済む (ρ|H の可約性は無問題).
  線形ケースは `restrict_add`/`restrict_smul` (ℤ-smul は `Int.cast_smul_eq_zsmul` 経由).
- `inner_mem_ZIrr_int` — `φ, ψ ∈ ZIrr G ⇒ ⟨φ, ψ⟩_G ∈ ℤ`.  ψ で span induction、base は
  `mem_ZIrr_inner_int` (ZIrrFourier)、右引数の共役線形性 (`inner_smul_right` + `star_intCast`).
- **`induce_mem_ZIrr`** `(H : Subgroup G) [Fintype G] [Invertible (Nat.card G:ℂ)] [Fintype H]
  [Invertible (Nat.card H:ℂ)] {θ} (hθ : θ ∈ ZIrr H) : induce H θ ∈ ZIrr G`.  (2.6.b) の本体.
  θ で span induction.  base case (θ ∈ Irr H): 各 χ ∈ Irr G に対し numerical Frobenius
  reciprocity `inner_induce_eq_inner_restrict` で `⟨Ind θ, χ⟩_G = ⟨θ, Res H χ⟩_H`、
  `restrict_mem_ZIrr` で `Res H χ ∈ ZIrr H` ⇒ `inner_mem_ZIrr_int` で整数係数 `f χ`.
  `Φ := ∑_{χ∈Irr G} (f χ) • χ ∈ ZIrr G` を作り、`Ind θ - Φ` が全 irreducible と直交
  (対角 Fourier 係数一致 by `irreducibleCharacter_inner_eq_ite`) ⇒ completeness
  `classFunction_eq_zero_of_orthogonal` で `Ind θ = Φ`.  線形ケースは `induce_add`/`induce_smul`.

これで上記「残作業プラン」の**項目 (1) (critical, 唯一最大の前提) が解決**.  AxiomsCheck.lean に
両定理を登録済み.  残る (2.6.b) 構成タスクは (2) M(B)=H(B)⋊N_L(B) / (3) α_B pullback /
(4) Möbius 相殺 / (5) 接続 のみ (これらは依然 ~350-450 LOC、別 sub-issue 推奨).

実装:
- `restrict_mem_ZIrr`, `induce_mem_ZIrr` ともに `ClassFunction` namespace
  (`OddOrder.RepresentationTheory.ClassFunction.{restrict,induce}_mem_ZIrr`).
- InducedCharacter.lean が ZIrrFourier + CharacterCompleteness を import するよう変更
  (循環なし; 下流 S02/S03/Clifford ビルド確認済み).
