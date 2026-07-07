---
id: 99
slug: s07-isometry-weaken-ruling
title: "HUB 裁定: S07 tau_isometry_diff を zSupportedSpan 形へ in-place 弱化 (Option A、owner=b、mixed-degree ブロッカー解消)"
created: 2026-07-07
---

# HUB 裁定: S07 `tau_isometry_diff` を zSupportedSpan 形へ in-place 弱化

## 背景

lane-a flag (issue 1019 update⁵⁵、2026-07-07): `S07.Hypothesis` の `tau_isometry_diff`
(**S07_Coherence.lean:1777**、S07_Subcoherent でなく — 調査で位置訂正) が**全 member 差分**の isometry を要求
→ mixed-degree family では honest Dade map に対し**偽** (deg a ≠ deg b の a−b は A-supported でない) →
S07.Hypothesis が mixed family で **uninstantiable** → **(9.11) non-Galois mixed extension が構造的にブロック**
(a の Pf 11.8 hY route = FT critical path、b の §13 mixed consumer にも波及)。

hub 調査 = workflow wf_4f8e7eca (2 agent: Coq interface trace / Lean consumer census)。

## 調査確定事実

- **Coq interface**: `subcoherent` clause (b) = `{in 'Z[S, L^#], isometry tau}` (PFsection5.v:488) —
  isometry は **degree-0 / L^#-supported sublattice のみ**。全差分 isometry は Coq 開発全体に**存在しない**。
  Dade 側の供給は A-supportedness 経由 (`prDade_subcoherent` の defSA step、PFsection5.v:701-710)。
- **全 extension 機構が L^#-restricted form のみ消費**: (5.4) subcoherent_norm / (5.6) extend_coherent
  (divisibility で χ − a·ξ₁ を degree-0 化) / (5.6.3) / (5.7) uniform_degree_coherence (等次数仮定が
  生差分を degree-0 にする**まさにその箇所**) / (5.9a)。**Coq (9.11)** `Ptype_core_coherence`
  (PFsection9.v:1484) は q·a 次数 S1 に q·u≠q·a 次数 S3 を接ぐ**真の mixed 拡張**をこの interface だけで実行。
- **Lean census**: instantiation 4 site (S14:4032 / S14:4131 / S15_SAndT_Setup:1393 / S16:1048 T_typeIII_hyp07)
  は**全て equal-degree** で、弱 field を既存 brick `dadeIntegralCharacterMap_inner_eq_on_supported_span`
  (S07_Coherence.lean:5533) で**無条件に** discharge 可能 (mixed family 含む)。consumer 4 箇所
  (S07_CoherenceConstantDegree:210/460/613 + S07_Subcoherent:168 irrSubcoherent) は**全て A-supported 差分のみ**使用。
- **強 field ⇏ 弱 field**: member 差分 isometry は non-difference degree-0 combo (q·a − q'·b, χ − a·χ₁) を
  制御しない。∴ Option B (並行弱構造) は forgetful map 無し → **A の全 consumer 作業 + 構造重複**に退化。
- mixed 接続 engine (`retarget_isCoherent_of_decompositions` S07_Coherence:4141 / `coherentPairChain` :5033)
  は既に Hypothesis-free で、scaled degree-0 combo を扱う = **弱化後の形が (9.11) non-Galois route の
  native な要求**。

## 裁定 (Option A)

**`tau_isometry_diff` を in-place で Coq-faithful に弱化**:

```
tau_isometry_diff : ∀ φ ψ, φ ∈ zSupportedSpan S A → ψ ∈ zSupportedSpan S A →
    ClassFunction.inner (tau φ) (tau ψ) = ClassFunction.inner φ ψ
```

(zSupportedSpan 形 = `{f ∈ zSpan S | support ⊆ A}`、S07_Coherence.lean:44-46。
**equal-degree 差分形への弱化では不足** — (5.6)/(5.9a) 型 consumer は weighted combo を要する。)

- **owner = lane b** (対象 6 file 中 5 が b 所有: S07_Coherence / S07_CoherenceConstantDegree /
  S07_Subcoherent / S14_MaximalI / S15_SAndT_Setup)。**9013 案A より優先 insert 推奨** — 機械的 ~1 session で
  a の critical path (11.8 hY) と b 自身の §13 mixed consumer を同時 unblock する最上流工事。
- **c の分担**: S16_NonExistenceG:1048 (T_typeIII_hyp07) の instantiation-lambda swap 1 箇所 (b landing 後に cite 修正)。
- 実装 sketch (census 詳細は wf_4f8e7eca): field 差し替え (~3 行+docstring) → S07_CoherenceConstantDegree の
  ~11 lemma chain に `hsuppdiff` threading (`coherent_of_constant_degree` の外部 signature **不変** —
  hsuppdiff は既に引数) → irrSubcoherent に hconjsupp 引数 1 本 → 4 instantiation の lambda swap。
  既存 per-site witness lemma (Sset_tau_isometry_diff 等) は standalone fact として温存。
- **併せて裁定 (a/b 並行構築 dup)**: a の S12 `inducedFamily_degreeSubfamily_isCoherent` と b の S15
  `sSetIrrDeg_subcoherent` は**両方 keep** (family が異なり両方 genuine — 成果保全原則)。family-parameterized
  一般化は optional follow-up (どちらかが (9.11) 本体で必要になった時点で)。a の claim-before-build miss は
  自己申告済み、是正不要。

## 完了条件

- [ ] b が S07_Coherence.lean:1777 の field を zSupportedSpan 形に弱化 + consumer threading (build green)
- [ ] 4 instantiation site の discharge を弱 field 経由に swap (S14×2/S15 = b、S16 = c)
- [ ] a の (9.11) mixed route が S07.Hypothesis を mixed family で組めることを確認 (1019 側で検証)

## 参照

- 調査 = workflow wf_4f8e7eca-b3b (coq:subcoherent-interface / lean:s07-consumer-census)、2026-07-07
- issues/1019 update⁵⁵ (a の flag)、issues/0098 (レーン再点検)、coq/theories/PFsection5.v:486-494・PFsection9.v:1484
