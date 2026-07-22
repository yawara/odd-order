---
id: 9164
slug: dedup-ringaut-algaut-bridge
title: "Suzuki の inlined toAlgAut を共有 ringAutMulEquivAlgAut に差し替え"
created: 2026-07-19
---

# Suzuki の inlined toAlgAut を共有 ringAutMulEquivAlgAut に差し替え

## 背景

Peterfalvi (9.7.b) の counting 段 (|Aut F| = q; issue 1043 (b)) を実装する際、
「体の環自己同型は素体を自動的に固定する ⟹ `RingAut F` = `Gal(F/𝔽_p)`」という橋が必要になった。

この橋は **既に repo 内に存在していたが再利用不能な形だった**:
`OddOrder/Peterfalvi/Appendices/Suzuki/SemilinearModel.lean:107` の
`ringAut_isCyclic_of_finite` の証明の中に

```lean
  let toAlgAut : RingAut F →* (F ≃ₐ[ZMod (ringChar F)] F) := { toFun := fun f => AlgEquiv.ofRingEquiv … }
```

として `let` で埋め込まれており、外から呼べない (しかも `MonoidHom` 止まりで逆向きが無い)。

そこで共有層に **`MulEquiv` 版**として切り出した:
`OddOrder/GroupTheory/RepresentationTheory/SemilinearFieldAut.lean`

```lean
def ringAutMulEquivAlgAut (F) [Field F] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F] :
    RingAut F ≃* (F ≃ₐ[ZMod p] F)
```

(4 フィールド全て `rfl`; `ringAutMulEquivAlgAut_apply` は `@[simp]`)。
これを使って `natCard_ringAut_eq_finrank` / `natCard_ringAut_galoisField` を証明した。

## やること

- [ ] `ringAut_isCyclic_of_finite` (Suzuki) を共有 `ringAutMulEquivAlgAut` 経由に書き換える
      (`isCyclic_of_injective (ringAutMulEquivAlgAut F (ringChar F)).toMonoidHom
      (ringAutMulEquivAlgAut F _).injective` 相当)。inline `let toAlgAut` を削除。
- [ ] 併せて `p` の取り方を確認 — Suzuki 側は `ringChar F` + `ZMod.algebra F (ringChar F)` を
      `letI` で作っている。共有版は `[Algebra (ZMod p) F]` を仮定として取る形なので、
      Suzuki 側で同じ `letI` を置いてから呼ぶ形になる (instance diamond に注意)。

## 完了条件

Suzuki 側が共有 `ringAutMulEquivAlgAut` を呼び、inline `toAlgAut` が消え、
`lake build OddOrder.Peterfalvi.Appendices.Suzuki.SemilinearModel` が green。

## 参照

- 切り出し元: `OddOrder/Peterfalvi/Appendices/Suzuki/SemilinearModel.lean:107-122`
- 新設: `OddOrder/GroupTheory/RepresentationTheory/SemilinearFieldAut.lean` (issue 1043 (b))
- ⚠ **owner 注意**: Suzuki 付録は lane a の territory ではない (issue 2048 = lane b 系)。
  差し替えは所有レーンか hub が行う。lane a 側は共有版を land 済みで、
  Suzuki 側が現状のままでもビルドは壊れない (単なる重複)。

---

## 🧭 HUB RULING (2026-07-22): owner = lane b、実施は 2053 の区切りで

Suzuki 付録は b territory ゆえ差し替え実施 owner = **b**。重複はビルドを壊さない
(単なる dup) ので緊急性なし — **2053 Theorem B の区切り** (issue 0127 ②の
Suzuki2Groups 統合と同じタイミング) でまとめて実施すること。hub は tick でこの間
dup 増殖がないかだけ watch。
