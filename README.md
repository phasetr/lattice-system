# lattice-system

Lean 4 + mathlib による一般的な格子模型の形式化プロジェクト.

先行プロジェクト [ising-model](https://github.com/phasetr/ising-model) の成果を
包含・一般化し, 以下の領域を段階的に扱う予定.

## スコープ

| 分野 | 位置付け | 典型文献 |
|---|---|---|
| 古典スピン系 (Ising 等) | ising-model から継承 | Friedli-Velenik, Glimm-Jaffe |
| 量子スピン系 | 当面の主対象 | Tasaki, Bru-Pedra |
| Hubbard / BCS | 中期 | Tasaki 1998, Bru-Pedra, Kashima |
| CAR 代数的定式化 | 中長期 | Araki-Moriya 2003, Bru-Pedra |
| 熱力学的極限・相転移 | 長期 | Simon, Friedli-Velenik |
| 格子 QCD | 最長期 | Aarts, Davies |

## プロジェクト状態

初期セットアップ段階. 形式化対象は未着手.

- 調査ノート: mathlib の量子スピン系サポート状況を確認済み
  (`.self-local/docs/quantum-spin-survey.md`, ローカル).
- CI: Lean Action CI + docgen-action + Jekyll Pages.

## ドキュメント

- Project page: https://phasetr.github.io/lattice-system/
- API documentation (doc-gen4): https://phasetr.github.io/lattice-system/docs/

## 形式化された定理

現時点で形式化された定理はない.

## フェーズ別進捗

| フェーズ | 概要 | 状態 |
|---|---|---|
| P0 | プロジェクト骨格, CI, ドキュメント基盤 | 着手 |
| P1 | 有限体積量子スピン系 (Pauli, Gibbs 状態) | 未着手 |
| P2 | Hubbard / BCS 有限体積 | 未着手 |
| P3 | CAR 代数, 準局所 C*-代数, KMS 状態 | 未着手 |
| P4 | 熱力学的極限, 相転移 | 未着手 |
| P5 | 格子 QCD | 未着手 |

## ビルド

```
lake build
```

Lean 4.29.1 を使用 (`lean-toolchain`).
