# Tasaki 本形式化の再設計・再実装方針

## Status / Decision

- Status: **proposed**
- 対象: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
  (Springer, 2020) の形式化を、保存された旧 `main` とは別の再実装系列で
  front-to-back に作り直す。
- 基準 revision: `01bcb49d49db92c225cfa74b74d409dd0a9c4edc`
  (`main` の 2026-09-15 時点の tip)。本書中の測定値は、特記しない限りこの
  revision で得た。
- この設計 PR の変更範囲は本ファイルだけである。現行 Lean source、tests、CI、
  catalogue、依存 manifest は削除も変更もしない。

本提案の decision は次の通りである。

1. 旧 `main` は履歴・比較・証明アイデアを読むための **frozen legacy** として残す。
   新系列に旧公開 API との互換性は要求しない。
2. 設計承認後の bootstrap PR で、新系列から旧 `LatticeSystem/` source、旧 tests、
   旧 status catalogue を除き、package/toolchain、最小 CI、参照文献だけを残す。
   本 PR ではその除去を先取りしない。
3. 新系列は、無限頂点型上の graph と有限 volume を分離し、有限 volume の
   configuration/operator を一つだけ定義する。
4. 有限次元 operator の canonical representation は `Matrix` とする。
   `Module.End` 等への bridge は spectral API の境界一箇所に閉じ込める。
5. spin-half と general spin、有限系と将来の無限体積系を、コピーではなく同じ
   kernel の特殊化・制限として構成する。
6. Tasaki の source item を印刷順に進める。旧実装の進捗地点や救出しやすさを理由に
   §2.5、Chapter 4、Hubbard 等へ先回りしない。
7. 旧 proof は仕様でも依存でもなく、再証明時に監査する参考資料である。旧 axiom は
   一括移植しない。

この文書の承認は設計の承認であり、旧 source の数学的正当性や移植可否を一括承認する
ものではない。

## Goals

- Tasaki の本文、定理、問題、必要な式を front-to-back に追える source-oriented な
  形式化を作る。
- 公開 theorem の statement が、証明経路ではなく本文の数学的対象と最弱仮定を表す
  ようにする。
- underlying combinatorial datum を graph とし、頂点型自体には有限性を組み込まない。
- 同じ有限 volume kernel を spin、fermion、将来の局所 observable に再利用できる
  ようにする。
- theorem/proof、source locator、actual axiom set、status の関係を一意にする。
- 小さい import surface と一方向の dependency DAG を保つ。
- `lake build` warning zero、`sorry` / `admit` / `native_decide` 不在を継続する。
- 強い仮定を置く theorem について、仮定の同時充足可能性と結論の非空虚性を確認する。
- 無限体積極限を長期目標として保持しつつ、Chapter 2 より先に C\*-algebra framework を
  作り込まない。

## Non-goals

- 旧 namespace、declaration name、import path の互換維持。
- 旧 source を新しい directory へ機械的に移動すること。
- 旧 catalogue の全行を新 status ledger へ機械的に移すこと。
- 旧 proof-stage module を順番に「きれいにする」漸進 refactor。
- Tasaki 本で現在必要のない Lieb、Miyao、別文献の独立形式化。
- 二つ目の具体的利用がない一般化や、将来便利そうという理由だけの helper。
- Chapter 2 の bootstrap 時点で quasi-local algebra、KMS、GNS、thermodynamic limit を
  完成させること。
- 旧実装と同じ declaration 数、file 数、証明方針を再現すること。

## Evidence-backed diagnosis

### 規模と形状

基準 revision には Lean file が 1,727 個、合計 287,519 行ある。

```sh
git rev-parse HEAD
find LatticeSystem -name '*.lean' | wc -l
find LatticeSystem -name '*.lean' -print0 | xargs -0 wc -l | tail -1
```

`LatticeSystem/Quantum/SpinS/` 直下だけで 873 file、
`LatticeSystem/Fermion/JordanWigner/Hubbard/` 直下で 369 file ある。

```sh
find LatticeSystem/Quantum/SpinS -maxdepth 1 -name '*.lean' | wc -l
find LatticeSystem/Fermion/JordanWigner/Hubbard -maxdepth 1 -name '*.lean' | wc -l
```

開発工程に由来する名前を持つ file は、dev-research の広義分類では約 186 file だった。
名称の分類境界に依存するため、この値自体を gate にはしない。同じ revision で、狭義の
`Core|Structural|Wrapper|Assembly|Capstone|Discharge|Conditional` は 143 file、
`Bridge|Final|Target|Endpoint|Step` まで含める広義再測定は 188 file である。

```sh
find LatticeSystem -name '*.lean' \
  | awk '$0 ~ /(Core|Structural|Wrapper|Assembly|Capstone|Discharge|Conditional)/' \
  | wc -l
find LatticeSystem -name '*.lean' \
  | awk '$0 ~ /(Core|Structural|Wrapper|Assembly|Capstone|Discharge|Conditional|Bridge|Final|Target|Endpoint|Step)/' \
  | wc -l
```

数値そのものより、`Core`、`Structural`、`Bridge`、`Capstone` 等が数学的責務ではなく
当時の proof stage を表し、その stage が恒久 import graph に残っていることが問題である。

### spin-half / general-spin の重複

`LatticeSystem/Quantum/ManyBody.lean` は

```lean
abbrev ManyBodyOp (Λ : Type*) :=
  Matrix (Λ → Fin 2) (Λ → Fin 2) ℂ
```

と `onSite` を定義する。一方、
`LatticeSystem/Quantum/SpinS/MultiSiteCore.lean` は

```lean
abbrev ManyBodyOpS (Λ : Type*) (N : ℕ) :=
  Matrix (Λ → Fin (N + 1)) (Λ → Fin (N + 1)) ℂ
```

と `onSiteS` を定義する。off-site agreement、pivot configuration、異なる site の
可換性、加法・scalar・adjoint の証明も両系列に重複する。spin-half は local basis
`Fin 2` を一般 local basis に代入すれば得られるため、二本の kernel は不要である。

### graph と finite volume の切断

`LatticeSystem/Lattice/Graph.lean` が `SimpleGraph Λ` 自体に `[Fintype Λ]` を要求しない
判断は正しい。しかし有限量子系は `Λ` 全体に `[Fintype Λ]` を要求し、無限体積系は
`LatticeSystem/Quantum/SpinS/InfiniteVolumeGroundState.lean` の別構造
`InfiniteSpinSystem` から始まる。無限 graph 上の有限 `Finset` volume、induced graph、
volume restriction を共有する中間層がない。

また Hamiltonian 側の主要 API は生の `J : Λ → Λ → ℂ` を受け、real、star-fixed、
symmetric、nonnegative、zero diagonal、support、strict positivity 等を theorem ごとに
再度要求する。`couplingOf` は uniform weight の薄い関数であり、model invariant を
bundle していない。このため、例えば Theorem 2.4 系の公開 signature に coupling の
実装詳細が多数露出する。

### theorem statement への proof route の流出

`LatticeSystem/Quantum/SpinS/AnisotropicHeisenbergSpinSTheorem24.lean` の capstone は、
coupling の複数条件、diagonal shift、MLM/toy Hamiltonian 用 scalar、sector 非空性、
balanced-sector bookkeeping、既存 theorem package を平坦な引数として受ける。
declaration name も `...of_MLM_casimir_ladder_t23_pf_general` のように証明経路を表す。

基準 revision の最新修正 `01bcb49d` は、7 module に 30 個あった固定 `c` による
全 `lam D` 一様上界という充足不能 binder を削除した。この修正は 11 file、
425 insertions / 172 deletions で、回帰 fixture
`LatticeSystem/Tests/AxisSwapDiagBoundSatisfiable.lean` だけで 305 行ある。

```sh
git show --stat --oneline 01bcb49d
wc -l LatticeSystem/Tests/AxisSwapDiagBoundSatisfiable.lean
```

これは個別の失敗だけでなく、巨大 signature、positional forwarding、proof-stage API、
signature fixture が組み合わさると、数学的 defect の修正より周辺維持の方が大きくなる
ことを示す。

### import root と test の役割過多

`LatticeSystem.lean` は公開 API を選ぶ facade ではなく、library import DAG の全 tip を
列挙することを自ら invariant としている。基準 revision では 103 imports ある。
`LatticeSystem/Tests.lean` は 187 test modules を手動列挙し、tests 全体は 26,827 行ある。

```sh
rg -n '^import ' LatticeSystem.lean | wc -l
rg -n '^import ' LatticeSystem/Tests.lean | wc -l
find LatticeSystem/Tests -name '*.lean' -print0 | xargs -0 wc -l | tail -1
```

proof 自身を再掲する signature shim、grep hit 数、過去の一時 signature を保つ fixture は、
数学的意味の regression test と分離されていない。

### axiom と status の堆積

基準 revisionには source-level `axiom` が 81 個ある。

```sh
rg -n '^axiom ' LatticeSystem --glob '*.lean' | wc -l
```

C\*-algebra、GNS、KMS 等の合意済み defer 対象だけでなく、後で discharge するための
定理、物理的 marker predicate、有限次元の未完部分が同じ構文で混在する。新系列で
これらを一括移植すると、古い分類判断まで無批判に固定してしまう。

status も Lean source、`docs/formalization/legacy/`、prototype の
`formalization-status/v2/`、`tex/proof-guide.tex` に重複する。現行 validator の厳密な
actual-axiom 照合という発想は採用するが、複数の status 正本と legacy catalogue guard は
採用しない。

## Adopt / Rewrite / Drop inventory

### Adopt: 判断または検証手法として採用

| 資産 | 採用する部分 | 条件 |
|---|---|---|
| `lakefile.toml` | pinned mathlib、`relaxedAutoImplicit = false`、warning-as-error、標準 linter、long-file check | bootstrap で最小構成として再確認する |
| `lean-toolchain`, `lake-manifest.json` | reproducible toolchain | 設計と無関係な dependency 更新をしない |
| `Lattice/Graph.lean` | graph に有限性を埋め込まない判断、path/cycle/hypercubic との接続 | API は新 `Geometry` 層で再記述する |
| `SpinS/Operators.lean` | `N = 2S`、basis `Fin (N+1)`、raising/lowering の係数 | source と再照合し、新 canonical API 上で証明し直す |
| `ManyBody.lean`, `MultiSiteCore.lean` | configuration basis 上の site embedding と可換性の数学的アイデア | generic local basis 一本に統合する |
| `Math/MatrixAnalysis/` 等 | source-neutral な有限次元線形代数の proof idea | 実際の次 theorem に必要、mathlib に同等物なし、最弱仮定を満たすものだけ |
| tests の A/B/C/G 型手法 | small finite exhaustive、entrywise、bridge identity | 意味を検査する短い test に限定 |
| status validator | actual axiom set と declaration module を Lean 環境から検査する発想 | ledger と checker を最小から作り直す |
| `.self-local/refs/` | Tasaki PDF/text と locator 調査 | repository 公開可否とは分離し、source review に使う |

低層資産は file 単位で採用しない。採用単位は「定義の数学的内容」「証明アイデア」または
「検証方法」であり、新系列の source は原則として書き直す。

### Rewrite: 数学的目的を保ち、表現を変更

| 現行対象 | 書き直し方 |
|---|---|
| `ManyBodyOp` / `ManyBodyOpS` | `Config Λ I` / `Op Λ I` と generic `embedSite` に一本化 |
| `spinSOp1/2/3` 群 | `Axis` indexed `spinOp` を中心にし、`S±` を導出 |
| 生の `J` と仮定列 | graph と edge coupling invariant を一つの構造へ bundle |
| `Bool` sublattice marker | 公開面は explicit bipartition witness、内部だけ必要なら Bool bridge |
| `Matrix.toLin'` の反復 | `Spectrum` 境界に `eigenspace` / `groundSpace` を定義 |
| 巨大 existential/conjunction capstone | `GroundState`、`GroundSpace`、sector 等の数学的 named definitions を使用 |
| finite/infinite の別系統 | 無限 `V` 上の `Finset V` volume と restriction から接続 |
| source status | 一つの machine-readable ledger と生成表示へ縮約 |
| theorem-oriented helper 名 | 数学的対象・作用・性質を表す名前へ変更 |

### Drop: 新系列へ持ち込まない

- 旧 declaration/import path の compatibility shim と deprecated alias。
- facade を旧 path に残すための `Core.lean` 分割。
- `Structural`、`Wrapper`、`Assembly`、`Discharge`、`Conditional` 等の proof-stage 分割。
- PR ごとの新 module。
- theorem の statement を再掲するだけの test。
- grep 数、line number、一時 signature を仕様化する test。
- legacy catalogue の手移植と旧 roadmap の PR chronicle。
- 参照ゼロの decorative helper と、将来便利そうという理由だけの一般化。
- 旧 axiom の一括移植。
- 本文より強いが証明を通しやすい仮定。

## Target dependency DAG and directory layout

依存方向は次に固定し、逆向き import と chapter の先取り import を禁止する。

```text
Mathlib
  ↓
LatticeSystem.Math       LatticeSystem.Geometry
             \             /
              Quantum.Finite
                    ↓
               Quantum.Spin
                    ↓
                  Models
                    ↓
          Tasaki2020.ChapterNN
                    ↓
            Tests / StatusChecks
```

初期 directory 案は次の通りである。file は PR 単位ではなく数学的責務で分ける。

```text
LatticeSystem/
  Math/
    ...                         # 要求された時だけ追加
  Geometry/
    Graph.lean
    Volume.lean
    Hypercubic.lean
  Quantum/
    Finite/
      Configuration.lean
      Operator.lean
      SiteEmbedding.lean
      Spectrum.lean
    Spin/
      Basis.lean
      Operators.lean
      Algebra.lean
      Rotation.lean
      ManyBody.lean
      MagnetizationSector.lean
  Models/
    Heisenberg/
      Definition.lean
      Ferromagnet.lean
      Antiferromagnet.lean
  Tasaki2020/
    Chapter02/
      Section01.lean
      Section02.lean
      Theorem21.lean
      Theorem22.lean
      ...
  Tests/
    Quantum/
    Tasaki2020/
```

`LatticeSystem.lean` は stable public surface だけを import する。全 leaf/tip coverage は
build target が担い、root file の責務にしない。source item の追加ごとに file を作る必要は
なく、同じ数学的責務で 700 行未満を目安に育てる。分割は責務が二つになった時に行う。

## Canonical types

以下は意図を示す sketch であり、この設計 PR では Lean 宣言を追加しない。

### Infinite vertices and finite volumes

```lean
variable {V : Type*}

abbrev Volume (V : Type*) := Finset V
```

`SimpleGraph V` と model data には `[Fintype V]` を要求しない。有限計算は
`Λ : Finset V` の subtype `↥Λ` で行う。有限 graph theorem が全頂点を扱う場合だけ
局所的に `[Fintype V]` と `Λ = Finset.univ` を用いる。

この境界により、将来 `V = ℤ`、`V = Fin d → ℤ` としたまま `Λₙ : Finset V` を増大させ、
同じ local Hamiltonian を制限できる。

### Generic local basis and Matrix canonical representation

```lean
abbrev Config (Λ : Finset V) (I : Type*) := ↥Λ → I
abbrev Ket (Λ : Finset V) (I : Type*) := Config Λ I → ℂ
abbrev Op (Λ : Finset V) (I : Type*) :=
  Matrix (Config Λ I) (Config Λ I) ℂ
```

必要な箇所で `[Fintype I] [DecidableEq I]` を置く。site embedding は一つだけ持つ。

```lean
def embedSite (Λ : Finset V) (x : ↥Λ) (A : Matrix I I ℂ) : Op Λ I := ...
```

spin-half は `I = Fin 2`、spin `S = N/2` は `I = Fin (N+1)` である。heterogeneous local
basis は Chapter 2 の要求ではないため初期 kernel には入れない。二つ目の実需要が出た時に
generalize する。

`Matrix` を canonical とする理由は、Tasaki の基底表示、entry sign、Perron--Frobenius、
small finite computation が主経路だからである。linear map/eigenspace が必要な時は
`Quantum.Finite.Spectrum` に一度だけ bridge を定義し、公開 theorem が毎回
`Matrix.toLin'` を展開しないようにする。`Matrix` と `Module.End` の双方を正準 API に
しない。

### Spin representation

- spin quantum number は `N : ℕ`、`2S = N` とする。
- local basis は `SpinBasis N := Fin (N+1)`。
- axis は `Axis` で indexed にする。
- `spinOp N : Axis → Matrix (SpinBasis N) (SpinBasis N) ℂ` を中心に置く。
- `spinRaise` / `spinLower`、Casimir、rotation はこの API から導く。
- `S=1/2`、`S=1` の行列を別定義せず、一般定義の specialization theorem にする。

### Bundled coupling

公開 theorem が次を個別引数として反復しない構造を用意する。

- underlying `graph : SimpleGraph V`
- real symmetric edge weight
- non-edge と diagonal で zero
- theorem に必要な場合だけ nonnegative / strictly positive edge property

実装上は proof-dependent edge function を避けるため、最初は symmetric pair function と
support invariant を bundle するのが安全である。Hamiltonian の正準定義は有限 induced
graph の unordered edge sum とする。ordered-pair sum と `1/2` は theorem の本文がその
表記を必要とする時の bridge に限定する。

positivity を coupling の全用途へ強制しない。例えば ferromagnetic/antiferromagnetic の
符号は model layer の refined structure または theorem hypothesis とする。

### Named mathematical predicates

以下を用意し、巨大な conjunction と representation detail を capstone から隠す。

- `IsEigenvector`
- `groundEnergy`
- `groundSpace`
- `IsGroundState`
- `MagnetizationSector`
- explicit bipartition / connected weighted graph predicate

bundle は仮定を隠して弱く見せるためではなく、同じ invariant 集合を一度構成し、すべての
consumer が同一の数学的対象を受け取るために使う。constructor の充足可能性 test も行う。

## Axiom policy

1. `sorry`、`admit`、`native_decide` は禁止する。
2. 旧 81 axiom は一つも自動移植しない。
3. 有限次元、固定 finite volume の線形代数・spectral・perturbation result は原則として
   証明対象であり、難しさだけを理由に defer しない。
4. defer 候補は抽象 C\*-algebra、GNS、KMS、weak dual/state、Wigner、真の無限体積
   analytic limit、volume-uniform perturbation theory に限る。
5. 内容のない predicate を `axiom ... : ... → Prop` として導入する場合も、存在 theorem を
   暗黙に与えていないか、結論を vacuous にしていないかを source item ごとに審査する。
6. conjecture は `def ... : Prop` として statement を記録してよいが、true と主張する
   `axiom` を置かない。
7. deferred declaration には source locator、欠けている数学、reopen condition、依存する
   capstone を一つの ledger entry に記録する。
8. 各 proved capstone の actual axiom set を Lean environment から検査する。許可される
   logical axioms と project-specific axiom を完全一致で区別する。
9. temporary axiom を後で discharge する workflow は使わない。大型 theorem は proved
   supporting lemma の列へ分割し、未証明 capstone を source に置かない。

## Source-item, PR, and test policy

### Source item

source item は Tasaki の一定理、一問題、または一つの数学的責務をなす連続した equation
block とする。edition、chapter/section、theorem/problem/equation number、page を必須にする。

Lean source が declaration の statement/kind/module の正本である。status、source locator、
actual axiom dependency は一つの小さな machine-readable ledger を正本とし、人間向け一覧は
生成する。proof exposition は重複 status ledger ではなく、Lean declaration へリンクする。

### PR unit

- 通常は 1 PR = 1 source item の完成した vertical slice。
- PR は定義、直前から backward-chain した必要補題、capstone、意味 test、source/status 更新を
  同時に完結させる。
- 大型 theorem だけ、同じ theorem issue の中で複数 PR に分割できる。各 PR はそれ自体で
  axiom-free な一つの数学結果を完成させ、最終 theorem のどの step に必要かを明記する。
- PR 分割の都合で `Core` / `Bridge` / `Final` file を増やさない。
- unrelated refactor、将来用 helper、別 chapter の準備を混ぜない。
- capstone 実装前に、本文との statement review と hypothesis audit を独立に行う。

### Adopt gate for an old declaration

旧 declaration の内容を再利用するには、次をすべて満たす。

1. source locator と本文 statement を再照合した。
2. 本文より強い仮定がない。
3. 仮定の同時充足可能性を具体 model または独立 consistency argument で確認した。
4. 結論が vacuous でない。
5. actual axiom set が新 policy に合う。
6. 現 source item の final line からの backward chain 上にある。
7. 新 canonical type 上で自然に表現できる。
8. mathlib または新 kernel と重複しない。
9. proof-route 名でなく数学的な名前を持つ。
10. statement review または小さい semantic test がある。

一項でも落ちたものは修理移植ではなく、本文 statement から再構成する。

### Test policy

- Lean proof 自身が theorem の第一の test である。
- 別 test は、small finite exhaustive、matrix entry、definition bridge、non-vacuity、過去に
  実際に起きた semantic regression のいずれかを検査する時だけ追加する。
- public theorem の型を `example := theoremName ...` で再掲する signature shim は、外部 API
  freeze を明示的に決めた対象以外では使わない。
- grep hit 数、file 行番号、proof helper 名、一時的な引数順を test invariant にしない。
- 強い bundle/refined structure には concrete constructor witness を置く。
- 強い theorem hypothesis には、可能なら最小非自明 graph/model で positive control を置く。
- false/unsatisfiable hypothesis を導入しないため、quantifier order と parameter dependence を
  statement review で明示する。

### Per-PR verification

1. 対象 module の局所 build。
2. `lake build`、warning zero。
3. `sorry` / `admit` / `native_decide` 不在。
4. capstone actual axiom set の完全一致確認。
5. source locator と statement review。
6. dependency-layer 違反と import cycle の確認。
7. semantic test と non-vacuity control。
8. cold/warm のどちらかを明記した compile-time delta と import 増分の記録。

## Migration sequence

### M0: legacy freeze and design

- 旧 `main` の tip を記録し、frozen legacy とする。
- 再実装用 main を旧 tip から派生し、履歴比較可能性を保つ。
- その main から本設計 branch/PR を作る。
- 本 PR は本ファイルだけを追加し、現コードを変更しない。

### M1: bootstrap after approval

設計承認後の別 PR で初めて、再実装系列から次を除く。

- 旧 `LatticeSystem/` production source
- 旧 `LatticeSystem/Tests*`
- 旧 legacy/prototype status catalogue と専用 migration guards
- 旧 root tip aggregator

残す候補は license、README の最小 project identity、`lean-toolchain`、必要最小限の
`lakefile.toml` / manifest、最小 CI、参照文献情報である。削除 scope は bootstrap 前に
read-only inventory を取り、旧 `main` から常に回収できることを確認する。

旧 API への compatibility shim、deprecated alias、facade は作らない。旧 proof を参照する時は
`git show <legacy-main>:<path>` 等で読み、新 source から import しない。

### M2: minimal foundation

- public root と layer rule
- minimal axiom/status checker
- Chapter 2 §2.1 に必要な single-site basis/operator だけ

この段階では many-body、graph Hamiltonian、infinite-volume framework を作らない。

### M3 onward: front-to-back source slices

各 source item について source statement、math-before-code、implementation、independent
verification、status generation を一周させる。chapter milestone では旧 declaration 数でなく、
Tasaki source item coverage と statement equivalence を監査する。

## Initial Tasaki front-to-back backlog

最初の backlog は「既存コードで完成度が高い順」ではなく、Tasaki の印刷順である。

1. **§2.1 冒頭: single spin の対象と basis**
   - `N = 2S`、`SpinBasis N = Fin (N+1)`。
   - `S³`、`S±` と basis action、eqs. (2.1.2), (2.1.3)。
   - Cartesian `S¹,S²,S³` と commutator eq. (2.1.1)、Casimir。
   - この slice に不要な site/graph/many-body abstraction は入れない。
2. **§2.1 concrete low-spin matrices**
   - spin-half action eqs. (2.1.4), (2.1.5)。
   - matrix forms eqs. (2.1.6)--(2.1.9)。
   - `S=1/2` と `S=1` を一般 spin operator の specialization として証明する。
3. **Problem 2.1.a**
   - operator polynomial/spanning statement を本文・solution p.493 と照合する。
   - matrix-unit/Lagrange 補題は、この問題の final line に必要なものだけ導入する。
4. **§2.1 rotations**
   - eqs. (2.1.10)--(2.1.25) を本文順に扱う。
   - matrix exponential の generic infrastructure は、この source item が要求する範囲に
     限る。
5. **Problems 2.1.b--2.1.g**
   - 本文に現れる順で処理し、spin-half/spin-one/general-spin の関係を specialization で保つ。
6. **§2.2 many-spin system**
   - ここで初めて `Volume`、generic `Config/Ket/Op`、`embedSite` を導入する。
   - total spin、global rotation、sector decomposition を §2.2 の source order で追加する。
   - §2.2 に入る前に future-proof な many-body framework を作り過ぎない。
7. **§2.3 time reversal**
8. **§2.4 ferromagnetic Heisenberg model**
9. **§2.5 antiferromagnetic Heisenberg model / Marshall--Lieb--Mattis**

Appendix の一般論は、本文の現在 item が必要とする時に mathlib と照合し、必要最小限を
`Math` に置く。Appendix 全体を先回りして形式化しない。旧 Theorem 2.4、Chapter 4、AKLT、
Hubbard の完成 proof を先に救出しない。

## Acceptance criteria

### This design PR

- 本ファイルだけが変更されている。
- 基準 SHA と各主要測定値に再測定 command がある。
- Adopt / Rewrite / Drop が file または pattern の根拠付きで分類されている。
- canonical representation、graph/volume boundary、generic local basis、coupling bundle が
  decision として記録されている。
- dependency DAG と初期 directory が一方向である。
- axiom の自動移植禁止と defer 境界が明記されている。
- source-item/PR/test/verification policy が明記されている。
- bootstrap が設計承認後の別 PR であり、本 PR が現コードを変更しないことが明記されている。
- compatibility shim を作らないことが明記されている。
- initial backlog が §2.1 から始まり、many-body kernel を §2.2 より前に作り過ぎない。
- 下記 P0 decisions が merge 前に明示的に解決される。

### Bootstrap PR

- 旧 `main` が変更されず、legacy tip が参照可能である。
- 削除対象の read-only inventory と回収方法が記録されている。
- 新系列に旧 production/test module の import がない。
- package/toolchain は再現可能で、依存更新を混ぜていない。
- minimal `lake build` が warning zero で通る。
- layer rule、forbidden proof construct check、actual axiom check の最小 gate がある。
- public root が DAG tip aggregator ではない。

### Each source-item PR

- Tasaki locator と statement review がある。
- final line から必要性を説明できない declaration がない。
- 本文より強い仮定がなく、強い仮定には consistency/non-vacuity evidence がある。
- build warning zero、禁止 proof construct zero、actual axiom set 合格。
- unrelated source item、future helper、compatibility work を含まない。
- status の正本が一箇所だけ更新され、表示は生成される。

### Chapter 2 milestone

- §2.1--§2.5 の対象 source item が印刷順に追跡可能である。
- spin-half と general-spin の many-body kernel が一つである。
- graph の有限性と finite volume の有限性が分離されている。
- public theorem が proof-route helper や `Matrix.toLin'` を露出しない。
- 旧 source を import せず、旧実装と同等の対象 statement を新 axiom policy 下で再現する。

## Open P0 decisions

以下は bootstrap を始める前に解決し、decision log に結果を固定する。

1. **再実装 trunk の恒久名と default/protection 設定**
   - 推奨: 旧 `main` はそのまま保存し、新 trunk は役割が分かる固定名を使う。
   - branch rename/default branch 変更は repository operation であり、本設計 PR の範囲外。
2. **package name / root namespace**
   - 推奨: package と root namespace `LatticeSystem` は維持する。旧 declaration path の
     互換性は維持しない。
3. **bootstrap で残す公開文書の最小集合**
   - 推奨: project identity、build instruction、設計文書だけ残し、旧 status/history は
     frozen legacy branch で読む。外部 URL を維持する必要がある場合は redirect だけを
     別 PR で扱う。
4. **新 status ledger の最小 schema**
   - 推奨必須 field: stable source-item id、locator、Lean declaration、status、expected
     project-specific axioms。PR chronicle、proof prose、複製 statement は入れない。
5. **logical axiom baseline**
   - `propext`、`Classical.choice`、`Quot.sound` 等、Lean/mathlib 由来の許容集合と、
     project-specific axiom zero/allowlist を checker 上で区別する exact policy を決める。
6. **file size / compile budget**
   - 推奨: 700 行を review trigger、900 行を split 検討の強い signal とし、数値だけで
     機械分割しない。PR ごとの import/build delta を最初の Chapter 2 実測から予算化する。

この P0 list を未解決のまま bootstrap の削除や実装を開始しない。
