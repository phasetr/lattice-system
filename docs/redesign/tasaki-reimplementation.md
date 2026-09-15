# Tasaki 本形式化の再設計・再実装方針

## Status / Decision

- Status: **review-ready proposal**。PR merge 前なので accepted ではないが、bootstrap を
  止める未決 P0 は残していない。以下の decision set 全体をこの PR で review する。
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
8. coverage universe は Chapter 2--11 と Appendix A の、番号付き Definition / Theorem /
   Lemma / Proposition / Corollary / Conjecture / Problem、および後続結果が参照する番号付き
   数式とする。Chapter 1 の概説と、番号がなく後続結果にも使われない説明は coverage 外と
   する。外部文献に証明を委ねるという理由だけでは coverage から外さない。
9. 計算上の canonical operator は `Matrix`、物理 observable は Hermitian 証明を持つ
   `Observable` bundle とする。zero vector を eigenvector と呼ばない。
10. volume inclusion、configuration restriction、operator の identity extension、volume
    equivalence による reindexing は、identity/composition law まで初期 API に含める。
11. weighted coupling の support は「non-edge なら weight zero」、実際に非零な辺からなる
    graph を `activeGraph` と定義する。connectivity と sign は `activeGraph` 上の refinement
    bundle に置く。
12. fermion は finite configuration/operator carrier だけを共有する。bosonic `embedSite` を
    fermion operator の API として共有せず、Chapter 9 到達時に ordered Jordan--Wigner 表現を
    canonical とする。
13. bootstrap は一つの atomic PR とし、旧 source 除去後の最終 tree、build target、public
    root、layer check、minimal status/axiom checker、新 trunk 用 CI を同時に成立させる。

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

基準 revision には Lean file が 1,727 個、合計 287,519 行ある。working tree の変化に
左右されない再測定は、revision を archive した一時 directory 上で行う。

```sh
revision=01bcb49d49db92c225cfa74b74d409dd0a9c4edc
measure_dir=$(mktemp -d)
git archive "$revision" LatticeSystem | tar -x -C "$measure_dir"
find "$measure_dir/LatticeSystem" -name '*.lean' | wc -l
find "$measure_dir/LatticeSystem" -name '*.lean' -print0 | xargs -0 wc -l | tail -1
```

`LatticeSystem/Quantum/SpinS/` 直下だけで 873 file、
`LatticeSystem/Fermion/JordanWigner/Hubbard/` 直下で 369 file ある。

```sh
find "$measure_dir/LatticeSystem/Quantum/SpinS" -maxdepth 1 -name '*.lean' | wc -l
find "$measure_dir/LatticeSystem/Fermion/JordanWigner/Hubbard" -maxdepth 1 -name '*.lean' | wc -l
```

開発工程に由来する名前を持つ file は、dev-research の広義分類では約 186 file だった。
名称の分類境界に依存するため、この値自体を gate にはしない。同じ revision で、狭義の
`Core|Structural|Wrapper|Assembly|Capstone|Discharge|Conditional` は 143 file、
`Bridge|Final|Target|Endpoint|Step` まで含める広義再測定は 188 file である。

```sh
find "$measure_dir/LatticeSystem" -name '*.lean' \
  | awk '$0 ~ /(Core|Structural|Wrapper|Assembly|Capstone|Discharge|Conditional)/' \
  | wc -l
find "$measure_dir/LatticeSystem" -name '*.lean' \
  | awk '$0 ~ /(Core|Structural|Wrapper|Assembly|Capstone|Discharge|Conditional|Bridge|Final|Target|Endpoint|Step)/' \
  | wc -l
rm -rf "$measure_dir"
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
git show --stat --oneline 01bcb49d49db92c225cfa74b74d409dd0a9c4edc
git show 01bcb49d49db92c225cfa74b74d409dd0a9c4edc:\
LatticeSystem/Tests/AxisSwapDiagBoundSatisfiable.lean | wc -l
```

これは個別の失敗だけでなく、巨大 signature、positional forwarding、proof-stage API、
signature fixture が組み合わさると、数学的 defect の修正より周辺維持の方が大きくなる
ことを示す。

### import root と test の役割過多

`LatticeSystem.lean` は公開 API を選ぶ facade ではなく、library import DAG の全 tip を
列挙することを自ら invariant としている。基準 revision では 103 imports ある。
`LatticeSystem/Tests.lean` は 187 test modules を手動列挙し、tests 全体は 26,827 行ある。

```sh
revision=01bcb49d49db92c225cfa74b74d409dd0a9c4edc
git show "$revision":LatticeSystem.lean | rg -n '^import ' | wc -l
git show "$revision":LatticeSystem/Tests.lean | rg -n '^import ' | wc -l
measure_dir=$(mktemp -d)
git archive "$revision" LatticeSystem/Tests | tar -x -C "$measure_dir"
find "$measure_dir/LatticeSystem/Tests" -name '*.lean' -print0 | xargs -0 wc -l | tail -1
rm -rf "$measure_dir"
```

proof 自身を再掲する signature shim、grep hit 数、過去の一時 signature を保つ fixture は、
数学的意味の regression test と分離されていない。

### axiom と status の堆積

基準 revision で行頭 `axiom ` を raw text 検索すると 81 hit するが、そのうち 11 hit は
module/doc comment 内の prose である。Lean declaration としての project axiom は **70 個**
である。11 個の false positive は次の file:line で、revision-pinned な grep 出力を全件
目視分類した。

- `GeneralFlatBandDisconnected.lean:119`
- `MielkeIncidenceMatrix.lean:375`
- `MielkeTheorems.lean:100`
- `SpinWaveExcitation.lean:24`
- `AnisotropicHeisenbergSpinSLambdaOneBoundary.lean:191`
- `AnisotropicHeisenbergSpinSObligation2FromSU2Unique.lean:36`
- `AnisotropicHeisenbergStrictGSAtSU2FromStrictGap.lean:16`
- `BoxLocalTranslationInvariant.lean:19`
- `BulkDensity.lean:14`
- `NoLongRangeOrder1D.lean:25`
- `ShastryNoSSBReduction.lean:371`

```sh
revision=01bcb49d49db92c225cfa74b74d409dd0a9c4edc
git grep -n '^axiom ' "$revision" -- 'LatticeSystem/**/*.lean'
# raw 81 - comment false positives 11 = project axiom declarations 70
```

C\*-algebra、GNS、KMS 等の合意済み defer 対象だけでなく、後で discharge するための
定理、物理的 marker predicate、有限次元の未完部分が同じ構文で混在する。新系列で
これらを一括移植すると、古い分類判断まで無批判に固定してしまう。

現行 governance では `docs/formalization/legacy/` が complete status / capstone の暫定
authority であり、prototype の `formalization-status/v2/` は全体 authority ではない。
しかし theorem claim、locator、declaration name、axiom status は Lean source、legacy
catalogue、`tex/proof-guide.tex`、一部の structured records に反復され、同期漏れで drift
する。現行 validator の厳密な actual-axiom 照合という発想は採用するが、複数の status
正本と legacy catalogue guard は採用しない。

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
| tests の具体的手法 | `Fin n` の全ケース証明、small matrix の全 entry 計算、二つの独立定義の等式 | 意味を検査する短い test に限定 |
| status validator | actual axiom set と declaration module を Lean 環境から検査する発想 | ledger と checker を最小から作り直す |
| Tasaki の書誌・locator | 1st ed., Springer 2020 の chapter/section/equation/page | tracked citation metadata に保持し、gitignored file を build/review の前提にしない |

低層資産は file 単位で採用しない。採用単位は「定義の数学的内容」「証明アイデア」または
「検証方法」であり、新系列の source は原則として書き直す。旧 code を直接 import せず、
commit や file を cherry-pick しない。各 source-item PR は adopt gate の各項目について
`adopt / rewrite / drop` と根拠を PR 内の legacy assessment に記録する。

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

volume API は包含 `h : Λ ⊆ Ω` と volume equivalence を一級データとして扱い、少なくとも
次を持つ。

- `restrictConfig h : Config Ω I → Config Λ I`: configuration の座標制限。
- `restrictGraph Λ G`: `G` の `↥Λ` への induced graph。
- `restrictCoupling Λ J`: graph/coupling の finite volume への制限。
- `extendOp h : Op Λ I → Op Ω I`: `Ω \ Λ` 上で恒等作用する tensor-factor identity
  extension。matrix entry は outside-`Λ` の configuration が一致しない時に zero とする。
- `reindexConfig` / `reindexOp`: volume/basis equivalence による添字変更。

次の law を定義と同時に証明する。

- restriction の identity と composition。
- identity extension の identity と composition
  (`extendOp (Λ ⊆ Θ) = extendOp (Ω ⊆ Θ) ∘ extendOp (Λ ⊆ Ω)`)。
- `extendOp` が zero/one/add/mul/scalar/adjoint を保つこと。
- reindexing の identity、inverse、composition と、restriction/extension との自然性。
- `Observable` の identity extension/reindexing が Hermitian 性を保つこと。

ket の `Λ → Ω` extension は outside-`Λ` の基準状態を選ばなければ canonical でないので、
初期 API には置かない。「operator の identity extension」と「configuration の restriction」を
混同しない。

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

計算 carrier と物理 observable は区別する。

```lean
structure Observable (Λ : Finset V) (I : Type*) where
  toMatrix : Op Λ I
  isHermitian : toMatrix.IsHermitian

def IsEigenvector (A : Op Λ I) (ψ : Ket Λ I) (μ : ℂ) : Prop :=
  ψ ≠ 0 ∧ A.mulVec ψ = μ • ψ
```

Hamiltonian、spin component、number operator 等、self-adjoint であることが数学的契約に
含まれる対象は `Observable` を返す。途中計算と非 self-adjoint な raising/lowering/
creation/annihilation は `Op` のまま扱う。`Observable` の add、real scalar、commuting mul、
unitary conjugation、identity extension は Hermitian 証明込みの constructor とする。

`Quantum.Finite.Spectrum` だけが matrix-to-linear-map bridge を所有し、次を公開する。

- `eigenspace A μ`
- Hermitian observable の実固有値列
- `groundEnergy H : ℝ`
- `groundSpace H`
- `IsGroundState H ψ := IsEigenvector H.toMatrix ψ (groundEnergy H)`

`IsEigenvector` は必ず `ψ ≠ 0` を含み、zero vector を eigenvector/ground state と呼ぶ API は
作らない。公開 theorem は `Matrix.toLin'`、固有値の並べ方、最小 index の実装を露出しない。
必要な `[Nonempty (Config Λ I)]` 等は `Spectrum` の constructor 境界で解決する。

### Spin representation

- spin quantum number は `N : ℕ`、`2S = N` とする。
- local basis は `SpinBasis N := Fin (N+1)`。
- axis は `Axis` で indexed にする。
- `spinOp N : Axis → Matrix (SpinBasis N) (SpinBasis N) ℂ` を中心に置く。
- `spinRaise` / `spinLower`、Casimir、rotation はこの API から導く。
- `S=1/2`、`S=1` の行列を別定義せず、一般定義の specialization theorem にする。

### Bundled coupling

公開 theorem が次を個別引数として反復しない構造を用意する。base structure は概念的に
次の形で確定する。

```lean
structure WeightedCoupling (V : Type*) where
  graph : SimpleGraph V
  weight : V → V → ℝ
  symm : ∀ x y, weight x y = weight y x
  zero_of_not_adj : ∀ {x y}, ¬ graph.Adj x y → weight x y = 0
```

`SimpleGraph` の irreflexivity と `zero_of_not_adj` から diagonal zero を導く。
`graph` は許容 support の supergraph であり、zero-weight edge は interaction を結ばない。
したがって

```lean
(J.activeGraph).Adj x y ↔ J.graph.Adj x y ∧ J.weight x y ≠ 0
```

と定義する。support の意味は **non-edge implies zero** であり、graph edge 上の nonzero を
base structure に要求しない。connectivity theorem は `J.graph.Connected` ではなく
`J.activeGraph.Connected` を要求する。

nonnegative/strictly-positive antiferromagnetic coupling、nonpositive/strictly-negative
ferromagnetic coupling、bipartite support は `activeGraph` 上の refinement bundle とする。
符号 convention は refined constructor で一度固定し、各 theorem に real/symmetric/support/
sign/connectivity を平坦に再掲しない。

Hamiltonian の正準定義は有限 induced `activeGraph` の unordered edge sum とする。
ordered-pair sum と `1/2` は theorem の本文がその表記を必要とする時の bridge に限定する。

positivity を coupling の全用途へ強制しない。例えば ferromagnetic/antiferromagnetic の
符号は model layer の refined structure とする。

### Fermion representation boundary

fermion は `Config` / `Ket` / `Op` という有限 matrix carrier と volume/reindexing machinery
だけを共有する。異なる site の operator が可換であることを契約に含む bosonic
`embedSite` を fermionic creation/annihilation の構成 API として共有しない。

Chapter 9 に到達した時、有限 mode に明示的な linear order を持たせ、ordered
Jordan--Wigner string を canonical concrete representation とする。CAR はその表現から
証明する。一般 graded tensor product、抽象 CAR algebra、order-independent equivalence は、
Tasaki の現在 source item が実際に必要とするまで導入しない。fermion のために Chapter 2 の
kernel を先に複雑化しない。

### Named mathematical predicates

以下を用意し、巨大な conjunction と representation detail を capstone から隠す。

- nonzero を含む `IsEigenvector`
- `Observable` 上の `groundEnergy` / `groundSpace` / `IsGroundState`
- `MagnetizationSector`
- explicit bipartition / connected weighted graph predicate

bundle は仮定を隠して弱く見せるためではなく、同じ invariant 集合を一度構成し、すべての
consumer が同一の数学的対象を受け取るために使う。constructor の充足可能性 test も行う。

## Axiom policy

1. `sorry`、`admit`、`native_decide` は禁止する。
2. 旧 project axiom declaration 70 個は一つも自動移植しない。
3. defer してよい対象は、抽象 C\*-algebra、GNS、KMS、`WeakDual`、state、Wigner、
   内容のない述語定義に限る。
4. 摂動論で defer してよいのは、cluster expansion、quasi-adiabatic continuation、
   Lieb--Robinson bound、Rellich--Kato 型の分岐連続性の一般論など、真に作用素環的・
   解析的極限を要するものに限る。
5. **無限体積または thermodynamic limit であること自体は defer 理由にならない。**
   無限グラフ、volume exhaustion、極限の存在・性質は長期中心目標として証明する。
   その途中で上記の抽象 C\*-algebra/state 等に該当する個別 component だけを、宣言単位で
   defer 審査する。
6. 有限次元・固定 finite volume の線形代数、spectral theory、固有値連続性、縮退摂動、
   変分評価は必ず証明する。「難しい」「摂動論」「後で使う」は defer 理由にならない。
7. 内容のない predicate を `axiom ... : ... → Prop` として導入する場合も、存在 theorem を
   暗黙に与えていないか、結論を vacuous にしていないかを source item ごとに審査する。
8. conjecture は `def ... : Prop` として statement を記録してよいが、true と主張する
   `axiom` を置かない。
9. deferred declaration には source locator、欠けている数学、reopen condition、依存する
   capstone を一つの ledger entry に記録する。
10. 各 proved capstone の actual axiom set を Lean environment から検査する。許可される
   logical axioms と project-specific axiom を完全一致で区別する。
11. temporary axiom を後で discharge する workflow は使わない。大型 theorem は proved
   supporting lemma の列へ分割し、未証明 capstone を source に置かない。

## Source-item, PR, and test policy

### Source item

coverage universe は、Tasaki 1st ed. (Springer, 2020) の Chapter 2--11 と Appendix A に
ある番号付き Definition / Theorem / Lemma / Proposition / Corollary / Conjecture / Problem、
および後続の covered result が参照する番号付き数式である。Chapter 1 の概説と、番号がなく
後続結果にも使われない説明は対象外である。この閉じた universe は tracked citation metadata
へ source-order key とともに登録し、未登録 item を ad hoc に選ばない。

source item は Tasaki の一定理、一問題、または一つの数学的責務をなす連続した equation
block とする。edition、chapter/section、theorem/problem/equation number、page を必須にする。
外部文献に証明を委ねる item も coverage に残し、新 axiom policy に従って prove/defer を
判断する。

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
- 旧 code を import または cherry-pick しない。proof idea を読む場合も、新 canonical API
  上で source から実装し直す。
- 各 source-item PR に `Legacy assessment` を置き、参照した旧 declaration ごとに
  `adopt idea / rewrite / drop`、adopt gate の判定、直接 code 移植がないことを記録する。

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

一項でも落ちたものは修理移植ではなく、本文 statement から再構成する。判定結果は当該
source-item PR の `Legacy assessment` に残し、設計 PR で旧資産全体を事前承認しない。

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

- 旧 `main` の anchor は
  `01bcb49d49db92c225cfa74b74d409dd0a9c4edc` とし、frozen legacy とする。
- 再実装 trunk は **`rewrite-main`** とする。`rewrite-main` は上記 anchor から派生し、
  履歴比較可能性を保つ。
- `redesign/tasaki-reimplementation-plan` を `rewrite-main` への設計 PR とする。
- 本 PR は本ファイルだけを追加し、現コードを変更しない。

### M1: atomic bootstrap after approval

設計承認後の一つの bootstrap PR で初めて、再実装系列から次を除く。

- 旧 `LatticeSystem/` production source
- 旧 `LatticeSystem/Tests*`
- 旧 legacy/prototype status catalogue と専用 migration guards
- 旧 root tip aggregator

この PR は「削除だけ」を一時的に merge して後続 PR で直す二段階にしない。同じ PR の
最終 tree で次を同時に成立させる。

- package identity、`lean-toolchain`、依存を変えない最小 `lakefile.toml` / manifest。
- public root `LatticeSystem.lean`。DAG tip aggregator ではなく、bootstrap 時点の空の stable
  surface を表す。
- default build target と、checker を含む CI target。
- import layer rule を検査する dependency-free checker。
- empty catalogue から開始できる minimal source/status schema と actual-axiom checker。
- `README.md` の最小 project identity、build command、legacy anchor、新 trunk の説明。
- tracked `references/tasaki-2020.json` に edition、ISBN/DOI、chapter/section/page range、
  source-order key を保持する。local extracted text/PDF は調査補助にすぎず、build、CI、
  review、再開の依存にしない。
- `.github/workflows/lean_action_ci.yml` の push branch を `main` から `rewrite-main` へ変更し、
  pull request でも同じ build/check を実行する。
- tracked docs 内の repository link は相対 link を優先し、branch を埋め込む必要がある link は
  `/blob/rewrite-main/` を使う。legacy 証跡だけは anchor SHA の permalink を使い、
  `/blob/main/` を新系列の current link として残さない。

削除 scope は bootstrap PR 内で read-only inventory を取り、legacy anchor から常に回収
できることを確認する。bootstrap commit 自身が `lake build`、layer check、empty-status
validation、actual-axiom check を通らない状態を branch 上に残さない。

旧 API への compatibility shim、deprecated alias、facade は作らない。旧 proof を参照する時は
`git show 01bcb49d49db92c225cfa74b74d409dd0a9c4edc:<path>` 等で読み、新 source から
import せず、commit/file を cherry-pick しない。

### M2: first source-item vertical slice

- 下記 backlog item 1 を最初の implementation PR とする。
- item 1 に必要な single-site basis/operator だけを同じ vertical slice 内で導入する。
- bootstrap infrastructure の追加・修理をこの PR に持ち越さない。

この段階では many-body、graph Hamiltonian、infinite-volume framework を作らない。

### M3 onward: front-to-back source slices

各 source item について source statement、math-before-code、implementation、independent
verification、status generation を一周させる。chapter milestone では旧 declaration 数でなく、
Tasaki source item coverage と statement equivalence を監査する。

## Initial Tasaki front-to-back backlog

最初の backlog は「既存コードで完成度が高い順」ではなく、Tasaki 1st ed., Springer 2020,
§2.1, pp. 13--20 の印刷順である。次の 10 item を tracked citation metadata にこの順で置く。

1. **`tasaki-2020-2.1-single-spin-foundation`, §2.1, pp. 13--14**
   - exact first implementation item。
   - 前置定義として spin quantum number `S = N/2`、Hilbert space `h₀` の次元 `2S+1`、
     axes `α = 1,2,3`、self-adjoint `Ŝ⁽ᵅ⁾`、Levi-Civita 記号、`Ŝ±`、正規直交 basis
     `|ψ_σ⟩` を、この item の concrete standard representation に必要な範囲で定義する。
   - **本文順を固定する**: commutation relations **eq. (2.1.1), p. 13** を先に証明し、次に
     本文直後の Casimir relation **`Ŝ² = S(S+1)1̂`, p. 14**、その後に basis actions
     **eqs. (2.1.2), (2.1.3), p. 14** を証明する。
   - 定義実装の都合で proof の宣言順を逆転させず、public source-order section もこの順に
     する。site、graph、many-body、rotation は入れない。
2. **`tasaki-2020-2.1-spin-half-actions`, §2.1, p. 14**
   - spin-half notation と basis actions eqs. (2.1.4), (2.1.5)。item 1 の specialization。
3. **`tasaki-2020-2.1-matrix-representations`, §2.1, pp. 14--15**
   - basis column eq. (2.1.6)、spin-half matrices eq. (2.1.7)、その直後の square/
     anticommutator、Pauli matrices eq. (2.1.8)、spin-one matrices eq. (2.1.9)。
4. **`tasaki-2020-problem-2.1.a`, §2.1, p. 15; solution p. 493**
   - 任意の `(2S+1) × (2S+1)` operator が `1̂,Ŝ¹,Ŝ²,Ŝ³` の polynomial であること。
5. **`tasaki-2020-2.1-rotation-definition`, §2.1, p. 15**
   - `Ûθ⁽ᵅ⁾ := exp[-iθŜ⁽ᵅ⁾]`、unitarity、same-axis group law、adjoint。eq. (2.1.10)
     より前の unnumbered claims。
6. **`tasaki-2020-2.1-rotation-matrices`, §2.1, pp. 15--16**
   - operator transformation eq. (2.1.10)、three-dimensional rotation matrices
     eq. (2.1.11)、entry formula eq. (2.1.12)。
7. **`tasaki-2020-2.1-rotation-conjugation`, §2.1, p. 16**
   - eqs. (2.1.13)--(2.1.16) と、本文の proof eqs. (2.1.17), (2.1.18)。
8. **`tasaki-2020-2.1-vector-covariance`, §2.1, p. 17**
   - `Ŝ·v` の covariance eqs. (2.1.19), (2.1.20)。
9. **`tasaki-2020-2.1-special-rotations`, §2.1, pp. 17--18**
   - `π` / `π/2` conjugation eqs. (2.1.21), (2.1.22)、`2π` rotation eq. (2.1.23)、
     π-rotation relations eqs. (2.1.24), (2.1.25)。
10. **`tasaki-2020-problem-2.1.b`, §2.1, p. 18; solution p. 493**
    - 先に本文の spin-half closed form eq. (2.1.26) を statement として登録し、直後の
      Problem 2.1.b の derivation で証明する。

以後も Problem 2.1.c, d, e、Z₂×Z₂ の定義と eq. (2.1.27) 以降、Problems 2.1.f, g の
印刷順を守り、§2.1 完了後にだけ §2.2 へ進む。§2.2 到達時に初めて `Volume`、generic
`Config/Ket/Op`、bosonic `embedSite` を導入し、total spin、global rotation、sector
decomposition を §2.2 の source order で追加する。§2.2 より前に future-proof な many-body
kernel を作らない。

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
- coverage、first item、spectral、volume、coupling、fermion を含む P0 decision がすべて
  本文と末尾の decision register で確定し、未決 P0 がゼロである。
- この PR が現在の implementation/status claim を変えないため、README、`docs/index.md`、
  `tex/proof-guide.tex` の同期が不要であることを確認している。

### Bootstrap PR

- 旧 `main` が変更されず、legacy tip が参照可能である。
- 削除対象の read-only inventory と回収方法が記録されている。
- 新系列に旧 production/test module の import がない。
- package/toolchain は再現可能で、依存更新を混ぜていない。
- minimal `lake build` が warning zero で通る。
- layer rule、forbidden proof construct check、actual axiom check の最小 gate がある。
- public root が DAG tip aggregator ではない。
- CI の push target が `rewrite-main` で、required check が branch protection に登録される。
- current repository link に `/blob/main/` が残らず、relative / `rewrite-main` / legacy anchor
  permalink の使い分けが検査される。

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

## P0 decision register

以下をすべて **decided** とする。未決 P0 はゼロである。

1. **trunk**: 新 trunk は `rewrite-main`。bootstrap merge 後に repository default を
   `rewrite-main` とし、build/layer/status/axiom checks を required にする。旧 `main` は
   anchor `01bcb49d49db92c225cfa74b74d409dd0a9c4edc` を含む frozen legacy として保護する。
2. **package / namespace**: package name と root namespace `LatticeSystem` は維持する。
   旧 declaration/import path の互換性は維持しない。
3. **bootstrap public docs**: project identity、build instruction、本設計、tracked citation
   metadata を残す。旧 status/history は legacy anchor で読む。必要な external route の
   redirect は bootstrap と混ぜず、別の docs-only PR で扱う。
4. **status ledger schema**: stable source-item id、source-order key、edition/locator、Lean
   declaration、status、expected logical axiom subset、expected project-specific axioms、
   legacy assessment を必須 field とする。PR chronicle、proof prose、statement copy は
   入れない。
5. **logical axiom baseline**: proved capstone の project-specific axiom は既定で空集合。
   Lean/mathlib の logical axioms `propext`、`Classical.choice`、`Quot.sound` は許容 universe
   とし、各 capstone record には実際に使う subset を完全一致で記録する。それ以外は
   explicit deferred record がなければ reject する。
6. **file / compile budget**: 700 行を responsibility review trigger、900 行を強い split
   signal とするが、数値だけで機械分割しない。compile/import budget は最初の Chapter 2
   実測を baseline とし、各 PR で delta を記録する。
7. **coverage universe**: Chapter 2--11 と Appendix A の番号付き result/problem、および
   covered result が参照する番号付き数式。Chapter 1 の概説は除く。
8. **first source item**: `tasaki-2020-2.1-single-spin-foundation`, 1st ed. §2.1,
   pp. 13--14。eq. (2.1.1) → Casimir → eqs. (2.1.2), (2.1.3) の順を固定する。
9. **spectral API**: `Matrix` が計算 canonical、Hermitian proof を持つ `Observable` が
   self-adjoint な物理量の API。`IsEigenvector` は nonzero を含み、spectral bridge は
   `Quantum.Finite.Spectrum` だけに置く。
10. **volume API**: configuration restriction、graph/coupling restriction、operator identity
    extension、equivalence reindexing と、それぞれの identity/composition/naturality law を
    初期 many-body API の完了条件とする。canonical でない ket extension は置かない。
11. **weighted support**: `zero_of_not_adj` を base semantics とし、非零 weight edge を
    `activeGraph` とする。connectivity、bipartition、ferro/antiferro sign は activeGraph 上の
    refinement bundle に置く。
12. **fermion representation**: carrier/volume/reindexing だけを共有し、bosonic `embedSite`
    を fermion API に使わない。Chapter 9 で ordered Jordan--Wigner を canonical とし、
    graded/CAR 一般化は実需要まで行わない。
13. **bootstrap atomicity / CI / citations**: M1 の最終 tree で build/root/layer/status/axiom
    checks と `rewrite-main` CI を同時成立させる。書誌・locator は tracked metadata に置き、
    gitignored local artifact を前提にしない。current link は relative または
    `rewrite-main`、legacy evidence は anchor SHA permalink とする。

## Documentation sync conclusion for this PR

本 PR は review 中の再設計提案を一ファイル追加するだけで、現在の実装、公開 theorem status、
build command、axiom status を変更しない。したがって `README.md`、`docs/index.md`、
`tex/proof-guide.tex` を同期すると、未承認の新系列を現在の公開状態として誤表示する。
この PR では三者の同期は **不要かつ行わない**。bootstrap merge 時に README と current
branch link を更新し、最初の source-item PR から生成 status を同期する。
