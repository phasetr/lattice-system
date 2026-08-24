import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebShenQiuShibaBridge
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveFullSectorUnique
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveBalancedGround
import LatticeSystem.Math.MatrixAnalysis.UnitaryGroundTransport
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebShenQiuShibaTransport
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismCenteredSector
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebShenQiuSectorCasimir

/-!
# Test coverage for the Theorem 10.8 Shiba Hamiltonian bridge (PR-1) and spin-transport (PR-2)

Pins the API contract of the constant-shift identity and the Shiba conjugation bridge of
`LatticeSystem/Fermion/JordanWigner/Hubbard/LiebShenQiuShibaBridge.lean` (PR-1 of the
Theorem 10.8 discharge, design report `.self-local/docs/theorem-10-8-design.md` §1), plus the
four public `euclideanExpectation` helpers of `LiebAttractive.lean`:

1. **B1** `symmetricAttractiveHubbardHamiltonian_eq_attractive_sub_smul` — the constant-shift
   identity `Ĥ^{attr,sym}(T,U) = Ĥ^{attr}(T + diag(U/2), U) − ((ΣU)/4)•1`.
2. **B2** `shibaSignedUnitary_conj_symmetricRepulsive_eq_symmetricAttractive` — the Hamiltonian
   bridge `Ûᴴ Ĥ^{rep,sym}(T,U) Û = Ĥ^{attr,sym}(T,U)` (composing the existing
   `shibaSignedUnitary_conj_symmetricRepulsive_eq_attractive` with B1, the `¼ΣU` shift cancelling
   exactly).
3. **P1–P4** the four `euclideanExpectation` helpers (`_smul`, `_add`, `_shiba_conj`,
   `_conjTranspose_mul_self`), public and sitting next to `euclideanExpectation` itself, so that
   the later Theorem 10.8 layers reuse them instead of re-deriving them.

Also pins the API contract of PR-2 (`Ŝ³φ = 0` extraction + Shiba transport,
`.self-local/docs/theorem-10-8-pr2-design.md` §2), TDD Red:

4. **G1** `LatticeSystem.Math.IsUniqueGroundStateOn.conj_unitary` — the generic unitary-conjugation
   ground-state transport (new file `Math/MatrixAnalysis/UnitaryGroundTransport.lean`), pinning
   the full two-sided hypothesis list (`hUUc`/`hconj`/`hfwd`/`hbwd`), the fragile part per
   design §4 R1/R2.
5. **S1** `fermionTotalSpinZ_mulVec_eq_zero_of_fermionTotalSpinSquared_mulVec_eq_zero` — the
   spin-algebra extraction (`LiebAttractiveFullSectorUnique.lean`, design §2.2), plus a sanity
   instance at `N = 0`, `f = 0`.
6. **T1** `shibaTransport_uniqueGroundStateOn_spinZSector` — the plain-attractive face of the
   Hubbard transport (`LiebRepulsiveBalancedGround.lean`, design §2.3), energy slot `E − (∑ U)/4`.
7. **T2** `shibaTransport_uniqueGroundStateOn_spinZSector_symmetricAttractive` — the
   symmetric-attractive face (new file `LiebShenQiuShibaTransport.lean`, design §2.4), energy slot
   exactly `E`, obtained by instantiating the shared transport
   `shibaTransport_uniqueGroundStateOn_spinZSector_of_conj` at the residual-free bridge **B2**.
8. **INV** a statement-invariance pin for `repulsiveSpinZSector_ground_unique` (design §1.1): the
   full existential type, discharged by the theorem name, so that a future refactor (PR-2's
   corollary form) cannot silently reorder/add conjuncts without breaking the three positional
   call sites at `LiebRepulsiveCorrelation.lean:144`, `LiebFerrimagnetismCenteredSector.lean:266`,
   `LiebRepulsiveSectorBridgeFinal.lean:159`.

Also pins the API contract of PR-3 (`k₀ → k` sector generalization + Casimir value, design report
`.self-local/docs/theorem-10-8-pr3-design.md`), TDD Red:

9. **C1** `liebShenQiu_towerExponent_weight_eq` — the tower-exponent weight arithmetic
   `L/2 − (a − Ne/2) = (Ne − (N+1))/2` (design §3 item 1), the generalized weight the
   symmetric-attractive Shiba transport's sector lands at.
10. **C2** `liebShenQiu_sectorGround_mem_halfFillingGround` — the generalized pinch
    (`liebRepulsive_sectorGroundEnergy_eq_groundEnergy`, PR-3's `k`-general form) applied to the
    transport's sector ground state, landing it in the `(N+1)`-electron ground submodule
    (design §3 item 2).
11. **C3** `liebShenQiu_casimir_eq` — Theorem 10.4's Casimir eigenvalue equation
    `Ŝ² ψ = S₀(S₀+1) ψ` transported onto that same sector ground state (design §3 item 3).

Each `example` fails to elaborate unless the corresponding declaration exists, is public, and has
exactly this signature.

**Not covered here**: the pair/ladder algebra and signed-sum inequality (PR-4); and the capstone
assembly (PR-5).
-/

namespace LatticeSystem.Tests.LiebShenQiuShibaBridge

open LatticeSystem.Fermion LatticeSystem.Quantum LatticeSystem.Math Matrix
open scoped BigOperators

variable {N : ℕ}

/-- Pins **B1**: the symmetric attractive Hamiltonian is the shifted plain attractive Hamiltonian
minus the constant `(ΣU)/4`. -/
example (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) :
    symmetricAttractiveHubbardHamiltonian N T U
      = attractiveHubbardHamiltonian N (T + Matrix.diagonal (fun x => U x / 2)) U
        - ((∑ x : Fin (N + 1), (U x : ℂ)) / 4) • (1 : ManyBodyOp (Fin (2 * N + 2))) :=
  symmetricAttractiveHubbardHamiltonian_eq_attractive_sub_smul N T U

/-- Pins **B2**, the Hamiltonian bridge: the Shiba conjugation of the symmetric repulsive
Hamiltonian equals the symmetric attractive Hamiltonian exactly (the `¼ΣU` shifts of the two sides
cancel). -/
example {A : Finset (Fin (N + 1))} {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hsymm : ∀ x y, T x y = T y x) (hbip : HoppingRespectsBipartition A T)
    (U : Fin (N + 1) → ℝ) :
    Matrix.conjTranspose (shibaSignedUnitary N (shibaSignFn A))
        * symmetricRepulsiveHubbardHamiltonian N T U
        * shibaSignedUnitary N (shibaSignFn A)
      = symmetricAttractiveHubbardHamiltonian N T U :=
  shibaSignedUnitary_conj_symmetricRepulsive_eq_symmetricAttractive hsymm hbip U

/-- Pins **P1** (de-privatized): the Euclidean expectation is homogeneous in the observable. -/
example (a : ℂ) (O : ManyBodyOp (Fin (2 * N + 2)))
    (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :
    euclideanExpectation (a • O) φ = a * euclideanExpectation O φ :=
  euclideanExpectation_smul a O φ

/-- Pins **P2** (de-privatized): the Euclidean expectation is additive in the observable. -/
example (O₁ O₂ : ManyBodyOp (Fin (2 * N + 2)))
    (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :
    euclideanExpectation (O₁ + O₂) φ
      = euclideanExpectation O₁ φ + euclideanExpectation O₂ φ :=
  euclideanExpectation_add O₁ O₂ φ

/-- Pins **P3** (de-privatized): Shiba transport of the Euclidean expectation. -/
example (O : ManyBodyOp (Fin (2 * N + 2)))
    (Ush : Matrix (Fin (2 * N + 2) → Fin 2) (Fin (2 * N + 2) → Fin 2) ℂ)
    (ψ φattr : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2))
    (hψ : ψ.ofLp = Ush.mulVec φattr.ofLp) :
    euclideanExpectation O ψ
      = euclideanExpectation (Matrix.conjTranspose Ush * O * Ush) φattr :=
  euclideanExpectation_shiba_conj O Ush ψ φattr hψ

/-- Pins **P4** (de-privatized): `⟨v| Aᴴ A |v⟩` is the (nonnegative real) squared norm of `A v`. -/
example (M : ManyBodyOp (Fin (2 * N + 2))) (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :
    euclideanExpectation (Matrix.conjTranspose M * M) φ
      = ((∑ j, Complex.normSq ((M.mulVec φ.ofLp) j) : ℝ) : ℂ) :=
  euclideanExpectation_conjTranspose_mul_self M φ

/-- Pins **G1**, the generic unitary-conjugation ground-state transport (design §2.1), at
abstract carrier `n`. Fails to elaborate unless `IsUniqueGroundStateOn.conj_unitary` exists with
exactly this two-sided-membership hypothesis list, and with the single unitarity hypothesis
`U Uᴴ = 1` (its companion `Uᴴ U = 1` being derivable on a square matrix). -/
example {n : Type*} [Fintype n] [DecidableEq n]
    {K K' : Submodule ℂ (EuclideanSpace ℂ n)}
    {Ugen H H' : Matrix n n ℂ} {E : ℝ} {φ : EuclideanSpace ℂ n}
    (hUUc : Ugen * Matrix.conjTranspose Ugen = 1)
    (hconj : Matrix.conjTranspose Ugen * H' * Ugen = H)
    (hfwd : ∀ v ∈ K, Matrix.toEuclideanLin Ugen v ∈ K')
    (hbwd : ∀ v ∈ K', Matrix.toEuclideanLin (Matrix.conjTranspose Ugen) v ∈ K)
    (hGS : LatticeSystem.Math.IsUniqueGroundStateOn K H E φ) :
    LatticeSystem.Math.IsUniqueGroundStateOn K' H' E (Matrix.toEuclideanLin Ugen φ) :=
  LatticeSystem.Math.IsUniqueGroundStateOn.conj_unitary hUUc hconj hfwd hbwd hGS

/-- Pins **S1**, the spin-algebra extraction: a null vector of the fermionic Casimir `Ŝ²` is a
null vector of `Ŝ³` (design §2.2, Tasaki Lemma A.11 route). -/
example {f : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (h : (fermionTotalSpinSquared N).mulVec f = 0) :
    (fermionTotalSpinZ N).mulVec f = 0 :=
  fermionTotalSpinZ_mulVec_eq_zero_of_fermionTotalSpinSquared_mulVec_eq_zero N h

/-- Sanity instance of **S1** at `N = 0`, `f = 0`: forces the `Fin (2 * 0 + 2)` instance path to
elaborate (design §5 item 3). -/
example : (fermionTotalSpinZ 0).mulVec (0 : (Fin (2 * 0 + 2) → Fin 2) → ℂ) = 0 :=
  fermionTotalSpinZ_mulVec_eq_zero_of_fermionTotalSpinSquared_mulVec_eq_zero 0
    (by rw [Matrix.mulVec_zero])

/-- Pins **T1**, the plain-attractive Shiba transport of `IsUniqueGroundStateOn` from the
`N̂ = Ne` electron-number sector to the `Ŝ³ = m` spin-`z` sector (design §2.3), energy slot
`E − (∑ x, U x) / 4`. -/
example (N Ne : ℕ) {A : Finset (Fin (N + 1))} {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hT_symm : ∀ x y, T x y = T y x) (hbip : HoppingRespectsBipartition A T)
    (U : Fin (N + 1) → ℝ) {E : ℝ} {φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hGS : IsUniqueGroundStateOn (electronNumberSectorEuclidean N Ne)
      (attractiveHubbardHamiltonian N (T + Matrix.diagonal (fun x => U x / 2)) U) E φ)
    (hsinglet : Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = 0) :
    ∃ ψ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
      ψ.ofLp = (shibaSignedUnitary N (shibaSignFn A)).mulVec φ.ofLp ∧
      IsUniqueGroundStateOn (spinZSectorEuclidean N (((Ne : ℂ) - ((N : ℂ) + 1)) / 2))
        (symmetricRepulsiveHubbardHamiltonian N T U)
        (E - (∑ x : Fin (N + 1), U x) / 4) ψ ∧
      Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) ψ = ((N : ℂ) + 1) • ψ :=
  shibaTransport_uniqueGroundStateOn_spinZSector N Ne hT_symm hbip U hGS hsinglet

/-- Pins **T2**, the symmetric-attractive-facing corollary (design §2.4): the same transport
starting from `symmetricAttractiveHubbardHamiltonian`, with energy slot **exactly** `E` (the
`¼ΣU` shifts on both sides cancel). -/
example (N Ne : ℕ) {A : Finset (Fin (N + 1))} {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hT_symm : ∀ x y, T x y = T y x) (hbip : HoppingRespectsBipartition A T)
    (U : Fin (N + 1) → ℝ) {E : ℝ} {φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hGS : IsUniqueGroundStateOn (electronNumberSectorEuclidean N Ne)
      (symmetricAttractiveHubbardHamiltonian N T U) E φ)
    (hsinglet : Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = 0) :
    ∃ ψ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
      ψ.ofLp = (shibaSignedUnitary N (shibaSignFn A)).mulVec φ.ofLp ∧
      IsUniqueGroundStateOn (spinZSectorEuclidean N (((Ne : ℂ) - ((N : ℂ) + 1)) / 2))
        (symmetricRepulsiveHubbardHamiltonian N T U) E ψ ∧
      Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) ψ = ((N : ℂ) + 1) • ψ :=
  shibaTransport_uniqueGroundStateOn_spinZSector_symmetricAttractive N Ne hT_symm hbip U hGS
    hsinglet

/-- **INV**: statement-invariance regression pin for `repulsiveSpinZSector_ground_unique`
(design §1.1). Restates its full existential type and discharges it by the theorem name, so a
future refactor (PR-2's corollary form) that reorders/adds a conjunct breaks this pin before it
can silently break the three positional call sites
(`LiebRepulsiveCorrelation.lean:144`, `LiebFerrimagnetismCenteredSector.lean:266`,
`LiebRepulsiveSectorBridgeFinal.lean:159`). -/
example (N Ne : ℕ)
    (hNe_even : Even Ne) (hNe_pos : 0 < Ne) (hNe_lt : Ne < 2 * (N + 1))
    {A : Finset (Fin (N + 1))} (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT_symm : ∀ x y, T x y = T y x) (hbip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU_pos : ∀ x, 0 < U x) :
    ∃ (E : ℝ) (φ φattr : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)),
      IsUniqueGroundStateOn
          (spinZSectorEuclidean N (((Ne : ℂ) - ((N : ℂ) + 1)) / 2))
          (symmetricRepulsiveHubbardHamiltonian N T U) E φ ∧
        φ.ofLp = (shibaSignedUnitary N (shibaSignFn A)).mulVec φattr.ofLp ∧
        (∀ x y : Fin (N + 1),
          0 < (euclideanExpectation (hubbardPairCorrelationOp N x y) φattr).re ∧
            (euclideanExpectation (hubbardPairCorrelationOp N x y) φattr).im = 0) ∧
        Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) φ = ((N : ℂ) + 1) • φ :=
  repulsiveSpinZSector_ground_unique N Ne hNe_even hNe_pos hNe_lt T hT_symm hbip hT_conn U hU_pos

/-! ## PR-3 (#5357): `k₀ → k` sector generalization + Casimir value (`LiebShenQiuSectorCasimir.lean`,
new module) -/

/-- Pins **C1**, the tower-exponent weight arithmetic (design §3 item 1): at tower exponent
`k := A.card - Ne / 2` (`hb`/`ha`/`hNe` are the side conditions `b ≤ Ne/2 ≤ a`, `Even Ne` that make
`k` land in `[0, L]`), the generalized-pinch weight `L/2 - k` equals the symmetric-attractive
Shiba transport's sector parameter `(Ne - (N+1))/2`. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (Ne : ℕ)
    (hb : 2 * (bipartitionComplement A).card ≤ Ne) (ha : Ne ≤ 2 * A.card) (hNe : Even Ne) :
    (sublatticeImbalance A : ℂ) / 2 - ((A.card - Ne / 2 : ℕ) : ℂ)
      = ((Ne : ℂ) - ((N : ℂ) + 1)) / 2 :=
  liebShenQiu_towerExponent_weight_eq N A Ne hb ha hNe

/-- Pins **C2**, the generalized pinch applied to the symmetric-attractive Shiba transport's
sector ground state `ψ` (design §3 item 2): under the Theorem 10.4 hypotheses (`hmin`/`hE₀`/`hcas`)
and PR-3's `(k, hk, hkm)` matching the transport's sector, `ψ` (unique ground state `hGS` at
half filling `hψN`) lies in the `(N+1)`-electron `E₀`-ground submodule. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT : ∀ i j, T i j = T j i) (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hmin : ∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) ≠ ⊥ → E₀.re ≤ E.re)
    (hE₀ : ((E₀.re : ℝ) : ℂ) = E₀)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w)
    (k : ℕ) (hk : k ≤ sublatticeImbalance A)
    {m : ℂ} (hkm : (sublatticeImbalance A : ℂ) / 2 - (k : ℂ) = m)
    {E : ℝ} {ψ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hGS : IsUniqueGroundStateOn (spinZSectorEuclidean N m)
      (symmetricRepulsiveHubbardHamiltonian N T U) E ψ)
    (hψN : Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) ψ = ((N : ℂ) + 1) • ψ) :
    ψ.ofLp ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) :=
  liebShenQiu_sectorGround_mem_halfFillingGround N A T hT U E₀ (hmin := hmin) (hE₀ := hE₀)
    (hcas := hcas) (hw0 := hw0) (hwG := hwG) (hz := hz) (k := k) (hk := hk) (hkm := hkm)
    (hGS := hGS) (hψN := hψN)

/-- Pins **C3**, the Casimir value on that same sector ground state (design §3 item 3): under the
full Theorem 10.5 model hypotheses (`hbip`, `hT_conn`, `hU`) and PR-3's `(k, hk, hkm)`, `ψ` is an
eigenvector of the total-spin Casimir `Ŝ²` with eigenvalue `liebRepulsiveSpinCasimir A =
S₀(S₀+1)`, `S₀ := L/2`. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT : ∀ i j, T i j = T j i) (hbip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU : ∀ x, 0 < U x)
    (k : ℕ) (hk : k ≤ sublatticeImbalance A)
    {m : ℂ} (hkm : (sublatticeImbalance A : ℂ) / 2 - (k : ℂ) = m)
    {E : ℝ} {ψ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hGS : IsUniqueGroundStateOn (spinZSectorEuclidean N m)
      (symmetricRepulsiveHubbardHamiltonian N T U) E ψ)
    (hψN : Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) ψ = ((N : ℂ) + 1) • ψ) :
    (fermionTotalSpinSquared N).mulVec ψ.ofLp = liebRepulsiveSpinCasimir A • ψ.ofLp :=
  liebShenQiu_casimir_eq N A T hT hbip hT_conn U hU (k := k) (hk := hk) (hkm := hkm)
    (hGS := hGS) (hψN := hψN)

end LatticeSystem.Tests.LiebShenQiuShibaBridge
