import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismCenteredSector

/-!
# §10.2.3 Theorem 10.6 — centered sector ↔ Theorem 10.5 bridge (specification)

Specification suite for
`LatticeSystem/Fermion/JordanWigner/Hubbard/LiebFerrimagnetismCenteredSector.lean` (PR-6 of the
Theorem 10.6 discharge arc, issue #5347). The `example`s pin down the exact signatures of the
five public declarations `T1`–`T6` (`T2` is `private`, so it is not pinned here) of
this arc's PR-6 design: the ground-energy realification
`T1`, the sector/ground energy match `T3`, the centered tower member's collinearity with the
sector's unique ground state `T4`, the transverse-sign transport `T5`, and the existential capstone
`T6` (consuming PR-5's `liebRepulsive_ground_exists_topWeight`). Mirrors the specification style of
`Tests/LiebFerrimagnetismGroundTower.lean`.

**PR-3 of the Theorem 10.8 discharge arc (issue #5357) generalizes `T3`'s underlying
declaration** `liebRepulsive_sectorGroundEnergy_eq_groundEnergy` from the hard-wired centered
exponent `k₀ = sublatticeImbalance A / 2` to an arbitrary `(k : ℕ) (hk : k ≤ sublatticeImbalance A)`
with the sector weight supplied via a matching hypothesis `{m : ℂ}
(hkm : (sublatticeImbalance A : ℂ) / 2 - (k : ℂ) = m)`, and de-privatizes
`liebRepulsive_centeredWeight_eq` (design `.self-local/docs/theorem-10-8-pr3-design.md` §2). The
`T3` pin below is updated to the generalized signature, instantiated at `k := L/2,
hkm := liebRepulsive_centeredWeight_eq A` so that it remains a byte-for-byte regression check of
the original centered statement (design §2.1/§8 "Regression").

Carrier throughout: `H := symmetricRepulsiveHubbardHamiltonian N T U`,
`G := hubbardGroundSubmoduleAtElectronNumber H E₀ (N+1)`, `k₀ := sublatticeImbalance A / 2`
(ℕ division), `mCentered := ((N + 1 + sublatticeImbalance A % 2 : ℕ : ℂ) - ((N : ℂ) + 1)) / 2` the
centered spin-`z` sector parameter that Theorem 10.5's `spinZSectorEuclidean` consumes. Each pin
records the hypothesis set the design fixes, so a later edit cannot silently widen it: `T3`–`T6`
take `hmin`/`hcas` in the same submodule-wide shape Theorem 10.4 exports (not the pointwise-weakest
hypothesis), and `T5`/`T6` need the full Theorem 10.5 model hypotheses (`hbip`, `hT_conn`, `hU`)
plus the design's single extra side condition `1 ≤ N` (no `B.Nonempty` hypothesis).

The closing section pins the centered-weight arithmetic that the design identifies as the only new
mathematics of the PR (design §2): `L % 2 = (N+1) % 2` (`N = 1`, two instantiations) and `Ne₀`'s
side conditions (`Even`, `0 < Ne₀ < 2(N+1)`) at `N = 1`, proved directly from
`bipartitionComplement_card_add` + `omega` without depending on the (private) `P1`.
-/

namespace LatticeSystem.Tests.LiebFerrimagnetismCenteredSector

open Matrix Module LatticeSystem.Fermion LatticeSystem.Quantum LatticeSystem.Math

/-! ## `T1` — realification of the ground energy -/

/-- **`T1`: ground energy is real.** If the `(N+1)`-electron ground submodule `G` of
`symmetricRepulsiveHubbardHamiltonian N T U` at `E₀` is nonzero, `E₀` is the complex cast of its own
real part: `((E₀.re : ℝ) : ℂ) = E₀`. Route (design §3 `T1`): Hermiticity
(`symmetricRepulsiveHubbardHamiltonian_isHermitian`) + `isHermitian_mulVec_eigenvalue_eq_ofReal`. -/
example (N : ℕ) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : ∀ i j, T i j = T j i)
    (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hne : hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) ≠ ⊥) :
    ((E₀.re : ℝ) : ℂ) = E₀ :=
  liebRepulsive_groundEnergy_eq_ofReal N T hT U E₀ (hne := hne)

/-! ## `T3` — the centered-sector ground energy equals the sector-agnostic ground energy -/

/-- **`T3`: sector ground energy = ground energy (generalized, PR-3 of #5357).** The unique ground
energy `E` of `H` on the spin-`z` sector `Ŝ³ = m` at an arbitrary tower exponent
`k ≤ L := sublatticeImbalance A` (matched to `m` via `hkm`) equals `E₀.re`, the real part of the
sector-agnostic `(N+1)`-electron ground energy — a two-sided pinch (design
`.self-local/docs/theorem-10-8-pr3-design.md` §2.1): `E₀.re ≤ E` from `φ`'s half-filling number
eigenvalue `hφN` transported through `mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul` and `hmin`;
`E ≤ E₀.re` from the `k`-th tower member `(Ŝ⁻_tot)^k w` witnessing `IsGroundEigenvalueOn`'s
minimality clause. Instantiated here at `k := L/2`, `hkm := liebRepulsive_centeredWeight_eq A` as a
byte-for-byte regression check of the original centered `T3` statement. -/
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
    {E : ℝ} {φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hGS : IsUniqueGroundStateOn
      (spinZSectorEuclidean N
        ((((N + 1 + sublatticeImbalance A % 2 : ℕ) : ℂ) - ((N : ℂ) + 1)) / 2))
      (symmetricRepulsiveHubbardHamiltonian N T U) E φ)
    (hφN : Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) φ = ((N : ℂ) + 1) • φ) :
    E = E₀.re :=
  liebRepulsive_sectorGroundEnergy_eq_groundEnergy N A T hT U E₀ (hmin := hmin) (hE₀ := hE₀)
    (hcas := hcas) (hw0 := hw0) (hwG := hwG) (hz := hz)
    (k := sublatticeImbalance A / 2) (hk := Nat.div_le_self _ _)
    (hkm := liebRepulsive_centeredWeight_eq A)
    (hGS := hGS) (hφN := hφN)

/-! ## `T4` — the centered tower member is a scalar multiple of the sector's unique ground state -/

/-- **`T4`: centered tower ∼ sector ground state.** Under the `T3` hypotheses, the centered tower
member `(Ŝ⁻_tot)^{k₀} w` (`k₀ := L/2`) equals `c • φ` for some nonzero `c : ℂ`: `T3`'s energy match
feeds `IsUniqueGroundStateOn`'s uniqueness clause (`DegeneratePerturbation.lean:287-288`), and
`c ≠ 0` follows from PR-5's `liebRepulsive_ground_tower_ne_zero` (design §3 `T4`). -/
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
    {E : ℝ} {φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hGS : IsUniqueGroundStateOn
      (spinZSectorEuclidean N
        ((((N + 1 + sublatticeImbalance A % 2 : ℕ) : ℂ) - ((N : ℂ) + 1)) / 2))
      (symmetricRepulsiveHubbardHamiltonian N T U) E φ)
    (hφN : Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) φ = ((N : ℂ) + 1) • φ) :
    ∃ c : ℂ, c ≠ 0 ∧
      (WithLp.toLp 2 (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)
          : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) = c • φ :=
  liebRepulsive_centered_eq_smul_sectorGround N A T hT U E₀ (hmin := hmin) (hE₀ := hE₀)
    (hcas := hcas) (hw0 := hw0) (hwG := hwG) (hz := hz) (hGS := hGS) (hφN := hφN)

/-! ## `T5` — the transverse-sign transport onto the centered tower member -/

/-- **`T5`: centered transverse sign.** Under the full Theorem 10.5 model hypotheses (`hbip`,
`hT_conn`, `hU`) plus the design's single extra side condition `1 ≤ N`, the transverse spin
correlation evaluated on the centered tower member `(Ŝ⁻_tot)^{k₀} w` has zero imaginary part and the
same same-sublattice / different-sublattice sign pattern as Theorem 10.5, transported through `T4`
(design §3 `T5`). -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT : ∀ i j, T i j = T j i) (hbip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU : ∀ x, 0 < U x) (hN : 1 ≤ N) (E₀ : ℂ)
    (hne : hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) ≠ ⊥)
    (hmin : ∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) ≠ ⊥ → E₀.re ≤ E.re)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w) :
    ∀ x y : Fin (N + 1),
      (vectorExpectation (fermionSpinTransverse N x y)
          (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)).im = 0 ∧
        (SameSublattice A x y →
            0 < (vectorExpectation (fermionSpinTransverse N x y)
              (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)).re) ∧
          (¬ SameSublattice A x y →
            (vectorExpectation (fermionSpinTransverse N x y)
              (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)).re < 0) :=
  liebRepulsive_centered_transverse_sign N A T hT hbip hT_conn U hU hN E₀ (hne := hne)
    (hmin := hmin) (hcas := hcas) (hw0 := hw0) (hwG := hwG) (hz := hz)

/-! ## `T6` — existential capstone -/

/-- **`T6`: existential centered transverse sign.** Combining PR-5's
`liebRepulsive_ground_exists_topWeight` with `T1` and `T5`, the `(N+1)`-electron ground submodule
`G` (assumed nonzero) contains a top-weight vector `w` whose centered tower member carries the `T5`
transverse-sign pattern — the shape PR-7 consumes for the tower-ratio argument, so the *same*
top-weight `w` witnesses both the weight equation and the sign pattern (design §3 `T6`). -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT : ∀ i j, T i j = T j i) (hbip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU : ∀ x, 0 < U x) (hN : 1 ≤ N) (E₀ : ℂ)
    (hne : hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) ≠ ⊥)
    (hmin : ∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) ≠ ⊥ → E₀.re ≤ E.re)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v) :
    ∃ w : (Fin (2 * N + 2) → Fin 2) → ℂ, w ≠ 0 ∧
      w ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) ∧
      (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w ∧
      ∀ x y : Fin (N + 1),
        (vectorExpectation (fermionSpinTransverse N x y)
            (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)).im = 0 ∧
          (SameSublattice A x y →
              0 < (vectorExpectation (fermionSpinTransverse N x y)
                (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)).re) ∧
            (¬ SameSublattice A x y →
              (vectorExpectation (fermionSpinTransverse N x y)
                (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)).re < 0) :=
  liebRepulsive_exists_centered_transverse_sign N A T hT hbip hT_conn U hU hN E₀ (hne := hne)
    (hmin := hmin) (hcas := hcas)

/-! ## Centered-weight arithmetic sanity checks (design §2, independent of `P1`/`P2`) -/

/-- **Parity `L % 2 = (N+1) % 2` at `N = 1`, `A = univ` (`L = 2`).** The balanced bipartition of
`Fin 2` has `|A| = 2`, `|B| = 0`, `L = 2`, and `L % 2 = 0 = (1 + 1) % 2`. -/
example :
    sublatticeImbalance (Finset.univ : Finset (Fin (1 + 1))) % 2 = (1 + 1) % 2 := by
  have hcard := bipartitionComplement_card_add 1 (Finset.univ : Finset (Fin (1 + 1)))
  have hA : (Finset.univ : Finset (Fin (1 + 1))).card = 2 := by simp
  rw [sublatticeImbalance]
  omega

/-- **Parity `L % 2 = (N+1) % 2` at `N = 1`, `A = {0}` (`L = 0`).** The singleton sublattice
`|A| = 1`, `|B| = 1`, `L = 0`, and `L % 2 = 0 = (1 + 1) % 2`. -/
example :
    sublatticeImbalance ({0} : Finset (Fin (1 + 1))) % 2 = (1 + 1) % 2 := by
  have hcard := bipartitionComplement_card_add 1 ({0} : Finset (Fin (1 + 1)))
  have hA : ({0} : Finset (Fin (1 + 1))).card = 1 := by simp
  rw [sublatticeImbalance]
  omega

/-- **`Ne₀` side conditions at `N = 1`, `A = univ` (`L = 2`, `Ne₀ = N + 1 + L % 2 = 2`).** `Ne₀` is
even, positive, and strictly below `2(N+1) = 4`: the `L % 2 = 0` branch of the design's parity
split, which needs no extra hypothesis beyond the arithmetic itself. -/
example :
    Even (1 + 1 + sublatticeImbalance (Finset.univ : Finset (Fin (1 + 1))) % 2) ∧
      0 < 1 + 1 + sublatticeImbalance (Finset.univ : Finset (Fin (1 + 1))) % 2 ∧
      1 + 1 + sublatticeImbalance (Finset.univ : Finset (Fin (1 + 1))) % 2 < 2 * (1 + 1) := by
  have hcard := bipartitionComplement_card_add 1 (Finset.univ : Finset (Fin (1 + 1)))
  have hA : (Finset.univ : Finset (Fin (1 + 1))).card = 2 := by simp
  have himb : sublatticeImbalance (Finset.univ : Finset (Fin (1 + 1))) = 2 := by
    rw [sublatticeImbalance]; omega
  rw [himb, Nat.even_iff]
  omega

/-- **`Ne₀` side conditions at `N = 2`, `A = univ` (`L = 3`, odd), the design's other parity
branch.** `|A| = 3`, `|B| = 0`, so `L = 3`, `L % 2 = 1`, `Ne₀ = N + 1 + L % 2 = 4`, which is even,
positive, and strictly below `2(N + 1) = 6` — the `1 ≤ N` side condition the design claims suffices
for the odd-`L` branch (design §2, `N = 0` is the excluded degenerate boundary `Ne₀ = 2(N+1)`). -/
example :
    Even (2 + 1 + sublatticeImbalance (Finset.univ : Finset (Fin (2 + 1))) % 2) ∧
      0 < 2 + 1 + sublatticeImbalance (Finset.univ : Finset (Fin (2 + 1))) % 2 ∧
      2 + 1 + sublatticeImbalance (Finset.univ : Finset (Fin (2 + 1))) % 2 < 2 * (2 + 1) := by
  have hcard := bipartitionComplement_card_add 2 (Finset.univ : Finset (Fin (2 + 1)))
  have hA : (Finset.univ : Finset (Fin (2 + 1))).card = 3 := by simp
  have himb : sublatticeImbalance (Finset.univ : Finset (Fin (2 + 1))) = 3 := by
    rw [sublatticeImbalance]; omega
  rw [himb, Nat.even_iff]
  omega

end LatticeSystem.Tests.LiebFerrimagnetismCenteredSector
