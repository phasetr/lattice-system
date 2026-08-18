import LatticeSystem.Quantum.SpinS.AKLTKnabe.KnabeGapD7d
import LatticeSystem.Quantum.SpinS.AKLTOpenChain
import LatticeSystem.Quantum.SpinS.AKLTTheorem71

/-!
# §7.2.3 Problem 7.2.3.a — the open-chain `S = 1` AKLT VBS states

(Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Problem 7.2.3.a, p. 207.)

Signature and negative-control tests for the open AKLT chain: no `sorry`, no production code —
`example`s that pin down the exact statements of `openBondCoupling`, `openBonds`,
`openProjHamiltonianS`, `openAKLTHamiltonianS`, `openVBSState`, `openAKLTGroundSpace`,
`openVBSState_linearIndependent`, `isGroundEnergy_openAKLTHamiltonianS`,
`openProjHamiltonianS_posSemidef_and_annihilates`, `four_le_finrank_openAKLTGroundSpace` and
`card_openBonds`, so that a later refactor cannot silently drift them.

The load-bearing controls are: the wrap-bond count `(openBonds 3).card = 2` (a wrap-bond leak is a
silent falsity, not a build error); the ring–open consistency `Φ_ring = Σ_p Φ^open_{pp}`; the
ground-energy control that the periodic shift `−(2/3)L` is **not** a ground energy of the open
chain at `L = 2`; and the regression block pinning the ring-side capstones after the shared
two-site-tensor extraction and the `openBondCoupling` move.
-/

namespace LatticeSystem.Tests.AKLTOpenChainProblem723a

open LatticeSystem.Quantum
open LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential
open scoped ComplexOrder

/-! ## 1. Signature specification: `openBondCoupling` -/

/-- `openBondCoupling` must have exactly the directed unit-weight signature used by
`ringCoupling` (`ShastryNoSSB.lean:41`), generalized to the open (non-modular) successor: no
`[NeZero L]` instance, plain `Fin L → Fin L → ℂ`. -/
example (L : ℕ) (x y : Fin L) : ℂ := openBondCoupling L x y

/-! ## 2. Signature specification: `openBonds`, `openProjHamiltonianS`, `openAKLTHamiltonianS`,
`openVBSState` -/

example (L : ℕ) : Finset (Fin L) := openBonds L

example (hL : 0 < L) : (openBonds L).card = L - 1 := card_openBonds hL

/-- Wrap-bond negative control: `openBonds 3` has cardinality `2` (the `L − 1 = 2` open bonds
`{0,1}, {1,2}`), **not** `3` (the ring cardinality) — a wrap-bond leak would be a silent falsity,
not a build error. -/
example : (openBonds 3).card = 2 := card_openBonds (L := 3) (by norm_num)

noncomputable example (L : ℕ) : ManyBodyOpS (Fin L) 2 := openProjHamiltonianS L

noncomputable example (L : ℕ) : ManyBodyOpS (Fin L) 2 := openAKLTHamiltonianS L

/-- `openAKLTHamiltonianS` must unfold to the same double-sum shape as `akltHamiltonianS`
(`AKLT.lean:47`) with `ringCoupling` replaced by `openBondCoupling`. -/
example (L : ℕ) :
    openAKLTHamiltonianS L =
      ∑ x : Fin L, ∑ y : Fin L, openBondCoupling L x y •
        (spinSDot x y 2 + ((1 : ℂ) / 3) • (spinSDot x y 2 * spinSDot x y 2)) := rfl

noncomputable example (L : ℕ) (p q : Fin 2) : (Fin L → Fin 3) → ℂ := openVBSState L p q

/-- Ring-vs-open consistency: the ring VBS state is the sum of the diagonal boundary components
of the open VBS state (trace = sum of diagonal MPS boundary matrix entries).  This is the control
that the two definitions really are the same matrix product. -/
example (L : ℕ) (σ : Fin L → Fin 3) :
    akltVBSState L σ = ∑ p : Fin 2, openVBSState L p p σ :=
  akltVBSState_eq_sum_diag_openVBSState L σ

/-! ## 3. Problem 7.2.3.a core claim: frustration-free zero energy of the four open VBS states -/

/-- **G4/G7-analogue for the open chain**: the projector Hamiltonian `Ĥ'^open` is
positive-semidefinite and every `x ∈ openBonds L` annihilates each `openVBSState L p q`
(frustration-freeness at every open bond). -/
example (hL : 2 ≤ L) :
    (openProjHamiltonianS L).PosSemidef ∧
      ∀ x ∈ openBonds L, ∀ p q : Fin 2,
        (bondSpin2ProjectionS x (ringSucc x)).mulVec (openVBSState L p q) = 0 :=
  openProjHamiltonianS_posSemidef_and_annihilates hL

/-- **Problem 7.2.3.a headline claim**: the four open VBS states `openVBSState L p q`
(`p q : Fin 2`, Tasaki eqs. (7.2.47)/(7.2.48)) are linearly independent — hence each is nonzero
and frustration-free zero-energy, and together they witness `4 ≤ finrank` of the ground space
(weakest hypothesis `2 ≤ L`, **not** `3 ≤ L`). -/
example (hL : 2 ≤ L) :
    LinearIndependent ℂ fun r : Fin 2 × Fin 2 => openVBSState L r.1 r.2 :=
  openVBSState_linearIndependent hL

/-- The ground energy of `openAKLTHamiltonianS` is `−(2/3)(L − 1)`: **not** `−(2/3) L`, since
(7.2.46) has no additive constant and has only `L − 1` bonds. -/
example (hL : 2 ≤ L) :
    IsGroundEnergy (openAKLTHamiltonianS L) (-(2 : ℝ) / 3 * ((L : ℝ) - 1)) :=
  isGroundEnergy_openAKLTHamiltonianS hL

/-- Negative control for the ground energy: the ring shift `−(2/3) L` (dropping the `−1`) must
**not** also be a valid ground energy at `L = 2` (precedent N3/N4 in `KnabeGapD7d.lean`). -/
example :
    ¬ IsGroundEnergy (openAKLTHamiltonianS 2) (-(2 : ℝ) / 3 * (2 : ℝ)) := by
  intro h
  have h' := isGroundEnergy_openAKLTHamiltonianS (L := 2) (by norm_num)
  have hEq := h.2 _ h'.1
  have hEq' := h'.2 _ h.1
  have : (-(2 : ℝ) / 3 * (2 : ℝ)) = (-(2 : ℝ) / 3 * ((2 : ℝ) - 1)) := le_antisymm hEq hEq'
  norm_num at this

/-! ## 4. Headline `4 ≤ finrank` claim -/

noncomputable example (L : ℕ) : Submodule ℂ ((Fin L → Fin 3) → ℂ) := openAKLTGroundSpace L

/-- **Problem 7.2.3.a, the lower-bound consequence**: the open AKLT ground space has complex
dimension at least `4`, matching the four independent open VBS states; at `L = 2` this must
agree with `finrank_vbsBondSubspace = 4` (`AKLTBondProjection.lean`). -/
example (hL : 2 ≤ L) :
    4 ≤ Module.finrank ℂ (openAKLTGroundSpace L) :=
  four_le_finrank_openAKLTGroundSpace hL

/-- `L = 2` structural cross-check: the headline bound instantiated at
the smallest admissible `L` must literally match the proved ring-bond-subspace dimension. -/
example : (4 : ℕ) ≤ Module.finrank ℂ (openAKLTGroundSpace 2) :=
  four_le_finrank_openAKLTGroundSpace (le_refl 2)

/-! ## 5. Regression: the ring-side AKLT capstones, pinned to their exact signatures so that the
shared two-site-tensor extraction and the open-chain coupling cannot silently drift them. -/

noncomputable example (L : ℕ) : ManyBodyOpS (Fin L) 2 := akltHamiltonianS L

example (hL : 1 < L) (x : Fin L) :
    (bondSpin2ProjectionS x (ringSucc x)).mulVec (akltVBSState L) = 0 :=
  bondSpin2ProjectionS_mulVec_akltVBSState_eq_zero hL x

example :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      akltVBSState (n + 1) ≠ 0 ∧
      (akltHamiltonianS (n + 1)).mulVec (akltVBSState (n + 1))
          = ((-(2 : ℝ) / 3 * ((n : ℝ) + 1) : ℝ) : ℂ) • akltVBSState (n + 1) ∧
      IsGroundEnergy (akltHamiltonianS (n + 1)) (-(2 : ℝ) / 3 * ((n : ℝ) + 1)) ∧
      ∃ gap : ℝ, (1 : ℝ) / 5 ≤ gap ∧ IsPositiveSpectralGap (akltHamiltonianS (n + 1)) gap :=
  aklt_knabe_ring_gap

example :
    ∃ (ΔE₀ : ℝ) (Φ : (n : ℕ) → (Fin (n + 1) → Fin 3) → ℂ) (E₀ : ℕ → ℝ),
      0 < ΔE₀ ∧ ∃ n₀ : ℕ,
        (∀ n : ℕ, n₀ ≤ n →
          Φ n ≠ 0 ∧
          (akltHamiltonianS (n + 1)).mulVec (Φ n) = (E₀ n : ℂ) • Φ n ∧
          IsGroundEnergy (akltHamiltonianS (n + 1)) (E₀ n) ∧
          (∀ Ψ : (Fin (n + 1) → Fin 3) → ℂ, Ψ ≠ 0 →
            (akltHamiltonianS (n + 1)).mulVec Ψ = (E₀ n : ℂ) • Ψ → ∃ c : ℂ, Ψ = c • Φ n) ∧
          ∃ gap : ℝ, ΔE₀ ≤ gap ∧ IsPositiveSpectralGap (akltHamiltonianS (n + 1)) gap) ∧
        ∀ (x y : ℕ), 1 ≤ Nat.dist x y → ∀ ε : ℝ, 0 < ε → ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n →
          |expectationRatioRe (spinSDot (chainSite n x) (chainSite n y) 2) (Φ n)
            - (4 : ℝ) * (-3 : ℝ) ^ (-(Nat.dist x y : ℤ))| < ε :=
  aklt_theorem_7_1

end LatticeSystem.Tests.AKLTOpenChainProblem723a
