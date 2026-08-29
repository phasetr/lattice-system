import LatticeSystem.Quantum.IsingLowEnergyProblem33aSpectrum

/-!
# Test coverage for Tasaki Problem 3.3.a — the low-energy `2L` matrix (TSK-005)

Fixtures for the low-energy analysis of the open-chain quantum Ising Hamiltonian
(`quantumIsingHamiltonian N (1/4) (lam/2)`, `S = σ/2` convention), Tasaki, *Physics and
Mathematics of Quantum Many-Body Systems*, Problem 3.3.a, statement p. 59, solution pp. 498-501,
eqs. (S.24)-(S.41).

The first block of fixtures covers the configuration-basis matrix-element API of
`quantumIsingHamiltonian` itself (`LatticeSystem/Quantum/IsingChainMatrixElements.lean`): the
signature pins state each of `quantumIsingHamiltonian_mulVec_apply`,
`quantumIsingHamiltonian_apply_diag`, `quantumIsingHamiltonian_apply_siteFlip` and
`quantumIsingHamiltonian_apply_eq_zero` in full and discharge it by the lemma itself. The numeric
fixtures evaluate the diagonal and single-flip entries at `L = 2` and `L = 3` through those
lemmas, pinning the concrete values `-(L-1)/4` (aligned), `0` (single kink) and `-h`.

The second block covers the `2L`-dimensional low-energy basis and its compression
(`LatticeSystem/Quantum/IsingLowEnergyProblem33a.lean`): `lowEnergyConfig`, its book-form
descriptions and injectivity, its adjacency structure under `siteFlipAt`, and the resulting
matrix identity `lowEnergyMatrix = E_GS^(0) • 1 + tightBindingRing`. The ring of (S.30) is a ring
of *basis labels* (`ZMod (2 * (N + 1))`), not of lattice sites — the lattice stays open. The
numeric fixtures at `L = 2` and `L = 3` evaluate individual entries of that identity.
-/

namespace LatticeSystem.Tests.Problem33aLowEnergy

open LatticeSystem.Quantum
open Matrix

/-! ## Signature pins for the four matrix-element lemmas -/

/-- **A1 signature pin.** `quantumIsingHamiltonian_mulVec_apply` expands `(H *ᵥ v) τ` into the
signed bond sum (`+1` on an aligned bond, `-1` across a domain wall) times `v τ`, plus the field
term summed over `siteFlipAt`. This is the base identity A2-A4 are derived from. -/
example (N : ℕ) (J h : ℝ) (v : (Fin (N + 1) → Fin 2) → ℂ) (τ : Fin (N + 1) → Fin 2) :
    (quantumIsingHamiltonian N J h *ᵥ v) τ =
      -(J : ℂ) * (∑ i : Fin N, if τ i.castSucc = τ i.succ then (1 : ℂ) else -1) * v τ
        - (h : ℂ) * ∑ i : Fin (N + 1), v (siteFlipAt τ i) :=
  quantumIsingHamiltonian_mulVec_apply N J h v τ

/-- **A2 signature pin.** `quantumIsingHamiltonian_apply_diag` gives the diagonal entry
`⟨Φ_τ|H|Φ_τ⟩` as `-J` times the signed bond sum (`+1` on an aligned bond, `-1` across a domain
wall), with no field-term contribution (a flipped configuration never equals the original). -/
example (N : ℕ) (J h : ℝ) (τ : Fin (N + 1) → Fin 2) :
    quantumIsingHamiltonian N J h τ τ =
      -(J : ℂ) * ∑ i : Fin N, (if τ i.castSucc = τ i.succ then (1 : ℂ) else -1) :=
  quantumIsingHamiltonian_apply_diag N J h τ

/-- **A3 signature pin.** `quantumIsingHamiltonian_apply_siteFlip` gives the matrix element
between a configuration and its single-site flip: exactly `-h`, independent of `J` and of the
flipped site. -/
example (N : ℕ) (J h : ℝ) (τ : Fin (N + 1) → Fin 2) (x : Fin (N + 1)) :
    quantumIsingHamiltonian N J h (siteFlipAt τ x) τ = -(h : ℂ) :=
  quantumIsingHamiltonian_apply_siteFlip N J h τ x

/-- **A4 signature pin.** `quantumIsingHamiltonian_apply_eq_zero` is the source's "all other
matrix elements are vanishing": distinct configurations that are also not a single-site flip of
one another have a zero matrix element. -/
example (N : ℕ) (J h : ℝ) (σ τ : Fin (N + 1) → Fin 2) (h₁ : σ ≠ τ)
    (h₂ : ∀ x, σ ≠ siteFlipAt τ x) :
    quantumIsingHamiltonian N J h σ τ = 0 :=
  quantumIsingHamiltonian_apply_eq_zero N J h σ τ h₁ h₂

/-! ## Numeric fixtures at `L = 2` (`N = 1`) -/

/-- **Aligned diagonal entry (A2 at `L = 2`).** The all-down configuration is aligned across
the single bond of the two-site *open* chain — one aligned bond and no domain wall — so the
signed bond sum is `+1` and the diagonal entry is `-J = -1/4 = -(L-1)/4`, Tasaki eq. (S.24).
Corresponds to design §8 fixture 3, adapted to the matrix-element API. -/
example :
    quantumIsingHamiltonian 1 (1 / 4 : ℝ) (1 : ℝ) (fun _ => (1 : Fin 2)) (fun _ => (1 : Fin 2))
      = -1 / 4 := by
  rw [quantumIsingHamiltonian_apply_diag 1 (1 / 4) 1 (fun _ => 1)]
  norm_num

/-- **Field-term value (A3 at `L = 2`).** The matrix element between the all-down configuration
and its site-`0` flip is exactly `-h`; here `h = 1`. -/
example :
    quantumIsingHamiltonian 1 (1 / 4 : ℝ) (1 : ℝ) (siteFlipAt (fun _ => (1 : Fin 2)) 0)
        (fun _ => (1 : Fin 2))
      = -1 :=
  quantumIsingHamiltonian_apply_siteFlip 1 (1 / 4) 1 (fun _ => 1) 0

/-- **Vanishing at distance `2` (A4 at `L = 2`).** The all-up and all-down configurations differ
at both sites of the two-site chain, so neither is the other nor a single-site flip of the other;
their matrix element is `0`. Matches design §8 fixture 5's second clause
(`lowEnergyMatrix 1 lam 0 2 = 0`) at the matrix-element level, one PR earlier. -/
example :
    quantumIsingHamiltonian 1 (1 / 4 : ℝ) (1 : ℝ) (fun _ => (0 : Fin 2)) (fun _ => (1 : Fin 2))
      = 0 :=
  quantumIsingHamiltonian_apply_eq_zero 1 (1 / 4) 1 (fun _ => 0) (fun _ => 1) (by decide)
    (by decide)

/-! ## Numeric fixtures at `L = 3` (`N = 2`) -/

/-- **Bond counting (A2 at `L = 3`).** The all-down configuration is aligned across both bonds of
the three-site open chain, so the signed bond sum is `+2` and the diagonal entry is
`-2J = -1/2 = -(L-1)/4`, Tasaki eq. (S.24). -/
example :
    quantumIsingHamiltonian 2 (1 / 4 : ℝ) (1 : ℝ) (fun _ => (1 : Fin 2)) (fun _ => (1 : Fin 2))
      = -1 / 2 := by
  rw [quantumIsingHamiltonian_apply_diag 2 (1 / 4) 1 (fun _ => 1)]
  norm_num

/-- **Single kink (A2 at `L = 3`).** Flipping site `0` of the all-down configuration creates one
domain wall and leaves one aligned bond, so the signed bond sum is `-1 + 1 = 0` and the diagonal
entry is `0`. This is Tasaki eq. (S.25), whose value `E_GS^(0) + 1/2 = -(L-1)/4 + 1/2` is `0`
exactly at `L = 3`. -/
example :
    quantumIsingHamiltonian 2 (1 / 4 : ℝ) (1 : ℝ) (siteFlipAt (fun _ => (1 : Fin 2)) 0)
        (siteFlipAt (fun _ => (1 : Fin 2)) 0)
      = 0 := by
  rw [quantumIsingHamiltonian_apply_diag 2 (1 / 4) 1 (siteFlipAt (fun _ => (1 : Fin 2)) 0),
    Fin.sum_univ_two]
  norm_num [siteFlipAt, Function.update_apply, Fin.ext_iff]

/-! ## Signature pins for the `2L`-basis and compressed-matrix API -/

/-- **B3 signature pin.** `lowEnergyConfig_natCast_le` gives the book form of the low-energy
configuration at a label `j ≤ L` cast from `ℕ`: site `x` is up (`Fin 2` value `0`) iff `x.val < j`.
At `j = 0` this is the all-down `|Φ↓⟩`; at `j = L` it is the all-up `|Φ↑⟩`; for `0 < j < L` it is
the single-domain-wall state `|Φ_j^↑↓⟩`. -/
example (N : ℕ) (j : ℕ) (hj : j ≤ N + 1) :
    lowEnergyConfig N (j : ZMod (2 * (N + 1))) = fun x => if x.val < j then (0 : Fin 2) else 1 :=
  lowEnergyConfig_natCast_le N j hj

/-- **B4 signature pin.** `lowEnergyConfig_natCast_add` gives the book form of the low-energy
configuration at a label `L + m` (`0 ≤ m ≤ L`): site `x` is down (`Fin 2` value `1`) iff
`x.val < m`, i.e. `|Φ_m^↓↑⟩`, the mirror of B3. Parametrizing by `m` rather than `j.val - L` keeps
`ℕ`-subtraction out of the statement. -/
example (N : ℕ) (m : ℕ) (hm : m ≤ N + 1) :
    lowEnergyConfig N (((N + 1) + m : ℕ) : ZMod (2 * (N + 1)))
      = fun x => if x.val < m then (1 : Fin 2) else 0 :=
  lowEnergyConfig_natCast_add N m hm

/-- **B5/C1 signature pin.** `lowEnergyConfig_injective` records that the `2L` labels give `2L`
pairwise distinct configurations — the low-energy space genuinely has the dimension the problem
statement claims. -/
example (N : ℕ) : Function.Injective (lowEnergyConfig N) :=
  lowEnergyConfig_injective N

/-- **B6 signature pin.** `lowEnergyConfig_succ_eq_siteFlipAt` says that advancing the ring label
by one step is exactly a single-site flip at `wallSite N a`, the unique domain-wall site of
`lowEnergyConfig N a`. This is what lets the off-diagonal entries of `lowEnergyMatrix` between
adjacent labels be read off `quantumIsingHamiltonian_apply_siteFlip` (A3) rather than a fresh
computation. The pin also records that the statement carries no size hypothesis. -/
example (N : ℕ) (a : ZMod (2 * (N + 1))) :
    lowEnergyConfig N (a + 1) = siteFlipAt (lowEnergyConfig N a) (wallSite N a) :=
  lowEnergyConfig_succ_eq_siteFlipAt N a

/-- **B6 at `L = 1` (`N = 0`).** The one-site chain is the degenerate label ring `ZMod 2`, where
the two ring neighbours `a + 1` and `a - 1` of a label coincide and where the only two labels are
the aligned `|Φ↓⟩` and `|Φ↑⟩`. The flip identity still holds, and the conjuncts pin the two
configurations. -/
example (a : ZMod (2 * (0 + 1))) :
    lowEnergyConfig 0 (a + 1) = siteFlipAt (lowEnergyConfig 0 a) (wallSite 0 a)
      ∧ lowEnergyConfig 0 0 = ![1] ∧ lowEnergyConfig 0 1 = ![0] :=
  ⟨lowEnergyConfig_succ_eq_siteFlipAt 0 a, by decide, by decide⟩

/-- **B7 signature pin.** `lowEnergyConfig_ne_of_not_adjacent` is the source's "all other matrix
elements are vanishing" transported to the `2L`-basis: labels that are not equal and not
ring-adjacent give configurations that are neither equal nor a single-site flip of one another, so
`quantumIsingHamiltonian_apply_eq_zero` (A4) applies. This is the non-diagonal, non-adjacent branch
of C2 below. -/
example (N : ℕ) (hN : 1 ≤ N) {a b : ZMod (2 * (N + 1))} (h₀ : b ≠ a) (h₁ : b ≠ a + 1)
    (h₂ : b ≠ a - 1) :
    lowEnergyConfig N b ≠ lowEnergyConfig N a
      ∧ ∀ x, lowEnergyConfig N b ≠ siteFlipAt (lowEnergyConfig N a) x :=
  lowEnergyConfig_ne_of_not_adjacent N hN h₀ h₁ h₂

/-- **C2 signature pin.** `lowEnergyMatrix_eq_add_tightBindingRing` is (S.24)-(S.27) plus "all
other matrix elements are vanishing" stated as a single entrywise matrix identity: the `2L × 2L`
compression of `quantumIsingHamiltonian` to the low-energy basis is `E_GS^(0)` on the diagonal
(`-(N:ℂ)/4 • 1`) plus a tight-binding ring on the labels (`tightBindingRing`, hopping `-λ/2`
between ring-adjacent labels and potential `ringPotential` elsewhere on the diagonal). The
`1 ≤ N` hypothesis is what the proof route needs — the non-adjacent entries go through
`lowEnergyConfig_ne_of_not_adjacent` — and not a structural constraint: `tightBindingRing`
contributes one hopping `if` per entry, so no hop is double-counted when the two ring neighbours
`a + 1` and `a - 1` coincide at `L = 1`. -/
example (N : ℕ) (lam : ℝ) (hN : 1 ≤ N) :
    lowEnergyMatrix N lam
      = (-(N : ℂ) / 4) • (1 : Matrix (ZMod (2 * (N + 1))) (ZMod (2 * (N + 1))) ℂ)
        + tightBindingRing N lam :=
  lowEnergyMatrix_eq_add_tightBindingRing N lam hN

/-! ## Low-energy matrix at `L = 2` (`N = 1`) -/

/-- **Open-chain diagonal matrix element on the ring labels (`L = 2`).** Both aligned labels (`0` =
`|Φ↓⟩` and `2` = `|Φ↑⟩`) have diagonal entry `E_GS^(0) = -(L-1)/4 = -1/4`, the single-bond open
chain value. -/
example (lam : ℝ) :
    lowEnergyMatrix 1 lam 0 0 = -1 / 4 ∧ lowEnergyMatrix 1 lam 2 2 = -1 / 4 := by
  have hN : (1 : ℕ) ≤ 1 := le_refl 1
  rw [lowEnergyMatrix_eq_add_tightBindingRing 1 lam hN]
  constructor
  all_goals simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    tightBindingRing, ringPotential]
  all_goals norm_num +decide

/-- **Single domain wall (`L = 2`).** The label `1` (`|Φ_1^↑↓⟩` at `L = 2`) has diagonal entry
`E_GS^(0) + 1/2 = -1/4 + 1/2`, Tasaki eq. (S.25). `L = 2` is the smallest size at which
`ringPotential` takes its nonzero value `1/2`: on a shorter label ring the only labels are `0`
and `L`, where it vanishes. -/
example (lam : ℝ) : lowEnergyMatrix 1 lam 1 1 = -1 / 4 + 1 / 2 := by
  have hN : (1 : ℕ) ≤ 1 := le_refl 1
  rw [lowEnergyMatrix_eq_add_tightBindingRing 1 lam hN]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    tightBindingRing, ringPotential]
  norm_num +decide

/-- **Hopping and vanishing (`L = 2`).** Ring-adjacent labels `0` and `1` hop at `-λ/2`
(Tasaki eq. (S.27)); labels `0` and `2`, at ring-distance `2` (not adjacent although the ring has
only `4` labels), have vanishing matrix element. -/
example (lam : ℝ) :
    lowEnergyMatrix 1 lam 0 1 = -(lam : ℂ) / 2 ∧ lowEnergyMatrix 1 lam 0 2 = 0 := by
  have hN : (1 : ℕ) ≤ 1 := le_refl 1
  rw [lowEnergyMatrix_eq_add_tightBindingRing 1 lam hN]
  constructor
  all_goals simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    tightBindingRing, ringPotential]
  all_goals norm_num +decide

/-! ## Low-energy matrix at `L = 3` (`N = 2`) — book convention and ring closure -/

/-- **Book-convention pin (`L = 3`).** Label `1` is `|Φ_1^↑↓⟩` (site `0` up, sites `1, 2` down) and
label `4 = L + 1` is its mirror `|Φ_1^↓↑⟩` (site `0` down, sites `1, 2` up). -/
example : lowEnergyConfig 2 1 = ![0, 1, 1] ∧ lowEnergyConfig 2 4 = ![1, 0, 0] := by
  have h₁ := lowEnergyConfig_natCast_le 2 1 (by norm_num)
  have h₂ := lowEnergyConfig_natCast_add 2 1 (by norm_num)
  norm_num at h₁ h₂
  refine ⟨?_, ?_⟩
  · rw [h₁]; funext x; fin_cases x <;> rfl
  · rw [h₂]; funext x; fin_cases x <;> rfl

/-- **Non-adjacent vanishing at ring-distance `2` (`L = 3`).** Labels `1` and `3` differ by two
domain-wall moves, so their matrix element vanishes. -/
example (lam : ℝ) : lowEnergyMatrix 2 lam 1 3 = 0 := by
  have hN : (1 : ℕ) ≤ 2 := by norm_num
  rw [lowEnergyMatrix_eq_add_tightBindingRing 2 lam hN]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    tightBindingRing, ringPotential]
  norm_num +decide

/-- **Ring closure (`L = 3`).** Label `2L - 1 = 5` is ring-adjacent to label `0`
(`⟨Φ↓|Ĥ|Φ_{L-1}^↓↑⟩`, the last case of Tasaki eq. (S.27)), giving hop `-λ/2`. The labels form
the ring type `ZMod (2 * (N + 1))`, in which `0 - 1` wraps to `2L - 1`. -/
example (lam : ℝ) : lowEnergyMatrix 2 lam 0 5 = -(lam : ℂ) / 2 := by
  have hN : (1 : ℕ) ≤ 2 := by norm_num
  rw [lowEnergyMatrix_eq_add_tightBindingRing 2 lam hN]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    tightBindingRing, ringPotential]
  norm_num +decide

/-! ## Bracket reading -/

/-- **Bracket reading (`L = 2`).** `lowEnergyMatrix` entries really are `⟨Φ_a|Ĥ|Φ_b⟩` in the
configuration basis, via the existing `basisVec_expectation_eq_diagonal`: no new bracket
convention is introduced by this PR. -/
example (lam : ℝ) :
    star (basisVec (lowEnergyConfig 1 0)) ⬝ᵥ
        (quantumIsingHamiltonian 1 (1 / 4) (lam / 2)).mulVec (basisVec (lowEnergyConfig 1 0))
      = lowEnergyMatrix 1 lam 0 0 :=
  basisVec_expectation_eq_diagonal (lowEnergyConfig 1 0)
    (quantumIsingHamiltonian 1 (1 / 4) (lam / 2))

/-! ## The eigenvalue equation and the parity ansätze -/

/-- **Signature pin (eigenvector equation as recursion).** `lowEnergyMatrix_mulVec_eq_iff`
rewrites the eigenvector equation `lowEnergyMatrix * φ = (E_GS^(0) + ε) • φ` as the (S.30)
tight-binding recursion at every ring label at once. This is what turns matrix-eigenvector
reasoning into the scalar recurrence solved by the (S.32) ansätze below. -/
example (N : ℕ) (lam eps : ℝ) (hN : 1 ≤ N) (phi : ZMod (2 * (N + 1)) → ℂ) :
    lowEnergyMatrix N lam *ᵥ phi = ((-(N : ℝ) / 4 + eps : ℝ) : ℂ) • phi ↔
      ∀ j : ZMod (2 * (N + 1)),
        (eps : ℂ) * phi j
          = -((lam : ℂ) / 2) * (phi (j - 1) + phi (j + 1)) + ringPotential N j * phi j :=
  lowEnergyMatrix_mulVec_eq_iff N lam hN eps phi

/-- **Signature pin (`tightBindingEnergy`).** `tightBindingEnergy` is (S.31),
`ε = -(λ/2)(e^κ + e^-κ) + 1/2`, and the fixture states that shape in full at `λ = 1`,
`κ = log 2` and closes it by `rfl`, so it pins the shape only at those values: a variant that
agrees there, such as the constant term read as `λ/2`, is not separated by it. The numeral is
pinned separately below. -/
example : tightBindingEnergy (1 : ℝ) (Real.log 2)
    = -(1 / 2 : ℝ) * (Real.exp (Real.log 2) + Real.exp (-Real.log 2)) + 1 / 2 :=
  rfl

/-- **Numeric pin (`tightBindingEnergy` at `λ = 1`, `κ = log 2`).** Evaluating (S.31) at
`e^κ = 2`, `e^-κ = 1/2` gives `-(1/2)(2 + 1/2) + 1/2 = -3/4`. -/
example : tightBindingEnergy (1 : ℝ) (Real.log 2) = -3 / 4 := by
  unfold tightBindingEnergy
  rw [Real.exp_log (by norm_num), Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

/-- **Signature pin (`rootEquation`).** `rootEquation` is (S.34) in cleared form, with `s = ±1`
folding the `±`/`∓` pair of the source into a single sign parameter shared by numerator and
denominator. -/
example (N : ℕ) (lam kappa s : ℝ) :
    rootEquation N lam kappa s ↔
      Real.exp kappa - Real.exp (-kappa)
        = lam⁻¹ * ((1 + s * Real.exp (-kappa * (N + 1 : ℕ)))
            / (1 - s * Real.exp (-kappa * (N + 1 : ℕ)))) :=
  Iff.rfl

/-- **Parity pin.** `φ_L = ±φ_0` under `s = ±1` — the source's own definition of the
symmetric/antisymmetric ansatz — holds for every `N` and `κ`, independently of the root
equation. -/
example (N : ℕ) (kappa : ℝ) :
    lowEnergyAnsatz N kappa 1 ((N + 1 : ℕ) : ZMod (2 * (N + 1)))
        = lowEnergyAnsatz N kappa 1 0
      ∧ lowEnergyAnsatz N kappa (-1) ((N + 1 : ℕ) : ZMod (2 * (N + 1)))
          = -lowEnergyAnsatz N kappa (-1) 0 := by
  have hvalL : (((N + 1 : ℕ)) : ZMod (2 * (N + 1))).val = N + 1 := ZMod.val_cast_of_lt (by omega)
  have hval0 : ((0 : ZMod (2 * (N + 1)))).val = 0 := ZMod.val_zero
  constructor <;>
    · simp only [lowEnergyAnsatz, hvalL, hval0, if_pos (le_refl (N + 1)),
        if_pos (Nat.zero_le (N + 1)), Nat.cast_zero, sub_self, sub_zero, mul_zero, Real.exp_zero]
      push_cast
      ring

/-- **Numeric pin (`L = 2`, `κ = log 2`, first branch, `j = 0, 1, 2`).** With `e^κ = 2`,
`e^-κ = 1/2` the symmetric ansatz (`s = 1`) takes the values `5/4, 1, 5/4` and the antisymmetric
one (`s = -1`) takes `3/4, 0, -3/4` at labels `0, 1, 2`. These are values of the first-branch
expression `e^{-κj} + s e^{-κ(L-j)}` of (S.32). The branch threshold is *not* pinned by them:
reading it as `j.val < N + 1` rather than `j.val ≤ N + 1` moves only the label `j = L`, where the
two branch expressions agree — they differ only in the order of their two summands — so all six
numerals stay the same. -/
example :
    lowEnergyAnsatz 1 (Real.log 2) 1 0 = 5 / 4 ∧ lowEnergyAnsatz 1 (Real.log 2) 1 1 = 1
      ∧ lowEnergyAnsatz 1 (Real.log 2) 1 2 = 5 / 4
      ∧ lowEnergyAnsatz 1 (Real.log 2) (-1) 0 = 3 / 4
      ∧ lowEnergyAnsatz 1 (Real.log 2) (-1) 1 = 0
      ∧ lowEnergyAnsatz 1 (Real.log 2) (-1) 2 = -3 / 4 := by
  have h0 : ((0 : ZMod (2 * (1 + 1)))).val = 0 := rfl
  have h1 : ((1 : ZMod (2 * (1 + 1)))).val = 1 := rfl
  have h2 : ((2 : ZMod (2 * (1 + 1)))).val = 2 := rfl
  have hc1 : Complex.exp (-Complex.log 2) = 1 / 2 := by
    rw [Complex.exp_neg, Complex.exp_log (by norm_num : (2 : ℂ) ≠ 0)]
    norm_num
  have hc2 : Complex.exp (-(Complex.log 2 * 2)) = 1 / 4 := by
    rw [show -(Complex.log 2 * 2) = -Complex.log 2 + -Complex.log 2 by ring, Complex.exp_add, hc1]
    norm_num
  norm_num [lowEnergyAnsatz, h0, h1, h2, hc1, hc2]

/-- **Numeric pin (`L = 2`, `κ = log 2`, second branch, `j = 3`).** Label `3` lies in the
`j = L, …, 2L` branch of (S.32), which the labels `0, 1, 2` above never reach; the values `1`
(`s = 1`) and `0` (`s = -1`) coincide with the `j = 1` values because `3` is the mirror of `1`
across `L = 2`. At `L = 2`, `j = 3` both `j - L` and `2L - j` equal `1`, so these values do not
distinguish the two exponents of that branch. -/
example :
    lowEnergyAnsatz 1 (Real.log 2) 1 3 = 1 ∧ lowEnergyAnsatz 1 (Real.log 2) (-1) 3 = 0 := by
  have h3 : ((3 : ZMod (2 * (1 + 1)))).val = 3 := rfl
  have hc1 : Complex.exp (-Complex.log 2) = 1 / 2 := by
    rw [Complex.exp_neg, Complex.exp_log (by norm_num : (2 : ℂ) ≠ 0)]
    norm_num
  norm_num [lowEnergyAnsatz, h3, hc1]

/-- **Numeric pin (`L = 3`, `κ = log 2`, second branch, `j = 4`).** This is the smallest size at
which the two exponents of the second branch `s e^{-κ(j-L)} + e^{-κ(2L-j)}` of (S.32) differ:
`j - L = 1` while `2L - j = 2`, giving `s/2 + 1/4`, i.e. `3/4` at `s = 1` and `-1/4` at
`s = -1`. -/
example :
    lowEnergyAnsatz 2 (Real.log 2) 1 4 = 3 / 4
      ∧ lowEnergyAnsatz 2 (Real.log 2) (-1) 4 = -1 / 4 := by
  have h4 : ((4 : ZMod (2 * (2 + 1)))).val = 4 := rfl
  have hc1 : Complex.exp (-Complex.log 2) = 1 / 2 := by
    rw [Complex.exp_neg, Complex.exp_log (by norm_num : (2 : ℂ) ≠ 0)]
    norm_num
  have hc2 : Complex.exp (-(Complex.log 2 * 2)) = 1 / 4 := by
    rw [show -(Complex.log 2 * 2) = -Complex.log 2 + -Complex.log 2 by ring, Complex.exp_add, hc1]
    norm_num
  constructor <;> norm_num [lowEnergyAnsatz, h4, hc1, hc2]

/-- **Signature pin (capstone eigenvector theorem).** `lowEnergyAnsatz_isEigenvector` is the
capstone of this module: under the root equation the ansatz is a nonzero eigenvector of
`lowEnergyMatrix` with eigenvalue `E_GS^(0) + tightBindingEnergy lam kappa`, i.e. (S.28)-(S.34)
assembled. Nothing here claims `ε_±` is an energy of the original Hamiltonian. -/
example (N : ℕ) (lam kappa s : ℝ) (hN : 1 ≤ N) (hlam : 0 < lam) (hk : 0 < kappa)
    (hs : s = 1 ∨ s = -1) (hroot : rootEquation N lam kappa s) :
    lowEnergyAnsatz N kappa s ≠ 0
      ∧ lowEnergyMatrix N lam *ᵥ lowEnergyAnsatz N kappa s
          = ((-(N : ℝ) / 4 + tightBindingEnergy lam kappa : ℝ) : ℂ) • lowEnergyAnsatz N kappa s :=
  lowEnergyAnsatz_isEigenvector N lam kappa s hN hlam hk hs hroot

/-! ## The `κ∞` layer: (S.35)-(S.39) -/

/-- **E1 signature/value pin.** `kappaInf` is the `L → ∞` root `κ∞` of (S.34), defined directly
by (S.35), `e^κ∞ - e^-κ∞ = λ⁻¹`, via `Real.arsinh`: since the left-hand side is `2 sinh κ∞`, the
argument of `arsinh` is `1 / (2λ)`, which at `λ = 1` is `1/2`. The value at `λ = 1` alone does not
separate that argument from `λ/2`, with which it agrees there; the argument is pinned as a
function of `λ` by `exp_kappaInf_sub_exp_neg` below. The two sides are not definitionally equal
(`1 / (2 * 1)` is not reducible to `1 / 2` in `ℝ`), so the numeral is normalized first. -/
example : kappaInf (1 : ℝ) = Real.arsinh (1 / 2) := by
  norm_num [kappaInf]

/-- **E2 signature pin.** `kappaInf_pos` records `κ∞ > 0` for `λ > 0`, matching the source's
"`κ > 0` is a constant to be determined" (below (S.30)) transported to the `L → ∞` limit. -/
example (lam : ℝ) (hlam : 0 < lam) : 0 < kappaInf lam :=
  kappaInf_pos hlam

/-- **E3 signature pin.** `exp_kappaInf_sub_exp_neg` is (S.35) itself,
`e^κ∞ - e^-κ∞ = λ⁻¹`, stated for `kappaInf`. -/
example (lam : ℝ) (hlam : 0 < lam) :
    Real.exp (kappaInf lam) - Real.exp (-(kappaInf lam)) = lam⁻¹ :=
  exp_kappaInf_sub_exp_neg hlam

/-- **E4 signature pin.** `exp_neg_kappaInf_eq` gives `e^-κ∞` in closed radical form,
`2λ / (1 + √(1 + 4λ²))`, the ingredient `Real.exp_arsinh` supplies for C6/E5 below. -/
example (lam : ℝ) (hlam : 0 < lam) :
    Real.exp (-(kappaInf lam)) = 2 * lam / (1 + Real.sqrt (1 + 4 * lam ^ 2)) :=
  exp_neg_kappaInf_eq hlam

/-- **C6 signature pin — (S.39).** `tightBindingEnergy_kappaInf_eq` is the source's `ε∞`,
`ε∞ = -(λ/2)(e^κ∞ + e^-κ∞) + 1/2 = -√(1 + 4λ²)/2 + 1/2`, the middle equality of (S.39). The
radical is confirmed present on the rendered PDF page 501 (printed p. 501); the `.txt` extract
drops it. The final `≃ -λ²` of (S.39) is a small-`λ` approximation and is not asserted here. -/
example (lam : ℝ) (hlam : 0 < lam) :
    tightBindingEnergy lam (kappaInf lam) = (1 - Real.sqrt (1 + 4 * lam ^ 2)) / 2 :=
  tightBindingEnergy_kappaInf_eq hlam

/-- **C6 numeric pin at `λ = 1/2`.** `1 + 4 * (1/2)^2 = 2`, so `ε∞ = (1 - √2)/2` — a concrete
value that is only reached through the radical of (S.39): a dropped-radical mis-transcription
(reading (S.39) as `ε∞ = (1 - λ)/2` or similar) gives a different rational value here. -/
example : tightBindingEnergy (1 / 2 : ℝ) (kappaInf (1 / 2)) = (1 - Real.sqrt 2) / 2 := by
  have h := tightBindingEnergy_kappaInf_eq (lam := (1 / 2 : ℝ)) (by norm_num)
  norm_num at h
  linarith [h]

/-- **E5 signature pin.** `tanh_kappaInf_eq` is `tanh κ∞ = 1/√(1 + 4λ²)`, the ingredient (S.41)
later needs (`E_1st - E_GS ≃ 2 tanh(κ∞) e^-κ∞L`), stated here purely in terms of `kappaInf`. -/
example (lam : ℝ) (hlam : 0 < lam) :
    Real.tanh (kappaInf lam) = (Real.sqrt (1 + 4 * lam ^ 2))⁻¹ :=
  tanh_kappaInf_eq hlam

/-- **E5 numeric pin at `λ = 1/2`.** `1 + 4 * (1/2)^2 = 2`, so `2 tanh κ∞ = 2/√2 = √2` — the
constant standing in front of `e^-κ∞L` in Tasaki eq. (S.41). -/
example : 2 * Real.tanh (kappaInf (1 / 2 : ℝ)) = Real.sqrt 2 := by
  have h := tanh_kappaInf_eq (lam := (1 / 2 : ℝ)) (by norm_num)
  have harg : (1 : ℝ) + 4 * (1 / 2 : ℝ) ^ 2 = 2 := by norm_num
  rw [harg] at h
  rw [h, ← div_eq_mul_inv]
  exact Real.div_sqrt

/-- **C8 signature pin.** `tendsto_exp_neg_kappaInf_div_atZero` is the first of the two small-`λ`
replacements behind the final form `≃ 2 λ^L` of (S.41): `e^-κ∞ / λ → 1` as `λ ↓ 0`, the limit
form of the source's `e^κ∞ ≃ λ⁻¹` (p. 500, below (S.35)). -/
example :
    Filter.Tendsto (fun l : ℝ => Real.exp (-(kappaInf l)) / l)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
  tendsto_exp_neg_kappaInf_div_atZero

/-- **C9 signature pin.** `tendsto_tanh_kappaInf_atZero` is the second small-`λ` replacement of
(S.41): the prefactor `tanh κ∞` tends to `1` as `λ ↓ 0`. -/
example :
    Filter.Tendsto (fun l : ℝ => Real.tanh (kappaInf l))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
  tendsto_tanh_kappaInf_atZero

end LatticeSystem.Tests.Problem33aLowEnergy
