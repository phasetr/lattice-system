/-
**Counterexample to the printed constant of Tasaki eq. (3.4.13), as literally quantified.**

Tasaki Problem 3.4.a (statement pp. 67-68, printed solution p. 501) asserts, for a Hamiltonian
`Ĥ = Σ_x ĥ_x` and order operator `Ô = Σ_x ô_x` on the periodic lattice `Λ_L`, each local term
supported on the radius-`r` ball of its own site with `manyBodyOperatorNormS ĥ_x ≤ h₀`,
`manyBodyOperatorNormS ô_x ≤ o₀`, and a normalized ground state `Φ`, the bound
`⟨Φ|[Ô,[Ĥ,Ô]]|Φ⟩ ≤ 4 (2r+1)^d (4r+1)^d h₀ o₀² L^d`.

The lattice `Λ_L` of eq. (3.1.2) (p. 51) is defined only for **even** `L`, so an admissible
instance of the Problem has `L` even; the counterexample below carries that admissibility as an
explicit conjunct of its statement.  The module exhibits an explicit `d = 1`, `r = 1`, `L = 4`
spin-1/2 ring satisfying every hypothesis of the Problem for which the printed constant is
**false**: the model attains `256`, exceeding the printed `4·3·5·1·1·4 = 240`.  It does satisfy the
repository's own honest bound `4 (4r+1)^d (8r+1)^d h₀ o₀² L^d = 720`
(`RangeLocalDoubleCommutatorBound.lean`), so nothing proved elsewhere in the repository is
affected; only the printed constant's literal quantification is refuted.  Whether the printed
constant holds for even `L > 4r+1` is left open.

The model: the 4-site ring `Λ = Fin 4` with `ringDist 4`, carrying a Bell pair on each of the site
pairs `{1,2}` and `{3,0}`.  Its four stabilizers `X̂₃X̂₀`, `X̂₁X̂₂`, `Ẑ₁Ẑ₂`, `Ẑ₃Ẑ₀` are commuting
Hermitian involutions; `ĥ_x` is the negative of the `x`-th of them, and the order terms are
`ô₀ = ô₁ = Ŷ₀Ŷ₁`, `ô₂ = ô₃ = Ŷ₂Ŷ₃`, each supported on the radius-1 ring ball of its own site.  The
joint `+1` eigenvector of the four stabilizers is the ground state, at `E₀ = −4`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, Problem 3.4.a, statement pp. 67-68, printed solution p. 501; the lattice `Λ_L` of
eq. (3.1.2), §3.1 p. 51, is defined for even `L`.
-/
import LatticeSystem.Quantum.SpinS.HaldaneConjecture
import LatticeSystem.Quantum.SpinS.RangeLocalDoubleCommutatorBound
import LatticeSystem.Quantum.SpinS.ExpectationNormBound

namespace LatticeSystem.Tests.PrintedConstantCounterexample

open LatticeSystem.Quantum LatticeSystem.Math Matrix

open scoped ComplexOrder

/-! ## Single-site 2×2 letters -/

/-- The single-site Pauli-`X` matrix `!![0,1;1,0]`. -/
private def sX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The single-site Pauli-`Z` matrix `!![1,0;0,-1]`. -/
private def sZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The single-site Pauli-`Y` matrix `!![0,-i;i,0]`. -/
private noncomputable def sY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-! ## Single-site 2×2 algebra -/

/-- `X² = 1`. -/
private lemma sX_mul_sX : sX * sX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sX, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- `Z² = 1`. -/
private lemma sZ_mul_sZ : sZ * sZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- `Y² = 1`. -/
private lemma sY_mul_sY : sY * sY = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sY, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Complex.ext_iff]

/-- `XY = iZ`. -/
private lemma sX_mul_sY : sX * sY = Complex.I • sZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sX, sY, sZ, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]

/-- `YX = −iZ`. -/
private lemma sY_mul_sX : sY * sX = (-Complex.I) • sZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sX, sY, sZ, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]

/-- `YZ = iX`. -/
private lemma sY_mul_sZ : sY * sZ = Complex.I • sX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sX, sY, sZ, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]

/-- `ZY = −iX`. -/
private lemma sZ_mul_sY : sZ * sY = (-Complex.I) • sX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sX, sY, sZ, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]

/-- `XZ = −iY`. -/
private lemma sX_mul_sZ : sX * sZ = (-Complex.I) • sY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sX, sY, sZ, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]

/-- `X` is Hermitian. -/
private lemma sX_conjTranspose : Matrix.conjTranspose sX = sX := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sX, Matrix.conjTranspose_apply]

/-- `Z` is Hermitian. -/
private lemma sZ_conjTranspose : Matrix.conjTranspose sZ = sZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sZ, Matrix.conjTranspose_apply]

/-- `Y` is Hermitian. -/
private lemma sY_conjTranspose : Matrix.conjTranspose sY = sY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sY, Matrix.conjTranspose_apply, Complex.ext_iff]

/-! ## Four-slot Pauli words on the 4-ring -/

/-- Case analysis on the four sites of the ring. -/
private lemma fin_four_cases {P : Fin 4 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3)
    (x : Fin 4) : P x := by
  fin_cases x
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- Both configurations of a qubit. -/
private lemma fin_two_cases (a : Fin 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Merging the leading letters of two right-nested words whose tails commute with the second
leading letter. -/
private lemma word_mul_step {a b R S : ManyBodyOpS (Fin 4) 1} (h : Commute R b) :
    a * R * (b * S) = a * b * (R * S) := by
  rw [mul_assoc a R (b * S), ← mul_assoc R b S, h.eq, mul_assoc b R S, ← mul_assoc a b (R * S)]

/-- The **Pauli word** `c · A₀ A₁ A₂ A₃`: the letter `Aₖ` sits at the site `k` of the 4-ring and
`c` is an overall phase.  Every operator of the model is such a word, and the whole operator
computation is carried out in this calculus. -/
private noncomputable def pw (c : ℂ) (A₀ A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℂ) :
    ManyBodyOpS (Fin 4) 1 :=
  c • (onSiteS 0 A₀ * (onSiteS 1 A₁ * (onSiteS 2 A₂ * onSiteS 3 A₃)))

/-- **Words multiply slotwise**: the product of two words is the word of the slotwise products,
with the phases multiplied. -/
private lemma pw_mul (c d : ℂ) (A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Matrix (Fin 2) (Fin 2) ℂ) :
    pw c A₀ A₁ A₂ A₃ * pw d B₀ B₁ B₂ B₃
      = pw (c * d) (A₀ * B₀) (A₁ * B₁) (A₂ * B₂) (A₃ * B₃) := by
  have h32 : Commute (onSiteS (3 : Fin 4) A₃ : ManyBodyOpS (Fin 4) 1) (onSiteS 2 B₂) :=
    onSiteS_commute_of_ne (by decide) _ _
  have h31 : Commute (onSiteS (3 : Fin 4) A₃ : ManyBodyOpS (Fin 4) 1) (onSiteS 1 B₁) :=
    onSiteS_commute_of_ne (by decide) _ _
  have h30 : Commute (onSiteS (3 : Fin 4) A₃ : ManyBodyOpS (Fin 4) 1) (onSiteS 0 B₀) :=
    onSiteS_commute_of_ne (by decide) _ _
  have h21 : Commute (onSiteS (2 : Fin 4) A₂ : ManyBodyOpS (Fin 4) 1) (onSiteS 1 B₁) :=
    onSiteS_commute_of_ne (by decide) _ _
  have h20 : Commute (onSiteS (2 : Fin 4) A₂ : ManyBodyOpS (Fin 4) 1) (onSiteS 0 B₀) :=
    onSiteS_commute_of_ne (by decide) _ _
  have h10 : Commute (onSiteS (1 : Fin 4) A₁ : ManyBodyOpS (Fin 4) 1) (onSiteS 0 B₀) :=
    onSiteS_commute_of_ne (by decide) _ _
  rw [pw, pw, pw, smul_mul_smul_comm]
  congr 1
  rw [word_mul_step (h10.mul_left (h20.mul_left h30)), word_mul_step (h21.mul_left h31),
    word_mul_step h32, onSiteS_mul_onSiteS_same, onSiteS_mul_onSiteS_same,
    onSiteS_mul_onSiteS_same, onSiteS_mul_onSiteS_same]

/-- A phase in the zeroth slot of a word is an overall phase. -/
private lemma pw_smul_slot0 (c e : ℂ) (A₀ A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℂ) :
    pw c (e • A₀) A₁ A₂ A₃ = pw (c * e) A₀ A₁ A₂ A₃ := by
  simp only [pw, onSiteS_smul, smul_mul_assoc, smul_smul]

/-- A phase in the first slot of a word is an overall phase. -/
private lemma pw_smul_slot1 (c e : ℂ) (A₀ A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℂ) :
    pw c A₀ (e • A₁) A₂ A₃ = pw (c * e) A₀ A₁ A₂ A₃ := by
  simp only [pw, onSiteS_smul, smul_mul_assoc, mul_smul_comm, smul_smul]

/-- A phase in the second slot of a word is an overall phase. -/
private lemma pw_smul_slot2 (c e : ℂ) (A₀ A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℂ) :
    pw c A₀ A₁ (e • A₂) A₃ = pw (c * e) A₀ A₁ A₂ A₃ := by
  simp only [pw, onSiteS_smul, smul_mul_assoc, mul_smul_comm, smul_smul]

/-- A phase in the third slot of a word is an overall phase. -/
private lemma pw_smul_slot3 (c e : ℂ) (A₀ A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℂ) :
    pw c A₀ A₁ A₂ (e • A₃) = pw (c * e) A₀ A₁ A₂ A₃ := by
  simp only [pw, onSiteS_smul, mul_smul_comm, smul_smul]

/-- Negating a word negates its phase. -/
private lemma pw_neg (c : ℂ) (A₀ A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) ℂ) :
    -pw c A₀ A₁ A₂ A₃ = pw (-c) A₀ A₁ A₂ A₃ := by
  rw [pw, pw, neg_smul]

/-- The word with trivial phase and all letters trivial is the identity operator. -/
private lemma pw_one_all : pw 1 1 1 1 1 = 1 := by
  simp only [pw, onSiteS_one, one_mul, one_smul]

/-! ## The counterexample -/

/-- **Counterexample to the printed constant of Tasaki eq. (3.4.13), as literally quantified.**
The explicit `d = 1`, `r = 1`, `L = 4` spin-1/2 ring model of this file (`hLoc`, `oLoc`, `gsState`)
lives on an admissible lattice — `Λ_L` of eq. (3.1.2) (p. 51) requires `L` even, discharged here as
the conjunct `Even 4` — and satisfies every hypothesis of Problem 3.4.a (range-1 support, unit
local-term norms, normalized ground state at `E₀ = −4`), yet has
`⟨Φ_GS|[Ô,[Ĥ,Ô]]|Φ_GS⟩ = 256`, exceeding the printed constant
`4(2·1+1)^1(4·1+1)^1·1·1²·4^1 = 240` of eq. (3.4.13) as literally quantified.  The repository's own
proved bound `4(4·1+1)^1(8·1+1)^1·1·1²·4^1 = 720` (`RangeLocalDoubleCommutatorBound.lean`) is
satisfied and unaffected.  Whether the printed constant holds for even `L > 4r+1` is open. -/
theorem tasaki_problem_3_4_a_printed_constant_counterexample :
    Even (4 : ℕ) ∧
      (∀ x : Fin 4, SupportedOnS (siteBall (ringDist 4) 1 x) (hLoc x)) ∧
      (∀ x : Fin 4, SupportedOnS (siteBall (ringDist 4) 1 x) (oLoc x)) ∧
      (∀ x : Fin 4, manyBodyOperatorNormS (hLoc x) ≤ 1) ∧
      (∀ x : Fin 4, manyBodyOperatorNormS (oLoc x) ≤ 1) ∧
      star gsState ⬝ᵥ gsState = 1 ∧
      IsGroundEnergy (∑ x, hLoc x) (-4) ∧
      (∑ x, hLoc x) *ᵥ gsState = ((-4 : ℝ) : ℂ) • gsState ∧
      rayleighOnVec
          ((∑ x, oLoc x) * ((∑ b, hLoc b) * (∑ x, oLoc x) - (∑ x, oLoc x) * (∑ b, hLoc b))
            - ((∑ b, hLoc b) * (∑ x, oLoc x) - (∑ x, oLoc x) * (∑ b, hLoc b)) * (∑ x, oLoc x))
          gsState = 256 ∧
      4 * (2 * (1 : ℝ) + 1) ^ 1 * (4 * (1 : ℝ) + 1) ^ 1 * 1 * 1 ^ 2 * (4 : ℝ) ^ 1
        < rayleighOnVec
            ((∑ x, oLoc x) * ((∑ b, hLoc b) * (∑ x, oLoc x) - (∑ x, oLoc x) * (∑ b, hLoc b))
              - ((∑ b, hLoc b) * (∑ x, oLoc x) - (∑ x, oLoc x) * (∑ b, hLoc b)) * (∑ x, oLoc x))
            gsState := by
  refine ⟨⟨2, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hLoc_supportedOnS_siteBall
  · exact oLoc_supportedOnS_siteBall
  · exact hLoc_manyBodyOperatorNormS_le_one
  · exact oLoc_manyBodyOperatorNormS_le_one
  · exact gsState_dotProduct_self_eq_one
  · exact hLoc_sum_isGroundEnergy
  · exact hLoc_sum_mulVec_gsState_eq_smul
  · exact doubleCommutator_rayleighOnVec_gsState_eq_value
  · exact doubleCommutator_rayleighOnVec_gsState_gt_printed_constant

end LatticeSystem.Tests.PrintedConstantCounterexample
