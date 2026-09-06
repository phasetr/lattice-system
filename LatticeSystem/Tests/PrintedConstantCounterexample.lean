/-
**Counterexample to the printed constant of Tasaki eq. (3.4.13), as literally quantified.**

Tasaki Problem 3.4.a (statement pp. 67-68, printed solution p. 501) asserts, for a Hamiltonian
`Ĥ = Σ_x ĥ_x` and order operator `Ô = Σ_x ô_x` on the periodic lattice `Λ_L`, each local term
supported on the radius-`r` ball of its own site with `manyBodyOperatorNormS ĥ_x ≤ h₀`,
`manyBodyOperatorNormS ô_x ≤ o₀`, and a normalized ground state `Φ`, the bound
`⟨Φ|[Ô,[Ĥ,Ô]]|Φ⟩ ≤ 4 (2r+1)^d (4r+1)^d h₀ o₀² L^d`.  This module exhibits an explicit `d = 1`,
`r = 1`, `L = 5` spin-1/2 ring satisfying every hypothesis of the Problem for which the printed
constant is **false**: the model attains `500`, exceeding the printed `4·3·5·1·1·5 = 300`.  It does
satisfy the repository's own honest bound `4 (4r+1)^d (8r+1)^d h₀ o₀² L^d = 500` (attained exactly,
`RangeLocalDoubleCommutatorBound.lean`), so nothing proved elsewhere in the repository is affected;
only the printed constant's literal quantification is refuted.  Whether the printed constant holds
in the regime `L > 4r+1` is left open.

The model: the 5-site ring `Λ = Fin 5` with `ringDist 5`, `ĥ_x = −Ẑ_{x−1}X̂_xẐ_{x+1}`,
`ô_x = X̂_{x−1}Ŷ_xX̂_{x+1}`, and the (normalized) cluster/graph state `Φ_GS` of the 5-cycle, which is
the unique ground state of `Ĥ = Σ_x ĥ_x` at `E₀ = −5` by Theorem 7.8
(`Quantum/SpinS/ClusterState.lean`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §3.4, Problem 3.4.a, statement pp. 67-68, printed solution p. 501.
-/
import LatticeSystem.Quantum.SpinS.ClusterState
import LatticeSystem.Quantum.SpinS.RangeLocalDoubleCommutatorBound
import LatticeSystem.Quantum.SpinS.ExpectationNormBound
import Mathlib.Combinatorics.SimpleGraph.Circulant

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

/-- `ZX = iY`. -/
private lemma sZ_mul_sX : sZ * sX = Complex.I • sY := by
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

/-- `2 Ŝ^{(3)} = Z` on the qubit: the repository's spin-`1/2` operator in Pauli letters. -/
private lemma two_smul_spinSOp3_eq_sZ : (2 : ℂ) • spinSOp3 1 = sZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sZ, spinSOp3, Matrix.diagonal_apply, Complex.ext_iff]

/-- `2 Ŝ^{(1)} = X` on the qubit: the repository's spin-`1/2` operator in Pauli letters. -/
private lemma two_smul_spinSOp1_eq_sX : (2 : ℂ) • spinSOp1 1 = sX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sX, spinSOp1, spinSOpPlus, spinSOpMinus, Matrix.add_apply, Complex.ext_iff]

/-! ## Ring index arithmetic and Pauli words -/

/-- Distinct offsets from a common centre land on distinct sites of the 5-ring. -/
private lemma offsetSite_ne (x : Fin 5) {a b : Fin 5} (hab : a ≠ b) : x + a ≠ x + b :=
  fun h => hab (add_left_cancel h)

/-- Single-site operators at distinct offsets from a common centre commute. -/
private lemma commute_offset (x : Fin 5) {a b : Fin 5} (hab : a ≠ b)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Commute (onSiteS (x + a) A : ManyBodyOpS (Fin 5) 1) (onSiteS (x + b) B) :=
  onSiteS_commute_of_ne (offsetSite_ne x hab) A B

/-- Merging the leading letters of two right-nested words whose tails commute with the second
leading letter. -/
private lemma word_mul_step {a b R S : ManyBodyOpS (Fin 5) 1} (h : Commute R b) :
    a * R * (b * S) = a * b * (R * S) := by
  rw [mul_assoc a R (b * S), ← mul_assoc R b S, h.eq, mul_assoc b R S, ← mul_assoc a b (R * S)]

/-- Moving the trailing letter of a three-letter right-nested word to the front. -/
private lemma word_rotate3 {a b c : ManyBodyOpS (Fin 5) 1} (h0 : Commute a c) (h1 : Commute b c) :
    a * (b * c) = c * (a * b) := by
  rw [h1.eq, ← mul_assoc, h0.eq, mul_assoc]

/-- Moving the trailing letter of a four-letter right-nested word to the front. -/
private lemma word_rotate4 {a b c d : ManyBodyOpS (Fin 5) 1} (h0 : Commute a d)
    (h1 : Commute b d) (h2 : Commute c d) : a * (b * (c * d)) = d * (a * (b * c)) := by
  rw [word_rotate3 h1 h2, ← mul_assoc, h0.eq, mul_assoc]

/-- Moving the trailing letter of a five-letter right-nested word to the front, when it commutes
with each of the other four. -/
private lemma word_rotate {a b c d e : ManyBodyOpS (Fin 5) 1} (h0 : Commute a e)
    (h1 : Commute b e) (h2 : Commute c e) (h3 : Commute d e) :
    a * (b * (c * (d * e))) = e * (a * (b * (c * d))) := by
  rw [word_rotate4 h1 h2 h3, ← mul_assoc, h0.eq, mul_assoc]

/-- A product of three pairwise commuting factors is unchanged by reversal. -/
private lemma triple_reverse {P Q R : ManyBodyOpS (Fin 5) 1} (hPQ : Commute P Q)
    (hPR : Commute P R) (hQR : Commute Q R) : R * Q * P = P * Q * R := by
  rw [mul_assoc, hPQ.symm.eq, ← mul_assoc, hPR.symm.eq, mul_assoc, hQR.symm.eq, ← mul_assoc]

/-- The **Pauli word** `c · A₀ A₁ A₂ A₃ A₄` anchored at `x`: the letter `Aₖ` sits at the site
`x + k` of the 5-ring, and `c` is an overall phase.  Every operator of the model is such a word,
and the whole computation is carried out in this calculus.  The anchor slot is written `x + 0`
rather than `x` so that all five slots are uniform offsets, which is what the commutation
bookkeeping of `pw_mul` and `pw_shift` consumes. -/
private noncomputable def pw (c : ℂ) (x : Fin 5) (A₀ A₁ A₂ A₃ A₄ : Matrix (Fin 2) (Fin 2) ℂ) :
    ManyBodyOpS (Fin 5) 1 :=
  c • (onSiteS (x + 0) A₀ * (onSiteS (x + 1) A₁ * (onSiteS (x + 2) A₂ *
    (onSiteS (x + 3) A₃ * onSiteS (x + 4) A₄))))

/-- **Words multiply slotwise**: the product of two words anchored at the same site is the word of
the slotwise products, with the phases multiplied. -/
private lemma pw_mul (c d : ℂ) (x : Fin 5)
    (A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ : Matrix (Fin 2) (Fin 2) ℂ) :
    pw c x A₀ A₁ A₂ A₃ A₄ * pw d x B₀ B₁ B₂ B₃ B₄
      = pw (c * d) x (A₀ * B₀) (A₁ * B₁) (A₂ * B₂) (A₃ * B₃) (A₄ * B₄) := by
  have h43 : Commute (onSiteS (x + 4) A₄ : ManyBodyOpS (Fin 5) 1) (onSiteS (x + 3) B₃) :=
    commute_offset x (Fin.ne_of_val_ne (by norm_num)) _ _
  have h32 : Commute (onSiteS (x + 3) A₃ : ManyBodyOpS (Fin 5) 1) (onSiteS (x + 2) B₂) :=
    commute_offset x (Fin.ne_of_val_ne (by norm_num)) _ _
  have h42 : Commute (onSiteS (x + 4) A₄ : ManyBodyOpS (Fin 5) 1) (onSiteS (x + 2) B₂) :=
    commute_offset x (Fin.ne_of_val_ne (by norm_num)) _ _
  have h21 : Commute (onSiteS (x + 2) A₂ : ManyBodyOpS (Fin 5) 1) (onSiteS (x + 1) B₁) :=
    commute_offset x (Fin.ne_of_val_ne (by norm_num)) _ _
  have h31 : Commute (onSiteS (x + 3) A₃ : ManyBodyOpS (Fin 5) 1) (onSiteS (x + 1) B₁) :=
    commute_offset x (Fin.ne_of_val_ne (by norm_num)) _ _
  have h41 : Commute (onSiteS (x + 4) A₄ : ManyBodyOpS (Fin 5) 1) (onSiteS (x + 1) B₁) :=
    commute_offset x (Fin.ne_of_val_ne (by norm_num)) _ _
  have h10 : Commute (onSiteS (x + 1) A₁ : ManyBodyOpS (Fin 5) 1) (onSiteS (x + 0) B₀) :=
    commute_offset x (Fin.ne_of_val_ne (by norm_num)) _ _
  have h20 : Commute (onSiteS (x + 2) A₂ : ManyBodyOpS (Fin 5) 1) (onSiteS (x + 0) B₀) :=
    commute_offset x (Fin.ne_of_val_ne (by norm_num)) _ _
  have h30 : Commute (onSiteS (x + 3) A₃ : ManyBodyOpS (Fin 5) 1) (onSiteS (x + 0) B₀) :=
    commute_offset x (Fin.ne_of_val_ne (by norm_num)) _ _
  have h40 : Commute (onSiteS (x + 4) A₄ : ManyBodyOpS (Fin 5) 1) (onSiteS (x + 0) B₀) :=
    commute_offset x (Fin.ne_of_val_ne (by norm_num)) _ _
  rw [pw, pw, pw, smul_mul_smul_comm]
  congr 1
  rw [word_mul_step (h10.mul_left (h20.mul_left (h30.mul_left h40))),
    word_mul_step (h21.mul_left (h31.mul_left h41)),
    word_mul_step (h32.mul_left h42), word_mul_step h43,
    onSiteS_mul_onSiteS_same, onSiteS_mul_onSiteS_same, onSiteS_mul_onSiteS_same,
    onSiteS_mul_onSiteS_same, onSiteS_mul_onSiteS_same]

/-- **Re-anchoring a word**: a word anchored at `x + 1` is the cyclically rotated word anchored at
`x`.  Iterating this lemma moves every translate of a model term to the common anchor at which the
slotwise product `pw_mul` applies. -/
private lemma pw_shift (c : ℂ) (x : Fin 5) (A₀ A₁ A₂ A₃ A₄ : Matrix (Fin 2) (Fin 2) ℂ) :
    pw c (x + 1) A₀ A₁ A₂ A₃ A₄ = pw c x A₄ A₀ A₁ A₂ A₃ := by
  have h0 : Commute (onSiteS (x + 1) A₀ : ManyBodyOpS (Fin 5) 1) (onSiteS (x + 0) A₄) :=
    commute_offset x (Fin.ne_of_val_ne (by norm_num)) _ _
  have h1 : Commute (onSiteS (x + 2) A₁ : ManyBodyOpS (Fin 5) 1) (onSiteS (x + 0) A₄) :=
    commute_offset x (Fin.ne_of_val_ne (by norm_num)) _ _
  have h2 : Commute (onSiteS (x + 3) A₂ : ManyBodyOpS (Fin 5) 1) (onSiteS (x + 0) A₄) :=
    commute_offset x (Fin.ne_of_val_ne (by norm_num)) _ _
  have h3 : Commute (onSiteS (x + 4) A₃ : ManyBodyOpS (Fin 5) 1) (onSiteS (x + 0) A₄) :=
    commute_offset x (Fin.ne_of_val_ne (by norm_num)) _ _
  rw [pw, pw, add_assoc x 1 0, add_assoc x 1 1, add_assoc x 1 2, add_assoc x 1 3, add_assoc x 1 4,
    show (1 : Fin 5) + 0 = 1 from rfl, show (1 : Fin 5) + 1 = 2 from rfl,
    show (1 : Fin 5) + 2 = 3 from rfl, show (1 : Fin 5) + 3 = 4 from rfl,
    show (1 : Fin 5) + 4 = 0 from rfl]
  congr 1
  exact word_rotate h0 h1 h2 h3

/-- A phase in the anchor slot of a word is an overall phase. -/
private lemma pw_smul_slot0 (c e : ℂ) (x : Fin 5) (A₀ A₁ A₂ A₃ A₄ : Matrix (Fin 2) (Fin 2) ℂ) :
    pw c x (e • A₀) A₁ A₂ A₃ A₄ = pw (c * e) x A₀ A₁ A₂ A₃ A₄ := by
  simp only [pw, onSiteS_smul, smul_mul_assoc, smul_smul]

/-- A phase in the first slot of a word is an overall phase. -/
private lemma pw_smul_slot1 (c e : ℂ) (x : Fin 5) (A₀ A₁ A₂ A₃ A₄ : Matrix (Fin 2) (Fin 2) ℂ) :
    pw c x A₀ (e • A₁) A₂ A₃ A₄ = pw (c * e) x A₀ A₁ A₂ A₃ A₄ := by
  simp only [pw, onSiteS_smul, smul_mul_assoc, mul_smul_comm, smul_smul]

/-- A phase in the second slot of a word is an overall phase. -/
private lemma pw_smul_slot2 (c e : ℂ) (x : Fin 5) (A₀ A₁ A₂ A₃ A₄ : Matrix (Fin 2) (Fin 2) ℂ) :
    pw c x A₀ A₁ (e • A₂) A₃ A₄ = pw (c * e) x A₀ A₁ A₂ A₃ A₄ := by
  simp only [pw, onSiteS_smul, smul_mul_assoc, mul_smul_comm, smul_smul]

/-- A phase in the third slot of a word is an overall phase. -/
private lemma pw_smul_slot3 (c e : ℂ) (x : Fin 5) (A₀ A₁ A₂ A₃ A₄ : Matrix (Fin 2) (Fin 2) ℂ) :
    pw c x A₀ A₁ A₂ (e • A₃) A₄ = pw (c * e) x A₀ A₁ A₂ A₃ A₄ := by
  simp only [pw, onSiteS_smul, smul_mul_assoc, mul_smul_comm, smul_smul]

/-- A phase in the fourth slot of a word is an overall phase. -/
private lemma pw_smul_slot4 (c e : ℂ) (x : Fin 5) (A₀ A₁ A₂ A₃ A₄ : Matrix (Fin 2) (Fin 2) ℂ) :
    pw c x A₀ A₁ A₂ A₃ (e • A₄) = pw (c * e) x A₀ A₁ A₂ A₃ A₄ := by
  simp only [pw, onSiteS_smul, mul_smul_comm, smul_smul]

/-- Negating a word negates its phase. -/
private lemma pw_neg (c : ℂ) (x : Fin 5) (A₀ A₁ A₂ A₃ A₄ : Matrix (Fin 2) (Fin 2) ℂ) :
    -pw c x A₀ A₁ A₂ A₃ A₄ = pw (-c) x A₀ A₁ A₂ A₃ A₄ := by
  rw [pw, pw, neg_smul]

/-! ## The model: the 5-cycle, its local Hamiltonian/order terms, and its cluster ground state -/

/-- The 5-cycle graph on `Fin 5`, the site graph of the model.  An `abbrev` (not a plain `def`) so
that `cycleGraph`'s `DecidableRel Adj` instance is found by unfolding through typeclass search. -/
private noncomputable abbrev ringG : SimpleGraph (Fin 5) := SimpleGraph.cycleGraph 5

/-- The local Hamiltonian term `ĥ_x = −Ẑ_{x−1}X̂_xẐ_{x+1}` at site `x`. -/
private noncomputable def hLoc (x : Fin 5) : ManyBodyOpS (Fin 5) 1 :=
  -(onSiteS (x - 1) sZ * onSiteS x sX * onSiteS (x + 1) sZ)

/-- The local order-operator term `ô_x = X̂_{x−1}Ŷ_xX̂_{x+1}` at site `x`. -/
private noncomputable def oLoc (x : Fin 5) : ManyBodyOpS (Fin 5) 1 :=
  onSiteS (x - 1) sX * onSiteS x sY * onSiteS (x + 1) sX

/-- The unnormalized cluster-state ray representative of the 5-cycle. -/
private noncomputable def gsVec : (Fin 5 → Fin 2) → ℂ := clusterStateVec ringG

/-- The normalized ground state `Φ_GS` used in the counterexample. -/
private noncomputable def gsState : (Fin 5 → Fin 2) → ℂ := unitNormalize gsVec

/-! ## The model as Pauli words -/

/-- On the 5-ring, the predecessor of a site is its shift by `4`. -/
private lemma sub_one_eq_add_four (x : Fin 5) : x - 1 = x + 4 := by
  rw [show (4 : Fin 5) = -1 from by rw [eq_neg_iff_add_eq_zero]; rfl, ← sub_eq_add_neg]

/-- A nonzero offset moves a site of the 5-ring. -/
private lemma site_ne_center (x : Fin 5) {a : Fin 5} (ha : a ≠ 0) : x + a ≠ x := fun h =>
  offsetSite_ne x ha (by rw [add_zero]; exact h)

/-- `ĥ_x` as a Pauli word: `−X̂` at `x`, `Ẑ` at `x+1`, `Ẑ` at `x+4 = x−1`. -/
private lemma hLoc_eq_pw (x : Fin 5) : hLoc x = pw (-1) x sX sZ 1 1 sZ := by
  have hRP : Commute (onSiteS (x + 4) sZ : ManyBodyOpS (Fin 5) 1) (onSiteS x sX) :=
    onSiteS_commute_of_ne (site_ne_center x (Fin.ne_of_val_ne (by norm_num))) _ _
  have hRQ : Commute (onSiteS (x + 4) sZ : ManyBodyOpS (Fin 5) 1) (onSiteS (x + 1) sZ) :=
    onSiteS_commute_of_ne (offsetSite_ne x (Fin.ne_of_val_ne (by norm_num))) _ _
  rw [hLoc, pw, add_zero, onSiteS_one, onSiteS_one, one_mul, one_mul, neg_smul, one_smul,
    sub_one_eq_add_four]
  congr 1
  rw [hRP.eq, mul_assoc, hRQ.eq]

/-- `ô_x` as a Pauli word: `Ŷ` at `x`, `X̂` at `x+1`, `X̂` at `x+4 = x−1`. -/
private lemma oLoc_eq_pw (x : Fin 5) : oLoc x = pw 1 x sY sX 1 1 sX := by
  have hRP : Commute (onSiteS (x + 4) sX : ManyBodyOpS (Fin 5) 1) (onSiteS x sY) :=
    onSiteS_commute_of_ne (site_ne_center x (Fin.ne_of_val_ne (by norm_num))) _ _
  have hRQ : Commute (onSiteS (x + 4) sX : ManyBodyOpS (Fin 5) 1) (onSiteS (x + 1) sX) :=
    onSiteS_commute_of_ne (offsetSite_ne x (Fin.ne_of_val_ne (by norm_num))) _ _
  rw [oLoc, pw, add_zero, onSiteS_one, onSiteS_one, one_mul, one_mul, one_smul,
    sub_one_eq_add_four, hRP.eq, mul_assoc, hRQ.eq]

/-- The word with trivial phase and all letters trivial is the identity operator. -/
private lemma pw_one_all (x : Fin 5) : pw 1 x 1 1 1 1 1 = 1 := by
  rw [pw, onSiteS_one, onSiteS_one, onSiteS_one, onSiteS_one, onSiteS_one, one_mul, one_mul,
    one_mul, one_mul, one_smul]

/-- `ĥ_x² = 1`: every local term of the model is an involution. -/
private lemma hLoc_mul_self (x : Fin 5) : hLoc x * hLoc x = 1 := by
  rw [hLoc_eq_pw, pw_mul, sX_mul_sX, sZ_mul_sZ, mul_one,
    show (-1 : ℂ) * (-1) = 1 from by norm_num, pw_one_all]

/-- `ô_x² = 1`: every order term of the model is an involution. -/
private lemma oLoc_mul_self (x : Fin 5) : oLoc x * oLoc x = 1 := by
  rw [oLoc_eq_pw, pw_mul, sX_mul_sX, sY_mul_sY, mul_one, one_mul, pw_one_all]

/-- A product of three pairwise commuting Hermitian factors is Hermitian. -/
private lemma triple_isHermitian {P Q R : ManyBodyOpS (Fin 5) 1}
    (hP : Matrix.conjTranspose P = P) (hQ : Matrix.conjTranspose Q = Q)
    (hR : Matrix.conjTranspose R = R) (hRP : Commute R P) (hRQ : Commute R Q)
    (hPQ : Commute P Q) : Matrix.conjTranspose (R * P * Q) = R * P * Q := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP, hQ, hR, ← mul_assoc]
  exact triple_reverse hRP hRQ hPQ

/-- `ĥ_x` is Hermitian. -/
private lemma hLoc_conjTranspose (x : Fin 5) : Matrix.conjTranspose (hLoc x) = hLoc x := by
  have hP : Matrix.conjTranspose (onSiteS x sX : ManyBodyOpS (Fin 5) 1) = onSiteS x sX := by
    rw [onSiteS_conjTranspose, sX_conjTranspose]
  have hQ : Matrix.conjTranspose (onSiteS (x + 1) sZ : ManyBodyOpS (Fin 5) 1)
      = onSiteS (x + 1) sZ := by rw [onSiteS_conjTranspose, sZ_conjTranspose]
  have hR : Matrix.conjTranspose (onSiteS (x - 1) sZ : ManyBodyOpS (Fin 5) 1)
      = onSiteS (x - 1) sZ := by rw [onSiteS_conjTranspose, sZ_conjTranspose]
  have hne1 : x - 1 ≠ x := by
    rw [sub_one_eq_add_four]; exact site_ne_center x (Fin.ne_of_val_ne (by norm_num))
  have hne2 : x - 1 ≠ x + 1 := by
    rw [sub_one_eq_add_four]; exact offsetSite_ne x (Fin.ne_of_val_ne (by norm_num))
  have hne3 : x ≠ x + 1 := (site_ne_center x (Fin.ne_of_val_ne (by norm_num))).symm
  rw [hLoc, Matrix.conjTranspose_neg]
  congr 1
  exact triple_isHermitian hP hQ hR (onSiteS_commute_of_ne hne1 _ _)
    (onSiteS_commute_of_ne hne2 _ _) (onSiteS_commute_of_ne hne3 _ _)

/-- `ô_x` is Hermitian. -/
private lemma oLoc_conjTranspose (x : Fin 5) : Matrix.conjTranspose (oLoc x) = oLoc x := by
  have hP : Matrix.conjTranspose (onSiteS x sY : ManyBodyOpS (Fin 5) 1) = onSiteS x sY := by
    rw [onSiteS_conjTranspose, sY_conjTranspose]
  have hQ : Matrix.conjTranspose (onSiteS (x + 1) sX : ManyBodyOpS (Fin 5) 1)
      = onSiteS (x + 1) sX := by rw [onSiteS_conjTranspose, sX_conjTranspose]
  have hR : Matrix.conjTranspose (onSiteS (x - 1) sX : ManyBodyOpS (Fin 5) 1)
      = onSiteS (x - 1) sX := by rw [onSiteS_conjTranspose, sX_conjTranspose]
  have hne1 : x - 1 ≠ x := by
    rw [sub_one_eq_add_four]; exact site_ne_center x (Fin.ne_of_val_ne (by norm_num))
  have hne2 : x - 1 ≠ x + 1 := by
    rw [sub_one_eq_add_four]; exact offsetSite_ne x (Fin.ne_of_val_ne (by norm_num))
  have hne3 : x ≠ x + 1 := (site_ne_center x (Fin.ne_of_val_ne (by norm_num))).symm
  rw [oLoc]
  exact triple_isHermitian hP hQ hR (onSiteS_commute_of_ne hne1 _ _)
    (onSiteS_commute_of_ne hne2 _ _) (onSiteS_commute_of_ne hne3 _ _)

/-! ## Locality and unit norms of the model terms -/

/-- A site lies in its own radius-1 ring ball. -/
private lemma mem_siteBall_self (x : Fin 5) : x ∈ siteBall (ringDist 5) 1 x :=
  mem_siteBall.mpr (by rw [ringDist_self]; norm_num)

/-- The successor of a site lies in its radius-1 ring ball. -/
private lemma mem_siteBall_succ (x : Fin 5) : x + 1 ∈ siteBall (ringDist 5) 1 x := by
  refine mem_siteBall.mpr ?_
  have hx := x.isLt
  simp only [ringDist, Fin.val_add]
  omega

/-- The predecessor of a site lies in its radius-1 ring ball. -/
private lemma mem_siteBall_pred (x : Fin 5) : x - 1 ∈ siteBall (ringDist 5) 1 x := by
  refine mem_siteBall.mpr ?_
  have hx := x.isLt
  rw [sub_one_eq_add_four]
  simp only [ringDist, Fin.val_add]
  omega

/-- **Hypothesis (a) for `ĥ`**: each local Hamiltonian term is supported on the radius-1 ring ball
of its own site, so the model has range `r = 1`. -/
private lemma hLoc_supportedOnS_siteBall :
    ∀ x : Fin 5, SupportedOnS (siteBall (ringDist 5) 1 x) (hLoc x) := by
  intro x
  rw [hLoc, ← neg_one_smul ℂ (onSiteS (x - 1) sZ * onSiteS x sX * onSiteS (x + 1) sZ)]
  exact (((supportedOnS_onSiteS (mem_siteBall_pred x) sZ).mul
    (supportedOnS_onSiteS (mem_siteBall_self x) sX)).mul
    (supportedOnS_onSiteS (mem_siteBall_succ x) sZ)).smul (-1)

/-- **Hypothesis (a) for `ô`**: each local order term is supported on the radius-1 ring ball of its
own site, so the model has range `r = 1`. -/
private lemma oLoc_supportedOnS_siteBall :
    ∀ x : Fin 5, SupportedOnS (siteBall (ringDist 5) 1 x) (oLoc x) := by
  intro x
  exact ((supportedOnS_onSiteS (mem_siteBall_pred x) sX).mul
    (supportedOnS_onSiteS (mem_siteBall_self x) sY)).mul
    (supportedOnS_onSiteS (mem_siteBall_succ x) sX)

/-- **Hypothesis (b) for `ĥ`**: each local Hamiltonian term is Hermitian and an involution, hence
unitary, so its operator norm is exactly `1` and in particular `h₀ = 1` is admissible. -/
private lemma hLoc_manyBodyOperatorNormS_le_one :
    ∀ x : Fin 5, manyBodyOperatorNormS (hLoc x) ≤ 1 := fun x =>
  le_of_eq (manyBodyOperatorNormS_eq_one_of_unitary
    (by rw [hLoc_conjTranspose, hLoc_mul_self]))

/-- **Hypothesis (b) for `ô`**: each local order term is Hermitian and an involution, hence
unitary, so its operator norm is exactly `1` and in particular `o₀ = 1` is admissible. -/
private lemma oLoc_manyBodyOperatorNormS_le_one :
    ∀ x : Fin 5, manyBodyOperatorNormS (oLoc x) ≤ 1 := fun x =>
  le_of_eq (manyBodyOperatorNormS_eq_one_of_unitary
    (by rw [oLoc_conjTranspose, oLoc_mul_self]))

/-! ## The cluster state as the ground state of the model -/

/-- The Briegel–Raussendorf stabilizer `K̂_x = Ẑ_{x−1}X̂_xẐ_{x+1} = −ĥ_x` at site `x`. -/
private noncomputable def kLoc (x : Fin 5) : ManyBodyOpS (Fin 5) 1 := -hLoc x

/-- The stabilizer written out as a product of single-site Pauli letters. -/
private lemma kLoc_eq (x : Fin 5) :
    kLoc x = onSiteS (x - 1) sZ * onSiteS x sX * onSiteS (x + 1) sZ := by
  rw [kLoc, hLoc]
  exact neg_neg _

/-- `K̂_x` is Hermitian. -/
private lemma kLoc_conjTranspose (x : Fin 5) : Matrix.conjTranspose (kLoc x) = kLoc x := by
  rw [kLoc, Matrix.conjTranspose_neg, hLoc_conjTranspose]

/-- `K̂_x² = 1`. -/
private lemma kLoc_mul_self (x : Fin 5) : kLoc x * kLoc x = 1 := by
  rw [kLoc, neg_mul_neg, hLoc_mul_self]

/-- The single-site `Ẑ` letter is the repository's `pauliZS`. -/
private lemma onSiteS_sZ_eq_pauliZS (i : Fin 5) :
    (onSiteS i sZ : ManyBodyOpS (Fin 5) 1) = pauliZS i := by
  rw [pauliZS, spinSSiteOp3_def, ← onSiteS_smul, two_smul_spinSOp3_eq_sZ]

/-- The single-site `X̂` letter is the repository's `pauliXS`. -/
private lemma onSiteS_sX_eq_pauliXS (i : Fin 5) :
    (onSiteS i sX : ManyBodyOpS (Fin 5) 1) = pauliXS i := by
  rw [pauliXS, spinSSiteOp1, ← onSiteS_smul, two_smul_spinSOp1_eq_sX]

/-- On the 5-cycle the neighbour-`Ẑ` product of a vertex is the pair of `Ẑ` letters at its two ring
neighbours. -/
private lemma neighborZProduct_ringG (x : Fin 5) :
    neighborZProduct ringG x = onSiteS (x - 1) sZ * onSiteS (x + 1) sZ := by
  have hne : x - 1 ≠ x + 1 := by
    rw [sub_one_eq_add_four]; exact offsetSite_ne x (Fin.ne_of_val_ne (by norm_num))
  rw [onSiteS_sZ_eq_pauliZS, onSiteS_sZ_eq_pauliZS, pauliZS_eq_diagonal, pauliZS_eq_diagonal,
    Matrix.diagonal_mul_diagonal, neighborZProduct]
  congr 1
  funext cfg
  rw [← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.cycleGraph_neighborFinset,
    Finset.prod_pair hne]

/-- The model's local terms are exactly the Briegel–Raussendorf stabilizers of the 5-cycle. -/
private lemma brStabilizer_ringG_eq_kLoc (x : Fin 5) : brStabilizer ringG x = kLoc x := by
  have hPR : Commute (onSiteS x sX : ManyBodyOpS (Fin 5) 1) (onSiteS (x - 1) sZ) := by
    refine onSiteS_commute_of_ne ?_ _ _
    rw [sub_one_eq_add_four]
    exact (site_ne_center x (Fin.ne_of_val_ne (by norm_num))).symm
  rw [brStabilizer, neighborZProduct_ringG, kLoc_eq, ← onSiteS_sX_eq_pauliXS, ← mul_assoc, hPR.eq]

/-- The model Hamiltonian is the graph-state Hamiltonian of the 5-cycle, on the nose: no shift and
no rescaling are needed, since the repository's cluster Hamiltonian is `−Σ_x K̂_x`. -/
private lemma hLoc_sum_eq_graphStateHamiltonianS :
    ∑ x, hLoc x = graphStateHamiltonianS ringG := by
  rw [graphStateHamiltonianS, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [brStabilizer_ringG_eq_kLoc, kLoc, neg_one_smul]
  exact (neg_neg _).symm

/-- **Hypothesis (d), first half**: `E₀ = −5` is the ground energy of `Ĥ = Σ_x ĥ_x`, by Tasaki
Theorem 7.8 applied to the 5-cycle. -/
private lemma hLoc_sum_isGroundEnergy : IsGroundEnergy (∑ x, hLoc x) (-5) := by
  have h := tasaki_theorem_7_8 ringG (by norm_num) gsVec rfl
  rw [Fintype.card_fin] at h
  simp only [Nat.cast_ofNat] at h
  rw [hLoc_sum_eq_graphStateHamiltonianS]
  exact h.1

/-- The unnormalized cluster state is a ground eigenvector of the model Hamiltonian: the ground
eigenspace of Theorem 7.8 is one-dimensional and spanned by it, so the eigenvalue equation follows
from the spectral statement. -/
private lemma hLoc_sum_mulVec_gsVec : (∑ x, hLoc x) *ᵥ gsVec = (-5 : ℂ) • gsVec := by
  obtain ⟨⟨hmem, _⟩, _, _, huniq⟩ := tasaki_theorem_7_8 ringG (by norm_num) gsVec rfl
  rw [Fintype.card_fin] at hmem huniq
  obtain ⟨Ψ, hΨ0, hΨ⟩ := hmem
  push_cast at hΨ huniq
  obtain ⟨c, rfl⟩ := huniq Ψ hΨ0 hΨ
  have hc : c ≠ 0 := by
    intro h; rw [h, zero_smul] at hΨ0; exact hΨ0 rfl
  rw [Matrix.mulVec_smul, smul_comm] at hΨ
  rw [hLoc_sum_eq_graphStateHamiltonianS]
  exact smul_right_injective _ hc hΨ

/-- The five stabilizers sum to `5` on the cluster state. -/
private lemma kLoc_sum_mulVec_gsVec : ∑ w, (kLoc w *ᵥ gsVec) = (5 : ℂ) • gsVec := by
  have h := hLoc_sum_mulVec_gsVec
  rw [show (∑ x, hLoc x) = -∑ x, kLoc x from by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun x _ => by rw [kLoc]; exact (neg_neg _).symm,
    Matrix.neg_mulVec, Matrix.sum_mulVec, neg_eq_iff_eq_neg] at h
  rw [h, ← neg_smul]
  norm_num

/-- **Stabilizer relations from the ground-state energy.**  Five Hermitian involutions that sum, on
a vector `v`, to `5 v` each fix `v`: the difference `K̂_w v − v` has squared norm
`2⟨v,v⟩ − 2⟨v,K̂_w v⟩`, the five squared norms sum to zero, and each is nonnegative. -/
private lemma mulVec_eq_of_sum_mulVec (K : Fin 5 → ManyBodyOpS (Fin 5) 1)
    (hH : ∀ w, Matrix.conjTranspose (K w) = K w) (hI : ∀ w, K w * K w = 1)
    (v : (Fin 5 → Fin 2) → ℂ) (hsum : ∑ w, (K w *ᵥ v) = (5 : ℂ) • v) (w : Fin 5) :
    K w *ᵥ v = v := by
  have hstar : ∀ z, star (K z *ᵥ v) ⬝ᵥ v = star v ⬝ᵥ (K z *ᵥ v) := by
    intro z; rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH]
  have hnorm : ∀ z, star (K z *ᵥ v) ⬝ᵥ (K z *ᵥ v) = star v ⬝ᵥ v := by
    intro z
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hH, hI,
      Matrix.one_mulVec]
  have hterm : ∀ z, star (K z *ᵥ v - v) ⬝ᵥ (K z *ᵥ v - v)
      = 2 * (star v ⬝ᵥ v) - 2 * (star v ⬝ᵥ (K z *ᵥ v)) := by
    intro z
    rw [star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hnorm, hstar]
    ring
  have hzero : ∑ z, star (K z *ᵥ v - v) ⬝ᵥ (K z *ᵥ v - v) = 0 := by
    simp only [hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Finset.mul_sum, ← dotProduct_sum, hsum, dotProduct_smul, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  have hnn : ∀ z ∈ (Finset.univ : Finset (Fin 5)),
      (0 : ℂ) ≤ star (K z *ᵥ v - v) ⬝ᵥ (K z *ᵥ v - v) := fun z _ => dotProduct_star_self_nonneg _
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero w (Finset.mem_univ w)
  exact sub_eq_zero.mp (dotProduct_star_self_eq_zero.mp hz)

/-- **The stabilizer relations `K̂_x Φ_C = Φ_C`** (Tasaki eqs. (7.3.29)-(7.3.30)) for the 5-ring
cluster state. -/
private lemma kLoc_mulVec_gsVec (w : Fin 5) : kLoc w *ᵥ gsVec = gsVec :=
  mulVec_eq_of_sum_mulVec kLoc kLoc_conjTranspose kLoc_mul_self gsVec kLoc_sum_mulVec_gsVec w

/-! ## Normalization of the ground state -/

/-- The cluster state is nonzero. -/
private lemma gsVec_ne_zero : gsVec ≠ 0 := clusterStateVec_ne_zero ringG

/-- The cluster state has positive squared norm, so it can be normalized. -/
private lemma gsVec_vecNormSqRe_pos : 0 < vecNormSqRe gsVec := by
  have h : (0 : ℂ) < star gsVec ⬝ᵥ gsVec := dotProduct_star_self_pos_iff.mpr gsVec_ne_zero
  simpa [vecNormSqRe] using (Complex.lt_def.mp h).1

/-- **Hypothesis (c)**: the ground state used in the counterexample is normalized. -/
private lemma gsState_dotProduct_self_eq_one : star gsState ⬝ᵥ gsState = 1 := by
  rw [gsState]
  exact unitNormalize_dotProduct_self gsVec gsVec_vecNormSqRe_pos

/-- **Hypothesis (d), second half**: the normalized cluster state is an eigenvector of `Ĥ` at the
ground energy `−5`. -/
private lemma hLoc_sum_mulVec_gsState_eq_smul :
    (∑ x, hLoc x) *ᵥ gsState = ((-5 : ℝ) : ℂ) • gsState := by
  rw [gsState, unitNormalize, Matrix.mulVec_smul, hLoc_sum_mulVec_gsVec, smul_comm]
  norm_num

/-! ## Translates of the model terms, re-anchored at a common site -/

/-- Re-anchoring a word by two sites. -/
private lemma pw_shift2 (c : ℂ) (x : Fin 5) (A₀ A₁ A₂ A₃ A₄ : Matrix (Fin 2) (Fin 2) ℂ) :
    pw c (x + 2) A₀ A₁ A₂ A₃ A₄ = pw c x A₃ A₄ A₀ A₁ A₂ := by
  rw [show x + 2 = x + 1 + 1 from by rw [add_assoc, show (1 : Fin 5) + 1 = 2 from rfl],
    pw_shift, pw_shift]

/-- Re-anchoring a word by three sites. -/
private lemma pw_shift3 (c : ℂ) (x : Fin 5) (A₀ A₁ A₂ A₃ A₄ : Matrix (Fin 2) (Fin 2) ℂ) :
    pw c (x + 3) A₀ A₁ A₂ A₃ A₄ = pw c x A₂ A₃ A₄ A₀ A₁ := by
  rw [show x + 3 = x + 2 + 1 from by rw [add_assoc, show (2 : Fin 5) + 1 = 3 from rfl],
    pw_shift, pw_shift2]

/-- Re-anchoring a word by four sites. -/
private lemma pw_shift4 (c : ℂ) (x : Fin 5) (A₀ A₁ A₂ A₃ A₄ : Matrix (Fin 2) (Fin 2) ℂ) :
    pw c (x + 4) A₀ A₁ A₂ A₃ A₄ = pw c x A₁ A₂ A₃ A₄ A₀ := by
  rw [show x + 4 = x + 3 + 1 from by rw [add_assoc, show (3 : Fin 5) + 1 = 4 from rfl],
    pw_shift, pw_shift3]

/-- `ĥ_{x+1}` as a word anchored at `x`. -/
private lemma hLoc_shift1 (x : Fin 5) : hLoc (x + 1) = pw (-1) x sZ sX sZ 1 1 := by
  rw [hLoc_eq_pw, pw_shift]

/-- `ĥ_{x+2}` as a word anchored at `x`. -/
private lemma hLoc_shift2 (x : Fin 5) : hLoc (x + 2) = pw (-1) x 1 sZ sX sZ 1 := by
  rw [hLoc_eq_pw, pw_shift2]

/-- `ĥ_{x+3}` as a word anchored at `x`. -/
private lemma hLoc_shift3 (x : Fin 5) : hLoc (x + 3) = pw (-1) x 1 1 sZ sX sZ := by
  rw [hLoc_eq_pw, pw_shift3]

/-- `ĥ_{x+4}` as a word anchored at `x`. -/
private lemma hLoc_shift4 (x : Fin 5) : hLoc (x + 4) = pw (-1) x sZ 1 1 sZ sX := by
  rw [hLoc_eq_pw, pw_shift4]

/-- `ô_{x+1}` as a word anchored at `x`. -/
private lemma oLoc_shift1 (x : Fin 5) : oLoc (x + 1) = pw 1 x sX sY sX 1 1 := by
  rw [oLoc_eq_pw, pw_shift]

/-- `ô_{x+2}` as a word anchored at `x`. -/
private lemma oLoc_shift2 (x : Fin 5) : oLoc (x + 2) = pw 1 x 1 sX sY sX 1 := by
  rw [oLoc_eq_pw, pw_shift2]

/-- `ô_{x+3}` as a word anchored at `x`. -/
private lemma oLoc_shift3 (x : Fin 5) : oLoc (x + 3) = pw 1 x 1 1 sX sY sX := by
  rw [oLoc_eq_pw, pw_shift3]

/-- `ô_{x+4}` as a word anchored at `x`. -/
private lemma oLoc_shift4 (x : Fin 5) : oLoc (x + 4) = pw 1 x sX 1 1 sX sY := by
  rw [oLoc_eq_pw, pw_shift4]

/-- `K̂_x` as a Pauli word. -/
private lemma kLoc_eq_pw (x : Fin 5) : kLoc x = pw 1 x sX sZ 1 1 sZ := by
  rw [kLoc, hLoc_eq_pw, pw_neg]
  norm_num

/-- `K̂_{x+1}` as a word anchored at `x`. -/
private lemma kLoc_shift1 (x : Fin 5) : kLoc (x + 1) = pw 1 x sZ sX sZ 1 1 := by
  rw [kLoc_eq_pw, pw_shift]

/-- `K̂_{x+2}` as a word anchored at `x`. -/
private lemma kLoc_shift2 (x : Fin 5) : kLoc (x + 2) = pw 1 x 1 sZ sX sZ 1 := by
  rw [kLoc_eq_pw, pw_shift2]

/-- `K̂_{x+3}` as a word anchored at `x`. -/
private lemma kLoc_shift3 (x : Fin 5) : kLoc (x + 3) = pw 1 x 1 1 sZ sX sZ := by
  rw [kLoc_eq_pw, pw_shift3]

/-- `K̂_{x+4}` as a word anchored at `x`. -/
private lemma kLoc_shift4 (x : Fin 5) : kLoc (x + 4) = pw 1 x sZ 1 1 sZ sX := by
  rw [kLoc_eq_pw, pw_shift4]

/-! ## The anticommutation table `ô_x ĥ_z = −ĥ_z ô_x` -/

/-- Anticommutation at offset `0`: the two words differ in three slots. -/
private lemma oLoc_hLoc_anticomm0 (x : Fin 5) :
    oLoc x * hLoc (x + 0) = -(hLoc (x + 0) * oLoc x) := by
  rw [add_zero, oLoc_eq_pw, hLoc_eq_pw, pw_mul, pw_mul, pw_neg]
  simp only [sY_mul_sX, sX_mul_sZ, sX_mul_sY, sZ_mul_sX, one_mul, mul_one, pw_smul_slot0,
    pw_smul_slot1, pw_smul_slot4]
  congr 1
  norm_num [Complex.ext_iff]

/-- Anticommutation at offset `1`: the two words differ in one slot. -/
private lemma oLoc_hLoc_anticomm1 (x : Fin 5) :
    oLoc x * hLoc (x + 1) = -(hLoc (x + 1) * oLoc x) := by
  rw [oLoc_eq_pw, hLoc_shift1, pw_mul, pw_mul, pw_neg]
  simp only [sY_mul_sZ, sZ_mul_sY, sX_mul_sX, one_mul, mul_one, pw_smul_slot0]
  congr 1
  norm_num [Complex.ext_iff]

/-- Anticommutation at offset `2`: the two words differ in one slot. -/
private lemma oLoc_hLoc_anticomm2 (x : Fin 5) :
    oLoc x * hLoc (x + 2) = -(hLoc (x + 2) * oLoc x) := by
  rw [oLoc_eq_pw, hLoc_shift2, pw_mul, pw_mul, pw_neg]
  simp only [sX_mul_sZ, sZ_mul_sX, one_mul, mul_one, pw_smul_slot1]
  congr 1
  norm_num [Complex.ext_iff]

/-- Anticommutation at offset `3`: the two words differ in one slot. -/
private lemma oLoc_hLoc_anticomm3 (x : Fin 5) :
    oLoc x * hLoc (x + 3) = -(hLoc (x + 3) * oLoc x) := by
  rw [oLoc_eq_pw, hLoc_shift3, pw_mul, pw_mul, pw_neg]
  simp only [sX_mul_sZ, sZ_mul_sX, one_mul, mul_one, pw_smul_slot4]
  congr 1
  norm_num [Complex.ext_iff]

/-- Anticommutation at offset `4`: the two words differ in one slot. -/
private lemma oLoc_hLoc_anticomm4 (x : Fin 5) :
    oLoc x * hLoc (x + 4) = -(hLoc (x + 4) * oLoc x) := by
  rw [oLoc_eq_pw, hLoc_shift4, pw_mul, pw_mul, pw_neg]
  simp only [sY_mul_sZ, sZ_mul_sY, sX_mul_sX, one_mul, mul_one, pw_smul_slot0]
  congr 1
  norm_num [Complex.ext_iff]

/-- Case analysis on the ring offset: a property of an arbitrary site follows from its five
instances at the offsets `0, 1, 2, 3, 4` from any fixed site. -/
private lemma fin5_offset_cases {P : Fin 5 → Prop} (x : Fin 5) (h0 : P (x + 0)) (h1 : P (x + 1))
    (h2 : P (x + 2)) (h3 : P (x + 3)) (h4 : P (x + 4)) (z : Fin 5) : P z := by
  obtain ⟨δ, rfl⟩ : ∃ δ, z = x + δ := ⟨z - x, (add_sub_cancel x z).symm⟩
  fin_cases δ
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- **The full anticommutation table**: every order term anticommutes with every local
Hamiltonian term of the model, at every relative offset on the ring. -/
private lemma oLoc_hLoc_anticomm (x z : Fin 5) : oLoc x * hLoc z = -(hLoc z * oLoc x) :=
  fin5_offset_cases (P := fun w => oLoc x * hLoc w = -(hLoc w * oLoc x)) x
    (oLoc_hLoc_anticomm0 x) (oLoc_hLoc_anticomm1 x) (oLoc_hLoc_anticomm2 x)
    (oLoc_hLoc_anticomm3 x) (oLoc_hLoc_anticomm4 x) z

/-- `Ĥ Ô = −Ô Ĥ` for the model, by bilinearity from the anticommutation table. -/
private lemma hLoc_sum_mul_oLoc_sum :
    (∑ b, hLoc b) * (∑ x, oLoc x) = -((∑ x, oLoc x) * (∑ b, hLoc b)) := by
  have h : ∀ b x : Fin 5, hLoc b * oLoc x = -(oLoc x * hLoc b) := by
    intro b x
    rw [oLoc_hLoc_anticomm x b]
    exact (neg_neg _).symm
  calc (∑ b, hLoc b) * (∑ x, oLoc x)
      = ∑ b, ∑ x, hLoc b * oLoc x := Fintype.sum_mul_sum _ _
    _ = ∑ b, ∑ x, -(oLoc x * hLoc b) :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ => h b x
    _ = -∑ x, ∑ b, oLoc x * hLoc b := by
        simp only [Finset.sum_neg_distrib]
        rw [Finset.sum_comm]
    _ = -((∑ x, oLoc x) * (∑ b, hLoc b)) := by rw [Fintype.sum_mul_sum]

/-! ## Products of two order terms are products of stabilizers -/

/-- At offset `0` the product of two order terms is the identity. -/
private lemma oLoc_pair0 (x : Fin 5) : oLoc (x + 0) * oLoc x = 1 := by
  rw [add_zero]; exact oLoc_mul_self x

/-- At offset `1` the product of two order terms is `K̂_{x+2} K̂_{x+4}`. -/
private lemma oLoc_pair1 (x : Fin 5) :
    oLoc (x + 1) * oLoc x = kLoc (x + 2) * kLoc (x + 4) := by
  rw [oLoc_shift1, oLoc_eq_pw, kLoc_shift2, kLoc_shift4, pw_mul, pw_mul]
  simp only [sX_mul_sY, sY_mul_sX, sZ_mul_sZ, one_mul, mul_one, pw_smul_slot0, pw_smul_slot1]
  congr 1
  norm_num [Complex.ext_iff]

/-- At offset `2` the product of two order terms is `K̂_x K̂_{x+2} K̂_{x+3} K̂_{x+4}`. -/
private lemma oLoc_pair2 (x : Fin 5) :
    oLoc (x + 2) * oLoc x = kLoc x * kLoc (x + 2) * kLoc (x + 3) * kLoc (x + 4) := by
  rw [oLoc_shift2, oLoc_eq_pw, kLoc_eq_pw, kLoc_shift2, kLoc_shift3, kLoc_shift4]
  simp only [pw_mul, sX_mul_sX, sZ_mul_sZ, sX_mul_sZ, sZ_mul_sX, sY_mul_sZ, one_mul, mul_one,
    pw_smul_slot0, pw_smul_slot2, pw_smul_slot3]
  congr 1
  norm_num [Complex.ext_iff]

/-- At offset `3` the product of two order terms is `K̂_x K̂_{x+1} K̂_{x+2} K̂_{x+3}`. -/
private lemma oLoc_pair3 (x : Fin 5) :
    oLoc (x + 3) * oLoc x = kLoc x * kLoc (x + 1) * kLoc (x + 2) * kLoc (x + 3) := by
  rw [oLoc_shift3, oLoc_eq_pw, kLoc_eq_pw, kLoc_shift1, kLoc_shift2, kLoc_shift3]
  simp only [pw_mul, sX_mul_sX, sZ_mul_sZ, sX_mul_sZ, sZ_mul_sX, sY_mul_sZ, one_mul, mul_one,
    pw_smul_slot0, pw_smul_slot1, pw_smul_slot2, pw_smul_slot3]
  congr 1
  norm_num [Complex.ext_iff]

/-- At offset `4` the product of two order terms is `K̂_{x+1} K̂_{x+3}`. -/
private lemma oLoc_pair4 (x : Fin 5) :
    oLoc (x + 4) * oLoc x = kLoc (x + 1) * kLoc (x + 3) := by
  rw [oLoc_shift4, oLoc_eq_pw, kLoc_shift1, kLoc_shift3, pw_mul, pw_mul]
  simp only [sX_mul_sY, sY_mul_sX, sZ_mul_sZ, one_mul, mul_one, pw_smul_slot0, pw_smul_slot4]
  congr 1
  norm_num [Complex.ext_iff]

/-- **Every product of two order terms fixes the cluster state**: each is a product of
stabilizers, and each stabilizer fixes it. -/
private lemma oLoc_pair_mulVec_gsVec (z x : Fin 5) : (oLoc z * oLoc x) *ᵥ gsVec = gsVec := by
  have h0 : (oLoc (x + 0) * oLoc x) *ᵥ gsVec = gsVec := by rw [oLoc_pair0, Matrix.one_mulVec]
  have h1 : (oLoc (x + 1) * oLoc x) *ᵥ gsVec = gsVec := by
    rw [oLoc_pair1]; simp only [← Matrix.mulVec_mulVec, kLoc_mulVec_gsVec]
  have h2 : (oLoc (x + 2) * oLoc x) *ᵥ gsVec = gsVec := by
    rw [oLoc_pair2]; simp only [← Matrix.mulVec_mulVec, kLoc_mulVec_gsVec]
  have h3 : (oLoc (x + 3) * oLoc x) *ᵥ gsVec = gsVec := by
    rw [oLoc_pair3]; simp only [← Matrix.mulVec_mulVec, kLoc_mulVec_gsVec]
  have h4 : (oLoc (x + 4) * oLoc x) *ᵥ gsVec = gsVec := by
    rw [oLoc_pair4]; simp only [← Matrix.mulVec_mulVec, kLoc_mulVec_gsVec]
  exact fin5_offset_cases (P := fun w => (oLoc w * oLoc x) *ᵥ gsVec = gsVec) x h0 h1 h2 h3 h4 z

/-- `Ô² Φ_C = 25 Φ_C`: all twenty-five products of two order terms fix the cluster state. -/
private lemma oLoc_sum_sq_mulVec_gsVec :
    ((∑ x, oLoc x) * (∑ z, oLoc z)) *ᵥ gsVec = (25 : ℂ) • gsVec := by
  rw [Fintype.sum_mul_sum]
  simp only [Matrix.sum_mulVec, oLoc_pair_mulVec_gsVec, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_smul]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  norm_num


/-! ## The exact value of the double-commutator expectation -/

/-- The double commutator `[Ô,[Ĥ,Ô]]` of the model, written exactly as in the capstone
`manyBodyOperatorNormS_doubleCommutator_le_of_rangeLocal`. -/
private noncomputable def dcOp : ManyBodyOpS (Fin 5) 1 :=
  (∑ x, oLoc x) * ((∑ b, hLoc b) * (∑ x, oLoc x) - (∑ x, oLoc x) * (∑ b, hLoc b))
    - ((∑ b, hLoc b) * (∑ x, oLoc x) - (∑ x, oLoc x) * (∑ b, hLoc b)) * (∑ x, oLoc x)

/-- **`[Ô,[Ĥ,Ô]] = −4 Ĥ Ô²`** for the model: with `Ĥ Ô = −Ô Ĥ` the inner commutator is `2 Ĥ Ô`
and the outer one collapses, so no expansion over the `125` triples is needed. -/
private lemma dcOp_eq : dcOp = (-4 : ℂ) • ((∑ b, hLoc b) * ((∑ x, oLoc x) * (∑ x, oLoc x))) := by
  set H := ∑ b, hLoc b with hHdef
  set O := ∑ x, oLoc x with hOdef
  have h1 : O * H = -(H * O) := by rw [hLoc_sum_mul_oLoc_sum]; exact (neg_neg _).symm
  have h2 : O * (H * O) = -(H * (O * O)) := by rw [← mul_assoc, h1, neg_mul, mul_assoc]
  have h3 : O * (O * H) = H * (O * O) := by
    rw [h1, mul_neg, h2]
    exact neg_neg _
  have h4 : H * O * O = H * (O * O) := mul_assoc H O O
  have h5 : O * H * O = -(H * (O * O)) := by rw [h1, neg_mul, mul_assoc]
  have expand : O * (H * O - O * H) - (H * O - O * H) * O
      = O * (H * O) - O * (O * H) - (H * O * O - O * H * O) := by noncomm_ring
  rw [dcOp, expand, h2, h3, h4, h5]
  module

/-- The double commutator acts on the unnormalized cluster state by the scalar `500`. -/
private lemma dcOp_mulVec_gsVec : dcOp *ᵥ gsVec = (500 : ℂ) • gsVec := by
  rw [dcOp_eq, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, oLoc_sum_sq_mulVec_gsVec,
    Matrix.mulVec_smul, hLoc_sum_mulVec_gsVec, smul_smul, smul_smul]
  norm_num

/-- The double commutator acts on the normalized ground state by the same scalar `500`. -/
private lemma dcOp_mulVec_gsState : dcOp *ᵥ gsState = (500 : ℂ) • gsState := by
  rw [gsState, unitNormalize, Matrix.mulVec_smul, dcOp_mulVec_gsVec, smul_comm]

/-- **The expectation value is exactly `500`.**  This is the left-hand side of Tasaki
eq. (3.4.13) for the model, evaluated exactly (not merely bounded). -/
private lemma doubleCommutator_rayleighOnVec_gsState_eq_five_hundred :
    rayleighOnVec dcOp gsState = 500 := by
  rw [rayleighOnVec, dcOp_mulVec_gsState, dotProduct_smul, smul_eq_mul,
    gsState_dotProduct_self_eq_one, mul_one]
  norm_num

/-- **The printed constant of eq. (3.4.13) is exceeded**: at `d = 1`, `r = 1`, `h₀ = o₀ = 1`,
`L = 5` the printed `4 (2r+1)^d (4r+1)^d h₀ o₀² L^d` is `300`, while the model's expectation is
`500`. -/
private lemma doubleCommutator_rayleighOnVec_gsState_gt_printed_constant :
    4 * (2 * (1 : ℝ) + 1) ^ 1 * (4 * (1 : ℝ) + 1) ^ 1 * 1 * 1 ^ 2 * (5 : ℝ) ^ 1
      < rayleighOnVec dcOp gsState := by
  rw [doubleCommutator_rayleighOnVec_gsState_eq_five_hundred]
  norm_num

/-! ## The counterexample -/

/-- **Counterexample to the printed constant of Tasaki eq. (3.4.13), as literally quantified.**
The explicit `d = 1`, `r = 1`, `L = 5` spin-1/2 ring model of this file (`hLoc`, `oLoc`, `gsState`)
satisfies every hypothesis of Problem 3.4.a (range-1 support, unit local-term norms, normalized
ground state at `E₀ = −5`) yet has `⟨Φ_GS|[Ô,[Ĥ,Ô]]|Φ_GS⟩ = 500`, exceeding the printed constant
`4(2·1+1)^1(4·1+1)^1·1·1²·5^1 = 300` of eq. (3.4.13) as literally quantified. The repository's own
proved bound `4(4·1+1)^1(8·1+1)^1·1·1²·5^1 = 500` (`RangeLocalDoubleCommutatorBound.lean`) is
attained exactly, and is unaffected. Whether the printed constant holds when `L > 4r+1` is open. -/
theorem tasaki_problem_3_4_a_printed_constant_counterexample :
    (∀ x : Fin 5, SupportedOnS (siteBall (ringDist 5) 1 x) (hLoc x)) ∧
      (∀ x : Fin 5, SupportedOnS (siteBall (ringDist 5) 1 x) (oLoc x)) ∧
      (∀ x : Fin 5, manyBodyOperatorNormS (hLoc x) ≤ 1) ∧
      (∀ x : Fin 5, manyBodyOperatorNormS (oLoc x) ≤ 1) ∧
      star gsState ⬝ᵥ gsState = 1 ∧
      IsGroundEnergy (∑ x, hLoc x) (-5) ∧
      (∑ x, hLoc x) *ᵥ gsState = ((-5 : ℝ) : ℂ) • gsState ∧
      rayleighOnVec
          ((∑ x, oLoc x) * ((∑ b, hLoc b) * (∑ x, oLoc x) - (∑ x, oLoc x) * (∑ b, hLoc b))
            - ((∑ b, hLoc b) * (∑ x, oLoc x) - (∑ x, oLoc x) * (∑ b, hLoc b)) * (∑ x, oLoc x))
          gsState = 500 ∧
      4 * (2 * (1 : ℝ) + 1) ^ 1 * (4 * (1 : ℝ) + 1) ^ 1 * 1 * 1 ^ 2 * (5 : ℝ) ^ 1
        < rayleighOnVec
            ((∑ x, oLoc x) * ((∑ b, hLoc b) * (∑ x, oLoc x) - (∑ x, oLoc x) * (∑ b, hLoc b))
              - ((∑ b, hLoc b) * (∑ x, oLoc x) - (∑ x, oLoc x) * (∑ b, hLoc b)) * (∑ x, oLoc x))
            gsState := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hLoc_supportedOnS_siteBall
  · exact oLoc_supportedOnS_siteBall
  · exact hLoc_manyBodyOperatorNormS_le_one
  · exact oLoc_manyBodyOperatorNormS_le_one
  · exact gsState_dotProduct_self_eq_one
  · exact hLoc_sum_isGroundEnergy
  · exact hLoc_sum_mulVec_gsState_eq_smul
  · exact doubleCommutator_rayleighOnVec_gsState_eq_five_hundred
  · exact doubleCommutator_rayleighOnVec_gsState_gt_printed_constant

end LatticeSystem.Tests.PrintedConstantCounterexample
