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

/-
Positive control (to be added and run after Green, then reverted — §3.3 of the design):

example : (500 : ℝ) ≠ 4 * (4 * (1 : ℝ) + 1) ^ 1 * (4 * (1 : ℝ) + 1) ^ 1 * 1 * 1 ^ 2 * (5 : ℝ) ^ 1 :=
  by norm_num

replacing the printed-constant literal `4*(2r+1)^1*(4r+1)^1*...` by the honest-bound literal
`4*(4r+1)^1*(4r+1)^1*...` (both equal 500) must turn the strict `<` conjunct into `500 < 500`,
which must fail to build; likewise substituting `499` for the exact value `500` in the eighth
conjunct must fail to build; likewise dropping the sign in any one anticommutation δ-lemma used by
the (future) proof of the eighth/ninth conjuncts must fail to build.
-/

end LatticeSystem.Tests.PrintedConstantCounterexample
