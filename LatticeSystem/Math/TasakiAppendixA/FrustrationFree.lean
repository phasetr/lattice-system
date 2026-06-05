import LatticeSystem.Math.RayleighPosSemidefKernel
import Mathlib.Analysis.Matrix.Order

/-!
# Tasaki Appendix A.2.3: frustration-free Hamiltonians (Lemmas A.9, A.10)

Tasaki's two characterizations of a *frustration-free* Hamiltonian `Ĥ = Σ_j ĥ_j` with each
local term bounded below, `ĥ_j ≥ ε_j` (here `(ĥ_j − ε_j) ≥ 0`, i.e. `(ĥ_j − ε_j • 1)`
positive-semidefinite).  These are the linear-algebra core behind the §11.3 / §11.4 flat-band
ground-state arguments; unlike the min–max theorem (A.7) they are fully proved.

* **Lemma A.9** (frustration-free 1): if a state `Φ` satisfies `ĥ_j Φ = ε_j Φ` for every `j`,
  then `Φ` is a ground state of `Ĥ` with energy `Σ_j ε_j` — concretely `Ĥ − (Σ_j ε_j) ≥ 0`
  (so `Σ_j ε_j` is a lower bound) and `Ĥ Φ = (Σ_j ε_j) Φ` (attained).
* **Lemma A.10** (frustration-free 2, converse): if the ground-state energy is `Σ_j ε_j`,
  i.e. `Ĥ Φ = (Σ_j ε_j) Φ`, then `Φ` is a simultaneous eigenstate, `ĥ_j Φ = ε_j Φ` for all `j`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.2.3, Lemmas A.9–A.10, pp. 469–470.
-/

namespace LatticeSystem.Math

open Matrix LatticeSystem.Quantum
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*}

omit [Fintype n] in
/-- `(∑ h j) − (∑ ε j) • 1 = ∑ (h j − ε j • 1)`. -/
private theorem sub_sum_smul_one (s : Finset ι) (h : ι → Matrix n n ℂ) (ε : ι → ℝ) :
    (∑ j ∈ s, h j) - ((∑ j ∈ s, ε j : ℝ) : ℂ) • (1 : Matrix n n ℂ)
      = ∑ j ∈ s, (h j - (ε j : ℂ) • (1 : Matrix n n ℂ)) := by
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
  push_cast
  rfl

omit [DecidableEq n] in
/-- `(∑ h j) *ᵥ Φ = ∑ (h j *ᵥ Φ)`. -/
private theorem sum_mulVec (s : Finset ι) (h : ι → Matrix n n ℂ) (Φ : n → ℂ) :
    (∑ j ∈ s, h j).mulVec Φ = ∑ j ∈ s, (h j).mulVec Φ := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih => rw [Finset.sum_cons, Finset.sum_cons, Matrix.add_mulVec, ih]

/-- **Tasaki Lemma A.9 (frustration-free Hamiltonian 1).**  For `Ĥ = ∑_j ĥ_j` with each local
term bounded below by `ε_j` (`(ĥ_j − ε_j • 1) ≥ 0`), a simultaneous eigenstate `Φ`
(`ĥ_j Φ = ε_j Φ` for all `j`) is a ground state at energy `∑_j ε_j`: the shifted Hamiltonian
`Ĥ − (∑_j ε_j) • 1` is positive-semidefinite (so `∑_j ε_j` lower-bounds the energy) and
`Ĥ Φ = (∑_j ε_j) Φ` (the bound is attained). -/
theorem frustration_free_isGroundState (s : Finset ι) (h : ι → Matrix n n ℂ) (ε : ι → ℝ)
    (Φ : n → ℂ) (hlb : ∀ j ∈ s, (h j - (ε j : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (heig : ∀ j ∈ s, (h j).mulVec Φ = (ε j : ℂ) • Φ) :
    ((∑ j ∈ s, h j) - ((∑ j ∈ s, ε j : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosSemidef ∧
      (∑ j ∈ s, h j).mulVec Φ = ((∑ j ∈ s, ε j : ℝ) : ℂ) • Φ := by
  refine ⟨?_, ?_⟩
  · rw [sub_sum_smul_one]
    exact Finset.sum_induction _ _ (fun _ _ => Matrix.PosSemidef.add) (by simpa using
      (Matrix.PosSemidef.zero (n := n))) hlb
  · rw [sum_mulVec, Finset.sum_congr rfl heig, ← Finset.sum_smul]
    push_cast
    rfl

/-- **Tasaki Lemma A.10 (frustration-free Hamiltonian 2, the converse).**  For `Ĥ = ∑_j ĥ_j`
with each local term bounded below by `ε_j`, if the ground-state energy is attained at
`∑_j ε_j` — i.e. `Ĥ Φ = (∑_j ε_j) Φ` — then `Φ` is a simultaneous eigenstate of every local
term, `ĥ_j Φ = ε_j Φ`.  (Each `⟨Φ|(ĥ_j − ε_j)|Φ⟩ ≥ 0`, their sum vanishes, hence each
vanishes, and Lemma A.11 gives `(ĥ_j − ε_j) Φ = 0`.) -/
theorem frustration_free_local_eigen (s : Finset ι) (h : ι → Matrix n n ℂ) (ε : ι → ℝ)
    (Φ : n → ℂ) (hlb : ∀ j ∈ s, (h j - (ε j : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (hgs : (∑ j ∈ s, h j).mulVec Φ = ((∑ j ∈ s, ε j : ℝ) : ℂ) • Φ) :
    ∀ j ∈ s, (h j).mulVec Φ = (ε j : ℂ) • Φ := by
  have hzeroVec :
      ((∑ j ∈ s, h j) - ((∑ j ∈ s, ε j : ℝ) : ℂ) • (1 : Matrix n n ℂ)).mulVec Φ = 0 := by
    rw [Matrix.sub_mulVec, hgs, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
  have hsum0 : ∑ j ∈ s, rayleighOnVec (h j - (ε j : ℂ) • (1 : Matrix n n ℂ)) Φ = 0 := by
    rw [← rayleighOnVec_sum, ← sub_sum_smul_one]
    unfold rayleighOnVec
    rw [hzeroVec, dotProduct_zero, Complex.zero_re]
  have hnn : ∀ j ∈ s, 0 ≤ rayleighOnVec (h j - (ε j : ℂ) • (1 : Matrix n n ℂ)) Φ := by
    intro j hj
    have hge := (hlb j hj).dotProduct_mulVec_nonneg Φ
    simpa using (Complex.le_def.mp hge).1
  intro j hj
  have hjz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0 j hj
  have hker := posSemidef_mulVec_eq_zero_of_rayleighOnVec_zero (hlb j hj) hjz
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hker
  exact hker

end LatticeSystem.Math
