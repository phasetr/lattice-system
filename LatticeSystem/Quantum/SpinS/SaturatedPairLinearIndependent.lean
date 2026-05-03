import LatticeSystem.Quantum.SpinS.MagnetizationDirectSum
import LatticeSystem.Quantum.SpinS.LadderIterateNonvanishing

/-!
# Linear independence of the first ladder pair on the saturated ferromagnet

For `0 < N` and `[Nonempty V]`, the pair
`{|σ_⊤⟩, Ŝ^-_{tot} · |σ_⊤⟩}` of all-up state and once-lowered all-up
state is `LinearIndependent ℂ`. They are eigenvectors of
`Ŝ^z_{tot}` at the distinct eigenvalues `m_max` and `m_max − 1`,
both non-zero, hence linearly independent by mathlib's
`Module.End.eigenvectors_linearIndependent'`.

This is the smallest non-trivial linear-independence statement on
the Tasaki §2.4 saturated-ferromagnet ladder; it scales (by induction)
to the full `(2m_max + 1)`-vector family
`{(Ŝ^-_{tot})^k · |σ_⊤⟩ : k = 0, …, 2m_max}` once the higher-`k`
non-vanishing extension of PR #890 is in hand.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Non-vanishing of the all-aligned state -/

/-- The all-aligned state is non-zero: its value at the all-aligned
configuration is `1`. -/
theorem allAlignedStateS_ne_zero (c : Fin (N + 1)) :
    (allAlignedStateS V N c) ≠ 0 := by
  intro h
  have hself : (allAlignedStateS V N c) (allAlignedConfigS V N c) = 1 := by
    unfold allAlignedStateS
    exact basisVecS_self _
  have hzero : (allAlignedStateS V N c) (allAlignedConfigS V N c) = 0 := by
    rw [h]; rfl
  rw [hself] at hzero
  exact one_ne_zero hzero

/-! ## Eigenspace membership lemmas -/

/-- The all-up state lies in the `Ŝ^z_{tot}`-eigenspace at the highest
weight `|V|·N/2`. -/
theorem allAlignedStateS_zero_mem_eigenspace_mMax :
    (allAlignedStateS V N (0 : Fin (N + 1))) ∈
      Module.End.eigenspace
          ((totalSpinSOp3 V N).mulVecLin)
          ((Fintype.card V : ℂ) * (N : ℂ) / 2) := by
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
  rw [totalSpinSOp3_mulVec_allAlignedStateS,
    magEigenvalueS_allAlignedConfigS]
  rw [show ((0 : Fin (N + 1)).val : ℂ) = 0 from by simp]
  congr 1
  ring

/-- The once-lowered all-up state lies in the `Ŝ^z_{tot}`-eigenspace
at `|V|·N/2 − 1`. -/
theorem totalSpinSOpMinus_mulVec_allAlignedStateS_zero_mem_eigenspace_mMaxSubOne :
    (totalSpinSOpMinus V N).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1))) ∈
      Module.End.eigenspace
          ((totalSpinSOp3 V N).mulVecLin)
          ((Fintype.card V : ℂ) * (N : ℂ) / 2 - 1) := by
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
  exact totalSpinSOp3_mulVec_totalSpinSOpMinus_mulVec_allAlignedStateS_zero

/-- Symmetric: the all-down state lies in the `Ŝ^z_{tot}`-eigenspace
at the lowest weight `−|V|·N/2`. -/
theorem allAlignedStateS_last_mem_eigenspace_negMMax :
    (allAlignedStateS V N (Fin.last N)) ∈
      Module.End.eigenspace
          ((totalSpinSOp3 V N).mulVecLin)
          (-((Fintype.card V : ℂ) * (N : ℂ) / 2)) := by
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
  rw [totalSpinSOp3_mulVec_allAlignedStateS,
    magEigenvalueS_allAlignedConfigS]
  rw [show ((Fin.last N).val : ℂ) = N from by simp [Fin.last]]
  congr 1
  ring

/-- Symmetric: the once-raised all-down state lies in the
`Ŝ^z_{tot}`-eigenspace at `−|V|·N/2 + 1`. -/
theorem totalSpinSOpPlus_mulVec_allAlignedStateS_last_mem_eigenspace_negMMaxAddOne :
    (totalSpinSOpPlus V N).mulVec
        (allAlignedStateS V N (Fin.last N)) ∈
      Module.End.eigenspace
          ((totalSpinSOp3 V N).mulVecLin)
          (-((Fintype.card V : ℂ) * (N : ℂ) / 2) + 1) := by
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
  exact totalSpinSOp3_mulVec_totalSpinSOpPlus_mulVec_allAlignedStateS_last

/-! ## Linear independence of the pair -/

/-- **Linear independence of the first ladder pair** (lowering side):
for `0 < N` and `[Nonempty V]`, the pair
`{|σ_⊤⟩, Ŝ^-_{tot} · |σ_⊤⟩}` is `LinearIndependent ℂ`.

Proof: both are non-zero `Ŝ^z_{tot}`-eigenvectors at distinct
eigenvalues (`m_max` and `m_max − 1`); apply mathlib's
`Module.End.eigenvectors_linearIndependent'`. -/
theorem allAlignedStateS_zero_totalSpinSOpMinus_mulVec_linearIndependent
    [Nonempty V] (hN : 0 < N) :
    LinearIndependent ℂ
      (![allAlignedStateS V N (0 : Fin (N + 1)),
         (totalSpinSOpMinus V N).mulVec
           (allAlignedStateS V N (0 : Fin (N + 1)))]) := by
  let f : Module.End ℂ ((V → Fin (N + 1)) → ℂ) :=
    (totalSpinSOp3 V N).mulVecLin
  let μ : Fin 2 → ℂ := ![(Fintype.card V : ℂ) * (N : ℂ) / 2,
    (Fintype.card V : ℂ) * (N : ℂ) / 2 - 1]
  have hμ_inj : Function.Injective μ := by
    intros i j hij
    have h_ne : (Fintype.card V : ℂ) * (N : ℂ) / 2 ≠
        (Fintype.card V : ℂ) * (N : ℂ) / 2 - 1 := by
      intro h
      have : (1 : ℂ) = 0 := by linear_combination h
      exact one_ne_zero this
    match i, j with
    | 0, 0 => rfl
    | 0, 1 => exact absurd hij h_ne
    | 1, 0 => exact absurd hij.symm h_ne
    | 1, 1 => rfl
  have h_eigenvec : ∀ i, Module.End.HasEigenvector f (μ i)
      (![allAlignedStateS V N (0 : Fin (N + 1)),
         (totalSpinSOpMinus V N).mulVec
           (allAlignedStateS V N (0 : Fin (N + 1)))] i) := by
    intro i
    match i with
    | 0 => exact ⟨allAlignedStateS_zero_mem_eigenspace_mMax,
        allAlignedStateS_ne_zero _⟩
    | 1 => exact ⟨totalSpinSOpMinus_mulVec_allAlignedStateS_zero_mem_eigenspace_mMaxSubOne,
        totalSpinSOpMinus_mulVec_allAlignedStateS_zero_ne_zero hN⟩
  exact Module.End.eigenvectors_linearIndependent' f μ hμ_inj _ h_eigenvec

/-- **Linear independence of the first ladder pair** (raising side):
for `0 < N` and `[Nonempty V]`, the pair
`{|σ_⊥⟩, Ŝ^+_{tot} · |σ_⊥⟩}` is `LinearIndependent ℂ`. -/
theorem allAlignedStateS_last_totalSpinSOpPlus_mulVec_linearIndependent
    [Nonempty V] (hN : 0 < N) :
    LinearIndependent ℂ
      (![allAlignedStateS V N (Fin.last N),
         (totalSpinSOpPlus V N).mulVec
           (allAlignedStateS V N (Fin.last N))]) := by
  let f : Module.End ℂ ((V → Fin (N + 1)) → ℂ) :=
    (totalSpinSOp3 V N).mulVecLin
  let μ : Fin 2 → ℂ := ![-((Fintype.card V : ℂ) * (N : ℂ) / 2),
    -((Fintype.card V : ℂ) * (N : ℂ) / 2) + 1]
  have hμ_inj : Function.Injective μ := by
    intros i j hij
    have h_ne : -((Fintype.card V : ℂ) * (N : ℂ) / 2) ≠
        -((Fintype.card V : ℂ) * (N : ℂ) / 2) + 1 := by
      intro h
      have : (1 : ℂ) = 0 := by linear_combination -h
      exact one_ne_zero this
    match i, j with
    | 0, 0 => rfl
    | 0, 1 => exact absurd hij h_ne
    | 1, 0 => exact absurd hij.symm h_ne
    | 1, 1 => rfl
  have h_eigenvec : ∀ i, Module.End.HasEigenvector f (μ i)
      (![allAlignedStateS V N (Fin.last N),
         (totalSpinSOpPlus V N).mulVec
           (allAlignedStateS V N (Fin.last N))] i) := by
    intro i
    match i with
    | 0 => exact ⟨allAlignedStateS_last_mem_eigenspace_negMMax,
        allAlignedStateS_ne_zero _⟩
    | 1 => exact ⟨totalSpinSOpPlus_mulVec_allAlignedStateS_last_mem_eigenspace_negMMaxAddOne,
        totalSpinSOpPlus_mulVec_allAlignedStateS_last_ne_zero hN⟩
  exact Module.End.eigenvectors_linearIndependent' f μ hμ_inj _ h_eigenvec

end LatticeSystem.Quantum
