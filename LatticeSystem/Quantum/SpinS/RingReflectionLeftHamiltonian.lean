/-
The left-half bond Hamiltonian of the ring is left-supported
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 16).

The left part `H_L` of the Dyson–Lieb–Simon decomposition of the ring antiferromagnet is the bond
Hamiltonian restricted to the left half: a Heisenberg Hamiltonian whose coupling vanishes unless
both sites lie in `{0, …, n−1}`.  Any such Hamiltonian is left-supported (`B(H_left) ⊗ I_right`): it
is a sum of scalar multiples of two-site dot products `Ŝ_x · Ŝ_y` with both sites in the left half.
This file records the general support lemma `heisenbergHamiltonianS_supportedOnLeft`, the concrete
left coupling `ringLeftCoupling`, and the resulting left-supported `ringLeftHamiltonian` — the `H_L`
that feeds the ring DLS decomposition (`RingReflectionRingInstance`).
-/
import LatticeSystem.Quantum.SpinS.RingReflectionRingInstance
import LatticeSystem.Quantum.SpinS.ShastryNoSSB

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- Left-supportedness is closed under finite sums. -/
theorem SupportedOnLeftS.sum {ι : Type*} (s : Finset ι) (f : ι → ManyBodyOpS (Fin (2 * n)) N)
    (h : ∀ i ∈ s, SupportedOnLeftS n N (f i)) : SupportedOnLeftS n N (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using SupportedOnLeftS.zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- **A Heisenberg Hamiltonian with left-supported coupling is left-supported.**  If the coupling
`J x y` vanishes unless both `x` and `y` lie in the left half, then `heisenbergHamiltonianS J N` is
left-supported. -/
theorem heisenbergHamiltonianS_supportedOnLeft {J : Fin (2 * n) → Fin (2 * n) → ℂ}
    (hJ : ∀ x y, J x y ≠ 0 → (x : ℕ) < n ∧ (y : ℕ) < n) :
    SupportedOnLeftS n N (heisenbergHamiltonianS J N) := by
  rw [heisenbergHamiltonianS_def]
  refine SupportedOnLeftS.sum _ _ (fun x _ => SupportedOnLeftS.sum _ _ (fun y _ => ?_))
  by_cases h : J x y = 0
  · simp only [h, zero_smul]
    exact SupportedOnLeftS.zero
  · obtain ⟨hx, hy⟩ := hJ x y h
    exact (spinSDot_supportedOnLeft hx hy).smul (J x y)

/-- The ring coupling restricted to the left half: the nearest-neighbor coupling kept only between
left-half sites. -/
noncomputable def ringLeftCoupling (n : ℕ) (x y : Fin (2 * n)) : ℂ :=
  if (x : ℕ) < n ∧ (y : ℕ) < n then ringCoupling (2 * n) x y else 0

/-- The left coupling is supported on the left half. -/
theorem ringLeftCoupling_ne_zero {x y : Fin (2 * n)} (h : ringLeftCoupling n x y ≠ 0) :
    (x : ℕ) < n ∧ (y : ℕ) < n := by
  by_contra hc
  rw [ringLeftCoupling, if_neg hc] at h
  exact h rfl

/-- The **left-half bond Hamiltonian** of the ring: the bond Hamiltonian restricted to the left
half, the `H_L` of the DLS decomposition. -/
noncomputable def ringLeftHamiltonian (n N : ℕ) : ManyBodyOpS (Fin (2 * n)) N :=
  heisenbergHamiltonianS (ringLeftCoupling n) N

/-- The left-half bond Hamiltonian is left-supported. -/
theorem ringLeftHamiltonian_supportedOnLeft : SupportedOnLeftS n N (ringLeftHamiltonian n N) :=
  heisenbergHamiltonianS_supportedOnLeft (fun _ _ h => ringLeftCoupling_ne_zero h)

end LatticeSystem.Quantum
