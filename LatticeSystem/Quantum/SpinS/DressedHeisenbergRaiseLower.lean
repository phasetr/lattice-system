import LatticeSystem.Quantum.SpinS.HeisenbergRaiseLower
import LatticeSystem.Quantum.SpinS.DressedHeisenberg

/-!
# Marshall-dressed Heisenberg matrix elements on raise/lower steps
(Tasaki §2.5 Phase B-γ γ-3 irreducibility prep)

For a bipartite sublattice indicator `A x ≠ A y` on a graph edge
`(x, y)`, a raise/lower step `σ ↦ σ'` flips the Marshall sign factor
to `-1`. Combined with the strict positivity of the Heisenberg
matrix element on the same step (PR #805), the dressed-Heisenberg
matrix element is *strictly negative*:

    `Re (dressedHeisenbergS A J N σ' σ) < 0`.

This is the "non-zero off-diagonal entries" input needed to apply
Perron–Frobenius to the dressed matrix on a magnetization subspace
(Tasaki Theorem 2.2 for general spin).

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [DecidableEq V] in
/-- Helper: a raise/lower-step witness `(x, y)` with bipartite
sublattice (`A x ≠ A y`) gives a `-1` Marshall sign factor:

    `marshallSignS A σ' * marshallSignS A σ = -1`. -/
private theorem marshallSignS_mul_eq_neg_one_of_raiseLowerStepS_witness
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (hAne : A x ≠ A y)
    {σ' σ : V → Fin (N + 1)}
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    marshallSignS A σ' * marshallSignS A σ = -1 := by
  -- Decompose into 4 (A x, A y) cases via decidability.
  have hxbool : A x = true ∨ A x = false := by cases A x <;> simp
  have hybool : A y = true ∨ A y = false := by cases A y <;> simp
  rcases hxbool with hAx | hAx <;> rcases hybool with hAy | hAy
  · exact (hAne (hAx.trans hAy.symm)).elim
  · -- A x = true, A y = false: x ∈ A. Need Odd at x.
    apply marshallSignS_mul_of_agree_off_two_site_bipartite_x A hxy hAx hAy
      hagree
    rcases hsh with ⟨hxr, _hyl⟩ | ⟨hxl, _hyr⟩
    · rw [show (σ' x).val = (σ x).val + 1 from hxr.symm]
      rw [show (σ x).val + 1 + (σ x).val = 2 * (σ x).val + 1 from by ring]
      exact ⟨(σ x).val, rfl⟩
    · rw [show (σ' x).val = (σ x).val - 1 from by omega]
      rw [show (σ x).val - 1 + (σ x).val = 2 * (σ x).val - 1 from by
        have hxv : (σ x).val ≥ 1 := by omega
        omega]
      refine ⟨(σ x).val - 1, ?_⟩
      have hxv : (σ x).val ≥ 1 := by omega
      omega
  · -- A x = false, A y = true: y ∈ A. Need Odd at y.
    apply marshallSignS_mul_of_agree_off_two_site_bipartite_y A hxy hAx hAy
      hagree
    rcases hsh with ⟨_hxr, hyl⟩ | ⟨_hxl, hyr⟩
    · rw [show (σ' y).val = (σ y).val - 1 from by omega]
      rw [show (σ y).val - 1 + (σ y).val = 2 * (σ y).val - 1 from by
        have hyv : (σ y).val ≥ 1 := by omega
        omega]
      refine ⟨(σ y).val - 1, ?_⟩
      have hyv : (σ y).val ≥ 1 := by omega
      omega
    · rw [show (σ' y).val = (σ y).val + 1 from hyr.symm]
      rw [show (σ y).val + 1 + (σ y).val = 2 * (σ y).val + 1 from by ring]
      exact ⟨(σ y).val, rfl⟩
  · exact (hAne (hAx.trans hAy.symm)).elim

/-- For a `RaiseLowerStepS G σ σ'` along a *bipartite* edge
(`A x ≠ A y`) with real symmetric coupling `(J x y).re > 0`, the
dressed Heisenberg matrix element has *strictly negative* real part:

    `Re (dressedHeisenbergS A J N σ' σ) < 0`.

Proof: dressed = sign σ' · sign σ · H σ' σ;
- `sign σ' · sign σ = -1` (bipartite raise/lower step);
- `Re (H σ' σ) > 0` (PR #805);
- so `Re (dressed) = -1 · Re(H σ' σ) < 0`. -/
theorem dressedHeisenbergS_apply_re_neg_of_raiseLowerStepS_witness
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ)
    {G : SimpleGraph V} {σ' σ : V → Fin (N + 1)}
    {x y : V} (hadj : G.Adj x y) (hAne : A x ≠ A y)
    (hJ_real : (J x y).im = 0) (hJ_pos : 0 < (J x y).re)
    (hJ_sym : J x y = J y x)
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (dressedHeisenbergS A J N σ' σ).re < 0 := by
  have hxy : x ≠ y := fun heq => G.loopless.irrefl _ (heq ▸ hadj)
  unfold dressedHeisenbergS
  -- Sign factor = -1.
  have hsign : marshallSignS A σ' * marshallSignS A σ = -1 :=
    marshallSignS_mul_eq_neg_one_of_raiseLowerStepS_witness A hxy hAne hsh hagree
  -- H σ' σ has positive real part.
  have hH_pos : 0 < ((heisenbergHamiltonianS J N) σ' σ).re :=
    heisenbergHamiltonianS_apply_re_pos_of_raiseLowerStepS_witness N hadj
      hJ_real hJ_pos hJ_sym hsh hagree
  -- After unfold dressedHeisenbergS A J N σ' σ:
  -- = marshallSignS A σ' * marshallSignS A σ * (heisenbergHamiltonianS J N) σ' σ
  rw [show marshallSignS A σ' * marshallSignS A σ *
        (heisenbergHamiltonianS J N) σ' σ =
      (marshallSignS A σ' * marshallSignS A σ) *
        (heisenbergHamiltonianS J N) σ' σ from by ring]
  rw [hsign]
  rw [show ((-1 : ℂ) * (heisenbergHamiltonianS J N) σ' σ).re =
        -((heisenbergHamiltonianS J N) σ' σ).re from by
    rw [Complex.mul_re]
    simp]
  linarith

/-- For a `RaiseLowerStepS G σ σ'` along a bipartite edge `(x, y)`
with positive real symmetric coupling, the dressed Heisenberg matrix
element is non-zero. -/
theorem dressedHeisenbergS_apply_ne_zero_of_raiseLowerStepS_witness
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ)
    {G : SimpleGraph V} {σ' σ : V → Fin (N + 1)}
    {x y : V} (hadj : G.Adj x y) (hAne : A x ≠ A y)
    (hJ_real : (J x y).im = 0) (hJ_pos : 0 < (J x y).re)
    (hJ_sym : J x y = J y x)
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    dressedHeisenbergS A J N σ' σ ≠ 0 := by
  intro heq
  have hneg := dressedHeisenbergS_apply_re_neg_of_raiseLowerStepS_witness A N
    hadj hAne hJ_real hJ_pos hJ_sym hsh hagree
  rw [heq] at hneg
  simp at hneg

/-! ## Real-matrix versions -/

/-- The real-valued dressed Heisenberg matrix entry on a bipartite
raise/lower step is *strictly negative*. -/
theorem dressedHeisenbergSReMatrix_apply_neg_of_raiseLowerStepS_witness
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ)
    {G : SimpleGraph V} {σ' σ : V → Fin (N + 1)}
    {x y : V} (hadj : G.Adj x y) (hAne : A x ≠ A y)
    (hJ_real : (J x y).im = 0) (hJ_pos : 0 < (J x y).re)
    (hJ_sym : J x y = J y x)
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    dressedHeisenbergSReMatrix A J N σ' σ < 0 := by
  rw [dressedHeisenbergSReMatrix_apply]
  exact dressedHeisenbergS_apply_re_neg_of_raiseLowerStepS_witness A N hadj
    hAne hJ_real hJ_pos hJ_sym hsh hagree

/-- The real-valued dressed Heisenberg matrix entry on a bipartite
raise/lower step is non-zero. -/
theorem dressedHeisenbergSReMatrix_apply_ne_zero_of_raiseLowerStepS_witness
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ)
    {G : SimpleGraph V} {σ' σ : V → Fin (N + 1)}
    {x y : V} (hadj : G.Adj x y) (hAne : A x ≠ A y)
    (hJ_real : (J x y).im = 0) (hJ_pos : 0 < (J x y).re)
    (hJ_sym : J x y = J y x)
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    dressedHeisenbergSReMatrix A J N σ' σ ≠ 0 := by
  intro heq
  have hneg := dressedHeisenbergSReMatrix_apply_neg_of_raiseLowerStepS_witness
    A N hadj hAne hJ_real hJ_pos hJ_sym hsh hagree
  rw [heq] at hneg
  simp at hneg

end LatticeSystem.Quantum
