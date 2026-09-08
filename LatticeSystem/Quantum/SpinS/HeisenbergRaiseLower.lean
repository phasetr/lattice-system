import LatticeSystem.Quantum.SpinS.Heisenberg
import LatticeSystem.Quantum.SpinS.RaiseLower

/-!
# Heisenberg matrix elements on raise/lower steps
(Tasaki §2.5 Phase B-γ γ-3 irreducibility prep)

For a raise/lower step `σ ↦ σ'` along a `G`-edge `(x, y)`, the
two-site formula `heisenbergHamiltonianS_apply_of_off_two_site_agree`
collapses the Heisenberg matrix element to a single bond contribution:

    `H σ' σ = (J(x, y) + J(y, x)) · (Ŝ_x · Ŝ_y) σ' σ`.

Combined with the strict positivity of `(Ŝ_x · Ŝ_y) σ' σ` on the
raise/lower pattern (PR #803), this gives a direct way to evaluate
the Heisenberg matrix element on a raise/lower-step neighbour and
read off its non-vanishing.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- For a `RaiseLowerStepS G σ σ'` (extracted witness `(x, y)`), the
Heisenberg matrix element `H σ' σ` collapses to the single-bond
two-site formula

    `H σ' σ = (J(x, y) + J(y, x)) · (Ŝ_x · Ŝ_y) σ' σ`. -/
theorem heisenbergHamiltonianS_apply_of_raiseLowerStepS_witness
    (J : V → V → ℂ) (N : ℕ)
    {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    {x y : V} (hadj : G.Adj x y)
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (heisenbergHamiltonianS J N) σ' σ =
      (J x y + J y x) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ := by
  have hxy : x ≠ y := fun heq => G.loopless.irrefl _ (heq ▸ hadj)
  -- σ' ≠ σ from raising/lowering at x.
  have hne : σ' ≠ σ := by
    intro heq
    rcases hsh with ⟨hxr, _⟩ | ⟨hxl, _⟩
    · have : (σ' x).val = (σ x).val := by rw [heq]
      omega
    · have : (σ' x).val = (σ x).val := by rw [heq]
      omega
  exact heisenbergHamiltonianS_apply_of_off_two_site_agree
    (Λ := V) hxy N hne hagree

/-- **Real part of the Heisenberg matrix element on a raise/lower step.**
For a `RaiseLowerStepS G σ σ'` (extracted witness `(x, y)`) with a real
symmetric coupling at that bond, the two-site collapse turns into the real
identity

    `Re (H σ' σ) = 2 · Re J(x, y) · Re (Ŝ_x · Ŝ_y) σ' σ`.

No sign hypothesis on `J` enters, so both the antiferromagnetic
(`Re J(x, y) > 0`) and the ferromagnetic (`Re J(x, y) < 0`) readings of the
entry follow by weighting the strictly positive bond entry
`spinSDot_apply_re_pos_of_raiseLowerStepS_witness` with this factor.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed., Springer, 2020), Proof of Theorem 2.2, properties (ii)-(iii),
pp. 40-42; §2.4 Theorem 2.1, p. 34. -/
theorem heisenbergHamiltonianS_apply_re_eq_of_raiseLowerStepS_witness
    {J : V → V → ℂ} (N : ℕ)
    {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    {x y : V} (hadj : G.Adj x y)
    (hJ_real : (J x y).im = 0) (hJ_sym : J x y = J y x)
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    ((heisenbergHamiltonianS J N) σ' σ).re =
      2 * (J x y).re * ((spinSDot x y N : ManyBodyOpS V N) σ' σ).re := by
  rw [heisenbergHamiltonianS_apply_of_raiseLowerStepS_witness J N hadj hsh
    hagree]
  -- (J x y + J y x) = 2 * (J x y) (real symmetric), a real scalar.
  rw [show J x y + J y x = 2 * J x y from by rw [← hJ_sym]; ring]
  rw [show (2 : ℂ) * J x y = ((2 * (J x y).re : ℝ) : ℂ) from by
    apply Complex.ext
    · simp
    · simp [hJ_real]]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]

/-- For a `RaiseLowerStepS G σ σ'` along `(x, y)` with real symmetric
coupling `J` and `(J x y).re > 0`, the Heisenberg matrix element
`H σ' σ` has *strictly positive* real part:

    `0 < Re (H σ' σ)`.

Combines the real collapse
`heisenbergHamiltonianS_apply_re_eq_of_raiseLowerStepS_witness` with
`spinSDot_apply_re_pos_of_raiseLowerStepS_witness`: both factors of
`2 · (J x y).re · Re(spinSDot σ' σ)` are strictly positive. -/
theorem heisenbergHamiltonianS_apply_re_pos_of_raiseLowerStepS_witness
    {J : V → V → ℂ} (N : ℕ)
    {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    {x y : V} (hadj : G.Adj x y)
    (hJ_real : (J x y).im = 0) (hJ_pos : 0 < (J x y).re)
    (hJ_sym : J x y = J y x)
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    0 < ((heisenbergHamiltonianS J N) σ' σ).re := by
  rw [heisenbergHamiltonianS_apply_re_eq_of_raiseLowerStepS_witness N hadj
    hJ_real hJ_sym hsh hagree]
  -- Both factors positive: (2 * (J x y).re) > 0 and Re(spinSDot σ' σ) > 0.
  have hspin_pos :
      0 < ((spinSDot x y N : ManyBodyOpS V N) σ' σ).re :=
    spinSDot_apply_re_pos_of_raiseLowerStepS_witness hadj hsh hagree
  have hJ2 : 0 < 2 * (J x y).re := by linarith
  positivity

/-- For a `RaiseLowerStepS G σ σ'` along `(x, y)` with real symmetric
coupling `J` and `(J x y).re > 0`, the Heisenberg matrix element is
non-zero. -/
theorem heisenbergHamiltonianS_apply_ne_zero_of_raiseLowerStepS_witness
    {J : V → V → ℂ} (N : ℕ)
    {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    {x y : V} (hadj : G.Adj x y)
    (hJ_real : (J x y).im = 0) (hJ_pos : 0 < (J x y).re)
    (hJ_sym : J x y = J y x)
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (heisenbergHamiltonianS J N) σ' σ ≠ 0 := by
  intro heq
  have hpos := heisenbergHamiltonianS_apply_re_pos_of_raiseLowerStepS_witness N
    hadj hJ_real hJ_pos hJ_sym hsh hagree
  rw [heq] at hpos
  simp at hpos

end LatticeSystem.Quantum
