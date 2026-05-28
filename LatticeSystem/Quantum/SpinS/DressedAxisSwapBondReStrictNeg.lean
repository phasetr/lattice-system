import LatticeSystem.Quantum.SpinS.AxisSwapBondReStrictPos
import LatticeSystem.Quantum.SpinS.DressedAxisSwapBondSign

/-!
# Strict negativity of the Marshall-dressed axis-swapped bond on a transverse witness

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Strict counterpart of `DressedAxisSwapBondSign.lean`.  On a `RaiseLowerStepS` witness at a bipartite
bond `{x, y}` (with `A`-site at either `x` or `y`) under case (i) strict (`−1 < λ.re ≤ 1` real),
the Marshall-dressed bond entry has **strictly negative real part**:

* the bare bond entry is strict positive real (#3790, `spinSDotXXZSwap_apply_re_pos_of_…_witness`);
* the bipartite Marshall sign product equals `−1` (#3760, via the odd `A`-site shift) for any `±1`
  move on the `A`-site;
* hence the dressed entry has real part `= − (strict positive) < 0`.

This is the per-bond ingredient of the full dressed-`Ĥ'` strict negativity on a transverse step
(PR5 / Tasaki §2.5 Theorem 2.4).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

omit [DecidableEq Λ] in
/-- Marshall dressing flips a real strictly-positive entry to strictly-negative across a bipartite
bond with `A`-site at `x` (`A x = true`, `A y = false`) and odd shift at `x`. -/
theorem dressed_entry_re_neg_bipartite_x
    (A : Λ → Bool) {x y : Λ} (hxy : x ≠ y) (hAx : A x = true) (hAy : A y = false)
    {σ' σ : Λ → Fin (N + 1)} (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hxod : Odd ((σ' x).val + (σ x).val))
    {z : ℂ} (hzp : 0 < z.re) :
    (marshallSignS A σ * marshallSignS A σ' * z).re < 0 := by
  rw [mul_comm (marshallSignS A σ) (marshallSignS A σ'),
    marshallSignS_mul_of_agree_off_two_site_bipartite_x A hxy hAx hAy h hxod,
    neg_one_mul, Complex.neg_re]
  linarith

omit [DecidableEq Λ] in
/-- Marshall dressing flips a real strictly-positive entry to strictly-negative across a bipartite
bond with `A`-site at `y` (`A x = false`, `A y = true`) and odd shift at `y`. -/
theorem dressed_entry_re_neg_bipartite_y
    (A : Λ → Bool) {x y : Λ} (hxy : x ≠ y) (hAx : A x = false) (hAy : A y = true)
    {σ' σ : Λ → Fin (N + 1)} (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hyod : Odd ((σ' y).val + (σ y).val))
    {z : ℂ} (hzp : 0 < z.re) :
    (marshallSignS A σ * marshallSignS A σ' * z).re < 0 := by
  rw [mul_comm (marshallSignS A σ) (marshallSignS A σ'),
    marshallSignS_mul_of_agree_off_two_site_bipartite_y A hxy hAx hAy h hyod,
    neg_one_mul, Complex.neg_re]
  linarith

/-- **Strict negativity** of the dressed axis-swapped bond on a `RaiseLowerStepS` witness on a
bipartite bond with `A`-site at `x` (case (i) strict). -/
theorem dressedAxisSwapped_bond_re_neg_bipartite_x_of_raiseLower_witness
    (A : Λ → Bool) {x y : Λ} (hxy : x ≠ y) (hAx : A x = true) (hAy : A y = false)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re)
    {σ' σ : Λ → Fin (N + 1)}
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (marshallSignS A σ * marshallSignS A σ' * spinSDotXXZSwap x y lam N σ' σ).re < 0 := by
  have hzp := spinSDotXXZSwap_apply_re_pos_of_raiseLowerStepS_witness hxy hlam hlb hsh h
  have hxod : Odd ((σ' x).val + (σ x).val) := by
    rcases hsh with ⟨hsx, _⟩ | ⟨hsx, _⟩ <;> · rw [Nat.odd_iff]; omega
  exact dressed_entry_re_neg_bipartite_x A hxy hAx hAy h hxod hzp

/-- **Strict negativity** of the dressed axis-swapped bond on a `RaiseLowerStepS` witness on a
bipartite bond with `A`-site at `y` (case (i) strict). -/
theorem dressedAxisSwapped_bond_re_neg_bipartite_y_of_raiseLower_witness
    (A : Λ → Bool) {x y : Λ} (hxy : x ≠ y) (hAx : A x = false) (hAy : A y = true)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re)
    {σ' σ : Λ → Fin (N + 1)}
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (marshallSignS A σ * marshallSignS A σ' * spinSDotXXZSwap x y lam N σ' σ).re < 0 := by
  have hzp := spinSDotXXZSwap_apply_re_pos_of_raiseLowerStepS_witness hxy hlam hlb hsh h
  have hyod : Odd ((σ' y).val + (σ y).val) := by
    rcases hsh with ⟨_, hsy⟩ | ⟨_, hsy⟩ <;> · rw [Nat.odd_iff]; omega
  exact dressed_entry_re_neg_bipartite_y A hxy hAx hAy h hyod hzp

end LatticeSystem.Quantum
