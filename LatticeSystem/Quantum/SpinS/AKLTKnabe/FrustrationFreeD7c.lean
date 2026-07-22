import LatticeSystem.Quantum.SpinS.AKLTBondProjection
import LatticeSystem.Quantum.SpinS.AKLTStringOrderTransfer
import LatticeSystem.Quantum.SpinS.MPSTheorem76Algebra

/-!
# Gate D7c (block ④-II): frustration-freeness of the ring VBS state

This module (Issue #5094; Tasaki §7.1.3–§7.1.4, Lemma 7.4 and Knabe's argument, pp. 186–190)
proves that the explicit periodic matrix-product AKLT state
`akltVBSState L` (`Quantum/SpinS/AKLTStringOrderDefs.lean:36`) lies in the kernel of the bond
spin-2 projection `P̂₂[Ŝ_x + Ŝ_{x+1}]` at **every** bond `x` of the ring, the wrap bond included:
the AKLT ring Hamiltonian is *frustration free* on it.

The route is the one fixed by the Gate D7a design, block ④-II (F0–F8):

* **F0** `ringSucc_eq_add_one` — the single point of contact between the production cyclic
  successor `ringSucc` (`AKLTBondProjection.lean:42`) and the group successor `x + 1` of `Fin L`.
* **F2** `akltVBSState_ne_zero` — the ring VBS state is nonzero for `2 ≤ L`, by the production
  norm formula `AKLTStringOrder.state_norm_pos` (`AKLTStringOrderTransfer.lean:718`).
* **F3** `akltVBSState_rotate` / `akltVBSState_shift` — the trace-product state is invariant under
  a one-step ring rotation, hence under any rotation.  Proved from `List.ofFn_succ'` (the `snoc`
  form of `List.ofFn`), the production `orderedProd_append` (`MPSTheorem76Algebra.lean:36`) and
  cyclicity of the matrix trace.
* **F4** `glueBond_shift` — rotating a glued bond configuration moves the bond to `x = 0`.
* **F5** `exists_bondSlice_eq_trace` — the *key structural fact*: for a periodic MPS state, every
  two-site bond slice is the linear functional `a ↦ tr (A^{a₀} A^{a₁} R)` of the two-site tensor,
  with a remainder matrix `R` independent of the bond configuration `a`.
* **F6** `akltTwoSiteTensor_eq` — the exact two-site tensor table
  `A^{a₀}A^{a₁} = !![¼Ψ_{↓↑}(a), sΨ_{↓↓}(a); −sΨ_{↑↑}(a), −¼Ψ_{↑↓}(a)]` with `s = (√2)⁻¹`, i.e.
  each of the four components of `A^{a₀}A^{a₁}` is a *multiple of a single VBS bond vector*
  `Ψ_{σσ'}` (`vbsBondVec`, Tasaki eqs. (7.1.19)–(7.1.20)).  The only irrational input is
  `(√2)⁻¹ · (√2)⁻¹ = ½`, used once.
* **F7** `akltVBSState_isVBSGroundForm` — every bond slice lies in the four-dimensional span `W`
  (`vbsBondSubspace`), by `Submodule.smul_mem` / `add_mem`.
* **F8** `bondSpin2ProjectionS_mulVec_akltVBSState_eq_zero` — frustration-freeness, by the `⇐`
  direction of the production `tasaki_lemma_7_4` (`AKLTBondProjection.lean:696`).

Nothing here is axiomatised or hypothesised: the only hypothesis is `1 < L` (needed already by
`tasaki_lemma_7_4`, and by the two-site bond having two distinct endpoints).

Exact rational pre-checks (`ℚ(√2)`, no floats) run before this file was written: the four
components of the F6 table match entry-by-entry over all nine `a`; frustration-freeness holds with
**0 violations** at `L = 3,4,5,6`; the negative control N1 (`A¹₀₀ = ½ → ⅓`) fires with 56
violations at `L = 4`; the rotation identity, `glueBond_shift` and the F5 trace decomposition hold
for `L = 2..6` and all bonds `x`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.3, Lemma 7.4, eqs. (7.1.19)–(7.1.21), pp. 186–187, and §7.2.2, eqs. (7.2.12)–(7.2.14),
pp. 195–196.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {L : ℕ}

/-! ### F0 — the production cyclic successor is the group successor -/

/-- **F0.**  The production cyclic successor `ringSucc` of a ring site is the group successor
`x + 1` of `Fin L`.  This is the only bridge used between the two successors. -/
theorem ringSucc_eq_add_one [NeZero L] (x : Fin L) : ringSucc x = x + 1 := by
  apply Fin.ext
  change (x.val + 1) % L = ((x + 1 : Fin L) : ℕ)
  rw [Fin.val_add, Fin.val_one' L, Nat.add_mod_mod]

/-! ### F2 — the ring VBS state is nonzero -/

/-- **F2.**  The periodic AKLT matrix-product state is nonzero as soon as the ring carries at least
two sites.  This is exactly the strict positivity of its squared norm
`‖Φ_L‖² = (3/4)^L + 3(−1/4)^L > 0` (Tasaki §7.2.2, eq. (7.2.21), p. 197), supplied by the
production theorem `AKLTStringOrder.state_norm_pos`.  Block ④-III consumes it for
`IsGroundEnergy Ĥ' 0` (G4) and for the gap statement (G7): a frustration-free kernel vector is a
ground state only if it is not the zero vector. -/
theorem akltVBSState_ne_zero (hL : 2 ≤ L) : akltVBSState L ≠ 0 := by
  intro h
  have hpos := AKLTStringOrder.state_norm_pos L hL
  rw [h] at hpos
  simp only [vecNormSqRe, star_zero, zero_dotProduct, Complex.zero_re, lt_self_iff_false] at hpos

/-! ### F3 — rotation invariance of the periodic MPS trace state -/

/-- The value of the `m`-fold ring successor, as a residue. -/
private lemma fin_iterate_succ_val [NeZero L] (m : ℕ) (k : Fin L) :
    ((fun j : Fin L => j + 1)^[m] k).val = (k.val + m) % L := by
  induction m with
  | zero => simp [Nat.mod_eq_of_lt k.isLt]
  | succ m ih =>
      rw [Function.iterate_succ_apply', Fin.val_add, Fin.val_one' L, Nat.add_mod_mod, ih,
        Nat.mod_add_mod, Nat.add_assoc]

/-- The `x.val`-fold ring successor is translation by `x`. -/
private lemma fin_iterate_succ_eq_add [NeZero L] (x k : Fin L) :
    (fun j : Fin L => j + 1)^[x.val] k = k + x := by
  apply Fin.ext
  rw [fin_iterate_succ_val, Fin.val_add]

/-- **F3a.**  The periodic trace-product AKLT state is invariant under a one-step ring rotation.
This is cyclicity of the matrix trace, transported through `List.ofFn`. -/
theorem akltVBSState_rotate [NeZero L] (σ : Fin L → Fin 3) :
    akltVBSState L (fun k => σ (k + 1)) = akltVBSState L σ := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by have := NeZero.ne L; omega⟩
  have hrot : List.ofFn (fun k : Fin (n + 1) => σ (k + 1))
      = (List.ofFn fun i : Fin n => σ i.succ) ++ [σ 0] := by
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append, Fin.coeSucc_eq_succ, Fin.last_add_one]
  simp only [akltVBSState]
  rw [hrot, orderedProd_append, Matrix.trace_mul_comm, List.ofFn_succ]
  simp only [orderedProd, mul_one]

/-- **F3b.**  The periodic trace-product AKLT state is invariant under any ring rotation. -/
theorem akltVBSState_shift [NeZero L] (m : ℕ) (σ : Fin L → Fin 3) :
    akltVBSState L (fun k => σ ((fun j : Fin L => j + 1)^[m] k)) = akltVBSState L σ := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hfun : (fun k : Fin L => σ ((fun j : Fin L => j + 1)^[m + 1] k))
          = fun k : Fin L => σ ((fun j : Fin L => j + 1)^[m] (k + 1)) := by
        funext k
        rw [Function.iterate_succ_apply]
      rw [hfun, akltVBSState_rotate fun i : Fin L => σ ((fun j : Fin L => j + 1)^[m] i), ih]

/-! ### F4 — moving a bond to the origin -/

/-- **F4.**  Rotating by `x` carries the bond `{x, x+1}` to the bond `{0, 1}`: the glued
configuration `glueBond x a τ` read along the rotated ring is `glueBond 0 a` applied to the
rotated rest configuration. -/
private lemma glueBond_shift [NeZero L] (x : Fin L) (a : Fin 2 → Fin 3)
    (τ : Fin L → Fin 3) (k : Fin L) :
    glueBond x a τ (k + x) = glueBond 0 a (fun j => τ (j + x)) k := by
  have hA : k + x = x ↔ k = 0 := by
    constructor
    · intro h
      have h' : k + x = 0 + x := by rw [zero_add]; exact h
      exact add_right_cancel h'
    · intro h
      rw [h, zero_add]
  have hB : k + x = x + 1 ↔ k = 1 := by
    constructor
    · intro h
      have h' : k + x = 1 + x := by rw [add_comm (1 : Fin L) x]; exact h
      exact add_right_cancel h'
    · intro h
      rw [h, add_comm]
  simp only [glueBond, ringSucc_eq_add_one, zero_add]
  by_cases h0 : k = 0
  · rw [if_pos (hA.mpr h0), if_pos h0]
  · rw [if_neg fun h => h0 (hA.mp h), if_neg h0]
    by_cases h1 : k = 1
    · rw [if_pos (hB.mpr h1), if_pos h1]
    · rw [if_neg fun h => h1 (hB.mp h), if_neg h1]

/-! ### F5 — a bond slice of a periodic MPS state is a two-site trace functional -/

/-- **F5.**  For the periodic matrix-product AKLT state, the two-site bond slice at any bond `x`
and any rest configuration `τ` is the linear functional `a ↦ tr (A^{a₀} A^{a₁} R)` of the two-site
tensor, where the remainder matrix `R` is the ordered product over the remaining `L − 2` sites and
does **not** depend on the bond configuration `a`. -/
theorem exists_bondSlice_eq_trace [NeZero L] (hL : 1 < L) (x : Fin L) (τ : Fin L → Fin 3) :
    ∃ R : Matrix (Fin 2) (Fin 2) ℂ, ∀ a : Fin 2 → Fin 3,
      bondSlice x (akltVBSState L) τ a
        = Matrix.trace (akltVBSMatrices (a 0) * akltVBSMatrices (a 1) * R) := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 2 := ⟨L - 2, by omega⟩
  refine ⟨orderedProd akltVBSMatrices (List.ofFn fun i : Fin m => τ (i.succ.succ + x)),
    fun a => ?_⟩
  have h10 : (1 : Fin (m + 2)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  have hfun : (fun k : Fin (m + 2) =>
        glueBond x a τ ((fun j : Fin (m + 2) => j + 1)^[x.val] k))
      = glueBond 0 a fun j => τ (j + x) := by
    funext k
    rw [fin_iterate_succ_eq_add, glueBond_shift x a τ k]
  have hstate : akltVBSState (m + 2) (glueBond x a τ)
      = akltVBSState (m + 2) (glueBond 0 a fun j => τ (j + x)) := by
    rw [← hfun, akltVBSState_shift]
  have hg0 : (glueBond (0 : Fin (m + 2)) a fun j => τ (j + x)) 0 = a 0 := by
    simp [glueBond]
  have hg1 : (glueBond (0 : Fin (m + 2)) a fun j => τ (j + x)) 1 = a 1 := by
    simp [glueBond, ringSucc_eq_add_one, h10]
  have hgs : ∀ i : Fin m, (glueBond (0 : Fin (m + 2)) a fun j => τ (j + x)) i.succ.succ
      = τ (i.succ.succ + x) := by
    intro i
    have hne0 : (i.succ.succ : Fin (m + 2)) ≠ 0 := Fin.succ_ne_zero _
    have hne1 : (i.succ.succ : Fin (m + 2)) ≠ 1 := by
      rw [← Fin.succ_zero_eq_one]
      exact fun h => Fin.succ_ne_zero i (Fin.succ_inj.mp h)
    simp [glueBond, ringSucc_eq_add_one, hne0, hne1]
  have hlist : List.ofFn (glueBond (0 : Fin (m + 2)) a fun j => τ (j + x))
      = a 0 :: a 1 :: List.ofFn (fun i : Fin m => τ (i.succ.succ + x)) := by
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [Fin.succ_zero_eq_one, hg0, hg1, hgs]
  change akltVBSState (m + 2) (glueBond x a τ) = _
  rw [hstate]
  simp only [akltVBSState]
  rw [hlist]
  simp only [orderedProd]
  rw [Matrix.mul_assoc]

/-! ### F6 — the exact two-site tensor table -/

/-- **F6.**  The two-site MPS tensor of the AKLT matrices, entry by entry: each of its four
components is a multiple of one VBS bond vector `Ψ_{σσ'}` of Tasaki eqs. (7.1.19)–(7.1.20),
with `s = (√2)⁻¹`,
`A^{a₀}A^{a₁} = !![¼ Ψ_{↓↑}(a), s Ψ_{↓↓}(a); −s Ψ_{↑↑}(a), −¼ Ψ_{↑↓}(a)]`.
The only irrational input is `(√2)⁻¹ (√2)⁻¹ = ½`, used once. -/
private lemma akltTwoSiteTensor_eq (a : Fin 2 → Fin 3) :
    akltVBSMatrices (a 0) * akltVBSMatrices (a 1) =
      !![(1 / 4 : ℂ) * vbsBondVec 1 0 a, ((Real.sqrt 2 : ℂ))⁻¹ * vbsBondVec 1 1 a;
        -((Real.sqrt 2 : ℂ))⁻¹ * vbsBondVec 0 0 a, (-1 / 4 : ℂ) * vbsBondVec 0 1 a] := by
  have hs : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = (1 / 2 : ℂ) := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  simp only [vbsBondVec, akltVBSMatrices]
  obtain ⟨u, hu⟩ : ∃ u, a 0 = u := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, a 1 = v := ⟨_, rfl⟩
  rw [hu, hv]
  fin_cases u <;> fin_cases v <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp +decide [Matrix.mul_apply, Fin.sum_univ_two, hs] <;>
    ring

/-! ### F7/F8 — frustration-freeness of the ring VBS state -/

/-- **F7.**  Every two-site bond slice of the periodic AKLT matrix-product state lies in the
four-dimensional VBS bond subspace `W` of Tasaki eq. (7.1.21): the state has the valence-bond-solid
singlet-tensor form at every bond of the ring, the wrap bond included. -/
theorem akltVBSState_isVBSGroundForm [NeZero L] (hL : 1 < L) (x : Fin L) :
    IsVBSGroundForm L x (akltVBSState L) := by
  intro τ
  obtain ⟨R, hR⟩ := exists_bondSlice_eq_trace hL x τ
  have htr : ∀ M : Matrix (Fin 2) (Fin 2) ℂ,
      Matrix.trace (M * R) = M 0 0 * R 0 0 + M 0 1 * R 1 0 + (M 1 0 * R 0 1 + M 1 1 * R 1 1) := by
    intro M
    rw [Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_two]
  have hmem : ∀ p q : Fin 2, vbsBondVec p q ∈ vbsBondSubspace := by
    intro p q
    simp only [vbsBondSubspace]
    exact Submodule.subset_span ⟨(p, q), rfl⟩
  have hslice : bondSlice x (akltVBSState L) τ
      = (R 0 0 * (1 / 4 : ℂ)) • vbsBondVec 1 0
        + (R 1 0 * ((Real.sqrt 2 : ℂ))⁻¹) • vbsBondVec 1 1
        + (R 0 1 * -((Real.sqrt 2 : ℂ))⁻¹) • vbsBondVec 0 0
        + (R 1 1 * (-1 / 4 : ℂ)) • vbsBondVec 0 1 := by
    funext a
    rw [hR a, akltTwoSiteTensor_eq a, htr]
    simp
    ring
  rw [hslice]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (hmem 1 0)) (Submodule.smul_mem _ _ (hmem 1 1)))
    (Submodule.smul_mem _ _ (hmem 0 0))) (Submodule.smul_mem _ _ (hmem 0 1))

/-- **F8 — frustration-freeness of the ring VBS state.**  The bond spin-2 projection
`P̂₂[Ŝ_x + Ŝ_{x+1}]` annihilates the periodic AKLT matrix-product state at **every** bond `x` of
the ring, the wrap bond included.  Equivalently, the ring VBS state lies in the kernel of every
local term of the AKLT Hamiltonian (Tasaki §7.1.3, Lemma 7.4, p. 187). -/
theorem bondSpin2ProjectionS_mulVec_akltVBSState_eq_zero (hL : 1 < L) (x : Fin L) :
    (bondSpin2ProjectionS x (ringSucc x)).mulVec (akltVBSState L) = 0 := by
  haveI : NeZero L := ⟨by omega⟩
  exact (tasaki_lemma_7_4 hL x (akltVBSState L)).mpr (akltVBSState_isVBSGroundForm hL x)

end LatticeSystem.Quantum
