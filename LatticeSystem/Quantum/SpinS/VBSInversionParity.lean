import LatticeSystem.Quantum.SpinS.ConfigPermMatrixS
import LatticeSystem.Quantum.SpinS.AKLTUniqueness.GroundStateUnique

/-!
# Tasaki §8.3.2 (S3): bond-centered inversion parity of the VBS state at `S = 1`

The bond-centered inversion of the periodic chain `{0, 1, …, L − 1}` is the site map
`x ↦ L − 1 − x`, i.e. `Fin.rev`, which induces `σ ↦ σ ∘ Fin.rev` on spin configurations and hence
the permutation operator `Û_inv` of Tasaki eq. (8.3.5).  It is a reflection of the cycle for
*every* `L` (the bond `{L − 1, 0}` is fixed setwise); for odd `L` it fixes in addition the single
site `(L − 1) / 2`, as every reflection of an odd cycle must.  So no parity restriction on `L` is
needed anywhere below.

The main result is the eigenvalue identity `Û_inv |Φ_VBS⟩ = (−1)^L |Φ_VBS⟩` at `S = 1`
(`tasaki_vbs_inversion_parity_spin_one`), together with its ground-state form via the AKLT
uniqueness theorem.  The mechanism is the book's "the inversion flips the sign of each
valence-bond": in the matrix-product representation the valence bond is the antisymmetric matrix
`ε = !![0, 1; -1, 0]`, and `ε (A^s)ᵀ = −(A^s ε)` for every spin label `s`, so transposing the
ordered product — which is what reversing the sites does under the trace — produces one sign per
site.  The trivial large-`D` product state has parity `+1` for every `L`, so for odd `L` the two
states have opposite parity and are not proportional.

The site map `Fin.rev` on `Fin L` restricts on `Fin (2 * n)` to the even-ring reflection
`ringReflect` of `RingBondReflection.lean` (equal, but not definitionally so: `2n − 1 − x` versus
`2n − (x + 1)`).  The two are kept separate here: unifying them would touch the whole
reflection-positivity stack and is a refactor of its own.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.3.2, eq. (8.3.5) and p. 257; worked example (S.63), p. 505; §7.1.1–§7.1.2,
eqs. (7.1.11)–(7.1.12), pp. 181–183 for the VBS state.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {L N : ℕ}

/-! ## The inversion operator `Û_inv` (Tasaki eq. (8.3.5)) -/

/-- The **bond-centered inversion of configurations** `σ^inv = (σ_{L−1}, …, σ_0)` of Tasaki
eq. (8.3.5): the reversal `σ ↦ σ ∘ Fin.rev` of the site order. -/
def bondInversionConfigS {L N : ℕ} (σ : Fin L → Fin (N + 1)) : Fin L → Fin (N + 1) :=
  σ ∘ Fin.rev

/-- Bond-centered inversion of configurations is an involution, for every `L` (odd or even). -/
theorem bondInversionConfigS_involutive :
    Function.Involutive (bondInversionConfigS (L := L) (N := N)) := by
  intro σ
  funext x
  simp [bondInversionConfigS, Fin.rev_rev]

/-- The **bond-centered inversion operator** `Û_inv` of Tasaki eq. (8.3.5): the permutation matrix
of `bondInversionConfigS`, i.e. `Û_inv |Ψ^σ⟩ = |Ψ^{σ^inv}⟩`. -/
noncomputable def bondInversionUnitaryS (L N : ℕ) : ManyBodyOpS (Fin L) N :=
  configPermMatrixS bondInversionConfigS

/-- Tasaki p. 257: `(Û_inv)² = 1̂`. -/
theorem bondInversionUnitaryS_mul_self :
    bondInversionUnitaryS L N * bondInversionUnitaryS L N = 1 :=
  configPermMatrixS_mul_self bondInversionConfigS_involutive

/-- Action of `Û_inv` on a state vector: `(Û_inv Φ)(σ) = Φ(σ^inv)`. -/
theorem bondInversionUnitaryS_mulVec (Φ : (Fin L → Fin (N + 1)) → ℂ) :
    (bondInversionUnitaryS L N).mulVec Φ = fun σ => Φ (σ ∘ Fin.rev) :=
  configPermMatrixS_mulVec bondInversionConfigS_involutive Φ

/-! ## The valence-bond sign -/

/-- The antisymmetric valence-bond matrix `ε = !![0, 1; -1, 0]` of the spin-one matrix-product
representation.  It carries the sign that inversion produces on each valence bond, and is used
only for that purpose. -/
private noncomputable def vbsEpsilon : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- The valence bond squares to `-1`: `ε² = -1`. -/
private theorem vbsEpsilon_mul_self : vbsEpsilon * vbsEpsilon = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vbsEpsilon, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The valence-bond sign flip.**  For every spin label `s`, transposition of the AKLT matrix
`A^s` is inversion by the valence bond up to a sign: `ε (A^s)ᵀ = −(A^s ε)`.  This is the Lean
content of Tasaki's "the inversion flips the sign of each valence-bond" (p. 257). -/
private theorem vbsEpsilon_mul_transpose (s : Fin 3) :
    vbsEpsilon * Matrix.transpose (akltVBSMatrices s) = -(akltVBSMatrices s * vbsEpsilon) := by
  fin_cases s <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [vbsEpsilon, akltVBSMatrices, Matrix.mul_apply, Fin.sum_univ_two]

/-- Conjugating the transposed ordered product by the valence bond reverses the order of the
matrices and produces one sign per site. -/
private theorem vbsEpsilon_mul_orderedProd_transpose (l : List (Fin 3)) :
    vbsEpsilon * Matrix.transpose (orderedProd akltVBSMatrices l)
      = ((-1 : ℂ) ^ l.length) • (orderedProd akltVBSMatrices l.reverse * vbsEpsilon) := by
  induction l with
  | nil => simp [orderedProd]
  | cons s t ih =>
    have hstep : orderedProd akltVBSMatrices (s :: t).reverse
        = orderedProd akltVBSMatrices t.reverse * akltVBSMatrices s := by
      rw [List.reverse_cons, orderedProd_append, orderedProd, orderedProd, Matrix.mul_one]
    calc vbsEpsilon * Matrix.transpose (orderedProd akltVBSMatrices (s :: t))
        = vbsEpsilon * Matrix.transpose (orderedProd akltVBSMatrices t) *
            Matrix.transpose (akltVBSMatrices s) := by
          rw [orderedProd, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = ((-1 : ℂ) ^ t.length) •
            (orderedProd akltVBSMatrices t.reverse *
              (vbsEpsilon * Matrix.transpose (akltVBSMatrices s))) := by
          rw [ih, Matrix.smul_mul, Matrix.mul_assoc]
      _ = ((-1 : ℂ) ^ (t.length + 1)) •
            (orderedProd akltVBSMatrices (s :: t).reverse * vbsEpsilon) := by
          rw [vbsEpsilon_mul_transpose, hstep, Matrix.mul_neg, Matrix.mul_assoc, pow_succ,
            mul_smul, neg_one_smul]
      _ = ((-1 : ℂ) ^ (s :: t).length) •
            (orderedProd akltVBSMatrices (s :: t).reverse * vbsEpsilon) := by
          rw [List.length_cons]

/-- Reversing the spin word multiplies the trace of the ordered product by `(−1)^ℓ`. -/
private theorem trace_orderedProd_reverse (l : List (Fin 3)) :
    Matrix.trace (orderedProd akltVBSMatrices l.reverse)
      = (-1 : ℂ) ^ l.length * Matrix.trace (orderedProd akltVBSMatrices l) := by
  have key : ∀ m : List (Fin 3),
      Matrix.trace (orderedProd akltVBSMatrices m)
        = (-1 : ℂ) ^ m.length * Matrix.trace (orderedProd akltVBSMatrices m.reverse) := by
    intro m
    have hL : Matrix.trace
        (vbsEpsilon * Matrix.transpose (orderedProd akltVBSMatrices m) * vbsEpsilon)
        = -Matrix.trace (orderedProd akltVBSMatrices m) := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, vbsEpsilon_mul_self, neg_one_mul,
        Matrix.trace_neg, Matrix.trace_transpose]
    have hR : Matrix.trace
        (vbsEpsilon * Matrix.transpose (orderedProd akltVBSMatrices m) * vbsEpsilon)
        = -((-1 : ℂ) ^ m.length * Matrix.trace (orderedProd akltVBSMatrices m.reverse)) := by
      rw [vbsEpsilon_mul_orderedProd_transpose, Matrix.smul_mul, Matrix.trace_smul,
        Matrix.mul_assoc, vbsEpsilon_mul_self, Matrix.mul_neg, Matrix.mul_one, Matrix.trace_neg]
      simp
    exact neg_inj.mp (hL.symm.trans hR)
  have h := key l.reverse
  rw [List.length_reverse, List.reverse_reverse] at h
  exact h

/-- Precomposing a tuple with `Fin.rev` reverses the list it enumerates. -/
private theorem list_ofFn_comp_rev {α : Type*} (σ : Fin L → α) :
    List.ofFn (σ ∘ Fin.rev) = (List.ofFn σ).reverse := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  rw [List.getElem_ofFn, List.getElem_reverse, List.getElem_ofFn]
  simp only [Function.comp_apply]
  refine congrArg σ (Fin.ext ?_)
  simp only [Fin.val_rev, List.length_ofFn]
  omega

/-! ## The parity identity -/

/-- **Reversal of the VBS coefficients.**  The unnormalized spin-one VBS coefficient on an
`L`-site ring changes by `(−1)^L` under reversal of the site order. -/
theorem akltVBSState_comp_rev (L : ℕ) (σ : Fin L → Fin 3) :
    akltVBSState L (σ ∘ Fin.rev) = (-1 : ℂ) ^ L * akltVBSState L σ := by
  simp only [akltVBSState]
  rw [list_ofFn_comp_rev, trace_orderedProd_reverse, List.length_ofFn]

/-- **Tasaki §8.3.2 (S3) at `S = 1`, eq. (8.3.5) and p. 257, PROVED.**  The periodic spin-one VBS
state is an eigenstate of the bond-centered inversion `Û_inv` with eigenvalue `(−1)^L`:
`Û_inv |Φ_VBS⟩ = (−1)^L |Φ_VBS⟩`, for every ring length `L` (no parity restriction).  At `L = 3`
this reproduces the book's worked example (S.63), p. 505.  The general-`S` formula `(−1)^{L·S}` is
not covered: it needs a general-`S` VBS construction, which the library does not have. -/
theorem tasaki_vbs_inversion_parity_spin_one (L : ℕ) :
    (bondInversionUnitaryS L 2).mulVec (akltVBSState L) = ((-1 : ℂ) ^ L) • akltVBSState L := by
  rw [bondInversionUnitaryS_mulVec]
  funext σ
  simpa using akltVBSState_comp_rev L σ

/-- **Tasaki p. 257: the trivial large-`D` state has inversion parity `+1`.**  The product state
with every site in a fixed magnetic label `m` — for the book's `|Φ₀⟩` with all `m = 0` this is the
constant configuration `fun _ => 1` in the library's labelling `0, 1, 2 ↔ +1, 0, −1` — is
invariant under `Û_inv` for every `L`. -/
theorem trivialProductState_bondInversion_spin_one (L : ℕ) (m : Fin 3) :
    (bondInversionUnitaryS L 2).mulVec (fun σ => if σ = fun _ => m then (1 : ℂ) else 0)
      = fun σ => if σ = fun _ => m then (1 : ℂ) else 0 := by
  have hiff : ∀ σ : Fin L → Fin 3, ((σ ∘ Fin.rev) = fun _ => m) ↔ (σ = fun _ => m) := by
    intro σ
    constructor
    · intro h
      funext x
      simpa [Fin.rev_rev] using congrFun h (Fin.rev x)
    · intro h
      subst h
      rfl
  rw [bondInversionUnitaryS_mulVec]
  funext σ
  exact if_congr (hiff σ) rfl rfl

/-- **Tasaki p. 257: opposite parities for odd `L`.**  On an odd ring with at least two sites the
VBS state has inversion parity `−1` while the trivial product state has parity `+1`, so the two
are not proportional — the `Z₂` obstruction the book uses to infer a transition point between the
Haldane and large-`D` phases.  Non-vacuity of the parity identity enters here through
`akltVBSState_ne_zero`. -/
theorem akltVBSState_ne_smul_trivialProductState_spin_one (L : ℕ) (hL : 2 ≤ L) (hodd : Odd L)
    (c : ℂ) :
    akltVBSState L ≠ c • (fun σ : Fin L → Fin 3 => if σ = fun _ => (1 : Fin 3) then (1 : ℂ)
      else 0) := by
  intro heq
  have hself : akltVBSState L = -akltVBSState L := by
    have hU := tasaki_vbs_inversion_parity_spin_one L
    rw [hodd.neg_one_pow] at hU
    rw [heq, Matrix.mulVec_smul, trivialProductState_bondInversion_spin_one, ← heq,
      neg_one_smul] at hU
    exact hU
  refine akltVBSState_ne_zero hL (funext fun σ => ?_)
  have h := congrFun hself σ
  rw [Pi.neg_apply] at h
  change akltVBSState L σ = 0
  linear_combination h / 2

/-- **Tasaki §8.3.2 (S3) at `S = 1`, ground-state form.**  Every nonzero ground state of the
spin-one AKLT ring Hamiltonian — not merely the explicit VBS vector — has bond-centered inversion
parity `(−1)^L`, which is the book's `Û_inv |Φ_GS⟩ = σ_inv |Φ_GS⟩` with `σ_inv = (−1)^L`.  The
ground state is unique (`aklt_ring_ground_state_unique`, Tasaki Theorem 7.1, §7.1.3), so the
parity of the VBS vector transfers to it. -/
theorem tasaki_vbs_inversion_parity_ground_state_spin_one (n : ℕ) (hn : 2 ≤ n)
    (Ψ : (Fin (n + 1) → Fin 3) → ℂ) (hΨ0 : Ψ ≠ 0)
    (hev : (akltHamiltonianS (n + 1)).mulVec Ψ
        = ((-(2 : ℝ) / 3 * ((n : ℝ) + 1) : ℝ) : ℂ) • Ψ) :
    (bondInversionUnitaryS (n + 1) 2).mulVec Ψ = ((-1 : ℂ) ^ (n + 1)) • Ψ := by
  obtain ⟨c, hc⟩ := aklt_ring_ground_state_unique n hn Ψ hΨ0 hev
  rw [hc, Matrix.mulVec_smul, tasaki_vbs_inversion_parity_spin_one, smul_comm]

end LatticeSystem.Quantum
