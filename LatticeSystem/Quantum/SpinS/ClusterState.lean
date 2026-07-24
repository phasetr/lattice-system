import LatticeSystem.Quantum.SpinS.AKLT
import LatticeSystem.Quantum.SpinS.HaldaneConjecture
import LatticeSystem.Quantum.SpinS.OrderOperatorAlgebra

/-!
# Tasaki §7.3.3: the Briegel–Raussendorf (cluster / graph) state and Theorem 7.8

The **Briegel–Raussendorf state** (cluster state on a regular lattice, graph state in general) is
the
`S = 1/2` analogue of the VBS state: a short-range-entangled state with no Néel order but a hidden
string order, central to measurement-based quantum computation and the theory of symmetry-protected
topological phases.  On a graph `(Λ, B)` it is the unique ground state of the **stabilizer
Hamiltonian** (eq. (7.3.30))
`Ĥ_BR = −Σ_{x∈Λ} σ̂_x^{(1)} ∏_{y∈N(x)} σ̂_y^{(3)}`,
a sum of the commuting stabilizers `K̂_x = σ̂_x^{(1)} ∏_{y∼x} σ̂_y^{(3)}` (each `K̂_x² = 1`, so
`K̂_x` has eigenvalues `±1`).

**Theorem 7.8**: the cluster state `|Φ_C⟩` is the **unique** ground state of `Ĥ_BR`, with ground
energy `E_GS = −N` (`N = |Λ|`), and the energy gap above the ground state is exactly `2`.

We work with the vertex set `Λ = Fin L`.  The theorem is **proved** (no longer an axiom) by two
operator conjugations that diagonalize `Ĥ_BR`:

    Ĥ_BR  =(Û_C conj)=  Ĥ_→ = −Σ σ̂_x^{(1)}  =(Hadamard conj)=  D = −Σ σ̂_x^{(3)}  (diagonal),

with the combined similarity `Ĥ_BR = V · D · V⁻¹`, `V = Û_C · W`, `V⁻¹ = 2^{−L} W · Û_C`.  Here
`Û_C` is the diagonal **controlled-`Z`** sign operator (`Û_C² = 1`) and `W` is the (unnormalized)
Hadamard operator with `W² = 2^L`.  The diagonal operator `D` has entry `f(σ) = −L + 2k`
(`k = #{x | σ_x = 1}`), whose spectrum `{−L, −L+2, …}` gives `E_GS = −L`, gap `= 2`, and a
one-dimensional ground eigenspace; everything transports back through `V` because the ground-state
predicates are defined purely via `realSpectrum`.  The cluster state is the explicit vector
`Φ_C = clusterStateVec G = V · e₀` (the all-plus product state sent through `Û_C`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.3.3, Theorem 7.8, eqs. (7.3.29)–(7.3.37), pp. 217–220; H. J. Briegel, R. Raussendorf,
Phys.
Rev. Lett. **86**, 910 (2001); R. Raussendorf, H. J. Briegel, Phys. Rev. Lett. **86**, 5188 (2001).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {L : ℕ}

/-- The single-site **Pauli `X` operator** `σ̂_x^{(1)} = 2 Ŝ_x^{(1)}` on qubit site `x` (spin
`S = 1/2`, `N = 1`); on the basis `Fin 2` it is the off-diagonal flip `[[0,1],[1,0]]`. -/
noncomputable def pauliXS (x : Fin L) : ManyBodyOpS (Fin L) 1 :=
  (2 : ℂ) • spinSSiteOp1 x 1

/-- The single-site **Pauli `Z` operator** `σ̂_x^{(3)} = 2 Ŝ_x^{(3)}` on qubit site `x`; on the
basis
`Fin 2` it is the diagonal `diag(1, −1)` (eigenvalue `(−1)^{σ_x}`). -/
noncomputable def pauliZS (x : Fin L) : ManyBodyOpS (Fin L) 1 :=
  (2 : ℂ) • spinSSiteOp3 x 1

/-- The **neighbour-`Z` product** `∏_{y∈N(x)} σ̂_y^{(3)}` for a vertex `x` of the graph `G`: as each
`σ̂_y^{(3)}` is diagonal and the factors on distinct neighbours commute, the product is the single
diagonal operator multiplying a configuration `σ` by `∏_{y∼x} (−1)^{σ_y}`. -/
noncomputable def neighborZProduct (G : SimpleGraph (Fin L)) [DecidableRel G.Adj] (x : Fin L) :
    ManyBodyOpS (Fin L) 1 :=
  Matrix.diagonal fun cfg : Fin L → Fin 2 =>
    ∏ y ∈ Finset.univ.filter fun y : Fin L => G.Adj x y, (-1 : ℂ) ^ ((cfg y).val)

/-- The **Briegel–Raussendorf stabilizer** `K̂_x = σ̂_x^{(1)} ∏_{y∼x} σ̂_y^{(3)}` at vertex `x`.
Each
`K̂_x` is self-inverse (`K̂_x² = 1`) and they mutually commute, so they share an eigenbasis with
eigenvalues `±1`. -/
noncomputable def brStabilizer (G : SimpleGraph (Fin L)) [DecidableRel G.Adj] (x : Fin L) :
    ManyBodyOpS (Fin L) 1 :=
  pauliXS x * neighborZProduct G x

/-- The **Briegel–Raussendorf (graph-state) Hamiltonian** `Ĥ_BR = −Σ_x K̂_x` (eq. (7.3.30)): minus
the sum of the stabilizers over all vertices of the graph `G`. -/
noncomputable def graphStateHamiltonianS (G : SimpleGraph (Fin L)) [DecidableRel G.Adj] :
    ManyBodyOpS (Fin L) 1 :=
  (-1 : ℂ) • ∑ x : Fin L, brStabilizer G x

/-- The **trivial paramagnet Hamiltonian** `Ĥ_→ = −Σ_x σ̂_x^{(1)}`: the product-state model to which
`Ĥ_BR` is conjugate through the controlled-`Z` unitary `Û_C` (Tasaki §7.3.3). -/
noncomputable def trivialParamagnetHamiltonianS (L : ℕ) : ManyBodyOpS (Fin L) 1 :=
  (-1 : ℂ) • ∑ x : Fin L, pauliXS x

/-- The **diagonal Pauli-`Z` Hamiltonian** `D = −Σ_x σ̂_x^{(3)}`: the fully diagonalized image of
`Ĥ_BR` after both conjugations, with entry `−Σ_x (−1)^{σ_x} = −L + 2k` (`k = #{x | σ_x = 1}`). -/
noncomputable def diagPauliZHamiltonianS (L : ℕ) : ManyBodyOpS (Fin L) 1 :=
  (-1 : ℂ) • ∑ x : Fin L, pauliZS x

/-! ## Elementary `Fin 2` sign facts -/

/-- On `Fin 2`, flipping a bit `a ↦ a + 1` and adding the old value gives `1`:
`(a + 1).val + a.val = 1`. -/
private lemma fin2_flip_val_add (a : Fin 2) : (a + 1).val + a.val = 1 := by
  fin_cases a <;> decide

/-- On `Fin 2`, `a + 1 ≠ a`. -/
private lemma fin2_succ_ne (a : Fin 2) : a + 1 ≠ a := by
  fin_cases a <;> decide

/-- On `Fin 2`, distinct bits are related by `a = b + 1`. -/
private lemma fin2_eq_succ_of_ne {a b : Fin 2} (h : a ≠ b) : a = b + 1 := by
  revert h; fin_cases a <;> fin_cases b <;> decide

/-- `1 + (−1)^(a.val + b.val) = 2` if `a = b` and `0` otherwise (`a, b : Fin 2`). -/
private lemma onePlusNegOnePow (a b : Fin 2) :
    (1 : ℂ) + (-1) ^ (a.val + b.val) = if a = b then 2 else 0 := by
  fin_cases a <;> fin_cases b <;>
    first
    | (rw [if_pos (by decide)]; norm_num)
    | (rw [if_neg (by decide)]; norm_num)

/-- `1 + (−1)^(a.val + b.val + 1) = 2` if `a = b + 1` and `0` otherwise (`a, b : Fin 2`). -/
private lemma onePlusNegOnePowSucc (a b : Fin 2) :
    (1 : ℂ) + (-1) ^ (a.val + b.val + 1) = if a = b + 1 then 2 else 0 := by
  fin_cases a <;> fin_cases b <;>
    first
    | (rw [if_pos (by decide)]; norm_num)
    | (rw [if_neg (by decide)]; norm_num)

/-- The value `∏_y (if σ' y = σ y then 2 else 0)` collapses to `2^L` (if `σ' = σ`) or `0`. -/
private lemma prod_two_or_zero (σ' σ : Fin L → Fin 2) :
    (∏ y : Fin L, if σ' y = σ y then (2 : ℂ) else 0) = if σ' = σ then (2 : ℂ) ^ L else 0 := by
  by_cases h : σ' = σ
  · subst h
    simp only [if_true, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg h]
    obtain ⟨y, hy⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ y) (by rw [if_neg hy])

/-- Fubini for a product-of-sums over the configuration space `Fin L → Fin 2`:
`∑_τ ∏_y g y (τ y) = ∏_y ∑_t g y t`. -/
private lemma sum_prod_swap (g : Fin L → Fin 2 → ℂ) :
    (∑ τ : Fin L → Fin 2, ∏ y : Fin L, g y (τ y)) = ∏ y : Fin L, ∑ t : Fin 2, g y t := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-! ## Single-site concrete forms of the Pauli operators -/

/-- **`σ̂_x^{(3)}` is diagonal**: `pauliZS x = diag(σ ↦ (−1)^{σ_x})`. -/
theorem pauliZS_eq_diagonal (x : Fin L) :
    pauliZS x = Matrix.diagonal fun cfg : Fin L → Fin 2 => (-1 : ℂ) ^ ((cfg x).val) := by
  have hmat : (2 : ℂ) • spinSOp3 1 = Matrix.diagonal fun k : Fin 2 => (-1 : ℂ) ^ (k.val) := by
    rw [spinSOp3]
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; rw [if_pos rfl, if_pos rfl]; fin_cases i <;> norm_num
    · rw [if_neg h, if_neg h, mul_zero]
  simp only [pauliZS, spinSSiteOp3]
  rw [← onSiteS_smul, hmat, onSiteS_diagonal]

/-- The single-site flip `flipSite σ x` toggles the value of `σ` at `x` (`σ_x ↦ σ_x + 1` in
`Fin 2`) and leaves every other site fixed; it is the action of `σ̂_x^{(1)}` on the basis. -/
def flipSite (σ : Fin L → Fin 2) (x : Fin L) : Fin L → Fin 2 :=
  Function.update σ x (σ x + 1)

/-- `flipSite σ x` at the flipped site: `flipSite σ x x = σ x + 1`. -/
theorem flipSite_self (σ : Fin L → Fin 2) (x : Fin L) : flipSite σ x x = σ x + 1 :=
  Function.update_self ..

/-- `flipSite σ x` away from the flipped site: `flipSite σ x y = σ y` for `y ≠ x`. -/
theorem flipSite_of_ne (σ : Fin L → Fin 2) {x y : Fin L} (h : y ≠ x) : flipSite σ x y = σ y :=
  Function.update_of_ne h ..

/-- **`σ̂_x^{(1)}` is the basis flip**: `pauliXS x σ' σ = 1` if `σ' = flipSite σ x` and `0`
otherwise. -/
theorem pauliXS_apply (x : Fin L) (σ' σ : Fin L → Fin 2) :
    pauliXS x σ' σ = if σ' = flipSite σ x then 1 else 0 := by
  have hPM : spinSOpPlus 1 + spinSOpMinus 1 = !![0, 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [spinSOpPlus, spinSOpMinus, Matrix.add_apply]
  have hmat : (2 : ℂ) • spinSOp1 1 = !![0, 1; 1, 0] := by
    rw [spinSOp1, smul_smul, show (2 : ℂ) * (1 / 2) = 1 by norm_num, one_smul, hPM]
  have hentry : ∀ a b : Fin 2, (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) a b =
      if a = b then 0 else 1 := by
    intro a b; fin_cases a <;> fin_cases b <;> simp
  have hpx : pauliXS x = onSiteS x !![0, 1; 1, 0] := by
    simp only [pauliXS, spinSSiteOp1]; rw [← onSiteS_smul, hmat]
  rw [hpx, onSiteS_apply]
  by_cases hup : σ' = flipSite σ x
  · rw [if_pos hup]
    have hoff : ∀ k, k ≠ x → σ' k = σ k := fun k hk => by rw [hup, flipSite_of_ne σ hk]
    rw [if_pos hoff, hentry]
    have hx : σ' x = σ x + 1 := by rw [hup, flipSite_self]
    rw [hx, if_neg (fin2_succ_ne (σ x))]
  · rw [if_neg hup]
    by_cases hoff : ∀ k, k ≠ x → σ' k = σ k
    · rw [if_pos hoff, hentry]
      have hxx : σ' x = σ x := by
        by_contra hne
        apply hup
        funext k
        by_cases hk : k = x
        · subst hk; rw [flipSite_self]; exact fin2_eq_succ_of_ne hne
        · rw [flipSite_of_ne σ hk]; exact hoff k hk
      rw [hxx, if_pos rfl]
    · rw [if_neg hoff]

/-! ## The unnormalized Hadamard operator -/

/-- The (unnormalized) tensor-Hadamard operator `W = H̃^{⊗L}` with integer entries
`W σ' σ = (−1)^{⟨σ', σ⟩}` (`⟨σ', σ⟩ = Σ_y σ'_y σ_y`).  Using `H̃ = [[1,1],[1,−1]]` (entries `±1`)
avoids `√2`; the normalization factor `2^{−L}` is pushed into `V⁻¹`. -/
noncomputable def hadamardAll (L : ℕ) : ManyBodyOpS (Fin L) 1 :=
  Matrix.of fun σ' σ : Fin L → Fin 2 => (-1 : ℂ) ^ (∑ y : Fin L, (σ' y).val * (σ y).val)

/-- Matrix element of `W`: `W σ' σ = (−1)^{Σ_y σ'_y σ_y}`. -/
theorem hadamardAll_apply (L : ℕ) (σ' σ : Fin L → Fin 2) :
    hadamardAll L σ' σ = (-1 : ℂ) ^ (∑ y : Fin L, (σ' y).val * (σ y).val) := rfl

/-- **`W² = 2^L`**: the unnormalized Hadamard operator squares to `2^L` times the identity. -/
theorem hadamardAll_sq (L : ℕ) :
    hadamardAll L * hadamardAll L = ((2 : ℂ) ^ L) • (1 : ManyBodyOpS (Fin L) 1) := by
  ext σ' σ
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hval : ∀ τ : Fin L → Fin 2, hadamardAll L σ' τ * hadamardAll L τ σ
      = ∏ y : Fin L, ((-1 : ℂ) ^ ((σ' y).val * (τ y).val)
          * (-1 : ℂ) ^ ((τ y).val * (σ y).val)) := by
    intro τ
    rw [hadamardAll_apply, hadamardAll_apply, ← Finset.prod_pow_eq_pow_sum,
        ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl (fun τ _ => hval τ)]
  rw [sum_prod_swap (fun y t => (-1 : ℂ) ^ ((σ' y).val * t.val) * (-1 : ℂ) ^ (t.val * (σ y).val))]
  have hy : ∀ y : Fin L,
      (∑ t : Fin 2, (-1 : ℂ) ^ ((σ' y).val * t.val) * (-1 : ℂ) ^ (t.val * (σ y).val))
      = if σ' y = σ y then (2 : ℂ) else 0 := by
    intro y
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, mul_zero, zero_mul, mul_one, one_mul, pow_zero]
    rw [← pow_add]
    exact onePlusNegOnePow (σ' y) (σ y)
  rw [Finset.prod_congr rfl (fun y _ => hy y), prod_two_or_zero]
  split_ifs <;> simp

/-! ## The Hadamard conjugation `W σ̂^{(3)} W = 2^L σ̂^{(1)}` -/

/-- **Hadamard conjugation of `σ̂_x^{(3)}`**: `W σ̂_x^{(3)} W = 2^L σ̂_x^{(1)}` (the Hadamard maps
the diagonal Pauli-`Z` to the off-diagonal Pauli-`X`, up to the unnormalized factor `2^L`). -/
theorem hadamardAll_conj_pauliZ (L : ℕ) (x : Fin L) :
    hadamardAll L * pauliZS x * hadamardAll L = ((2 : ℂ) ^ L) • pauliXS x := by
  ext σ' σ
  rw [pauliZS_eq_diagonal, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  have hval : ∀ α : Fin L → Fin 2,
      hadamardAll L σ' α * (-1 : ℂ) ^ ((α x).val) * hadamardAll L α σ
      = ∏ y : Fin L, (-1 : ℂ) ^ ((σ' y).val * (α y).val
          + (if y = x then (α y).val else 0) + (α y).val * (σ y).val) := by
    intro α
    have hz : (-1 : ℂ) ^ ((α x).val)
        = ∏ y : Fin L, (-1 : ℂ) ^ (if y = x then (α y).val else 0) := by
      rw [Finset.prod_pow_eq_pow_sum, Finset.sum_ite_eq' Finset.univ x fun y => (α y).val]
      simp
    rw [hadamardAll_apply, hadamardAll_apply, hz, ← Finset.prod_pow_eq_pow_sum,
        ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro y _
    rw [← pow_add, ← pow_add]
  rw [Finset.sum_congr rfl (fun α _ => hval α)]
  rw [sum_prod_swap (fun y t => (-1 : ℂ) ^ ((σ' y).val * t.val
      + (if y = x then t.val else 0) + t.val * (σ y).val))]
  have hy : ∀ y : Fin L,
      (∑ t : Fin 2, (-1 : ℂ) ^ ((σ' y).val * t.val
          + (if y = x then t.val else 0) + t.val * (σ y).val))
      = if σ' y = flipSite σ x y then (2 : ℂ) else 0 := by
    intro y
    rw [Fin.sum_univ_two]
    by_cases hyx : y = x
    · rw [hyx]
      simp only [if_true, Fin.val_zero, Fin.val_one, mul_zero, zero_mul,
        mul_one, one_mul, add_zero, pow_zero]
      rw [flipSite_self, show (σ' x).val + 1 + (σ x).val = (σ' x).val + (σ x).val + 1 by ring]
      exact onePlusNegOnePowSucc (σ' x) (σ x)
    · simp only [if_neg hyx, Fin.val_zero, Fin.val_one, mul_zero, zero_mul, mul_one, one_mul,
        add_zero]
      rw [flipSite_of_ne σ hyx]
      exact onePlusNegOnePow (σ' y) (σ y)
  rw [Finset.prod_congr rfl (fun y _ => hy y), prod_two_or_zero]
  rw [Matrix.smul_apply, pauliXS_apply, smul_eq_mul]
  split_ifs <;> simp

/-! ## The controlled-`Z` unitary -/

/-- The controlled-`Z` sign exponent: `Σ_{x<y, x∼y} σ_x σ_y` over the undirected edges of `G`
(each edge counted once via `x < y`). -/
private def czExp (G : SimpleGraph (Fin L)) [DecidableRel G.Adj] (cfg : Fin L → Fin 2) : ℕ :=
  ∑ p ∈ Finset.univ.filter fun p : (Fin L) × (Fin L) => p.1 < p.2 ∧ G.Adj p.1 p.2,
    (cfg p.1).val * (cfg p.2).val

/-- The **controlled-`Z` unitary** `Û_C = ∏_{x<y, x∼y} Ĉ_{xy}`: the diagonal sign operator with
entry `(−1)^{Σ_{x<y, x∼y} σ_x σ_y}`.  It is an involution (`Û_C² = 1`) and satisfies
`Û_C σ̂_x^{(1)} Û_C = K̂_x` (Tasaki §7.3.3). -/
noncomputable def unitaryCZ (G : SimpleGraph (Fin L)) [DecidableRel G.Adj] :
    ManyBodyOpS (Fin L) 1 :=
  Matrix.diagonal fun cfg : Fin L → Fin 2 => (-1 : ℂ) ^ (czExp G cfg)

/-- **`Û_C² = 1`**: the controlled-`Z` unitary is an involution. -/
theorem unitaryCZ_sq (G : SimpleGraph (Fin L)) [DecidableRel G.Adj] :
    unitaryCZ G * unitaryCZ G = 1 := by
  rw [unitaryCZ, Matrix.diagonal_mul_diagonal]
  rw [show (fun cfg : Fin L → Fin 2 => (-1 : ℂ) ^ (czExp G cfg) * (-1 : ℂ) ^ (czExp G cfg))
        = fun _ => (1 : ℂ) from ?_, Matrix.diagonal_one]
  funext cfg
  rw [← pow_add]
  exact Even.neg_one_pow ⟨czExp G cfg, by ring⟩

/-- **Sign-flip identity**: `Û_C(flip_x σ) · Û_C(σ) = ∏_{y∼x} (−1)^{σ_y}`, the diagonal value of the
neighbour-`Z` product.  This is the pointwise heart of `Û_C σ̂_x^{(1)} Û_C = K̂_x`: flipping the bit
at `x` changes the controlled-`Z` sign by exactly the product over the edges incident to `x`. -/
private lemma unitaryCZ_sign_flip (G : SimpleGraph (Fin L)) [DecidableRel G.Adj]
    (x : Fin L) (σ : Fin L → Fin 2) :
    (-1 : ℂ) ^ czExp G (flipSite σ x) * (-1 : ℂ) ^ czExp G σ
      = ∏ y ∈ Finset.univ.filter fun y : Fin L => G.Adj x y, (-1 : ℂ) ^ ((σ y).val) := by
  simp only [czExp]
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  have hsub : (Finset.univ.filter fun p : (Fin L) × (Fin L) => p.1 < p.2 ∧ G.Adj p.1 p.2).filter
      (fun p => p.1 = x ∨ p.2 = x) ⊆
      Finset.univ.filter fun p : (Fin L) × (Fin L) => p.1 < p.2 ∧ G.Adj p.1 p.2 :=
    Finset.filter_subset _ _
  rw [← Finset.prod_subset hsub]
  · refine Finset.prod_bij'
      (i := fun p _ => if p.1 = x then p.2 else p.1)
      (j := fun y _ => if x < y then (x, y) else (y, x))
      (t := Finset.univ.filter fun y : Fin L => G.Adj x y) ?hi ?hj ?linv ?rinv ?hval
    case hi =>
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpE, hpx⟩ := hp
      rw [Finset.mem_filter] at hpE
      obtain ⟨_, hlt, hadj⟩ := hpE
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      dsimp only
      rcases hpx with h1 | h2
      · rw [if_pos h1, ← h1]; exact hadj
      · have hp1 : p.1 ≠ x := by
          intro h; rw [h, h2] at hlt; exact (lt_irrefl x) hlt
        rw [if_neg hp1, ← h2]; exact hadj.symm
    case hj =>
      intro y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨_, hadj⟩ := hy
      have hne : x ≠ y := G.ne_of_adj hadj
      dsimp only
      rw [Finset.mem_filter, Finset.mem_filter]
      by_cases hlt : x < y
      · rw [if_pos hlt]
        exact ⟨⟨Finset.mem_univ _, hlt, hadj⟩, Or.inl rfl⟩
      · rw [if_neg hlt]
        have hyx : y < x := lt_of_le_of_ne (not_lt.mp hlt) hne.symm
        exact ⟨⟨Finset.mem_univ _, hyx, hadj.symm⟩, Or.inr rfl⟩
    case linv =>
      intro p hp
      rw [Finset.mem_filter, Finset.mem_filter] at hp
      obtain ⟨⟨_, hlt, _⟩, hpx⟩ := hp
      dsimp only
      rcases hpx with h1 | h2
      · rw [if_pos h1]
        have hxlt : x < p.2 := h1 ▸ hlt
        rw [if_pos hxlt, ← h1]
      · have hp1 : p.1 ≠ x := by
          intro h; rw [h, h2] at hlt; exact (lt_irrefl x) hlt
        rw [if_neg hp1]
        have hp1lt : ¬ x < p.1 := by rw [← h2]; exact not_lt.mpr (le_of_lt hlt)
        rw [if_neg hp1lt, ← h2]
    case rinv =>
      intro y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨_, hadj⟩ := hy
      have hne : x ≠ y := G.ne_of_adj hadj
      dsimp only
      by_cases hlt : x < y
      · rw [if_pos hlt, if_pos rfl]
      · rw [if_neg hlt, if_neg hne.symm]
    case hval =>
      intro p hp
      rw [Finset.mem_filter, Finset.mem_filter] at hp
      obtain ⟨⟨_, hlt, _⟩, hpx⟩ := hp
      dsimp only
      rcases hpx with h1 | h2
      · rw [if_pos h1]
        have hp2 : p.2 ≠ x := by intro h; rw [h1, h] at hlt; exact (lt_irrefl x) hlt
        rw [h1, flipSite_self σ, flipSite_of_ne σ hp2, ← pow_add, ← add_mul,
          fin2_flip_val_add, one_mul]
      · have hp1 : p.1 ≠ x := by intro h; rw [h, h2] at hlt; exact (lt_irrefl x) hlt
        rw [if_neg hp1, h2, flipSite_of_ne σ hp1, flipSite_self σ, ← pow_add, ← mul_add,
          fin2_flip_val_add, mul_one]
  · intro p hp hpx
    have hp1 : p.1 ≠ x := by
      intro h; exact hpx (by rw [Finset.mem_filter]; exact ⟨hp, Or.inl h⟩)
    have hp2 : p.2 ≠ x := by
      intro h; exact hpx (by rw [Finset.mem_filter]; exact ⟨hp, Or.inr h⟩)
    rw [flipSite_of_ne σ hp1, flipSite_of_ne σ hp2, ← pow_add]
    exact Even.neg_one_pow ⟨(σ p.1).val * (σ p.2).val, by ring⟩

/-- **Stabilizer conjugation**: `Û_C σ̂_x^{(1)} Û_C = K̂_x` (eq. (7.3.31)–(7.3.33)). -/
theorem unitaryCZ_conj_pauliX (G : SimpleGraph (Fin L)) [DecidableRel G.Adj] (x : Fin L) :
    unitaryCZ G * pauliXS x * unitaryCZ G = brStabilizer G x := by
  ext σ' σ
  rw [unitaryCZ, Matrix.mul_diagonal, Matrix.diagonal_mul, brStabilizer, neighborZProduct,
    Matrix.mul_diagonal, pauliXS_apply]
  by_cases hflip : σ' = flipSite σ x
  · rw [if_pos hflip]
    simp only [mul_one, one_mul]
    rw [hflip]
    exact unitaryCZ_sign_flip G x σ
  · rw [if_neg hflip]; ring

/-! ## Conjugate Hamiltonians -/

/-- `Û_C Ĥ_→ Û_C = Ĥ_BR` (the graph-state Hamiltonian is the controlled-`Z` conjugate of the trivial
paramagnet), summing the stabilizer conjugation over all vertices. -/
theorem graphStateHamiltonianS_eq_conj_paramagnet (G : SimpleGraph (Fin L)) [DecidableRel G.Adj] :
    unitaryCZ G * trivialParamagnetHamiltonianS L * unitaryCZ G = graphStateHamiltonianS G := by
  rw [trivialParamagnetHamiltonianS, graphStateHamiltonianS, mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => unitaryCZ_conj_pauliX G x

/-- `W D W = 2^L Ĥ_→`: the Hadamard conjugate of the diagonal Pauli-`Z` Hamiltonian is `2^L` times
the trivial paramagnet, summing the single-site Hadamard conjugation over all vertices. -/
theorem hadamardAll_conj_diagPauliZ (L : ℕ) :
    hadamardAll L * diagPauliZHamiltonianS L * hadamardAll L
      = ((2 : ℂ) ^ L) • trivialParamagnetHamiltonianS L := by
  rw [diagPauliZHamiltonianS, trivialParamagnetHamiltonianS, mul_smul_comm, smul_mul_assoc,
    Finset.mul_sum, Finset.sum_mul]
  simp_rw [hadamardAll_conj_pauliZ]
  rw [← Finset.smul_sum, smul_comm]

/-! ## The similarity `Ĥ_BR = V D V⁻¹` -/

/-- The similarity operator `V = Û_C W`. -/
private noncomputable def clusterV (G : SimpleGraph (Fin L)) [DecidableRel G.Adj] :
    ManyBodyOpS (Fin L) 1 :=
  unitaryCZ G * hadamardAll L

/-- The inverse similarity operator `V⁻¹ = 2^{−L} W Û_C`. -/
private noncomputable def clusterVinv (G : SimpleGraph (Fin L)) [DecidableRel G.Adj] :
    ManyBodyOpS (Fin L) 1 :=
  ((2 : ℂ) ^ L)⁻¹ • (hadamardAll L * unitaryCZ G)

/-- `V V⁻¹ = 1`. -/
theorem clusterV_mul_clusterVinv (G : SimpleGraph (Fin L)) [DecidableRel G.Adj] :
    clusterV G * clusterVinv G = 1 := by
  have h2 : (2 : ℂ) ^ L ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [clusterV, clusterVinv, mul_smul_comm]
  rw [show unitaryCZ G * hadamardAll L * (hadamardAll L * unitaryCZ G)
        = unitaryCZ G * (hadamardAll L * hadamardAll L) * unitaryCZ G from by
        simp only [mul_assoc]]
  rw [hadamardAll_sq, mul_smul_comm, smul_mul_assoc, mul_one, unitaryCZ_sq, smul_smul,
    inv_mul_cancel₀ h2, one_smul]

/-- `V⁻¹ V = 1`. -/
theorem clusterVinv_mul_clusterV (G : SimpleGraph (Fin L)) [DecidableRel G.Adj] :
    clusterVinv G * clusterV G = 1 := by
  have h2 : (2 : ℂ) ^ L ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [clusterV, clusterVinv, smul_mul_assoc]
  rw [show hadamardAll L * unitaryCZ G * (unitaryCZ G * hadamardAll L)
        = hadamardAll L * (unitaryCZ G * unitaryCZ G) * hadamardAll L from by
        simp only [mul_assoc]]
  rw [unitaryCZ_sq, mul_one, hadamardAll_sq, smul_smul, inv_mul_cancel₀ h2, one_smul]

/-- **The full similarity** `Ĥ_BR = V D V⁻¹`. -/
theorem graphStateHamiltonianS_eq_conj (G : SimpleGraph (Fin L)) [DecidableRel G.Adj] :
    graphStateHamiltonianS G = clusterV G * diagPauliZHamiltonianS L * clusterVinv G := by
  have h2 : (2 : ℂ) ^ L ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [clusterV, clusterVinv, mul_smul_comm]
  rw [show unitaryCZ G * hadamardAll L * diagPauliZHamiltonianS L * (hadamardAll L * unitaryCZ G)
        = unitaryCZ G * (hadamardAll L * diagPauliZHamiltonianS L * hadamardAll L) * unitaryCZ G
      from by simp only [mul_assoc]]
  rw [hadamardAll_conj_diagPauliZ, mul_smul_comm, smul_mul_assoc,
    graphStateHamiltonianS_eq_conj_paramagnet, smul_smul, inv_mul_cancel₀ h2, one_smul]

/-! ## Diagonal spectrum -/

/-- The real spectrum of a diagonal operator with real entries is the range of its diagonal. -/
theorem diagonal_realSpectrum {L N : ℕ} (h : (Fin L → Fin (N + 1)) → ℝ) :
    realSpectrum (Matrix.diagonal fun cfg => (h cfg : ℂ)) = Set.range h := by
  ext E
  simp only [realSpectrum, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨Φ, hΦ, heq⟩
    obtain ⟨cfg, hcfg⟩ := Function.ne_iff.mp hΦ
    simp only [Pi.zero_apply] at hcfg
    refine ⟨cfg, ?_⟩
    have hval := congrFun heq cfg
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at hval
    have : (h cfg : ℂ) = (E : ℂ) := mul_right_cancel₀ hcfg hval
    exact_mod_cast this
  · rintro ⟨cfg, rfl⟩
    refine ⟨basisVecS cfg, ?_, ?_⟩
    · exact Function.ne_iff.mpr ⟨cfg, by simp [basisVecS]⟩
    · funext τ
      rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
      by_cases hτ : τ = cfg
      · subst hτ; simp
      · rw [basisVecS_of_ne hτ, mul_zero, mul_zero]

/-- The diagonal energy of a configuration `σ`: `−L + 2k` with `k = #{x | σ_x = 1}`. -/
noncomputable def clusterEnergy (L : ℕ) (cfg : Fin L → Fin 2) : ℝ :=
  2 * ((Finset.univ.filter fun x : Fin L => cfg x = 1).card : ℝ) - (L : ℝ)

/-- `Σ_x (−1)^{σ_x} = L − 2 #{x | σ_x = 1}`. -/
private lemma sum_neg_one_pow_cfg (σ : Fin L → Fin 2) :
    (∑ x : Fin L, (-1 : ℂ) ^ ((σ x).val))
      = (L : ℂ) - 2 * ((Finset.univ.filter fun x : Fin L => σ x = 1).card : ℂ) := by
  have hpt : ∀ x : Fin L, (-1 : ℂ) ^ ((σ x).val) = if σ x = 1 then -1 else 1 := by
    intro x
    rcases eq_or_ne (σ x) 1 with h | h
    · rw [h]; norm_num
    · rw [if_neg h]
      have hv : (σ x).val = 0 := by revert h; generalize σ x = a; fin_cases a <;> decide
      rw [hv]; norm_num
  rw [Finset.sum_congr rfl fun x _ => hpt x, Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  have hcard : (Finset.univ.filter fun x : Fin L => σ x = 1).card
      + (Finset.univ.filter fun x : Fin L => ¬ σ x = 1).card = L := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hcast : ((Finset.univ.filter fun x : Fin L => σ x = 1).card : ℂ)
      + ((Finset.univ.filter fun x : Fin L => ¬ σ x = 1).card : ℂ) = (L : ℂ) := by
    exact_mod_cast hcard
  simp only [nsmul_eq_mul, mul_neg, mul_one]
  linear_combination hcast

/-- **`D` is diagonal** with entry `clusterEnergy σ`. -/
theorem diagPauliZHamiltonianS_eq_diagonal (L : ℕ) :
    diagPauliZHamiltonianS L
      = Matrix.diagonal fun cfg : Fin L → Fin 2 => (clusterEnergy L cfg : ℂ) := by
  rw [diagPauliZHamiltonianS]
  ext σ' σ
  rw [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  by_cases h : σ' = σ
  · subst h
    rw [Matrix.diagonal_apply_eq]
    have hsum : (∑ x : Fin L, pauliZS x σ' σ') = ∑ x : Fin L, (-1 : ℂ) ^ ((σ' x).val) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [pauliZS_eq_diagonal, Matrix.diagonal_apply_eq]
    rw [hsum, sum_neg_one_pow_cfg, clusterEnergy]; push_cast; ring
  · rw [Matrix.diagonal_apply_ne _ h]
    have hsum : (∑ x : Fin L, pauliZS x σ' σ) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [pauliZS_eq_diagonal, Matrix.diagonal_apply_ne _ h]
    rw [hsum, mul_zero]

/-! ## Spectrum of `D` -/

/-- `clusterEnergy (all-zeros) = −L`. -/
private lemma clusterEnergy_const_zero (L : ℕ) : clusterEnergy L (fun _ => 0) = -(L : ℝ) := by
  rw [clusterEnergy]
  have : (Finset.univ.filter fun x : Fin L => (fun _ => (0 : Fin 2)) x = 1) = ∅ := by
    rw [Finset.filter_eq_empty_iff]; intro x _; exact (by decide : ¬ (0 : Fin 2) = 1)
  rw [this]; simp

/-- `clusterEnergy σ ≥ −L`. -/
private lemma clusterEnergy_ge (L : ℕ) (cfg : Fin L → Fin 2) : -(L : ℝ) ≤ clusterEnergy L cfg := by
  rw [clusterEnergy]
  have : (0 : ℝ) ≤ 2 * ((Finset.univ.filter fun x : Fin L => cfg x = 1).card : ℝ) := by positivity
  linarith

/-- If `clusterEnergy σ > −L` then `clusterEnergy σ ≥ −L + 2` (the second spectral value). -/
private lemma clusterEnergy_second (L : ℕ) (cfg : Fin L → Fin 2)
    (h : -(L : ℝ) < clusterEnergy L cfg) : -(L : ℝ) + 2 ≤ clusterEnergy L cfg := by
  rw [clusterEnergy] at h ⊢
  have hcardpos : 0 < (Finset.univ.filter fun x : Fin L => cfg x = 1).card := by
    rcases Nat.eq_zero_or_pos (Finset.univ.filter fun x : Fin L => cfg x = 1).card with h0 | hp
    · exfalso; rw [h0] at h; norm_num at h
    · exact hp
  have hk1 : (1 : ℝ) ≤ ((Finset.univ.filter fun x : Fin L => cfg x = 1).card : ℝ) := by
    exact_mod_cast hcardpos
  linarith

/-- `clusterEnergy σ ≠ −L` when `σ` is not the all-zeros configuration. -/
private lemma clusterEnergy_ne_of_ne (L : ℕ) (cfg : Fin L → Fin 2) (h : cfg ≠ fun _ => 0) :
    clusterEnergy L cfg ≠ -(L : ℝ) := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp h
  have hx1 : cfg x = 1 := by
    have h0 : cfg x ≠ 0 := hx
    revert h0; generalize cfg x = a; fin_cases a <;> decide
  have hmem : x ∈ Finset.univ.filter fun x : Fin L => cfg x = 1 := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hx1⟩
  have hcard : 1 ≤ (Finset.univ.filter fun x : Fin L => cfg x = 1).card :=
    Finset.card_pos.mpr ⟨x, hmem⟩
  rw [clusterEnergy]
  have : (1 : ℝ) ≤ ((Finset.univ.filter fun x : Fin L => cfg x = 1).card : ℝ) := by
    exact_mod_cast hcard
  intro hcontra; nlinarith

/-- There is a configuration with `clusterEnergy = −L + 2` when `0 < L` (a single excited site). -/
private lemma exists_clusterEnergy_second (L : ℕ) (hL : 0 < L) :
    ∃ cfg : Fin L → Fin 2, clusterEnergy L cfg = -(L : ℝ) + 2 := by
  refine ⟨Function.update (fun _ => 0) ⟨0, hL⟩ 1, ?_⟩
  rw [clusterEnergy]
  have hset : (Finset.univ.filter fun x : Fin L =>
      Function.update (fun _ => (0 : Fin 2)) ⟨0, hL⟩ 1 x = 1) = {⟨0, hL⟩} := by
    ext y
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hy⟩
      by_contra hne
      rw [Function.update_of_ne hne] at hy; exact absurd hy (by decide)
    · rintro rfl; exact ⟨Finset.mem_univ _, by rw [Function.update_self]⟩
  rw [hset, Finset.card_singleton]; push_cast; ring

/-- **`E_GS = −L` is the ground energy of `D`**. -/
theorem diagPauliZ_isGroundEnergy (L : ℕ) :
    IsGroundEnergy (diagPauliZHamiltonianS L) (-(L : ℝ)) := by
  rw [diagPauliZHamiltonianS_eq_diagonal, IsGroundEnergy, diagonal_realSpectrum]
  refine ⟨⟨fun _ => 0, clusterEnergy_const_zero L⟩, ?_⟩
  rintro E ⟨cfg, rfl⟩
  exact clusterEnergy_ge L cfg

/-- **The spectral gap of `D` is exactly `2`** (`0 < L` gives an excited configuration). -/
theorem diagPauliZ_isPositiveSpectralGap (L : ℕ) (hL : 0 < L) :
    IsPositiveSpectralGap (diagPauliZHamiltonianS L) 2 := by
  obtain ⟨cfg₁, hcfg₁⟩ := exists_clusterEnergy_second L hL
  refine ⟨-(L : ℝ), -(L : ℝ) + 2, diagPauliZ_isGroundEnergy L, ?_, by linarith, by ring, ?_⟩
  · rw [diagPauliZHamiltonianS_eq_diagonal, diagonal_realSpectrum]; exact ⟨cfg₁, hcfg₁⟩
  · rw [diagPauliZHamiltonianS_eq_diagonal, diagonal_realSpectrum]
    rintro E ⟨cfg, rfl⟩ hlt
    exact clusterEnergy_second L cfg hlt

/-- **Uniqueness of the ground eigenvector of `D`**: any eigenvector at `−L` is a multiple of the
all-zeros basis vector. -/
theorem diagPauliZ_ground_eigvec_unique (L : ℕ) (Ψ : (Fin L → Fin 2) → ℂ)
    (hΨ : (diagPauliZHamiltonianS L).mulVec Ψ = (-(L : ℝ) : ℂ) • Ψ) :
    Ψ = Ψ (fun _ => 0) • basisVecS (fun _ => (0 : Fin 2)) := by
  rw [diagPauliZHamiltonianS_eq_diagonal] at hΨ
  funext τ
  have hτ := congrFun hΨ τ
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at hτ
  by_cases h : τ = fun _ => 0
  · subst h; simp
  · have hE : (clusterEnergy L τ : ℂ) ≠ (-(L : ℝ) : ℂ) := by
      exact_mod_cast clusterEnergy_ne_of_ne L τ h
    have hΨτ : Ψ τ = 0 := by
      have hfac : ((clusterEnergy L τ : ℂ) - (-(L : ℝ) : ℂ)) * Ψ τ = 0 := by
        rw [sub_mul, hτ]; ring
      rcases mul_eq_zero.mp hfac with h1 | h1
      · exact absurd (sub_eq_zero.mp h1) hE
      · exact h1
    rw [hΨτ, Pi.smul_apply, basisVecS_of_ne h, smul_zero]

/-! ## Transport back to `Ĥ_BR` -/

/-- Conjugation carries an eigenvector: if `(V D V⁻¹) Ψ = E Ψ` then `D (V⁻¹ Ψ) = E (V⁻¹ Ψ)`. -/
private lemma conj_eigenvector {L N : ℕ} {V Vinv D : ManyBodyOpS (Fin L) N}
    (hVinvV : Vinv * V = 1) {Ψ : (Fin L → Fin (N + 1)) → ℂ} {E : ℂ}
    (h : (V * D * Vinv).mulVec Ψ = E • Ψ) :
    D.mulVec (Vinv.mulVec Ψ) = E • (Vinv.mulVec Ψ) := by
  have key : D * Vinv = Vinv * (V * D * Vinv) := by
    rw [← mul_assoc, ← mul_assoc, hVinvV, one_mul]
  calc D.mulVec (Vinv.mulVec Ψ)
      = (D * Vinv).mulVec Ψ := by rw [Matrix.mulVec_mulVec]
    _ = (Vinv * (V * D * Vinv)).mulVec Ψ := by rw [key]
    _ = Vinv.mulVec ((V * D * Vinv).mulVec Ψ) := by rw [Matrix.mulVec_mulVec]
    _ = Vinv.mulVec (E • Ψ) := by rw [h]
    _ = E • Vinv.mulVec Ψ := by rw [Matrix.mulVec_smul]

/-- Nonzero vectors survive conjugation. -/
private lemma clusterVinv_mulVec_ne_zero {L N : ℕ} {V Vinv : ManyBodyOpS (Fin L) N}
    (hVVinv : V * Vinv = 1) {Ψ : (Fin L → Fin (N + 1)) → ℂ} (hΨ : Ψ ≠ 0) :
    Vinv.mulVec Ψ ≠ 0 := by
  intro hzero
  apply hΨ
  have : V.mulVec (Vinv.mulVec Ψ) = Ψ := by
    rw [Matrix.mulVec_mulVec, hVVinv, Matrix.one_mulVec]
  rw [hzero, Matrix.mulVec_zero] at this
  exact this.symm

/-- Similarity preserves the real spectrum: `realSpectrum (V D V⁻¹) = realSpectrum D`. -/
theorem realSpectrum_conj_eq {L N : ℕ} {V Vinv D : ManyBodyOpS (Fin L) N}
    (hVVinv : V * Vinv = 1) (hVinvV : Vinv * V = 1) :
    realSpectrum (V * D * Vinv) = realSpectrum D := by
  ext E
  simp only [realSpectrum, Set.mem_setOf_eq]
  constructor
  · rintro ⟨Ψ, hΨ, heq⟩
    exact ⟨Vinv.mulVec Ψ, clusterVinv_mulVec_ne_zero hVVinv hΨ, conj_eigenvector hVinvV heq⟩
  · rintro ⟨Φ, hΦ, heq⟩
    refine ⟨V.mulVec Φ, clusterVinv_mulVec_ne_zero hVinvV hΦ, ?_⟩
    have key : (V * D * Vinv) * V = V * D := by rw [mul_assoc, hVinvV, mul_one]
    calc (V * D * Vinv).mulVec (V.mulVec Φ)
        = ((V * D * Vinv) * V).mulVec Φ := by rw [Matrix.mulVec_mulVec]
      _ = (V * D).mulVec Φ := by rw [key]
      _ = V.mulVec (D.mulVec Φ) := by rw [Matrix.mulVec_mulVec]
      _ = V.mulVec ((E : ℂ) • Φ) := by rw [heq]
      _ = (E : ℂ) • V.mulVec Φ := by rw [Matrix.mulVec_smul]

/-! ## The cluster state and Theorem 7.8 -/

/-- The **cluster state** `Φ_C = Û_C W e₀ = V e₀`: the all-plus product state sent through the
controlled-`Z` unitary (eq. (7.3.29)). -/
noncomputable def clusterStateVec (G : SimpleGraph (Fin L)) [DecidableRel G.Adj] :
    (Fin L → Fin 2) → ℂ :=
  (clusterV G).mulVec (basisVecS (fun _ => (0 : Fin 2)))

/-- **Cluster-state predicate** `IsClusterState G Φ`: `Φ` is the Briegel–Raussendorf / graph state
of `G` (eq. (7.3.29)), the explicit vector `clusterStateVec G = Û_C · (all-plus)` obtained from the
controlled-`Z` construction. -/
def IsClusterState (G : SimpleGraph (Fin L)) [DecidableRel G.Adj]
    (Φ : (Fin L → Fin 2) → ℂ) : Prop :=
  Φ = clusterStateVec G

/-- The cluster state satisfies its own predicate (non-vacuity witness). -/
theorem isClusterState_clusterStateVec (G : SimpleGraph (Fin L)) [DecidableRel G.Adj] :
    IsClusterState G (clusterStateVec G) := rfl

/-- The cluster state is nonzero. -/
theorem clusterStateVec_ne_zero (G : SimpleGraph (Fin L)) [DecidableRel G.Adj] :
    clusterStateVec G ≠ 0 := by
  intro hzero
  rw [clusterStateVec] at hzero
  have hbasis : (clusterVinv G).mulVec ((clusterV G).mulVec (basisVecS (fun _ => (0 : Fin 2))))
      = basisVecS (fun _ => (0 : Fin 2)) := by
    rw [Matrix.mulVec_mulVec, clusterVinv_mul_clusterV, Matrix.one_mulVec]
  rw [hzero, Matrix.mulVec_zero] at hbasis
  have hz : (basisVecS (fun _ => (0 : Fin 2)) : (Fin L → Fin 2) → ℂ) (fun _ => 0) = 0 := by
    rw [← hbasis]; rfl
  rw [basisVecS_self] at hz
  exact one_ne_zero hz

/-- **Tasaki Theorem 7.8 (the cluster state is the unique gapped ground state).**  The
Briegel–Raussendorf / graph state `Φ` (`IsClusterState`) is the **unique ground state** of the
stabilizer Hamiltonian `Ĥ_BR = −Σ_x K̂_x` (eq. (7.3.30)): the ground energy is `E_GS = −N`
(`N = |Λ| = L`), the gap above it is **exactly `2`** (`IsPositiveSpectralGap … 2`), and every
ground-energy eigenvector is a scalar multiple of `Φ`.  Proved by mapping `Ĥ_BR` to the trivial
paramagnet `Ĥ_→ = −Σ_x σ̂_x^{(1)}` through the controlled-`Z` unitary `Û_C` (`Û_C² = 1`) and
then diagonalizing with the Hadamard operator.  The hypothesis `0 < L` excludes the empty lattice,
where the Hilbert space is one-dimensional and there is no excited state for the gap.
Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer, 2020), §7.3.3,
Theorem 7.8, eqs. (7.3.29)–(7.3.37), pp. 217–220. -/
theorem tasaki_theorem_7_8 (G : SimpleGraph (Fin L)) [DecidableRel G.Adj] (hL : 0 < L)
    (Φ : (Fin L → Fin 2) → ℂ) (hΦ : IsClusterState G Φ) :
    IsGroundEnergy (graphStateHamiltonianS G) (-(Fintype.card (Fin L) : ℝ)) ∧
      IsPositiveSpectralGap (graphStateHamiltonianS G) 2 ∧ Φ ≠ 0 ∧
        ∀ Ψ : (Fin L → Fin 2) → ℂ, Ψ ≠ 0 →
          (graphStateHamiltonianS G).mulVec Ψ = (-(Fintype.card (Fin L) : ℝ) : ℂ) • Ψ →
            ∃ c : ℂ, Ψ = c • Φ := by
  rw [IsClusterState] at hΦ
  have hVVinv := clusterV_mul_clusterVinv G
  have hVinvV := clusterVinv_mul_clusterV G
  have hspec : realSpectrum (graphStateHamiltonianS G)
      = realSpectrum (diagPauliZHamiltonianS L) := by
    rw [graphStateHamiltonianS_eq_conj, realSpectrum_conj_eq hVVinv hVinvV]
  rw [Fintype.card_fin]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [IsGroundEnergy, hspec]; exact diagPauliZ_isGroundEnergy L
  · have hgap := diagPauliZ_isPositiveSpectralGap L hL
    rw [IsPositiveSpectralGap] at hgap ⊢
    obtain ⟨E₀, E₁, hg, hE₁, hlt, hgapval, hmin⟩ := hgap
    refine ⟨E₀, E₁, ?_, ?_, hlt, hgapval, ?_⟩
    · rw [IsGroundEnergy, hspec]; exact hg
    · rw [hspec]; exact hE₁
    · intro E hE hlt'; rw [hspec] at hE; exact hmin E hE hlt'
  · rw [hΦ]; exact clusterStateVec_ne_zero G
  · intro Ψ hΨ heq
    rw [graphStateHamiltonianS_eq_conj] at heq
    have hDeig := conj_eigenvector hVinvV heq
    have huniq := diagPauliZ_ground_eigvec_unique L ((clusterVinv G).mulVec Ψ) hDeig
    refine ⟨(clusterVinv G).mulVec Ψ (fun _ => 0), ?_⟩
    rw [hΦ, clusterStateVec]
    have hrecover : (clusterV G).mulVec ((clusterVinv G).mulVec Ψ) = Ψ := by
      rw [Matrix.mulVec_mulVec, hVVinv, Matrix.one_mulVec]
    calc Ψ = (clusterV G).mulVec ((clusterVinv G).mulVec Ψ) := hrecover.symm
      _ = (clusterV G).mulVec
          ((clusterVinv G).mulVec Ψ (fun _ => 0) • basisVecS (fun _ => (0 : Fin 2))) := by
            rw [← huniq]
      _ = (clusterVinv G).mulVec Ψ (fun _ => 0) •
          (clusterV G).mulVec (basisVecS (fun _ => (0 : Fin 2))) := by rw [Matrix.mulVec_smul]

end LatticeSystem.Quantum
