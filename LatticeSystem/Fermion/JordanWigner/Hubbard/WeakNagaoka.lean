import LatticeSystem.Fermion.JordanWigner.Hubbard.EffectiveHamiltonianMatrix
import Mathlib.Analysis.MeanInequalities

/-!
# The Cauchy–Schwarz energy bound toward weak Nagaoka ferromagnetism (11.2.9)

This file formalizes the Schwarz step of Tasaki's proof of the weak version of
Nagaoka's theorem (§11.2.1, eq. (11.2.9)). For an arbitrary real expansion of a
state in the one-hole Tasaki basis,

  `|Φ⟩ = Σ_{x,σ} ϕ(x,σ) |Φ_{x,σ}⟩`,

the effective-Hamiltonian energy `⟨Φ|Ĥ_eff|Φ⟩` is bounded below by the energy of
the *ferromagnetic* state

  `|Φ_↑⟩ = Σ_x ξ_x |Φ_{x,(↑)}⟩`,   `ξ_x = (Σ_σ ϕ(x,σ)²)^{1/2}`,

provided the hopping amplitudes are non-negative (`t_{x,y} ≥ 0`) and there is no
self-hopping (`t_{i,i} = 0`). This is the inequality `⟨Φ|Ĥ_eff|Φ⟩ ≥
⟨Φ_↑|Ĥ_eff|Φ_↑⟩` of (11.2.9), and it shows that `|Φ_↑⟩` is also a ground state.

The spin configurations on `Λ \ {x}` are encoded as the subtype
`HoleSpin N x` of configurations whose hole-site spin is canonically `↑`, so
that each one-hole configuration is parametrized exactly once. The
hole-moving map `σ ↦ σ_{y→x}` becomes a bijection `holeSpinMoveEquiv` between
`HoleSpin N x` and `HoleSpin N y`, which lets the Cauchy–Schwarz reindexing
`Σ_σ ϕ(y, σ_{y→x})² = ξ_y²` go through.

Tracked in Issue #4130. Reference: Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, 1st edition, §11.2.1, eq. (11.2.9), pp. 384-385.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-! ## Canonical hole-spin configurations -/

/-- The spin configurations relevant to a hole at site `x`: configurations on
all sites whose hole-site spin is canonically fixed to `↑` (`true`). Each
one-hole hard-core configuration `hubbardOneHoleConfig N x σ` (which ignores
`σ x`) is parametrized exactly once by an element of `HoleSpin N x`. -/
def HoleSpin (N : ℕ) (x : Fin (N + 1)) : Type :=
  {σ : Fin (N + 1) → Bool // σ x = true}

instance (N : ℕ) (x : Fin (N + 1)) : Fintype (HoleSpin N x) :=
  Subtype.fintype _

instance (N : ℕ) (x : Fin (N + 1)) : DecidableEq (HoleSpin N x) :=
  Subtype.instDecidableEq

/-- The hole-moving map on canonical hole-spin configurations: moving the
electron from `x` into the hole `y` and re-canonicalizing the new hole `y` to
`↑`. This realizes Tasaki's `σ ↦ σ_{y→x}` as a map `HoleSpin N x → HoleSpin N y`
(here written for a hole moving `x → y`). -/
def holeSpinMove (N : ℕ) (x y : Fin (N + 1)) (σ : HoleSpin N x) : HoleSpin N y :=
  ⟨Function.update (Function.update σ.val x (σ.val y)) y true, by
    rw [Function.update_self]⟩

/-- `holeSpinMove` is a bijection between `HoleSpin N x` and `HoleSpin N y`
(for `x ≠ y`): its inverse moves the electron back from `y` to `x`. -/
def holeSpinMoveEquiv (N : ℕ) {x y : Fin (N + 1)} (hxy : x ≠ y) :
    HoleSpin N x ≃ HoleSpin N y where
  toFun := holeSpinMove N x y
  invFun := holeSpinMove N y x
  left_inv σ := by
    apply Subtype.ext
    funext p
    by_cases hpx : p = x <;> by_cases hpy : p = y <;>
      simp_all [holeSpinMove, σ.2, hxy.symm]
  right_inv τ := by
    apply Subtype.ext
    funext p
    by_cases hpx : p = x <;> by_cases hpy : p = y <;>
      simp_all [holeSpinMove, τ.2, hxy.symm]

/-- The all-spin-up configuration `(↑)`, a canonical hole-spin element at any
hole. -/
def holeSpinUp (N : ℕ) (x : Fin (N + 1)) : HoleSpin N x :=
  ⟨fun _ => true, rfl⟩

/-- The hole moves the all-up configuration to the all-up configuration. -/
theorem holeSpinMove_up (N : ℕ) (x y : Fin (N + 1)) :
    holeSpinMove N x y (holeSpinUp N x) = holeSpinUp N y := by
  apply Subtype.ext
  funext p
  simp [holeSpinMove, holeSpinUp]

/-! ## The effective-Hamiltonian energy and its quadratic form -/

/-- The basis state family indexed by a hole site and a canonical hole-spin
configuration. -/
noncomputable def tasakiState (N : ℕ) (p : (x : Fin (N + 1)) × HoleSpin N x) :
    (Fin (2 * N + 2) → Fin 2) → ℂ :=
  hubbardTasakiBasisState N p.1 p.2.val

/-- The real-bilinear effective-Hamiltonian energy of a state. -/
noncomputable def hubbardEffEnergy (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ)
    (U : ℂ) (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) : ℂ :=
  ∑ w : Fin (2 * N + 2) → Fin 2, ψ w * (hubbardEffectiveHamiltonian N t U *ᵥ ψ) w

/-- Quadratic-form expansion of the energy of a state expanded in the Tasaki
basis: `⟨Φ|Ĥ_eff|Φ⟩ = Σ_p Σ_q c_p c_q ⟨Φ_p|Ĥ_eff|Φ_q⟩`. -/
theorem hubbardEffEnergy_expand (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (c : ((x : Fin (N + 1)) × HoleSpin N x) → ℂ) :
    hubbardEffEnergy N t U (∑ p, c p • tasakiState N p) =
      ∑ p, ∑ q, c p * c q *
        (∑ w : Fin (2 * N + 2) → Fin 2,
          tasakiState N p w * (hubbardEffectiveHamiltonian N t U *ᵥ tasakiState N q) w) := by
  unfold hubbardEffEnergy
  have hmv : (hubbardEffectiveHamiltonian N t U *ᵥ ∑ q, c q • tasakiState N q) =
      ∑ q, c q • (hubbardEffectiveHamiltonian N t U *ᵥ tasakiState N q) := by
    rw [Matrix.mulVec_sum]
    exact Finset.sum_congr rfl (fun q _ => Matrix.mulVec_smul _ _ _)
  rw [hmv]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun w _ => Finset.sum_mul_sum _ _ _ _)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun w _ => by ring)

/-! ## Bridge between configuration equality and the hole-move bijection -/

/-- A `Fin 2` value is `0` or `1`. -/
private theorem fin_two_cases' (r : Fin 2) : r = 0 ∨ r = 1 := by
  rcases r with ⟨rv, hrv⟩; interval_cases rv
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The one-hole configuration depends on the spin assignment only off the hole
site. -/
theorem oneHoleConfig_congr (N : ℕ) (x : Fin (N + 1)) (σ₁ σ₂ : Fin (N + 1) → Bool)
    (h : ∀ z, z ≠ x → σ₁ z = σ₂ z) :
    hubbardOneHoleConfig N x σ₁ = hubbardOneHoleConfig N x σ₂ := by
  funext k
  obtain ⟨z, r, rfl⟩ := exists_spinfulIndex N k
  by_cases hzx : z = x
  · subst hzx
    rcases fin_two_cases' r with rfl | rfl
    · simp [hubbardOneHoleConfig_apply_up]
    · simp [hubbardOneHoleConfig_apply_down]
  · have hzx' : z.val ≠ x.val := fun hh => hzx (Fin.ext hh)
    rcases fin_two_cases' r with rfl | rfl
    · rw [hubbardOneHoleConfig_apply_up, hubbardOneHoleConfig_apply_up, h z hzx]
    · rw [hubbardOneHoleConfig_apply_down, hubbardOneHoleConfig_apply_down, h z hzx]

/-- Conversely, configuration equality forces the spin assignments to agree off
the hole site. -/
theorem oneHoleConfig_spin_eq (N : ℕ) (x : Fin (N + 1)) (σ₁ σ₂ : Fin (N + 1) → Bool)
    (h : hubbardOneHoleConfig N x σ₁ = hubbardOneHoleConfig N x σ₂)
    (z : Fin (N + 1)) (hzx : z ≠ x) : σ₁ z = σ₂ z := by
  have hzx' : z.val ≠ x.val := fun hh => hzx (Fin.ext hh)
  have e := congrFun h (spinfulIndex N z 0)
  rw [hubbardOneHoleConfig_apply_up, hubbardOneHoleConfig_apply_up, if_neg hzx',
    if_neg hzx'] at e
  by_cases h1 : σ₁ z <;> by_cases h2 : σ₂ z <;> simp_all

/-- The hole-move bridge: for `x ≠ y`, the moved configuration
`C_x(σ_{x→y of τ})` equals `C_{x} σ` exactly when `τ` is the hole-move image
`holeSpinMove N x y σ`. This is the uniqueness underlying the collapse of the
matrix-element indicator sum. -/
theorem oneHoleConfig_move_eq_iff (N : ℕ) {x y : Fin (N + 1)} (hxy : x ≠ y)
    (σ : HoleSpin N x) (τ : HoleSpin N y) :
    hubbardOneHoleConfig N x (hubbardSpinMove N τ.val y x) =
        hubbardOneHoleConfig N x σ.val ↔ τ = holeSpinMove N x y σ := by
  have hyx : y ≠ x := fun h => hxy h.symm
  constructor
  · intro h
    apply Subtype.ext
    funext p
    have key : ∀ z, z ≠ x → (Function.update τ.val y (τ.val x)) z = σ.val z := by
      intro z hz
      have := oneHoleConfig_spin_eq N x _ _ h z hz
      simpa [hubbardSpinMove] using this
    by_cases hpx : p = x
    · subst hpx
      have := key y hyx
      rw [Function.update_self] at this
      simp [holeSpinMove, hxy, this]
    · by_cases hpy : p = y
      · subst hpy; simp [holeSpinMove, τ.2]
      · have := key p hpx
        rw [Function.update_of_ne hpy] at this
        simp [holeSpinMove, hpx, hpy, this]
  · intro h
    subst h
    refine oneHoleConfig_congr N x _ _ (fun z hz => ?_)
    simp only [hubbardSpinMove, holeSpinMove, Function.update_apply]
    by_cases hzy : z = y
    · subst hzy; simp [hxy]
    · simp [hz, hzy]

/-! ## The energy as an explicit quadratic form -/

/-- Tasaki eq. (11.2.9) line 2: the effective-Hamiltonian energy of a Tasaki-basis
expansion is the off-diagonal quadratic form `-Σ_{x≠y} t_{y,x} Σ_σ c_{x,σ}
c_{y, σ_{x→y}}` (no self-hopping `t_{ii}=0` makes the diagonal vanish). -/
theorem hubbardEffEnergy_tasaki_quadratic (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) (htdiag : ∀ i, t i i = 0)
    (c : ((x : Fin (N + 1)) × HoleSpin N x) → ℂ) :
    hubbardEffEnergy N t U (∑ p, c p • tasakiState N p) =
      ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
        (if x = y then 0 else
          -(t y x) * ∑ σ : HoleSpin N x, c ⟨x, σ⟩ * c ⟨y, holeSpinMove N x y σ⟩) := by
  have inner : ∀ (x y : Fin (N + 1)),
      (∑ σ : HoleSpin N x, ∑ τ : HoleSpin N y, c ⟨x, σ⟩ * c ⟨y, τ⟩ *
        (∑ w : Fin (2 * N + 2) → Fin 2, tasakiState N ⟨x, σ⟩ w *
          (hubbardEffectiveHamiltonian N t U *ᵥ tasakiState N ⟨y, τ⟩) w)) =
      if x = y then 0 else
        -(t y x) * ∑ σ : HoleSpin N x, c ⟨x, σ⟩ * c ⟨y, holeSpinMove N x y σ⟩ := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl]
      refine Finset.sum_eq_zero (fun σ _ => Finset.sum_eq_zero (fun τ _ => ?_))
      simp only [tasakiState]
      rw [hubbardEffective_tasaki_matrixElement_diag N x τ.val σ.val t U htdiag,
        mul_zero]
    · rw [if_neg hxy]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      -- inner τ-sum collapses to τ = holeSpinMove
      rw [show (∑ τ : HoleSpin N y, c ⟨x, σ⟩ * c ⟨y, τ⟩ *
            (∑ w, tasakiState N ⟨x, σ⟩ w *
              (hubbardEffectiveHamiltonian N t U *ᵥ tasakiState N ⟨y, τ⟩) w)) =
          ∑ τ : HoleSpin N y, c ⟨x, σ⟩ * c ⟨y, τ⟩ *
            (-(t y x) * (if τ = holeSpinMove N x y σ then 1 else 0)) from
        Finset.sum_congr rfl (fun τ _ => by
          unfold tasakiState
          rw [hubbardEffective_tasaki_matrixElement N y x τ.val σ.val t U
            (fun h => hxy h.symm)]
          congr 2
          by_cases hb : hubbardOneHoleConfig N x (hubbardSpinMove N τ.val y x) =
              hubbardOneHoleConfig N x σ.val
          · rw [if_pos hb, if_pos ((oneHoleConfig_move_eq_iff N hxy σ τ).mp hb)]
          · rw [if_neg hb, if_neg (fun h => hb ((oneHoleConfig_move_eq_iff N hxy σ τ).mpr h))])]
      rw [show (∑ τ : HoleSpin N y, c ⟨x, σ⟩ * c ⟨y, τ⟩ *
            (-(t y x) * (if τ = holeSpinMove N x y σ then 1 else 0))) =
          ∑ τ : HoleSpin N y, (if τ = holeSpinMove N x y σ then
            c ⟨x, σ⟩ * c ⟨y, τ⟩ * -(t y x) else 0) from
        Finset.sum_congr rfl (fun τ _ => by split_ifs <;> ring),
        Finset.sum_ite_eq' Finset.univ (holeSpinMove N x y σ)
          (fun τ => c ⟨x, σ⟩ * c ⟨y, τ⟩ * -(t y x))]
      simp only [Finset.mem_univ, if_true]
      ring
  rw [hubbardEffEnergy_expand, Fintype.sum_sigma]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [show (∑ σ : HoleSpin N x, ∑ q, c ⟨x, σ⟩ * c q *
        (∑ w, tasakiState N ⟨x, σ⟩ w *
          (hubbardEffectiveHamiltonian N t U *ᵥ tasakiState N q) w)) =
      ∑ σ : HoleSpin N x, ∑ y : Fin (N + 1), ∑ τ : HoleSpin N y,
        c ⟨x, σ⟩ * c ⟨y, τ⟩ *
        (∑ w, tasakiState N ⟨x, σ⟩ w *
          (hubbardEffectiveHamiltonian N t U *ᵥ tasakiState N ⟨y, τ⟩) w) from
    Finset.sum_congr rfl (fun σ _ => by rw [Fintype.sum_sigma])]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun y _ => inner x y)

/-! ## The Cauchy–Schwarz energy bound (11.2.9) -/

/-- The real off-diagonal quadratic form `Σ_{x≠y} (-t_{y,x}) Σ_σ ϕ_{x,σ}
ϕ_{y, σ_{x→y}}` underlying the effective-Hamiltonian energy of a Tasaki-basis
expansion with real coefficients `ϕ`. -/
noncomputable def tasakiQuadForm (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (ϕ : ((x : Fin (N + 1)) × HoleSpin N x) → ℝ) : ℝ :=
  ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
    (if x = y then 0 else
      -(t y x) * ∑ σ : HoleSpin N x, ϕ ⟨x, σ⟩ * ϕ ⟨y, holeSpinMove N x y σ⟩)

/-- The ferromagnetic amplitude `ξ_x = (Σ_σ ϕ(x,σ)²)^{1/2}` of (11.2.7). -/
noncomputable def ferroXi (N : ℕ) (ϕ : ((x : Fin (N + 1)) × HoleSpin N x) → ℝ)
    (x : Fin (N + 1)) : ℝ :=
  Real.sqrt (∑ σ : HoleSpin N x, (ϕ ⟨x, σ⟩) ^ 2)

/-- The coefficients of the ferromagnetic state `|Φ_↑⟩` of (11.2.8): weight
`ξ_x` on the all-up configuration at each hole, `0` otherwise. -/
noncomputable def ferroCoeff (N : ℕ) (ϕ : ((x : Fin (N + 1)) × HoleSpin N x) → ℝ) :
    ((x : Fin (N + 1)) × HoleSpin N x) → ℝ :=
  fun p => if p.2 = holeSpinUp N p.1 then ferroXi N ϕ p.1 else 0

/-- `ξ_x ≥ 0`. -/
theorem ferroXi_nonneg (N : ℕ) (ϕ : ((x : Fin (N + 1)) × HoleSpin N x) → ℝ)
    (x : Fin (N + 1)) : 0 ≤ ferroXi N ϕ x :=
  Real.sqrt_nonneg _

/-- Reindexing identity: summing `ϕ(y, ·)²` over the hole-move images of
`HoleSpin N x` recovers `ξ_y²`. -/
theorem sum_sq_holeSpinMove (N : ℕ) {x y : Fin (N + 1)} (hxy : x ≠ y)
    (ϕ : ((x : Fin (N + 1)) × HoleSpin N x) → ℝ) :
    (∑ σ : HoleSpin N x, (ϕ ⟨y, holeSpinMove N x y σ⟩) ^ 2) =
      ∑ τ : HoleSpin N y, (ϕ ⟨y, τ⟩) ^ 2 := by
  rw [← Equiv.sum_comp (holeSpinMoveEquiv N hxy) (fun τ => (ϕ ⟨y, τ⟩) ^ 2)]
  rfl

/-- Per-pair Cauchy–Schwarz: `Σ_σ ϕ_{x,σ} ϕ_{y, σ_{x→y}} ≤ ξ_x ξ_y`. -/
theorem sum_mul_holeSpinMove_le (N : ℕ) {x y : Fin (N + 1)} (hxy : x ≠ y)
    (ϕ : ((x : Fin (N + 1)) × HoleSpin N x) → ℝ) :
    (∑ σ : HoleSpin N x, ϕ ⟨x, σ⟩ * ϕ ⟨y, holeSpinMove N x y σ⟩) ≤
      ferroXi N ϕ x * ferroXi N ϕ y := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun σ : HoleSpin N x => ϕ ⟨x, σ⟩) (fun σ => ϕ ⟨y, holeSpinMove N x y σ⟩)
  rw [sum_sq_holeSpinMove N hxy] at hcs
  -- hcs : (Σ ϕϕ)² ≤ (Σ ϕ_x²)(Σ ϕ_y²) = ξ_x² ξ_y²
  have hsq : (∑ σ : HoleSpin N x, ϕ ⟨x, σ⟩ * ϕ ⟨y, holeSpinMove N x y σ⟩) ^ 2 ≤
      (ferroXi N ϕ x * ferroXi N ϕ y) ^ 2 := by
    rw [mul_pow, ferroXi, ferroXi, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
      Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact hcs
  exact (abs_le_of_sq_le_sq' hsq
    (mul_nonneg (ferroXi_nonneg N ϕ x) (ferroXi_nonneg N ϕ y))).2

/-- The ferromagnetic quadratic-form term factorizes as `ξ_x ξ_y`. -/
theorem sum_ferroCoeff_holeSpinMove (N : ℕ) (x y : Fin (N + 1))
    (ϕ : ((x : Fin (N + 1)) × HoleSpin N x) → ℝ) :
    (∑ σ : HoleSpin N x, ferroCoeff N ϕ ⟨x, σ⟩ *
        ferroCoeff N ϕ ⟨y, holeSpinMove N x y σ⟩) =
      ferroXi N ϕ x * ferroXi N ϕ y := by
  rw [Finset.sum_eq_single (holeSpinUp N x)]
  · rw [holeSpinMove_up]; simp [ferroCoeff]
  · intro σ _ hσ; simp [ferroCoeff, hσ]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Tasaki eq. (11.2.9): the Cauchy–Schwarz energy bound.** For non-negative
hopping amplitudes (`t_{i,j} ≥ 0`), the off-diagonal effective-Hamiltonian
energy of any real Tasaki-basis expansion `ϕ` is bounded below by that of the
associated ferromagnetic state `|Φ_↑⟩` (with amplitudes `ξ_x`). Hence `|Φ_↑⟩`
attains the minimum, the weak-Nagaoka conclusion. -/
theorem tasakiQuadForm_ferro_le (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (hpos : ∀ i j, 0 ≤ t i j) (ϕ : ((x : Fin (N + 1)) × HoleSpin N x) → ℝ) :
    tasakiQuadForm N t (ferroCoeff N ϕ) ≤ tasakiQuadForm N t ϕ := by
  unfold tasakiQuadForm
  refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => ?_))
  by_cases hxy : x = y
  · simp [hxy]
  · rw [if_neg hxy, if_neg hxy, sum_ferroCoeff_holeSpinMove N x y ϕ]
    exact mul_le_mul_of_nonpos_left (sum_mul_holeSpinMove_le N hxy ϕ)
      (by have := hpos y x; linarith)

/-- The effective-Hamiltonian energy of a real Tasaki-basis expansion equals
(the complexification of) the real quadratic form. -/
theorem hubbardEffEnergy_eq_quadForm (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (U : ℂ) (htdiag : ∀ i, t i i = 0)
    (ψ : ((x : Fin (N + 1)) × HoleSpin N x) → ℝ) :
    hubbardEffEnergy N (fun i j => (t i j : ℂ)) U
        (∑ p, (ψ p : ℂ) • tasakiState N p) = (tasakiQuadForm N t ψ : ℂ) := by
  rw [hubbardEffEnergy_tasaki_quadratic N (fun i j => (t i j : ℂ)) U
    (fun i => by simp [htdiag i]) (fun p => (ψ p : ℂ)),
    tasakiQuadForm]
  push_cast
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  by_cases hxy : x = y
  · simp [hxy]
  · rw [if_neg hxy, if_neg hxy]
    push_cast
    ring

/-- **Weak Nagaoka, energy form (Tasaki eq. (11.2.9)).** With non-negative
hopping (`t ≥ 0`) and no self-hopping (`t_{ii} = 0`), the effective-Hamiltonian
energy of the ferromagnetic state `|Φ_↑⟩` is `≤` that of any real Tasaki-basis
expansion `|Φ⟩`; hence `|Φ_↑⟩` is also a ground state. -/
theorem hubbardWeakNagaoka_energy_bound (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (U : ℂ) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j)
    (ϕ : ((x : Fin (N + 1)) × HoleSpin N x) → ℝ) :
    (hubbardEffEnergy N (fun i j => (t i j : ℂ)) U
          (∑ p, (ferroCoeff N ϕ p : ℂ) • tasakiState N p)).re ≤
      (hubbardEffEnergy N (fun i j => (t i j : ℂ)) U
          (∑ p, (ϕ p : ℂ) • tasakiState N p)).re := by
  rw [hubbardEffEnergy_eq_quadForm N t U htdiag, hubbardEffEnergy_eq_quadForm N t U htdiag,
    Complex.ofReal_re, Complex.ofReal_re]
  exact tasakiQuadForm_ferro_le N t hpos ϕ

end LatticeSystem.Fermion
