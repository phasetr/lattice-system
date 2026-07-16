/-
Staggered relabel bridging the classical mirror reflections to the quantum signed field copies
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer: symmetrisation stage PR7d-ii).

The classical cyclic averaging inequality `reflectionPositivity_averaging` (Tasaki Lemma 4.5,
(4.1.55)–(4.1.57), pp. 87–88) is stated for the **sign-free** mirror reflections
`reflectLeft`/`reflectRight` (`LatticeSystem/Math/ReflectionPositivityAveraging.lean`).  The quantum
one reflection step (PR7c) instead produces the **signed** reflected field copies
`ringFieldReflectLeft n h = physFieldOf n h h`, whose right half carries a minus sign
`h_L z = −h (r z)` (DLS/Marshall structure).  Reconciling these two conventions is the point Tasaki
§4.1 explicitly defers at the field Hamiltonian (4.1.48), book pp. 85–86, where the field enters as
`Ŝ⁽³⁾ₓ − (−1)ˣ h_x` with a **staggered** `(−1)ˣ` factor.

This file discharges that `−(−1)ˣ` sign decision once and for all by the **staggered relabel**
`P h z = (−1)^z · h z`.  It is a period-2 involution whose right-half sign `(−1)^{r z} = −(−1)^z`
(the bond reflection `r = ringReflect n` maps `z ↦ 2n−1−z`, flipping the staggered sublattice,
`ringStaggeredSublattice_ringReflect`) exactly cancels the `physFieldOf` minus sign `−h (r z)`.
Consequently `P` carries the classical mirror reflections onto the quantum signed field copies:
`P (reflectLeft g) = ringFieldReflectLeft (P g)` and `P (reflectRight g) = ringFieldReflectRight
(P g)`.  After this relabel the classical Lemma 4.5 applies verbatim (consumed downstream in
PR7d-iii).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, staggered field Hamiltonian (4.1.48) and reflected field copies (4.1.50), pp. 85–86;
chessboard estimate Lemma 4.5, (4.1.55)–(4.1.57), pp. 87–88.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionFieldPartition
import LatticeSystem.Math.ReflectionPositivityAveraging

namespace LatticeSystem.Quantum

/-- **Bond reflection equals `Fin.rev`.**  On `Fin (2n)` the geometric bond reflection
`ringReflect n z = 2n−1−z` coincides with the generic reverse `z.rev = 2n−(z+1)` used by the
classical mirror reflections `reflectLeft`/`reflectRight`; both send `z ↦ 2n−1−z`. -/
private lemma ringReflect_eq_rev (n : ℕ) (z : Fin (2 * n)) :
    z.rev = ringReflect n z := by
  apply Fin.ext
  rw [Fin.val_rev, ringReflect_val]
  have := z.isLt
  omega

/-- **The staggered sign flips under the bond reflection.**  With `r = ringReflect n`,
`(−1)^{r z} = −(−1)^z`, because `r z = 2n−1−z` and `2n−1` is odd (`ringStaggeredSublattice_
ringReflect`).  This is the sign that cancels the `physFieldOf` right-half minus sign `−h (r z)`,
resolving the `−(−1)ˣ` convention of Tasaki's staggered field Hamiltonian (4.1.48), pp. 85–86. -/
private lemma neg_one_pow_ringReflect (n : ℕ) (z : Fin (2 * n)) :
    (-1 : ℝ) ^ (ringReflect n z : ℕ) = -(-1 : ℝ) ^ (z : ℕ) := by
  have hval : (ringReflect n z : ℕ) = 2 * n - 1 - (z : ℕ) := ringReflect_val n z
  have hlt : (z : ℕ) < 2 * n := z.isLt
  rw [hval]
  have hsum : (2 * n - 1 - (z : ℕ)) + (z : ℕ) = 2 * n - 1 := by omega
  have hodd : (-1 : ℝ) ^ (2 * n - 1) = -1 := Odd.neg_one_pow ⟨n - 1, by omega⟩
  have h1 : (-1 : ℝ) ^ (2 * n - 1 - (z : ℕ)) * (-1 : ℝ) ^ (z : ℕ) = -1 := by
    rw [← pow_add, hsum, hodd]
  have hsq : (-1 : ℝ) ^ (z : ℕ) * (-1 : ℝ) ^ (z : ℕ) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have step : (-1 : ℝ) ^ (2 * n - 1 - (z : ℕ)) * ((-1 : ℝ) ^ (z : ℕ) * (-1 : ℝ) ^ (z : ℕ))
      = -(-1 : ℝ) ^ (z : ℕ) := by
    rw [← mul_assoc, h1]; ring
  rwa [hsq, mul_one] at step

/-- **Staggered relabel** `P h z = (−1)^z · h z` (Tasaki §4.1, staggered field factor of (4.1.48),
pp. 85–86).  A period-2 involution (`ringStaggeredRelabel_involutive`) whose right-half sign flip
carries the classical sign-free mirror reflections onto the quantum signed field copies. -/
def ringStaggeredRelabel (n : ℕ) (h : Fin (2 * n) → ℝ) : Fin (2 * n) → ℝ :=
  fun z => (-1 : ℝ) ^ (z : ℕ) * h z

/-- **The staggered relabel is an involution:** `P (P h) = h`, since `(−1)^z · (−1)^z = 1`.  This
lets PR7d-iii recover an arbitrary physical field `h` as `P g` with `g = P h`, feeding it into the
classical averaging inequality (Tasaki Lemma 4.5, pp. 87–88). -/
theorem ringStaggeredRelabel_involutive (n : ℕ) :
    Function.Involutive (ringStaggeredRelabel n) := by
  intro h
  funext z
  simp only [ringStaggeredRelabel]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- **Left mirror ↔ signed left field copy.**  `P (reflectLeft g) = ringFieldReflectLeft (P g)`
(Tasaki §4.1, reflected field copies (4.1.50), pp. 85–86).  On the left half both sides are
`(−1)^z g z`; on the right half the classical mirror gives `(−1)^z g (r z)` while the signed copy
gives `−(P g)(r z) = −(−1)^{r z} g (r z) = (−1)^z g (r z)` — equal because `(−1)^{r z} = −(−1)^z`
(`neg_one_pow_ringReflect`) cancels the `physFieldOf` minus sign. -/
theorem ringStaggeredRelabel_reflectLeft (n : ℕ) (g : Fin (2 * n) → ℝ) :
    ringStaggeredRelabel n (LatticeSystem.Math.reflectLeft n g)
      = ringFieldReflectLeft n (ringStaggeredRelabel n g) := by
  funext z
  simp only [ringStaggeredRelabel, ringFieldReflectLeft, physFieldOf,
    LatticeSystem.Math.reflectLeft]
  by_cases hz : (z : ℕ) < n
  · rw [if_pos hz, if_pos hz]
  · rw [if_neg hz, if_neg hz, ringReflect_eq_rev n z, neg_one_pow_ringReflect]
    ring

/-- **Right mirror ↔ signed right field copy.**  `P (reflectRight g) = ringFieldReflectRight (P g)`
(Tasaki §4.1, reflected field copies (4.1.50), pp. 85–86).  Symmetric to the left case: on the right
half both sides are `(−1)^z g z` (via involutivity of `r`), and on the left half the two right-half
minus signs cancel through `(−1)^{r z} = −(−1)^z` (`neg_one_pow_ringReflect`). -/
theorem ringStaggeredRelabel_reflectRight (n : ℕ) (g : Fin (2 * n) → ℝ) :
    ringStaggeredRelabel n (LatticeSystem.Math.reflectRight n g)
      = ringFieldReflectRight n (ringStaggeredRelabel n g) := by
  funext z
  simp only [ringStaggeredRelabel, ringFieldReflectRight, physFieldOf,
    LatticeSystem.Math.reflectRight]
  by_cases hz : (z : ℕ) < n
  · rw [if_pos hz, if_pos hz, ringReflect_eq_rev n z, neg_one_pow_ringReflect]
    ring
  · rw [if_neg hz, if_neg hz, ringReflect_involutive n z]
    ring

end LatticeSystem.Quantum
