/-
Machine-checked results from the overnight Collatz session (2026-07-15).

Target 1: the unrolled orbit identity  2^(A N) * n N = 3^N * n 0 + D N
Target 2: the Böhm–Sontacchi sign dichotomy for closed orbits:
          a p-cycle satisfies (2^(A p) - 3^p) * n 0 = D p with D p > 0,
          hence subcritical cycles (2^A < 3^p) have negative seeds.
-/
import Mathlib.Tactic

namespace CollatzNight

open Finset

/-- Syracuse orbit data: at each step, `2 ^ a j * n (j+1) = 3 * n j + 1`.
    (The `a j` are the division counts; oddness is not needed for the identity.) -/
def SyracuseRel (n : ℕ → ℤ) (a : ℕ → ℕ) : Prop :=
  ∀ j, 2 ^ (a j) * n (j + 1) = 3 * n j + 1

/-- Cumulative divisions `A N = a 0 + ⋯ + a (N-1)`. -/
def A (a : ℕ → ℕ) (N : ℕ) : ℕ := ∑ j ∈ range N, a j

/-- The Böhm–Sontacchi numerator `D N = ∑_{j<N} 3^(N-1-j) * 2^(A j)`. -/
def D (a : ℕ → ℕ) (N : ℕ) : ℤ := ∑ j ∈ range N, 3 ^ (N - 1 - j) * 2 ^ (A a j)

lemma A_succ (a : ℕ → ℕ) (N : ℕ) : A a (N + 1) = A a N + a N := by
  simp [A, sum_range_succ]

lemma D_succ (a : ℕ → ℕ) (N : ℕ) :
    D a (N + 1) = 3 * D a N + 2 ^ (A a N) := by
  unfold D
  rw [sum_range_succ]
  have h1 : (N + 1) - 1 - N = 0 := by omega
  rw [h1, pow_zero, one_mul, mul_sum]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  have hjN : j < N := mem_range.mp hj
  have h2 : (N + 1) - 1 - j = (N - 1 - j) + 1 := by omega
  rw [h2, pow_succ]
  ring

/-- **Target 1 (machine-checked).** The unrolled orbit identity. -/
theorem unrolled_identity (n : ℕ → ℤ) (a : ℕ → ℕ) (h : SyracuseRel n a) :
    ∀ N, 2 ^ (A a N) * n N = 3 ^ N * n 0 + D a N := by
  intro N
  induction N with
  | zero => simp [A, D]
  | succ N ih =>
      have step := h N
      have : (2:ℤ) ^ (A a (N + 1)) * n (N + 1)
           = 2 ^ (A a N) * (2 ^ (a N) * n (N + 1)) := by
        rw [A_succ, pow_add]; ring
      rw [this, step, D_succ, pow_succ]
      linear_combination (3:ℤ) * ih

/-- `D p > 0` for any nonempty script: it is a sum of positive terms. -/
theorem D_pos (a : ℕ → ℕ) (p : ℕ) (hp : 0 < p) : 0 < D a p := by
  unfold D
  apply sum_pos
  · intro j _
    positivity
  · exact nonempty_range_iff.mpr (by omega)

/-- **Target 2a (machine-checked).** A closed orbit of period `p` satisfies the
    Böhm–Sontacchi equation `(2^(A p) - 3^p) * n 0 = D p`. -/
theorem cycle_equation (n : ℕ → ℤ) (a : ℕ → ℕ) (h : SyracuseRel n a)
    (p : ℕ) (hcyc : n p = n 0) :
    ((2:ℤ) ^ (A a p) - 3 ^ p) * n 0 = D a p := by
  have := unrolled_identity n a h p
  rw [hcyc] at this
  linarith [this]

/-- **Target 2b (machine-checked): the sign dichotomy.** A subcritical closed
    orbit (`2^A < 3^p`, i.e. average division count below `log₂ 3`) has a
    strictly negative seed. The classical impostor cycles at −1, −5, −17 are
    exactly this phenomenon; no positive cycle can be subcritical. -/
theorem subcritical_cycle_is_negative (n : ℕ → ℤ) (a : ℕ → ℕ)
    (h : SyracuseRel n a) (p : ℕ) (hp : 0 < p) (hcyc : n p = n 0)
    (hsub : (2:ℤ) ^ (A a p) < 3 ^ p) : n 0 < 0 := by
  have hD : 0 < D a p := D_pos a p hp
  have heq := cycle_equation n a h p hcyc
  nlinarith [heq, hD, hsub]

/-- Complementary direction: a positive seed on a closed orbit forces the
    supercritical inequality `3^p < 2^(A p)` — Baker/Steiner territory. -/
theorem positive_cycle_is_supercritical (n : ℕ → ℤ) (a : ℕ → ℕ)
    (h : SyracuseRel n a) (p : ℕ) (hp : 0 < p) (hcyc : n p = n 0)
    (hpos : 0 < n 0) : (3:ℤ) ^ p < 2 ^ (A a p) := by
  have hD : 0 < D a p := D_pos a p hp
  have heq := cycle_equation n a h p hcyc
  nlinarith [heq, hD, hpos]

end CollatzNight

namespace Mod3Slaving

/-- **Target 3a (machine-checked): the mod-3 slaving lemma.** If `2^a * m = 3*n + 1`
    (one Syracuse step: `m` is the next odd iterate, `a` the division count), then
    `m ≡ (−1)^a (mod 3)`: the entire 3-adic coordinate of the orbit is a
    deterministic function of the division sequence. -/
theorem next_odd_mod3 (m n : ℤ) (a : ℕ) (h : 2 ^ a * m = 3 * n + 1) :
    (m : ZMod 3) = (-1) ^ a := by
  have h3 : ((2 : ZMod 3)) ^ a * (m : ZMod 3) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod 3)) h
    push_cast at this
    simpa [show (3 : ZMod 3) = 0 by decide] using this
  have h2 : (2 : ZMod 3) = -1 := by decide
  rw [h2] at h3
  calc (m : ZMod 3) = ((-1) ^ a * (-1) ^ a) * m := by
        rw [← pow_add]
        have : Even (a + a) := ⟨a, rfl⟩
        rw [this.neg_one_pow, one_mul]
      _ = (-1) ^ a * ((-1) ^ a * m) := by ring
      _ = (-1) ^ a := by rw [h3, mul_one]

end Mod3Slaving

namespace CarryTheorem

open Finset

/-- The alternating-bit integer `S m = Σ_{j<m} 4^j = 0b0101…01` (`m` ones):
    the `2m`-bit truncation of the 2-adic expansion of `−1/3`. -/
def S (m : ℕ) : ℤ := ∑ j ∈ range m, 4 ^ j

lemma three_mul_S (m : ℕ) : 3 * S m = 4 ^ m - 1 := by
  induction m with
  | zero => simp [S]
  | succ m ih =>
      unfold S at ih ⊢
      rw [sum_range_succ, mul_add, ih, pow_succ]
      ring

/-- **Target 3b (machine-checked): the carry theorem, arithmetic core.**
    `4^m ∣ 3n+1` iff the low `2m` bits of `n` are the alternating pattern
    `0101…01` — i.e. `n` agrees with the 2-adic expansion of `−1/3` to `2m`
    places. Hence `v₂(3n+1)` equals the length of trailing agreement of `n`
    with `…010101₂`, which is where the carry chain propagates. -/
theorem carry_core (m : ℕ) (n : ℤ) :
    (4 : ℤ) ^ m ∣ 3 * n + 1 ↔ (4 : ℤ) ^ m ∣ n - S m := by
  have key : 3 * n + 1 = 3 * (n - S m) + 4 ^ m := by
    have h := three_mul_S m
    ring_nf
    ring_nf at h
    linarith
  have hcop : IsCoprime ((4 : ℤ) ^ m) 3 := by
    apply IsCoprime.pow_left
    rw [Int.isCoprime_iff_gcd_eq_one]
    decide
  constructor
  · intro h
    have h2 : (4 : ℤ) ^ m ∣ 3 * (n - S m) := by
      have heq : (3 : ℤ) * (n - S m) = (3 * n + 1) - 4 ^ m := by linarith
      rw [heq]
      exact dvd_sub h (dvd_refl _)
    exact hcop.dvd_of_dvd_mul_left h2
  · intro h
    rw [key]
    exact dvd_add (h.mul_left 3) (dvd_refl _)

end CarryTheorem
