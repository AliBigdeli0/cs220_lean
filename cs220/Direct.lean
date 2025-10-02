import Mathlib.Data.Nat.Basic
import Mathlib.Tactic



/-- For all natural numbers n, if n is positive then n ≤ n^2.
    Or in predicate logic: ∀ n ∈ ℕ, 0 < n → n ≤ n^2 -/
theorem le_square (n : ℕ) (hpos : 0 < n): n ≤ n^2 := by
  rw [Nat.pow_add_one]                      -- now goal is `n ≤ n^1 * n`
  rw [Nat.pow_one]                          -- now goal is `n ≤ n * n`
  rw (occs := .pos [1]) [←Nat.one_mul n]    -- now goal is `1 * n ≤ n * n`
  -- this is exactly what `mul_le_mul` tells us if we have the two hypotheses
  -- `1 ≤ n` (which is lean can infer from `hpos`) and `n ≤ n`
  -- (which we get from reflexivity: `le_refl n`)
  exact Nat.mul_le_mul hpos (le_refl n)

-- Manually providing that proof is a bit laborious, but Lean has tactics that
-- can search for proofs such as `nlinarith` which tries nonlinear arithmetic!
theorem le_square_fancy (n : ℕ) (hpos : 1 ≤ n) : n ≤ n^2 := by nlinarith

-- `nlinarith` is clever enough to figure out a proof for the case n = 0 too
theorem le_square_general (n : ℕ) : n ≤ n^2 := by nlinarith



/-- The square of an odd integer is odd. -/
theorem odd_sq (n : ℤ) (hodd : Odd n) : Odd (n^2) := by
  -- implicitly, we do universal instantiation to get the variable n
  match hodd with                 -- existential instantiation with `Odd n : ∃ k, n = 2*k + 1`
  | ⟨k, hn⟩ =>                    -- to introduce particular `k : ℕ` and `hn : n = 2*k+1`
    let l := 2*k*(k+1)            -- name a variable `l` for convenience
    have hn2 : n^2 = 2*l + 1 := by calc n^2
      _ = (2*k+1)^2 := by rw [hn] -- substitute using hnk
      _ = 2*l + 1 := by ring      -- make Lean do all the algebra
    exact ⟨l, hn2⟩                -- construct the conclusion `∃ l, n^2 = 2*l + 1`
    -- universal generalization at the end is again implicit

/-- This is such a simple proof that the `grind` tactic can do it entirely! -/
theorem odd_sq_fancy (n : ℤ) (hodd : Odd n) : Odd (n^2) := by grind



/-- For integers x and y, if x divides y then x^2 divides y^2.
    Interestingly, this is too complex for `by grind` to work on its own. -/
theorem dvd_sq (x y : ℤ) (hdiv : x ∣ y) : x^2 ∣ y^2 := by
  match hdiv with
  | ⟨a, hy⟩ =>
    have : y^2 = x^2*a^2 := by rw [hy]; ring
    exact ⟨a^2, this⟩
