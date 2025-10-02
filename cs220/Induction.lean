import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-- Theorem: For all natural numbers n ≥ 4, 4^n ≥ n^4.
    This is a slightly complicated example as the natural statement starts at n = 4 not n = 0.
    We an induction principle for this kind of statement, but it entails some extra work compared
    to starting from zero. -/
theorem exp_ge_pow (n : ℕ) (hn : 4 ≤ n) : 4^n ≥ n^4 := by
  induction n, hn using Nat.le_induction

  case base =>
    -- Goal: 4^4 ≥ 4^4
    rfl

  case succ n hn ih =>
    -- Goal : 4^(n+1) ≥ (n+1)^4
    -- Hypotheses: hn : n ≥ 4 and ih : 4^n ≥ n^4
    calc 4^(n + 1)
      _ ≥ 4 * n^4           := by omega -- applies ih for us since it's of the right form
      _ ≥ (n + 1)^4         := by -- a tricky calculation...
          calc 4 * n^4
          _ = n^4 + n^4 + n^4 + n^4 := by ring
          _ ≥ n^4 + 4*n^3 + 6*n^2 + (4*n + 1) := by
            gcongr
            -- have hn : 4 ≤ n so a single nlinarith should sort out all these goals, no?
            . -- goal is 4*n^3 ≤ n^4
              have : 4 * n^3 ≤ n * n^3 := by gcongr
              nlinarith
            . -- goal is 6*n^2 ≤ n^4
              have : 6 ≤ n^2 := by nlinarith
              nlinarith
            . -- goal is 4*n+1 ≤ n^4
              have : 4*n ≤ n^2 := by nlinarith
              nlinarith
          _ = (n + 1)^4 := by ring

-- A clever tactic significantly shortens the proof
theorem exp_ge_pow_fancy (n : ℕ) (hn : 4 ≤ n) : 4^n ≥ n^4 := by
  induction n, hn using Nat.le_induction
  case base => rfl
  case succ n hn ih =>
    calc 4^(n + 1)
      _ ≥ 4 * n^4           := by omega
      _ ≥ (n + 1)^4         := by
        -- Introduce n' ∈ ℕ such that n' + 4 = n which tactics like nlinarith handle better
        obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hn
        ring_nf
        nlinarith
