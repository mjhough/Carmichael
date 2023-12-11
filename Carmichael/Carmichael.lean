import Mathlib.FieldTheory.Finite.Basic


/-!
# Carmichael numbers

In this file we define Carmichael numbers: composite numbers for which there
exists no Fermat witness. Given an integer `n`, an integer `a` is a Fermat
witness for `n` if `a^n` is not congruent to `a` modulo `n`.

## Main Results

The main definition of this file is

- `CarmichaelNumber`: A composite number `n` is a Carmichael number if for all
integers `a`, `a^n` is congruent to `a` modulo `n`.

The main theorems of this file are
- `carmichael_sub_one`: If `n` is a Carmichael number, `a^(n-1)` is congruent to `1` modulo `n` for
all integers `a` coprime to `n`.
- `carmichael_num_is_odd`: Any Carmichael number must be odd.
-/


/--
`n` is a Carmichael number of for all integers `a`, `a^n` is congruent to `a` modulo `n`.
-/
def CarmichaelNumber (n : ℕ) : Prop :=
  (∀ (a : ℤ) , a.pow n ≡ a [ZMOD n]) ∧ ¬ Nat.Prime n ∧ (n > 0)


/--
This lemma says that if gcd(m,k) = 1 then gcd(m^n, k) = 1. It will be used in the proof of
`carmichael_sub_one`.
-/
lemma Int.Coprime.pow_left (n : ℕ) {m k : ℤ} (h : Int.gcd m k = 1) : Int.gcd (Int.pow m n) k = 1 :=
  Int.isCoprime_iff_gcd_eq_one.1 (Int.isCoprime_iff_gcd_eq_one.2 h).pow_left


/--
`carmichael_sub_one` proves that if `n` is a Carmichael number, `a^(n-1)` is congruent to `1` modulo `n` for
all integers `a` coprime to `n`.
-/
theorem carmichael_sub_one {n : ℕ} (hc : CarmichaelNumber n) : ∀ (a : ℤ) (h : Int.gcd a n = 1),
(a.pow (n - 1) ≡ 1 [ZMOD n]) := by
  intro a h
  nth_rewrite 1 [← Nat.div_one n]
  apply Int.Coprime.pow_left n at h
  rw [Int.gcd_comm] at h
  nth_rewrite 1 [← h]
  apply @Int.ModEq.cancel_right_div_gcd n (Int.pow a (n-1)) 1 (Int.pow a n) _ _
  · have := hc.2.2.lt
    linarith [this]
  rw [one_mul,Int.ModEq,hc.1,Int.mul_emod,hc.1,← Int.mul_emod,pow_eq]
  nth_rewrite 2 [← pow_one a]
  rw [← pow_add, add_comm, add_comm, ← Nat.sub_add_comm, Nat.add_one_sub_one, ← Int.ModEq, ← pow_eq]
  apply hc.1
  apply hc.2.2

/--
`carmichael_num_is_odd` proves that all Carmichael numbers must be odd.
-/
theorem carmichael_num_is_odd {n : ℕ} (hc : CarmichaelNumber n) : Odd n := by
  by_contra! n_even
  have n_sub_pow_cong : Int.pow (n-1) n ≡ 1 [ZMOD n]
  · apply Int.ModEq.trans (@Int.ModEq.pow n (n-1) (-1) _ _)
    · rw [(neg_one_pow_eq_one_iff_even _).2 (Nat.even_iff_not_odd.2 n_even)]
      simp
    rw [Int.modEq_iff_add_fac]
    refine' ⟨-1, by simp [sub_add_eq_add_sub]⟩
  have := hc.1 (n-1)
  have := this.symm.trans n_sub_pow_cong
  obtain (a | b) := le_or_gt n 2
  · obtain (rfl | lt) := eq_or_lt_of_le a
    · apply hc.2.1
      exact Nat.prime_two
    · obtain (rfl | rfl) := Nat.le_one_iff_eq_zero_or_eq_one.1 (Nat.lt_succ.1 lt)
      · apply hc.2.2.ne rfl
      apply n_even odd_one
  have hf := Int.ModEq.eq this
  rw [Int.emod_eq_of_lt, Int.emod_eq_of_lt] at hf
  · apply ne_of_gt b
    linarith
  · linarith
  · linarith
  · linarith
  linarith
