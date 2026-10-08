import Mathlib.Tactic

/-!
# Root-Trunk Test for c ≥ 4 (self-contained)

The root-trunk test (Theorem 4, Eq 3.59): an an+b conjecture is proven if
1. c = a + b is a power of 2, and
2. U(c) = c · 2^min_q ≤ m = 2 · a² · v.

For the family c = 2^k (k ≥ 2), a = c − 1, b = 1, min_q = k, v = c/4 we get
U(c) = c² and m = c/2 · (c − 1)², and the test reduces to

  c² < c/2 · (c − 1)²,  which holds for all c ≥ 4 (indeed for c > 2 + √3).

- Collatz 3n+1 = family at k = 2: c = 4, U(c) = 16 < 18 = m
- Barina 7n±1 = family at k = 3: c = 8, U(c) = 64 < 196 = m
-/

/-- The key inequality: c² < c/2 · (c − 1)² for c ≥ 4. -/
theorem key_ineq {c : ℝ} (hc : 4 ≤ c) : c ^ 2 < c / 2 * (c - 1) ^ 2 := by
  nlinarith

/-- Parameters for a Conway an+b function. -/
structure AnbParams where
  a : ℤ
  b : ℤ
  v : ℤ  -- number of odd subfunctions
  minQ : ℕ  -- minimum upward exponent

/-- The trivial root: c = a + b (Eq 3.2) -/
def AnbParams.trivialRoot (p : AnbParams) : ℤ := p.a + p.b

/-- U(c) = c · 2^min_q — the trunk height (Eq 3.3) -/
def AnbParams.trunkHeight (p : AnbParams) : ℤ := p.trivialRoot * 2 ^ p.minQ

/-- m = 2 · a² · v — the periodicity (Eq 3.38) -/
def AnbParams.periodicity (p : AnbParams) : ℤ := 2 * p.a ^ 2 * p.v

def isPowerOfTwo (n : ℤ) : Prop := ∃ k : ℕ, n = 2 ^ k

/-- The root-trunk test (Eq 3.59) -/
def AnbParams.rootTrunkTestPasses (p : AnbParams) : Prop :=
  isPowerOfTwo p.trivialRoot ∧ p.trunkHeight ≤ p.periodicity

/-! ## The c = 2^k family -/

/-- c = 2^k, a = c − 1, b = 1, min_q = k, v = c/4 = 2^(k−2). -/
def pow2Family (k : ℕ) : AnbParams where
  a := 2 ^ k - 1
  b := 1
  v := 2 ^ (k - 2)
  minQ := k

/-- The test passes for every c = 2^k ≥ 4: with c = 4d, U(c) = c² = 16d² and
    m = c/2 · (c − 1)² = 2d(4d − 1)², and 16d² < 2d(4d − 1)² since d ≥ 1. -/
theorem pow2Family_rootTrunkTest (k : ℕ) (hk : 2 ≤ k) :
    (pow2Family k).rootTrunkTestPasses := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  refine ⟨⟨j + 2, by simp [pow2Family, AnbParams.trivialRoot]⟩, ?_⟩
  have hd : (1 : ℤ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  simp only [AnbParams.trunkHeight, AnbParams.periodicity, AnbParams.trivialRoot,
    pow2Family, Nat.add_sub_cancel, pow_add]
  nlinarith

/-! ## Collatz 3n+1 and Barina 7n±1 -/

/-- Collatz 3n+1: a = 3, b = 1, v = 1, min_q = 2 -/
def collatz3n1 : AnbParams := pow2Family 2

/-- Barina 7n±1: a = 7, b = 1, v = 2, min_q = 3. The ± dispatch (7n+1 on [1]₄,
    7n−1 on [3]₄) does not enter the test; only the offset at n = 1 matters. -/
def barina7n1 : AnbParams := pow2Family 3

example : collatz3n1 = ⟨3, 1, 1, 2⟩ := rfl
example : barina7n1 = ⟨7, 1, 2, 3⟩ := rfl

theorem collatz_rootTrunkTest : collatz3n1.rootTrunkTestPasses :=
  pow2Family_rootTrunkTest 2 le_rfl

theorem barina_rootTrunkTest : barina7n1.rootTrunkTestPasses :=
  pow2Family_rootTrunkTest 3 (by norm_num)
