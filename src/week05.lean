-- Math 52: Week 5

import .utils
open classical

-- The following lemmas may be useful for the next proof.
-- mul_lt_mul_of_pos_left (a b c : ℝ) : a < b → 0 < c → c * a < c * b
-- mul_lt_mul_of_pos_right (a b c : ℝ) : a < b → 0 < c → a * c < b * c

-- Lakins 2.1.2: For all real numbers a and b, if 0 < a < b, then a² < b².
theorem L212 : ∀ (a b : ℝ), 0 < a ∧ a < b → a * a < b * b :=
begin
sorry
end

-- The following lemmas may be useful for the next proof.
-- mul_le_mul_of_nonneg_left (a b c : ℝ) : a ≤ b → 0 ≤ c → c * a ≤ c * b
-- mul_le_mul_of_nonneg_right (a b c : ℝ) : a ≤ b → 0 ≤ c → a * c ≤ b * c
-- mul_le_mul_of_nonpos_left (a b c : ℝ) : b ≤ a → c ≤ 0 → c * a ≤ c * b
-- mul_le_mul_of_nonpos_right (a b c : ℝ) : b ≤ a → c ≤ 0 → a * c ≤ b * c

-- Lakins 2.1.6: For all real numbers x, 0 ≤ x².
theorem L216 : ∀ (x : ℝ), 0 ≤ x * x :=
begin
sorry
end

-- The following lemmas may be useful in the following proof.
-- div_le_of_le_mul_of_pos (a b c : ℝ) : a ≤ b * c → c > 0 → a / c ≤ b
-- le_div_of_mul_le_of_pos (a b c : ℝ) : a * c ≤ b → c > 0 → a ≤ b / c

-- Lakins 2.1.11: For all real numbers x and y, if x ≤ y then x ≤ (x + y)/2 ≤ y.
theorem L2111 : ∀ (x y : ℝ), x ≤ y → x ≤ (x + y)/2 ∧ (x + y)/2 ≤ y :=
begin
sorry
end

-- The following lemmas may be useful in the next proof.
-- ne_of_lt (a b : ℝ) : a < b → a ≠ b
-- mul_pos (a b : ℝ) : a > 0 → b > 0 → a * b > 0
-- mul_neg_of_pos_of_neg (a b : ℝ) : a > 0 → b < 0 → a * b < 0
-- mul_neg_of_neg_of_pos (a b : ℝ) : a < 0 → b > 0 → a * b < 0
-- mul_pos_of_neg_of_neg (a b : ℝ) : a < 0 → b < 0 → a * b > 0

-- Lakins 2.1.7: For all real numbers x and y, if xy = 0, then x = 0 or y = 0.
theorem L217 : ∀ (x y : ℝ), x * y = 0 → x = 0 ∨ y = 0 :=
begin
sorry
end 

-- This is a really tricky proof!
-- Lakins 2.1.9: For all real numbers x and y, if x² = y², then x = y or x = −y; i.e., x = ±y.
theorem L219 : ∀ (x y : ℝ), x * x = y * y → x = y ∨ x = -y :=
begin
intros x y H,
have L : x - y = 0 ∨ x + y = 0,
begin
apply L217,
calc (x - y) * (x + y)
= x * (x + y) - y * (x + y) : by rw sub_mul ...
= (x * x + x * y) - y * (x + y) : by rw mul_add ...
= (x * x + x * y) - (y * x + y * y) : by rw mul_add ...
= ((x * x + x * y) - y * x) - y * y : by rw sub_sub ...
= ((x * x + x * y) - x * y) - y * y : by ac_refl ...
= x * x - y * y : by rw add_sub_cancel ...
= x * x - x * x : by rw H ...
= 0 : by rw sub_self,
end,
cases L,
{ left,
  apply eq_of_sub_eq_zero,
  assumption
},
{ right,
  apply eq_of_sub_eq_zero,
  rw sub_neg_eq_add,
  assumption,
},
end
