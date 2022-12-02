import algebra.ring.basic
import tactic
set_option old_structure_cmd true

universes u

@[protect_proj, ancestor add_monoid_with_one comm_monoid]
class wheel (α : Type u) extends add_comm_monoid_with_one α, comm_monoid α :=
(div : α → α)
(div_invol : ∀ x, div (div x) = x)
(div_mul_distrib : ∀ x y, div (x * y) = div x * div y)
(add_distrib_mul : ∀ x y z, (x + y) * z + (0 : α) * z = x * z + y * z)
(add_distrib_div : ∀ x y z, (x + y * z) * div y = x * div y + z + (0 : α) * y)
(zero_mul : (0 : α) * (0 : α) = 0)
(add_zero_mul : ∀ x y z, (x + (0 : α) * y) * z = x * z + (0 : α) * y)
(div_add_zero : ∀ x y, div (x + (0 : α) * y) = div x + 0 * y)
(add_infinity : ∀ x, 0 * div 0 + x = (0 : α) * div 0)

attribute [simp] wheel.div_invol wheel.div_mul_distrib wheel.add_distrib_mul wheel.zero_mul wheel.add_infinity

-- localized "notation (name := wheel.bot) `⊥` := (0 * wheel.div 0 : wheel)" in wheel
-- localized "notation (name := wheel.infinity) `∞` := (wheel.div 0 : wheel)" in wheel
-- localized "prefix `/`:(std.prec.max + 4) := wheel.div" in wheel
prefix `/`:(std.prec.max + 4) := wheel.div
-- notation (name := wheel.infinity) `∞` := (/0 : wheel)
-- notation (name := wheel.bot) `⊥` := (0 * /0 : wheel)

namespace wheel

variables {W : Type u} [wheel W]

lemma zero_mul_add : ∀ (x y : W), 0 * (x + y) = 0 * x + 0 * y :=
begin
  intros x y,
	rw mul_comm,
	nth_rewrite 1 mul_comm,
	nth_rewrite 2 mul_comm,
	simpa using wheel.add_distrib_mul x y 0,
end

@[simp]
lemma div_one_eq_one : /(1 : W) = 1 :=
begin
	calc /(1 : W)
	    = (1 : W) * /(1 : W) : (one_mul _).symm
	... = /(/(1 : W)) * /(1 : W) : by rw wheel.div_invol
	... = /(/(1 : W) * 1) : by rw wheel.div_mul_distrib
	... = /(/(1 : W)) : by rw mul_one
	... = 1 : wheel.div_invol _,
end

lemma zero_mul_mul_eq_zero_mul_add_zero_mul : ∀ (x y : W), 0 * x + 0 * y = 0 * x * y :=
begin
	intros x y,
	rw (wheel.add_zero_mul 0 y x).symm,
  rw [zero_add, mul_assoc], 
	nth_rewrite 1 mul_comm,
	rwa ← mul_assoc,
end

lemma infinity_mul : ∀ (x : W), 0 * /0 * x = 0 * /0 :=
begin
	intro x,
	rw ← zero_mul_mul_eq_zero_mul_add_zero_mul (/0) x,
	exact wheel.add_infinity (0 * x),
end

lemma div_self : ∀ (x : W), x * /x = 1 + 0 * x * /x :=
begin
	intro x,
	have := wheel.add_distrib_div 0 x 1,
	rw [zero_add, mul_one] at this,
	rw [this, add_assoc, add_comm, add_assoc],
	rwa zero_mul_mul_eq_zero_mul_add_zero_mul,
end

lemma mul_cancel : ∀ (x y z : W), x * z = y * z → x + 0 * z * /z = y + 0 * z * /z :=
begin
	intros x y z h,
	have : x * z * /z = y * z * /z := congr_arg (λ p, p * /z) h,
	rw [mul_assoc, mul_assoc] at this,
	rw div_self z at this,
	rw [mul_comm, mul_comm y _, mul_assoc] at this,
	rw [wheel.add_zero_mul 1 _ x, wheel.add_zero_mul 1 _ y, one_mul, one_mul] at this,
	rwa mul_assoc,
end

lemma zero_eq_one_imp_one_eq_infinity : 0 = (1 : W) → 1 = 0 * /(0 : W) :=
begin
	intro h,
	calc 1
	    = 1 * 1 : (mul_one 1).symm
	... = 1 * /(1 : W) : by rw div_one_eq_one
	... = 0 * /0 : by rw h,
end

lemma zero_eq_bot_imp_zero_eq_infinity : 0 = /(0 : W) → 0 = 0 * /(0 : W) :=
begin
	intro h,
	calc 0 
		  = 0 * 0 : wheel.zero_mul.symm
	... = 0 * /(0 : W) : by rw ← h,
end

lemma zero_eq_infinity_imp_eq_infinity : (0 : W) = 0 * /0 → ∀ (x : W), x = 0 * /0 :=
begin
	intros h x,
	calc x
			= 0 + x : (zero_add x).symm
	... = 0 * /0 + x : by rw ← h
	... = 0 * /0 : wheel.add_infinity _,	
end

lemma one_eq_bot_imp_one_eq_infinity : (1 : W) = /0 → (1 : W) = 0 * /0 :=
begin
	intro h,
	calc (1 : W)
	    = 1 * /1 : by rw [one_mul, div_one_eq_one]
	... = /0 * /(/0) : by rw h
	... = 0 * /0 : by rw [wheel.div_invol, mul_comm],
end

lemma one_eq_infinity_imp_eq_infinity : (1 : W) = 0 * /0 → ∀ (x : W), x = 0 * /0 :=
begin
	intros h x,
	calc x
			= 1 * x : (one_mul x).symm
	... = 0 * /0 * x : by rw h
	... = 0 * /0 : infinity_mul x,
end

lemma bot_eq_infinity_imp_eq_infinity : /(0 : W) = 0 * /0 → ∀ (x : W), x = 0 * /0 :=
begin
	intros h x,
	calc x
			= 0 + x : (zero_add x).symm
	... = /(/0) + x : by rw wheel.div_invol
	... = /(0 * /0) + x : by rw ← h
	... = 0 * /(0) + x : by rw [wheel.div_mul_distrib, wheel.div_invol, mul_comm]
	... = 0 * /0 : wheel.add_infinity _,
end

lemma zero_one_bot_infinity_unique : ((0 : W) = 1) ∨ (0 = /(0 : W)) ∨ (0 = 0 * /(0 : W)) ∨ (1 = /(0 : W)) ∨ (1 = 0 * /(0 : W)) ∨ (/(0 : W) = 0 * /(0 : W)) → ∀ (x y : W), x = y :=
begin
	intro h,
	suffices : ∀ x, x = (0 : W) * /0,
	{ intros x y, exact (this x).trans (this y).symm, },
	obtain (h | h | h | h | h | h) := h,
	{ exact one_eq_infinity_imp_eq_infinity (zero_eq_one_imp_one_eq_infinity h), },
	{ exact zero_eq_infinity_imp_eq_infinity (zero_eq_bot_imp_zero_eq_infinity h), },
	{ exact zero_eq_infinity_imp_eq_infinity h, },
	{ exact one_eq_infinity_imp_eq_infinity (one_eq_bot_imp_one_eq_infinity h), },
	{ exact one_eq_infinity_imp_eq_infinity h, },
	{ exact bot_eq_infinity_imp_eq_infinity h, }
end

end wheel